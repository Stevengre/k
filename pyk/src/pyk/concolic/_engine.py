from __future__ import annotations

import logging
from dataclasses import dataclass, field
from typing import TYPE_CHECKING

from ..cterm import CTerm
from ..kast.inner import Subst
from ..kore.rpc import LogRewrite, RewriteSuccess, StopReason

if TYPE_CHECKING:
    from collections.abc import Iterable

    from ..cterm.symbolic import CTermSymbolic
    from ..kast.inner import KInner
    from ..kore.rpc import ExecuteResult, LogEntry, State


_LOGGER = logging.getLogger(__name__)

# Safety bound on the number of `execute` round-trips per pass, so a runaway loop always terminates.
_MAX_EXECUTE_CALLS = 10_000


@dataclass(frozen=True)
class PathConstraint:
    """A single branch taken along an execution path.

    Attributes:
        condition: The ML predicate guarding the branch that was taken (e.g. ``{ true #Equals X <Int 5 }``).
        depth: The cumulative rewrite depth at which the branch was taken.
        rule_id: The unique id of the rule whose application produced this branch (matched against the
            concrete trace).
        siblings: The rule predicates of the non-chosen successors at this branch node, converted to
            KAST. Each sibling condition is the ``rk`` (remainder) for that alternative branch — the
            sub-space of inputs that would take that branch instead of the chosen one. Siblings whose
            ``rule_predicate`` is ``None`` are omitted.
    """

    condition: KInner
    depth: int
    rule_id: str | None
    siblings: tuple[KInner, ...] = field(default_factory=tuple)


@dataclass(frozen=True)
class ConcolicTrace:
    """The result of replaying one concrete input through the symbolic semantics.

    Attributes:
        input: The concrete input (a substitution over the symbolic input variables) that drove the run.
        path: The ordered branch conditions taken, the _path condition_ of the run.
        final: The final symbolic state reached.
        status: Why execution stopped: ``terminal``, ``depth_bound`` or ``undetermined``.
        rule_trace: The ordered rule ids applied during the concrete pass that guided this trace.
    """

    input: Subst
    path: tuple[PathConstraint, ...]
    final: CTerm
    status: str
    rule_trace: tuple[str, ...]

    @property
    def signature(self) -> tuple[str, ...]:
        """A hashable fingerprint of the path condition, used to deduplicate explored paths."""
        return tuple(str(pc.condition) for pc in self.path)


class ConcolicEngine:
    """A proof-of-concept concolic (concrete + symbolic) execution engine on top of `CTermSymbolic`.

    The engine realizes the defining idea of concolic execution: a fast, deterministic *concrete*
    run produces an execution trace, which is then *reused* to drive a *symbolic* run down the very
    same path. Because the concrete trace already records which rule fired at every branch, the
    symbolic pass picks each branch by matching rule ids -- it never asks the SMT solver "which
    branch does this input take?". The solver is consulted only when synthesizing a new diverging
    input, by solving ``prefix ∧ rk`` where ``rk`` is the sibling (remainder) condition recorded
    at a branch node (remainder-driven DART).

    Concretely, for each input the engine runs two passes against the same Kore backend (so rule
    ids share one namespace):

    1. **Concrete pass** (``concrete_trace``): substitute the concrete input into the configuration and
       execute. With branch-relevant data ground, execution is deterministic -- no forking -- and the
       ordered list of applied rule ids is harvested from the rewrite logs.
    2. **Symbolic pass** (``trace``): execute with the input left symbolic. At each branch, follow the
       successor whose rule id appears next in the concrete trace, recording its guard as a path
       constraint (``ck``) and the sibling successors' guards as remainder conditions (``rk``). No
       per-branch solver call is made.
    3. **Diverging inputs** (``diverging_inputs``): for each branch node ``i``, solve
       ``prefix_{<i} ∧ rk`` for every sibling ``rk``. Each satisfying model is a new concrete input
       that follows the same path up to branch ``i``, then diverges to a sibling branch. Infeasible
       siblings are pruned automatically (``get_model`` returns ``None``).

    This remainder-driven approach handles multi-way branches correctly (no manual negation of
    ``ck``) and guarantees that every generated input explores a genuinely new, feasible path.

    Attributes:
        cterm_symbolic: The symbolic execution interface (wraps a running Kore RPC server).
        input_vars: Names of the free configuration variables treated as symbolic program input.
        max_step: Maximum rewrite depth per `execute` call.
        max_branches: Safety bound on the number of branch points followed in a single trace.
        module_name: Optional Kore module name to evaluate against.
    """

    cterm_symbolic: CTermSymbolic
    input_vars: tuple[str, ...]
    max_step: int
    max_branches: int
    module_name: str | None

    def __init__(
        self,
        cterm_symbolic: CTermSymbolic,
        input_vars: Iterable[str],
        *,
        max_step: int = 1000,
        max_branches: int = 100,
        module_name: str | None = None,
    ) -> None:
        self.cterm_symbolic = cterm_symbolic
        self.input_vars = tuple(input_vars)
        self.max_step = max_step
        self.max_branches = max_branches
        self.module_name = module_name

    def concrete_trace(self, init: CTerm, concrete_input: Subst) -> tuple[str, ...]:
        """Run `init` concretely under `concrete_input` and return the ordered rule ids applied.

        The concrete input is substituted into the configuration before execution. As long as it
        determines every branch, the run is deterministic and the returned trace is the rule-id
        sequence used to guide the symbolic pass.

        Args:
            init: The initial symbolic configuration, with the `input_vars` left free.
            concrete_input: A concrete assignment to the `input_vars`.

        Returns:
            The ordered tuple of rule ids applied during the concrete run.
        """
        cterm = CTerm(concrete_input(init.config), [concrete_input(c) for c in init.constraints])
        pattern = self.cterm_symbolic.kast_to_kore(cterm.kast)

        rule_ids: list[str] = []
        for _ in range(_MAX_EXECUTE_CALLS):
            result = self._execute(pattern)
            rule_ids.extend(self._rewrite_rule_ids(result.logs))

            if result.next_states:
                # Branch-relevant data should be ground, so this is unexpected; follow the first
                # successor deterministically to stay robust.
                _LOGGER.warning('Concrete run branched unexpectedly; following the first successor')
                pattern = result.next_states[0].kore
                continue
            if result.reason is StopReason.DEPTH_BOUND:
                pattern = result.state.kore
                continue
            break
        return tuple(rule_ids)

    def trace(self, init: CTerm, concrete_input: Subst) -> ConcolicTrace:
        """Symbolically replay `init` along the path that `concrete_input` takes concretely.

        First computes the concrete rule trace, then executes with the input left symbolic, selecting
        each branch by matching rule ids against that trace (no per-branch solver call). At each
        branch, the sibling (non-chosen) successors' predicates are recorded as remainder conditions
        (``rk``) on the ``PathConstraint``, enabling remainder-driven input generation.

        Args:
            init: The initial symbolic configuration, with the `input_vars` left free.
            concrete_input: A concrete assignment to the `input_vars`.

        Returns:
            A `ConcolicTrace` recording the branch conditions taken and the final symbolic state.
        """
        rule_trace = self.concrete_trace(init, concrete_input)
        trace_idx = 0

        cterm = init
        path: list[PathConstraint] = []
        total_depth = 0
        status = 'depth_bound'

        for _ in range(_MAX_EXECUTE_CALLS):
            result = self._execute(self.cterm_symbolic.kast_to_kore(cterm.kast))
            total_depth += result.depth
            next_states = result.next_states

            if not next_states:
                cterm = self._to_cterm(result.state)
                if result.reason is StopReason.DEPTH_BOUND:
                    continue
                status = 'terminal'
                break

            if len(next_states) == 1:
                # A single successor (e.g. a cut-point rule); follow it without recording a branch.
                cterm = self._to_cterm(next_states[0])
                continue

            chosen, siblings, trace_idx = self._match_branch(next_states, rule_trace, trace_idx)
            if chosen is None:
                _LOGGER.warning('No branch matched the concrete rule trace; stopping trace')
                cterm = self._to_cterm(result.state)
                status = 'undetermined'
                break

            # Collect remainder (rk) conditions from sibling successors.
            sibling_conditions: list[KInner] = []
            for ns in siblings:
                if ns.rule_predicate is not None:
                    sibling_conditions.append(self.cterm_symbolic.kore_to_kast(ns.rule_predicate))

            cterm = self._to_cterm(chosen)
            if chosen.rule_predicate is not None:
                condition = self.cterm_symbolic.kore_to_kast(chosen.rule_predicate)
                cterm = cterm.add_constraint(condition)
                path.append(
                    PathConstraint(
                        condition=condition,
                        depth=total_depth,
                        rule_id=chosen.rule_id,
                        siblings=tuple(sibling_conditions),
                    )
                )

        return ConcolicTrace(
            input=concrete_input,
            path=tuple(path),
            final=cterm,
            status=status,
            rule_trace=rule_trace,
        )

    def diverging_inputs(self, init: CTerm, trace: ConcolicTrace) -> list[Subst]:
        """Synthesize new concrete inputs by solving prefix conditions against sibling (remainder) conditions.

        For each branch node ``i`` along the path, and for each sibling (remainder) condition ``rk``
        recorded at that node, builds the constraint set ``c_0 & ... & c_(i-1) & rk`` and asks the
        SMT solver for a satisfying model over the ``input_vars``. Each feasible model is a new
        concrete input that follows the same path up to branch ``i``, then diverges to the sibling
        branch guarded by ``rk``.

        This remainder-driven approach handles multi-way branches without manual negation and
        naturally prunes infeasible siblings (those for which ``get_model`` returns ``None``).

        Args:
            init: The same initial symbolic configuration used to produce `trace`.
            trace: A previously recorded trace whose sibling branches should be explored.

        Returns:
            The list of feasible new inputs; infeasible sibling branches are dropped.
        """
        results: list[Subst] = []
        for i, pc in enumerate(trace.path):
            prefix = [trace.path[j].condition for j in range(i)]
            for sibling in pc.siblings:
                constraints = prefix + [sibling]
                constrained = init
                for constraint in constraints:
                    constrained = constrained.add_constraint(constraint)
                model = self.cterm_symbolic.get_model(constrained, module_name=self.module_name)
                if model is None:
                    _LOGGER.debug(f'Sibling branch at node {i} is infeasible; skipping')
                    continue
                results.append(self._restrict_to_inputs(model))
        return results

    def explore(self, init: CTerm, seed_input: Subst, *, max_iterations: int = 50) -> list[ConcolicTrace]:
        """Run the concolic exploration loop, discovering distinct execution paths from a seed input.

        Maintains a worklist of concrete inputs, traces each one, and enqueues the inputs synthesized
        by solving prefix conditions against sibling (remainder) conditions -- skipping inputs whose
        path condition was already seen. Bounded by `max_iterations` so the loop always terminates.

        Args:
            init: The initial symbolic configuration with `input_vars` free.
            seed_input: The first concrete input to explore.
            max_iterations: Maximum number of traces to run.

        Returns:
            One `ConcolicTrace` per distinct path discovered, in the order they were found.
        """
        worklist: list[Subst] = [seed_input]
        seen_signatures: set[tuple[str, ...]] = set()
        traces: list[ConcolicTrace] = []

        while worklist and len(traces) < max_iterations:
            current = worklist.pop(0)
            trace = self.trace(init, current)
            if trace.signature in seen_signatures:
                continue
            seen_signatures.add(trace.signature)
            traces.append(trace)

            for new_input in self.diverging_inputs(init, trace):
                worklist.append(new_input)

        return traces

    def _execute(self, pattern: object) -> ExecuteResult:
        # The CTerm-level API drops rule ids from successors, so the trace-guided passes go through
        # the lower-level Kore client to access `State.rule_id` and the rewrite logs.
        return self.cterm_symbolic._kore_client.execute(
            pattern,  # type: ignore[arg-type]
            max_depth=self.max_step,
            module_name=self.module_name,
            log_successful_rewrites=True,
        )

    def _to_cterm(self, state: State) -> CTerm:
        return CTerm.from_kast(self.cterm_symbolic.kore_to_kast(state.kore))

    @staticmethod
    def _rewrite_rule_ids(logs: Iterable[LogEntry]) -> list[str]:
        return [
            entry.result.rule_id
            for entry in logs
            if isinstance(entry, LogRewrite) and isinstance(entry.result, RewriteSuccess)
        ]

    @staticmethod
    def _match_branch(
        next_states: Iterable[State],
        rule_trace: tuple[str, ...],
        trace_idx: int,
    ) -> tuple[State | None, list[State], int]:
        """Select the branch successor whose rule id appears next in the concrete rule trace.

        Args:
            next_states: The successor states returned by a symbolic ``execute`` call at a branch.
            rule_trace: The full ordered rule id sequence from the concrete pass.
            trace_idx: The current position in ``rule_trace`` (entries before this index are already
                consumed by earlier branch decisions).

        Returns:
            A triple ``(chosen, siblings, new_idx)`` where ``chosen`` is the matched successor (or
            ``None`` if no match was found), ``siblings`` is the list of non-chosen successors, and
            ``new_idx`` is the updated trace index (advanced past the matched entry).
        """
        states = list(next_states)
        candidates = {s.rule_id: s for s in states if s.rule_id is not None}
        for k in range(trace_idx, len(rule_trace)):
            match = candidates.get(rule_trace[k])
            if match is not None:
                siblings = [s for s in states if s is not match]
                return match, siblings, k + 1
        return None, [], trace_idx

    def _restrict_to_inputs(self, model: Subst) -> Subst:
        return Subst({var: term for var, term in model.items() if var in self.input_vars})
