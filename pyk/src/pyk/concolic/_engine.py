from __future__ import annotations

import logging
from dataclasses import dataclass
from typing import TYPE_CHECKING

from ..kast.inner import Subst
from ..kast.prelude.ml import is_top, mlNot

if TYPE_CHECKING:
    from collections.abc import Iterable

    from ..cterm import CTerm
    from ..cterm.symbolic import CTermSymbolic
    from ..kast.inner import KInner


_LOGGER = logging.getLogger(__name__)


@dataclass(frozen=True)
class PathConstraint:
    """A single branch taken along a concrete execution path.

    Attributes:
        condition: The ML predicate guarding the branch that was taken (e.g. ``{ true #Equals X <Int 5 }``).
        depth: The cumulative rewrite depth at which the branch was taken.
    """

    condition: KInner
    depth: int


@dataclass(frozen=True)
class ConcolicTrace:
    """The result of executing one concrete input through the symbolic semantics.

    Attributes:
        input: The concrete input (a substitution over the symbolic input variables) that drove the run.
        path: The ordered branch conditions taken, the _path condition_ of the run.
        final: The final symbolic state reached.
        status: Why execution stopped: ``terminal``, ``depth_bound`` or ``undetermined``.
    """

    input: Subst
    path: tuple[PathConstraint, ...]
    final: CTerm
    status: str

    @property
    def signature(self) -> tuple[str, ...]:
        """A hashable fingerprint of the path condition, used to deduplicate explored paths."""
        return tuple(str(pc.condition) for pc in self.path)


class ConcolicEngine:
    """A proof-of-concept concolic (concrete + symbolic) execution engine on top of `CTermSymbolic`.

    The engine drives the K symbolic backend along the single path selected by a concrete input,
    recording the branch conditions encountered (the _path condition_). By negating a prefix of the
    path condition and asking the backend's SMT solver for a model, it synthesizes new concrete
    inputs that drive execution down previously unexplored branches -- the classic DART/SAGE loop.

    Attributes:
        cterm_symbolic: The symbolic execution interface (wraps a running Kore RPC server).
        input_vars: Names of the free configuration variables treated as symbolic program input.
        max_step: Maximum rewrite depth per `execute` call.
        max_branches: Safety bound on the number of branch points followed in a single trace.
        module_name: Optional Kore module name to evaluate against.
    """

    cterm_symbolic: CTermSymbolic
    input_vars: tuple[str, ...]
    max_step: int = 1000
    max_branches: int = 100
    module_name: str | None = None

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

    def trace(self, init: CTerm, concrete_input: Subst) -> ConcolicTrace:
        """Execute `init` symbolically, following the single path picked out by `concrete_input`.

        Args:
            init: The initial symbolic configuration, with the `input_vars` left free.
            concrete_input: A concrete assignment to (a subset of) `input_vars`.

        Returns:
            A `ConcolicTrace` recording the branch conditions taken and the final state.
        """
        cterm = init
        path: list[PathConstraint] = []
        total_depth = 0
        status = 'terminal'

        for _ in range(self.max_branches):
            exec_result = self.cterm_symbolic.execute(cterm, depth=self.max_step, module_name=self.module_name)
            total_depth += exec_result.depth
            next_states = exec_result.next_states

            if not next_states:
                # No successors: terminal or stuck, unless we ran into the depth bound.
                if exec_result.depth >= self.max_step:
                    status = 'depth_bound'
                cterm = exec_result.state
                break

            if len(next_states) == 1:
                # A single successor (e.g. a cut-point rule); follow it without recording a branch.
                cterm = next_states[0].state
                continue

            chosen = self._select_branch(next_states, concrete_input)
            if chosen is None:
                _LOGGER.warning('Could not determine branch for concrete input; stopping trace')
                cterm = exec_result.state
                status = 'undetermined'
                break

            condition, next_cterm = chosen
            path.append(PathConstraint(condition=condition, depth=total_depth))
            cterm = next_cterm
        else:
            status = 'depth_bound'

        return ConcolicTrace(input=concrete_input, path=tuple(path), final=cterm, status=status)

    def flipped_inputs(self, init: CTerm, trace: ConcolicTrace) -> list[Subst]:
        """Synthesize new concrete inputs by negating each prefix of `trace`'s path condition.

        For each branch ``i`` along the path, the engine builds the constraint set
        ``c_0 & ... & c_(i-1) & not c_i`` and asks the SMT solver for a satisfying model over the
        `input_vars`. Each feasible model is a concrete input that diverges from `trace` at branch ``i``.

        Args:
            init: The same initial symbolic configuration used to produce `trace`.
            trace: A previously recorded trace whose branches should be flipped.

        Returns:
            The list of feasible new inputs, one per flippable branch (infeasible flips are dropped).
        """
        results: list[Subst] = []
        for i, pc in enumerate(trace.path):
            prefix = [trace.path[j].condition for j in range(i)]
            constraints = prefix + [mlNot(pc.condition)]
            constrained = init
            for constraint in constraints:
                constrained = constrained.add_constraint(constraint)

            model = self.cterm_symbolic.get_model(constrained, module_name=self.module_name)
            if model is None:
                _LOGGER.debug(f'Flipping branch {i} is infeasible')
                continue
            results.append(self._restrict_to_inputs(model))
        return results

    def explore(self, init: CTerm, seed_input: Subst, *, max_iterations: int = 50) -> list[ConcolicTrace]:
        """Run the concolic exploration loop, discovering distinct execution paths from a seed input.

        Maintains a worklist of concrete inputs, traces each one, and enqueues the inputs synthesized
        by flipping its branches -- skipping inputs whose path condition was already seen. Bounded by
        `max_iterations` so the loop always terminates.

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

            for new_input in self.flipped_inputs(init, trace):
                worklist.append(new_input)

        return traces

    def _select_branch(
        self,
        next_states: Iterable[tuple[CTerm, KInner | None]],
        concrete_input: Subst,
    ) -> tuple[KInner, CTerm] | None:
        for next_state in next_states:
            cterm, condition = next_state
            if condition is None:
                continue
            if self._holds_under(condition, concrete_input):
                return condition, cterm
        return None

    def _holds_under(self, condition: KInner, concrete_input: Subst) -> bool:
        substituted = concrete_input(condition)
        simplified, _ = self.cterm_symbolic.kast_simplify(substituted, module_name=self.module_name)
        return is_top(simplified, weak=True)

    def _restrict_to_inputs(self, model: Subst) -> Subst:
        return Subst({var: term for var, term in model.items() if var in self.input_vars})
