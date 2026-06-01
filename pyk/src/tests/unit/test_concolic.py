from __future__ import annotations

from dataclasses import dataclass, field
from typing import TYPE_CHECKING, NamedTuple, cast

from pyk.concolic import ConcolicEngine
from pyk.kast.inner import KApply, KToken, KVariable, Subst
from pyk.kast.prelude.kbool import FALSE, TRUE
from pyk.kast.prelude.kint import intToken, leInt
from pyk.kast.prelude.ml import mlBottom, mlEqualsFalse, mlEqualsTrue, mlTop

if TYPE_CHECKING:
    from pyk.cterm import CTerm
    from pyk.cterm.symbolic import CTermSymbolic
    from pyk.kast.inner import KInner


# ----------------------------------------------------------------------------
# A tiny in-memory symbolic interpreter standing in for `CTermSymbolic`.
#
# It models the one-branch IMP program over a single symbolic input ``N``:
#     if (N <= 5) { found = 1 ; } else { found = 0 ; }
#
# This exercises the engine's orchestration (branch selection, path-condition
# negation, the exploration worklist) without requiring a kompiled definition
# or a running Kore RPC server.
# ----------------------------------------------------------------------------


class _NextState(NamedTuple):
    state: FakeCTerm
    condition: KInner | None


@dataclass
class _ExecResult:
    state: FakeCTerm
    next_states: tuple[_NextState, ...]
    depth: int


@dataclass(frozen=True)
class FakeCTerm:
    pc: str  # 'if', 'then', 'else'
    constraints: tuple[KInner, ...] = field(default_factory=tuple)

    def add_constraint(self, constraint: KInner) -> FakeCTerm:
        return FakeCTerm(self.pc, self.constraints + (constraint,))


_N = KVariable('N', 'Int')
_GUARD = leInt(_N, intToken(5))  # N <= 5
_COND_THEN = mlEqualsTrue(_GUARD)
_COND_ELSE = mlEqualsFalse(_GUARD)


class FakeSymbolic:
    def execute(self, cterm: FakeCTerm, depth: int | None = None, module_name: str | None = None) -> _ExecResult:
        if cterm.pc == 'if':
            return _ExecResult(
                state=cterm,
                next_states=(
                    _NextState(FakeCTerm('then'), _COND_THEN),
                    _NextState(FakeCTerm('else'), _COND_ELSE),
                ),
                depth=2,
            )
        # 'then'/'else' are terminal: no successors.
        return _ExecResult(state=cterm, next_states=(), depth=1)

    def kast_simplify(self, kast: KInner, module_name: str | None = None) -> tuple[KInner, tuple]:
        # Evaluate a ground ML predicate built over `N <= 5`.
        value = _eval_pred(kast)
        if value is None:
            return kast, ()
        return (mlTop() if value else mlBottom()), ()

    def get_model(self, cterm: FakeCTerm, module_name: str | None = None) -> Subst | None:
        # Tiny integer solver: find an N in [-100, 100] satisfying all constraints.
        for candidate in range(-100, 101):
            subst = Subst({'N': intToken(candidate)})
            if all(_eval_pred(subst(c)) for c in cterm.constraints):
                return subst
        return None


def _eval_pred(term: KInner) -> bool | None:
    """Evaluate a ground ML predicate over integers, or `None` if not ground."""
    if isinstance(term, KApply):
        if term.label.name == '#Not':
            inner = _eval_pred(term.args[0])
            return None if inner is None else not inner
        if term.label.name == '#Equals':
            lhs, rhs = term.args
            lhs_b, rhs_b = _eval_bool(lhs), _eval_bool(rhs)
            if lhs_b is None or rhs_b is None:
                return None
            return lhs_b == rhs_b
    return None


def _eval_bool(term: KInner) -> bool | None:
    if term == TRUE:
        return True
    if term == FALSE:
        return False
    if isinstance(term, KApply) and term.label.name == '_<=Int_':
        lhs, rhs = term.args
        if isinstance(lhs, KToken) and isinstance(rhs, KToken):
            return int(lhs.token) <= int(rhs.token)
    return None


def _engine() -> ConcolicEngine:
    return ConcolicEngine(cast('CTermSymbolic', FakeSymbolic()), input_vars=['N'])


def _init() -> CTerm:
    return cast('CTerm', FakeCTerm('if'))


def _pc(cterm: CTerm) -> str:
    return cast('FakeCTerm', cterm).pc


def test_trace_follows_else_branch() -> None:
    engine = _engine()
    trace = engine.trace(_init(), Subst({'N': intToken(10)}))
    assert trace.status == 'terminal'
    assert _pc(trace.final) == 'else'
    assert len(trace.path) == 1
    assert trace.path[0].condition == _COND_ELSE


def test_trace_follows_then_branch() -> None:
    engine = _engine()
    trace = engine.trace(_init(), Subst({'N': intToken(3)}))
    assert _pc(trace.final) == 'then'
    assert trace.path[0].condition == _COND_THEN


def test_flip_branch_synthesizes_diverging_input() -> None:
    engine = _engine()
    init = _init()
    trace = engine.trace(init, Subst({'N': intToken(10)}))

    new_inputs = engine.flipped_inputs(init, trace)

    assert len(new_inputs) == 1
    value = new_inputs[0]['N']
    assert isinstance(value, KToken)
    assert int(value.token) <= 5
    # And the flipped input drives the other branch.
    assert _pc(engine.trace(init, new_inputs[0]).final) == 'then'


def test_explore_discovers_both_paths() -> None:
    engine = _engine()
    traces = engine.explore(_init(), Subst({'N': intToken(10)}))
    assert len(traces) == 2
    assert {_pc(t.final) for t in traces} == {'then', 'else'}
    assert len({t.signature for t in traces}) == 2
