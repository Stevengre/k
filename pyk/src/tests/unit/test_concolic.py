from __future__ import annotations

from dataclasses import dataclass
from typing import TYPE_CHECKING, cast

from pyk.concolic import ConcolicEngine
from pyk.kast.inner import Subst
from pyk.kast.prelude.kint import intToken
from pyk.kore.rpc import LogRewrite, RewriteFailure, RewriteSuccess

if TYPE_CHECKING:
    from pyk.cterm.symbolic import CTermSymbolic
    from pyk.kore.rpc import LogEntry, State


# ---------------------------------------------------------------------------
# These unit tests target the trace-guided "brain" of the engine -- the pure
# logic that reuses a concrete rule trace to drive branch selection -- without
# a kompiled definition or a Kore server. The full two-pass flow (concrete
# pass -> symbolic replay -> flip) is covered by the IMP integration test.
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class _FakeState:
    """Minimal stand-in for `kore.rpc.State`; `_match_branch` only reads `rule_id`."""

    rule_id: str | None


def _states(*rule_ids: str | None) -> list[State]:
    return [cast('State', _FakeState(rid)) for rid in rule_ids]


def _engine() -> ConcolicEngine:
    return ConcolicEngine(cast('CTermSymbolic', object()), input_vars=['N'])


# --- branch selection by matching the concrete rule trace --------------------


def test_match_branch_picks_rule_from_trace() -> None:
    # Candidates are the two branch successors; the concrete trace took 'else'.
    states = _states('then-id', 'else-id')
    chosen, idx = ConcolicEngine._match_branch(states, ('lookup', 'le', 'else-id', 'assign'), 0)
    assert chosen is not None
    assert chosen.rule_id == 'else-id'
    assert idx == 3  # pointer advanced past the matched entry


def test_match_branch_respects_start_index() -> None:
    # An earlier 'else-id' in the trace must be ignored once the pointer has moved past it.
    states = _states('then-id', 'else-id')
    chosen, idx = ConcolicEngine._match_branch(states, ('else-id', 'then-id'), 1)
    assert chosen is not None
    assert chosen.rule_id == 'then-id'
    assert idx == 2


def test_match_branch_handles_loops() -> None:
    # The same branch rule taken twice (a loop) is consumed one occurrence per call.
    states = _states('body-id', 'exit-id')
    trace = ('body-id', 'body-id', 'exit-id')

    first, idx = ConcolicEngine._match_branch(states, trace, 0)
    assert first is not None and first.rule_id == 'body-id' and idx == 1

    second, idx = ConcolicEngine._match_branch(states, trace, idx)
    assert second is not None and second.rule_id == 'body-id' and idx == 2

    third, idx = ConcolicEngine._match_branch(states, trace, idx)
    assert third is not None and third.rule_id == 'exit-id' and idx == 3


def test_match_branch_no_match_returns_none() -> None:
    states = _states('then-id', 'else-id')
    chosen, idx = ConcolicEngine._match_branch(states, ('lookup', 'le', 'assign'), 0)
    assert chosen is None
    assert idx == 0  # pointer unchanged


# --- harvesting the concrete trace from rewrite logs -------------------------


def test_rewrite_rule_ids_extracts_successes_in_order() -> None:
    logs: list[LogEntry] = [
        LogRewrite(origin=cast('object', None), result=RewriteSuccess(rule_id='r1')),  # type: ignore[arg-type]
        LogRewrite(origin=cast('object', None), result=RewriteFailure(rule_id='r2', reason='nope')),  # type: ignore[arg-type]
        LogRewrite(origin=cast('object', None), result=RewriteSuccess(rule_id='r3')),  # type: ignore[arg-type]
    ]
    assert ConcolicEngine._rewrite_rule_ids(logs) == ['r1', 'r3']


def test_rewrite_rule_ids_ignores_non_rewrite_entries() -> None:
    @dataclass
    class _Other:
        pass

    logs: list[LogEntry] = [
        cast('LogEntry', _Other()),
        LogRewrite(origin=cast('object', None), result=RewriteSuccess(rule_id='r1')),  # type: ignore[arg-type]
    ]
    assert ConcolicEngine._rewrite_rule_ids(logs) == ['r1']


# --- model restriction -------------------------------------------------------


def test_restrict_to_inputs_keeps_only_input_vars() -> None:
    engine = _engine()
    model = Subst({'N': intToken(3), 'GENERATED_COUNTER_CELL': intToken(9)})
    restricted = engine._restrict_to_inputs(model)
    assert dict(restricted) == {'N': intToken(3)}
