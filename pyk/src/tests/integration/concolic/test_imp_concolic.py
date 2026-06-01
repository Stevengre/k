from __future__ import annotations

from typing import TYPE_CHECKING

from pyk.concolic import ConcolicEngine
from pyk.cterm import CTerm
from pyk.kast.inner import KApply, KSequence, KToken, KVariable, Subst
from pyk.kast.prelude.kint import intToken
from pyk.testing import CTermSymbolicTest, KPrintTest

from ..utils import K_FILES

if TYPE_CHECKING:
    from pyk.cterm import CTermSymbolic
    from pyk.ktool.kprint import KPrint


# A one-branch IMP program over a single symbolic input ``n``:
#   if (n <= 5) { found = 1 ; } else { found = 0 ; }
PGM: str = 'if (n <= 5) { found = 1 ; } else { found = 0 ; }'


class TestImpConcolic(CTermSymbolicTest, KPrintTest):
    KOMPILE_MAIN_FILE = K_FILES / 'imp.k'

    @staticmethod
    def config(kprint: KPrint) -> CTerm:
        # ``n`` is the symbolic input variable ``N:Int``; ``found`` is initialized concretely.
        # The program has no variables, so it parses in program mode; the state map needs rule
        # mode to admit the free variable ``N:Int``.
        k_parsed = kprint.parse_token(KToken(PGM, 'Stmt'), as_rule=False)
        state_parsed = kprint.parse_token(
            KToken('#token("n","Id") |-> N:Int #token("found","Id") |-> 0', 'Map'), as_rule=True
        )
        return CTerm(
            KApply(
                '<generatedTop>',
                KApply(
                    '<T>',
                    (
                        KApply('<k>', KSequence(k_parsed)),
                        KApply('<state>', state_parsed),
                    ),
                ),
                KVariable('GENERATED_COUNTER_CELL'),
            ),
        )

    @staticmethod
    def found_value(kprint: KPrint, cterm: CTerm) -> str:
        return kprint.pretty_print(cterm.cell('STATE_CELL'))

    def test_trace_follows_concrete_branch(self, cterm_symbolic: CTermSymbolic, kprint: KPrint) -> None:
        # Given
        init = self.config(kprint)
        engine = ConcolicEngine(cterm_symbolic, input_vars=['N'])

        # When: n = 10 should take the else branch (found = 0)
        trace = engine.trace(init, Subst({'N': intToken(10)}))

        # Then
        assert trace.status == 'terminal'
        assert len(trace.path) == 1
        assert 'found |-> 0' in self.found_value(kprint, trace.final)

    def test_diverging_input_produces_other_branch(self, cterm_symbolic: CTermSymbolic, kprint: KPrint) -> None:
        # Given
        init = self.config(kprint)
        engine = ConcolicEngine(cterm_symbolic, input_vars=['N'])
        trace = engine.trace(init, Subst({'N': intToken(10)}))

        # When: use remainder-driven diverging_inputs to synthesize an input for the sibling branch
        new_inputs = engine.diverging_inputs(init, trace)

        # Then
        assert len(new_inputs) == 1
        new_input = new_inputs[0]
        assert 'N' in new_input
        new_value = new_input['N']
        assert isinstance(new_value, KToken)
        assert int(new_value.token) <= 5

        # And: re-tracing the diverging input takes the other branch (found = 1)
        new_trace = engine.trace(init, new_input)
        assert new_trace.signature != trace.signature
        assert 'found |-> 1' in self.found_value(kprint, new_trace.final)

    def test_explore_discovers_both_paths(self, cterm_symbolic: CTermSymbolic, kprint: KPrint) -> None:
        # Given
        init = self.config(kprint)
        engine = ConcolicEngine(cterm_symbolic, input_vars=['N'])

        # When
        traces = engine.explore(init, Subst({'N': intToken(10)}))

        # Then: the two feasible branches of the program are both discovered
        assert len(traces) == 2
        signatures = {trace.signature for trace in traces}
        assert len(signatures) == 2


# A two-branch IMP program: two sequential conditionals over a single symbolic input ``n``:
#   if (n <= 5) { a = 1 ; } else { a = 0 ; }
#   if (n <= 10) { b = 1 ; } else { b = 0 ; }
#
# The feasible path leaves are:
#   n<=5  ∧  n<=10   (e.g. N=3)
#   ¬n<=5 ∧  n<=10   (e.g. N=7)
#   ¬n<=5 ∧ ¬n<=10   (e.g. N=11)
#
# The combination n<=5 ∧ ¬n<=10 is UNSAT and must NOT be generated.
TWO_BRANCH_PGM: str = 'if (n <= 5) { a = 1 ; } else { a = 0 ; } if (n <= 10) { b = 1 ; } else { b = 0 ; }'


class TestImpConcolicTwoBranch(CTermSymbolicTest, KPrintTest):
    KOMPILE_MAIN_FILE = K_FILES / 'imp.k'

    @staticmethod
    def config(kprint: KPrint) -> CTerm:
        k_parsed = kprint.parse_token(KToken(TWO_BRANCH_PGM, 'Stmt'), as_rule=False)
        state_parsed = kprint.parse_token(
            KToken(
                '#token("n","Id") |-> N:Int #token("a","Id") |-> 0 #token("b","Id") |-> 0',
                'Map',
            ),
            as_rule=True,
        )
        return CTerm(
            KApply(
                '<generatedTop>',
                KApply(
                    '<T>',
                    (
                        KApply('<k>', KSequence(k_parsed)),
                        KApply('<state>', state_parsed),
                    ),
                ),
                KVariable('GENERATED_COUNTER_CELL'),
            ),
        )

    def test_explore_discovers_exactly_three_feasible_paths(
        self, cterm_symbolic: CTermSymbolic, kprint: KPrint
    ) -> None:
        """Remainder-driven exploration finds the 3 feasible leaves and skips the UNSAT one.

        Seed N=3 (takes both true branches):
        - B1 sibling rk=¬(n<=5): solve prefix=[] ∧ ¬(n<=5) -> N=6 queued
        - B2 sibling rk=¬(n<=10): solve prefix=[n<=5] ∧ ¬(n<=10) = UNSAT -> pruned

        N=6 (false, true):
        - B1 sibling rk=(n<=5): solve prefix=[] ∧ (n<=5) -> rediscovers N=3 path, skipped
        - B2 sibling rk=¬(n<=10): solve prefix=[¬(n<=5)] ∧ ¬(n<=10) -> N=11 queued

        N=11 (false, false):
        - B1 sibling produces N<=5 path (already seen)
        - B2 sibling produces ¬(n<=5)∧(n<=10) path (already seen as N=6)

        Result: exactly 3 distinct path signatures.
        """
        # Given
        init = self.config(kprint)
        engine = ConcolicEngine(cterm_symbolic, input_vars=['N'])

        # When: seed N=3 (both branches take the true side)
        traces = engine.explore(init, Subst({'N': intToken(3)}))

        # Then: exactly 3 distinct feasible paths are discovered
        signatures = {trace.signature for trace in traces}
        assert len(signatures) == 3, f'Expected 3 distinct paths, got {len(signatures)}: {signatures}'

        # All discovered traces must have terminated normally
        for trace in traces:
            assert trace.status == 'terminal', f'Trace did not terminate: {trace.status}'
