from __future__ import annotations

import os
import time
from typing import TYPE_CHECKING, Any

import pytest

from pyk.concolic import ConcolicEngine
from pyk.cterm import CTerm
from pyk.kast.inner import KApply, KSequence, KToken, KVariable, Subst
from pyk.kast.prelude.kint import intToken
from pyk.kore.rpc import BranchingResult
from pyk.testing import CTermSymbolicTest, KPrintTest

from ..utils import K_FILES

if TYPE_CHECKING:
    from pyk.cterm import CTermSymbolic
    from pyk.ktool.kprint import KPrint


class TestConcolicBenchmark(CTermSymbolicTest, KPrintTest):
    """Benchmark scaling the concolic engine over k sequential conditionals."""

    KOMPILE_MAIN_FILE = K_FILES / 'imp.k'
    DISABLE_LEGACY = True

    @staticmethod
    def _build_program(k: int) -> str:
        """Build a program of k sequential conditionals with monotone thresholds 1..k.

        Args:
            k: Number of sequential conditionals.

        Returns:
            IMP program string with k if-else statements over variable n.
        """
        stmts = []
        for i in range(1, k + 1):
            stmts.append(f'if (n <= {i}) {{ x{i} = 1 ; }} else {{ x{i} = 0 ; }}')
        return ' '.join(stmts)

    @staticmethod
    def _build_state_map(k: int) -> str:
        """Build the state map token string for k variables plus n.

        Args:
            k: Number of x-variables (x1..xk).

        Returns:
            Map token string for parse_token.
        """
        parts = ['#token("n","Id") |-> N:Int']
        for i in range(1, k + 1):
            parts.append(f'#token("x{i}","Id") |-> 0')
        return ' '.join(parts)

    @staticmethod
    def config(kprint: KPrint, k: int) -> CTerm:
        """Build the initial CTerm configuration for k conditionals.

        Args:
            kprint: KPrint instance for parsing tokens.
            k: Number of sequential conditionals.

        Returns:
            Initial CTerm with symbolic input N.
        """
        pgm = TestConcolicBenchmark._build_program(k)
        state_str = TestConcolicBenchmark._build_state_map(k)
        k_parsed = kprint.parse_token(KToken(pgm, 'Stmt'), as_rule=False)
        state_parsed = kprint.parse_token(KToken(state_str, 'Map'), as_rule=True)
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

    @pytest.mark.skipif(not os.environ.get('CONCOLIC_BENCH'), reason='benchmark; set CONCOLIC_BENCH=1 to run')
    def test_benchmark(self, cterm_symbolic: CTermSymbolic, kprint: KPrint) -> None:
        """Measure execute vs get_model cost split across scaling family of branchy IMP programs."""
        # Counters shared across closures via mutable dict
        counters: dict[str, Any] = {}

        def reset_counters() -> None:
            counters['n_execute'] = 0
            counters['t_execute'] = 0.0
            counters['n_branching'] = 0
            counters['n_get_model'] = 0
            counters['t_get_model'] = 0.0

        # Save originals before patching
        orig_execute = cterm_symbolic._kore_client.execute
        orig_get_model = cterm_symbolic.get_model

        def wrapped_execute(*args: Any, **kwargs: Any) -> Any:
            counters['n_execute'] += 1
            t0 = time.perf_counter()
            result = orig_execute(*args, **kwargs)
            counters['t_execute'] += time.perf_counter() - t0
            if isinstance(result, BranchingResult):
                counters['n_branching'] += 1
            return result

        def wrapped_get_model(*args: Any, **kwargs: Any) -> Any:
            counters['n_get_model'] += 1
            t0 = time.perf_counter()
            result = orig_get_model(*args, **kwargs)
            counters['t_get_model'] += time.perf_counter() - t0
            return result

        cterm_symbolic._kore_client.execute = wrapped_execute  # type: ignore[method-assign]
        cterm_symbolic.get_model = wrapped_get_model  # type: ignore[method-assign]

        rows: list[tuple[int, int, int, int, float, int, float, float]] = []

        try:
            for k in [1, 2, 3, 4, 5, 6]:
                reset_counters()
                init = self.config(kprint, k)
                engine = ConcolicEngine(cterm_symbolic, input_vars=['N'])

                t0_total = time.perf_counter()
                traces = engine.explore(init, Subst({'N': intToken(0)}))
                t_total = time.perf_counter() - t0_total

                n_paths = len({t.signature for t in traces})
                assert n_paths == k + 1, (
                    f'k={k}: expected {k + 1} paths, got {n_paths}. ' f'traces={[t.signature for t in traces]}'
                )

                rows.append(
                    (
                        k,
                        n_paths,
                        counters['n_execute'],
                        counters['n_branching'],
                        counters['t_execute'],
                        counters['n_get_model'],
                        counters['t_get_model'],
                        t_total,
                    )
                )
        finally:
            cterm_symbolic._kore_client.execute = orig_execute  # type: ignore[method-assign]
            cterm_symbolic.get_model = orig_get_model  # type: ignore[method-assign]

        # Print markdown table
        header = '| k | paths | n_execute | n_branching | t_execute(s) | n_get_model | t_get_model(s) | t_total(s) |'
        sep = '|---|-------|-----------|-------------|--------------|-------------|----------------|------------|'
        print()
        print(header)
        print(sep)
        for k, n_paths, n_exec, n_branch, t_exec, n_gm, t_gm, t_tot in rows:
            print(f'| {k} | {n_paths} | {n_exec} | {n_branch} | {t_exec:.3f} | {n_gm} | {t_gm:.3f} | {t_tot:.3f} |')

        print()
        print('Per-k breakdown (% of t_total):')
        for k, _n_paths, _n_exec, _n_branch, t_exec, _n_gm, t_gm, t_tot in rows:
            exec_pct = 100.0 * t_exec / t_tot if t_tot > 0 else 0.0
            gm_pct = 100.0 * t_gm / t_tot if t_tot > 0 else 0.0
            print(f'  k={k}: t_execute={exec_pct:.1f}%  t_get_model={gm_pct:.1f}%')
