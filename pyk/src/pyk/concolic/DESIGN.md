# Concolic execution — design

This document records the design of the `pyk.concolic` engine and the backend work it depends on.
It is the agreed target (**v1**); the code currently in the package is an intermediate **v0** (see
*Current status*).

## Goals

1. **Accelerate symbolic execution.** Use a fast, deterministic *concrete* run to pin down a single
   path, so the symbolic side does not search for applicable rules, fork at every branch, or spend
   an SMT call per branch deciding feasibility.
2. **Bug / assertion reproduction.** Systematically generate concrete inputs that drive execution
   down every feasible path until a target is hit (a stuck state, a failing assertion, a target cell
   pattern); the input that reaches it is the witness.

## Background: the two engines today

K already provides both halves concolic needs, against one kompiled definition:

- **Concrete:** the LLVM backend (directly, or inside Booster) rewrites ground terms fast.
- **Symbolic:** the Haskell backend / Booster, exposed over Kore JSON-RPC (`execute`, `simplify`,
  `implies`, `get-model`), keeps inputs symbolic and branches when a guard is undecided.

Crucially, rule identities (`rule_id`, a per-rule hash) are shared across these backends because they
come from the same kompiled definition. This is what lets a trace recorded on one side drive the
other.

## Core idea: reuse the concrete trace

A concrete run collapses input-derived values to concretes, so it cannot, by itself, recover a
*symbolic* path condition (`if (10 <= 5)` does not record that the `10` came from input `N`). The
symbolic input must be propagated somewhere. Instead of re-running a full *search-based* symbolic
execution (which forks and prunes), we **replay the exact rule sequence the concrete run took**,
applying those rules to a symbolic configuration. The path is already known, so the replay is
deterministic — no search, no forking, no per-branch feasibility SMT.

```
 CONCRETE PASS (ground input, deterministic — no fork)
   execute(config[N := 10])  ->  ordered rule-id trace:  [.. , var, <=, if-false, assign, ..]
                                          │  reuse the rule sequence
                                          ▼
 SYMBOLIC REPLAY (N stays symbolic; apply exactly those rules)
   at each branch:  the fired rule's guard, instantiated over N, is the path constraint
                    NO search, NO fork, NO per-branch SMT
```

## The path-exploration algorithm (DART, remainder-driven)

A program's executions form a tree: every input-dependent branch splits it. Each root→leaf path is
one *path condition*; the goal is one concrete input per feasible leaf.

```
                      n <= 5 ?
                   /            \
            true (N<=5)       false (¬N<=5)
              |                   |
          n <= 10 ?            n <= 10 ?
           /      \             /      \
       true      false      true      false
     N<=5∧N<=10 N<=5∧¬N<=10 ¬N<=5∧N<=10 ¬N<=5∧¬N<=10
      N=3 ✓      UNSAT ✗     N=7 ✓       N=11 ✓
```

(example: `if (n<=5) {a=1;} else {a=0;}  if (n<=10) {b=1;} else {b=0;}`)

### `ck` and `rk`

At the k-th branch node, the backend applies the rule `R` the concrete trace selected and returns two
**predicates over the symbolic input** (not concrete values):

| symbol | name | meaning | example (if-false taken, N=10) |
|---|---|---|---|
| `ck` | applied | the condition under which `R` fires (its instantiated `requires` / match) | `ck = ¬(N <=Int 5)` |
| `rk` | remainder | the subspace where `R` does **not** fire — the sibling branch(es) | `rk = (N <=Int 5)` |

- For a binary boolean branch, `rk = ¬ck`. For multi-way / `owise`, `rk` is the union of the other
  siblings — which is why the backend should compute it rather than the engine negating `ck`.
- `ck`/`rk` are *formulas*; a concrete value comes only from solving them.

### The loop

```
worklist = [seed_input];  seen = {}            # seen keyed by path-condition signature
while worklist and budget remains:
    input = worklist.pop()
    rule_trace = concrete_run(init, input)     # ordered rule_ids (deterministic)
    prefix = []                                 # accumulated applied conditions
    for each step k in guided_replay(init, rule_trace):   # symbolic, no fork
        ck, rk = step.applied, step.remainder
        prefix.append(ck)
        if rk is satisfiable:                   # this is a branch node
            N' = solve(prefix_{<k} ∧ rk)        # same path until k, then the other side
            worklist.push(N')                   # N' provably reaches the sibling branch
    record path-condition signature in seen (skip if already seen)
# stop when every remainder is ⊥ (tree exhausted) or a bound is hit
```

- `prefix_{<k}` is the conjunction of applied conditions *before* step k. `solve(prefix_{<k} ∧ rk)`
  yields an input that follows the same path up to k, then diverges — guaranteed feasible, so every
  generated input explores a genuinely new path (the "directed" in DART).
- Infeasible branches are pruned for free: their `rk` is UNSAT, so no input is produced
  (e.g. `N<=5 ∧ ¬(N<=10)` above).
- SMT is spent **only at branch nodes** (testing `rk` / extracting a model) — never in the forward
  replay.

### Worked example (seed N=3)

1. `N=3`: concrete takes (n≤5 true, n≤10 true). Replay: at B1 `rk=¬(N≤5)` → solve → `N=6` queued; at
   B2 `prefix={N≤5}`, `solve(N≤5 ∧ ¬(N≤10))` = UNSAT → pruned. Signature `{N≤5, N≤10}`.
2. `N=6`: (n≤5 false, n≤10 true). At B2 `solve(¬(N≤5) ∧ ¬(N≤10))` → `N=11` queued. Signature
   `{¬N≤5, N≤10}`.
3. `N=11`: (false, false). At B2 `solve(¬(N≤5) ∧ N≤10)` → `N=7` queued. Signature `{¬N≤5, ¬N≤10}`.
4. Remaining inputs rediscover seen signatures and are skipped.

Result: the three feasible leaves `{N≤5,N≤10}`, `{¬N≤5,N≤10}`, `{¬N≤5,¬N≤10}` are found; the
infeasible leaf is never generated.

## Architecture: where is the symbolic input propagated?

| | who propagates `N` | backend change | avoids re-search? |
|---|---|---|---|
| **C** (today's v0) | Haskell `execute` re-explores (forks) | none | no — forks internally |
| **A** (v1, chosen) | Haskell applies the *named* rule, one step, no search | Haskell: guided-step | yes |
| **B** (long term) | LLVM carries a symbolic shadow, emits the path condition in one run | LLVM: concolic mode | yes (no Haskell on the forward path) |

**Decision: Option A for v1.** It is the smallest change with the biggest conceptual payoff and keeps
rule application (matching, hooks, predicate instantiation) in the backend that already does it.

## v1 contract: the guided-step RPC

Extend the Kore RPC with a *guided* mode (a new option on `execute`, or a new `replay` method): given a
symbolic term and the rule-id sequence from the concrete run, apply those rules **deterministically**.

```
request:
  term:      <symbolic configuration>
  rule-ids:  [id0, id1, ...]          # the concrete trace's rule sequence

per applied rule, return:
  rewritten-term:        <symbolic successor>
  applied-predicate:     ck           # R's instantiated guard (accumulate into the path condition)
  remainder-predicate:   rk           # subspace where R does not apply (sibling branches)

final: rewritten-term after the last rule
```

Semantics: for each id, match `R`'s LHS against the current term, rewrite, and return `ck`/`rk`. **Do
not** search other rules, **do not** branch, **do not** run a feasibility SMT check — feasibility is
witnessed by the concrete run. Booster already computes remainders internally (for `owise` / hand-off
decisions), so returning `rk` is close to free.

## Engine data flow

```
ConcolicEngine
  concrete_trace(init, input)   -> rule-id sequence            (KoreClient.execute, ground, logs)
  trace(init, input)            -> ConcolicTrace               (guided-step replay; collect ck, rk)
        for each branch node with SAT rk:  queue solve(prefix ∧ rk)   (get-model)
  explore(init, seed)           -> [ConcolicTrace]             (worklist + signature dedup)
```

Branch discovery and the diverging input both come from the sibling (remainder) predicates `rk`
recorded at each branch node, instead of the engine post-hoc negating the chosen condition. The
sibling predicates are already returned by the existing `execute` (each successor carries its
`rule_predicate`), so **the remainder-driven loop needs no backend change** — see *Current status* and
*Milestones*. The guided-step backend feature is a performance optimization on top of this.

## Backend changes required

**Haskell backend / Booster (v1, optimization — not required for correctness):**

The remainder-driven loop already works on the existing `execute`: at a branch, Booster returns each
successor with its `rule_predicate` (the siblings = `rk`), and it already computes a *remainder
predicate* internally (`Rewrite.hs`: `RewriteBranch` is returned only when a rule group's remainder is
unsatisfiable; a satisfiable remainder currently *aborts*). The optimization:

- A guided/forced-rule mode on `execute` (extra request field) that, given the concrete trace's rule
  sequence, applies the named rule per step **without** the per-branch feasibility SMT (feasibility is
  witnessed by the concrete run), and surfaces the `remainder-predicate` Booster already computes
  (including the fall-through/`owise` region it currently aborts on) so the engine can also generate
  inputs for it. Surface: `kore-rpc-types/Types.hs`, `booster/JsonRpc.hs`, `booster/JsonRpc/Utils.hs`,
  `kore/JsonRpc.hs`, plus pyk's `KoreClient`.

**LLVM backend (v2 / v3, optional optimizations):**

- *v2:* expose an LLVM rule-ordinal → `rule_id` (unique-id) mapping (or emit unique-ids in proof
  hints) so the concrete trace can be sourced from fast LLVM proof hints instead of a Booster ground
  run. Hints already carry rule events (ordinal + substitution) and side-condition results.
- *v3:* a full concolic mode (symbolic shadow / taint) in the LLVM interpreter that emits the symbolic
  path condition during a single concrete run — removes Haskell from the forward path entirely.

## Milestones

- **v1 (done, no backend change):** concrete pass via ground `execute`; symbolic replay via existing
  `execute`, selecting the branch by matching `rule_id` against the concrete trace; **remainder-driven**
  diverging-input generation (`diverging_inputs`) using the sibling `rule_predicate`s returned at each
  branch. Works on legacy + Booster; the backend still forks/checks feasibility internally.
- **v1.1 (optimization):** guided/forced-rule mode on `execute` so the forward replay skips per-branch
  feasibility SMT and surfaces Booster's remainder (incl. the `owise` fall-through it currently aborts on).
- **v2:** LLVM proof hints (+ ordinal→id) as the concrete-trace source for a faster concrete pass.
- **v3:** LLVM concolic mode (Option B).

Suggested next implementation step (v1.1): a spike confirming the forced-rule + remainder contract on
Booster on the IMP example, then wiring the engine's replay onto it.

## Current status (v1, remainder-driven)

`_engine.py` implements: `concrete_trace` (ground run → rule-id sequence), `trace` (symbolic replay
selecting branches via `rule_id` matching, recording each chosen condition `ck` and the sibling
remainder conditions `rk`), `diverging_inputs` (solve `prefix ∧ rk` per sibling), and `explore`
(worklist + signature dedup). It is
validated by `src/tests/unit/test_concolic.py` (trace-matching logic) and
`src/tests/integration/concolic/test_imp_concolic.py` (end-to-end on IMP, single- and two-branch
programs, legacy + Booster — the two-branch test confirms exactly the three feasible leaves are found
and the UNSAT one is pruned). The next (v1.1) step replaces the internal `execute`-and-select with the
forced-rule mode so the forward replay drops per-branch feasibility SMT.

## Scope & limitations

- A path's feasibility is established by a real concrete run, so branch selection needs no SMT; only
  spawning a diverging input does.
- Loops/recursion make the path tree unbounded; exploration is bounded by `max_step`, `max_branches`,
  and `max_iterations`.
- v1 still relies on the symbolic backend for the forward replay (one guided step per rule). Removing
  that dependency is v3 (Option B).
