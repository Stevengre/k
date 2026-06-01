# Concolic execution (proof-of-concept)

This package is a **proof-of-concept** concolic (concrete + symbolic) execution engine
built on top of pyk's existing symbolic-execution interface, `CTermSymbolic`.

> **Design & roadmap:** see [`DESIGN.md`](DESIGN.md) for the target architecture (the
> remainder-driven DART loop and the Haskell guided-step backend feature). This README documents
> what is implemented today.

It does **not** add a new backend. The defining idea is that a fast, deterministic *concrete*
run produces an execution trace, which is then **reused** to drive a *symbolic* run down the
very same path. Because the concrete trace already records which rule fired at every branch, the
symbolic pass selects each branch by **matching rule ids** — it never asks the SMT solver "which
branch does this input take?". The solver is consulted only at the end, to negate a prefix of
the path condition and synthesize a new input (the classic DART/SAGE loop).

## How it works

Both passes run against the **same** Kore backend, so rule ids share one namespace. Given an
initial symbolic configuration with free *input variables* and a concrete assignment to them:

1. **`concrete_trace(init, concrete_input)`** — Substitute the concrete input into the
   configuration and execute. With the branch-relevant data ground, the run is **deterministic
   (no forking)**, and the ordered rule ids applied are harvested from the rewrite logs. This is
   the *concrete trace*.

2. **`trace(init, concrete_input)`** — Execute with the input left **symbolic**. At each branch,
   follow the successor whose `rule_id` appears next in the concrete trace, recording its guard
   as a path constraint. Branch selection is an O(1) rule-id lookup — **no per-branch SMT /
   simplify call**. (This pass uses the lower-level `KoreClient` directly, because the
   `CTermSymbolic` wrapper drops `rule_id` from successors.)

3. **`flipped_inputs(init, trace)`** — For each branch `i` along the recorded path, build the
   constraint set `c_0 & … & c_(i-1) & ¬c_i` and ask `CTermSymbolic.get_model` for a satisfying
   assignment over the input variables. Each feasible model is a new concrete input that diverges
   from `trace` at branch `i`.

4. **`explore(init, seed_input)`** — A bounded worklist loop: trace an input, enqueue the inputs
   produced by flipping its branches, skip inputs whose path condition was already seen, and stop
   after `max_iterations`. The result is one trace per distinct path discovered.

### Why reuse the trace?

Without the concrete trace, the symbolic engine would have to *decide* at each branch which side
a given input takes — i.e. substitute the value and call the solver/simplifier per candidate.
Reusing the concrete trace replaces that work with a cheap rule-id lookup, and keeps the
expensive solver on the critical path only once per new input (the flip).

> **Honest scope:** this reuses the concrete trace for *branch selection*. The symbolic backend
> still computes the branch split itself (it returns both successors at a branch over the RPC);
> we do not yet stop it from forking. Eliminating that forking entirely would require either
> *concretizing* the branch-deciding term or backend-level support to apply a chosen rule — see
> *Scope and limitations*.

## Architecture

The engine adds no new backend; it orchestrates pyk's existing `CTermSymbolic` interface, which
talks to a running Kore RPC server (the legacy Haskell backend or Booster) and its SMT solver.

```mermaid
flowchart TB
    subgraph User["Caller / tests"]
        T["test_imp_concolic.py / unit tests<br/>build initial symbolic config + seed input"]
    end

    subgraph Concolic["pyk.concolic (this package · PoC)"]
        E["ConcolicEngine"]
        subgraph API["Public methods"]
            M0["concrete_trace(init, input)<br/>ground run -> ordered rule-id trace"]
            M1["trace(init, input)<br/>symbolic replay, select branch by rule-id"]
            M2["flipped_inputs(init, trace)<br/>negate path prefix -> solve for new inputs"]
            M3["explore(init, seed_input)<br/>worklist loop + path dedup"]
        end
        subgraph Helpers["Internal helpers"]
            H1["_match_branch<br/>next successor whose rule-id is next in trace"]
            H2["_rewrite_rule_ids<br/>harvest rule-ids from rewrite logs"]
            H3["_restrict_to_inputs<br/>trim model to input variables"]
        end
        subgraph Data["Data types"]
            D1["ConcolicTrace<br/>(input, path, final, status, rule_trace)"]
            D2["PathConstraint<br/>(condition, depth, rule_id)"]
        end
        E --> API
        API --> Helpers
        API --> Data
    end

    subgraph Pyk["pyk symbolic-execution interface (existing)"]
        CS["CTermSymbolic"]
        CS3["get_model()<br/>SMT solve -> Subst model (only for flips)"]
        CONV["kast_to_kore / kore_to_kast"]
        CS --> CS3 & CONV
    end

    subgraph Backend["K symbolic backend (Kore RPC)"]
        KC["KoreClient (JSON-RPC)<br/>execute() returns next_states w/ rule_id + logs"]
        SRV["kore-rpc (legacy Haskell backend)<br/>/ kore-rpc-booster (Booster)"]
        Z3["Z3 SMT solver"]
        KC --> SRV --> Z3
    end

    T -->|"trace / explore"| E
    M0 -->|"execute ground (no fork) + logs"| KC
    M1 -->|"execute symbolic, read rule_id"| KC
    M2 --> CS3
    E -.->|convert KAST <-> KORE| CONV
    CS --> KC

    classDef new fill:#d4f7d4,stroke:#2a8a2a,color:#000;
    class Concolic,E,API,Helpers,Data,M0,M1,M2,M3,H1,H2,H3,D1,D2 new;
```

## Exploration flow

```mermaid
flowchart TD
    Start(["explore(init, seed_input)"]) --> Init["worklist = [seed_input]<br/>seen_signatures = empty<br/>traces = []"]
    Init --> Cond{"worklist non-empty<br/>and len(traces) < max_iterations?"}
    Cond -->|no| Done(["return traces<br/>(one per distinct path)"])
    Cond -->|yes| Pop["input = worklist.pop(0)"]

    Pop --> Trace["trace(init, input)"]

    subgraph TraceLoop["trace: concrete pass feeds symbolic replay"]
        direction TB
        CP["CONCRETE PASS — concrete_trace(init, input)<br/>execute(config[input := value]) ground, deterministic<br/>harvest ordered rule-ids from rewrite logs"]
        CP --> RT[/"rule_trace = (r0, r1, ..., r_if-false, ...)"/]
        RT --> SP["SYMBOLIC PASS — input stays symbolic<br/>cterm = init, path = []"]
        SP --> Ex["KoreClient.execute(cterm) — symbolic"]
        Ex --> Br{"next_states?"}
        Br -->|"none (terminal/stuck)"| TEnd["status = terminal<br/>return ConcolicTrace"]
        Br -->|"one (cut-point)"| Follow["follow that state"] --> Ex
        Br -->|"many (branching)"| Sel["_match_branch:<br/>pick successor whose rule_id is the<br/>next matching entry in rule_trace<br/>(no SMT/simplify)"]
        Sel --> Pick["path.append(condition, rule_id)<br/>cterm = that successor + its guard"] --> Ex
    end

    Trace --> TraceLoop
    TraceLoop --> Sig{"trace.signature<br/>already in seen?"}
    Sig -->|yes| Cond
    Sig -->|no| Record["seen.add(signature)<br/>traces.append(trace)"]

    Record --> Flip["flipped_inputs(init, trace)"]

    subgraph FlipLoop["flipped_inputs: synthesize diverging inputs"]
        direction TB
        FS["for each branch i on the path"] --> FC["build constraints:<br/>c0 & ... & c(i-1) & not ci"]
        FC --> GM["CTermSymbolic.get_model(constraints)<br/>(Z3 solve)"]
        GM --> Feas{"satisfiable?"}
        Feas -->|yes| Add["trim to input variables<br/>-> new concrete input"]
        Feas -->|no| Skip["skip (branch infeasible)"]
    end

    Flip --> FlipLoop
    FlipLoop --> Enq["enqueue new inputs onto worklist"]
    Enq --> Cond

    classDef accent fill:#fff3cd,stroke:#b8860b,color:#000;
    class Sel,Pick,FC,GM accent;
```

## Example

For the one-branch IMP program

```
if (n <= 5) { found = 1 ; } else { found = 0 ; }
```

with `n` symbolic, seeding the engine with `n = 10` (the `else` branch) yields a flipped input
`n ≤ 5` (the `then` branch), and `explore` discovers both feasible paths. See
`src/tests/integration/concolic/test_imp_concolic.py` for the end-to-end version and
`src/tests/unit/test_concolic.py` for a toolchain-free unit test of the orchestration logic.

## Scope and limitations

This is a deliberately small PoC:

- **Single concrete path per trace.** Branch selection assumes branches are mutually exclusive
  and that the concrete input determines exactly one (true for ground integer guards like the
  IMP example).
- **No coverage metric or smart search heuristic.** `explore` is a plain breadth-first
  worklist bounded by `max_iterations`; it is not coverage-guided.
- **No CLI yet.** The engine is a library only. A `kpyk concolic` entry point and a
  coverage-guided search strategy are natural follow-ups.
- **Loops/recursion** are bounded only by `max_step` / `max_branches`; unbounded loops are not
  handled specially.

## Running the tests

```
# Toolchain-free unit test of the engine orchestration (run from pyk/)
uv run -- pytest src/tests/unit/test_concolic.py

# End-to-end test (run from pyk/; needs a `kompile` + Kore RPC server matching this source
# tree -- e.g. `kup install k --version v7.1.322`). Exercises both the legacy Haskell backend
# and the Booster server.
uv run -- pytest src/tests/integration/concolic/test_imp_concolic.py
```
