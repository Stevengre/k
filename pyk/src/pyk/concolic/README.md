# Concolic execution (proof-of-concept)

This package is a **proof-of-concept** concolic (concrete + symbolic) execution engine
built on top of pyk's existing symbolic-execution interface, `CTermSymbolic`.

It does **not** add a new backend. It orchestrates the K symbolic backend (Kore RPC /
Haskell backend or Booster) to follow the single path picked out by a *concrete* input,
records the branch conditions encountered along that path (the *path condition*), and then
uses the backend's SMT solver to synthesize new concrete inputs that drive execution down
previously unexplored branches — the classic DART/SAGE loop.

## How it works

Given an initial symbolic configuration with some free *input variables* and a concrete
assignment to them, `ConcolicEngine` does three things:

1. **`trace(init, concrete_input)`** — Steps the configuration with `CTermSymbolic.execute`.
   At each branch point, it substitutes the concrete input into each candidate branch
   condition and simplifies it; the branch that simplifies to `#Top` is the one the concrete
   input takes. The taken conditions accumulate into the trace's *path condition*.

2. **`flipped_inputs(init, trace)`** — For each branch `i` along the recorded path, it builds
   the constraint set `c_0 & … & c_(i-1) & ¬c_i` and asks `CTermSymbolic.get_model` for a
   satisfying assignment over the input variables. Each feasible model is a new concrete input
   that diverges from `trace` at branch `i`.

3. **`explore(init, seed_input)`** — A bounded worklist loop: trace an input, enqueue the
   inputs produced by flipping its branches, skip inputs whose path condition was already seen,
   and stop after `max_iterations`. The result is one trace per distinct path discovered.

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
            M1["trace(init, concrete_input)<br/>follow concrete path + collect path condition"]
            M2["flipped_inputs(init, trace)<br/>negate path prefix -> solve for new inputs"]
            M3["explore(init, seed_input)<br/>worklist loop + path dedup"]
        end
        subgraph Helpers["Internal helpers"]
            H1["_select_branch<br/>pick the branch the concrete input takes"]
            H2["_holds_under<br/>substitute concrete value, simplify to truth"]
            H3["_restrict_to_inputs<br/>trim model to input variables"]
        end
        subgraph Data["Data types"]
            D1["ConcolicTrace<br/>(input, path, final, status)"]
            D2["PathConstraint<br/>(condition, depth)"]
        end
        E --> API
        API --> Helpers
        API --> Data
    end

    subgraph Pyk["pyk symbolic-execution interface (existing)"]
        CS["CTermSymbolic"]
        CS1["execute()<br/>step/branch -> next_states + branch conditions"]
        CS2["kast_simplify()<br/>simplify predicate -> #Top / #Bottom"]
        CS3["get_model()<br/>SMT solve -> Subst model"]
        CS --> CS1 & CS2 & CS3
    end

    subgraph Backend["K symbolic backend (Kore RPC)"]
        KC["KoreClient (JSON-RPC)"]
        SRV["kore-rpc (legacy Haskell backend)<br/>/ kore-rpc-booster (Booster)"]
        Z3["Z3 SMT solver"]
        KC --> SRV --> Z3
    end

    T -->|"trace / explore"| E
    M1 --> CS1
    H1 --> CS1
    H2 --> CS2
    M2 --> CS3
    CS --> KC

    classDef new fill:#d4f7d4,stroke:#2a8a2a,color:#000;
    class Concolic,E,API,Helpers,Data,M1,M2,M3,H1,H2,H3,D1,D2 new;
```

## Exploration flow

```mermaid
flowchart TD
    Start(["explore(init, seed_input)"]) --> Init["worklist = [seed_input]<br/>seen_signatures = empty<br/>traces = []"]
    Init --> Cond{"worklist non-empty<br/>and len(traces) < max_iterations?"}
    Cond -->|no| Done(["return traces<br/>(one per distinct path)"])
    Cond -->|yes| Pop["input = worklist.pop(0)"]

    Pop --> Trace["trace(init, input)"]

    subgraph TraceLoop["trace: walk one path for the concrete input"]
        direction TB
        TS["cterm = init, path = []"] --> Ex["CTermSymbolic.execute(cterm)"]
        Ex --> Br{"next_states?"}
        Br -->|"none (terminal/stuck)"| TEnd["status = terminal<br/>return ConcolicTrace"]
        Br -->|"one (cut-point)"| Follow["follow that state"] --> Ex
        Br -->|"many (branching)"| Sel["_select_branch:<br/>substitute concrete value into each<br/>branch condition, _holds_under -> simplify"]
        Sel --> Pick["pick the matching branch<br/>path.append(condition)<br/>cterm = that branch state"] --> Ex
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
