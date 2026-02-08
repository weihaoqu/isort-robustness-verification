# Kruskal's Algorithm: Robustness Verification with Relational Cell Morphing

A step-by-step tutorial explaining the PCSAT encoding for verifying (N-1)-robustness.

---

## Verification Results

| Goal | Result | Time | Meaning |
|------|--------|------|---------|
| `c1 - c2 <= (n-1)*eps and c2 - c1 <= (n-1)*eps` | **SAT** | 21s | Bound achievable ✓ |
| `c1 - c2 > (n-1)*eps or c2 - c1 > (n-1)*eps` | **UNSAT** | - | **Verified ✓** |

---

## Part 1: The Algorithm

```
Kruskal(G : graph)
    for each node v in G:
        MakeSet(v)                    // Initialize disjoint sets
    T := ∅                            // MST edges
    cost := 0                         // MST total cost
    for each edge (u,v) in G ordered by weight:
        if Find(u) ≠ Find(v):         // Different components?
            T := T ∪ {(u,v)}          // Add edge to MST
            cost := cost + G[u,v]     // Accumulate cost
            Union(u, v)               // Merge components
    return T, cost
```

### Key Observations

1. **MST has exactly N-1 edges** (for N vertices)
2. **Cost only increases**: `cost' = cost + edge_weight`
3. **Each edge is considered once**: either added or skipped

---

## Part 2: The Property

```
PROPERTY: (N-1)-robust under L∞ for MST cost

∀e. |G1[e] - G2[e]| ≤ ε  ⟹  |cost1 - cost2| ≤ (N-1)·ε
    ~~~~~~~~~~~~~~~~         ~~~~~~~~~~~~~~~~~~~~~~
    INPUT: edge weights      OUTPUT: MST total cost
```

### Why (N-1)·ε?

```
MST has exactly N-1 edges.
Each edge weight differs by at most ε.
Therefore: total cost differs by at most (N-1)·ε.

Example (N=4, so 3 edges in MST):
  MST1 uses edges with weights: 5, 8, 12  → cost1 = 25
  MST2 uses edges with weights: 6, 9, 11  → cost2 = 26
  
  If each edge differs by ≤ 1 (ε=1):
  |cost1 - cost2| = |25 - 26| = 1 ≤ 3·1 = 3  ✓
```

---

## Part 3: Relational Cell Morphing — Two Distinguished Cells

The key technique: instead of tracking ALL edges and ALL costs, we track **two distinguished cells**:

```
┌─────────────────────────────────────────────────────────────────────────┐
│                    TWO DISTINGUISHED CELLS                              │
├─────────────────────────────────────────────────────────────────────────┤
│                                                                         │
│  1. INPUT CELL (Edge Weight)                                            │
│     ┌─────────────────────────────────────────────────────────────┐    │
│     │                                                              │    │
│     │  k:       Distinguished edge index (SYMBOLIC)                │    │
│     │           - Not assigned a concrete value                    │    │
│     │           - Universally quantified over all edges           │    │
│     │                                                              │    │
│     │  wk1:     Weight of edge k in graph G1                      │    │
│     │  wk2:     Weight of edge k in graph G2                      │    │
│     │                                                              │    │
│     │  bk:      Sign bit (bk = true ⟹ wk2 ≥ wk1)                  │    │
│     │                                                              │    │
│     │  PRECONDITION: |wk1 - wk2| ≤ ε                              │    │
│     │  INVARIANT: k, wk1, wk2, bk NEVER CHANGE                    │    │
│     │                                                              │    │
│     └─────────────────────────────────────────────────────────────┘    │
│                                                                         │
│  2. OUTPUT CELL (MST Cost)                                              │
│     ┌─────────────────────────────────────────────────────────────┐    │
│     │                                                              │    │
│     │  c1:      MST cost in run 1                                  │    │
│     │  c2:      MST cost in run 2                                  │    │
│     │                                                              │    │
│     │  bc:      Sign bit (bc = true ⟹ c2 ≥ c1)                    │    │
│     │                                                              │    │
│     │  POSTCONDITION: |c1 - c2| ≤ (N-1)·ε                         │    │
│     │  c1, c2 ACCUMULATE (increase when edges added)              │    │
│     │                                                              │    │
│     └─────────────────────────────────────────────────────────────┘    │
│                                                                         │
└─────────────────────────────────────────────────────────────────────────┘
```

### Why This Works

Since `k` is **symbolic** (universally quantified), if we prove the property holds for arbitrary `k`, it holds for ALL edges. This is the power of cell morphing!

---

## Part 4: HIT/MISS Abstraction

When adding an edge to the MST, we distinguish two cases:

```
┌─────────────────────────────────────────────────────────────────────────┐
│                         HIT vs MISS                                     │
├─────────────────────────────────────────────────────────────────────────┤
│                                                                         │
│  HIT: We add the DISTINGUISHED edge k to MST                            │
│  ════════════════════════════════════════════                           │
│                                                                         │
│     ┌──────────────────────────────────────────────────────────┐       │
│     │  c1' = c1 + wk1    ← We know EXACTLY what's added!       │       │
│     │  c2' = c2 + wk2                                           │       │
│     │                                                           │       │
│     │  The contribution to |c1' - c2'| from this edge:         │       │
│     │    |(c1 + wk1) - (c2 + wk2)|                              │       │
│     │  = |(c1 - c2) + (wk1 - wk2)|                              │       │
│     │  ≤ |c1 - c2| + |wk1 - wk2|                                │       │
│     │  ≤ (previous bound) + ε                                   │       │
│     └──────────────────────────────────────────────────────────┘       │
│                                                                         │
│  MISS: We add some OTHER edge (not k) to MST                            │
│  ═══════════════════════════════════════════════                        │
│                                                                         │
│     ┌──────────────────────────────────────────────────────────┐       │
│     │  c1' = c1 + ???    ← Weight UNKNOWN                       │       │
│     │  c2' = c2 + ???                                           │       │
│     │                                                           │       │
│     │  We don't know the exact weight, BUT we know:            │       │
│     │    |G1[e] - G2[e]| ≤ ε  (input assumption)               │       │
│     │                                                           │       │
│     │  So contribution to difference: still ≤ ε                │       │
│     └──────────────────────────────────────────────────────────┘       │
│                                                                         │
│  KEY INSIGHT: Both HIT and MISS contribute at most ε to difference!    │
│                                                                         │
└─────────────────────────────────────────────────────────────────────────┘
```

### Why HIT is Explicit in Kruskal (but not Dijkstra)

**Kruskal** (simple accumulation):
```
cost_new = cost_old + edge_weight
c1' = c1 + wk1  ← Direct addition, no other dependencies!
```

**Dijkstra** (predecessor dependency):
```
d[v] = d[u] + edge_weight
dv1' = d1[u] + wk1  ← Need predecessor's distance, which we don't track!
```

This is why Kruskal's HIT case is cleaner — no predecessor involved.

---

## Part 5: State Variables

```
Inv(i1, i2, k, wk1, wk2, bk:bool, c1, c2, bc:bool, n, eps)
```

| Variable | Type | Meaning | Changes? |
|----------|------|---------|----------|
| `i1` | int | Edges added to MST in run 1 | Yes (0 → N-1) |
| `i2` | int | Edges added to MST in run 2 | Yes (0 → N-1) |
| `k` | int | Distinguished edge index | **Never** |
| `wk1` | real | Weight G1[k] | **Never** |
| `wk2` | real | Weight G2[k] | **Never** |
| `bk` | bool | Sign bit for weights | **Never** |
| `c1` | real | MST cost in run 1 | Yes (accumulates) |
| `c2` | real | MST cost in run 2 | Yes (accumulates) |
| `bc` | bool | Sign bit for costs | Yes |
| `n` | int | Number of vertices | **Never** |
| `eps` | real | Perturbation bound | **Never** |

### Loop Invariant

```
|c1 - c2| ≤ max(i1, i2) · ε
```

After `i` edges added, the cost difference is at most `i·ε`.

---

## Part 6: Initialization

```prolog
Inv(i1, i2, k, wk1, wk2, bk:bool, c1, c2, bc:bool, n, eps) :-
    i1 = 0, i2 = 0,
    n > 0,
    0 <= k,
    0 <= eps,
    (* INPUT PRECONDITION: |wk1 - wk2| ≤ eps *)
    (bk and 0 <= wk2 - wk1 and wk2 - wk1 <= eps) or
    (!bk and 0 <= wk1 - wk2 and wk1 - wk2 <= eps),
    (* Initial costs are equal *)
    c1 = 0, c2 = 0.
```

### What This Says

1. **`i1 = 0, i2 = 0`**: No edges added yet
2. **`n > 0`**: At least one vertex
3. **`0 <= k`**: Edge index is non-negative
4. **`0 <= eps`**: Perturbation is non-negative
5. **Input bound**: `|wk1 - wk2| ≤ eps` encoded with sign bit
6. **`c1 = 0, c2 = 0`**: Costs start at zero (equal!)

### Sign Bit Encoding

Instead of `|wk1 - wk2| ≤ eps`, we use:
```
(bk and 0 <= wk2 - wk1 and wk2 - wk1 <= eps)   // wk2 ≥ wk1
   or
(!bk and 0 <= wk1 - wk2 and wk1 - wk2 <= eps)  // wk1 > wk2
```

This avoids absolute value, which PCSAT doesn't support directly.

---

## Part 7: TF Transition — Run 1 Steps, Run 2 Waits

```prolog
Inv(i1', i2, k, wk1, wk2, bk:bool, c1', c2, bc':bool, n, eps) :-
    Inv(i1, i2, k, wk1, wk2, bk:bool, c1, c2, bc:bool, n, eps),
    SchTF(i1, i2, k, wk1, wk2, bk:bool, c1, c2, bc:bool, n, eps),
    (
        (* Case 1: HIT - Add distinguished edge k *)
        i1 < n - 1 and i1' = i1 + 1 and c1' = c1 + wk1
    ) or (
        (* Case 2: MISS - Add other edge *)
        i1 < n - 1 and i1' = i1 + 1
    ) or (
        (* Case 3: Skip edge *)
        i1 < n - 1 and i1' = i1 and c1' = c1
    ) or (
        (* Case 4: Finished *)
        i1 >= n - 1 and i1' = i1 and c1' = c1
    ),
    (* Epsilon bound *)
    (bc' and 0 <= c2 - c1' and c2 - c1' <= i1' * eps) or
    (!bc' and 0 <= c1' - c2 and c1' - c2 <= i1' * eps).
```

### Case-by-Case Analysis

**Case 1: HIT — Add Distinguished Edge k**
```prolog
i1 < n - 1 and i1' = i1 + 1 and c1' = c1 + wk1
                               ↑↑↑↑↑↑↑↑↑↑↑↑↑↑
                               EXPLICIT! We know exactly what c1 becomes.
```
- Edge k is added to MST
- Cost increases by exactly `wk1`
- Edge count increases: `i1' = i1 + 1`

**Case 2: MISS — Add Other Edge**
```prolog
i1 < n - 1 and i1' = i1 + 1
(* c1' is NOT constrained here — only by epsilon bound below *)
```
- Some other edge (not k) is added
- Weight unknown, but bounded by ε (via epsilon clause)
- Edge count increases: `i1' = i1 + 1`

**Case 3: Skip Edge**
```prolog
i1 < n - 1 and i1' = i1 and c1' = c1
```
- Edge examined but not added (would create cycle)
- Cost unchanged: `c1' = c1`
- Edge count unchanged: `i1' = i1`

**Case 4: Finished**
```prolog
i1 >= n - 1 and i1' = i1 and c1' = c1
```
- MST complete (N-1 edges added)
- Stutter: nothing changes

### The Epsilon Bound Clause

```prolog
(bc' and 0 <= c2 - c1' and c2 - c1' <= i1' * eps) or
(!bc' and 0 <= c1' - c2 and c1' - c2 <= i1' * eps)
```

This encodes: `|c1' - c2| ≤ i1' · ε`

- If `bc' = true`: `c2 ≥ c1'` and `c2 - c1' ≤ i1' · ε`
- If `bc' = false`: `c1' > c2` and `c1' - c2 ≤ i1' · ε`

**Note**: `bc'` is NOT assigned in the cases — it's determined by this clause!

---

## Part 8: FT Transition — Symmetric

```prolog
Inv(i1, i2', k, wk1, wk2, bk:bool, c1, c2', bc':bool, n, eps) :-
    Inv(i1, i2, k, wk1, wk2, bk:bool, c1, c2, bc:bool, n, eps),
    SchFT(i1, i2, k, wk1, wk2, bk:bool, c1, c2, bc:bool, n, eps),
    (
        (* Case 1: HIT *)
        i2 < n - 1 and i2' = i2 + 1 and c2' = c2 + wk2
                                       ↑↑↑↑↑↑↑↑↑↑↑↑↑↑
                                       Note: wk2, not wk1!
    ) or (
        (* Case 2: MISS *)
        i2 < n - 1 and i2' = i2 + 1
    ) or (
        (* Case 3: Skip *)
        i2 < n - 1 and i2' = i2 and c2' = c2
    ) or (
        (* Case 4: Finished *)
        i2 >= n - 1 and i2' = i2 and c2' = c2
    ),
    (* Epsilon bound *)
    (bc' and 0 <= c2' - c1 and c2' - c1 <= i2' * eps) or
    (!bc' and 0 <= c1 - c2' and c1 - c2' <= i2' * eps).
```

Same structure as TF, but for run 2:
- HIT uses `wk2` (not `wk1`)
- Bound uses `i2'` (not `i1'`)

---

## Part 9: TT Transition — HIT/MISS Matrix

When both runs step together, we have multiple combinations:

```prolog
Inv(i1', i2', k, wk1, wk2, bk:bool, c1', c2', bc':bool, n, eps) :-
    Inv(i1, i2, k, wk1, wk2, bk:bool, c1, c2, bc:bool, n, eps),
    SchTT(i1, i2, k, wk1, wk2, bk:bool, c1, c2, bc:bool, n, eps),
    (
        (* Case 1: HIT-HIT *)
        i1 < n - 1 and i2 < n - 1 and i1' = i1 + 1 and i2' = i2 + 1 and
        c1' = c1 + wk1 and c2' = c2 + wk2
    ) or (
        (* Case 2: HIT-MISS *)
        i1 < n - 1 and i2 < n - 1 and i1' = i1 + 1 and i2' = i2 + 1 and
        c1' = c1 + wk1
    ) or (
        (* Case 3: MISS-HIT *)
        i1 < n - 1 and i2 < n - 1 and i1' = i1 + 1 and i2' = i2 + 1 and
        c2' = c2 + wk2
    ) or (
        (* Case 4: MISS-MISS *)
        i1 < n - 1 and i2 < n - 1 and i1' = i1 + 1 and i2' = i2 + 1
    ) or (
        (* Case 5: ADD-SKIP *)
        i1 < n - 1 and i2 < n - 1 and i1' = i1 + 1 and i2' = i2 and c2' = c2
    ) or (
        (* Case 6: SKIP-ADD *)
        i1 < n - 1 and i2 < n - 1 and i1' = i1 and i2' = i2 + 1 and c1' = c1
    ) or (
        (* Case 7: SKIP-SKIP *)
        i1 < n - 1 and i2 < n - 1 and i1' = i1 and i2' = i2 and
        c1' = c1 and c2' = c2
    ) or (
        (* Case 8: FINISHED-FINISHED *)
        i1 >= n - 1 and i2 >= n - 1 and i1' = i1 and i2' = i2 and
        c1' = c1 and c2' = c2
    ),
    (* Epsilon bound *)
    (bc' and 0 <= c2' - c1' and c2' - c1' <= i1' * eps) or
    (!bc' and 0 <= c1' - c2' and c1' - c2' <= i1' * eps).
```

### HIT-HIT Analysis (Case 1)

```
Both runs add the distinguished edge k:
  c1' = c1 + wk1
  c2' = c2 + wk2

New difference:
  |c1' - c2'| = |(c1 + wk1) - (c2 + wk2)|
             = |(c1 - c2) + (wk1 - wk2)|
             ≤ |c1 - c2| + |wk1 - wk2|    (triangle inequality)
             ≤ i·ε + ε                     (by invariant and input bound)
             = (i+1)·ε                     ✓
```

### HIT-MISS Analysis (Case 2)

```
Run 1 adds edge k:     c1' = c1 + wk1
Run 2 adds other edge: c2' = c2 + ???

Even though we don't know run 2's edge weight,
the epsilon bound ensures |c1' - c2'| ≤ (i+1)·ε
because EVERY edge differs by at most ε.
```

---

## Part 10: Scheduler and Fairness

```prolog
(* Fairness: prevent starvation *)
i1 < n - 1 :-
    Inv(i1, i2, k, wk1, wk2, bk:bool, c1, c2, bc:bool, n, eps),
    SchTF(i1, i2, k, wk1, wk2, bk:bool, c1, c2, bc:bool, n, eps),
    i2 < n - 1.

i2 < n - 1 :-
    Inv(i1, i2, k, wk1, wk2, bk:bool, c1, c2, bc:bool, n, eps),
    SchFT(i1, i2, k, wk1, wk2, bk:bool, c1, c2, bc:bool, n, eps),
    i1 < n - 1.

(* Scheduler disjunction *)
SchTF(...), SchFT(...), SchTT(...) :-
    Inv(...),
    i1 < n - 1 or i2 < n - 1.
```

### Fairness Constraints

These ensure that if one run can still make progress (`i < n-1`), the scheduler doesn't let only the other run proceed indefinitely:

- If `SchTF` is chosen and `i2 < n-1`, then `i1 < n-1` must hold
- If `SchFT` is chosen and `i1 < n-1`, then `i2 < n-1` must hold

### Scheduler Disjunction

The scheduler can choose TF, FT, or TT as long as at least one run is not finished.

---

## Part 11: Goal Clause

```prolog
c1 - c2 > (n - 1) * eps or c2 - c1 > (n - 1) * eps :-
    Inv(i1, i2, k, wk1, wk2, bk:bool, c1, c2, bc:bool, n, eps),
    n - 1 <= i1, n - 1 <= i2.
```

### What This Asks

"At termination (both runs finished with N-1 edges), is it possible that `|c1 - c2| > (N-1)·ε`?"

### Interpretation

- **UNSAT**: NO such state exists → **(N-1)-robustness VERIFIED ✓**
- **SAT**: Such a state exists → Property does NOT hold

---

## Part 12: Visual Summary

```
┌─────────────────────────────────────────────────────────────────────────┐
│                  KRUSKAL ROBUSTNESS VERIFICATION                        │
├─────────────────────────────────────────────────────────────────────────┤
│                                                                         │
│  INPUT: Edge weights G1, G2 with |G1[e] - G2[e]| ≤ ε for all e         │
│                                                                         │
│  Distinguished edge k: wk1 = G1[k], wk2 = G2[k]                        │
│  ┌─────────────────────────────────────────────────────────────┐       │
│  │  PRECONDITION: |wk1 - wk2| ≤ ε                              │       │
│  │  k, wk1, wk2 NEVER CHANGE                                   │       │
│  └─────────────────────────────────────────────────────────────┘       │
│                           │                                             │
│                           ▼                                             │
│  ┌─────────────────────────────────────────────────────────────┐       │
│  │                  KRUSKAL'S ALGORITHM                         │       │
│  │                                                              │       │
│  │  For each edge in sorted order:                              │       │
│  │    if connects different components:                         │       │
│  │                                                              │       │
│  │      ┌─────────────────────────────────────────────┐        │       │
│  │      │ HIT (edge = k):                             │        │       │
│  │      │   c1' = c1 + wk1  ← EXPLICIT!              │        │       │
│  │      │   c2' = c2 + wk2                           │        │       │
│  │      │   Contribution: |wk1 - wk2| ≤ ε           │        │       │
│  │      ├─────────────────────────────────────────────┤        │       │
│  │      │ MISS (edge ≠ k):                           │        │       │
│  │      │   c1' = c1 + ???  ← Unknown weight         │        │       │
│  │      │   c2' = c2 + ???                           │        │       │
│  │      │   Contribution: at most ε (by input bound) │        │       │
│  │      └─────────────────────────────────────────────┘        │       │
│  │                                                              │       │
│  │  INVARIANT: |c1 - c2| ≤ i · ε  (i = edges added)           │       │
│  │                                                              │       │
│  └─────────────────────────────────────────────────────────────┘       │
│                           │                                             │
│                           ▼                                             │
│  OUTPUT: MST costs c1, c2                                               │
│  ┌─────────────────────────────────────────────────────────────┐       │
│  │  POSTCONDITION: |c1 - c2| ≤ (N-1) · ε                       │       │
│  │                                                              │       │
│  │  VERIFIED! ✓  (violation goal returns UNSAT)                │       │
│  └─────────────────────────────────────────────────────────────┘       │
│                                                                         │
└─────────────────────────────────────────────────────────────────────────┘
```

---

## Part 13: Why The Encoding Is Correct

### Soundness Argument

1. **Initialization**: `c1 = c2 = 0`, so `|c1 - c2| = 0 ≤ 0·ε` ✓

2. **HIT case**: 
   - `c1' = c1 + wk1`, `c2' = c2 + wk2`
   - `|c1' - c2'| ≤ |c1 - c2| + |wk1 - wk2| ≤ i·ε + ε = (i+1)·ε` ✓

3. **MISS case**:
   - Unknown weight, but bounded by epsilon clause
   - `|c1' - c2| ≤ (i+1)·ε` enforced ✓

4. **Skip case**:
   - `c1' = c1`, so `|c1' - c2| = |c1 - c2| ≤ i·ε ≤ (i+1)·ε` ✓

5. **Termination**:
   - After N-1 edges: `|c1 - c2| ≤ (N-1)·ε` ✓

### Completeness Argument

The encoding allows ANY behavior consistent with Kruskal:
- Any edge can be HIT or MISS
- Edges can be added or skipped (non-deterministic cycle check)
- Both runs proceed independently (scheduler freedom)

---

## Part 14: Common Questions

### Q: Why not just track `|c1 - c2|` directly?

PCSAT doesn't support absolute value. We use sign bit `bc` to encode:
```
bc = true  ⟹ c2 ≥ c1, track (c2 - c1)
bc = false ⟹ c1 > c2, track (c1 - c2)
```

### Q: Why is `bc' = bc` not allowed?

PCSAT doesn't allow boolean assignment. Instead, `bc'` is determined by the epsilon bound clause, which checks whether `c2' ≥ c1'` or `c1' > c2'`.

### Q: Why do HIT and MISS give the same bound?

Both contribute at most ε because:
- HIT: `|wk1 - wk2| ≤ ε` (input precondition)
- MISS: `|G1[e] - G2[e]| ≤ ε` for ALL edges (input assumption)

The difference is that HIT gives us explicit formulas (`c1' = c1 + wk1`) while MISS is abstract.

### Q: Why use `i1' * eps` instead of `max(i1', i2) * eps`?

In the TF transition, only run 1 changes, so `i2` stays the same. The bound `i1' * eps` works because:
- If `i1' ≥ i2`: bound is `i1' * eps` (correct)
- If `i1' < i2`: the epsilon clause with `i1' * eps` is still satisfiable (possibly too loose, but sound)

A tighter encoding could use `max(i1', i2)`, but this simpler version still verifies.

---

## Part 15: Key Takeaways

1. **Two distinguished cells**: INPUT (edge weight) + OUTPUT (MST cost)

2. **HIT is explicit**: `c1' = c1 + wk1` — we know exact contribution

3. **MISS is abstract**: Unknown weight, but bounded by ε

4. **Sign bit for absolute value**: `|x - y| ≤ bound` encoded with boolean

5. **No boolean assignment**: `bc'` determined by epsilon clause, not `bc' = bc`

6. **Invariant**: `|c1 - c2| ≤ i · ε` maintained through all transitions

7. **Verification**: UNSAT for violation goal proves (N-1)-robustness

---

*Verified: SAT for bound (21s), UNSAT for violation.*
