# Histogram Sensitivity: Verification with Relational Cell Morphing

A step-by-step tutorial explaining the PCSAT encoding for verifying L1 sensitivity 2 under the replace metric.

---

## Verification Results

| Goal | Result | Time | Meaning |
|------|--------|------|---------|
| `l1 > 2` | **UNSAT** | 6.6s | **Sensitivity ≤ 2 VERIFIED ✓** |
| `l1 <= 2` | **SAT** | - | Bound achievable ✓ |

---

## Part 1: The Algorithm

```
Histogram(D: dataset, m: num_bins)
    h := array of m zeros
    for i = 0 to n-1:
        bin := D[i]           // Element i maps to bin D[i]
        h[bin] := h[bin] + 1  // Increment that bin's count
    return h
```

### What It Does

- Input: Dataset D with n elements, each element is a bin index in [0, m)
- Output: Histogram h where h[b] = count of elements mapping to bin b

### Example

```
D = [2, 0, 1, 2, 0]  (n=5 elements, m=3 bins)

Processing:
  D[0]=2: h[2]++  →  h = [0, 0, 1]
  D[1]=0: h[0]++  →  h = [1, 0, 1]
  D[2]=1: h[1]++  →  h = [1, 1, 1]
  D[3]=2: h[2]++  →  h = [1, 1, 2]
  D[4]=0: h[0]++  →  h = [2, 1, 2]

Output: h = [2, 1, 2]
```

---

## Part 2: The Property — L1 Sensitivity under Replace Metric

### Replace Metric (Neighboring Datasets)

Two datasets D1 and D2 are **neighbors** if they differ in exactly one element:

```
∃k. D1[k] ≠ D2[k]  AND  ∀i ≠ k. D1[i] = D2[i]
```

- Position k: D1[k] may differ from D2[k]
- All other positions: identical

### L1 Sensitivity

```
Sensitivity = max         ||h(D1) - h(D2)||_1
              D1,D2 neighbors

where ||h1 - h2||_1 = Σ_b |h1[b] - h2[b]|
```

### Claim: Sensitivity = 2

We want to prove:
```
∀D1, D2 neighbors.  ||h(D1) - h(D2)||_1 ≤ 2
```

---

## Part 3: Why Sensitivity is 2 — Informal Proof

Let k be the position where D1 and D2 may differ.
Let dk1 = D1[k] and dk2 = D2[k].

### Case 1: dk1 = dk2 (same bin)

```
Element k maps to the SAME bin in both datasets.

Run 1: h1[dk1] += 1
Run 2: h2[dk2] += 1  (but dk2 = dk1, so same bin!)

Result: h1[dk1] = h2[dk1]
L1 = 0  ✓
```

### Case 2: dk1 ≠ dk2 (different bins)

```
Element k maps to DIFFERENT bins in the two datasets.

Run 1: h1[dk1] += 1  →  h1[dk1] = h2[dk1] + 1
Run 2: h2[dk2] += 1  →  h2[dk2] = h1[dk2] + 1

Differences:
  |h1[dk1] - h2[dk1]| = |1 - 0| = 1
  |h1[dk2] - h2[dk2]| = |0 - 1| = 1
  All other bins: equal (MISS elements go to same bin)

L1 = 1 + 1 = 2  ✓
```

### What About MISS Elements (i ≠ k)?

```
For all i ≠ k: D1[i] = D2[i]  (by replace metric!)

So MISS elements go to the SAME bin in both runs.
Both h1[D1[i]] and h2[D2[i]] increment by 1.
Net contribution to L1: 0
```

**This is the key insight**: The replace metric ensures MISS elements don't contribute to L1!

---

## Part 4: Relational Cell Morphing Structure

```
┌─────────────────────────────────────────────────────────────────────────┐
│  INPUT CELL (distinguished dataset element)                             │
│  ───────────────────────────────────────────                            │
│                                                                         │
│  k:     Distinguished index (position where datasets MAY differ)        │
│  dk1:   D1[k] — bin for element k in dataset 1                         │
│  dk2:   D2[k] — bin for element k in dataset 2                         │
│                                                                         │
│  PRECONDITION: 0 ≤ dk1, dk2 < m (valid bins)                           │
│  CONSTRAINT: ∀i ≠ k: D1[i] = D2[i] (replace metric — implicit!)        │
│                                                                         │
│  k, dk1, dk2 NEVER CHANGE                                              │
│                                                                         │
├─────────────────────────────────────────────────────────────────────────┤
│  OUTPUT CELL (L1 difference)                                            │
│  ───────────────────────────────────────                                │
│                                                                         │
│  l1:    Current ||h1 - h2||_1                                          │
│                                                                         │
│  POSTCONDITION: l1 ≤ 2                                                  │
│                                                                         │
│  l1 CAN CHANGE during execution                                         │
│                                                                         │
└─────────────────────────────────────────────────────────────────────────┘
```

### How the Replace Metric is Encoded

The constraint "∀i ≠ k: D1[i] = D2[i]" is **NOT stated explicitly**.

Instead, it's captured **implicitly** through the HIT/MISS abstraction:

- **HIT (i = k)**: We process the distinguished element. D1[k] and D2[k] may differ (dk1 vs dk2).
- **MISS (i ≠ k)**: We process some other element. By the replace metric, D1[i] = D2[i], so both runs increment the same bin. L1 unchanged.

This is the elegance of cell morphing — we don't track the full datasets!

---

## Part 5: HIT/MISS Abstraction

### When Processing Element i:

```
┌─────────────────────────────────────────────────────────────────────────┐
│  HIT (i = k): Process the DISTINGUISHED element                         │
│  ──────────────────────────────────────────────                         │
│                                                                         │
│  Run 1 increments h1[dk1]                                               │
│  Run 2 increments h2[dk2]                                               │
│                                                                         │
│  Effect on L1 depends on whether dk1 = dk2:                            │
│                                                                         │
│  ┌────────────────────────────────────────────────────────────────┐    │
│  │ Sub-case: dk1 = dk2 (same bin)                                  │    │
│  │                                                                 │    │
│  │   Both runs increment the SAME bin.                            │    │
│  │   - Run 1 HIT alone: l1 = 1 (h1 ahead by 1)                   │    │
│  │   - Run 2 HIT alone: l1 = 1 (h2 ahead by 1)                   │    │
│  │   - Both HIT: l1 = 0 (cancels out!)                           │    │
│  │                                                                 │    │
│  │   At termination: l1 = 0                                       │    │
│  └────────────────────────────────────────────────────────────────┘    │
│                                                                         │
│  ┌────────────────────────────────────────────────────────────────┐    │
│  │ Sub-case: dk1 ≠ dk2 (different bins)                           │    │
│  │                                                                 │    │
│  │   Runs increment DIFFERENT bins.                               │    │
│  │   - Run 1 HIT: l1 += 1 (h1[dk1] increases, h2[dk1] doesn't)   │    │
│  │   - Run 2 HIT: l1 += 1 (h2[dk2] increases, h1[dk2] doesn't)   │    │
│  │                                                                 │    │
│  │   At termination: l1 = 2                                       │    │
│  └────────────────────────────────────────────────────────────────┘    │
│                                                                         │
├─────────────────────────────────────────────────────────────────────────┤
│  MISS (i ≠ k): Process some OTHER element                               │
│  ────────────────────────────────────────────                           │
│                                                                         │
│  By replace metric: D1[i] = D2[i]                                       │
│  Both runs increment the SAME bin.                                      │
│                                                                         │
│  Effect on L1: UNCHANGED (l1' = l1)                                    │
│                                                                         │
│  This is why MISS is simple — no contribution to sensitivity!          │
│                                                                         │
└─────────────────────────────────────────────────────────────────────────┘
```

---

## Part 6: State Variables

```prolog
Inv(i1, i2, k, dk1, dk2, hit1:bool, hit2:bool, l1, n)
```

| Variable | Type | Meaning | Changes? |
|----------|------|---------|----------|
| `i1` | int | Elements processed in run 1 | Yes (0 → n) |
| `i2` | int | Elements processed in run 2 | Yes (0 → n) |
| `k` | int | Distinguished element index | **Never** |
| `dk1` | int | D1[k] — bin for element k in run 1 | **Never** |
| `dk2` | int | D2[k] — bin for element k in run 2 | **Never** |
| `hit1` | bool | Has run 1 processed element k? | Yes (false → true) |
| `hit2` | bool | Has run 2 processed element k? | Yes (false → true) |
| `l1` | int | Current L1 difference | Yes |
| `n` | int | Dataset size | **Never** |

### Invariant

```
l1 = ||h1 - h2||_1 at current point in execution

Specifically:
  If dk1 = dk2:
    l1 = |hit1 - hit2|  ∈ {0, 1}
    (1 if exactly one has processed k, 0 otherwise)
    
  If dk1 ≠ dk2:
    l1 = (hit1 ? 1 : 0) + (hit2 ? 1 : 0)  ∈ {0, 1, 2}
    (counts how many runs have processed k)
```

---

## Part 7: Initialization

```prolog
Inv(i1, i2, k, dk1, dk2, hit1:bool, hit2:bool, l1, n) :-
    i1 = 0, i2 = 0,
    n > 0,
    0 <= k, k < n,
    0 <= dk1, 0 <= dk2,
    !hit1, !hit2,
    l1 = 0.
```

### What This Says

1. **`i1 = 0, i2 = 0`**: No elements processed yet
2. **`n > 0`**: Dataset has at least one element
3. **`0 <= k, k < n`**: Distinguished index is valid
4. **`0 <= dk1, 0 <= dk2`**: Bin indices are non-negative
5. **`!hit1, !hit2`**: Element k not yet processed in either run
6. **`l1 = 0`**: Initial L1 difference is 0 (empty histograms are equal)

---

## Part 8: TF Transition (Run 1 Steps)

```prolog
Inv(i1', i2, k, dk1, dk2, hit1':bool, hit2:bool, l1', n) :-
    Inv(i1, i2, k, dk1, dk2, hit1:bool, hit2:bool, l1, n),
    SchTF(i1, i2, k, dk1, dk2, hit1:bool, hit2:bool, l1, n),
    (
        (* HIT with dk1 = dk2 and hit2: cancels out *)
        i1 < n and i1 = k and dk1 = dk2 and hit2 and
        i1' = i1 + 1 and hit1' and l1' = 0
    ) or (
        (* HIT with dk1 = dk2 and !hit2: l1 becomes 1 *)
        i1 < n and i1 = k and dk1 = dk2 and !hit2 and
        i1' = i1 + 1 and hit1' and l1' = 1
    ) or (
        (* HIT with dk1 ≠ dk2: l1 increases by 1 *)
        i1 < n and i1 = k and dk1 <> dk2 and
        i1' = i1 + 1 and hit1' and l1' = l1 + 1
    ) or (
        (* MISS: no change *)
        i1 < n and i1 <> k and
        i1' = i1 + 1 and
        (hit1' and hit1 or !hit1' and !hit1) and
        l1' = l1
    ) or (
        (* Finished *)
        i1 >= n and i1' = i1 and
        (hit1' and hit1 or !hit1' and !hit1) and
        l1' = l1
    ).
```

### Case-by-Case Analysis

**Case 1: HIT with dk1 = dk2 and hit2 already true**
```
Run 2 already processed k (added to bin dk2 = dk1).
Now run 1 processes k (adds to bin dk1).
Both added to same bin → cancels out.
l1' = 0
```

**Case 2: HIT with dk1 = dk2 and hit2 false**
```
Run 2 hasn't processed k yet.
Run 1 processes k (adds to bin dk1).
h1[dk1] is now 1 ahead of h2[dk1].
l1' = 1
```

**Case 3: HIT with dk1 ≠ dk2**
```
Bins are different.
Run 1 processes k (adds to bin dk1).
h1[dk1] increases by 1, h2[dk1] unchanged.
l1' = l1 + 1
```

**Case 4: MISS**
```
Processing element i ≠ k.
D1[i] = D2[i] by replace metric.
Both runs will add to same bin.
l1' = l1 (unchanged)
```

**Case 5: Finished**
```
i1 >= n, nothing to process.
l1' = l1
```

---

## Part 9: Why hit1/hit2 Preservation Uses Explicit Cases

You might wonder why we write:
```prolog
(hit1' and hit1 or !hit1' and !hit1)
```

Instead of `hit1' = hit1`.

**Reason**: PCSAT doesn't allow boolean assignment `b' = b`.

This pattern explicitly says "hit1' has the same value as hit1":
- If `hit1` is true, then `hit1'` must be true
- If `hit1` is false, then `hit1'` must be false

---

## Part 10: TT Transition — Key Cases

The TT transition handles all combinations. The most important cases:

### HIT-HIT with dk1 = dk2

```prolog
i1 < n and i1 = k and i2 < n and i2 = k and dk1 = dk2 and
i1' = i1 + 1 and i2' = i2 + 1 and hit1' and hit2' and l1' = 0
```

Both runs process k simultaneously, both add to the same bin.
Net effect: l1 = 0 (perfect cancellation).

### HIT-HIT with dk1 ≠ dk2

```prolog
i1 < n and i1 = k and i2 < n and i2 = k and dk1 <> dk2 and
i1' = i1 + 1 and i2' = i2 + 1 and hit1' and hit2' and l1' = l1 + 2
```

Both runs process k simultaneously, but add to different bins.
Net effect: l1 increases by 2.

### MISS-MISS

```prolog
i1 < n and i1 <> k and i2 < n and i2 <> k and
... and l1' = l1
```

Both runs process non-k elements.
By replace metric, both add to the same bin.
l1 unchanged.

---

## Part 11: Goal Clause

```prolog
l1 > 2 :-
    Inv(i1, i2, k, dk1, dk2, hit1:bool, hit2:bool, l1, n),
    n <= i1, n <= i2.
```

### What This Asks

"At termination (both runs finished), is it possible that l1 > 2?"

### Interpretation

- **UNSAT**: NO such state exists → **Sensitivity ≤ 2 VERIFIED ✓**
- **SAT**: Such a state exists → Property does NOT hold

---

## Part 12: Correctness Argument

### Why l1 ≤ 2 at Termination

At termination, both runs have processed all n elements, including element k.
So `hit1 = true` and `hit2 = true`.

**Case dk1 = dk2:**
```
Both runs added 1 to the same bin (dk1 = dk2).
These cancel out.
l1 = 0 ≤ 2 ✓
```

**Case dk1 ≠ dk2:**
```
Run 1 added 1 to bin dk1.
Run 2 added 1 to bin dk2.
|h1[dk1] - h2[dk1]| = 1
|h1[dk2] - h2[dk2]| = 1
All other bins: equal (MISS elements, same bin by replace metric)
l1 = 1 + 1 = 2 ≤ 2 ✓
```

### Why MISS Elements Don't Contribute

The replace metric guarantees: ∀i ≠ k. D1[i] = D2[i]

So for MISS elements, both runs increment the **same bin**.
This means h1[b] and h2[b] both increase by 1.
The difference |h1[b] - h2[b]| is unchanged.

**This is the key property that makes the encoding work!**

---

## Part 13: Visual Summary

```
┌─────────────────────────────────────────────────────────────────────────┐
│                 HISTOGRAM SENSITIVITY VERIFICATION                       │
├─────────────────────────────────────────────────────────────────────────┤
│                                                                         │
│  INPUT: Two neighboring datasets D1, D2 (replace metric)               │
│                                                                         │
│    D1 = [a, b, c, dk1, e, f, ...]     (element k has value dk1)        │
│    D2 = [a, b, c, dk2, e, f, ...]     (element k has value dk2)        │
│              ↑   ↑   ↑   ↑    ↑                                         │
│             same same  k  same same    ← Replace metric!               │
│                                                                         │
│  Distinguished element k: dk1 = D1[k], dk2 = D2[k]                     │
│  ┌─────────────────────────────────────────────────────────────┐       │
│  │  PRECONDITION: Only position k may differ                   │       │
│  │  k, dk1, dk2 NEVER CHANGE                                   │       │
│  └─────────────────────────────────────────────────────────────┘       │
│                           │                                             │
│                           ▼                                             │
│  ┌─────────────────────────────────────────────────────────────┐       │
│  │                    HISTOGRAM ALGORITHM                       │       │
│  │                                                              │       │
│  │  For each element i:                                         │       │
│  │                                                              │       │
│  │    ┌─────────────────────────────────────────────────┐      │       │
│  │    │ HIT (i = k):                                    │      │       │
│  │    │   Run 1 increments h1[dk1]                      │      │       │
│  │    │   Run 2 increments h2[dk2]                      │      │       │
│  │    │                                                 │      │       │
│  │    │   If dk1 = dk2: same bin, cancels → l1 = 0     │      │       │
│  │    │   If dk1 ≠ dk2: diff bins → l1 += 1 per run    │      │       │
│  │    ├─────────────────────────────────────────────────┤      │       │
│  │    │ MISS (i ≠ k):                                   │      │       │
│  │    │   D1[i] = D2[i] by replace metric!             │      │       │
│  │    │   Both runs increment same bin                  │      │       │
│  │    │   l1 UNCHANGED                                  │      │       │
│  │    └─────────────────────────────────────────────────┘      │       │
│  │                                                              │       │
│  └─────────────────────────────────────────────────────────────┘       │
│                           │                                             │
│                           ▼                                             │
│  OUTPUT: L1 difference = ||h1 - h2||_1                                 │
│  ┌─────────────────────────────────────────────────────────────┐       │
│  │  POSTCONDITION: l1 ≤ 2                                      │       │
│  │                                                              │       │
│  │  At termination:                                            │       │
│  │    dk1 = dk2 → l1 = 0  ✓                                   │       │
│  │    dk1 ≠ dk2 → l1 = 2  ✓                                   │       │
│  │                                                              │       │
│  │  VERIFIED! ✓  (goal l1 > 2 returns UNSAT)                  │       │
│  └─────────────────────────────────────────────────────────────┘       │
│                                                                         │
└─────────────────────────────────────────────────────────────────────────┘
```

---

## Part 14: Comparison with Kruskal

| Aspect | Kruskal | Histogram |
|--------|---------|-----------|
| **Property** | (N-1)-robust MST cost | L1 sensitivity 2 |
| **INPUT cell** | `k, wk1, wk2` (edge weights) | `k, dk1, dk2` (bin indices) |
| **OUTPUT cell** | `c1, c2` (MST costs) | `l1` (L1 difference) |
| **HIT effect** | `c1' = c1 + wk1` (explicit) | `l1' = l1 + 1` or complex |
| **MISS effect** | Unknown weight, bounded by ε | `l1' = l1` (exactly 0!) |
| **Final bound** | (N-1)·ε (grows with N) | 2 (constant!) |
| **Why bound holds** | Each edge ≤ ε, N-1 edges | At most 2 bins differ |

### Key Difference

**Kruskal**: MISS contributes **unknown amount bounded by ε**
- We don't know the exact edge weight
- But we know it's within ε of the other run

**Histogram**: MISS contributes **exactly 0**
- Replace metric guarantees D1[i] = D2[i] for i ≠ k
- Same bin incremented in both runs
- Perfect cancellation

This makes histogram simpler in some ways — MISS has no uncertainty!

---

## Part 15: Key Takeaways

1. **Replace metric is implicit**: We don't state "∀i ≠ k. D1[i] = D2[i]" explicitly. Instead, MISS elements implicitly go to the same bin because that's what replace metric guarantees.

2. **Two distinguished cells**:
   - INPUT: `k, dk1, dk2` (never change)
   - OUTPUT: `l1` (tracks current L1 difference)

3. **HIT is where the action is**: Only element k contributes to L1 difference. MISS elements contribute nothing.

4. **Sensitivity is constant**: Unlike Kruskal where bound grows with N, histogram sensitivity is always ≤ 2, regardless of dataset size.

5. **dk1 = dk2 case**: If element k maps to the same bin in both datasets, there's no difference at all (l1 = 0).

6. **dk1 ≠ dk2 case**: Maximum sensitivity of 2, achieved when element k maps to different bins.

---

## Part 16: Test Queries

```prolog
(* Test 1: L1 ≤ 2 achievable - should be SAT *)
l1 <= 2 :-
    Inv(...), n <= i1, n <= i2.

(* Test 2: L1 = 2 when dk1 ≠ dk2 - should be SAT *)
l1 = 2 :-
    Inv(...), n <= i1, n <= i2, dk1 <> dk2.

(* Test 3: L1 = 0 when dk1 = dk2 - should be SAT *)
l1 = 0 :-
    Inv(...), n <= i1, n <= i2, dk1 = dk2.

(* Test 4: L1 > 0 when dk1 = dk2? - should be UNSAT *)
l1 > 0 :-
    Inv(...), n <= i1, n <= i2, dk1 = dk2.

(* Test 5: Sensitivity 1 too tight - should be SAT (violation reachable) *)
l1 > 1 :-
    Inv(...), n <= i1, n <= i2.
```

| Test | Expected | Meaning |
|------|----------|---------|
| `l1 > 2` | **UNSAT** | Sensitivity ≤ 2 verified |
| `l1 <= 2` | **SAT** | Bound achievable |
| `l1 = 2` with `dk1 <> dk2` | **SAT** | Max sensitivity achieved |
| `l1 = 0` with `dk1 = dk2` | **SAT** | Same bin → no diff |
| `l1 > 0` with `dk1 = dk2` | **UNSAT** | Same bin → must be 0 |
| `l1 > 1` | **SAT** | Sensitivity 1 too tight |

---

*Verified: UNSAT for l1 > 2 (6.6s), SAT for l1 <= 2.*
