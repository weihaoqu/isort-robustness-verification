(*
Histogram(D: dataset, m: num_bins)
    h := array of m zeros
    for i = 0 to n-1:
        bin := D[i]
        h[bin] := h[bin] + 1
    return h
*)

(*
PROPERTY: L1 Sensitivity 2 under Replace Metric

Replace metric: D1 and D2 differ in exactly one element (at position k).
  - D1[k] may differ from D2[k]
  - For all i ≠ k: D1[i] = D2[i]

Claim: ||h(D1) - h(D2)||_1 ≤ 2

================================================================================
RELATIONAL CELL MORPHING
================================================================================

INPUT CELL (distinguished dataset element):
  k:     Distinguished element index (where datasets MAY differ)
  dk1:   D1[k] - bin for element k in dataset 1
  dk2:   D2[k] - bin for element k in dataset 2
  
  PRECONDITION: 0 ≤ dk1, dk2 < m (valid bins)
  CONSTRAINT: ∀i ≠ k: D1[i] = D2[i] (replace metric — implicit in HIT/MISS)
  
  k, dk1, dk2 NEVER CHANGE

OUTPUT CELL (L1 difference):
  l1:    Current ||h1 - h2||_1
  
  POSTCONDITION: l1 ≤ 2

================================================================================
ANALYSIS: How L1 Changes
================================================================================

For MISS (i ≠ k):
  D1[i] = D2[i], so both runs increment the same bin
  L1 unchanged

For HIT (i = k):
  Run 1 increments h1[dk1]
  Run 2 increments h2[dk2]
  
  Sub-case dk1 = dk2 (same bin):
    Both increments go to the same bin
    - Run 1 alone: h1[dk1] += 1, L1 = |1 - 0| = 1
    - Run 2 alone: h2[dk1] += 1, L1 = |0 - 1| = 1  
    - Both: h1[dk1] += 1, h2[dk1] += 1, L1 = |1 - 1| = 0
    
  Sub-case dk1 ≠ dk2 (different bins):
    Increments go to different bins
    - Run 1 alone: h1[dk1] += 1, L1 = |1| + |0| = 1
    - Run 2 alone: h2[dk2] += 1, L1 = |0| + |-1| = 1
    - Both: L1 = |1| + |-1| = 2

================================================================================
SIMPLIFIED MODEL
================================================================================

Since L1 depends on whether dk1 = dk2, and on the order of HITs,
we track:
  - hit1: has run 1 processed element k?
  - hit2: has run 2 processed element k?
  - l1:   current L1 difference

Update rules for l1:
  
  Case dk1 = dk2:
    l1 = |hit1 - hit2|  (0 or 1 during, 0 at end)
    - If hit1 and !hit2: l1 = 1
    - If !hit1 and hit2: l1 = 1
    - If hit1 and hit2:  l1 = 0
    - If !hit1 and !hit2: l1 = 0
  
  Case dk1 ≠ dk2:
    l1 = hit1 + hit2  (0, 1, or 2)
    - l1 increases by 1 each time a HIT occurs
    
At termination: hit1 = hit2 = true
  - If dk1 = dk2: l1 = |1 - 1| = 0 ≤ 2 ✓
  - If dk1 ≠ dk2: l1 = 1 + 1 = 2 ≤ 2 ✓

================================================================================
STATE VARIABLES
================================================================================

  i1, i2      : elements processed (0 to n)
  k           : distinguished element index (NEVER CHANGES)
  dk1, dk2    : D1[k], D2[k] - bins for element k (NEVER CHANGE)
  hit1, hit2  : has element k been processed? (CAN CHANGE)
  l1          : current L1 difference (CAN CHANGE)
  n           : dataset size
*)


(******************************************************************************)
(* INITIALIZATION                                                             *)
(******************************************************************************)

Inv(i1, i2, k, dk1, dk2, hit1:bool, hit2:bool, l1, n) :-
    i1 = 0, i2 = 0,
    n > 0,
    0 <= k, k < n,
    0 <= dk1, 0 <= dk2,
    !hit1, !hit2,
    l1 = 0.


(******************************************************************************)
(* TF TRANSITION - Only run 1 steps                                           *)
(*                                                                            *)
(* HIT (i1 = k):                                                              *)
(*   If dk1 = dk2:                                                            *)
(*     - If !hit2: l1' = 1 (run 1 added, run 2 hasn't)                       *)
(*     - If hit2:  l1' = 0 (both added to same bin, cancels)                 *)
(*   If dk1 ≠ dk2:                                                            *)
(*     - l1' = l1 + 1 (run 1 adds to its bin)                                *)
(*                                                                            *)
(* MISS (i1 ≠ k): l1' = l1 (same bin in both runs, no change)                *)
(******************************************************************************)

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


(******************************************************************************)
(* FT TRANSITION - Only run 2 steps                                           *)
(******************************************************************************)

Inv(i1, i2', k, dk1, dk2, hit1:bool, hit2':bool, l1', n) :-
    Inv(i1, i2, k, dk1, dk2, hit1:bool, hit2:bool, l1, n),
    SchFT(i1, i2, k, dk1, dk2, hit1:bool, hit2:bool, l1, n),
    (
        (* HIT with dk1 = dk2 and hit1: cancels out *)
        i2 < n and i2 = k and dk1 = dk2 and hit1 and
        i2' = i2 + 1 and hit2' and l1' = 0
    ) or (
        (* HIT with dk1 = dk2 and !hit1: l1 becomes 1 *)
        i2 < n and i2 = k and dk1 = dk2 and !hit1 and
        i2' = i2 + 1 and hit2' and l1' = 1
    ) or (
        (* HIT with dk1 ≠ dk2: l1 increases by 1 *)
        i2 < n and i2 = k and dk1 <> dk2 and
        i2' = i2 + 1 and hit2' and l1' = l1 + 1
    ) or (
        (* MISS: no change *)
        i2 < n and i2 <> k and
        i2' = i2 + 1 and
        (hit2' and hit2 or !hit2' and !hit2) and
        l1' = l1
    ) or (
        (* Finished *)
        i2 >= n and i2' = i2 and
        (hit2' and hit2 or !hit2' and !hit2) and
        l1' = l1
    ).


(******************************************************************************)
(* TT TRANSITION - Both runs step                                             *)
(******************************************************************************)

Inv(i1', i2', k, dk1, dk2, hit1':bool, hit2':bool, l1', n) :-
    Inv(i1, i2, k, dk1, dk2, hit1:bool, hit2:bool, l1, n),
    SchTT(i1, i2, k, dk1, dk2, hit1:bool, hit2:bool, l1, n),
    (
        (* HIT-HIT with dk1 = dk2: both add to same bin, l1 = 0 *)
        i1 < n and i1 = k and i2 < n and i2 = k and dk1 = dk2 and
        i1' = i1 + 1 and i2' = i2 + 1 and hit1' and hit2' and l1' = 0
    ) or (
        (* HIT-HIT with dk1 ≠ dk2: both add to different bins, l1 += 2 *)
        i1 < n and i1 = k and i2 < n and i2 = k and dk1 <> dk2 and
        i1' = i1 + 1 and i2' = i2 + 1 and hit1' and hit2' and l1' = l1 + 2
    ) or (
        (* HIT-MISS with dk1 = dk2 and hit2: run 1 cancels existing diff *)
        i1 < n and i1 = k and i2 < n and i2 <> k and dk1 = dk2 and hit2 and
        i1' = i1 + 1 and i2' = i2 + 1 and hit1' and
        (hit2' and hit2 or !hit2' and !hit2) and l1' = 0
    ) or (
        (* HIT-MISS with dk1 = dk2 and !hit2: l1 becomes 1 *)
        i1 < n and i1 = k and i2 < n and i2 <> k and dk1 = dk2 and !hit2 and
        i1' = i1 + 1 and i2' = i2 + 1 and hit1' and
        (hit2' and hit2 or !hit2' and !hit2) and l1' = 1
    ) or (
        (* HIT-MISS with dk1 ≠ dk2: l1 += 1 *)
        i1 < n and i1 = k and i2 < n and i2 <> k and dk1 <> dk2 and
        i1' = i1 + 1 and i2' = i2 + 1 and hit1' and
        (hit2' and hit2 or !hit2' and !hit2) and l1' = l1 + 1
    ) or (
        (* MISS-HIT with dk1 = dk2 and hit1: run 2 cancels existing diff *)
        i1 < n and i1 <> k and i2 < n and i2 = k and dk1 = dk2 and hit1 and
        i1' = i1 + 1 and i2' = i2 + 1 and
        (hit1' and hit1 or !hit1' and !hit1) and hit2' and l1' = 0
    ) or (
        (* MISS-HIT with dk1 = dk2 and !hit1: l1 becomes 1 *)
        i1 < n and i1 <> k and i2 < n and i2 = k and dk1 = dk2 and !hit1 and
        i1' = i1 + 1 and i2' = i2 + 1 and
        (hit1' and hit1 or !hit1' and !hit1) and hit2' and l1' = 1
    ) or (
        (* MISS-HIT with dk1 ≠ dk2: l1 += 1 *)
        i1 < n and i1 <> k and i2 < n and i2 = k and dk1 <> dk2 and
        i1' = i1 + 1 and i2' = i2 + 1 and
        (hit1' and hit1 or !hit1' and !hit1) and hit2' and l1' = l1 + 1
    ) or (
        (* MISS-MISS: no change *)
        i1 < n and i1 <> k and i2 < n and i2 <> k and
        i1' = i1 + 1 and i2' = i2 + 1 and
        (hit1' and hit1 or !hit1' and !hit1) and
        (hit2' and hit2 or !hit2' and !hit2) and
        l1' = l1
    ) or (
        (* HIT-Finished *)
        i1 < n and i1 = k and i2 >= n and dk1 = dk2 and hit2 and
        i1' = i1 + 1 and i2' = i2 and hit1' and
        (hit2' and hit2 or !hit2' and !hit2) and l1' = 0
    ) or (
        i1 < n and i1 = k and i2 >= n and dk1 = dk2 and !hit2 and
        i1' = i1 + 1 and i2' = i2 and hit1' and
        (hit2' and hit2 or !hit2' and !hit2) and l1' = 1
    ) or (
        i1 < n and i1 = k and i2 >= n and dk1 <> dk2 and
        i1' = i1 + 1 and i2' = i2 and hit1' and
        (hit2' and hit2 or !hit2' and !hit2) and l1' = l1 + 1
    ) or (
        (* Finished-HIT *)
        i1 >= n and i2 < n and i2 = k and dk1 = dk2 and hit1 and
        i1' = i1 and i2' = i2 + 1 and
        (hit1' and hit1 or !hit1' and !hit1) and hit2' and l1' = 0
    ) or (
        i1 >= n and i2 < n and i2 = k and dk1 = dk2 and !hit1 and
        i1' = i1 and i2' = i2 + 1 and
        (hit1' and hit1 or !hit1' and !hit1) and hit2' and l1' = 1
    ) or (
        i1 >= n and i2 < n and i2 = k and dk1 <> dk2 and
        i1' = i1 and i2' = i2 + 1 and
        (hit1' and hit1 or !hit1' and !hit1) and hit2' and l1' = l1 + 1
    ) or (
        (* MISS-Finished, Finished-MISS, Finished-Finished: no change *)
        (i1 >= n or i1 <> k) and (i2 >= n or i2 <> k) and
        (i1 < n and i1' = i1 + 1 or i1 >= n and i1' = i1) and
        (i2 < n and i2' = i2 + 1 or i2 >= n and i2' = i2) and
        (hit1' and hit1 or !hit1' and !hit1) and
        (hit2' and hit2 or !hit2' and !hit2) and
        l1' = l1
    ).


(******************************************************************************)
(* SCHEDULER                                                                  *)
(******************************************************************************)

i1 < n :-
    Inv(i1, i2, k, dk1, dk2, hit1:bool, hit2:bool, l1, n),
    SchTF(i1, i2, k, dk1, dk2, hit1:bool, hit2:bool, l1, n),
    i2 < n.

i2 < n :-
    Inv(i1, i2, k, dk1, dk2, hit1:bool, hit2:bool, l1, n),
    SchFT(i1, i2, k, dk1, dk2, hit1:bool, hit2:bool, l1, n),
    i1 < n.

SchTF(i1, i2, k, dk1, dk2, hit1:bool, hit2:bool, l1, n),
SchFT(i1, i2, k, dk1, dk2, hit1:bool, hit2:bool, l1, n),
SchTT(i1, i2, k, dk1, dk2, hit1:bool, hit2:bool, l1, n) :-
    Inv(i1, i2, k, dk1, dk2, hit1:bool, hit2:bool, l1, n),
    i1 < n or i2 < n.


(******************************************************************************)
(* GOAL: L1 Sensitivity 2                                                     *)
(*                                                                            *)
(* Violation: l1 > 2 should be UNSAT                                         *)
(******************************************************************************)

l1 > 2 :-
    Inv(i1, i2, k, dk1, dk2, hit1:bool, hit2:bool, l1, n),
    n <= i1, n <= i2.


(******************************************************************************)
(* TEST QUERIES                                                               *)
(******************************************************************************)

(*
(* Test 1: L1 ≤ 2 achievable - should be SAT *)
l1 <= 2 :-
    Inv(i1, i2, k, dk1, dk2, hit1:bool, hit2:bool, l1, n),
    n <= i1, n <= i2.

(* Test 2: L1 = 2 when dk1 ≠ dk2 - should be SAT *)
l1 = 2 :-
    Inv(i1, i2, k, dk1, dk2, hit1:bool, hit2:bool, l1, n),
    n <= i1, n <= i2, dk1 <> dk2.

(* Test 3: L1 = 0 when dk1 = dk2 - should be SAT *)
l1 = 0 :-
    Inv(i1, i2, k, dk1, dk2, hit1:bool, hit2:bool, l1, n),
    n <= i1, n <= i2, dk1 = dk2.

(* Test 4: L1 > 0 when dk1 = dk2? - should be UNSAT *)
l1 > 0 :-
    Inv(i1, i2, k, dk1, dk2, hit1:bool, hit2:bool, l1, n),
    n <= i1, n <= i2, dk1 = dk2.

(* Test 5: Sensitivity 1 too tight - should be SAT *)
l1 > 1 :-
    Inv(i1, i2, k, dk1, dk2, hit1:bool, hit2:bool, l1, n),
    n <= i1, n <= i2.
*)
