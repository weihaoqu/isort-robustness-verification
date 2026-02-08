(*
CDF(D: dataset, m: num_bins)
    h := Histogram(D, m)
    c := array of m zeros
    c[0] := h[0]
    for b = 1 to m-1:
        c[b] := c[b-1] + h[b]
    return c

Equivalently: c[b] = count of elements i where D[i] <= b
*)

(*
PROPERTY: L1 Sensitivity |dk2 - dk1| under Replace Metric

Replace metric: D1 and D2 differ at exactly one position k.
  D1[k] = dk1 (bin for element k in dataset 1)
  D2[k] = dk2 (bin for element k in dataset 2)
  For all i ≠ k: D1[i] = D2[i]

================================================================================
ANALYSIS
================================================================================

CDF definition: c[b] = number of elements with value <= b

For element k:
  - In run 1: contributes +1 to c1[b] for all b >= dk1
  - In run 2: contributes +1 to c2[b] for all b >= dk2

WLOG assume dk1 <= dk2:
  
  Bins b < dk1:      c1[b] = c2[b]     (neither run counts k)
  Bins dk1 <= b < dk2: c1[b] = c2[b] + 1 (only run 1 counts k)
  Bins b >= dk2:     c1[b] = c2[b]     (both runs count k)

L1 = Σ_b |c1[b] - c2[b]| = |dk2 - dk1|

Maximum L1 = m - 1 (when dk1 = 0, dk2 = m-1)

For MISS elements (i ≠ k):
  D1[i] = D2[i], so same contribution to both CDFs.
  L1 unchanged.

================================================================================
RELATIONAL CELL MORPHING
================================================================================

INPUT CELL (distinguished dataset element):
  k:     Distinguished element index
  dk1:   D1[k] - bin for element k in dataset 1
  dk2:   D2[k] - bin for element k in dataset 2
  
  k, dk1, dk2 NEVER CHANGE

OUTPUT CELL (L1 difference):
  l1:    Current ||c1 - c2||_1
  
  POSTCONDITION: l1 <= |dk2 - dk1|

================================================================================
KEY INSIGHT
================================================================================

Unlike histogram where L1 ∈ {0, 2}, CDF L1 = |dk2 - dk1|.

The L1 comes from the "gap" between dk1 and dk2:
  - If dk1 = dk2: L1 = 0 (same bin, no difference)
  - If dk1 ≠ dk2: L1 = |dk2 - dk1| (the range of bins where only one run counts k)

================================================================================
STATE VARIABLES
================================================================================

  i1, i2      : elements processed (0 to n)
  k           : distinguished element index (NEVER CHANGES)
  dk1, dk2    : bins for element k (NEVER CHANGE)
  hit1, hit2  : has element k been processed? (CAN CHANGE)
  l1          : current L1 difference (CAN CHANGE)
  n           : dataset size
  m           : number of bins

Note: We use sign bit bd to track whether dk1 <= dk2 or dk1 > dk2.
      |dk2 - dk1| = (dk2 - dk1) if bd, else (dk1 - dk2)
*)


(******************************************************************************)
(* INITIALIZATION                                                             *)
(******************************************************************************)

Inv(i1, i2, k, dk1, dk2, bd:bool, hit1:bool, hit2:bool, l1, n, m) :-
    i1 = 0, i2 = 0,
    n > 0, m > 0,
    0 <= k, k < n,
    0 <= dk1, dk1 < m,
    0 <= dk2, dk2 < m,
    (* bd encodes sign of dk2 - dk1 *)
    (bd and dk2 >= dk1) or (!bd and dk1 > dk2),
    !hit1, !hit2,
    l1 = 0.


(******************************************************************************)
(* TF TRANSITION - Only run 1 steps                                           *)
(*                                                                            *)
(* HIT (i1 = k):                                                              *)
(*   Run 1 processes element k, which has bin dk1.                            *)
(*   This means c1[b] += 1 for all b >= dk1.                                 *)
(*                                                                            *)
(*   Effect on L1:                                                            *)
(*   - If dk1 = dk2: no difference (both will count k in same bins)          *)
(*   - If dk1 < dk2 and !hit2: l1 += (dk2 - dk1)                             *)
(*     (run 1 counts k in bins [dk1, dk2-1], run 2 doesn't yet)              *)
(*   - If dk1 < dk2 and hit2: l1 = 0                                          *)
(*     (run 2 already counted, now run 1 catches up → cancels)               *)
(*   - If dk1 > dk2 and !hit2: l1 += (dk1 - dk2)                             *)
(*   - If dk1 > dk2 and hit2: l1 = 0                                          *)
(*                                                                            *)
(* MISS (i1 ≠ k): l1 unchanged                                               *)
(******************************************************************************)

Inv(i1', i2, k, dk1, dk2, bd:bool, hit1':bool, hit2:bool, l1', n, m) :-
    Inv(i1, i2, k, dk1, dk2, bd:bool, hit1:bool, hit2:bool, l1, n, m),
    SchTF(i1, i2, k, dk1, dk2, bd:bool, hit1:bool, hit2:bool, l1, n, m),
    (
        (* HIT with dk1 = dk2: no change to l1 *)
        i1 < n and i1 = k and dk1 = dk2 and
        i1' = i1 + 1 and hit1' and l1' = l1
    ) or (
        (* HIT with dk1 < dk2 and !hit2: l1 increases by (dk2 - dk1) *)
        i1 < n and i1 = k and bd and dk1 <> dk2 and !hit2 and
        i1' = i1 + 1 and hit1' and l1' = l1 + dk2 - dk1
    ) or (
        (* HIT with dk1 < dk2 and hit2: l1 becomes 0 (cancels) *)
        i1 < n and i1 = k and bd and dk1 <> dk2 and hit2 and
        i1' = i1 + 1 and hit1' and l1' = 0
    ) or (
        (* HIT with dk1 > dk2 and !hit2: l1 increases by (dk1 - dk2) *)
        i1 < n and i1 = k and !bd and !hit2 and
        i1' = i1 + 1 and hit1' and l1' = l1 + dk1 - dk2
    ) or (
        (* HIT with dk1 > dk2 and hit2: l1 becomes 0 (cancels) *)
        i1 < n and i1 = k and !bd and hit2 and
        i1' = i1 + 1 and hit1' and l1' = 0
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

Inv(i1, i2', k, dk1, dk2, bd:bool, hit1:bool, hit2':bool, l1', n, m) :-
    Inv(i1, i2, k, dk1, dk2, bd:bool, hit1:bool, hit2:bool, l1, n, m),
    SchFT(i1, i2, k, dk1, dk2, bd:bool, hit1:bool, hit2:bool, l1, n, m),
    (
        (* HIT with dk1 = dk2: no change *)
        i2 < n and i2 = k and dk1 = dk2 and
        i2' = i2 + 1 and hit2' and l1' = l1
    ) or (
        (* HIT with dk1 < dk2 and !hit1: l1 increases by (dk2 - dk1) *)
        i2 < n and i2 = k and bd and dk1 <> dk2 and !hit1 and
        i2' = i2 + 1 and hit2' and l1' = l1 + dk2 - dk1
    ) or (
        (* HIT with dk1 < dk2 and hit1: l1 becomes 0 *)
        i2 < n and i2 = k and bd and dk1 <> dk2 and hit1 and
        i2' = i2 + 1 and hit2' and l1' = 0
    ) or (
        (* HIT with dk1 > dk2 and !hit1: l1 increases *)
        i2 < n and i2 = k and !bd and !hit1 and
        i2' = i2 + 1 and hit2' and l1' = l1 + dk1 - dk2
    ) or (
        (* HIT with dk1 > dk2 and hit1: l1 becomes 0 *)
        i2 < n and i2 = k and !bd and hit1 and
        i2' = i2 + 1 and hit2' and l1' = 0
    ) or (
        (* MISS *)
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

Inv(i1', i2', k, dk1, dk2, bd:bool, hit1':bool, hit2':bool, l1', n, m) :-
    Inv(i1, i2, k, dk1, dk2, bd:bool, hit1:bool, hit2:bool, l1, n, m),
    SchTT(i1, i2, k, dk1, dk2, bd:bool, hit1:bool, hit2:bool, l1, n, m),
    (
        (* HIT-HIT: both process k simultaneously *)
        (* dk1 = dk2: both add to same bins, l1 unchanged *)
        i1 < n and i1 = k and i2 < n and i2 = k and dk1 = dk2 and
        i1' = i1 + 1 and i2' = i2 + 1 and hit1' and hit2' and l1' = l1
    ) or (
        (* HIT-HIT with dk1 ≠ dk2: both process k, difference is |dk2 - dk1| *)
        (* But since both process simultaneously, the L1 is established *)
        i1 < n and i1 = k and i2 < n and i2 = k and dk1 <> dk2 and bd and
        i1' = i1 + 1 and i2' = i2 + 1 and hit1' and hit2' and l1' = dk2 - dk1
    ) or (
        i1 < n and i1 = k and i2 < n and i2 = k and dk1 <> dk2 and !bd and
        i1' = i1 + 1 and i2' = i2 + 1 and hit1' and hit2' and l1' = dk1 - dk2
    ) or (
        (* HIT-MISS: run 1 hits, run 2 misses *)
        i1 < n and i1 = k and i2 < n and i2 <> k and dk1 = dk2 and
        i1' = i1 + 1 and i2' = i2 + 1 and hit1' and
        (hit2' and hit2 or !hit2' and !hit2) and l1' = l1
    ) or (
        i1 < n and i1 = k and i2 < n and i2 <> k and bd and dk1 <> dk2 and !hit2 and
        i1' = i1 + 1 and i2' = i2 + 1 and hit1' and
        (hit2' and hit2 or !hit2' and !hit2) and l1' = l1 + dk2 - dk1
    ) or (
        i1 < n and i1 = k and i2 < n and i2 <> k and bd and dk1 <> dk2 and hit2 and
        i1' = i1 + 1 and i2' = i2 + 1 and hit1' and
        (hit2' and hit2 or !hit2' and !hit2) and l1' = 0
    ) or (
        i1 < n and i1 = k and i2 < n and i2 <> k and !bd and !hit2 and
        i1' = i1 + 1 and i2' = i2 + 1 and hit1' and
        (hit2' and hit2 or !hit2' and !hit2) and l1' = l1 + dk1 - dk2
    ) or (
        i1 < n and i1 = k and i2 < n and i2 <> k and !bd and hit2 and
        i1' = i1 + 1 and i2' = i2 + 1 and hit1' and
        (hit2' and hit2 or !hit2' and !hit2) and l1' = 0
    ) or (
        (* MISS-HIT: run 1 misses, run 2 hits *)
        i1 < n and i1 <> k and i2 < n and i2 = k and dk1 = dk2 and
        i1' = i1 + 1 and i2' = i2 + 1 and
        (hit1' and hit1 or !hit1' and !hit1) and hit2' and l1' = l1
    ) or (
        i1 < n and i1 <> k and i2 < n and i2 = k and bd and dk1 <> dk2 and !hit1 and
        i1' = i1 + 1 and i2' = i2 + 1 and
        (hit1' and hit1 or !hit1' and !hit1) and hit2' and l1' = l1 + dk2 - dk1
    ) or (
        i1 < n and i1 <> k and i2 < n and i2 = k and bd and dk1 <> dk2 and hit1 and
        i1' = i1 + 1 and i2' = i2 + 1 and
        (hit1' and hit1 or !hit1' and !hit1) and hit2' and l1' = 0
    ) or (
        i1 < n and i1 <> k and i2 < n and i2 = k and !bd and !hit1 and
        i1' = i1 + 1 and i2' = i2 + 1 and
        (hit1' and hit1 or !hit1' and !hit1) and hit2' and l1' = l1 + dk1 - dk2
    ) or (
        i1 < n and i1 <> k and i2 < n and i2 = k and !bd and hit1 and
        i1' = i1 + 1 and i2' = i2 + 1 and
        (hit1' and hit1 or !hit1' and !hit1) and hit2' and l1' = 0
    ) or (
        (* MISS-MISS *)
        i1 < n and i1 <> k and i2 < n and i2 <> k and
        i1' = i1 + 1 and i2' = i2 + 1 and
        (hit1' and hit1 or !hit1' and !hit1) and
        (hit2' and hit2 or !hit2' and !hit2) and
        l1' = l1
    ) or (
        (* HIT-Finished *)
        i1 < n and i1 = k and i2 >= n and dk1 = dk2 and
        i1' = i1 + 1 and i2' = i2 and hit1' and
        (hit2' and hit2 or !hit2' and !hit2) and l1' = l1
    ) or (
        i1 < n and i1 = k and i2 >= n and bd and dk1 <> dk2 and !hit2 and
        i1' = i1 + 1 and i2' = i2 and hit1' and
        (hit2' and hit2 or !hit2' and !hit2) and l1' = l1 + dk2 - dk1
    ) or (
        i1 < n and i1 = k and i2 >= n and bd and dk1 <> dk2 and hit2 and
        i1' = i1 + 1 and i2' = i2 and hit1' and
        (hit2' and hit2 or !hit2' and !hit2) and l1' = 0
    ) or (
        i1 < n and i1 = k and i2 >= n and !bd and !hit2 and
        i1' = i1 + 1 and i2' = i2 and hit1' and
        (hit2' and hit2 or !hit2' and !hit2) and l1' = l1 + dk1 - dk2
    ) or (
        i1 < n and i1 = k and i2 >= n and !bd and hit2 and
        i1' = i1 + 1 and i2' = i2 and hit1' and
        (hit2' and hit2 or !hit2' and !hit2) and l1' = 0
    ) or (
        (* Finished-HIT *)
        i1 >= n and i2 < n and i2 = k and dk1 = dk2 and
        i1' = i1 and i2' = i2 + 1 and
        (hit1' and hit1 or !hit1' and !hit1) and hit2' and l1' = l1
    ) or (
        i1 >= n and i2 < n and i2 = k and bd and dk1 <> dk2 and !hit1 and
        i1' = i1 and i2' = i2 + 1 and
        (hit1' and hit1 or !hit1' and !hit1) and hit2' and l1' = l1 + dk2 - dk1
    ) or (
        i1 >= n and i2 < n and i2 = k and bd and dk1 <> dk2 and hit1 and
        i1' = i1 and i2' = i2 + 1 and
        (hit1' and hit1 or !hit1' and !hit1) and hit2' and l1' = 0
    ) or (
        i1 >= n and i2 < n and i2 = k and !bd and !hit1 and
        i1' = i1 and i2' = i2 + 1 and
        (hit1' and hit1 or !hit1' and !hit1) and hit2' and l1' = l1 + dk1 - dk2
    ) or (
        i1 >= n and i2 < n and i2 = k and !bd and hit1 and
        i1' = i1 and i2' = i2 + 1 and
        (hit1' and hit1 or !hit1' and !hit1) and hit2' and l1' = 0
    ) or (
        (* MISS-Finished, Finished-MISS, Finished-Finished *)
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
    Inv(i1, i2, k, dk1, dk2, bd:bool, hit1:bool, hit2:bool, l1, n, m),
    SchTF(i1, i2, k, dk1, dk2, bd:bool, hit1:bool, hit2:bool, l1, n, m),
    i2 < n.

i2 < n :-
    Inv(i1, i2, k, dk1, dk2, bd:bool, hit1:bool, hit2:bool, l1, n, m),
    SchFT(i1, i2, k, dk1, dk2, bd:bool, hit1:bool, hit2:bool, l1, n, m),
    i1 < n.

SchTF(i1, i2, k, dk1, dk2, bd:bool, hit1:bool, hit2:bool, l1, n, m),
SchFT(i1, i2, k, dk1, dk2, bd:bool, hit1:bool, hit2:bool, l1, n, m),
SchTT(i1, i2, k, dk1, dk2, bd:bool, hit1:bool, hit2:bool, l1, n, m) :-
    Inv(i1, i2, k, dk1, dk2, bd:bool, hit1:bool, hit2:bool, l1, n, m),
    i1 < n or i2 < n.


(******************************************************************************)
(* GOAL: L1 Sensitivity = |dk2 - dk1| <= m - 1                                *)
(*                                                                            *)
(* At termination:                                                            *)
(*   If dk1 = dk2: l1 = 0                                                    *)
(*   If dk1 ≠ dk2: l1 = |dk2 - dk1|                                          *)
(*                                                                            *)
(* Maximum: m - 1 (when dk1 and dk2 are at opposite ends)                    *)
(******************************************************************************)

(* Violation: l1 > m - 1 should be UNSAT *)
l1 > m - 1 :-
    Inv(i1, i2, k, dk1, dk2, bd:bool, hit1:bool, hit2:bool, l1, n, m),
    n <= i1, n <= i2.

(* Alternative: l1 > |dk2 - dk1| should be UNSAT *)
(* This is tighter but requires encoding |dk2 - dk1| *)
(*
(bd and l1 > dk2 - dk1) or (!bd and l1 > dk1 - dk2) :-
    Inv(i1, i2, k, dk1, dk2, bd:bool, hit1:bool, hit2:bool, l1, n, m),
    n <= i1, n <= i2.
*)


(******************************************************************************)
(* TEST QUERIES                                                               *)
(******************************************************************************)

(*
(* Test 1: L1 <= m - 1 - should be SAT *)
l1 <= m - 1 :-
    Inv(i1, i2, k, dk1, dk2, bd:bool, hit1:bool, hit2:bool, l1, n, m),
    n <= i1, n <= i2.

(* Test 2: L1 = 0 when dk1 = dk2 - should be SAT *)
l1 = 0 :-
    Inv(i1, i2, k, dk1, dk2, bd:bool, hit1:bool, hit2:bool, l1, n, m),
    n <= i1, n <= i2, dk1 = dk2.

(* Test 3: L1 > 0 when dk1 = dk2? - should be UNSAT *)
l1 > 0 :-
    Inv(i1, i2, k, dk1, dk2, bd:bool, hit1:bool, hit2:bool, l1, n, m),
    n <= i1, n <= i2, dk1 = dk2.
*)
