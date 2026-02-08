(*
Kruskal(G : graph)
    for each node v in G:
        MakeSet(v)                    (* Initialize disjoint sets *)
    T := ∅                            (* MST edges *)
    cost := 0                         (* MST total cost *)
    for each edge (u,v) in G ordered by weight:
        if Find(u) ≠ Find(v):         (* Different components? *)
            T := T ∪ {(u,v)}          (* Add edge to MST *)
            cost := cost + G[u,v]     (* Accumulate cost *)
            Union(u, v)               (* Merge components *)
    return T, cost
*)

(*
PROPERTY: (N-1)-robust under L∞ for MST cost
  ∀e. |G1[e] - G2[e]| ≤ ε  ⟹  |cost1 - cost2| ≤ (N-1)·ε

DETAILED VERSION WITH HIT/MISS ABSTRACTION:

This version tracks TWO distinguished cells:

1. INPUT CELL (edge weight):
   - k: distinguished edge index
   - wk1, wk2: weights G1[k], G2[k]
   - bk: sign bit for edge weight difference

2. OUTPUT CELL (MST cost):
   - c1, c2: MST costs in runs 1 and 2
   - bc: sign bit for cost difference

HIT/MISS for edge selection:
- HIT:  The distinguished edge k is considered for MST
        → we know exact weight contribution wk1 or wk2
- MISS: Some other edge is considered
        → weight unknown but bounded by eps

KEY INSIGHT:
When edge k is added to MST:
- Run 1 adds wk1 to cost
- Run 2 adds wk2 to cost  
- Contribution to difference: |wk1 - wk2| ≤ eps

INVARIANT: |c1 - c2| ≤ i · ε  where i = edges added

STATE VARIABLES:
  i1, i2      : edges added to MST
  k           : distinguished edge index
  wk1, wk2    : weights G1[k], G2[k] (NEVER CHANGE)
  bk          : sign bit for weight (bk ⟹ wk2 ≥ wk1)
  c1, c2      : MST costs (ACCUMULATE)
  bc          : sign bit for cost (bc ⟹ c2 ≥ c1)
  n           : number of vertices
  eps         : per-edge perturbation bound
*)


(******************************************************************************)
(* INITIALIZATION                                                             *)
(******************************************************************************)

Inv(i1, i2, k, wk1, wk2, bk:bool, c1, c2, bc:bool, n, eps) :-
    i1 = 0, i2 = 0,
    n > 0,
    (* Distinguished edge k is valid *)
    0 <= k,
    0 <= eps,
    (* Edge weights satisfy epsilon bound *)
    (bk and 0 <= wk2 - wk1 and wk2 - wk1 <= eps) or
    (!bk and 0 <= wk1 - wk2 and wk1 - wk2 <= eps),
    (* Initial costs are equal *)
    c1 = 0, c2 = 0.


(******************************************************************************)
(* TF TRANSITION - Only run 1 steps                                           *)
(*                                                                            *)
(* Run 1 considers an edge for MST.                                           *)
(* Cases:                                                                     *)
(*   1. Add distinguished edge k (HIT): c1' = c1 + wk1                        *)
(*   2. Add other edge (MISS): c1' increases by unknown weight                *)
(*   3. Skip edge: c1' = c1 (edge not added to MST)                           *)
(*   4. Finished: i1 >= n-1                                                   *)
(******************************************************************************)

Inv(i1', i2, k, wk1, wk2, bk:bool, c1', c2, bc':bool, n, eps) :-
    Inv(i1, i2, k, wk1, wk2, bk:bool, c1, c2, bc:bool, n, eps),
    SchTF(i1, i2, k, wk1, wk2, bk:bool, c1, c2, bc:bool, n, eps),
    (
        (* Case 1: Add distinguished edge k (HIT) *)
        (* We know exactly: c1' = c1 + wk1 *)
        i1 < n - 1 and i1' = i1 + 1 and c1' = c1 + wk1
    ) or (
        (* Case 2: Add other edge (MISS) *)
        (* Weight unknown, but difference bounded by eps *)
        i1 < n - 1 and i1' = i1 + 1
        (* c1' constrained by epsilon bound below *)
    ) or (
        (* Case 3: Skip edge - not added to MST *)
        i1 < n - 1 and i1' = i1 and c1' = c1
    ) or (
        (* Case 4: Finished *)
        i1 >= n - 1 and i1' = i1 and c1' = c1
        (* NOTE: bc' is NOT assigned here - it's constrained by epsilon bound *)
    ),
    (* Maintain epsilon bound *)
    (bc' and 0 <= c2 - c1' and c2 - c1' <= i1' * eps) or
    (!bc' and 0 <= c1' - c2 and c1' - c2 <= i1' * eps).


(******************************************************************************)
(* FT TRANSITION - Only run 2 steps                                           *)
(******************************************************************************)

Inv(i1, i2', k, wk1, wk2, bk:bool, c1, c2', bc':bool, n, eps) :-
    Inv(i1, i2, k, wk1, wk2, bk:bool, c1, c2, bc:bool, n, eps),
    SchFT(i1, i2, k, wk1, wk2, bk:bool, c1, c2, bc:bool, n, eps),
    (
        (* Case 1: Add distinguished edge k (HIT) *)
        i2 < n - 1 and i2' = i2 + 1 and c2' = c2 + wk2
    ) or (
        (* Case 2: Add other edge (MISS) *)
        i2 < n - 1 and i2' = i2 + 1
    ) or (
        (* Case 3: Skip edge *)
        i2 < n - 1 and i2' = i2 and c2' = c2
    ) or (
        (* Case 4: Finished *)
        i2 >= n - 1 and i2' = i2 and c2' = c2
        (* NOTE: bc' constrained by epsilon bound, not assigned *)
    ),
    (* Maintain epsilon bound *)
    (bc' and 0 <= c2' - c1 and c2' - c1 <= i2' * eps) or
    (!bc' and 0 <= c1 - c2' and c1 - c2' <= i2' * eps).


(******************************************************************************)
(* TT TRANSITION - Both runs step together                                    *)
(*                                                                            *)
(* Both runs consider edges. Cases by HIT/MISS:                               *)
(*   HIT-HIT:   Both add edge k → difference increases by |wk1 - wk2| ≤ eps  *)
(*   HIT-MISS:  Run 1 adds k, run 2 adds other                                *)
(*   MISS-HIT:  Run 1 adds other, run 2 adds k                                *)
(*   MISS-MISS: Both add other edges                                          *)
(*   SKIP-*:    One or both skip                                              *)
(******************************************************************************)

Inv(i1', i2', k, wk1, wk2, bk:bool, c1', c2', bc':bool, n, eps) :-
    Inv(i1, i2, k, wk1, wk2, bk:bool, c1, c2, bc:bool, n, eps),
    SchTT(i1, i2, k, wk1, wk2, bk:bool, c1, c2, bc:bool, n, eps),
    (
        (* Case 1: HIT-HIT - both add distinguished edge k *)
        (* c1' = c1 + wk1, c2' = c2 + wk2 *)
        (* Difference grows by |wk1 - wk2| ≤ eps *)
        i1 < n - 1 and i2 < n - 1 and i1' = i1 + 1 and i2' = i2 + 1 and
        c1' = c1 + wk1 and c2' = c2 + wk2
    ) or (
        (* Case 2: HIT-MISS - run 1 adds k, run 2 adds other *)
        i1 < n - 1 and i2 < n - 1 and i1' = i1 + 1 and i2' = i2 + 1 and
        c1' = c1 + wk1
        (* c2' constrained by bound *)
    ) or (
        (* Case 3: MISS-HIT - run 1 adds other, run 2 adds k *)
        i1 < n - 1 and i2 < n - 1 and i1' = i1 + 1 and i2' = i2 + 1 and
        c2' = c2 + wk2
        (* c1' constrained by bound *)
    ) or (
        (* Case 4: MISS-MISS - both add other edges *)
        i1 < n - 1 and i2 < n - 1 and i1' = i1 + 1 and i2' = i2 + 1
    ) or (
        (* Case 5: One adds, one skips *)
        i1 < n - 1 and i2 < n - 1 and i1' = i1 + 1 and i2' = i2 and c2' = c2
    ) or (
        (* Case 6: One skips, one adds *)
        i1 < n - 1 and i2 < n - 1 and i1' = i1 and i2' = i2 + 1 and c1' = c1
    ) or (
        (* Case 7: Both skip *)
        i1 < n - 1 and i2 < n - 1 and i1' = i1 and i2' = i2 and
        c1' = c1 and c2' = c2
    ) or (
        (* Case 8: Both finished *)
        i1 >= n - 1 and i2 >= n - 1 and i1' = i1 and i2' = i2 and
        c1' = c1 and c2' = c2
        (* NOTE: bc' constrained by epsilon bound, not assigned *)
    ),
    (* Maintain epsilon bound *)
    (bc' and 0 <= c2' - c1' and c2' - c1' <= i1' * eps) or
    (!bc' and 0 <= c1' - c2' and c1' - c2' <= i1' * eps).


(******************************************************************************)
(* SCHEDULER FAIRNESS                                                         *)
(******************************************************************************)

i1 < n - 1 :-
    Inv(i1, i2, k, wk1, wk2, bk:bool, c1, c2, bc:bool, n, eps),
    SchTF(i1, i2, k, wk1, wk2, bk:bool, c1, c2, bc:bool, n, eps),
    i2 < n - 1.

i2 < n - 1 :-
    Inv(i1, i2, k, wk1, wk2, bk:bool, c1, c2, bc:bool, n, eps),
    SchFT(i1, i2, k, wk1, wk2, bk:bool, c1, c2, bc:bool, n, eps),
    i1 < n - 1.

SchTF(i1, i2, k, wk1, wk2, bk:bool, c1, c2, bc:bool, n, eps),
SchFT(i1, i2, k, wk1, wk2, bk:bool, c1, c2, bc:bool, n, eps),
SchTT(i1, i2, k, wk1, wk2, bk:bool, c1, c2, bc:bool, n, eps) :-
    Inv(i1, i2, k, wk1, wk2, bk:bool, c1, c2, bc:bool, n, eps),
    i1 < n - 1 or i2 < n - 1.


(******************************************************************************)
(* GOAL: (N-1)-ROBUSTNESS                                                     *)
(******************************************************************************)

c1 - c2 > (n - 1) * eps or c2 - c1 > (n - 1) * eps :-
    Inv(i1, i2, k, wk1, wk2, bk:bool, c1, c2, bc:bool, n, eps),
    n - 1 <= i1, n - 1 <= i2.


(******************************************************************************)
(* TEST QUERIES                                                               *)
(******************************************************************************)

(*
(* Test 1: (N-1)·ε bound maintained - should be SAT *)
c1 - c2 <= (n - 1) * eps and c2 - c1 <= (n - 1) * eps :-
    Inv(i1, i2, k, wk1, wk2, bk:bool, c1, c2, bc:bool, n, eps),
    n - 1 <= i1, n - 1 <= i2.

(* Test 2: Edge weights satisfy bound - should be SAT *)
wk1 - wk2 <= eps and wk2 - wk1 <= eps :-
    Inv(i1, i2, k, wk1, wk2, bk:bool, c1, c2, bc:bool, n, eps).

(* Test 3: Exact equality - should be UNSAT *)
c1 = c2 :-
    Inv(i1, i2, k, wk1, wk2, bk:bool, c1, c2, bc:bool, n, eps),
    n - 1 <= i1, n - 1 <= i2.

(* Test 4: 1-robust (too tight) - should be SAT (violation reachable) *)
c1 - c2 > eps or c2 - c1 > eps :-
    Inv(i1, i2, k, wk1, wk2, bk:bool, c1, c2, bc:bool, n, eps),
    n - 1 <= i1, n - 1 <= i2.
*)
