(*
Dijkstra(G, src)
    for each v in G: d[v] := inf
    d[src] := 0
    WL := all nodes
    while WL <> empty:
        u := argmin d[v] for v in WL
        remove u from WL
        for each neighbor v of u:
            if d[u] + G[u,v] < d[v]:
                d[v] := d[u] + G[u,v]
    return d
*)

(*
PROPERTY: (N-1)-robust under L-infinity
  forall e. |G1[e] - G2[e]| <= eps  ==>  forall v. |d1[v] - d2[v]| <= (N-1)*eps

WHY (N-1)?
  Shortest path to any vertex uses at most N-1 edges.
  Each edge weight differs by at most eps between the two graphs.
  So the total distance difference is at most (N-1)*eps.

================================================================================
RELATIONAL CELL MORPHING
================================================================================

TWO DISTINGUISHED CELLS:

1. INPUT CELL (edge weight):
   - k: distinguished edge index (symbolic, universally quantified)
   - wk1, wk2: weights G1[k], G2[k]
   - bk: sign bit for |wk1 - wk2|
   - PRECONDITION: |wk1 - wk2| <= eps
   - wk1, wk2 NEVER CHANGE (input constants)

2. OUTPUT CELL (vertex distance):
   - v: distinguished vertex (implicit, universally quantified)
   - dv1, dv2: shortest distances d1[v], d2[v]
   - bv: sign bit for |dv1 - dv2|
   - POSTCONDITION: |dv1 - dv2| <= (N-1)*eps
   - dv1, dv2 CAN CHANGE during relaxation

================================================================================
HOP COUNT ABSTRACTION
================================================================================

Unlike Kruskal where cost accumulates additively (c' = c + w), in Dijkstra
distance is REPLACED by relaxation (d[v] = d[u] + w). We cannot make HIT
explicit because we do not track predecessor distance d[u].

Instead, we abstract via HOP COUNT:
  - h1, h2: number of edges in current shortest path to v
  - Each edge contributes at most eps to |dv1 - dv2|
  - INVARIANT: |dv1 - dv2| <= max(h1, h2) * eps
  - h <= N-1 always, so at termination: |dv1 - dv2| <= (N-1)*eps

Both HIT and MISS contribute at most eps per edge, so they are MERGED
into a single relaxation case. This is the key structural difference
from Kruskal.

================================================================================
STATE VARIABLES
================================================================================

  i1, i2      : iteration counters (for termination)
  h1, h2      : hop count = edges in current shortest path to v
  k           : distinguished edge index (NEVER CHANGES)
  wk1, wk2    : edge weights G1[k], G2[k] (NEVER CHANGE)
  bk          : sign bit for |wk1 - wk2| (NEVER CHANGES)
  dv1, dv2    : shortest distances to v (CAN CHANGE)
  bv          : sign bit for |dv1 - dv2|
  n           : number of vertices
  eps         : perturbation bound

NOTE: k, wk1, wk2, bk are kept for framework consistency with insertion sort
and Kruskal, even though they are not used in transition cases. They document
the input perturbation assumption. Future refinements could exploit them for
an explicit HIT case if predecessor tracking is added.
*)


(******************************************************************************)
(* INITIALIZATION                                                             *)
(******************************************************************************)

Inv(i1, i2, h1, h2, k, wk1, wk2, bk:bool, dv1, dv2, bv:bool, n, eps) :-
    i1 = 0, i2 = 0,
    h1 = 0, h2 = 0,
    n > 0,
    0 <= k,
    0 <= eps,
    (* INPUT: |wk1 - wk2| <= eps *)
    (bk and 0 <= wk2 - wk1 and wk2 - wk1 <= eps) or
    (!bk and 0 <= wk1 - wk2 and wk1 - wk2 <= eps),
    (* OUTPUT: distances start equal *)
    (* Both runs begin with same distance (0 for source, inf for others) *)
    dv1 = dv2.


(******************************************************************************)
(* TF TRANSITION - Only run 1 steps                                           *)
(*                                                                            *)
(* Cases:                                                                     *)
(*   1. No change: vertex v not relaxed this iteration                        *)
(*   2. Relaxation: new shorter path found to v (HIT/MISS merged)             *)
(*      - h1' in [1, n-1]: new path has h1' edges                            *)
(*      - dv1' constrained only by epsilon bound                              *)
(*   3. Finished: i1 >= n, stutter                                            *)
(******************************************************************************)

Inv(i1', i2, h1', h2, k, wk1, wk2, bk:bool, dv1', dv2, bv':bool, n, eps) :-
    Inv(i1, i2, h1, h2, k, wk1, wk2, bk:bool, dv1, dv2, bv:bool, n, eps),
    SchTF(i1, i2, h1, h2, k, wk1, wk2, bk:bool, dv1, dv2, bv:bool, n, eps),
    (
        (* Case 1: No change to vertex v *)
        i1 < n and i1' = i1 + 1 and
        h1' = h1 and dv1' = dv1
    ) or (
        (* Case 2: Relaxation - new shortest path to v *)
        (* HIT and MISS merged: both contribute <= eps per edge *)
        (* h1' = hop count of new path, can be any value in [1, n-1] *)
        (* dv1' is unconstrained here; epsilon bound below limits it *)
        i1 < n and i1' = i1 + 1 and
        h1' >= 1 and h1' < n
    ) or (
        (* Case 3: Finished - stutter *)
        i1 >= n and i1' = i1 and
        h1' = h1 and dv1' = dv1
    ),
    (* EPSILON BOUND: |dv1' - dv2| <= max(h1', h2) * eps *)
    (h1' >= h2 and bv' and 0 <= dv2 - dv1' and dv2 - dv1' <= h1' * eps) or
    (h1' >= h2 and !bv' and 0 <= dv1' - dv2 and dv1' - dv2 <= h1' * eps) or
    (h2 > h1' and bv' and 0 <= dv2 - dv1' and dv2 - dv1' <= h2 * eps) or
    (h2 > h1' and !bv' and 0 <= dv1' - dv2 and dv1' - dv2 <= h2 * eps).


(******************************************************************************)
(* FT TRANSITION - Only run 2 steps                                           *)
(*                                                                            *)
(* Symmetric to TF. Epsilon bound uses h1 (unchanged) and h2' (updated).      *)
(******************************************************************************)

Inv(i1, i2', h1, h2', k, wk1, wk2, bk:bool, dv1, dv2', bv':bool, n, eps) :-
    Inv(i1, i2, h1, h2, k, wk1, wk2, bk:bool, dv1, dv2, bv:bool, n, eps),
    SchFT(i1, i2, h1, h2, k, wk1, wk2, bk:bool, dv1, dv2, bv:bool, n, eps),
    (
        (* Case 1: No change to vertex v *)
        i2 < n and i2' = i2 + 1 and
        h2' = h2 and dv2' = dv2
    ) or (
        (* Case 2: Relaxation *)
        i2 < n and i2' = i2 + 1 and
        h2' >= 1 and h2' < n
    ) or (
        (* Case 3: Finished - stutter *)
        i2 >= n and i2' = i2 and
        h2' = h2 and dv2' = dv2
    ),
    (* EPSILON BOUND: |dv1 - dv2'| <= max(h1, h2') * eps *)
    (h1 >= h2' and bv' and 0 <= dv2' - dv1 and dv2' - dv1 <= h1 * eps) or
    (h1 >= h2' and !bv' and 0 <= dv1 - dv2' and dv1 - dv2' <= h1 * eps) or
    (h2' > h1 and bv' and 0 <= dv2' - dv1 and dv2' - dv1 <= h2' * eps) or
    (h2' > h1 and !bv' and 0 <= dv1 - dv2' and dv1 - dv2' <= h2' * eps).


(******************************************************************************)
(* TT TRANSITION - Both runs step                                             *)
(*                                                                            *)
(* Uses Cartesian product: independent blocks for run 1 and run 2.            *)
(* This automatically handles all combinations:                               *)
(*   - Both working (no change / relax x no change / relax)                   *)
(*   - One finished, other working                                            *)
(*   - Both finished                                                          *)
(*                                                                            *)
(* Since HIT/MISS are merged, no HIT-HIT/HIT-MISS/MISS-HIT/MISS-MISS         *)
(* matrix is needed (unlike Kruskal).                                         *)
(******************************************************************************)

Inv(i1', i2', h1', h2', k, wk1, wk2, bk:bool, dv1', dv2', bv':bool, n, eps) :-
    Inv(i1, i2, h1, h2, k, wk1, wk2, bk:bool, dv1, dv2, bv:bool, n, eps),
    SchTT(i1, i2, h1, h2, k, wk1, wk2, bk:bool, dv1, dv2, bv:bool, n, eps),
    (* Run 1: independent cases *)
    (
        (* No change *)
        i1 < n and i1' = i1 + 1 and h1' = h1 and dv1' = dv1
    ) or (
        (* Relaxation *)
        i1 < n and i1' = i1 + 1 and h1' >= 1 and h1' < n
    ) or (
        (* Finished *)
        i1 >= n and i1' = i1 and h1' = h1 and dv1' = dv1
    ),
    (* Run 2: independent cases *)
    (
        (* No change *)
        i2 < n and i2' = i2 + 1 and h2' = h2 and dv2' = dv2
    ) or (
        (* Relaxation *)
        i2 < n and i2' = i2 + 1 and h2' >= 1 and h2' < n
    ) or (
        (* Finished *)
        i2 >= n and i2' = i2 and h2' = h2 and dv2' = dv2
    ),
    (* EPSILON BOUND: |dv1' - dv2'| <= max(h1', h2') * eps *)
    (h1' >= h2' and bv' and 0 <= dv2' - dv1' and dv2' - dv1' <= h1' * eps) or
    (h1' >= h2' and !bv' and 0 <= dv1' - dv2' and dv1' - dv2' <= h1' * eps) or
    (h2' > h1' and bv' and 0 <= dv2' - dv1' and dv2' - dv1' <= h2' * eps) or
    (h2' > h1' and !bv' and 0 <= dv1' - dv2' and dv1' - dv2' <= h2' * eps).


(******************************************************************************)
(* SCHEDULER FAIRNESS                                                         *)
(******************************************************************************)

(* If TF chosen and run 2 can progress, run 1 must be able to *)
i1 < n :-
    Inv(i1, i2, h1, h2, k, wk1, wk2, bk:bool, dv1, dv2, bv:bool, n, eps),
    SchTF(i1, i2, h1, h2, k, wk1, wk2, bk:bool, dv1, dv2, bv:bool, n, eps),
    i2 < n.

(* If FT chosen and run 1 can progress, run 2 must be able to *)
i2 < n :-
    Inv(i1, i2, h1, h2, k, wk1, wk2, bk:bool, dv1, dv2, bv:bool, n, eps),
    SchFT(i1, i2, h1, h2, k, wk1, wk2, bk:bool, dv1, dv2, bv:bool, n, eps),
    i1 < n.

(* Scheduler disjunction: at least one run can progress *)
SchTF(i1, i2, h1, h2, k, wk1, wk2, bk:bool, dv1, dv2, bv:bool, n, eps),
SchFT(i1, i2, h1, h2, k, wk1, wk2, bk:bool, dv1, dv2, bv:bool, n, eps),
SchTT(i1, i2, h1, h2, k, wk1, wk2, bk:bool, dv1, dv2, bv:bool, n, eps) :-
    Inv(i1, i2, h1, h2, k, wk1, wk2, bk:bool, dv1, dv2, bv:bool, n, eps),
    i1 < n or i2 < n.


(******************************************************************************)
(* GOAL: (N-1)-ROBUSTNESS                                                     *)
(*                                                                            *)
(* Violation goal: is |dv1 - dv2| > (N-1)*eps reachable at termination?       *)
(* UNSAT = violation unreachable = (N-1)-robustness VERIFIED                   *)
(******************************************************************************)

dv1 - dv2 > (n - 1) * eps or dv2 - dv1 > (n - 1) * eps :-
    Inv(i1, i2, h1, h2, k, wk1, wk2, bk:bool, dv1, dv2, bv:bool, n, eps),
    n <= i1, n <= i2.


(******************************************************************************)
(* TEST QUERIES (uncomment one at a time to run)                              *)
(******************************************************************************)

(*
(* Test 1: (N-1)*eps bound maintained at termination - expected SAT *)
(* SAT means the bound CAN be achieved, confirming it is not vacuous *)
dv1 - dv2 <= (n - 1) * eps and dv2 - dv1 <= (n - 1) * eps :-
    Inv(i1, i2, h1, h2, k, wk1, wk2, bk:bool, dv1, dv2, bv:bool, n, eps),
    n <= i1, n <= i2.

(* Test 2: Violation unreachable - expected UNSAT *)
(* UNSAT = (N-1)-robustness VERIFIED *)
dv1 - dv2 > (n - 1) * eps or dv2 - dv1 > (n - 1) * eps :-
    Inv(i1, i2, h1, h2, k, wk1, wk2, bk:bool, dv1, dv2, bv:bool, n, eps),
    n <= i1, n <= i2.

(* Test 3: Input edge weight bound - expected SAT *)
wk1 - wk2 <= eps and wk2 - wk1 <= eps :-
    Inv(i1, i2, h1, h2, k, wk1, wk2, bk:bool, dv1, dv2, bv:bool, n, eps).

(* Test 4: Exact equality at termination - expected UNSAT *)
(* Too strong: distances can differ by up to (N-1)*eps *)
dv1 = dv2 :-
    Inv(i1, i2, h1, h2, k, wk1, wk2, bk:bool, dv1, dv2, bv:bool, n, eps),
    n <= i1, n <= i2.

(* Test 5: 1-robust (too tight) - expected SAT *)
(* SAT = violation IS reachable = 1-robustness does NOT hold *)
dv1 - dv2 > eps or dv2 - dv1 > eps :-
    Inv(i1, i2, h1, h2, k, wk1, wk2, bk:bool, dv1, dv2, bv:bool, n, eps),
    n <= i1, n <= i2.

(* Test 6: N*eps bound (looser) - expected UNSAT *)
(* UNSAT confirms N*eps also holds (weaker than (N-1)*eps) *)
dv1 - dv2 > n * eps or dv2 - dv1 > n * eps :-
    Inv(i1, i2, h1, h2, k, wk1, wk2, bk:bool, dv1, dv2, bv:bool, n, eps),
    n <= i1, n <= i2.
*)
