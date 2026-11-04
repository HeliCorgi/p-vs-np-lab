# One outer case split can prove the whole gated obstruction

The hard pair targets *directed* clause-by-clause transport between different
residuals. It does not exclude solving the union directly. The
[case refuter](../src/pnp_lab/case_parity.py) either proves the input UNSAT
by the existing [private-resolution/parity pass](private_resolution.md), or
finds a bit s such that this pass proves both F|s=0 and F|s=1 UNSAT.
Every complete assignment chooses one of the two values, so the two
refutations together prove the original F UNSAT. This is a single outer
split over a parity proof system, not depth-one ordinary RUP. An outer
UNKNOWN never establishes SAT or a failed transport direction.

No candidate variable is supplied by the construction. The implementation
orders occurring variables by descending literal occurrences (ID breaks
ties); `max_pivots` is an optional budget on outer candidates only. An
unsuccessful first side permits skipping the second. With m occurring
variables the search uses at most 1+2m inner calls, each a polynomial
private-resolution/conditional-parity pass. The test at the unsplit root
is optional. This cost statement concerns finding proofs or returning
UNKNOWN. It has no completeness hypothesis. The independent replayer
uses the original CNF, drops satisfied clauses, removes occurrences of the
pinned variable without changing the remaining order or IDs, and checks
both supplied child proofs with the existing checker. Clause indices in
the inner certificates refer to their respective lists of restricted clauses.

## Why the gate is exposed

Gate each original ternary clause (a OR b OR c) by a switch literal g
and its own private helper w, using:

    (g OR a OR w) AND (not w OR b OR c).

At the unsplit root resolving on w would produce a width-four clause outside
the inner pass. Distinct helper names prevent a full local parity group
from appearing: for fixed s, or fixed edge x, all candidate two-variable
slices involve one helper appearing in just one clause of that side and
support. At a helper pivot the two clauses live on opposite sides; neither
side extracts a parity from its single pair. The original triples are unique
as signed-clause *supports* within this construction: helper presence plus
the two different, unshared other-variable pairs prevent repeated supports.
Thus the existing root pass is silent on these genuine cubic instances.

After the outer test s=i, each clause in the active bank has become
(a OR w) AND (not w OR b OR c): its width-three resolvent is now eligible.
The inactive bank does not need to be solved. All parity clauses of the
active graph now appear; XORing its vertex equations cancels every edge
and gives 0=1 for odd total charge. This works for any odd/odd pair of
such graphs and any number of variable-disjoint copies conjoined. Testing
one switch covers both sides of just one UNSAT conjunct. On the cubic
construction a selector occurs once per encoded clause in both banks,
more often than an edge or a helper; across disjoint modules any
highest-frequency choice is such a switch. This is an elementary escape
from this particular obstruction, not a claim about the best way to solve
disconnected formulas or a bound on the overall SAT solver.

The [reproduced experiment](../results/case_parity.json) checks the two
ten-vertex cubic graph examples, gives each bank its own edge and helper
variables in the module controls, and permutes IDs, signs and clause order.
On eight modules (888 variables, 1,280 clauses) the odd input is refuted
with three inner calls: the inconclusive root and the two sides of the first
candidate. The even sibling has a checked original satisfying assignment;
the refuter returns UNKNOWN. Applying the [blind-image recovery](blind_recovery.md)
first also works on the 488-variable, 651-clause signed-permuted image
of the shared-edge example: the verified reduced problem has 96 variables
and 160 clauses. On the odd version its two cases refute it; on the even
version an independently supplied model lifts through the verified map.

## A failure with every candidate tried

The eight signed clauses on three fixed bits forbid every possible word.
Replace EACH (a OR b OR c) separately with two private chain bits p,q:

    (a OR p) AND (not p OR q) AND (not q OR b OR c).

If all three original literals are false, the chain forces p then q true
and falsifies the last clause. If at least one original literal is true the
chain extends (choose p=q=false when a=true, and p=q=true otherwise).
The resulting 19-variable, 24-clause instance is therefore UNSAT, yet the
implemented one-case refuter returns UNKNOWN even with all 19 outer pivots
tested and no budget. Eliminating private bits successively would undo this
example; it is not a lower bound for every parity proof or SAT solver.

[Tests and proof-tamper examples](../tests/test_case_parity.py) ·
[experiment](../experiments/case_parity.py).
