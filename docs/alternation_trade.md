# A lower-bound calibration: what alternation trading actually rules out

**Verdict.** We replay two published SAT time-space arguments to calibrate the
strength of a general machine lower bound. They apply to unrestricted SAT
*inputs*, but to deterministic random-access algorithms using only
subpolynomial workspace. Do not spend the next phase searching for longer
lists of these same rules: a theorem bounds what all of them can achieve.

## A finite object with precisely scoped semantics

[The checker](../src/pnp_lab/alternation_trade.py) evaluates positive rational
exponents exactly. It implements a strict subset of Definition 4.1 in
R. Williams, [*Alternation-Trading Proofs, Linear Programming, and Lower
Bounds*](https://people.csail.mit.edu/rrw/automated-lbs.pdf)
([journal DOI](https://doi.org/10.1145/2493246.2493249)). The sources for
the logic are its local reduction Theorem 3.1, speedup/slowdown Lemmas
3.3/3.4, normal-form Lemma 4.3, and alternating hierarchy Theorem 3.5.
These theorems are **external premises** of the arithmetic replay. We do
not claim to have formalized their machine semantics in Lean or to have
discovered a new SAT lower bound.

Let N be the full encoded input length. Write D(a) for the paper's class
with **simultaneous** deterministic random-access time N^(a+o(1)) and
workspace N^o(1). A line consists of alternating quantifier blocks followed
by D(t). For each block record its type, exponent g for guessed bits and
exponent b for the size of the input passed to the next stage (all scaled
to the same original N). A zero exponent in a newly introduced block permits
the logarithmic choice of segment index; it does not mean an empty guess.

Argue by contradiction from NTIME[N] contained in D(c), c>1. The paper's
quasilinear-length, locally computable reduction implies that a SAT
algorithm with the claimed simultaneous bounds would supply this premise:
simulate each access to a reduction output bit locally instead of storing
the formula. Polylogarithmic costs fit in the o(1) exponent. SAT's ordinary
NP-completeness by an unspecified polynomial reduction would not justify
these fine exponents.

The checker computes inclusions, rather than trusting proposed new lines:

- On a deterministic line, split time at 0<x<=t-1. Output an existential
  block (x,max(x,1)), a universal block (0,1), and D(t-x). Guess
  checkpoints, choose one segment universally, and replay it.
- On an alternating line, merge the first new guess into the last old
  quantifier by using the appropriate polarity of the speedup. Its pair
  (g,b) becomes (max(g,x),max(b,x)); append the opposite block (0,b)
  and use D(t-x).
- Discharge the last block only under the assumed NTIME simulation.
  Its replacement exponent is c times the largest of the old tail time,
  the last guess, the input passed by the last block, and the input that
  block *received*. The latter is the preceding block's pass exponent,
  or one at the beginning.

Both endpoints must be deterministic, no interior line may be deterministic,
and the checker asks for a **strict** exponent contraction. A failed test is
only a failed template. Williams also treats equal endpoints under the
full theorem; this checker deliberately does not use that case.

Why the endpoints give a contradiction: a contraction D(a) contained in
D(b), a>b, translates under padding to contractions at progressively larger
exponents. Iterating forces all polynomial-time D classes into D(b).
The *same assumption* NTIME[N] contained in D(c) then puts arbitrarily large
polynomial nondeterministic time classes into D(b), hence into co-nondeterministic
time of smaller exponent, contradicting the alternating time hierarchy
(take a constant slack for the o(1) factors). Merely writing down D(a)
contained in D(b) and invoking the ordinary deterministic time hierarchy
would miss the simultaneous space restriction. See Lemma 4.3 for the proof.

## Two reproducible traces

The three-instruction template starts at D(2), splits with x=1, and
discharges both quantifiers. Its endpoint is D(c^2). Thus it proves a
strict contraction for 1<c<sqrt(2).

The seven-instruction template uses splits x=c^2/2, 1, c^2/2, interleaved
as up,up,down,down,up,down,down. For sqrt(2)<=c<2 its endpoints are
D(2+c^2/2) and D(c^4/2), as in Williams §3. Its strict threshold within
this interval is sqrt((1+sqrt(17))/2), about 1.600485. In particular it
passes at c=1.6004 and does not pass at 1.601. At c=8/5 the checker
calculates time exponents

    82/25, 2, 1, 8/5, 64/25, 32/25, 256/125, 2048/625.

The endpoints differ by exactly 2/625. This is a proof about the class
hypothesis, not arithmetic extrapolated from finitely many SAT instances.

```bash
PYTHONPATH=src python -c "from pnp_lab.alternation_trade import standard_trace; print(standard_trace('8/5'))"
PYTHONPATH=src python -m unittest discover -s tests -p 'test_alternation_trade.py'
```

## What must change to go further?

**Exponent.** Buss and Williams, [*Limits on Alternation-Trading Proofs for
Time-Space Lower Bounds*, Theorem 1.1](https://mathweb.ucsd.edu/~sbuss/ResearchWeb/npProofLimits/paper-journal.pdf)
([publication](https://doi.org/10.1007/s00037-015-0104-9)), show that in
their subpolynomial-space system a contradiction is possible only for
c < 2 cos(pi/7), approximately 1.80194. This is a theorem about the
inference system, not a limit for all SAT lower-bound proofs. The code
neither verifies that upper ceiling nor claims to attain it.

**Space.** In the standard direct checkpoint simulation of time N^a
and space N^s, N^x explicit configurations cost N^(x+s+o(1)) guessed
bits, while replaying a segment costs N^(a-x+o(1)) time. This is the
bookkeeping behind Williams's Lemma 3.3, which carries positive space
exponents explicitly. If we budget at least linear time in N, the best
value of the charge max(1,x+s,a-x) is max(1,(a+s)/2) for a>=1 and
0<=s<=a: the two affine charges balance at x=(a-s)/2, and their average
is a lower bound on their maximum. When s=a the optimum uses x=0 and gives
no strict saving. This diagnostic uses **full snapshots and uniform worst-case
charges**; it is not a lower bound for a different way to check computations,
nor a proof that SAT algorithms must occupy that much space. It does not
extend the checker's subpolynomial-space slowdown rule to positive s.

Even excluding every subpolynomial-space algorithm of every polynomial time
bound would still leave polynomial-time algorithms using polynomial workspace.
Conversely, excluding one specified time exponent for unrestricted space
would still leave higher polynomial exponents. A lower-bound program for
P versus NP must address both quantifiers. A proposed simulation must state
what replaces the full configurations, how their consistency is verified,
and its time and space with both charges included before a new rule is tested.
