# Auditing a reduction through a streaming algorithm's state

The [previous target](mcsp_streaming_gate.md) would imply P≠NP if proved.
This continuation tries to force a slow update by extracting a difficult
answer from a streaming algorithm's state. **No valid reduction yielding
the target was obtained.** The findings below identify where the attempted
reduction was assuming uncharged computation. They use standard
configuration-simulation arguments and elementary circuit constructions;
no novelty or new complexity separation is claimed.

## 1. Explicitly reaching the state already costs the long input length

Let an instance x of length m describe a truth table T_x on n variables,
with each of its N=2^n entries computable in polynomial time in m+n.
Suppose a streaming algorithm uses polynomial-in-n update time.

Simulating it until it has read all of T_x still performs **N reads**.
The straightforward reduction takes 2^n times a polynomial, even though
the generator, the stream algorithm's storage, and a single update are
small. An entry generator is not the explicit truth-table input required
by ordinary MCSP. A reduction must charge all reads it performs.

In fact a correct deterministic search-MCSP algorithm must inspect the
whole table on every YES input before halting with its circuit output.
If a bit were left unread, flip that bit. The run up to termination and
the returned circuit would be the same, but that circuit cannot compute
both tables. Whether the modified table is YES or NO, the same output is
incorrect on it. This is a linear-in-N input-reading bound, fully consistent
with the permitted N times polynomial-in-n total time; it is not the
desired superpolynomial-in-n update lower bound.

For a polynomial-time reduction on x, useful possibilities include
n=O(log m), a proved polynomial bound on the number of reads actually
needed, or a proved shortcut to the relevant state. No such reduction
has been constructed here. In addition, reducing SAT to a proposed
algorithm would show a conditional upper bound for SAT; NP-hardness
alone would not supply an unconditional lower bound on that algorithm.

## 2. A general state shortcut would imply P=PSPACE

Let F:{0,1}^w -> {0,1}^w be an explicitly given Boolean circuit with w
outputs, z an initial state, and L a nonnegative integer given in binary.
Consider the following decision problem:

\[
        \operatorname{JumpBit}(F,z,L,j)=[F^{L}(z)]_j.
\]

The input length includes the circuit encoding, w-bit state, binary L,
and the output coordinate j. This problem is PSPACE-complete under
polynomial-time reductions, already for the hard family with L=2^w.

**Membership.** Keep the current w-bit state, a log(L+1)-bit counter,
and polynomial workspace for one evaluation of F. Apply F repeatedly,
reusing the workspace. The time may be exponential; the space is
polynomial in the explicit input length. Handle L=0 by returning z_j.

**Hardness.** Let M be any fixed deterministic polynomial-space decider
and let x be its input. Encode a complete configuration in w=poly(|x|)
bits, padding if necessary to include |x| in that bound. Construct a
polynomial-size circuit F_x for one transition. The read-only input x
can be hardwired. A next-configuration circuit is uniformly constructible
in polynomial time: it reads the encoded machine state, head positions
and addressed tape symbols and updates the indicated cells. Make accepting
and rejecting configurations absorbing, and define invalid encodings
arbitrarily so the circuit is a total function.

There are at most 2^w configuration encodings. Before halting, a
deterministic decider cannot repeat a configuration, since it would then
loop. By 2^w transitions it has reached its absorbing halting state.
An acceptance coordinate of F_x^(2^w)(z_x) is therefore M(x). The integer
2^w has only w+1 bits in binary, so the reduction's output has polynomial
length. This applies to every language in PSPACE.

It follows that a **uniform polynomial-time** routine computing the exact
state F^L(z) on all such inputs exists if and only if P=PSPACE. One direction
uses the reduction above; for the other, compute the w output coordinates
using their PSPACE predicates. This is not a proof that P differs from
PSPACE, and that separation is not being assumed.

A stream of L zero bits can simply cause one application of F on each
read. Its update time and memory are polynomial in the description of F.
Thus cheap individual updates do not justify a polynomial-time shortcut
across a long constant stream. Such a general shortcut would itself imply
P=PSPACE, and hence P=NP, a substantially stronger proposed algorithmic
result than a routine implementation optimization.

### Why repeated squaring is not a free shortcut

For a general circuit, constructing F composed with F uses two copies
whose input wires refer to different values. Straightforward repeated
composition can double the circuit size at each squaring. Sharing the
**code** of the composed function in a program does not share the work of
executing its calls on different arguments. This describes the cost of
that construction, not a lower bound on every circuit for the iterated
function.

Alternatively, tabulate the function on all 2^w states and square the
table. That needs exponentially many entries. For affine F over F2,
matrix exponentiation really does give a polynomial-time shortcut; the
matrix representation stays polynomial under composition. No analogous
closed representation is supplied here for arbitrary Boolean transitions.

## 3. Hard state contents can occur on easy MCSP YES inputs

One might avoid computing the entire state and try to derive a lower
bound merely from its containing a hard answer. The following construction
shows why that is insufficient as well.

Encode F,z and the designated acceptance coordinate of a configuration
simulation above as a header H of h bits, using a fixed parseable format.
The initial state is explicit, so w<=h. Put n=2h and use the truth table

\[
       T_H=H\,0^{2^n-h}.
\]

**Every such table has an explicitly constructible circuit within n^2
gates.** For each 1 at a header position i<h, construct the indicator
of the n-bit input i. It has at most n NOT gates and n-1 AND gates.
OR the indicators, or return the zero constant if there are none. If
there are q>0 ones, the count is at most

\[
       q(2n-1)+(q-1)=2nq-1\le 2nh-1=n^2-1.
\]

Construct this circuit by looping over the h header positions, not over
the 2^n truth-table entries. Its description is computable in polynomial
time in h, since n=2h. All these MCSP instances are YES instances, and a
valid output circuit is available directly from the header.

Now consider a fixed auxiliary stream procedure. It reads the first n/2
bits, validates them as a transition-circuit header, and, if valid, applies
F once after each subsequent input bit. On malformed headers or odd n it
disables this auxiliary computation. All stored descriptions are capped
by the header size. Parsing, circuit evaluation, and memory use are
polynomial in n on **all** inputs. No long initialization is hidden.

On T_H it makes 2^n-h transitions. For h>=1 this is at least 2^h>=2^w.
The absorbing acceptance flag thus contains the answer to the PSPACE
computation represented by H. That answer was computed during the
exponentially many input arrivals, with only polynomial work per arrival.

For any **putative** correct MCSP streaming algorithm A with the desired
polynomial space and update/reporting bounds, form B by running A and
this auxiliary procedure in parallel on the same input bits. B returns
exactly A's output and retains the auxiliary flag as an unused state
component. The additional costs are polynomial in n, so B still has
polynomial-in-s=n^2 bounds, with a possibly larger fixed exponent.

This is a conditional wrapper construction: it does not assert that a
fast correct A exists. It shows that adding a PSPACE-answer component
does not invalidate the proposed resource bounds. The exact full state
can therefore require a hard long-run computation without forcing a
slow **individual** update or a difficult MCSP output on the constructed
family. A state-based argument must be invariant under such irrelevant
auxiliary work, or justify why its chosen component is necessary for the
required output. No such necessity theorem was obtained.

## 4. Extracting from an arbitrary compression output has another gate

Suppose a proposed reduction polynomially constructs a circuit C_x of
size within the MCSP budget and uses its truth table T_x as the oracle
instance. Suppose further that a polynomial-time decoder D(x,C) recovers
the answer to a language L for **every** valid size-bounded circuit C
computing T_x. Then

\[
                  x\longmapsto D(x,C_x)
\]

already decides L in polynomial time without the compression solver.
This follows simply because C_x is one permitted output. The observation
does not rule out every use of MCSP in a reduction. It rules out claiming
new information from an arbitrary compression witness when a witness of
the permitted size was already efficiently constructed.

Requiring the solver to return a canonical or minimum circuit would be
a stronger contract than the search problem used in the existing bridge.
Relying on one algorithm's particular output, instead of every valid
witness, would require a separate argument. In either case, the cost of
presenting the exponentially long truth table must still be accounted for.

## Decision and limits

The attempted reduction has not produced a resource-bounded contradiction:

- Explicit simulation charges the entire long stream.
- Uniformly jumping arbitrary state transitions is PSPACE-complete.
- A hard component of a reachable state need not be relevant to MCSP's
  answer and can be computed over many cheap updates.
- An arbitrary returned circuit may be the easily constructed input witness.

PSPACE-completeness is not an unconditional superpolynomial time lower
bound. The deterministic time hierarchy separates P from EXPTIME, but
does not establish P≠PSPACE or make the particular state predicate above
an unconditionally hard language for P. It cannot fill that gap by name.

The **current MCSP proof attempts are parked**: none has supplied the
all-algorithm lower bound. This is a research decision about these
arguments, not a theorem excluding future magnification approaches.
Reopening the branch would require a new mechanism that charges the
actual input and computation, and survives the alternative representations
and auxiliary computations above. We have no such mechanism at present.
No complete P-versus-NP proof or active complete-proof candidate results.

## Bounded check of the easy-input construction

All 30 headers of lengths 1 through 4 were checked, with n=2h. The
constructed circuits matched all 4,680 truth-table entries. Their maximum
gate counts were 3, 14, 33 and 59, within budgets 4, 16, 36 and 64.
This checks the small construction, not PSPACE-hardness or an asymptotic
lower bound. The general gate bound and simulation arguments are the
paper proofs above, with no Lean claim. From the repository root:

```sh
python3 - <<'PY'
from experiments.mcsp_update_gate import BooleanCircuit
cases = checks = 0
for h in range(1, 5):
    n = 2*h
    for header in range(1 << h):
        c = BooleanCircuit(n)
        terms = [c.point_indicator(i) for i in range(h) if header >> i & 1]
        out = terms[0] if terms else 0
        for term in terms[1:]:
            out = c.gate('OR', out, term)
        expected = [header >> i & 1 if i < h else 0 for i in range(1 << n)]
        assert c.table(out) == expected
        assert len(c.gates) <= n*n
        cases += 1
        checks += len(expected)
print(cases, checks)  # 30 4680
PY
```

Only the bounded verification enumerates the whole table. Constructing
the circuit itself uses h positions. No production code, test suite or
Lean source was changed for this continuation.
