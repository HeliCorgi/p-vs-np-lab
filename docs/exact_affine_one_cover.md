# Phase 25: exact affine one-cover number for binary inner product

## Hypothesis and prespecified stopping rule

**H:** For every integer \(m\ge1\), the minimum number of nonempty Boolean
affine flats contained in the positive level of \(Q_m(x,y)=x\cdot y\) required
to cover the positive level is exactly \(2^m-1\). This improves the
nonoptimal \(2^{m-2}\) lower bound verified in
[phase 24](affine_cover_circuit_boundary.md).

**Falsifiers:** (i) a positive affine flat of dimension at least \(m\);
(ii) the positive-level cardinality differs from
\((2^m-1)2^{m-1}\); or (iii) the proposed \(2^m-1\)-flat partition fails.
**Budget and stop:** exhaustively enumerate every affine flat only for
\(m=1,2,3\); finish a general linear-algebra argument, test it independently,
and stop. Do not increase the finite benchmark to substitute for proof.

## Theorem and full mathematical proof

Let \(V=\mathbb F_2^m\), \(m\ge1\), with standard dot product, and
\[
Q_m(x,y)=\sum_{i=1}^m x_iy_i\bmod2,\qquad
P_m=\{(x,y)\in V\times V:Q_m(x,y)=1\}.
\]
An *affine one-cover* is a finite indexed family of affine flats
\(A_j=a_j+U_j\subseteq P_m\) whose union contains \(P_m\).
Repetitions and overlaps are allowed. These are flats on the **original**
\(2m\) input bits, without auxiliary coordinates.

**Lemma 1 (sharp positive-flat dimension).** If \(A=a+U\subseteq P_m\),
then \(\dim U\le m-1\), and hence \(|A|\le 2^{m-1}\).

*Proof.* Project onto the first block, \(\pi_x:V\times V\to V\), and
write \(X=\pi_x(A)=a_x+L\), where \(L=\pi_x(U)\), \(r=\dim L\).
Put \(K=\{v\in V:(0,v)\in U\}\), \(k=\dim K\). The kernel of
\(\pi_x|_U\) is isomorphic to \(K\); rank-nullity gives
\(\dim U=r+k\).

For every \((x,y)\in A\) and \(v\in K\), also \((x,y+v)\in A\).
The two values of \(Q_m\) equal one, so \(x\cdot v=0\). Thus
\(X\subseteq K^\perp\). Also \(0\notin X\), because \(0\cdot y\ne1\)
for every \(y\). The standard dot product is nondegenerate, hence
\(K^\perp\) is a linear space of dimension \(m-k\).
The direction \(L=X-X\) is a subspace of \(K^\perp\). If
\(r=m-k\), then \(L=K^\perp\) and the nonempty affine translate
\(X=a_x+L\subseteq K^\perp\) equals all \(K^\perp\), including zero:
contradiction. Therefore \(r\le m-k-1\) and
\(\dim U=r+k\le m-1\). □

**Lemma 2 (exact positive-level cardinality).**
\(|P_m|=(2^m-1)2^{m-1}\).

*Proof.* With \(x=0\) there is no positive \(y\).
For each \(x\ne0\), the linear form \(y\mapsto x\cdot y\)
is nonzero, so its level-one fiber has \(2^{m-1}\) elements.
There are \(2^m-1\) such \(x\). □

**Theorem.** The exact minimum cover number \(c_m\) satisfies
\[
\boxed{c_m=2^m-1\quad\text{for every }m\ge1.}
\]

*Proof.* If \(P_m\subseteq\bigcup_{j=1}^s A_j\subseteq P_m\),
then by Lemmas 1–2 and the union bound,
\[
(2^m-1)2^{m-1}=|P_m|
 \le \sum_{j=1}^s|A_j|
 \le s2^{m-1}.
\]
Because \(2^{m-1}>0\), \(s\ge2^m-1\), regardless of repetitions
or overlap. Conversely, for each fixed \(x\ne0\), define
\[
A_x=\{x\}\times\{y\in V:x\cdot y=1\}.
\]
These are disjoint affine \((m-1)\)-flats indexed by the \(2^m-1\)
nonzero vectors \(x\), and their union is \(P_m\). This gives
\(s\le2^m-1\) and proves equality. □

**Circuit comparison.** As recorded in phase 24, the function
\(Q_m\) has a uniform AND/OR/NOT circuit of \(5m-4\) gates.
The exact original-variable positive affine cover requires
\(2^m-1\) flats. Thus no polynomial in *arbitrary circuit size*
bounds this exact original-variable affine-cover size in general.
This is a representation lower bound, NOT a Boolean circuit lower
bound, a SAT proof lower bound, or a P vs NP resolution.

## Reproducible finite checks

The script
[experiments/exact_affine_one_cover.py](../experiments/exact_affine_one_cover.py)
enumerates every RREF direction subspace and each coset; no random
sampling or SAT oracle is used. The separate
[unittest](../tests/test_exact_affine_one_cover.py) independently computes
the inner product, verifies the Gaussian-binomial numbers of subspaces
and checks the entire finite output. The deterministic
[JSON report](../results/exact_affine_one_cover.json) stores results.

| m | Positive points | Maximum positive flat dimension | Positive flats by dimension | Optimal cover |
|---|---:|---:|---|---:|
| 1 | 1 | 0 | d=0: 1 | 1 |
| 2 | 6 | 1 | d=0: 6; d=1: 15 | 3 |
| 3 | 28 | 2 | d=0: 28; d=1: 378; d=2: 315 | 7 |

Run from the repository root on Python 3.10+:
```bash
python experiments/exact_affine_one_cover.py
python -m unittest discover -s tests -p 'test_exact_affine_one_cover.py' -v
```
The all-\(m\) conclusion comes from the mathematical proof above,
**not** from the finite samples. No new Lean claim is made in this
phase. Phase-24 Lean proves a weaker dimension bound and remains intact.

## Primary sources and related context

- O. S. Rothaus, *On “Bent” Functions*, J. Combinatorial Theory A
  **20** (1976), 300–305,
  [doi:10.1016/0097-3165(76)90024-8](https://doi.org/10.1016/0097-3165(76)90024-8).
- J. F. Dillon, *Elementary Hadamard Difference Sets*, University
  of Maryland PhD thesis (1974),
  [institutional record](https://drum.lib.umd.edu/items/d8150b1f-1bdd-4c3d-9987-c14a95251edc).

These are primary sources for bent-function/Boolean Fourier and finite
geometric background, **not** citations claiming that they prove this
specific exact-cover formulation. We make no novelty/priority claim.
The direct proof uses only standard finite-dimensional linear algebra.

## Remaining gap and next adversarial test

This closes one specific original-variable *representation* measure.
The general-algorithm quantifier of P vs NP is untouched. A bounded
next test is to build a *Tseitin auxiliary-variable encoding* of the
linear-size AND/XOR circuit for \(Q_m=1\), verify that projection of
its witnesses gives exactly \(P_m\), and inspect an explicitly
specified proof/algorithm simulation with bit and gate costs.
The present affine-cover bound must **not** be transferred to that
extended representation. Separately, formalization of the published
expander PC separator and the full phase-20 DAG lower bound remain open.
Do not rerun larger flat enumerations in lieu of these tests.
