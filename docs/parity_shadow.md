# Why even all proper linear projections can miss a parity conflict

The [previous proposed next step](observation_limits.md) was to learn conflicts between parity checks of a 2-CNF relaxation. Here is an all-sizes test of what can be learned **from feasibility after dropping linear information**. The two inputs below have identical answers to *every* rank-deficient linear feasibility query, across every choice of coordinates, yet their full answers differ. The contradiction has a short global certificate visible in the binary clauses.

## Two 2-CNFs on the same options

Let `k ≥ 2`. There are `k` rows and `k−1` options in each row. In the **closed** instance option `(i,j)` uses resource `j`. Forbid every pair of options in the same row or using the same resource, with one negative binary clause per pair. Use zero-based indices. In the **open** instance change only the resource of option `(k−1,k−2)`, assigning it a fresh resource `k−1`. This drops exactly `k−1` conflicting pairs and introduces no new ones. The number of bits and the linear map below are identical. Both ordinary 2-CNFs have full affine hull: the empty assignment and every singleton satisfy them.

Write `s_i(x)` for the parity of the selected options in row `i`, and `u = (1,...,1)`. The full decision query requires `s(x)=u`: at most one option per row was already enforced, so each row must now select exactly one.

* The **closed** instance realizes exactly the syndromes in `F₂^k ∖ {u}`. The selected options form a partial matching. To realize any proper subset of rows, assign its members distinct resources from `0,...,k−2`. To realize all rows would require `k` distinct resources.
* The **open** instance realizes all of `F₂^k`. Choose option `(i,i)` in the first `k−1` rows and the moved option in the last row. This is a perfect matching; any subset of it realizes the desired syndrome.

**Hall cut.** In the closed instance the set of all `k` demanded rows has just `k−1` resource neighbors. The verifier reconstructs those neighbors rather than trusting a reported number. There is an analogous certificate on *any* labelled assignment instance if a set of demanded rows has fewer neighbors than rows. The necessity follows by pigeonhole; the full characterization is [Hall's marriage theorem, 1935](https://doi.org/10.1112/jlms/s1-10.37.26). We do not claim this matching fact is new. The twins use `k(k−1)` bits and O(k³) explicit 2-clauses; matching decides these structured instances in polynomial time. This is not a recognition algorithm for a disguised arbitrary 2-CNF.

## Identical answers under every proper linear observation

Let `H` be **any** binary matrix with `k` columns and rank less than `k`. Allow any number of rows, dense linear combinations, redundant equations, and any right side `b`. The map `s ↦ Hs` has a nonzero kernel. For both instances:

> Some 2-CNF model satisfies `H s(x) = b` if and only if `b` is in the image of `H`.

If `b` is inconsistent, both answers are no. Otherwise the syndrome fiber has at least two points, so it contains a syndrome different from `u`. The closed instance realizes that point; the open one does too. In particular, inspecting all proper subsets of the original equations is insufficient, and **changing basis or adaptively asking feasibility for all lower-rank maps does not help a decision oracle whose only information is those answers**. Taking `H` to be the identity and `b=u` distinguishes the twins. The claim also holds with affine offsets by translating the right side.

This falsifies the proposed local rule as a complete strategy even when the allowed rank grows up to `k−1`. It does **not** lower-bound solvers that read the 2-CNF clauses, count models of the slices, exploit matching structure, or search arbitrary proof systems. Our previous observation solver sees the clauses. Substituting a basis of the affine fiber `s(x)=u` into the binary clauses gives forbidden intersections of at most two affine equations, so this control fits the previous 2-SUB-SAT/affine-event setting. It concerns the displayed parity map, not every possible re-encoding of the task.

## Reproduction

The [implementation](../src/pnp_lab/parity_shadow.py) emits the raw signed clauses and reconstructs matching witnesses for any compatible queried syndrome. It row-reduces `H s=b` with all free bits set to zero: below full rank the particular solution cannot be all ones. In the full-rank inconsistent-with-matching case it returns the unique forced syndrome and the Hall cut separately. An inconsistent linear system alone has no Hall cut.

[Tests](../tests/test_parity_shadow.py) independently enumerate the raw signed CNF assignments of each twin through `k=4`, compare all 512 binary 3-by-3 matrices at all eight right sides, and check witnesses and rejection of invalid Hall cuts on a dense change of basis at `k=64`.

```bash
PYTHONPATH=src python -m unittest discover -s tests -p 'test_parity_shadow.py'
```
