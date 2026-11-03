# Selected OpenAI math source snapshot

Source: [openai/math](https://github.com/openai/math/tree/4eaee87548250b2682affda7d05d947c05554bae),
commit `4eaee87548250b2682affda7d05d947c05554bae` (2026-10-30).

The manuscript credits OpenAI. These selected upstream sources are redistributed
under the upstream [Apache License 2.0](LICENSE). Full copies are unchanged.
The two excerpts have prominent modification/provenance comments and preserve
the selected mathematical text. Their source intervals and all file hashes are
recorded in [manifest.json](manifest.json).

This is a compact, inspectable source snapshot, **not a complete Lean project**
and not an independent verification of the upstream theorem. In particular:

- `lean/docs/378.md` records exactly which runtime statement upstream formalizes.
- `lean/ComparatorChallenges/SubexponentialSAT.lean` is the **challenge
  specification**. Its expected `sorry` is not an implementation proof.
- `lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/Final.lean` is the actual
  endpoint proof source. Its thousands of transitive imports are intentionally
  absent from this compact snapshot.
- `SqrtLogSpace/Asymptotics.lean` and `SqrtLogSpace/NativeLargeEntry.lean`, under
  that same source directory, retain the exact integer schedule and the
  large-input cutoff conditions for independent parameter experiments.
- `paper/measurement-separation-excerpt.tex` contains the integer measurement
  identity, explicit hypotheses, enumeration cost, and the warning that small
  integer rank alone does not bound the number of signatures.
- `lean/docs/102.md` records the scope of the Unique Games and approximation
  reductions; it is a research lead, not a P-versus-NP separation.

Upstream uses Lean 4.34.1 with Mathlib. This repository's small `Formal/` library
keeps its own Lean 4.19.0 toolchain. These files are not imported into that build.
The pinned upstream audit must run in a separate package and record its actual
outcome. A timeout, unavailable dependency, or unfinished comparator check is
not a successful verification.

See [the reuse and audit note](../../docs/openai_math_reuse.md) for the
claim/evidence boundary, selected algorithmic reuse, and build details.
Upstream-relative links in unmodified copies may require following the canonical
`upstream_url` fields in the manifest.
