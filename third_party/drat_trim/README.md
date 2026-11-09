# Pinned independent UNSAT checker

Unmodified `drat-trim.c` and MIT license from
[marijnheule/drat-trim](https://github.com/marijnheule/drat-trim/tree/2e3b2dc0ecf938addbd779d42877b6ed69d9a985),
commit `2e3b2dc0ecf938addbd779d42877b6ed69d9a985`.
`manifest.json` records exact source URLs, byte lengths and SHA256 values.

The optional [CDCL runner](../../scripts/run_cdcl_audit.py) verifies these
files and builds the checker with `gcc -O2 -std=gnu99`. The source uses
`getc_unlocked`, so strict ISO C99 without the relevant feature declaration
does not compile on the local compiler; GNU C99 succeeds. No source patch
was made. Binaries, proof files and runtime logs are not vendored.

The default stdlib suite checks the source manifest; it does not execute
this checker. External runs require both zero exit status and an exact
`s VERIFIED` line for each UNSAT certificate, plus rejection of a deliberately
false proof. This is an independent software check, not Lean formalization.
