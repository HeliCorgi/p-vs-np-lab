import Lake
open Lake DSL

package pnp_ordinary_pc

require mathlib from git "https://github.com/leanprover-community/mathlib4.git" @
  "67248ba34806c60bf24b5e99f0f09946ffc465c9"

lean_lib claims

@[default_target] lean_lib ProofLab
