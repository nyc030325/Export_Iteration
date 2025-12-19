import Lake
open Lake DSL

package mil where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩, -- pretty-prints `fun a ↦ b`
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩]

@[default_target]
lean_lib test_problem where
lean_lib Optlib where

require mathlib from git "https://github.com/leanprover-community/mathlib4"@"v4.10.0"

