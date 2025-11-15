import Lake
open Lake DSL

package Stanley where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩,
    ⟨`weak.linter.mathlibStandardSet, true⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

require checkdecls from git
  "https://github.com/PatrickMassot/checkdecls.git"

@[default_target]
lean_lib Stanley
