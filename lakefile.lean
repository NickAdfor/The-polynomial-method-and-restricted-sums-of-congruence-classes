import Lake
open Lake DSL

package Stanley where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩,
    ⟨`weak.linter.mathlibStandardSet, true⟩
  ]
  moreLinkArgs := #[
    "-L./.lake/packages/LeanCopilot/.lake/build/lib",
    "-lctranslate2"
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.25.0"

require checkdecls from git
  "https://github.com/PatrickMassot/checkdecls.git"

@[default_target]
lean_lib Stanley
