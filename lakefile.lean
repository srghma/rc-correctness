import Lake
open Lake DSL

package "rc-correctness" where
  -- Settings applied to both builds and further repository imports

@[default_target]
lean_lib «RcCorrectness» where
  -- Customize the library configuration if necessary
  srcDir := "src"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.11.0"
