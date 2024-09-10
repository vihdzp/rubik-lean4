import Lake
open Lake DSL

package "rubik" where
  -- add package configuration options here

lean_lib «Rubik» where
  -- add library configuration options here

require mathlib from git
  "https://github.com/leanprover-community/mathlib4"

@[default_target]
lean_exe "rubik" where
  root := `Main