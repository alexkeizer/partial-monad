import Lake
open Lake DSL

package «partial-monad» where
  -- add package configuration options here

lean_lib «PartialMonad» where
  -- add library configuration options here

require std from git "https://github.com/leanprover/std4" @ "main"
require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "master"

@[default_target]
lean_exe «partial-monad» where
  root := `Main
