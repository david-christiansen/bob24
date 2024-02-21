-- This is the Lean build system/package configuration format
import Lake
open Lake DSL

require std from git "https://github.com/leanprover/std4" @ "main"

package bob where
  -- add package configuration options here

lean_lib Bob where
  -- add library configuration options here

@[default_target]
lean_exe bob where
  root := `Main
