-- This is the Lean build system/package configuration format
import Lake
open Lake DSL

package bob where
  -- add package configuration options here

lean_lib Bob where
  -- add library configuration options here

@[default_target]
lean_exe bobfilter where
  root := `Main
