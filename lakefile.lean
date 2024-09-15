import Lake
open Lake DSL

require "leanprover-community" / "Qq" @ git "v4.11.0"

package "regex" where
  -- add package configuration options here

lean_lib «Regex» where
  -- add library configuration options here

@[default_target]
lean_exe "regex" where
  root := `Main
