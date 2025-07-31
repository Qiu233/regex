import Lake
open Lake DSL

package "regex" where
  -- add package configuration options here

lean_lib «Regex» where
  -- add library configuration options here

@[default_target]
lean_exe "regex" where
  root := `Main
