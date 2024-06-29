import Lake
open Lake DSL

package «larc» where
  -- add package configuration options here

lean_lib «Larc» where
  -- add library configuration options here

@[default_target]
lean_exe «larc» where
  root := `Main
