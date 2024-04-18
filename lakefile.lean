import Lake
open Lake DSL

package «INDPRO» where
  -- add package configuration options here

lean_lib «INDPRO» where
  -- add library configuration options here

@[default_target]
lean_exe «indpro» where
  root := `Main
