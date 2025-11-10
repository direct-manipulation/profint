import Lake
open Lake DSL

package profint { }
lean_lib Profint { }

@[default_target]
lean_exe profint {
  root := `Proof
}
