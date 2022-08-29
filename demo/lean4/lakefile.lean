import Lake
open Lake DSL

package profint { }
lean_lib Profint { }

@[defaultTarget]
lean_exe profint {
  root := `Proof
}
