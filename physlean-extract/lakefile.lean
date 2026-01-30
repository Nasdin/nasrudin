import Lake
open Lake DSL

package PhysLeanExtract where
  leanOptions := #[
    ⟨`autoImplicit, false⟩
  ]

lean_lib PhysLeanExtract where
  srcDir := "."

lean_exe extract where
  root := `PhysLeanExtract.Main

require PhysLean from git
  "https://github.com/HEPLean/PhysLean.git" @ "master"
