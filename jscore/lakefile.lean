import Lake
open Lake DSL

package jscore where
  leanOptions := #[
    ⟨`autoImplicit, false⟩
  ]

lean_lib JSCore where
  srcDir := "."
