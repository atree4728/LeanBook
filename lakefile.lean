import Lake
open Lake DSL

package «LeanBook» where
  version := v!"0.1.0"

lean_lib «LeanBook» where

@[default_target]
lean_lib "LakeBook" where
  globs := #[.submodules `LeanBook]
