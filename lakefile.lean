import Lake
open Lake DSL

package «residua»

-- BEGIN RCIC
-- RCIC: the R-CIC kernel theory (lean/rcic) and the SHA-256 model it uses.
-- `ResiduaSHA256` is built with default arguments, as in the Residua development
-- tree, so build traces agree module by module.
lean_lib «ResiduaSHA256» where
  srcDir := "lean"
  roots := #[`Residua.SHA256]

@[default_target]
lean_lib «RCIC» where
  srcDir := "lean"
  globs := #[.submodules `rcic]
  weakLeanArgs := #["--tstack=65536"]
  moreLeanArgs := #["--tstack=65536"]

-- RCICCore: only the core results (in-scope rows, subject reduction, type
-- uniqueness, machine soundness) and their import closure.
lean_lib «RCICCore» where
  srcDir := "lean"
  roots := #[`rcic.RcicCore]
  moreLeanArgs := #["--tstack=65536"]
-- END RCIC
