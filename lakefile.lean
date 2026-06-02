import Lake
open Lake DSL

require "leanprover-community" / "mathlib" @ git "v4.28.0"

package «SchurComplement» where

@[default_target]
lean_lib «SchurComplement» where
