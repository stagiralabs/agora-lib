import Lake
open Lake DSL

package «agora_lib» {
  -- add any package configuration options here
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.17.0"

-- require batteries from git
--  "https://github.com/leanprover-community/batteries.git"

require "leanprover-community" / "batteries" @ git "v4.17.0"

require "leanprover" / "Cli" @ git "v4.17.0"



@[default_target]
lean_lib Library where

@[default_target]
lean_lib Targets where


lean_lib Utils where

@[default_target]
lean_exe get_theorems where
  root := `get_theorems
  supportInterpreter := true
