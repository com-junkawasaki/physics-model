import Lake
open Lake DSL

package "physics-model" where
  version := v!"0.1.0"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.23.0"

require «time» from git
  "https://github.com/com-junkawasaki/time.git" @
    "d9b56f386c4cf3e2f597864c0b75c4ff7d25a950"

require «inc-rqm» from git
  "https://github.com/com-junkawasaki/inc-RQM.git" @
    "e5f72e1a26a490cc3321c391e9dfd12e47042878"

lean_lib "PhysicsModel" where

@[default_target]
lean_exe "physics-model" where
  root := `Main
  supportInterpreter := true
