import Lake
open Lake DSL

package «qae_lean» where
  version := v!"0.1.0"

require quantum from git
  "https://github.com/duckki/quantum-computing-lean.git" @ "22f7b16c03a3486da550244cee19b94b993d3de8"

@[default_target]
lean_lib QAELean where
