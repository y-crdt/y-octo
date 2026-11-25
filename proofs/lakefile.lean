import Lake
open Lake DSL

require aeneas from "../.proof-tools/backends/lean"
require «yocto-spec» from "../proofs-yata"

package yoctoCore

@[default_target]
lean_lib YoctoCore
