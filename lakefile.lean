import Lake
open Lake DSL

package verbose {
  -- add package configuration options here
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"@"a7a8e463eb56c18d55ddaac7e75d9cad6bee99b3"

@[defaultTarget]
lean_lib Verbose {
}
