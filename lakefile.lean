import Lake
open Lake DSL

package «math_480_project» {
  -- add any package configuration options here
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib «Math480Project» {
  -- add any library configuration options here
}
