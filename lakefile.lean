import Lake
open Lake DSL

package dmdanal {
  -- add package configuration options here
}

require mathlib from git "https://github.com/leanprover-community/mathlib4.git"

lean_lib DmdAnal {
  -- add library configuration options here
}

-- @[defaultTarget]
lean_exe dmdanal {
  root := `DmdAnal
}
