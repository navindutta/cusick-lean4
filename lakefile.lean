import Lake
open Lake DSL

package «cusick-conjecture» where
  name := `CusickConjecture

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.14.0"

lean_lib «Cusick» where
  srcDir := "."
