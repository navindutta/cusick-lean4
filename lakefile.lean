import Lake
open Lake DSL

package CusickConjecture where
  name := `CusickConjecture

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.14.0"

lean_lib Cusick where
  roots := #[`Cusick.SumOfDigits, `Cusick.BinaryStrings, `Cusick.Density]
