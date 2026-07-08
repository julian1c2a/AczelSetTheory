import AczelSetTheory.Rationals.Basic
import AczelSetTheory.Rationals.Canonical
import AczelSetTheory.Integers.HFInt
import AczelSetTheory.Rationals.HFRat

open Peano Peano.Arith

namespace HFRat_test

def add (a b : HFRat) : HFRat :=
  { cls  := a.cls + b.cls
    pair := a.pair + b.pair
    hEq  := by
      -- we need to prove ℚ₀'.toQ0 (a.pair + b.pair) = a.cls + b.cls
      -- a.pair + b.pair is defined as ℚ₀'.ofQ0 (ℚ₀'.toQ0 a.pair + ℚ₀'.toQ0 b.pair)
      change ℚ₀'.toQ0 (ℚ₀'.ofQ0 (ℚ₀'.toQ0 a.pair + ℚ₀'.toQ0 b.pair)) = a.cls + b.cls
      rw [ℚ₀'.toQ0_ofQ0]
      rw [a.hEq, b.hEq]
  }

end HFRat_test
