import AczelSetTheory.Rationals.Basic
import AczelSetTheory.Rationals.Canonical
import AczelSetTheory.Integers.HFInt
import AczelSetTheory.Rationals.HFRat

open Peano Peano.Arith

theorem le_pair_iff (a b : HFRat) : a ≤ b ↔ a.pair ≤ b.pair := by
  change a.cls ≤ b.cls ↔ ℚ₀'.toQ0 a.pair ≤ ℚ₀'.toQ0 b.pair
  rw [a.hEq, b.hEq]

theorem lt_pair_iff (a b : HFRat) : a < b ↔ a.pair < b.pair := by
  change a.cls < b.cls ↔ ℚ₀'.toQ0 a.pair < ℚ₀'.toQ0 b.pair
  rw [a.hEq, b.hEq]
