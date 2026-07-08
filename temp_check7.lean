import Peano.PeanoNat.Arith
open Peano Peano.Arith

theorem coprime_gcd_eq_one {a b : ℕ₀} (h : Coprime a b) : gcd a b = 𝟙 := by
  have hg := IsGCD_gcd a b
  -- Since both 𝟙 and gcd a b are GCDs, they must be equal.
  -- Is there IsGCD_unique?
  sorry
