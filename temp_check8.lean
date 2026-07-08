import Peano.PeanoNat.Arith
import Peano.PeanoNat.Primes
open Peano Peano.Arith

theorem gcd_eq_one_of_coprime {a b : ℕ₀} (h : Coprime a b) : gcd a b = 𝟙 := by
  have hg := IsGCD_gcd a b
  have hd : gcd a b ∣ 𝟙 := h.2.2 (gcd a b) ⟨hg.1, hg.2.1⟩
  rcases hd with ⟨c, hc⟩
  exact (Peano.Primes.mul_eq_one hc.symm).1
