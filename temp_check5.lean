import AczelSetTheory.Rationals.Basic
import AczelSetTheory.Rationals.Canonical
import AczelSetTheory.Integers.HFInt

open Peano Peano.Arith

theorem div_one (a : ℕ₀) : a / 𝟙 = a := by
  change Peano.Div.div a 𝟙 = a
  unfold Peano.Div.div Peano.Div.divMod
  split
  · contradiction
  · split
    · rw [‹a = 𝟘›]
    · split
      · rfl
      · contradiction

private theorem reduce_id (p : ℤ₀ × ℕ₁)
    (h : (p.1 = 0 ∧ p.2.val = 𝟙) ∨ (p.1 ≠ 0 ∧ Peano.Arith.gcd (ℤ₀.toNat (ℤ₀.abs p.1)) p.2.val = 𝟙)) :
    ℚ₀.reduce p = p := by
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have h_abs : ℤ₀.toNat (ℤ₀.abs p.1) = 𝟘 := by
      rw [h1, ℤ₀.abs_eq_zero_iff.mpr rfl]
      have hz : (0 : ℤ₀) = ℤ₀.ofNat 0 := rfl
      rw [hz]
      exact ℤ₀.toNat_ofNat 0
    have h_gcd : Peano.Arith.gcd (ℤ₀.toNat (ℤ₀.abs p.1)) p.2.val = 𝟙 := by
      rw [h_abs, h2, Peano.Arith.gcd_zero_left]
    apply Prod.ext
    · change Mul.mul (ℤ₀.sign p.1) (ℤ₀.ofNat (ℤ₀.toNat (ℤ₀.abs p.1) / Peano.Arith.gcd (ℤ₀.toNat (ℤ₀.abs p.1)) p.2.val)) = p.1
      rw [h1, ℤ₀.sign_zero, ℤ₀.zero_mul]
    · apply Subtype.ext
      change p.2.val / Peano.Arith.gcd (ℤ₀.toNat (ℤ₀.abs p.1)) p.2.val = p.2.val
      rw [h_gcd, div_one]
  · apply Prod.ext
    · change Mul.mul (ℤ₀.sign p.1) (ℤ₀.ofNat (ℤ₀.toNat (ℤ₀.abs p.1) / Peano.Arith.gcd (ℤ₀.toNat (ℤ₀.abs p.1)) p.2.val)) = p.1
      have hs : p.1 = Mul.mul (ℤ₀.sign p.1) (ℤ₀.ofNat (ℤ₀.toNat (ℤ₀.abs p.1))) :=
        ℚ₀.self_eq_sign_mul_toNat_abs p.1
      rw [h2, div_one]
      exact hs.symm
    · apply Subtype.ext
      change p.2.val / Peano.Arith.gcd (ℤ₀.toNat (ℤ₀.abs p.1)) p.2.val = p.2.val
      rw [h2, div_one]
