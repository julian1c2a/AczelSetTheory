import AczelSetTheory.Rationals.Basic
import AczelSetTheory.Rationals.Canonical
import AczelSetTheory.Integers.HFInt

open Peano Peano.Arith

private theorem reduce_id (p : ℤ₀ × ℕ₁)
    (h : (p.1 = 0 ∧ p.2.val = 𝟙) ∨ (p.1 ≠ 0 ∧ Peano.Arith.gcd (ℤ₀.toNat (ℤ₀.abs p.1)) p.2.val = 𝟙)) :
    ℚ₀.reduce p = p := by
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have h_abs : ℤ₀.toNat (ℤ₀.abs p.1) = 𝟘 := by rw [h1]; exact rfl
    have h_gcd : Peano.Arith.gcd (ℤ₀.toNat (ℤ₀.abs p.1)) p.2.val = 𝟙 := by
      rw [h_abs, h2, Peano.Arith.gcd_zero_left]
    apply Prod.ext
    · change Mul.mul (ℤ₀.sign p.1) (ℤ₀.ofNat (ℤ₀.toNat (ℤ₀.abs p.1) / Peano.Arith.gcd (ℤ₀.toNat (ℤ₀.abs p.1)) p.2.val)) = p.1
      rw [h1, ℤ₀.sign_zero, Peano.Mul.zero_mul]
    · apply Subtype.ext
      change p.2.val / Peano.Arith.gcd (ℤ₀.toNat (ℤ₀.abs p.1)) p.2.val = p.2.val
      simp only [h_gcd, Peano.Div.div_one]
  · apply Prod.ext
    · change Mul.mul (ℤ₀.sign p.1) (ℤ₀.ofNat (ℤ₀.toNat (ℤ₀.abs p.1) / Peano.Arith.gcd (ℤ₀.toNat (ℤ₀.abs p.1)) p.2.val)) = p.1
      have hs : p.1 = Peano.Mul.mul (ℤ₀.sign p.1) (ℤ₀.ofNat (ℤ₀.toNat (ℤ₀.abs p.1))) :=
        ℚ₀.self_eq_sign_mul_toNat_abs p.1
      simp only [h2, Peano.Div.div_one]
      exact hs.symm
    · apply Subtype.ext
      change p.2.val / Peano.Arith.gcd (ℤ₀.toNat (ℤ₀.abs p.1)) p.2.val = p.2.val
      simp only [h2, Peano.Div.div_one]
