import AczelSetTheory.Rationals.Basic
import AczelSetTheory.Rationals.Canonical
import AczelSetTheory.Integers.HFInt
import AczelSetTheory.Rationals.HFRat

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

namespace ℚ₀'
theorem ofQ0_toQ0 (p : ℚ₀') : ofQ0 (toQ0 p) = p := by
  have H : ℚ₀.repr (toQ0 p) = (p.val.1.cls, p.val.2) := by
    change ℚ₀.reduce (p.val.1.cls, p.val.2) = (p.val.1.cls, p.val.2)
    apply reduce_id
    have hp := p.property
    -- hp is (p.val.1 = 0 ∧ p.val.2.val = 𝟙) ∨ (p.val.1 ≠ 0 ∧ Peano.Arith.gcd p.val.1.absNat p.val.2.val = 𝟙)
    -- We need to change p.val.1 = 0 to p.val.1.cls = 0.
    rcases hp with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · left
      have h1_cls : p.val.1.cls = 0 := by
        have h_cls : p.val.1.cls = (0 : HFInt).cls := by rw [h1]
        exact h_cls
      exact ⟨h1_cls, h2⟩
    · right
      have h1_cls : p.val.1.cls ≠ 0 := by
        intro h
        apply h1
        apply HFInt.ext
        exact h
      exact ⟨h1_cls, h2⟩
  apply Subtype.ext
  apply Prod.ext
  · apply HFInt.ext
    change (HFInt.ofZ0 (ℚ₀.repr (toQ0 p)).1).cls = p.val.1.cls
    rw [H]
    rfl
  · change (ℚ₀.repr (toQ0 p)).2 = p.val.2
    rw [H]
end ℚ₀'
