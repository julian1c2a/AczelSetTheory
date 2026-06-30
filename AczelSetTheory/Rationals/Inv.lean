import AczelSetTheory.Rationals.Basic
import AczelSetTheory.Integers.Functions

namespace ℚ₀

open Peano Peano.Axioms Peano.Add Peano.Mul Peano.Order

private def absNat (z : ℤ₀) : ℕ₀ := ℤ₀.toNat (ℤ₀.abs z)

private theorem absNat_ne_zero {z : ℤ₀} (h : z ≠ 0) : absNat z ≠ 𝟘 := by
  intro h_abs
  unfold absNat at h_abs
  have h_abs_nonneg : (0:ℤ₀) ≤ ℤ₀.abs z := ℤ₀.abs_nonneg z
  have h_eq : ℤ₀.abs z = ℤ₀.ofNat (ℤ₀.abs z).repr.1 := ℤ₀.nonneg_eq_ofNat h_abs_nonneg
  have h_toNat : ℤ₀.toNat (ℤ₀.abs z) = (ℤ₀.abs z).repr.1 := rfl
  rw [← h_toNat, h_abs] at h_eq
  have h_abs_zero : ℤ₀.abs z = 0 := by
    rw [h_eq]
    exact ℤ₀.ofNat_zero
  have h_z_zero : z = 0 := ℤ₀.abs_eq_zero_iff.mp h_abs_zero
  exact h h_z_zero

noncomputable section

open Classical

private noncomputable def invDen (z : ℤ₀) : ℕ₁ :=
  if h : z = 0 then ⟨𝟙, succ_neq_zero 𝟘⟩
  else ⟨absNat z, absNat_ne_zero h⟩

private noncomputable def invRaw (p : ℤ₀ × ℕ₁) : ℤ₀ × ℕ₁ :=
  if p.1 = 0 then (0, ⟨𝟙, succ_neq_zero 𝟘⟩)
  else if 0 ≤ p.1 then (ℤ₀.ofNat p.2.val, invDen p.1)
  else (- ℤ₀.ofNat p.2.val, invDen p.1)

private theorem invWD (p q : ℤ₀ × ℕ₁) (h : Mul.mul p.1 (ℤ₀.ofNat q.2.val) = Mul.mul q.1 (ℤ₀.ofNat p.2.val)) :
    Mul.mul (invRaw p).1 (ℤ₀.ofNat (invRaw q).2.val) = Mul.mul (invRaw q).1 (ℤ₀.ofNat (invRaw p).2.val) := by
  sorry

def inv (a : ℚ₀) : ℚ₀ := Quotient.liftOn a
  (fun p => mk (invRaw p).1 (invRaw p).2)
  (fun p q h => Quotient.sound (invWD p q h))

instance : Inv ℚ₀ := ⟨inv⟩

instance : Div ℚ₀ := ⟨fun a b => a * b⁻¹⟩

end

end ℚ₀
