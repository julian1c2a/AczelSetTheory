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

private theorem eq_zero_of_mul_ofNat_eq_zero {z : ℤ₀} {n : ℕ₁} (h : Mul.mul z (ℤ₀.ofNat n.val) = 0) : z = 0 := by
  have hz_mul : Mul.mul 0 (ℤ₀.ofNat n.val) = 0 := ℤ₀.zero_mul _
  have h1 : Mul.mul z (ℤ₀.ofNat n.val) ≤ Mul.mul 0 (ℤ₀.ofNat n.val) := by rw [h, hz_mul]; exact ℤ₀.le_refl 0
  have h2 : Mul.mul 0 (ℤ₀.ofNat n.val) ≤ Mul.mul z (ℤ₀.ofNat n.val) := by rw [h, hz_mul]; exact ℤ₀.le_refl 0
  have hz1 : z ≤ 0 := (ℤ₀.mul_le_mul_right_ofNat_pos n.property z 0).mpr h1
  have hz2 : 0 ≤ z := (ℤ₀.mul_le_mul_right_ofNat_pos n.property 0 z).mpr h2
  exact ℤ₀.le_antisymm hz1 hz2

private theorem ofNat_invDen_val_eq_abs {z : ℤ₀} (h : z ≠ 0) : ℤ₀.ofNat (invDen z).val = ℤ₀.abs z := by
  unfold invDen
  rw [dif_neg h]
  have h_abs_nonneg : 0 ≤ ℤ₀.abs z := ℤ₀.abs_nonneg z
  exact (ℤ₀.nonneg_eq_ofNat h_abs_nonneg).symm

private theorem abs_of_pos {z : ℤ₀} (h : 0 ≤ z) : ℤ₀.abs z = z := by
  unfold ℤ₀.abs
  rw [if_pos h]

private theorem abs_of_neg {z : ℤ₀} (h : ¬0 ≤ z) : ℤ₀.abs z = -z := by
  unfold ℤ₀.abs
  rw [if_neg h]

private theorem invWD (p q : ℤ₀ × ℕ₁) (h : Mul.mul p.1 (ℤ₀.ofNat q.2.val) = Mul.mul q.1 (ℤ₀.ofNat p.2.val)) :
    Mul.mul (invRaw p).1 (ℤ₀.ofNat (invRaw q).2.val) = Mul.mul (invRaw q).1 (ℤ₀.ofNat (invRaw p).2.val) := by
  unfold invRaw
  by_cases h_p : p.1 = 0
  · by_cases h_q : q.1 = 0
    · simp [h_p, h_q]
    · -- p.1 = 0, q.1 ≠ 0: contradiction
      have h1 : Mul.mul q.1 (ℤ₀.ofNat p.2.val) = 0 := by
        rw [← h, h_p, ℤ₀.zero_mul]
      have hq_zero : q.1 = 0 := eq_zero_of_mul_ofNat_eq_zero h1
      exact False.elim (h_q hq_zero)
  · by_cases h_q : q.1 = 0
    · -- p.1 ≠ 0, q.1 = 0: contradiction
      have h1 : Mul.mul p.1 (ℤ₀.ofNat q.2.val) = 0 := by
        rw [h, h_q, ℤ₀.zero_mul]
      have hp_zero : p.1 = 0 := eq_zero_of_mul_ofNat_eq_zero h1
      exact False.elim (h_p hp_zero)
    · -- p.1 ≠ 0, q.1 ≠ 0
      by_cases hp_pos : 0 ≤ p.1
      · by_cases hq_pos : 0 ≤ q.1
        · -- 0 ≤ p.1, 0 ≤ q.1
          simp [h_p, h_q, hp_pos, hq_pos]
          have h1 : ℤ₀.ofNat (invDen q.1).val = q.1 := by
            rw [ofNat_invDen_val_eq_abs h_q, abs_of_pos hq_pos]
          have h2 : ℤ₀.ofNat (invDen p.1).val = p.1 := by
            rw [ofNat_invDen_val_eq_abs h_p, abs_of_pos hp_pos]
          rw [h1, h2]
          -- Goal: p.2 * q.1 = q.2 * p.1
          rw [ℤ₀.mul_comm, ← h, ℤ₀.mul_comm]
        · -- 0 ≤ p.1, ¬ (0 ≤ q.1)
          simp [h_p, h_q, hp_pos, hq_pos]
          have h1 : ℤ₀.ofNat (invDen q.1).val = -q.1 := by
            rw [ofNat_invDen_val_eq_abs h_q, abs_of_neg hq_pos]
          have h2 : ℤ₀.ofNat (invDen p.1).val = p.1 := by
            rw [ofNat_invDen_val_eq_abs h_p, abs_of_pos hp_pos]
          rw [h1, h2]
          -- Goal: p.2 * -q.1 = -q.2 * p.1
          rw [ℤ₀.mul_neg, ℤ₀.neg_mul]
          congr 1
          rw [ℤ₀.mul_comm, ← h, ℤ₀.mul_comm]
      · by_cases hq_pos : 0 ≤ q.1
        · -- ¬ (0 ≤ p.1), 0 ≤ q.1
          simp [h_p, h_q, hp_pos, hq_pos]
          have h1 : ℤ₀.ofNat (invDen q.1).val = q.1 := by
            rw [ofNat_invDen_val_eq_abs h_q, abs_of_pos hq_pos]
          have h2 : ℤ₀.ofNat (invDen p.1).val = -p.1 := by
            rw [ofNat_invDen_val_eq_abs h_p, abs_of_neg hp_pos]
          rw [h1, h2]
          -- Goal: -p.2 * q.1 = q.2 * -p.1
          rw [ℤ₀.neg_mul, ℤ₀.mul_neg]
          congr 1
          rw [ℤ₀.mul_comm, ← h, ℤ₀.mul_comm]
        · -- ¬ (0 ≤ p.1), ¬ (0 ≤ q.1)
          simp [h_p, h_q, hp_pos, hq_pos]
          have h1 : ℤ₀.ofNat (invDen q.1).val = -q.1 := by
            rw [ofNat_invDen_val_eq_abs h_q, abs_of_neg hq_pos]
          have h2 : ℤ₀.ofNat (invDen p.1).val = -p.1 := by
            rw [ofNat_invDen_val_eq_abs h_p, abs_of_neg hp_pos]
          rw [h1, h2]
          -- Goal: -p.2 * -q.1 = -q.2 * -p.1
          rw [ℤ₀.neg_mul, ℤ₀.mul_neg, ℤ₀.neg_neg]
          rw [ℤ₀.neg_mul, ℤ₀.mul_neg, ℤ₀.neg_neg]
          rw [ℤ₀.mul_comm, ← h, ℤ₀.mul_comm]

def inv (a : ℚ₀) : ℚ₀ := Quotient.liftOn a
  (fun p => mk (invRaw p).1 (invRaw p).2)
  (fun p q h => Quotient.sound (invWD p q h))

instance : Inv ℚ₀ := ⟨inv⟩

instance : Div ℚ₀ := ⟨fun a b => a * b⁻¹⟩

end

end ℚ₀
