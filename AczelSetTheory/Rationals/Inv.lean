/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

import AczelSetTheory.Rationals.Basic
import AczelSetTheory.Integers.Functions

namespace ℚ₀cls

open Peano Peano.Axioms Peano.Add Peano.Mul Peano.Order

private def absNat (z : ℤ₀cls) : ℕ₀ := ℤ₀cls.toNat (ℤ₀cls.abs z)

private theorem absNat_ne_zero {z : ℤ₀cls} (h : z ≠ 0) : absNat z ≠ 𝟘 := by
  intro h_abs
  unfold absNat at h_abs
  have h_abs_nonneg : (0:ℤ₀cls) ≤ ℤ₀cls.abs z := ℤ₀cls.abs_nonneg z
  have h_eq : ℤ₀cls.abs z = ℤ₀cls.ofNat (ℤ₀cls.abs z).repr.1 := ℤ₀cls.nonneg_eq_ofNat h_abs_nonneg
  have h_toNat : ℤ₀cls.toNat (ℤ₀cls.abs z) = (ℤ₀cls.abs z).repr.1 := rfl
  rw [← h_toNat, h_abs] at h_eq
  have h_abs_zero : ℤ₀cls.abs z = 0 := by
    rw [h_eq]
    exact ℤ₀cls.ofNat_zero
  have h_z_zero : z = 0 := ℤ₀cls.abs_eq_zero_iff.mp h_abs_zero
  exact h h_z_zero

private def invDen (z : ℤ₀cls) : ℕ₁ :=
  if h : z = 0 then ⟨𝟙, succ_neq_zero 𝟘⟩
  else ⟨absNat z, absNat_ne_zero h⟩

private def invRaw (p : ℤ₀cls × ℕ₁) : ℤ₀cls × ℕ₁ :=
  if p.1 = 0 then (0, ⟨𝟙, succ_neq_zero 𝟘⟩)
  else if 0 ≤ p.1 then (ℤ₀cls.ofNat p.2.val, invDen p.1)
  else (- ℤ₀cls.ofNat p.2.val, invDen p.1)

private theorem eq_zero_of_mul_ofNat_eq_zero {z : ℤ₀cls} {n : ℕ₁} (h : Mul.mul z (ℤ₀cls.ofNat n.val) = 0) : z = 0 := by
  have hz_mul : Mul.mul 0 (ℤ₀cls.ofNat n.val) = 0 := ℤ₀cls.zero_mul _
  have h1 : Mul.mul z (ℤ₀cls.ofNat n.val) ≤ Mul.mul 0 (ℤ₀cls.ofNat n.val) := by rw [h, hz_mul]; exact ℤ₀cls.le_refl 0
  have h2 : Mul.mul 0 (ℤ₀cls.ofNat n.val) ≤ Mul.mul z (ℤ₀cls.ofNat n.val) := by rw [h, hz_mul]; exact ℤ₀cls.le_refl 0
  have hz1 : z ≤ 0 := (ℤ₀cls.mul_le_mul_right_ofNat_pos n.property z 0).mpr h1
  have hz2 : 0 ≤ z := (ℤ₀cls.mul_le_mul_right_ofNat_pos n.property 0 z).mpr h2
  exact ℤ₀cls.le_antisymm hz1 hz2

private theorem ofNat_invDen_val_eq_abs {z : ℤ₀cls} (h : z ≠ 0) : ℤ₀cls.ofNat (invDen z).val = ℤ₀cls.abs z := by
  unfold invDen
  rw [dif_neg h]
  have h_abs_nonneg : 0 ≤ ℤ₀cls.abs z := ℤ₀cls.abs_nonneg z
  exact (ℤ₀cls.nonneg_eq_ofNat h_abs_nonneg).symm

private theorem abs_of_pos {z : ℤ₀cls} (h : 0 ≤ z) : ℤ₀cls.abs z = z := by
  unfold ℤ₀cls.abs
  rw [if_pos h]

private theorem abs_of_neg {z : ℤ₀cls} (h : ¬0 ≤ z) : ℤ₀cls.abs z = -z := by
  unfold ℤ₀cls.abs
  rw [if_neg h]

private theorem invWD (p q : ℤ₀cls × ℕ₁) (h : Mul.mul p.1 (ℤ₀cls.ofNat q.2.val) = Mul.mul q.1 (ℤ₀cls.ofNat p.2.val)) :
    Mul.mul (invRaw p).1 (ℤ₀cls.ofNat (invRaw q).2.val) = Mul.mul (invRaw q).1 (ℤ₀cls.ofNat (invRaw p).2.val) := by
  unfold invRaw
  by_cases h_p : p.1 = 0
  · by_cases h_q : q.1 = 0
    · simp [h_p, h_q]
    · -- p.1 = 0, q.1 ≠ 0: contradiction
      have h1 : Mul.mul q.1 (ℤ₀cls.ofNat p.2.val) = 0 := by
        rw [← h, h_p, ℤ₀cls.zero_mul]
      have hq_zero : q.1 = 0 := eq_zero_of_mul_ofNat_eq_zero h1
      exact False.elim (h_q hq_zero)
  · by_cases h_q : q.1 = 0
    · -- p.1 ≠ 0, q.1 = 0: contradiction
      have h1 : Mul.mul p.1 (ℤ₀cls.ofNat q.2.val) = 0 := by
        rw [h, h_q, ℤ₀cls.zero_mul]
      have hp_zero : p.1 = 0 := eq_zero_of_mul_ofNat_eq_zero h1
      exact False.elim (h_p hp_zero)
    · -- p.1 ≠ 0, q.1 ≠ 0
      by_cases hp_pos : 0 ≤ p.1
      · by_cases hq_pos : 0 ≤ q.1
        · -- 0 ≤ p.1, 0 ≤ q.1
          simp [h_p, h_q, hp_pos, hq_pos]
          have h1 : ℤ₀cls.ofNat (invDen q.1).val = q.1 := by
            rw [ofNat_invDen_val_eq_abs h_q, abs_of_pos hq_pos]
          have h2 : ℤ₀cls.ofNat (invDen p.1).val = p.1 := by
            rw [ofNat_invDen_val_eq_abs h_p, abs_of_pos hp_pos]
          rw [h1, h2]
          -- Goal: p.2 * q.1 = q.2 * p.1
          rw [ℤ₀cls.mul_comm, ← h, ℤ₀cls.mul_comm]
        · -- 0 ≤ p.1, ¬ (0 ≤ q.1)
          simp [h_p, h_q, hp_pos, hq_pos]
          have h1 : ℤ₀cls.ofNat (invDen q.1).val = -q.1 := by
            rw [ofNat_invDen_val_eq_abs h_q, abs_of_neg hq_pos]
          have h2 : ℤ₀cls.ofNat (invDen p.1).val = p.1 := by
            rw [ofNat_invDen_val_eq_abs h_p, abs_of_pos hp_pos]
          rw [h1, h2]
          -- Goal: p.2 * -q.1 = -q.2 * p.1
          rw [ℤ₀cls.mul_neg, ℤ₀cls.neg_mul]
          congr 1
          rw [ℤ₀cls.mul_comm, ← h, ℤ₀cls.mul_comm]
      · by_cases hq_pos : 0 ≤ q.1
        · -- ¬ (0 ≤ p.1), 0 ≤ q.1
          simp [h_p, h_q, hp_pos, hq_pos]
          have h1 : ℤ₀cls.ofNat (invDen q.1).val = q.1 := by
            rw [ofNat_invDen_val_eq_abs h_q, abs_of_pos hq_pos]
          have h2 : ℤ₀cls.ofNat (invDen p.1).val = -p.1 := by
            rw [ofNat_invDen_val_eq_abs h_p, abs_of_neg hp_pos]
          rw [h1, h2]
          -- Goal: -p.2 * q.1 = q.2 * -p.1
          rw [ℤ₀cls.neg_mul, ℤ₀cls.mul_neg]
          congr 1
          rw [ℤ₀cls.mul_comm, ← h, ℤ₀cls.mul_comm]
        · -- ¬ (0 ≤ p.1), ¬ (0 ≤ q.1)
          simp [h_p, h_q, hp_pos, hq_pos]
          have h1 : ℤ₀cls.ofNat (invDen q.1).val = -q.1 := by
            rw [ofNat_invDen_val_eq_abs h_q, abs_of_neg hq_pos]
          have h2 : ℤ₀cls.ofNat (invDen p.1).val = -p.1 := by
            rw [ofNat_invDen_val_eq_abs h_p, abs_of_neg hp_pos]
          rw [h1, h2]
          -- Goal: -p.2 * -q.1 = -q.2 * -p.1
          rw [ℤ₀cls.neg_mul, ℤ₀cls.mul_neg, ℤ₀cls.neg_neg]
          rw [ℤ₀cls.neg_mul, ℤ₀cls.mul_neg, ℤ₀cls.neg_neg]
          rw [ℤ₀cls.mul_comm, ← h, ℤ₀cls.mul_comm]

def inv (a : ℚ₀cls) : ℚ₀cls := Quotient.liftOn a
  (fun p => mk (invRaw p).1 (invRaw p).2)
  (fun p q h => Quotient.sound (invWD p q h))

instance : Inv ℚ₀cls := ⟨inv⟩

instance : Div ℚ₀cls := ⟨fun a b => a * b⁻¹⟩

theorem inv_mk (a : ℤ₀cls) (b : ℕ₁) :
    (mk a b)⁻¹ = mk (invRaw (a, b)).1 (invRaw (a, b)).2 := rfl

theorem mul_inv_cancel {q : ℚ₀cls} (h : q ≠ 0) : q * q⁻¹ = 1 := by
  revert h
  refine Quotient.inductionOn q (fun p hp => ?_)
  change mk p.1 p.2 * (mk p.1 p.2)⁻¹ = 1
  have ha : p.1 ≠ 0 := by
    intro ha_zero
    apply hp
    exact mk_eq_zero_iff.mpr ha_zero
  have h_mk : mk p.1 p.2 * (mk p.1 p.2)⁻¹ = mk (p.1 * (invRaw p).1) (mulDen p.2 (invRaw p).2) := rfl
  rw [h_mk]
  unfold invRaw
  rw [if_neg ha]
  by_cases hpos : 0 ≤ p.1
  · rw [if_pos hpos]
    rw [one_def, mk_eq_iff]
    -- Goal: p.1 * p.2.val * 1 = 1 * (p.2.val * invDen p.1)
    have h_den1 : ℤ₀cls.ofNat den1.val = 1 := rfl
    rw [h_den1, ℤ₀cls.mul_one, ℤ₀cls.one_mul]
    have h_mulDen : ℤ₀cls.ofNat (mulDen p.2 (invDen p.1)).val = ℤ₀cls.ofNat p.2.val * ℤ₀cls.ofNat (invDen p.1).val := ℤ₀cls.ofNat_mul p.2.val (invDen p.1).val
    rw [h_mulDen]
    have h_invDen : ℤ₀cls.ofNat (invDen p.1).val = p.1 := by
      rw [ofNat_invDen_val_eq_abs ha, abs_of_pos hpos]
    rw [h_invDen]
    exact ℤ₀cls.mul_comm p.1 (ℤ₀cls.ofNat p.2.val)
  · rw [if_neg hpos]
    rw [one_def, mk_eq_iff]
    have h_den1 : ℤ₀cls.ofNat den1.val = 1 := rfl
    rw [h_den1, ℤ₀cls.mul_one, ℤ₀cls.one_mul]
    have h_mulDen : ℤ₀cls.ofNat (mulDen p.2 (invDen p.1)).val = ℤ₀cls.ofNat p.2.val * ℤ₀cls.ofNat (invDen p.1).val := ℤ₀cls.ofNat_mul p.2.val (invDen p.1).val
    rw [h_mulDen]
    have h_invDen : ℤ₀cls.ofNat (invDen p.1).val = -p.1 := by
      rw [ofNat_invDen_val_eq_abs ha, abs_of_neg hpos]
    rw [h_invDen]
    -- p.1 * -ℤ₀cls.ofNat p.2.val = ℤ₀cls.ofNat p.2.val * -p.1
    have h1 : p.1 * (-ℤ₀cls.ofNat p.2.val) = Neg.neg (p.1 * ℤ₀cls.ofNat p.2.val) := ℤ₀cls.mul_neg p.1 (ℤ₀cls.ofNat p.2.val)
    have h2 : ℤ₀cls.ofNat p.2.val * -p.1 = Neg.neg (ℤ₀cls.ofNat p.2.val * p.1) := ℤ₀cls.mul_neg (ℤ₀cls.ofNat p.2.val) p.1
    have h3 : p.1 * ℤ₀cls.ofNat p.2.val = ℤ₀cls.ofNat p.2.val * p.1 := ℤ₀cls.mul_comm p.1 (ℤ₀cls.ofNat p.2.val)
    -- We need to prove: p.1 * (-ℤ₀cls.ofNat p.2.val, invDen p.1).fst = ℤ₀cls.ofNat p.2.val * -p.1
    -- Actually, we can just use `change` and then `rw`.
    change p.1 * (-ℤ₀cls.ofNat p.2.val) = ℤ₀cls.ofNat p.2.val * -p.1
    rw [h1, h2, h3]

theorem inv_mul_cancel {q : ℚ₀cls} (h : q ≠ 0) : q⁻¹ * q = 1 := by
  rw [mul_comm, mul_inv_cancel h]

theorem inv_unique {x y : ℚ₀cls} (hx : x ≠ 0) (h : x * y = 1) : y = x⁻¹ := by
  have h1 : x⁻¹ * (x * y) = x⁻¹ * 1 := congrArg (fun z => x⁻¹ * z) h
  rw [← ℚ₀cls.mul_assoc, inv_mul_cancel hx, one_mul, mul_one] at h1
  exact h1

theorem one_ne_zero : (1 : ℚ₀cls) ≠ 0 := by
  intro h
  have h1 : ℚ₀cls.mk (ℤ₀cls.ofNat 𝟙) den1 = ℚ₀cls.mk (ℤ₀cls.ofNat 𝟘) den1 := h
  have h2 := ℚ₀cls.mk_eq_zero_iff.mp h1
  have h3 : 𝟙 = 𝟘 := ℤ₀cls.ofNat_injective h2
  cases h3

theorem inv_mul_inv (x y : ℚ₀cls) (hx : x ≠ 0) (hy : y ≠ 0) : (x * y)⁻¹ = x⁻¹ * y⁻¹ := by
  have h1 : (x * y) * (x⁻¹ * y⁻¹) = 1 := calc
    (x * y) * (x⁻¹ * y⁻¹) = x * (y * (x⁻¹ * y⁻¹)) := ℚ₀cls.mul_assoc _ _ _
    _ = x * (y * (y⁻¹ * x⁻¹)) := by rw [mul_comm x⁻¹ y⁻¹]
    _ = x * ((y * y⁻¹) * x⁻¹) := by rw [← ℚ₀cls.mul_assoc y y⁻¹ x⁻¹]
    _ = x * (1 * x⁻¹) := by rw [mul_inv_cancel hy]
    _ = x * x⁻¹ := by rw [one_mul]
    _ = 1 := mul_inv_cancel hx
  have h_xy_ne_0 : x * y ≠ 0 := by
    intro h
    have h2 : (x * y) * (x⁻¹ * y⁻¹) = 0 := by rw [h, zero_mul]
    rw [h1] at h2
    exact one_ne_zero h2
  exact (inv_unique h_xy_ne_0 h1).symm

theorem inv_sub_inv_eq (x y : ℚ₀cls) (hx : x ≠ 0) (hy : y ≠ 0) :
    x⁻¹ - y⁻¹ = (y - x) * (x * y)⁻¹ := by
  have h1 : (x⁻¹ - y⁻¹) * (x * y) = y - x := by
    calc
      (x⁻¹ - y⁻¹) * (x * y) = Add.add (x⁻¹) (-y⁻¹) * (x * y) := rfl
      _ = Add.add (x⁻¹ * (x * y)) ((-y⁻¹) * (x * y)) := by rw [ℚ₀cls.right_distrib]
      _ = Add.add ((x⁻¹ * x) * y) ((-y⁻¹) * (x * y)) := by rw [← ℚ₀cls.mul_assoc]
      _ = Add.add (1 * y) ((-y⁻¹) * (x * y)) := by rw [inv_mul_cancel hx]
      _ = Add.add y ((-y⁻¹) * (x * y)) := by rw [one_mul]
      _ = Add.add y (- (y⁻¹ * (x * y))) := by rw [ℚ₀cls.neg_mul]
      _ = Add.add y (- (y⁻¹ * (y * x))) := by rw [mul_comm x y]
      _ = Add.add y (- ((y⁻¹ * y) * x)) := by rw [← ℚ₀cls.mul_assoc]
      _ = Add.add y (- (1 * x)) := by rw [inv_mul_cancel hy]
      _ = Add.add y (- x) := by rw [one_mul]
      _ = y - x := rfl
  have h_xy_ne_0 : x * y ≠ 0 := by
    intro h
    have h_one : (x * y) * (x⁻¹ * y⁻¹) = 1 := calc
      (x * y) * (x⁻¹ * y⁻¹) = x * (y * (x⁻¹ * y⁻¹)) := ℚ₀cls.mul_assoc _ _ _
      _ = x * (y * (y⁻¹ * x⁻¹)) := by rw [mul_comm x⁻¹ y⁻¹]
      _ = x * ((y * y⁻¹) * x⁻¹) := by rw [← ℚ₀cls.mul_assoc y y⁻¹ x⁻¹]
      _ = x * (1 * x⁻¹) := by rw [mul_inv_cancel hy]
      _ = x * x⁻¹ := by rw [one_mul]
      _ = 1 := mul_inv_cancel hx
    have h2 : (x * y) * (x⁻¹ * y⁻¹) = 0 := by rw [h, zero_mul]
    rw [h_one] at h2
    exact one_ne_zero h2
  have h2 : ((x⁻¹ - y⁻¹) * (x * y)) * (x * y)⁻¹ = (y - x) * (x * y)⁻¹ := congrArg (fun z => z * (x * y)⁻¹) h1
  rw [ℚ₀cls.mul_assoc, mul_inv_cancel h_xy_ne_0, mul_one] at h2
  exact h2

theorem inv_nonneg {x : ℚ₀cls} (hx : 0 ≤ x) (h_ne : x ≠ 0) : 0 ≤ x⁻¹ := by
  revert hx h_ne
  refine Quotient.inductionOn x (fun p hx h_ne => ?_)
  change 0 ≤ (mk p.1 p.2)⁻¹
  rw [inv_mk]
  have ha : p.1 ≠ 0 := by
    intro ha_zero
    apply h_ne
    exact mk_eq_zero_iff.mpr ha_zero
  unfold invRaw
  rw [if_neg ha]
  have hpos : 0 ≤ p.1 := by
    change 0 ≤ mk p.1 p.2 at hx
    have h_zero : (0 : ℚ₀cls) = mk 0 den1 := rfl
    rw [h_zero, mk_le_mk] at hx
    have h_den : ℤ₀cls.ofNat den1.val = 1 := rfl
    rw [h_den, ℤ₀cls.mul_one, ℤ₀cls.zero_mul] at hx
    exact hx
  rw [if_pos hpos]
  change 0 ≤ mk (ℤ₀cls.ofNat p.2.val) (invDen p.1)
  have h_zero : (0 : ℚ₀cls) = mk 0 den1 := rfl
  rw [h_zero, mk_le_mk]
  have h_den : ℤ₀cls.ofNat den1.val = 1 := rfl
  rw [h_den, ℤ₀cls.mul_one, ℤ₀cls.zero_mul]
  exact ℤ₀cls.zero_le_ofNat _

-- ─────────────────────────────────────────────────────────────────────────────
-- Orden e inversa: si 1 ≤ q entonces q⁻¹ ≤ 1
-- ─────────────────────────────────────────────────────────────────────────────

private theorem zero_le_one_inv : (0 : ℚ₀cls) ≤ 1 := by
  have h0 : (0 : ℚ₀cls) = mk 0 den1 := rfl
  have h1 : (1 : ℚ₀cls) = mk 1 den1 := rfl
  rw [h0, h1, mk_le_mk]
  have hd : ℤ₀cls.ofNat den1.val = (1 : ℤ₀cls) := rfl
  rw [hd, ℤ₀cls.mul_one, ℤ₀cls.mul_one]
  exact ℤ₀cls.zero_le_ofNat 𝟙

/-- Si `1 ≤ q` entonces `q⁻¹ ≤ 1`. -/
theorem inv_le_one {q : ℚ₀cls} (hq : 1 ≤ q) : q⁻¹ ≤ 1 := by
  have hq0 : q ≠ 0 := fun h => one_ne_zero (le_antisymm (h ▸ hq) zero_le_one_inv)
  have hqnn : 0 ≤ q := le_trans zero_le_one_inv hq
  have hinn : 0 ≤ q⁻¹ := inv_nonneg hqnn hq0
  have h1 : q⁻¹ * 1 ≤ q⁻¹ * q := mul_le_mul_left_of_nonneg hq hinn
  rw [mul_one, inv_mul_cancel hq0] at h1
  exact h1

end ℚ₀cls
