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

theorem inv_mk (a : ℤ₀) (b : ℕ₁) :
    (mk a b)⁻¹ = mk (invRaw (a, b)).1 (invRaw (a, b)).2 := rfl

theorem mul_inv_cancel {q : ℚ₀} (h : q ≠ 0) : q * q⁻¹ = 1 := by
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
    have h_den1 : ℤ₀.ofNat den1.val = 1 := rfl
    rw [h_den1, ℤ₀.mul_one, ℤ₀.one_mul]
    have h_mulDen : ℤ₀.ofNat (mulDen p.2 (invDen p.1)).val = ℤ₀.ofNat p.2.val * ℤ₀.ofNat (invDen p.1).val := ℤ₀.ofNat_mul p.2.val (invDen p.1).val
    rw [h_mulDen]
    have h_invDen : ℤ₀.ofNat (invDen p.1).val = p.1 := by
      rw [ofNat_invDen_val_eq_abs ha, abs_of_pos hpos]
    rw [h_invDen]
    exact ℤ₀.mul_comm p.1 (ℤ₀.ofNat p.2.val)
  · rw [if_neg hpos]
    rw [one_def, mk_eq_iff]
    have h_den1 : ℤ₀.ofNat den1.val = 1 := rfl
    rw [h_den1, ℤ₀.mul_one, ℤ₀.one_mul]
    have h_mulDen : ℤ₀.ofNat (mulDen p.2 (invDen p.1)).val = ℤ₀.ofNat p.2.val * ℤ₀.ofNat (invDen p.1).val := ℤ₀.ofNat_mul p.2.val (invDen p.1).val
    rw [h_mulDen]
    have h_invDen : ℤ₀.ofNat (invDen p.1).val = -p.1 := by
      rw [ofNat_invDen_val_eq_abs ha, abs_of_neg hpos]
    rw [h_invDen]
    -- p.1 * -ℤ₀.ofNat p.2.val = ℤ₀.ofNat p.2.val * -p.1
    have h1 : p.1 * (-ℤ₀.ofNat p.2.val) = Neg.neg (p.1 * ℤ₀.ofNat p.2.val) := ℤ₀.mul_neg p.1 (ℤ₀.ofNat p.2.val)
    have h2 : ℤ₀.ofNat p.2.val * -p.1 = Neg.neg (ℤ₀.ofNat p.2.val * p.1) := ℤ₀.mul_neg (ℤ₀.ofNat p.2.val) p.1
    have h3 : p.1 * ℤ₀.ofNat p.2.val = ℤ₀.ofNat p.2.val * p.1 := ℤ₀.mul_comm p.1 (ℤ₀.ofNat p.2.val)
    -- We need to prove: p.1 * (-ℤ₀.ofNat p.2.val, invDen p.1).fst = ℤ₀.ofNat p.2.val * -p.1
    -- Actually, we can just use `change` and then `rw`.
    change p.1 * (-ℤ₀.ofNat p.2.val) = ℤ₀.ofNat p.2.val * -p.1
    rw [h1, h2, h3]

theorem inv_mul_cancel {q : ℚ₀} (h : q ≠ 0) : q⁻¹ * q = 1 := by
  rw [mul_comm, mul_inv_cancel h]

theorem inv_unique {x y : ℚ₀} (hx : x ≠ 0) (h : x * y = 1) : y = x⁻¹ := by
  have h1 : x⁻¹ * (x * y) = x⁻¹ * 1 := congrArg (fun z => x⁻¹ * z) h
  rw [← ℚ₀.mul_assoc, inv_mul_cancel hx, one_mul, mul_one] at h1
  exact h1

theorem one_ne_zero : (1 : ℚ₀) ≠ 0 := by
  intro h
  have h1 : ℚ₀.mk (ℤ₀.ofNat 𝟙) den1 = ℚ₀.mk (ℤ₀.ofNat 𝟘) den1 := h
  have h2 := ℚ₀.mk_eq_zero_iff.mp h1
  have h3 : 𝟙 = 𝟘 := ℤ₀.ofNat_injective h2
  cases h3

theorem inv_mul_inv (x y : ℚ₀) (hx : x ≠ 0) (hy : y ≠ 0) : (x * y)⁻¹ = x⁻¹ * y⁻¹ := by
  have h1 : (x * y) * (x⁻¹ * y⁻¹) = 1 := calc
    (x * y) * (x⁻¹ * y⁻¹) = x * (y * (x⁻¹ * y⁻¹)) := ℚ₀.mul_assoc _ _ _
    _ = x * (y * (y⁻¹ * x⁻¹)) := by rw [mul_comm x⁻¹ y⁻¹]
    _ = x * ((y * y⁻¹) * x⁻¹) := by rw [← ℚ₀.mul_assoc y y⁻¹ x⁻¹]
    _ = x * (1 * x⁻¹) := by rw [mul_inv_cancel hy]
    _ = x * x⁻¹ := by rw [one_mul]
    _ = 1 := mul_inv_cancel hx
  have h_xy_ne_0 : x * y ≠ 0 := by
    intro h
    have h2 : (x * y) * (x⁻¹ * y⁻¹) = 0 := by rw [h, zero_mul]
    rw [h1] at h2
    exact one_ne_zero h2
  exact (inv_unique h_xy_ne_0 h1).symm

theorem inv_sub_inv_eq (x y : ℚ₀) (hx : x ≠ 0) (hy : y ≠ 0) :
    x⁻¹ - y⁻¹ = (y - x) * (x * y)⁻¹ := by
  have h1 : (x⁻¹ - y⁻¹) * (x * y) = y - x := by
    calc
      (x⁻¹ - y⁻¹) * (x * y) = Add.add (x⁻¹) (-y⁻¹) * (x * y) := rfl
      _ = Add.add (x⁻¹ * (x * y)) ((-y⁻¹) * (x * y)) := by rw [ℚ₀.right_distrib]
      _ = Add.add ((x⁻¹ * x) * y) ((-y⁻¹) * (x * y)) := by rw [← ℚ₀.mul_assoc]
      _ = Add.add (1 * y) ((-y⁻¹) * (x * y)) := by rw [inv_mul_cancel hx]
      _ = Add.add y ((-y⁻¹) * (x * y)) := by rw [one_mul]
      _ = Add.add y (- (y⁻¹ * (x * y))) := by rw [ℚ₀.neg_mul]
      _ = Add.add y (- (y⁻¹ * (y * x))) := by rw [mul_comm x y]
      _ = Add.add y (- ((y⁻¹ * y) * x)) := by rw [← ℚ₀.mul_assoc]
      _ = Add.add y (- (1 * x)) := by rw [inv_mul_cancel hy]
      _ = Add.add y (- x) := by rw [one_mul]
      _ = y - x := rfl
  have h_xy_ne_0 : x * y ≠ 0 := by
    intro h
    have h_one : (x * y) * (x⁻¹ * y⁻¹) = 1 := calc
      (x * y) * (x⁻¹ * y⁻¹) = x * (y * (x⁻¹ * y⁻¹)) := ℚ₀.mul_assoc _ _ _
      _ = x * (y * (y⁻¹ * x⁻¹)) := by rw [mul_comm x⁻¹ y⁻¹]
      _ = x * ((y * y⁻¹) * x⁻¹) := by rw [← ℚ₀.mul_assoc y y⁻¹ x⁻¹]
      _ = x * (1 * x⁻¹) := by rw [mul_inv_cancel hy]
      _ = x * x⁻¹ := by rw [one_mul]
      _ = 1 := mul_inv_cancel hx
    have h2 : (x * y) * (x⁻¹ * y⁻¹) = 0 := by rw [h, zero_mul]
    rw [h_one] at h2
    exact one_ne_zero h2
  have h2 : ((x⁻¹ - y⁻¹) * (x * y)) * (x * y)⁻¹ = (y - x) * (x * y)⁻¹ := congrArg (fun z => z * (x * y)⁻¹) h1
  rw [ℚ₀.mul_assoc, mul_inv_cancel h_xy_ne_0, mul_one] at h2
  exact h2

theorem inv_nonneg {x : ℚ₀} (hx : 0 ≤ x) (h_ne : x ≠ 0) : 0 ≤ x⁻¹ := by
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
    have h_zero : (0 : ℚ₀) = mk 0 den1 := rfl
    rw [h_zero, mk_le_mk] at hx
    have h_den : ℤ₀.ofNat den1.val = 1 := rfl
    rw [h_den, ℤ₀.mul_one, ℤ₀.zero_mul] at hx
    exact hx
  rw [if_pos hpos]
  change 0 ≤ mk (ℤ₀.ofNat p.2.val) (invDen p.1)
  have h_zero : (0 : ℚ₀) = mk 0 den1 := rfl
  rw [h_zero, mk_le_mk]
  have h_den : ℤ₀.ofNat den1.val = 1 := rfl
  rw [h_den, ℤ₀.mul_one, ℤ₀.zero_mul]
  exact ℤ₀.zero_le_ofNat _

end


end ℚ₀
