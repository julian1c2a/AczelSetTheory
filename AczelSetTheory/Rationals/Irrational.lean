/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

import AczelSetTheory.Rationals.Roots
import AczelSetTheory.Rationals.Archimedean
import AczelSetTheory.Integers.Functions
import AczelSetTheory.Integers.Order
import Peano.PeanoNat.Combinatorics.Pow

open Peano Peano.Axioms Peano.Order

namespace ℤ₀cls

private theorem one_le_of_ne_zero_nat {n : ℕ₀} (h : n ≠ 𝟘) : le₀ 𝟙 n := by
  cases n with
  | zero => exact False.elim (h rfl)
  | succ k => exact succ_le_succ_if_wp (zero_le k)

private theorem sub_eq_add_neg (a b : ℤ₀cls) : Sub.sub a b = Add.add a (Neg.neg b) := rfl

private theorem sub_ne_zero_of_ne {x y : ℤ₀cls} (h : x ≠ y) : Sub.sub x y ≠ 0 := by
  intro heq
  have h1 : Add.add (Sub.sub x y) y = Add.add 0 y := congrArg (fun a => Add.add a y) heq
  rw [sub_eq_add_neg, add_assoc, neg_add_self, add_zero, zero_add] at h1
  exact h h1

/-- Lema de Separación en enteros: Si x e y son enteros distintos, su diferencia absoluta es mayor o igual a 1. -/
theorem int_sep_lemma (x y : ℤ₀cls) (h : x ≠ y) : (1:ℤ₀cls) ≤ ℤ₀cls.abs (Sub.sub x y) := by
  have h_ne : Sub.sub x y ≠ 0 := sub_ne_zero_of_ne h
  have hz : ℤ₀cls.abs (Sub.sub x y) ≠ 0 := fun hz_eq => h_ne (ℤ₀cls.abs_eq_zero_iff.mp hz_eq)
  have h_nonneg : 0 ≤ ℤ₀cls.abs (Sub.sub x y) := ℤ₀cls.abs_nonneg _
  have h_eq : ℤ₀cls.abs (Sub.sub x y) = ℤ₀cls.ofNat (ℤ₀cls.toNat (ℤ₀cls.abs (Sub.sub x y))) :=
    ℤ₀cls.nonneg_eq_ofNat h_nonneg
  have h_n_ne : ℤ₀cls.toNat (ℤ₀cls.abs (Sub.sub x y)) ≠ 𝟘 := by
    intro hn
    have h_abs_zero : ℤ₀cls.abs (Sub.sub x y) = 0 := by
      calc ℤ₀cls.abs (Sub.sub x y) = ℤ₀cls.ofNat (ℤ₀cls.toNat (ℤ₀cls.abs (Sub.sub x y))) := h_eq
           _ = ℤ₀cls.ofNat 𝟘 := congrArg ℤ₀cls.ofNat hn
           _ = 0 := ℤ₀cls.ofNat_zero
    exact hz h_abs_zero
  have h_le_nat : le₀ 𝟙 (ℤ₀cls.toNat (ℤ₀cls.abs (Sub.sub x y))) := one_le_of_ne_zero_nat h_n_ne
  have h_le_int : ℤ₀cls.ofNat 𝟙 ≤ ℤ₀cls.ofNat (ℤ₀cls.toNat (ℤ₀cls.abs (Sub.sub x y))) :=
    ℤ₀cls.le_ofNat_iff.mpr h_le_nat
  have h_one : (1:ℤ₀cls) = ℤ₀cls.ofNat 𝟙 := rfl
  rw [h_one, h_eq]
  exact h_le_int

/-- Lema de Separación para potencias: Si a^n y m * b^n son distintos, su diferencia absoluta es ≥ 1 -/
theorem int_sep_pow_lemma (a b m : ℤ₀cls) (n : ℕ₀) (h : ℤ₀cls.powZ a n ≠ Mul.mul m (ℤ₀cls.powZ b n)) :
    (1:ℤ₀cls) ≤ ℤ₀cls.abs (Sub.sub (ℤ₀cls.powZ a n) (Mul.mul m (ℤ₀cls.powZ b n))) :=
  int_sep_lemma (ℤ₀cls.powZ a n) (Mul.mul m (ℤ₀cls.powZ b n)) h

end ℤ₀cls

namespace ℚ₀cls

def powN1 (b : ℕ₁) (n : ℕ₀) : ℕ₁ := 
  ⟨Peano.Pow.pow b.val n, Peano.Pow.pow_ne_zero b.property n⟩

theorem powN1_zero (b : ℕ₁) : powN1 b 𝟘 = den1 := rfl

theorem pow_mk (a : ℤ₀cls) (b : ℕ₁) (n : ℕ₀) : 
  pow (mk a b) n = mk (ℤ₀cls.powZ a n) (powN1 b n) := by
  induction n with
  | zero =>
    have h1 : pow (mk a b) 𝟘 = ofNat₀ 𝟙 := rfl
    have h2 : ℤ₀cls.powZ a 𝟘 = 1 := rfl
    have h_ofNat₀ : ofNat₀ 𝟙 = mk 1 den1 := ofNat₀_eq_mk 𝟙
    rw [h1, h_ofNat₀, h2]
    rfl
  | succ k ih =>
    change Mul.mul (mk a b) (pow (mk a b) k) = mk (Mul.mul (ℤ₀cls.powZ a k) a) (powN1 b (σ k))
    rw [ih]
    rw [mul_mk]
    have h_num : Mul.mul a (ℤ₀cls.powZ a k) = Mul.mul (ℤ₀cls.powZ a k) a := ℤ₀cls.mul_comm _ _
    rw [h_num]
    apply congrArg (mk (Mul.mul (ℤ₀cls.powZ a k) a))
    have h_den : (mulDen b (powN1 b k)).val = (powN1 b (σ k)).val := by
      change Peano.Mul.mul b.val (Peano.Pow.pow b.val k) = Peano.Mul.mul (Peano.Pow.pow b.val k) b.val
      exact Peano.Mul.mul_comm _ _
    exact Subtype.ext h_den

theorem ofInt_eq_mk (m : ℤ₀cls) : ofInt m = mk m den1 := rfl

theorem powZ_ofNat_eq (b : ℕ₀) (n : ℕ₀) : ℤ₀cls.ofNat (Peano.Pow.pow b n) = ℤ₀cls.powZ (ℤ₀cls.ofNat b) n := by
  induction n with
  | zero =>
    change ℤ₀cls.ofNat 𝟙 = 1
    exact ℤ₀cls.ofNat_one
  | succ k ih =>
    change ℤ₀cls.ofNat (Peano.Mul.mul (Peano.Pow.pow b k) b) = Mul.mul (ℤ₀cls.powZ (ℤ₀cls.ofNat b) k) (ℤ₀cls.ofNat b)
    rw [ℤ₀cls.ofNat_mul]
    rw [ih]

theorem rational_not_root (a : ℤ₀cls) (b : ℕ₁) (m : ℤ₀cls) (n : ℕ₀) 
  (h_irr : ∀ a' b', ℤ₀cls.powZ a' n ≠ Mul.mul m (ℤ₀cls.powZ (ℤ₀cls.ofNat b') n)) : 
  pow (mk a b) n ≠ ofInt m := by
  intro heq
  rw [pow_mk] at heq
  have h_ofInt : ofInt m = mk m den1 := rfl
  rw [h_ofInt] at heq
  have h_eq_iff := mk_eq_iff (ℤ₀cls.powZ a n) m (powN1 b n) den1
  rw [h_eq_iff] at heq
  have h_den1 : ℤ₀cls.ofNat den1.val = 1 := rfl
  rw [h_den1] at heq
  rw [ℤ₀cls.mul_one] at heq
  have h_irr_spec := h_irr a b.val
  have h_powZ_b : ℤ₀cls.ofNat (powN1 b n).val = ℤ₀cls.powZ (ℤ₀cls.ofNat b.val) n := powZ_ofNat_eq b.val n
  rw [h_powZ_b] at heq
  exact h_irr_spec heq

def pow_bound (x y : ℚ₀cls) : ℕ₀ → ℚ₀cls
  | 𝟘 => 0
  | σ k => Add.add (Mul.mul x (pow_bound x y k)) (pow y k)

theorem add_sub_cancel' (x y : ℚ₀cls) : Add.add y (Sub.sub x y) = x := by
  change Add.add y (Add.add x (Neg.neg y)) = x
  rw [add_comm x (Neg.neg y)]
  rw [← add_assoc]
  rw [add_comm y (Neg.neg y)]
  rw [neg_add_self y]
  rw [zero_add]

theorem mul_assoc_mul (a b c : ℚ₀cls) : Mul.mul (Mul.mul a b) c = Mul.mul a (Mul.mul b c) := mul_assoc a b c
theorem mul_comm_mul (a b : ℚ₀cls) : Mul.mul a b = Mul.mul b a := mul_comm a b
theorem add_assoc_add (a b c : ℚ₀cls) : Add.add (Add.add a b) c = Add.add a (Add.add b c) := add_assoc a b c
theorem add_comm_add (a b : ℚ₀cls) : Add.add a b = Add.add b a := add_comm a b

theorem pow_sub_eq (x y : ℚ₀cls) (n : ℕ₀) : 
  pow x n = Add.add (pow y n) (Mul.mul (Sub.sub x y) (pow_bound x y n)) := by
  induction n with
  | zero =>
    have h1 : pow x 𝟘 = 1 := rfl
    have h2 : pow y 𝟘 = 1 := rfl
    have h3 : pow_bound x y 𝟘 = 0 := rfl
    rw [h1, h2, h3]
    have h_mul : Mul.mul (Sub.sub x y) 0 = 0 := mul_zero _
    rw [h_mul]
    exact (add_zero _).symm
  | succ k ih =>
    have h_pow_x : pow x (σ k) = Mul.mul x (pow x k) := rfl
    rw [h_pow_x]
    rw [ih]
    have hd1 : Mul.mul x (Add.add (pow y k) (Mul.mul (Sub.sub x y) (pow_bound x y k))) = Add.add (Mul.mul x (pow y k)) (Mul.mul x (Mul.mul (Sub.sub x y) (pow_bound x y k))) := left_distrib x _ _
    rw [hd1]
    have h_bound : pow_bound x y (σ k) = Add.add (Mul.mul x (pow_bound x y k)) (pow y k) := rfl
    rw [h_bound]
    have hd2 : Mul.mul (Sub.sub x y) (Add.add (Mul.mul x (pow_bound x y k)) (pow y k)) = Add.add (Mul.mul (Sub.sub x y) (Mul.mul x (pow_bound x y k))) (Mul.mul (Sub.sub x y) (pow y k)) := left_distrib (Sub.sub x y) _ _
    rw [hd2]
    have h_pow_y : pow y (σ k) = Mul.mul y (pow y k) := rfl
    rw [h_pow_y]
    have h1 : Mul.mul (Sub.sub x y) (Mul.mul x (pow_bound x y k)) = Mul.mul x (Mul.mul (Sub.sub x y) (pow_bound x y k)) := by
      rw [← mul_assoc_mul, mul_comm_mul (Sub.sub x y) x, mul_assoc_mul]
    rw [h1]
    have h2 : Add.add (Mul.mul y (pow y k)) (Add.add (Mul.mul (Sub.sub x y) (Mul.mul x (pow_bound x y k))) (Mul.mul (Sub.sub x y) (pow y k))) = 
              Add.add (Add.add (Mul.mul y (pow y k)) (Mul.mul (Sub.sub x y) (pow y k))) (Mul.mul (Sub.sub x y) (Mul.mul x (pow_bound x y k))) := by
      have step1 := (add_assoc_add (Mul.mul y (pow y k)) (Mul.mul (Sub.sub x y) (Mul.mul x (pow_bound x y k))) (Mul.mul (Sub.sub x y) (pow y k))).symm
      have step2 := congrArg (fun a => Add.add a (Mul.mul (Sub.sub x y) (pow y k))) (add_comm_add (Mul.mul y (pow y k)) (Mul.mul (Sub.sub x y) (Mul.mul x (pow_bound x y k))))
      have step3 := add_assoc_add (Mul.mul (Sub.sub x y) (Mul.mul x (pow_bound x y k))) (Mul.mul y (pow y k)) (Mul.mul (Sub.sub x y) (pow y k))
      have step4 := add_comm_add (Mul.mul (Sub.sub x y) (Mul.mul x (pow_bound x y k))) (Add.add (Mul.mul y (pow y k)) (Mul.mul (Sub.sub x y) (pow y k)))
      exact Eq.trans step1 (Eq.trans step2 (Eq.trans step3 step4))
    have h3 : Add.add (Mul.mul y (pow y k)) (Mul.mul (Sub.sub x y) (pow y k)) = Mul.mul x (pow y k) := by
      have hd3 : Mul.mul (Add.add y (Sub.sub x y)) (pow y k) = Add.add (Mul.mul y (pow y k)) (Mul.mul (Sub.sub x y) (pow y k)) := right_distrib y (Sub.sub x y) (pow y k)
      have hd3_symm := hd3.symm
      have hsub := add_sub_cancel' x y
      have hd3_sub := congrArg (fun a => Mul.mul a (pow y k)) hsub
      exact Eq.trans hd3_symm hd3_sub
    have h_final : Add.add (Mul.mul x (pow y k)) (Mul.mul x (Mul.mul (Sub.sub x y) (pow_bound x y k))) = 
                   Add.add (Mul.mul y (pow y k)) (Add.add (Mul.mul x (Mul.mul (Sub.sub x y) (pow_bound x y k))) (Mul.mul (Sub.sub x y) (pow y k))) := by
      have step1 := congrArg (fun a => Add.add a (Mul.mul x (Mul.mul (Sub.sub x y) (pow_bound x y k)))) h3.symm
      have step2 := congrArg (fun a => Add.add (Add.add (Mul.mul y (pow y k)) (Mul.mul (Sub.sub x y) (pow y k))) a) h1.symm
      have step3 := Eq.trans step1 step2
      have step4_1 := add_assoc_add (Mul.mul y (pow y k)) (Mul.mul (Sub.sub x y) (pow y k)) (Mul.mul (Sub.sub x y) (Mul.mul x (pow_bound x y k)))
      have step4_2 := congrArg (fun a => Add.add (Mul.mul y (pow y k)) a) (add_comm_add (Mul.mul (Sub.sub x y) (pow y k)) (Mul.mul (Sub.sub x y) (Mul.mul x (pow_bound x y k))))
      have step4_3 := Eq.trans step4_1 step4_2
      have step4_4 := congrArg (fun a => Add.add (Mul.mul y (pow y k)) (Add.add a (Mul.mul (Sub.sub x y) (pow y k)))) h1
      have step4 := Eq.trans step4_3 step4_4
      exact Eq.trans step3 step4
    exact h_final

theorem pow_nonneg (y : ℚ₀cls) (hy : 0 ≤ y) (n : ℕ₀) : 0 ≤ pow y n := by
  induction n with
  | zero =>
    have h : pow y 𝟘 = 1 := rfl
    rw [h]
    exact ofNat₀_nonneg 1
  | succ k ih =>
    have h : pow y (σ k) = Mul.mul y (pow y k) := rfl
    rw [h]
    exact mul_nonneg hy ih

theorem pow_bound_nonneg (x y : ℚ₀cls) (hx : 0 ≤ x) (hy : 0 ≤ y) (n : ℕ₀) : 0 ≤ pow_bound x y n := by
  induction n with
  | zero =>
    have h : pow_bound x y 𝟘 = 0 := rfl
    rw [h]
    exact le_refl 0
  | succ k ih =>
    have h : pow_bound x y (σ k) = Add.add (Mul.mul x (pow_bound x y k)) (pow y k) := rfl
    rw [h]
    have h1 : 0 ≤ Mul.mul x (pow_bound x y k) := mul_nonneg hx ih
    have h2 : 0 ≤ pow y k := pow_nonneg y hy k
    exact add_nonneg h1 h2

theorem pow_bound_mono (x1 x2 y : ℚ₀cls) (hx1 : 0 ≤ x1) (hy : 0 ≤ y) (h : x1 ≤ x2) (n : ℕ₀) : 
  pow_bound x1 y n ≤ pow_bound x2 y n := by
  induction n with
  | zero =>
    have h1 : pow_bound x1 y 𝟘 = 0 := rfl
    have h2 : pow_bound x2 y 𝟘 = 0 := rfl
    rw [h1, h2]
    exact le_refl 0
  | succ k ih =>
    have hb1 : pow_bound x1 y (σ k) = Add.add (Mul.mul x1 (pow_bound x1 y k)) (pow y k) := rfl
    have hb2 : pow_bound x2 y (σ k) = Add.add (Mul.mul x2 (pow_bound x2 y k)) (pow y k) := rfl
    rw [hb1, hb2]
    have h_nonneg_B1 : 0 ≤ pow_bound x1 y k := pow_bound_nonneg x1 y hx1 hy k
    have step1 : Mul.mul x1 (pow_bound x1 y k) ≤ Mul.mul x2 (pow_bound x1 y k) := mul_le_mul_right_of_nonneg h h_nonneg_B1
    have hx2_nonneg : 0 ≤ x2 := le_trans hx1 h
    have step2 : Mul.mul x2 (pow_bound x1 y k) ≤ Mul.mul x2 (pow_bound x2 y k) := mul_le_mul_left_of_nonneg ih hx2_nonneg
    have step3 : Mul.mul x1 (pow_bound x1 y k) ≤ Mul.mul x2 (pow_bound x2 y k) := le_trans step1 step2
    exact add_le_add_right step3 (pow y k)

theorem pow_bound_pos_succ (x y : ℚ₀cls) (hx : 0 < x) (hy : 0 ≤ y) (k : ℕ₀) : 0 < pow_bound x y (σ k) := by
  induction k with
  | zero =>
    change 0 < pow_bound x y 1
    have h1 : pow_bound x y 1 = Add.add (Mul.mul x 0) 1 := rfl
    rw [h1]
    have hm : Mul.mul x 0 = 0 := mul_zero x
    rw [hm, zero_add]
    exact zero_lt_one
  | succ k' ih =>
    have h_step : pow_bound x y (σ (σ k')) = Add.add (Mul.mul x (pow_bound x y (σ k'))) (pow y (σ k')) := rfl
    rw [h_step]
    have h1 : 0 < Mul.mul x (pow_bound x y (σ k')) := mul_pos_pub hx ih
    have h2 : 0 ≤ pow y (σ k') := pow_nonneg y hy _
    rw [add_comm]
    exact add_pos_of_nonneg_of_pos h2 h1

theorem pow_bound_pos (x y : ℚ₀cls) (hx : 0 < x) (hy : 0 ≤ y) (n : ℕ₀) (hn : n ≠ 0) : 0 < pow_bound x y n := by
  cases n with
  | zero => exact False.elim (hn rfl)
  | succ k => exact pow_bound_pos_succ x y hx hy k

theorem sub_pos_of_lt {a b : ℚ₀cls} (h : b < a) : 0 < Sub.sub a b := by
  have h_le : 0 ≤ Sub.sub a b := by
    have h1 : Add.add b (Neg.neg b) ≤ Add.add a (Neg.neg b) := add_le_add_right h.1 (Neg.neg b)
    have h2 : Add.add b (Neg.neg b) = 0 := add_neg_self b
    rw [h2] at h1
    exact h1
  have h_not_le : ¬(Sub.sub a b ≤ 0) := by
    intro hc
    have hc_eq : Sub.sub a b = 0 := le_antisymm hc h_le
    have hc3 : Add.add (Sub.sub a b) b = Add.add 0 b := congrArg (fun z => Add.add z b) hc_eq
    have ha : Add.add (Sub.sub a b) b = a := by
      have hd : Sub.sub a b = Add.add a (Neg.neg b) := rfl
      rw [hd, add_assoc, neg_add_self, add_zero]
    rw [zero_add] at hc3
    rw [ha] at hc3
    have h_a_le_b : a ≤ b := by rw [hc3]; exact le_refl b
    exact h.2 h_a_le_b
  exact ⟨h_le, h_not_le⟩

theorem sub_nonneg_of_mul_nonneg (A B c : ℚ₀cls) (hB : 0 ≤ B) (hc : 0 < c) (h_mul : c ≤ Mul.mul A B) : 0 ≤ A := by
  cases le_total 0 A with
  | inl h_pos => exact h_pos
  | inr h_neg =>
    have h1 : Mul.mul A B ≤ Mul.mul 0 B := mul_le_mul_right_of_nonneg h_neg hB
    have hm : Mul.mul 0 B = 0 := zero_mul B
    rw [hm] at h1
    have h2 : c ≤ 0 := le_trans h_mul h1
    exact False.elim (hc.2 h2)

theorem newton_seq_apart_lt (q r : ℚ₀cls) (n : ℕ₂) (hq : 0 < q) (hr : 0 ≤ r) (h : pow r n.val.val < q) :
  ∃ N : ℕ₀, ∃ δ > (0:ℚ₀cls), ∀ k, Peano.Order.le₀ N k → δ ≤ Sub.sub (newton_raphson_seq q n k) r := by
  exists 1
  let c := Sub.sub q (pow r n.val.val)
  have hc : 0 < c := sub_pos_of_lt h
  let x1 := newton_raphson_seq q n 1
  have hx1 : 0 < x1 := newton_seq_pos q n hq 1
  let M := pow_bound x1 r n.val.val
  have hM_pos : 0 < M := pow_bound_pos x1 r hx1 hr n.val.val n.val.property
  let delta := Mul.mul c (inv M)
  have h_delta_pos : 0 < delta := mul_pos_pub hc (inv_pos hM_pos)
  exists delta
  exists h_delta_pos
  intro k hk
  cases k with
  | zero =>
    cases hk with
    | inl h_lt =>
      cases h_lt
    | inr h_eq =>
      cases h_eq
  | succ k' =>
    let x_k := newton_raphson_seq q n (σ k')
    have h_q_le_xk_n : q ≤ pow x_k n.val.val := newton_seq_pow_ge q n hq k'
    have h_sub_le : c ≤ Sub.sub (pow x_k n.val.val) (pow r n.val.val) := add_le_add_right h_q_le_xk_n _
    have h_pow_sub_eq : pow x_k n.val.val = Add.add (pow r n.val.val) (Mul.mul (Sub.sub x_k r) (pow_bound x_k r n.val.val)) := pow_sub_eq x_k r n.val.val
    have h_sub_eq : Sub.sub (pow x_k n.val.val) (pow r n.val.val) = Mul.mul (Sub.sub x_k r) (pow_bound x_k r n.val.val) := by
      have hd1 : Sub.sub (pow x_k n.val.val) (pow r n.val.val) = Add.add (pow x_k n.val.val) (Neg.neg (pow r n.val.val)) := rfl
      rw [hd1, h_pow_sub_eq]
      rw [add_assoc, add_comm (Mul.mul _ _) _, ←add_assoc, add_neg_self, zero_add]
    rw [h_sub_eq] at h_sub_le
    have h_x_le_x1 : x_k ≤ x1 := newton_seq_le_x1 q n hq k'
    have hxk_pos : 0 < x_k := newton_seq_pos q n hq (σ k')
    have h_B_le_M : pow_bound x_k r n.val.val ≤ M := pow_bound_mono x_k x1 r (le_of_lt hxk_pos) hr h_x_le_x1 n.val.val
    have hB_pos : 0 < pow_bound x_k r n.val.val := pow_bound_pos x_k r hxk_pos hr n.val.val n.val.property
    have h_diff_nonneg : 0 ≤ Sub.sub x_k r := sub_nonneg_of_mul_nonneg _ _ c hB_pos.1 hc h_sub_le
    have h_B_mul : Mul.mul (Sub.sub x_k r) (pow_bound x_k r n.val.val) ≤ Mul.mul (Sub.sub x_k r) M := mul_le_mul_left_of_nonneg h_B_le_M h_diff_nonneg
    have h_c_le_diff_M : c ≤ Mul.mul (Sub.sub x_k r) M := le_trans h_sub_le h_B_mul
    have h_mul_inv : Mul.mul c (inv M) ≤ Mul.mul (Mul.mul (Sub.sub x_k r) M) (inv M) := mul_le_mul_right_of_nonneg h_c_le_diff_M (inv_pos hM_pos).1
    have h_assoc : Mul.mul (Mul.mul (Sub.sub x_k r) M) (inv M) = Mul.mul (Sub.sub x_k r) (Mul.mul M (inv M)) := mul_assoc _ _ _
    have hM_ne_zero : M ≠ 0 := by 
      intro hM_eq
      have hM_le : M ≤ 0 := by rw [hM_eq]; exact le_refl 0
      exact hM_pos.2 hM_le
    have h_M_inv : Mul.mul M (inv M) = 1 := mul_inv_cancel hM_ne_zero
    have h_mul_one : Mul.mul (Sub.sub x_k r) 1 = Sub.sub x_k r := mul_one _
    rw [h_assoc, h_M_inv, h_mul_one] at h_mul_inv
    exact h_mul_inv

theorem newton_seq_succ_le (q : ℚ₀cls) (n : ℕ₂) (hq : 0 < q) (k : ℕ₀) (h1 : Peano.Order.le₀ 1 k) :
  newton_raphson_seq q n (σ k) ≤ newton_raphson_seq q n k := by
  cases k with
  | zero => exact False.elim (Peano.Order.le_1_0_then_false h1)
  | succ k' => exact newton_seq_monotone q n hq k'

theorem newton_seq_anti (q : ℚ₀cls) (n : ℕ₂) (hq : 0 < q) (N k : ℕ₀) (h1 : Peano.Order.le₀ 1 N) (hk : Peano.Order.le₀ N k) :
  newton_raphson_seq q n k ≤ newton_raphson_seq q n N := by
  induction k with
  | zero =>
    have hN : N = 0 := Peano.Order.le_zero_eq_wp hk
    rw [hN] at h1
    exact False.elim (Peano.Order.le_1_0_then_false h1)
  | succ k' ih =>
    have h_or : Peano.Order.le₀ N k' ∨ N = σ k' := Peano.Order.le_succ_then_le_or_eq_wp hk
    cases h_or with
    | inl h_le =>
      have h_ih : newton_raphson_seq q n k' ≤ newton_raphson_seq q n N := ih h_le
      have h_k_ge_1 : Peano.Order.le₀ 1 k' := Peano.Order.le_trans 1 N k' h1 h_le
      have h_step : newton_raphson_seq q n (σ k') ≤ newton_raphson_seq q n k' := newton_seq_succ_le q n hq k' h_k_ge_1
      exact le_trans h_step h_ih
    | inr h_eq =>
      rw [h_eq]
      exact le_refl _

-- Helper lemma: If x_k >= r, then the Newton step decreases by at least a constant delta.
theorem newton_seq_step_bound (q r : ℚ₀cls) (n : ℕ₂) (hq : 0 < q) (hr : 0 ≤ r) (h : q < pow r n.val.val) :
  ∃ delta > (0:ℚ₀cls), ∀ k : ℕ₀, Peano.Order.le₀ 1 k → r ≤ newton_raphson_seq q n k →
  Add.add (newton_raphson_seq q n (σ k)) delta ≤ newton_raphson_seq q n k := sorry

-- Helper lemma: Telescoping sum of the lower bound.
theorem newton_seq_telescope (f : ℕ₀ → ℚ₀cls) (delta : ℚ₀cls) (h_delta : 0 < delta) 
  (h_step : ∀ k : ℕ₀, Peano.Order.le₀ 1 k → Add.add (f (σ k)) delta ≤ f k) :
  ∀ k : ℕ₀, Add.add (f (σ k)) (Mul.mul (ofNat₀ k) delta) ≤ f 1 := by
  intro k
  induction k with
  | zero =>
    have h_0 : ofNat₀ 𝟘 = 0 := rfl
    have h_mul_zero : Mul.mul (0:ℚ₀cls) delta = 0 := zero_mul delta
    have h_add_zero : Add.add (f (σ 𝟘)) 0 = f (σ 𝟘) := add_zero _
    rw [h_0, h_mul_zero, h_add_zero]
    exact le_refl _
  | succ k' ih =>
    have h1 : Peano.Order.le₀ 1 (σ k') := Peano.Order.le_1_succ _
    have h_step' := h_step (σ k') h1
    have h_sigma : ofNat₀ (σ k') = Add.add (ofNat₀ k') 1 := by
      have hh : ofNat₀ (σ k') = ofNat₀ (Peano.Add.add k' 𝟙) := rfl
      rw [hh, ofNat₀_add]
      rfl
    rw [h_sigma]
    have h_dist : Mul.mul (Add.add (ofNat₀ k') 1) delta = Add.add (Mul.mul (ofNat₀ k') delta) (Mul.mul 1 delta) := right_distrib _ _ _
    rw [h_dist]
    have h_one : Mul.mul (1:ℚ₀cls) delta = delta := one_mul delta
    rw [h_one]
    have h_assoc : Add.add (f (σ (σ k'))) (Add.add (Mul.mul (ofNat₀ k') delta) delta) = Add.add (Add.add (f (σ (σ k'))) delta) (Mul.mul (ofNat₀ k') delta) := by
      have h1 : Add.add (f (σ (σ k'))) (Add.add (Mul.mul (ofNat₀ k') delta) delta) = Add.add (Add.add (f (σ (σ k'))) (Mul.mul (ofNat₀ k') delta)) delta := (ℚ₀cls.add_assoc _ _ _).symm
      rw [h1]
      have h3 : Add.add (Add.add (f (σ (σ k'))) (Mul.mul (ofNat₀ k') delta)) delta = Add.add (f (σ (σ k'))) (Add.add (Mul.mul (ofNat₀ k') delta) delta) := ℚ₀cls.add_assoc _ _ _
      have h4 : Add.add (Mul.mul (ofNat₀ k') delta) delta = Add.add delta (Mul.mul (ofNat₀ k') delta) := add_comm _ _
      rw [h3, h4]
      exact (ℚ₀cls.add_assoc _ _ _).symm
    rw [h_assoc]
    have h_le1 : Add.add (Add.add (f (σ (σ k'))) delta) (Mul.mul (ofNat₀ k') delta) ≤ Add.add (f (σ k')) (Mul.mul (ofNat₀ k') delta) := by
      exact add_le_add_right h_step' _
    exact le_trans h_le1 ih

/-- Búsqueda constructiva acotada: hasta el índice `σ K`, o bien ya hay un testigo
`N` con `seq N < r`, o bien `r` sigue siendo una cota inferior en `σ K` y la suma
telescópica de los descensos por `h_step` está acotada por `seq 1`. Sustituye al uso
de `Classical.byContradiction` de la versión anterior: la disyunción se decide en
cada paso vía la instancia `Decidable` de `≤` en `ℚ₀cls` (`ℚ₀cls.le_total` + `resolve_right`),
sin asumir el medio excluido no constructivo. -/
private theorem newton_bounded_search (q r : ℚ₀cls) (n : ℕ₂)
    (delta : ℚ₀cls) (_h_delta_pos : 0 < delta)
    (h_step : ∀ k : ℕ₀, Peano.Order.le₀ 1 k → r ≤ newton_raphson_seq q n k →
      Add.add (newton_raphson_seq q n (σ k)) delta ≤ newton_raphson_seq q n k) :
    ∀ K : ℕ₀,
      (∃ N : ℕ₀, Peano.Order.le₀ 1 N ∧ newton_raphson_seq q n N < r) ∨
      (r ≤ newton_raphson_seq q n (σ K) ∧
        Add.add (newton_raphson_seq q n (σ K)) (Mul.mul (ofNat₀ K) delta) ≤ newton_raphson_seq q n 1) := by
  intro K
  induction K with
  | zero =>
    by_cases hr_le : r ≤ newton_raphson_seq q n 1
    · refine Or.inr ⟨hr_le, ?_⟩
      have h0 : ofNat₀ (𝟘 : ℕ₀) = (0:ℚ₀cls) := rfl
      have hmz : Mul.mul (0:ℚ₀cls) delta = 0 := zero_mul delta
      have haz : Add.add (newton_raphson_seq q n (σ 𝟘)) (0:ℚ₀cls) = newton_raphson_seq q n (σ 𝟘) := add_zero _
      rw [h0, hmz, haz]
      exact le_refl _
    · have hlt : newton_raphson_seq q n 1 < r := ⟨(ℚ₀cls.le_total _ _).resolve_right hr_le, hr_le⟩
      exact Or.inl ⟨1, Peano.Order.le_refl 1, hlt⟩
  | succ K' ih =>
    rcases ih with ⟨N, hN1, hNlt⟩ | ⟨hle_K', htele_K'⟩
    · exact Or.inl ⟨N, hN1, hNlt⟩
    · by_cases hr_le2 : r ≤ newton_raphson_seq q n (σ (σ K'))
      · refine Or.inr ⟨hr_le2, ?_⟩
        have h_sigma : ofNat₀ (σ K') = Add.add (ofNat₀ K') 1 := by
          have hh : ofNat₀ (σ K') = ofNat₀ (Peano.Add.add K' 𝟙) := rfl
          rw [hh, ofNat₀_add]
          rfl
        rw [h_sigma]
        have h_dist : Mul.mul (Add.add (ofNat₀ K') 1) delta
            = Add.add (Mul.mul (ofNat₀ K') delta) (Mul.mul 1 delta) := right_distrib _ _ _
        rw [h_dist]
        have h_one : Mul.mul (1:ℚ₀cls) delta = delta := one_mul delta
        rw [h_one]
        have h_step' := h_step (σ K') (Peano.Order.le_1_succ _) hle_K'
        have h_assoc :
            Add.add (newton_raphson_seq q n (σ (σ K'))) (Add.add (Mul.mul (ofNat₀ K') delta) delta)
              = Add.add (Add.add (newton_raphson_seq q n (σ (σ K'))) delta) (Mul.mul (ofNat₀ K') delta) := by
          have h1 : Add.add (newton_raphson_seq q n (σ (σ K'))) (Add.add (Mul.mul (ofNat₀ K') delta) delta)
              = Add.add (Add.add (newton_raphson_seq q n (σ (σ K'))) (Mul.mul (ofNat₀ K') delta)) delta :=
            (ℚ₀cls.add_assoc _ _ _).symm
          rw [h1]
          have h3 : Add.add (Add.add (newton_raphson_seq q n (σ (σ K'))) (Mul.mul (ofNat₀ K') delta)) delta
              = Add.add (newton_raphson_seq q n (σ (σ K'))) (Add.add (Mul.mul (ofNat₀ K') delta) delta) :=
            ℚ₀cls.add_assoc _ _ _
          have h4 : Add.add (Mul.mul (ofNat₀ K') delta) delta = Add.add delta (Mul.mul (ofNat₀ K') delta) :=
            add_comm _ _
          rw [h3, h4]
          exact (ℚ₀cls.add_assoc _ _ _).symm
        rw [h_assoc]
        have h_le1 :
            Add.add (Add.add (newton_raphson_seq q n (σ (σ K'))) delta) (Mul.mul (ofNat₀ K') delta)
              ≤ Add.add (newton_raphson_seq q n (σ K')) (Mul.mul (ofNat₀ K') delta) :=
          add_le_add_right h_step' _
        exact le_trans h_le1 htele_K'
      · have hlt2 : newton_raphson_seq q n (σ (σ K')) < r :=
          ⟨(ℚ₀cls.le_total _ _).resolve_right hr_le2, hr_le2⟩
        exact Or.inl ⟨σ (σ K'), Peano.Order.le_1_succ _, hlt2⟩

theorem newton_seq_eventually_lt (q r : ℚ₀cls) (n : ℕ₂) (hq : 0 < q) (hr : 0 ≤ r) (h : q < pow r n.val.val) :
  ∃ N : ℕ₀, And (Peano.Order.le₀ 1 N) (newton_raphson_seq q n N < r) := by
  have h_bound := newton_seq_step_bound q r n hq hr h
  rcases h_bound with ⟨delta, h_delta_pos, h_step⟩

  -- By Archimedean property, there exists M such that x_1 < M * delta
  have h_arch := archimedean delta (newton_raphson_seq q n 1) h_delta_pos
  rcases h_arch with ⟨M, hM⟩

  rcases newton_bounded_search q r n delta h_delta_pos h_step M with h_wit | ⟨h_le_M, h_tele_M⟩
  · exact h_wit
  · -- Si no hay testigo hasta σM, la suma telescópica contradice la cota arquimediana:
    -- de ahí se sigue lo que sea, en particular el testigo buscado (ex falso, constructivo).
    exfalso
    have h_xM_nonneg : 0 ≤ newton_raphson_seq q n (σ M) := le_trans hr h_le_M
    have h_M_delta_le : Mul.mul (ofNat₀ M) delta ≤ Add.add (newton_raphson_seq q n (σ M)) (Mul.mul (ofNat₀ M) delta) := by
      have hz : Add.add 0 (Mul.mul (ofNat₀ M) delta) ≤ Add.add (newton_raphson_seq q n (σ M)) (Mul.mul (ofNat₀ M) delta) := add_le_add_right h_xM_nonneg _
      rw [ℚ₀cls.zero_add] at hz
      exact hz

    have h_M_delta_le_x1 : Mul.mul (ofNat₀ M) delta ≤ newton_raphson_seq q n 1 := le_trans h_M_delta_le h_tele_M

    exact hM.2 h_M_delta_le_x1

theorem newton_seq_apart_gt (q r : ℚ₀cls) (n : ℕ₂) (hq : 0 < q) (hr : 0 ≤ r) (h : q < pow r n.val.val) :
  ∃ N : ℕ₀, ∃ δ > (0:ℚ₀cls), ∀ k, Peano.Order.le₀ N k → δ ≤ Sub.sub r (newton_raphson_seq q n k) := by
  have h_exists_N : ∃ N : ℕ₀, And (Peano.Order.le₀ 1 N) (newton_raphson_seq q n N < r) := newton_seq_eventually_lt q r n hq hr h
  cases h_exists_N with
  | intro N h_xN_lt_r =>
    let x_N := newton_raphson_seq q n N
    have h_delta_pos : 0 < Sub.sub r x_N := sub_pos_of_lt h_xN_lt_r.2
    exists N
    exists (Sub.sub r x_N)
    exists h_delta_pos
    intro k hk
    have h_anti : newton_raphson_seq q n k ≤ x_N := newton_seq_anti q n hq N k h_xN_lt_r.1 hk
    have h_neg : Neg.neg x_N ≤ Neg.neg (newton_raphson_seq q n k) := neg_le_neg h_anti
    have h_sub : Add.add r (Neg.neg x_N) ≤ Add.add r (Neg.neg (newton_raphson_seq q n k)) := add_le_add_left h_neg r
    exact h_sub

end ℚ₀cls
