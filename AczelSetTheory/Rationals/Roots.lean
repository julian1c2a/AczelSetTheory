/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

import AczelSetTheory.Rationals.Basic
import AczelSetTheory.Rationals.Inv

namespace ℚ₀

/--
Potencia n-ésima natural de un número racional.
x^n definido por inducción sobre ℕ₀.
-/
def pow (x : ℚ₀) : ℕ₀ → ℚ₀
  | 𝟘 => ofNat₀ 𝟙
  | σ k => Mul.mul x (pow x k)

theorem ofNat₀_add (n m : ℕ₀) : ofNat₀ (Peano.Add.add n m) = Add.add (ofNat₀ n) (ofNat₀ m) := by
  have hn : ofNat₀ n = mk (ℤ₀.ofNat n) den1 := ofNat₀_eq_mk n
  have hm : ofNat₀ m = mk (ℤ₀.ofNat m) den1 := ofNat₀_eq_mk m
  have hnm : ofNat₀ (Peano.Add.add n m) = mk (ℤ₀.ofNat (Peano.Add.add n m)) den1 := ofNat₀_eq_mk _
  rw [hn, hm, add_mk, hnm, mk_eq_iff]
  have h_den_one : ℤ₀.ofNat den1.val = 1 := rfl
  have h_mul_den_one : ℤ₀.ofNat (mulDen den1 den1).val = 1 := rfl
  simp only [h_den_one, h_mul_den_one, ℤ₀.mul_one, ℤ₀.ofNat_add]

theorem ofNat₀_mul (n m : ℕ₀) : ofNat₀ (Peano.Mul.mul n m) = Mul.mul (ofNat₀ n) (ofNat₀ m) := by
  have hn : ofNat₀ n = mk (ℤ₀.ofNat n) den1 := ofNat₀_eq_mk n
  have hm : ofNat₀ m = mk (ℤ₀.ofNat m) den1 := ofNat₀_eq_mk m
  have hnm : ofNat₀ (Peano.Mul.mul n m) = mk (ℤ₀.ofNat (Peano.Mul.mul n m)) den1 := ofNat₀_eq_mk _
  rw [hn, hm, mul_mk, hnm, mk_eq_iff]
  have h_den_one : ℤ₀.ofNat den1.val = 1 := rfl
  have h_mul_den_one : ℤ₀.ofNat (mulDen den1 den1).val = 1 := rfl
  simp only [h_den_one, h_mul_den_one, ℤ₀.mul_one, ℤ₀.ofNat_mul]

theorem ofNat₀_nonneg (n : ℕ₀) : (0:ℚ₀) ≤ ofNat₀ n := by
  have h_mk : ofNat₀ n = mk (ℤ₀.ofNat n) den1 := ofNat₀_eq_mk n
  rw [h_mk]
  apply (zero_le_iff_num_nonneg (ℤ₀.ofNat n, den1)).mpr
  exact ℤ₀.zero_le_ofNat n

theorem square_nonneg (x : ℚ₀) : (0:ℚ₀) ≤ Mul.mul x x := by
  cases le_total (0:ℚ₀) x with
  | inl h => exact mul_nonneg h h
  | inr h => exact mul_nonneg_of_nonpos_of_nonpos h h

theorem le_add_of_nonneg_right {a b : ℚ₀} (hb : 0 ≤ b) : a ≤ Add.add a b := by
  have h : Add.add a 0 ≤ Add.add a b := add_le_add_left hb a
  rw [add_zero] at h
  exact h

-- Prove Bernoulli's inequality
theorem bernoulli_ineq (x : ℚ₀) (hx : (0:ℚ₀) ≤ Add.add (1:ℚ₀) x) (n : ℕ₀) :
  Add.add (1:ℚ₀) (Mul.mul (ofNat₀ n) x) ≤ pow (Add.add (1:ℚ₀) x) n := by
  induction n with
  | zero =>
    have h1 : Mul.mul (0:ℚ₀) x = (0:ℚ₀) := zero_mul x
    have h2 : Add.add (1:ℚ₀) (0:ℚ₀) = (1:ℚ₀) := add_zero (1:ℚ₀)
    have h3 : pow (Add.add (1:ℚ₀) x) 𝟘 = (1:ℚ₀) := rfl
    have h4 : Add.add (1:ℚ₀) (Mul.mul (ofNat₀ 𝟘) x) = (1:ℚ₀) := by
      have h_zero : ofNat₀ 𝟘 = (0:ℚ₀) := rfl
      rw [h_zero, h1, h2]
    rw [h4, h3]
    exact le_refl (1:ℚ₀)
  | succ k hk =>
    have h_pow_succ : pow (Add.add (1:ℚ₀) x) (σ k) = Mul.mul (Add.add (1:ℚ₀) x) (pow (Add.add (1:ℚ₀) x) k) := rfl
    have h_mul_ih : Mul.mul (Add.add (1:ℚ₀) x) (Add.add (1:ℚ₀) (Mul.mul (ofNat₀ k) x)) ≤ Mul.mul (Add.add (1:ℚ₀) x) (pow (Add.add (1:ℚ₀) x) k) :=
      mul_le_mul_left_of_nonneg hk hx
    
    have h_k_succ : ofNat₀ (σ k) = Add.add (ofNat₀ k) (1:ℚ₀) := by
      have h1 : σ k = Peano.Add.add k 𝟙 := rfl
      have h2 : ofNat₀ 𝟙 = (1:ℚ₀) := rfl
      rw [h1, ofNat₀_add, h2]

    have h_LHS : Add.add (1:ℚ₀) (Mul.mul (ofNat₀ (σ k)) x) = Add.add (Add.add (1:ℚ₀) (Mul.mul (ofNat₀ k) x)) x := by
      rw [h_k_succ]
      change Add.add 1 (Add.add (ofNat₀ k) 1 * x) = Add.add (Add.add 1 (Mul.mul (ofNat₀ k) x)) x
      rw [right_distrib, one_mul]
      change Add.add 1 (Add.add (Mul.mul (ofNat₀ k) x) x) = Add.add (Add.add 1 (Mul.mul (ofNat₀ k) x)) x
      rw [←add_assoc]

    have h_RHS : Mul.mul (Add.add (1:ℚ₀) x) (Add.add (1:ℚ₀) (Mul.mul (ofNat₀ k) x)) = Add.add (Add.add (Add.add (1:ℚ₀) (Mul.mul (ofNat₀ k) x)) x) (Mul.mul (ofNat₀ k) (Mul.mul x x)) := by
      change Add.add (1:ℚ₀) x * (Add.add (1:ℚ₀) (Mul.mul (ofNat₀ k) x)) = _
      rw [right_distrib]
      change Add.add (1 * Add.add 1 (Mul.mul (ofNat₀ k) x)) (x * Add.add 1 (Mul.mul (ofNat₀ k) x)) = _
      rw [one_mul]
      change Add.add (Add.add 1 (Mul.mul (ofNat₀ k) x)) (x * Add.add 1 (Mul.mul (ofNat₀ k) x)) = _
      rw [left_distrib]
      change Add.add (Add.add 1 (Mul.mul (ofNat₀ k) x)) (Add.add (x * 1) (x * Mul.mul (ofNat₀ k) x)) = _
      rw [mul_one, ←add_assoc]
      change Add.add (Add.add (Add.add 1 (Mul.mul (ofNat₀ k) x)) x) (Mul.mul x (Mul.mul (ofNat₀ k) x)) = _
      have h_comm : Mul.mul x (Mul.mul (ofNat₀ k) x) = Mul.mul (ofNat₀ k) (Mul.mul x x) := by
        change x * (ofNat₀ k * x) = ofNat₀ k * (x * x)
        rw [←mul_assoc, mul_comm x (ofNat₀ k), mul_assoc]
      rw [h_comm]

    have h_nonneg : (0:ℚ₀) ≤ Mul.mul (ofNat₀ k) (Mul.mul x x) := by
      have h1 : (0:ℚ₀) ≤ ofNat₀ k := ofNat₀_nonneg k
      have h2 : (0:ℚ₀) ≤ Mul.mul x x := square_nonneg x
      exact mul_nonneg h1 h2

    have h_le : Add.add (Add.add (1:ℚ₀) (Mul.mul (ofNat₀ k) x)) x ≤ Add.add (Add.add (Add.add (1:ℚ₀) (Mul.mul (ofNat₀ k) x)) x) (Mul.mul (ofNat₀ k) (Mul.mul x x)) := by
      exact le_add_of_nonneg_right h_nonneg

    rw [h_pow_succ, h_LHS]
    have h_trans : Add.add (Add.add (1:ℚ₀) (Mul.mul (ofNat₀ k) x)) x ≤ Mul.mul (Add.add (1:ℚ₀) x) (pow (Add.add (1:ℚ₀) x) k) := by
      have h_step : Add.add (Add.add (Add.add (1:ℚ₀) (Mul.mul (ofNat₀ k) x)) x) (Mul.mul (ofNat₀ k) (Mul.mul x x)) = Mul.mul (Add.add (1:ℚ₀) x) (Add.add (1:ℚ₀) (Mul.mul (ofNat₀ k) x)) := h_RHS.symm
      have h_le2 : Add.add (Add.add (1:ℚ₀) (Mul.mul (ofNat₀ k) x)) x ≤ Mul.mul (Add.add (1:ℚ₀) x) (Add.add (1:ℚ₀) (Mul.mul (ofNat₀ k) x)) := by
        rw [←h_step]
        exact h_le
      exact le_trans h_le2 h_mul_ih
    exact h_trans

theorem lt_of_le_of_ne {a b : ℚ₀} (h_le : a ≤ b) (h_ne : a ≠ b) : a < b := by
  constructor
  · exact h_le
  · intro h_ba
    have heq : a = b := le_antisymm h_le h_ba
    exact h_ne heq

theorem pos_of_gt_zero {a : ℚ₀} (h : 0 < a) : 0 ≤ a ∧ a ≠ 0 := by
  constructor
  · exact h.1
  · intro heq
    have h2 : a ≤ 0 := by rw [heq]; exact le_refl 0
    exact h.2 h2

theorem inv_ne_zero {a : ℚ₀} (h : a ≠ 0) : a⁻¹ ≠ 0 := by
  intro h_inv_zero
  have h1 : a * a⁻¹ = 1 := mul_inv_cancel h
  have h2 : a * a⁻¹ = 0 := by rw [h_inv_zero, mul_zero]
  rw [h2] at h1
  exact one_ne_zero h1.symm

theorem inv_pos {a : ℚ₀} (h : 0 < a) : 0 < a⁻¹ := by
  have h_ne : a ≠ 0 := (pos_of_gt_zero h).2
  have h_le : 0 ≤ a⁻¹ := inv_nonneg (pos_of_gt_zero h).1 h_ne
  have h_inv_ne : a⁻¹ ≠ 0 := inv_ne_zero h_ne
  exact lt_of_le_of_ne h_le h_inv_ne.symm

theorem add_nonneg {a b : ℚ₀} (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ Add.add a b := by
  have h1 : Add.add (0:ℚ₀) (0:ℚ₀) ≤ Add.add a b := add_le_add ha hb
  have h2 : Add.add (0:ℚ₀) (0:ℚ₀) = (0:ℚ₀) := add_zero (0:ℚ₀)
  rw [h2] at h1
  exact h1

theorem eq_neg_of_add_eq_zero_pub {x y : ℚ₀} (h : Add.add x y = 0) : x = -y := by
  have h1 : Add.add (Add.add x y) (-y) = Add.add 0 (-y) := congrArg (fun z => Add.add z (-y)) h
  rw [add_assoc, add_neg_self, add_zero] at h1
  have h2 : Add.add 0 (-y) = -y := zero_add (-y)
  rw [h2] at h1
  exact h1

theorem add_pos_of_nonneg_of_pos {a b : ℚ₀} (ha : 0 ≤ a) (hb : 0 < b) : 0 < Add.add a b := by
  have h_le : 0 ≤ Add.add a b := add_nonneg ha (pos_of_gt_zero hb).1
  have h_ne : Add.add a b ≠ 0 := by
    intro h_eq_zero
    have h_a_eq_neg_b : a = Neg.neg b := eq_neg_of_add_eq_zero_pub h_eq_zero
    have h_neg_b_le_neg_zero : Neg.neg b ≤ Neg.neg (0:ℚ₀) := neg_le_neg (pos_of_gt_zero hb).1
    rw [neg_zero] at h_neg_b_le_neg_zero
    rw [← h_a_eq_neg_b] at h_neg_b_le_neg_zero
    have h_a_eq_zero : a = 0 := le_antisymm h_neg_b_le_neg_zero ha
    rw [h_a_eq_zero] at h_eq_zero
    rw [zero_add] at h_eq_zero
    exact (pos_of_gt_zero hb).2 h_eq_zero
  exact lt_of_le_of_ne h_le h_ne.symm

theorem add_pos {a b : ℚ₀} (ha : 0 < a) (hb : 0 < b) : 0 < Add.add a b :=
  add_pos_of_nonneg_of_pos (pos_of_gt_zero ha).1 hb

theorem eq_zero_of_mul_eq_zero {a b : ℚ₀} (h : a * b = 0) (hb : b ≠ 0) : a = 0 := by
  have h1 : (a * b) * b⁻¹ = 0 * b⁻¹ := congrArg (fun z => z * b⁻¹) h
  rw [mul_assoc, mul_inv_cancel hb, mul_one, zero_mul] at h1
  exact h1

theorem mul_pos_pub {a b : ℚ₀} (ha : 0 < a) (hb : 0 < b) : 0 < a * b := by
  have h_le : 0 ≤ a * b := mul_nonneg (pos_of_gt_zero ha).1 (pos_of_gt_zero hb).1
  have h_ne : a * b ≠ 0 := by
    intro h_eq_zero
    have h_a_eq_zero : a = 0 := eq_zero_of_mul_eq_zero h_eq_zero (pos_of_gt_zero hb).2
    exact (pos_of_gt_zero ha).2 h_a_eq_zero
  exact lt_of_le_of_ne h_le h_ne.symm

theorem zero_lt_one : (0:ℚ₀) < 1 := by
  have h_le : (0:ℚ₀) ≤ 1 := by
    have h1 : (1:ℚ₀) = ofNat₀ 𝟙 := rfl
    rw [h1]
    exact ofNat₀_nonneg 𝟙
  exact lt_of_le_of_ne h_le (fun h => one_ne_zero h.symm)

theorem pow_pos {x : ℚ₀} (k : ℕ₀) (hx : 0 < x) : 0 < pow x k := by
  induction k with
  | zero =>
    -- pow x 0 es 1
    exact zero_lt_one
  | succ k' ih =>
    -- pow x (σ k') es x * pow x k'
    change 0 < x * pow x k'
    exact mul_pos_pub hx ih

theorem ofNat₀_inj_zero {n : ℕ₀} (h : ofNat₀ n = 0) : n = 0 := by
  have h1 : mk (ℤ₀.ofNat n) den1 = 0 := by
    rw [←ofNat₀_eq_mk n]
    exact h
  have h2 : ℤ₀.ofNat n = 0 := mk_eq_zero_iff.mp h1
  have h3 : ℤ₀.ofNat n = ℤ₀.ofNat 𝟘 := by
    rw [h2]
    exact ℤ₀.ofNat_zero.symm
  exact ℤ₀.ofNat_injective h3

theorem ofNat₀_pos {k : ℕ₀} (hk : k ≠ 0) : 0 < ofNat₀ k := by
  have h_le : 0 ≤ ofNat₀ k := ofNat₀_nonneg k
  have h_ne : ofNat₀ k ≠ 0 := by
    intro h_eq
    have h_k_eq_zero : k = 0 := ofNat₀_inj_zero h_eq
    exact hk h_k_eq_zero
  exact lt_of_le_of_ne h_le h_ne.symm

/--
Aproximación por el método de Newton-Raphson.
Para calcular la raíz n-ésima de q, se itera:
x_{k+1} = (1 / n) * ((n - 1) * x_k + q / (x_k ^ (n - 1)))
-/
def newton_raphson_step (q : ℚ₀) (n : Peano.ℕ₂) (x : ℚ₀) : ℚ₀ :=
  -- Si q = 0 o q = 1, la sucesión es constante y vale q (evitamos divisiones por cero u otras indefiniciones)
  if q = (0:ℚ₀) ∨ q = (1:ℚ₀) then
    q
  else
    -- Queremos calcular: (1/n) * [ (n-1)*x + q * inv (x^(n-1)) ]
    let n_val := n.val.val
    let inv_n := inv (ofNat₀ n_val)
    -- Nota: n_minus_one = n - 1
    let n_minus_one := Peano.Sub.sub n_val 𝟙
    let part1 := Mul.mul (ofNat₀ n_minus_one) x
    let part2 := Mul.mul q (inv (pow x n_minus_one))
    Mul.mul inv_n (Add.add part1 part2)

/--
Sucesión de aproximaciones de Newton-Raphson para la raíz n-ésima de q.
Comienza con la semilla x_0 = q.
-/
def newton_raphson_seq (q : ℚ₀) (n : Peano.ℕ₂) : ℕ₀ → ℚ₀
  | 𝟘 => q
  | σ k => newton_raphson_step q n (newton_raphson_seq q n k)

theorem newton_seq_pos (q : ℚ₀) (n : Peano.ℕ₂) (hq : 0 < q) (k : ℕ₀) : 0 < newton_raphson_seq q n k := by
  induction k with
  | zero =>
    exact hq
  | succ k' ih =>
    have h_step : newton_raphson_seq q n (σ k') = newton_raphson_step q n (newton_raphson_seq q n k') := rfl
    rw [h_step]
    unfold newton_raphson_step
    split
    · exact hq
    · rename_i h_not_or
      have h_part1_nonneg : 0 ≤ Mul.mul (ofNat₀ (Peano.Sub.sub n.val.val 𝟙)) (newton_raphson_seq q n k') :=
        mul_nonneg (ofNat₀_nonneg _) (pos_of_gt_zero ih).1
      have h_part2_pos : 0 < Mul.mul q (inv (pow (newton_raphson_seq q n k') (Peano.Sub.sub n.val.val 𝟙))) :=
        mul_pos_pub hq (inv_pos (pow_pos _ ih))
      have h_sum_pos : 0 < Add.add (Mul.mul (ofNat₀ (Peano.Sub.sub n.val.val 𝟙)) (newton_raphson_seq q n k')) (Mul.mul q (inv (pow (newton_raphson_seq q n k') (Peano.Sub.sub n.val.val 𝟙)))) :=
        add_pos_of_nonneg_of_pos h_part1_nonneg h_part2_pos
      have h_inv_n_pos : 0 < inv (ofNat₀ n.val.val) := inv_pos (ofNat₀_pos n.val.property)
      exact mul_pos_pub h_inv_n_pos h_sum_pos

end ℚ₀
