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

theorem le_of_add_le_add_right {a b c : ℚ₀} (h : Add.add a c ≤ Add.add b c) : a ≤ b := by
  have h1 : Add.add (Add.add a c) (Neg.neg c) ≤ Add.add (Add.add b c) (Neg.neg c) := add_le_add_right h (Neg.neg c)
  have ha : Add.add (Add.add a c) (Neg.neg c) = a := by rw [add_assoc, add_neg_self, add_zero]
  have hb : Add.add (Add.add b c) (Neg.neg c) = b := by rw [add_assoc, add_neg_self, add_zero]
  rw [ha, hb] at h1
  exact h1

theorem le_add_right (a b : ℚ₀) (hb : 0 ≤ b) : a ≤ Add.add a b := by
  have h1 : Add.add a 0 ≤ Add.add a b := add_le_add_left hb a
  rw [add_zero] at h1
  exact h1

theorem le_add_left (a b : ℚ₀) (ha : 0 ≤ a) : b ≤ Add.add a b := by
  have h1 : Add.add 0 b ≤ Add.add a b := add_le_add_right ha b
  rw [zero_add] at h1
  exact h1

theorem le_of_lt {a b : ℚ₀} (h : a < b) : a ≤ b := h.1

theorem le_w_sq_add_one {w : ℚ₀} (hw : 0 ≤ w) : w ≤ Add.add (Mul.mul w w) 1 := by
  cases le_total 1 w with
  | inl h1 =>
    have h2 : Mul.mul w 1 ≤ Mul.mul w w := mul_le_mul_left_of_nonneg h1 hw
    have hm : Mul.mul w 1 = w := mul_one w
    rw [hm] at h2
    have h3 : Mul.mul w w ≤ Add.add (Mul.mul w w) 1 := le_add_right _ _ (le_of_lt zero_lt_one)
    exact le_trans h2 h3
  | inr h2 =>
    have hsq : 0 ≤ Mul.mul w w := mul_nonneg hw hw
    have h3 : 1 ≤ Add.add (Mul.mul w w) 1 := le_add_left _ _ hsq
    exact le_trans h2 h3

theorem bernoulli_ineq_alt2 (w : ℚ₀) (hw : 0 ≤ w) (n : ℕ₀) :
  Add.add (1:ℚ₀) (Mul.mul (ofNat₀ n) w) ≤ Add.add (pow w n) (ofNat₀ n) := by
  let x := Add.add w (Neg.neg (1:ℚ₀))
  have h_w_eq : Add.add (1:ℚ₀) x = w := by
    have hc : Add.add (1:ℚ₀) x = Add.add (1:ℚ₀) (Add.add w (Neg.neg (1:ℚ₀))) := rfl
    have hc2 : Add.add (1:ℚ₀) (Add.add w (Neg.neg (1:ℚ₀))) = Add.add (Add.add (1:ℚ₀) w) (Neg.neg (1:ℚ₀)) := (add_assoc _ _ _).symm
    have hc3 : Add.add (1:ℚ₀) w = Add.add w (1:ℚ₀) := add_comm _ _
    have hc4 : Add.add (Add.add w (1:ℚ₀)) (Neg.neg (1:ℚ₀)) = Add.add w (Add.add (1:ℚ₀) (Neg.neg (1:ℚ₀))) := add_assoc _ _ _
    have hc5 : Add.add (1:ℚ₀) (Neg.neg (1:ℚ₀)) = (0:ℚ₀) := add_neg_self _
    have hc6 : Add.add w (0:ℚ₀) = w := add_zero _
    rw [hc, hc2, hc3, hc4, hc5, hc6]
  
  have hx_cond : (0:ℚ₀) ≤ Add.add (1:ℚ₀) x := by
    rw [h_w_eq]
    exact hw
    
  have h_bern := bernoulli_ineq x hx_cond n
  
  have h_nx : Mul.mul (ofNat₀ n) x = Add.add (Mul.mul (ofNat₀ n) w) (Neg.neg (ofNat₀ n)) := by
    have d : Mul.mul (ofNat₀ n) x = Add.add (Mul.mul (ofNat₀ n) w) (Mul.mul (ofNat₀ n) (Neg.neg (1:ℚ₀))) := left_distrib _ _ _
    have mn : Mul.mul (ofNat₀ n) (Neg.neg (1:ℚ₀)) = Neg.neg (Mul.mul (ofNat₀ n) (1:ℚ₀)) := mul_neg _ _
    have mo : Mul.mul (ofNat₀ n) (1:ℚ₀) = ofNat₀ n := mul_one _
    rw [d, mn, mo]
    
  have h_lhs : Add.add (1:ℚ₀) (Mul.mul (ofNat₀ n) x) = Add.add (Add.add (1:ℚ₀) (Mul.mul (ofNat₀ n) w)) (Neg.neg (ofNat₀ n)) := by
    rw [h_nx, ← add_assoc]
    
  rw [h_w_eq, h_lhs] at h_bern
  
  have h_add_n := add_le_add_right h_bern (ofNat₀ n)
  
  have h_cancel : Add.add (Add.add (Add.add (1:ℚ₀) (Mul.mul (ofNat₀ n) w)) (Neg.neg (ofNat₀ n))) (ofNat₀ n) = Add.add (1:ℚ₀) (Mul.mul (ofNat₀ n) w) := by
    have hc1 : Add.add (Add.add (Add.add (1:ℚ₀) (Mul.mul (ofNat₀ n) w)) (Neg.neg (ofNat₀ n))) (ofNat₀ n) = Add.add (Add.add (1:ℚ₀) (Mul.mul (ofNat₀ n) w)) (Add.add (Neg.neg (ofNat₀ n)) (ofNat₀ n)) := add_assoc _ _ _
    have hc2 : Add.add (Neg.neg (ofNat₀ n)) (ofNat₀ n) = (0:ℚ₀) := neg_add_self _
    have hc3 : Add.add (Add.add (1:ℚ₀) (Mul.mul (ofNat₀ n) w)) (0:ℚ₀) = Add.add (1:ℚ₀) (Mul.mul (ofNat₀ n) w) := add_zero _
    rw [hc1, hc2, hc3]
    
  rw [h_cancel] at h_add_n
  exact h_add_n

theorem pow_one (n : ℕ₀) : pow (1:ℚ₀) n = (1:ℚ₀) := by
  induction n with
  | zero => rfl
  | succ k ih =>
    have h1 : pow (1:ℚ₀) (σ k) = Mul.mul (1:ℚ₀) (pow (1:ℚ₀) k) := rfl
    have hm : Mul.mul (1:ℚ₀) (1:ℚ₀) = (1:ℚ₀) := one_mul _
    rw [h1, ih, hm]

theorem pow_ne_zero_of_pos {x : ℚ₀} (hx : 0 < x) (n : ℕ₀) : pow x n ≠ 0 := by
  have hp : 0 < pow x n := pow_pos n hx
  intro h
  rw [h] at hp
  exact hp.2 (le_refl 0)

theorem pow_mul_distrib (a b : ℚ₀) (n : ℕ₀) : pow (Mul.mul a b) n = Mul.mul (pow a n) (pow b n) := by
  induction n with
  | zero => rfl
  | succ k ih =>
    have h1 : pow (Mul.mul a b) (σ k) = Mul.mul (Mul.mul a b) (pow (Mul.mul a b) k) := rfl
    have h2 : pow a (σ k) = Mul.mul a (pow a k) := rfl
    have h3 : pow b (σ k) = Mul.mul b (pow b k) := rfl
    rw [h1, ih, h2, h3]
    have hc1 : Mul.mul (Mul.mul a b) (Mul.mul (pow a k) (pow b k)) = Mul.mul a (Mul.mul b (Mul.mul (pow a k) (pow b k))) := mul_assoc _ _ _
    have hc2 : Mul.mul b (Mul.mul (pow a k) (pow b k)) = Mul.mul (pow a k) (Mul.mul b (pow b k)) := by
      have hc2_1 : Mul.mul b (Mul.mul (pow a k) (pow b k)) = Mul.mul (Mul.mul b (pow a k)) (pow b k) := (mul_assoc _ _ _).symm
      have hc2_2 : Mul.mul b (pow a k) = Mul.mul (pow a k) b := mul_comm _ _
      have hc2_3 : Mul.mul (Mul.mul (pow a k) b) (pow b k) = Mul.mul (pow a k) (Mul.mul b (pow b k)) := mul_assoc _ _ _
      rw [hc2_1, hc2_2, hc2_3]
    have hc3 : Mul.mul a (Mul.mul (pow a k) (Mul.mul b (pow b k))) = Mul.mul (Mul.mul a (pow a k)) (Mul.mul b (pow b k)) := (mul_assoc _ _ _).symm
    rw [hc1, hc2, hc3]

theorem pow_inv (b : ℚ₀) (hb : 0 < b) (n : ℕ₀) : pow (inv b) n = inv (pow b n) := by
  have h_mul : Mul.mul (pow b n) (pow (inv b) n) = (1:ℚ₀) := by
    have hd : Mul.mul (pow b n) (pow (inv b) n) = pow (Mul.mul b (inv b)) n := (pow_mul_distrib b (inv b) n).symm
    have hb_ne : b ≠ 0 := by
      intro hc; rw [hc] at hb; exact hb.2 (le_refl 0)
    have hi : Mul.mul b (inv b) = (1:ℚ₀) := mul_inv_cancel hb_ne
    have ho : pow (1:ℚ₀) n = (1:ℚ₀) := pow_one n
    rw [hd, hi, ho]
  
  have hb_pow_ne_zero : pow b n ≠ 0 := pow_ne_zero_of_pos hb n
  exact inv_unique hb_pow_ne_zero h_mul

theorem newton_seq_pow_ge (q : ℚ₀) (n : Peano.ℕ₂) (hq : 0 < q) (k : ℕ₀) :
  q ≤ pow (newton_raphson_seq q n (σ k)) n.val.val := by
  let x_k := newton_raphson_seq q n k
  have hx_k_pos : 0 < x_k := newton_seq_pos q n hq k
  let x_next := newton_raphson_seq q n (σ k)
  
  -- Si q = 1, es trivial
  by_cases hq_one : q = (1:ℚ₀)
  · have h_step : newton_raphson_seq q n (σ k) = newton_raphson_step q n x_k := rfl
    have h_or : q = (0:ℚ₀) ∨ q = (1:ℚ₀) := Or.inr hq_one
    have h_if : newton_raphson_step q n x_k = q := if_pos h_or
    rw [h_step, h_if, hq_one, pow_one]
    exact le_refl (1:ℚ₀)
  
  -- Si q ≠ 1, usamos la expansión algebraica
  · let n_val := n.val.val
    let n_min_1 := Peano.Sub.sub n_val 𝟙
    
    have hn_eq : n_val = σ n_min_1 := by
      cases h_val : n_val with
      | zero => 
        have h_lt : n.val.val ≠ 0 := n.val.property
        exact False.elim (h_lt h_val)
      | succ n' => 
        have h_nmin1 : n_min_1 = n' := by
          change Peano.Sub.sub n_val 𝟙 = n'
          rw [h_val, Peano.Sub.sub_one]
          exact τ_σ_eq_self n'
        rw [h_nmin1]
      
    let w := Mul.mul x_next (inv x_k)
    
    have hx_ne : x_k ≠ 0 := by
      intro hc; rw [hc] at hx_k_pos; exact hx_k_pos.2 (le_refl 0)
      
    have hx_next_pos : 0 < x_next := newton_seq_pos q n hq (σ k)
    have hw_nonneg : 0 ≤ w := mul_nonneg (le_of_lt hx_next_pos) (inv_nonneg (le_of_lt hx_k_pos) hx_ne)
    
    have h_or : ¬(q = (0:ℚ₀) ∨ q = (1:ℚ₀)) := by
      intro hc
      cases hc with
      | inl h0 => rw [h0] at hq; exact hq.2 (le_refl 0)
      | inr h1 => exact hq_one h1
    
    have h_step : x_next = newton_raphson_step q n x_k := rfl
    have h_xnext_def : x_next = Mul.mul (inv (ofNat₀ n_val)) (Add.add (Mul.mul (ofNat₀ n_min_1) x_k) (Mul.mul q (inv (pow x_k n_min_1)))) := by
      rw [h_step]
      unfold newton_raphson_step
      rw [if_neg h_or]
      
    have hn_pos : 0 < ofNat₀ n_val := ofNat₀_pos n.val.property
    have hn_ne_0 : ofNat₀ n_val ≠ 0 := by
      intro hc
      rw [hc] at hn_pos
      exact hn_pos.2 (le_refl 0)
      
    have h_xnext : Mul.mul (ofNat₀ n_val) x_next = Add.add (Mul.mul (ofNat₀ n_min_1) x_k) (Mul.mul q (inv (pow x_k n_min_1))) := by
      rw [h_xnext_def]
      have h_assoc : Mul.mul (ofNat₀ n_val) (Mul.mul (inv (ofNat₀ n_val)) (Add.add (Mul.mul (ofNat₀ n_min_1) x_k) (Mul.mul q (inv (pow x_k n_min_1))))) = Mul.mul (Mul.mul (ofNat₀ n_val) (inv (ofNat₀ n_val))) (Add.add (Mul.mul (ofNat₀ n_min_1) x_k) (Mul.mul q (inv (pow x_k n_min_1)))) := (mul_assoc _ _ _).symm
      rw [h_assoc]
      have h_mul_inv : Mul.mul (ofNat₀ n_val) (inv (ofNat₀ n_val)) = 1 := mul_inv_cancel hn_ne_0
      rw [h_mul_inv]
      exact ℚ₀.one_mul _
      
    have h_nw_step1 : Mul.mul (ofNat₀ n_val) w = Mul.mul (Add.add (Mul.mul (ofNat₀ n_min_1) x_k) (Mul.mul q (inv (pow x_k n_min_1)))) (inv x_k) := by
      change Mul.mul (ofNat₀ n_val) (Mul.mul x_next (inv x_k)) = _
      have h_assoc : Mul.mul (ofNat₀ n_val) (Mul.mul x_next (inv x_k)) = Mul.mul (Mul.mul (ofNat₀ n_val) x_next) (inv x_k) := (mul_assoc _ _ _).symm
      rw [h_assoc, h_xnext]

    have h_nw_step2 : Mul.mul (Add.add (Mul.mul (ofNat₀ n_min_1) x_k) (Mul.mul q (inv (pow x_k n_min_1)))) (inv x_k) = Add.add (Mul.mul (Mul.mul (ofNat₀ n_min_1) x_k) (inv x_k)) (Mul.mul (Mul.mul q (inv (pow x_k n_min_1))) (inv x_k)) := right_distrib _ _ _

    have h_term1 : Mul.mul (Mul.mul (ofNat₀ n_min_1) x_k) (inv x_k) = ofNat₀ n_min_1 := by
      have h_assoc_term1 : Mul.mul (Mul.mul (ofNat₀ n_min_1) x_k) (inv x_k) = Mul.mul (ofNat₀ n_min_1) (Mul.mul x_k (inv x_k)) := mul_assoc _ _ _
      rw [h_assoc_term1]
      have h_xk_inv : Mul.mul x_k (inv x_k) = 1 := mul_inv_cancel hx_ne
      rw [h_xk_inv]
      exact ℚ₀.mul_one _

    have h_term2 : Mul.mul (Mul.mul q (inv (pow x_k n_min_1))) (inv x_k) = Mul.mul q (inv (pow x_k n_val)) := by
      have h_assoc_term2 : Mul.mul (Mul.mul q (inv (pow x_k n_min_1))) (inv x_k) = Mul.mul q (Mul.mul (inv (pow x_k n_min_1)) (inv x_k)) := mul_assoc _ _ _
      rw [h_assoc_term2]
      have h_inv_mul : Mul.mul (inv (pow x_k n_min_1)) (inv x_k) = inv (pow x_k n_val) := by
        have hh : inv (Mul.mul (pow x_k n_min_1) x_k) = Mul.mul (inv (pow x_k n_min_1)) (inv x_k) := inv_mul_inv (pow x_k n_min_1) x_k (pow_ne_zero_of_pos hx_k_pos n_min_1) hx_ne
        rw [← hh]
        have h_pow_comm : Mul.mul (pow x_k n_min_1) x_k = Mul.mul x_k (pow x_k n_min_1) := mul_comm _ _
        rw [h_pow_comm]
        have h_pow_def : Mul.mul x_k (pow x_k n_min_1) = pow x_k (σ n_min_1) := rfl
        rw [h_pow_def, ← hn_eq]
      rw [h_inv_mul]

    have h_nw : Mul.mul (ofNat₀ n_val) w = Add.add (ofNat₀ n_min_1) (Mul.mul q (inv (pow x_k n_val))) := by
      rw [h_nw_step1, h_nw_step2, h_term1, h_term2]
      
    have h_one_add_nw : Add.add (1:ℚ₀) (Mul.mul (ofNat₀ n_val) w) = Add.add (ofNat₀ n_val) (Mul.mul q (inv (pow x_k n_val))) := by
      rw [h_nw]
      have h_assoc_add : Add.add (1:ℚ₀) (Add.add (ofNat₀ n_min_1) (Mul.mul q (inv (pow x_k n_val)))) = Add.add (Add.add (1:ℚ₀) (ofNat₀ n_min_1)) (Mul.mul q (inv (pow x_k n_val))) := (add_assoc _ _ _).symm
      rw [h_assoc_add]
      have h_one_add_n_min_1 : Add.add (1:ℚ₀) (ofNat₀ n_min_1) = ofNat₀ n_val := by
        have h1_def : (1:ℚ₀) = ofNat₀ 𝟙 := rfl
        rw [h1_def, ← ofNat₀_add]
        have h_add_comm : Peano.Add.add 𝟙 n_min_1 = Peano.Add.add n_min_1 𝟙 := Peano.Add.add_comm _ _
        rw [h_add_comm]
        have hh : Peano.Add.add n_min_1 𝟙 = σ n_min_1 := rfl
        rw [hh, ← hn_eq]
      rw [h_one_add_n_min_1]
      
    have h_bern := bernoulli_ineq_alt2 w hw_nonneg n_val
    rw [h_one_add_nw] at h_bern
    have h_comm : Add.add (ofNat₀ n_val) (Mul.mul q (inv (pow x_k n_val))) = Add.add (Mul.mul q (inv (pow x_k n_val))) (ofNat₀ n_val) := add_comm _ _
    rw [h_comm] at h_bern
    
    have h_le := le_of_add_le_add_right h_bern
    
    have h_wn : pow w n_val = Mul.mul (pow x_next n_val) (inv (pow x_k n_val)) := by
      have h_pow_w : pow w n_val = pow (Mul.mul x_next (inv x_k)) n_val := rfl
      rw [h_pow_w, pow_mul_distrib, pow_inv _ hx_k_pos]
      
    rw [h_wn] at h_le
    
    have h_mul_xn := mul_le_mul_right_of_nonneg h_le (le_of_lt (pow_pos n_val hx_k_pos))
    
    have h_cancel1 : Mul.mul (Mul.mul q (inv (pow x_k n_val))) (pow x_k n_val) = q := by
      have h_assoc : Mul.mul (Mul.mul q (inv (pow x_k n_val))) (pow x_k n_val) = Mul.mul q (Mul.mul (inv (pow x_k n_val)) (pow x_k n_val)) := mul_assoc _ _ _
      have h_inv : Mul.mul (inv (pow x_k n_val)) (pow x_k n_val) = (1:ℚ₀) := inv_mul_cancel (pow_ne_zero_of_pos hx_k_pos n_val)
      have hm1 : Mul.mul q (1:ℚ₀) = q := mul_one _
      rw [h_assoc, h_inv, hm1]
      
    have h_cancel2 : Mul.mul (Mul.mul (pow x_next n_val) (inv (pow x_k n_val))) (pow x_k n_val) = pow x_next n_val := by
      have h_assoc : Mul.mul (Mul.mul (pow x_next n_val) (inv (pow x_k n_val))) (pow x_k n_val) = Mul.mul (pow x_next n_val) (Mul.mul (inv (pow x_k n_val)) (pow x_k n_val)) := mul_assoc _ _ _
      have h_inv : Mul.mul (inv (pow x_k n_val)) (pow x_k n_val) = (1:ℚ₀) := inv_mul_cancel (pow_ne_zero_of_pos hx_k_pos n_val)
      have hm2 : Mul.mul (pow x_next n_val) (1:ℚ₀) = pow x_next n_val := mul_one _
      rw [h_assoc, h_inv, hm2]
      
    rw [h_cancel1, h_cancel2] at h_mul_xn
    exact h_mul_xn

theorem newton_seq_monotone (q : ℚ₀) (n : Peano.ℕ₂) (hq : 0 < q) (k : ℕ₀) :
  newton_raphson_seq q n (σ (σ k)) ≤ newton_raphson_seq q n (σ k) := by
  by_cases hq_one : q = 1
  · have h_step1 : newton_raphson_seq q n (σ k) = newton_raphson_step q n (newton_raphson_seq q n k) := rfl
    have h_eval1 : newton_raphson_step q n (newton_raphson_seq q n k) = q := by
      unfold newton_raphson_step
      rw [if_pos (Or.inr hq_one)]
    have h_step2 : newton_raphson_seq q n (σ (σ k)) = newton_raphson_step q n (newton_raphson_seq q n (σ k)) := rfl
    have h_eval2 : newton_raphson_step q n (newton_raphson_seq q n (σ k)) = q := by
      unfold newton_raphson_step
      rw [if_pos (Or.inr hq_one)]
    rw [h_step1, h_eval1, h_step2, h_eval2]
    exact le_refl q
  · let y := newton_raphson_seq q n (σ k)
    have hy_pos : 0 < y := newton_seq_pos q n hq (σ k)
    have hy_ne : y ≠ 0 := by intro hc; rw [hc] at hy_pos; exact hy_pos.2 (le_refl 0)
    
    have hq_le_yn : q ≤ pow y n.val.val := newton_seq_pow_ge q n hq k
    
    let y_next := newton_raphson_seq q n (σ (σ k))
    
    have h_or : ¬(q = (0:ℚ₀) ∨ q = (1:ℚ₀)) := by
      intro hc
      cases hc with
      | inl h0 => rw [h0] at hq; exact hq.2 (le_refl 0)
      | inr h1 => exact hq_one h1

    have h_ynext_def : y_next = Mul.mul (inv (ofNat₀ n.val.val)) (Add.add (Mul.mul (ofNat₀ (Peano.Sub.sub n.val.val 𝟙)) y) (Mul.mul q (inv (pow y (Peano.Sub.sub n.val.val 𝟙))))) := by
      have h_step : y_next = newton_raphson_step q n y := rfl
      rw [h_step]
      unfold newton_raphson_step
      rw [if_neg h_or]
      
    let n_val := n.val.val
    let n_min_1 := Peano.Sub.sub n_val 𝟙
    have hn_eq : n_val = σ n_min_1 := by
      cases h_val : n_val with
      | zero => 
        have h_lt : n.val.val ≠ 0 := n.val.property
        exact False.elim (h_lt h_val)
      | succ n' => 
        have h_nmin1 : n_min_1 = n' := by
          change Peano.Sub.sub n_val 𝟙 = n'
          rw [h_val, Peano.Sub.sub_one]
          exact τ_σ_eq_self n'
        rw [h_nmin1]
      
    have hn_pos : 0 < ofNat₀ n_val := ofNat₀_pos n.val.property
    have hn_ne_0 : ofNat₀ n_val ≠ 0 := by
      intro hc; rw [hc] at hn_pos; exact hn_pos.2 (le_refl 0)

    have hn_val_y : Mul.mul (ofNat₀ n_val) y = Add.add (Mul.mul (ofNat₀ n_min_1) y) y := by
      have h_one_add : ofNat₀ n_val = Add.add (ofNat₀ n_min_1) (1:ℚ₀) := by
        have hh : ofNat₀ n_val = ofNat₀ (Peano.Add.add n_min_1 𝟙) := by rw [hn_eq]; rfl
        rw [hh, ofNat₀_add]
        rfl
      have hd : Mul.mul (Add.add (ofNat₀ n_min_1) (1:ℚ₀)) y = Add.add (Mul.mul (ofNat₀ n_min_1) y) (Mul.mul (1:ℚ₀) y) := right_distrib _ _ _
      have h1 : Mul.mul (1:ℚ₀) y = y := one_mul y
      rw [h_one_add, hd, h1]
      
    have h_n_ynext : Mul.mul (ofNat₀ n_val) y_next = Add.add (Mul.mul (ofNat₀ n_min_1) y) (Mul.mul q (inv (pow y n_min_1))) := by
      rw [h_ynext_def]
      have h_assoc : Mul.mul (ofNat₀ n_val) (Mul.mul (inv (ofNat₀ n_val)) (Add.add (Mul.mul (ofNat₀ n_min_1) y) (Mul.mul q (inv (pow y n_min_1))))) = Mul.mul (Mul.mul (ofNat₀ n_val) (inv (ofNat₀ n_val))) (Add.add (Mul.mul (ofNat₀ n_min_1) y) (Mul.mul q (inv (pow y n_min_1)))) := (mul_assoc _ _ _).symm
      rw [h_assoc]
      have h_inv : Mul.mul (ofNat₀ n_val) (inv (ofNat₀ n_val)) = 1 := mul_inv_cancel hn_ne_0
      have h1 : Mul.mul (1:ℚ₀) (Add.add (Mul.mul (ofNat₀ n_min_1) y) (Mul.mul q (inv (pow y n_min_1)))) = Add.add (Mul.mul (ofNat₀ n_min_1) y) (Mul.mul q (inv (pow y n_min_1))) := one_mul _
      rw [h_inv, h1]

    have h_pow_pos : 0 < pow y n_min_1 := pow_pos n_min_1 hy_pos
    have h_pow_inv_pos : 0 < inv (pow y n_min_1) := inv_pos h_pow_pos
    
    have h_mul_le_pow : Mul.mul q (inv (pow y n_min_1)) ≤ Mul.mul (pow y n_val) (inv (pow y n_min_1)) := 
      mul_le_mul_right_of_nonneg hq_le_yn (le_of_lt h_pow_inv_pos)
      
    have h_cancel : Mul.mul (pow y n_val) (inv (pow y n_min_1)) = y := by
      have h_pow_def : pow y n_val = pow y (σ n_min_1) := by rw [hn_eq]
      rw [h_pow_def]
      change Mul.mul (Mul.mul y (pow y n_min_1)) (inv (pow y n_min_1)) = y
      have h_assoc : Mul.mul (Mul.mul y (pow y n_min_1)) (inv (pow y n_min_1)) = Mul.mul y (Mul.mul (pow y n_min_1) (inv (pow y n_min_1))) := mul_assoc _ _ _
      rw [h_assoc]
      have h_inv : Mul.mul (pow y n_min_1) (inv (pow y n_min_1)) = 1 := mul_inv_cancel (pow_ne_zero_of_pos hy_pos _)
      have h1 : Mul.mul y (1:ℚ₀) = y := mul_one y
      rw [h_inv, h1]

    rw [h_cancel] at h_mul_le_pow
    
    have h_add_le : Add.add (Mul.mul (ofNat₀ n_min_1) y) (Mul.mul q (inv (pow y n_min_1))) ≤ Add.add (Mul.mul (ofNat₀ n_min_1) y) y := 
      add_le_add_left h_mul_le_pow _
      
    rw [← h_n_ynext, ← hn_val_y] at h_add_le
    
    have h_final_mul : Mul.mul (inv (ofNat₀ n_val)) (Mul.mul (ofNat₀ n_val) y_next) ≤ Mul.mul (inv (ofNat₀ n_val)) (Mul.mul (ofNat₀ n_val) y) := 
      mul_le_mul_left_of_nonneg h_add_le (le_of_lt (inv_pos hn_pos))
      
    have h_inv_cancel : Mul.mul (inv (ofNat₀ n_val)) (ofNat₀ n_val) = 1 := inv_mul_cancel hn_ne_0
    
    have h_left : Mul.mul (inv (ofNat₀ n_val)) (Mul.mul (ofNat₀ n_val) y_next) = y_next := by
      have h_assoc : Mul.mul (inv (ofNat₀ n_val)) (Mul.mul (ofNat₀ n_val) y_next) = Mul.mul (Mul.mul (inv (ofNat₀ n_val)) (ofNat₀ n_val)) y_next := (mul_assoc _ _ _).symm
      have h1 : Mul.mul (1:ℚ₀) y_next = y_next := one_mul y_next
      rw [h_assoc, h_inv_cancel, h1]
    have h_right : Mul.mul (inv (ofNat₀ n_val)) (Mul.mul (ofNat₀ n_val) y) = y := by
      have h_assoc : Mul.mul (inv (ofNat₀ n_val)) (Mul.mul (ofNat₀ n_val) y) = Mul.mul (Mul.mul (inv (ofNat₀ n_val)) (ofNat₀ n_val)) y := (mul_assoc _ _ _).symm
      have h1 : Mul.mul (1:ℚ₀) y = y := one_mul y
      rw [h_assoc, h_inv_cancel, h1]
      
    rw [h_left, h_right] at h_final_mul
    exact h_final_mul

end ℚ₀
