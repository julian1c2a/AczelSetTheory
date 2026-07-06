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

/--
Aproximación por el método de Newton-Raphson.
Para calcular la raíz n-ésima de m, se itera:
x_{k+1} = (1 / n) * ((n - 1) * x_k + m / (x_k ^ (n - 1)))
-/
def newton_raphson_step (m : ℕ₀) (n : Peano.ℕ₂) (x : ℚ₀) : ℚ₀ :=
  -- Si m = 0 o m = 1, la sucesión es constante y vale m (evitamos divisiones por cero u otras indefiniciones)
  if m = 𝟘 ∨ m = 𝟙 then
    ofNat₀ m
  else
    -- Queremos calcular: (1/n) * [ (n-1)*x + m * inv (x^(n-1)) ]
    let n_val := n.val.val
    let inv_n := inv (ofNat₀ n_val)
    -- Nota: n_minus_one = n - 1
    let n_minus_one := Peano.Sub.sub n_val 𝟙
    let part1 := Mul.mul (ofNat₀ n_minus_one) x
    let part2 := Mul.mul (ofNat₀ m) (inv (pow x n_minus_one))
    Mul.mul inv_n (Add.add part1 part2)

/--
Sucesión de aproximaciones de Newton-Raphson para la raíz n-ésima de m.
Comienza con la semilla x_0 = m.
-/
def newton_raphson_seq (m : ℕ₀) (n : Peano.ℕ₂) : ℕ₀ → ℚ₀
  | 𝟘 => ofNat₀ m
  | σ k => newton_raphson_step m n (newton_raphson_seq m n k)

end ℚ₀
