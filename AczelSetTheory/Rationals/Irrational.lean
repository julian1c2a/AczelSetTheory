/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

import AczelSetTheory.Rationals.Roots
import AczelSetTheory.Integers.Functions
import AczelSetTheory.Integers.Order
import Peano.PeanoNat.Combinatorics.Pow

open Peano Peano.Axioms Peano.Order

namespace ℤ₀

private theorem one_le_of_ne_zero_nat {n : ℕ₀} (h : n ≠ 𝟘) : le₀ 𝟙 n := by
  cases n with
  | zero => exact False.elim (h rfl)
  | succ k => exact succ_le_succ_if_wp (zero_le k)

private theorem sub_eq_add_neg (a b : ℤ₀) : Sub.sub a b = Add.add a (Neg.neg b) := rfl

private theorem sub_ne_zero_of_ne {x y : ℤ₀} (h : x ≠ y) : Sub.sub x y ≠ 0 := by
  intro heq
  have h1 : Add.add (Sub.sub x y) y = Add.add 0 y := congrArg (fun a => Add.add a y) heq
  rw [sub_eq_add_neg, add_assoc, neg_add_self, add_zero, zero_add] at h1
  exact h h1

/-- Lema de Separación en enteros: Si x e y son enteros distintos, su diferencia absoluta es mayor o igual a 1. -/
theorem int_sep_lemma (x y : ℤ₀) (h : x ≠ y) : (1:ℤ₀) ≤ ℤ₀.abs (Sub.sub x y) := by
  have h_ne : Sub.sub x y ≠ 0 := sub_ne_zero_of_ne h
  have hz : ℤ₀.abs (Sub.sub x y) ≠ 0 := fun hz_eq => h_ne (ℤ₀.abs_eq_zero_iff.mp hz_eq)
  have h_nonneg : 0 ≤ ℤ₀.abs (Sub.sub x y) := ℤ₀.abs_nonneg _
  have h_eq : ℤ₀.abs (Sub.sub x y) = ℤ₀.ofNat (ℤ₀.toNat (ℤ₀.abs (Sub.sub x y))) :=
    ℤ₀.nonneg_eq_ofNat h_nonneg
  have h_n_ne : ℤ₀.toNat (ℤ₀.abs (Sub.sub x y)) ≠ 𝟘 := by
    intro hn
    have h_abs_zero : ℤ₀.abs (Sub.sub x y) = 0 := by
      calc ℤ₀.abs (Sub.sub x y) = ℤ₀.ofNat (ℤ₀.toNat (ℤ₀.abs (Sub.sub x y))) := h_eq
           _ = ℤ₀.ofNat 𝟘 := congrArg ℤ₀.ofNat hn
           _ = 0 := ℤ₀.ofNat_zero
    exact hz h_abs_zero
  have h_le_nat : le₀ 𝟙 (ℤ₀.toNat (ℤ₀.abs (Sub.sub x y))) := one_le_of_ne_zero_nat h_n_ne
  have h_le_int : ℤ₀.ofNat 𝟙 ≤ ℤ₀.ofNat (ℤ₀.toNat (ℤ₀.abs (Sub.sub x y))) :=
    ℤ₀.le_ofNat_iff.mpr h_le_nat
  have h_one : (1:ℤ₀) = ℤ₀.ofNat 𝟙 := rfl
  rw [h_one, h_eq]
  exact h_le_int

/-- Lema de Separación para potencias: Si a^n y m * b^n son distintos, su diferencia absoluta es ≥ 1 -/
theorem int_sep_pow_lemma (a b m : ℤ₀) (n : ℕ₀) (h : ℤ₀.powZ a n ≠ Mul.mul m (ℤ₀.powZ b n)) :
    (1:ℤ₀) ≤ ℤ₀.abs (Sub.sub (ℤ₀.powZ a n) (Mul.mul m (ℤ₀.powZ b n))) :=
  int_sep_lemma (ℤ₀.powZ a n) (Mul.mul m (ℤ₀.powZ b n)) h

end ℤ₀

namespace ℚ₀

def powN1 (b : ℕ₁) (n : ℕ₀) : ℕ₁ := 
  ⟨Peano.Pow.pow b.val n, Peano.Pow.pow_ne_zero b.property n⟩

theorem powN1_zero (b : ℕ₁) : powN1 b 𝟘 = den1 := rfl

theorem pow_mk (a : ℤ₀) (b : ℕ₁) (n : ℕ₀) : 
  pow (mk a b) n = mk (ℤ₀.powZ a n) (powN1 b n) := by
  induction n with
  | zero =>
    have h1 : pow (mk a b) 𝟘 = ofNat₀ 𝟙 := rfl
    have h2 : ℤ₀.powZ a 𝟘 = 1 := rfl
    have h_ofNat₀ : ofNat₀ 𝟙 = mk 1 den1 := ofNat₀_eq_mk 𝟙
    rw [h1, h_ofNat₀, h2]
    rfl
  | succ k ih =>
    change Mul.mul (mk a b) (pow (mk a b) k) = mk (Mul.mul (ℤ₀.powZ a k) a) (powN1 b (σ k))
    rw [ih]
    rw [mul_mk]
    have h_num : Mul.mul a (ℤ₀.powZ a k) = Mul.mul (ℤ₀.powZ a k) a := ℤ₀.mul_comm _ _
    rw [h_num]
    apply congrArg (mk (Mul.mul (ℤ₀.powZ a k) a))
    have h_den : (mulDen b (powN1 b k)).val = (powN1 b (σ k)).val := by
      change Peano.Mul.mul b.val (Peano.Pow.pow b.val k) = Peano.Mul.mul (Peano.Pow.pow b.val k) b.val
      exact Peano.Mul.mul_comm _ _
    exact Subtype.ext h_den

theorem ofInt_eq_mk (m : ℤ₀) : ofInt m = mk m den1 := rfl

theorem powZ_ofNat_eq (b : ℕ₀) (n : ℕ₀) : ℤ₀.ofNat (Peano.Pow.pow b n) = ℤ₀.powZ (ℤ₀.ofNat b) n := by
  induction n with
  | zero =>
    change ℤ₀.ofNat 𝟙 = 1
    exact ℤ₀.ofNat_one
  | succ k ih =>
    change ℤ₀.ofNat (Peano.Mul.mul (Peano.Pow.pow b k) b) = Mul.mul (ℤ₀.powZ (ℤ₀.ofNat b) k) (ℤ₀.ofNat b)
    rw [ℤ₀.ofNat_mul]
    rw [ih]

theorem rational_not_root (a : ℤ₀) (b : ℕ₁) (m : ℤ₀) (n : ℕ₀) 
  (h_irr : ∀ a' b', ℤ₀.powZ a' n ≠ Mul.mul m (ℤ₀.powZ (ℤ₀.ofNat b') n)) : 
  pow (mk a b) n ≠ ofInt m := by
  intro heq
  rw [pow_mk] at heq
  have h_ofInt : ofInt m = mk m den1 := rfl
  rw [h_ofInt] at heq
  have h_eq_iff := mk_eq_iff (ℤ₀.powZ a n) m (powN1 b n) den1
  rw [h_eq_iff] at heq
  have h_den1 : ℤ₀.ofNat den1.val = 1 := rfl
  rw [h_den1] at heq
  rw [ℤ₀.mul_one] at heq
  have h_irr_spec := h_irr a b.val
  have h_powZ_b : ℤ₀.ofNat (powN1 b n).val = ℤ₀.powZ (ℤ₀.ofNat b.val) n := powZ_ofNat_eq b.val n
  rw [h_powZ_b] at heq
  exact h_irr_spec heq

end ℚ₀
