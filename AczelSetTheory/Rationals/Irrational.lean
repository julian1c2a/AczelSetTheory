/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

import AczelSetTheory.Rationals.Roots
import AczelSetTheory.Integers.Functions
import AczelSetTheory.Integers.Order

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

end ℚ₀
