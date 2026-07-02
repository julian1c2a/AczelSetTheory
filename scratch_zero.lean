import AczelSetTheory.Integers.Basic
import AczelSetTheory.Integers.Order

open Peano
open Peano.Axioms
open ℤ₀

theorem eq_zero_of_mul_ofNat_eq_zero {z : ℤ₀} {n : ℕ₁} (h : Mul.mul z (ℤ₀.ofNat n.val) = 0) : z = 0 := by
  have hz_mul : Mul.mul 0 (ℤ₀.ofNat n.val) = 0 := ℤ₀.zero_mul _
  have h1 : Mul.mul z (ℤ₀.ofNat n.val) ≤ Mul.mul 0 (ℤ₀.ofNat n.val) := by rw [h, hz_mul]; exact ℤ₀.le_refl 0
  have h2 : Mul.mul 0 (ℤ₀.ofNat n.val) ≤ Mul.mul z (ℤ₀.ofNat n.val) := by rw [h, hz_mul]; exact ℤ₀.le_refl 0
  have hz1 : z ≤ 0 := (ℤ₀.mul_le_mul_right_ofNat_pos n.property z 0).mpr h1
  have hz2 : 0 ≤ z := (ℤ₀.mul_le_mul_right_ofNat_pos n.property 0 z).mpr h2
  exact ℤ₀.le_antisymm hz1 hz2
