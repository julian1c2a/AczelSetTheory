import AczelSetTheory.Rationals.Inv

open Peano
open Peano.Axioms

theorem absNat_ne_zero {z : ℤ₀} (h : z ≠ 0) : ℚ₀.absNat z ≠ 𝟘 := by
  intro h_abs
  unfold ℚ₀.absNat at h_abs
  have h_abs_nonneg : (0:ℤ₀) ≤ ℤ₀.abs z := ℤ₀.abs_nonneg z
  have h_eq : ℤ₀.abs z = ℤ₀.ofNat (ℤ₀.abs z).repr.1 := ℤ₀.nonneg_eq_ofNat h_abs_nonneg
  have h_toNat : ℤ₀.toNat (ℤ₀.abs z) = (ℤ₀.abs z).repr.1 := rfl
  rw [← h_toNat, h_abs] at h_eq
  have h_abs_zero : ℤ₀.abs z = 0 := by
    rw [h_eq]
    exact ℤ₀.ofNat_zero
  have h_z_zero : z = 0 := ℤ₀.abs_eq_zero_iff.mp h_abs_zero
  exact h h_z_zero
