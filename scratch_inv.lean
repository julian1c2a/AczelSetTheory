import AczelSetTheory.Rationals.Inv

open Peano
open Peano.Axioms
open ℚ₀
open ℤ₀

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

private theorem invWD_proof (p q : ℤ₀ × ℕ₁) (h : Mul.mul p.1 (ℤ₀.ofNat q.2.val) = Mul.mul q.1 (ℤ₀.ofNat p.2.val))
    (h_p : p.1 ≠ 0) (h_q : q.1 ≠ 0) (hp_pos : 0 ≤ p.1) (hq_pos : 0 ≤ q.1) :
    Mul.mul (ℤ₀.ofNat p.2.val) (ℤ₀.ofNat (invDen q.1).val) = Mul.mul (ℤ₀.ofNat q.2.val) (ℤ₀.ofNat (invDen p.1).val) := by
  have h1 : ℤ₀.ofNat (invDen q.1).val = q.1 := by
    rw [ofNat_invDen_val_eq_abs h_q, abs_of_pos hq_pos]
  have h2 : ℤ₀.ofNat (invDen p.1).val = p.1 := by
    rw [ofNat_invDen_val_eq_abs h_p, abs_of_pos hp_pos]
  change Mul.mul (ℤ₀.ofNat p.2.val) q.1 = Mul.mul (ℤ₀.ofNat q.2.val) p.1
  rw [ℤ₀.mul_comm, ← h, ℤ₀.mul_comm]
