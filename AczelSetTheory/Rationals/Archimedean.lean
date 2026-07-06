import AczelSetTheory.Rationals.Basic
import AczelSetTheory.Integers.Basic
import AczelSetTheory.Integers.Order
import AczelSetTheory.Integers.Functions
import Peano

open Peano Peano.Order Peano.Axioms Peano.Add Peano.Mul
open ℤ₀ ℚ₀

theorem le_ofNat_repr_fst (a : ℤ₀) : a ≤ ofNat a.repr.1 := by
  have h := (ℤ₀.le_iff_mpr (a := a) (b := ofNat a.repr.1))
  have hb : (ofNat a.repr.1 : ℤ₀).repr = (a.repr.1, 𝟘) := repr_ofNat _
  have h1 : add a.repr.1 𝟘 = a.repr.1 := by omega₀
  have h2 : add a.repr.2 a.repr.1 = add a.repr.1 a.repr.2 := by omega₀
  apply h
  rw [hb]
  show le₀ (add a.repr.1 𝟘) (add a.repr.2 a.repr.1)
  rw [h1, h2]
  exact le_self_add a.repr.1 a.repr.2

theorem int_not_le_zero_implies_ge_one (a : ℤ₀) (h : ¬ a ≤ 0) : (1:ℤ₀) ≤ a := by
  have hz : (0 : ℤ₀).repr = (𝟘, 𝟘) := by show (ofNat 𝟘).repr = (𝟘, 𝟘); exact repr_ofNat 𝟘
  have ho : (1 : ℤ₀).repr = (𝟙, 𝟘) := by show (ofNat 𝟙).repr = (𝟙, 𝟘); exact repr_ofNat 𝟙
  have h_not : ¬ (add a.repr.1 𝟘 ≤ add a.repr.2 𝟘) := by
    intro hh
    apply h
    apply ℤ₀.le_iff_mpr
    rw [hz]
    exact hh
  have h_add_zero1 : add a.repr.1 𝟘 = a.repr.1 := by omega₀
  have h_add_zero2 : add a.repr.2 𝟘 = a.repr.2 := by omega₀
  rw [h_add_zero1, h_add_zero2] at h_not
  apply ℤ₀.le_iff_mpr
  rw [ho]
  -- we have h_not : ¬ le₀ a.repr.1 a.repr.2
  have h_gt : lt₀ a.repr.2 a.repr.1 := ngt_then_le a.repr.1 a.repr.2 h_not
  -- h_gt : a.repr.2 < a.repr.1 i.e. succ a.repr.2 ≤ a.repr.1
  have h_le : le₀ (add 𝟙 a.repr.2) (add 𝟘 a.repr.1) := by
    -- 1 + a.repr.2 is succ a.repr.2
    have h1 : add 𝟙 a.repr.2 = σ a.repr.2 := by
      rw [Peano.Add.add_comm, Peano.Add.add_one]
    have h2 : add 𝟘 a.repr.1 = a.repr.1 := Peano.Add.zero_add a.repr.1
    rw [h1, h2]
    exact lt_nm_then_le_nm _ _ h_gt
  exact h_le

theorem int_lt_add_of_pos {a b : ℤ₀} (hb : 0 < b) : a < Add.add a b := by
  have h := add_lt_add_right hb a
  have h0 : Add.add 0 a = a := zero_add a
  rwa [h0, add_comm b a] at h

theorem int_lt_of_le_of_lt {a b c : ℤ₀} (hab : a ≤ b) (hbc : b < c) : a < c := by
  have hac : a ≤ c := le_trans hab hbc.1
  refine ⟨hac, fun hca => hbc.2 (le_trans hca hab)⟩

theorem int_lt_of_lt_of_le {a b c : ℤ₀} (hab : a < b) (hbc : b ≤ c) : a < c := by
  have hac : a ≤ c := le_trans hab.1 hbc
  refine ⟨hac, fun hca => hab.2 (le_trans hbc hca)⟩

theorem int_zero_lt_one : (0:ℤ₀) < (1:ℤ₀) := by
  have h1 : (0:ℤ₀) ≤ (1:ℤ₀) := zero_le_ofNat 1
  have h2 : ¬ (1:ℤ₀) ≤ (0:ℤ₀) := by
    intro h
    have hh : ¬ ofNat 1 ≤ ofNat 𝟘 := by
      have hne : (1:ℕ₀) ≠ 0 := by
        intro hh; have hh2 : σ 𝟘 = 𝟘 := hh; exact succ_neq_zero 𝟘 hh2
      have hpos : 0 < (ofNat 1:ℤ₀) := ofNat_pos_of_ne_zero hne
      exact hpos.2
    exact hh h
  exact ⟨h1, h2⟩

theorem archimedean_int (p1 q1 : ℤ₀) (p2 q2 : ℕ₀) (hx : ¬ p1 ≤ 0) (hq2_ne : q2 ≠ 𝟘) :
    ∃ N : ℕ₀, ¬ Mul.mul (ofNat N) (Mul.mul p1 (ofNat q2)) ≤ Mul.mul q1 (ofNat p2) := by
  let A := Mul.mul p1 (ofNat q2)
  let B := Mul.mul q1 (ofNat p2)
  let M := mul q1.repr.1 p2
  let N := σ M
  refine ⟨N, ?_⟩

  have hp1 : (1:ℤ₀) ≤ p1 := int_not_le_zero_implies_ge_one p1 hx

  have hq2_not_le_0 : ¬ ofNat q2 ≤ 0 := by
    intro h
    have hh : q2 = 𝟘 := by
      have h1 : (0:ℤ₀).repr = (𝟘, 𝟘) := repr_ofNat _
      have h2 : (ofNat q2 : ℤ₀).repr = (q2, 𝟘) := repr_ofNat _
      have h' := ℤ₀.le_iff_mp h
      rw [h1, h2] at h'
      have hq2 : add q2 𝟘 = q2 := Peano.Add.add_zero q2
      have h00 : add 𝟘 𝟘 = 𝟘 := Peano.Add.add_zero 𝟘
      rw [hq2, h00] at h'
      exact (Peano.Order.le_zero_eq_zero q2).mp h'
    exact hq2_ne hh

  have hq2_int : (1:ℤ₀) ≤ ofNat q2 := int_not_le_zero_implies_ge_one (ofNat q2) hq2_not_le_0

  have hA_ge1 : (1:ℤ₀) ≤ A := by
    have h1 : Mul.mul (1:ℤ₀) (1:ℤ₀) = 1 := by
      show ofNat (mul 1 1) = ofNat 1
      have hmul : mul 1 1 = 1 := by
        change Peano.Mul.mul 1 𝟙 = 1
        rw [Peano.Mul.mul_one]
      rw [hmul]
    have hp1_nonneg : (0:ℤ₀) ≤ p1 := le_trans (zero_le_ofNat 1) hp1
    have step1 : Mul.mul (1:ℤ₀) (1:ℤ₀) ≤ Mul.mul p1 (1:ℤ₀) :=
      mul_le_mul_right_of_nonneg hp1 (zero_le_ofNat 1)
    have step2 : Mul.mul p1 (1:ℤ₀) ≤ Mul.mul p1 (ofNat q2) :=
      mul_le_mul_left_of_nonneg hq2_int hp1_nonneg
    have hhh : Mul.mul (1:ℤ₀) (1:ℤ₀) ≤ A := le_trans step1 step2
    rwa [h1] at hhh

  have hA_pos : (0:ℤ₀) < A := int_lt_of_lt_of_le int_zero_lt_one hA_ge1

  have hB_le_M : B ≤ ofNat M := by
    have hz : ofNat (mul q1.repr.1 p2) = Mul.mul (ofNat q1.repr.1) (ofNat p2) := ofNat_mul _ _
    have h1 : Mul.mul (ofNat q1.repr.1) (ofNat p2) = ofNat M := hz.symm
    have hh : B ≤ Mul.mul (ofNat q1.repr.1) (ofNat p2) :=
      mul_le_mul_right_of_nonneg (le_ofNat_repr_fst q1) (zero_le_ofNat p2)
    rwa [h1] at hh

  have hM_le_MA : ofNat M ≤ Mul.mul (ofNat M) A := by
    have hm : ofNat (mul M 1) = Mul.mul (ofNat M) (ofNat 1) := ofNat_mul _ _
    have hm1 : mul M 1 = M := by
      change Peano.Mul.mul M 𝟙 = M
      rw [Peano.Mul.mul_one]
    have h1 : ofNat M = Mul.mul (ofNat M) (1:ℤ₀) := by
      show ofNat M = Mul.mul (ofNat M) (ofNat 1)
      rw [← hm, hm1]
    have step1 : Mul.mul (ofNat M) (1:ℤ₀) ≤ Mul.mul (ofNat M) A :=
      mul_le_mul_left_of_nonneg hA_ge1 (zero_le_ofNat M)
    rwa [← h1] at step1

  have h_mul_N : Mul.mul (ofNat N) A = Add.add (Mul.mul (ofNat M) A) A := by
    have hN : ofNat N = Add.add (ofNat M) (1:ℤ₀) := by
      show ofNat (σ M) = Add.add (ofNat M) (ofNat 1)
      rw [← ofNat_add]
      have hs : add M 1 = σ M := by
        change Peano.Add.add M 𝟙 = σ M
        rw [add_one]
      rw [hs]
    rw [hN, ℤ₀.right_distrib]
    have h_mul1 : Mul.mul (1:ℤ₀) A = A := by
      have hh : Mul.mul (1:ℤ₀) A = Mul.mul A (1:ℤ₀) := mul_comm _ _
      rw [hh]
      have hc : A = ofNat A.repr.1 := nonneg_eq_ofNat (le_trans (zero_le_ofNat 1) hA_ge1)
      rw [hc]
      show Mul.mul (ofNat A.repr.1) (ofNat 1) = ofNat A.repr.1
      have hh2 : ofNat (mul A.repr.1 1) = Mul.mul (ofNat A.repr.1) (ofNat 1) := ofNat_mul _ _
      rw [← hh2]
      have hm1 : mul A.repr.1 1 = A.repr.1 := by
        change Peano.Mul.mul A.repr.1 𝟙 = A.repr.1
        rw [Peano.Mul.mul_one]
      rw [hm1]
    rw [h_mul1]

  have h_strict : Mul.mul (ofNat M) A < Mul.mul (ofNat N) A := by
    rw [h_mul_N]
    exact int_lt_add_of_pos hA_pos

  have h_B_lt_NA : B < Mul.mul (ofNat N) A := by
    have step1 : B ≤ Mul.mul (ofNat M) A := le_trans hB_le_M hM_le_MA
    exact int_lt_of_le_of_lt step1 h_strict

  exact h_B_lt_NA.2


theorem archimedean (x y : ℚ₀) : 0 < x → ∃ N : ℕ₀, y < Mul.mul (ofNat₀ N) x := by
  revert x y
  refine Quotient.ind₂ (fun p q hx => ?_)
  sorry
