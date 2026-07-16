/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- AczelSetTheory/Integers/Functions.lean
-- Funciones básicas sobre ℤ₀cls: signo, valor absoluto, truncación, sucesor/predecesor, potencia.
--
-- Público:
--   ℤ₀cls.sign     : ℤ₀cls → ℤ₀cls   (−1, 0, 1)
--   ℤ₀cls.abs      : ℤ₀cls → ℤ₀cls   (valor absoluto)
--   ℤ₀cls.toNat    : ℤ₀cls → ℕ₀   (parte positiva del representante canónico)
--   ℤ₀cls.succZ    : ℤ₀cls → ℤ₀cls   (z + 1)
--   ℤ₀cls.predZ    : ℤ₀cls → ℤ₀cls   (z − 1)
--   ℤ₀cls.powZ     : ℤ₀cls → ℕ₀ → ℤ₀cls
--   Lemas: sign_zero, sign_ofNat, sign_neg
--          abs_ofNat, abs_nonneg, abs_neg
--          toNat_ofNat, toNat_neg
--          succZ_pred, predZ_succ
--          powZ_zero, powZ_succ, powZ_one

import AczelSetTheory.Integers.Order
import Peano.PeanoNat.Div

namespace ℤ₀cls

open Peano Peano.Axioms Peano.StrictOrder Peano.Add Peano.Sub Peano.Mul Peano.Div Peano.Order

-- ─────────────────────────────────────────────────────────────────────────────
-- Lemas privados auxiliares
-- ─────────────────────────────────────────────────────────────────────────────

private theorem neg_zero : Neg.neg (0 : ℤ₀cls) = 0 :=
  (add_zero (Neg.neg (0 : ℤ₀cls))).symm.trans (neg_add_self 0)

private theorem neg_le_zero_of_zero_le {z : ℤ₀cls} (h : 0 ≤ z) : Neg.neg z ≤ 0 := by
  have := neg_le_neg h; rwa [neg_zero] at this

private theorem zero_le_neg_of_le_zero {z : ℤ₀cls} (h : z ≤ 0) : 0 ≤ Neg.neg z := by
  have := neg_le_neg h; rwa [neg_zero] at this

-- ─────────────────────────────────────────────────────────────────────────────
-- sign
-- ─────────────────────────────────────────────────────────────────────────────

/-- Signo de z: 1 si z > 0, −1 si z < 0, 0 si z = 0. -/
def sign (z : ℤ₀cls) : ℤ₀cls :=
  if (0 : ℤ₀cls) < z then 1 else if z < (0 : ℤ₀cls) then -1 else 0

theorem sign_zero : sign (0 : ℤ₀cls) = 0 := by
  simp only [sign]
  have h : ¬ (0 : ℤ₀cls) < 0 := fun h => h.2 (le_refl 0)
  rw [if_neg h, if_neg h]

theorem sign_ofNat (n : ℕ₀) (hn : n ≠ 𝟘) : sign (ofNat n) = 1 := by
  simp only [sign]
  rw [if_pos]
  exact ⟨zero_le_ofNat n, fun hle => hn (by
    have h : ofNat n ≤ ofNat 𝟘 := hle
    rw [le_ofNat_iff] at h; omega₀)⟩

theorem sign_neg (z : ℤ₀cls) (hz : z < 0) : sign z = -1 := by
  simp only [sign]
  have h1 : ¬ (0 : ℤ₀cls) < z := fun h => hz.2 h.1
  rw [if_neg h1, if_pos hz]

-- ─────────────────────────────────────────────────────────────────────────────
-- abs
-- ─────────────────────────────────────────────────────────────────────────────

/-- Valor absoluto: z si z ≥ 0, −z si z < 0. -/
def abs (z : ℤ₀cls) : ℤ₀cls := if 0 ≤ z then z else -z

theorem abs_ofNat (n : ℕ₀) : abs (ofNat n) = ofNat n := by
  simp [abs, zero_le_ofNat]

theorem abs_nonneg (z : ℤ₀cls) : 0 ≤ abs z := by
  simp only [abs]
  by_cases h : (0 : ℤ₀cls) ≤ z
  · rw [if_pos h]; exact h
  · rw [if_neg h]
    exact zero_le_neg_of_le_zero ((le_total z 0).resolve_right h)

theorem abs_neg (z : ℤ₀cls) : abs (-z) = abs z := by
  simp only [abs]
  by_cases hz : (0 : ℤ₀cls) ≤ z
  · by_cases hnz : (0 : ℤ₀cls) ≤ -z
    · rw [if_pos hz, if_pos hnz]
      have h1 : -z ≤ 0 := neg_le_zero_of_zero_le hz
      have h2 : -z = 0    := le_antisymm h1 hnz
      have h3 : z = 0     := by have := neg_neg z; rw [h2, neg_zero] at this; exact this.symm
      rw [h2, h3]
    · rw [if_neg hnz, if_pos hz, neg_neg]
  · by_cases hnz : (0 : ℤ₀cls) ≤ -z
    · rw [if_pos hnz, if_neg hz]
    · exfalso
      exact hnz (zero_le_neg_of_le_zero ((le_total z 0).resolve_right hz))

-- ─────────────────────────────────────────────────────────────────────────────
-- abs_eq_zero_iff

theorem abs_eq_zero_iff {z : ℤ₀cls} : abs z = 0 ↔ z = 0 := by
  constructor
  · intro h
    unfold abs at h
    by_cases h0 : (0 : ℤ₀cls) ≤ z
    · rw [if_pos h0] at h; exact h
    · rw [if_neg h0] at h
      have h_neg : Neg.neg (Neg.neg z) = Neg.neg 0 := by rw [h]
      rw [neg_neg, neg_zero] at h_neg
      exact h_neg
  · intro h
    rw [h]
    unfold abs
    have h0 : (0 : ℤ₀cls) ≤ 0 := le_refl 0
    rw [if_pos h0]

-- ─────────────────────────────────────────────────────────────────────────────
-- toNat
-- ─────────────────────────────────────────────────────────────────────────────

/-- Parte positiva del representante canónico (cero si z ≤ 0). -/
def toNat (z : ℤ₀cls) : ℕ₀ := z.repr.1

theorem toNat_ofNat (n : ℕ₀) : toNat (ofNat n) = n := by
  simp [toNat, repr_ofNat]

theorem toNat_neg (n : ℕ₀) : toNat (Neg.neg (ofNat n)) = 𝟘 := by
  simp only [toNat]
  have heq := repr_neg_intEq (ofNat n)
  rw [repr_ofNat] at heq
  simp only [] at heq
  rcases repr_normalized (Neg.neg (ofNat n)) with h | h
  · exact h
  · simp only [h] at heq; omega₀

-- ─────────────────────────────────────────────────────────────────────────────
-- succZ / predZ
-- ─────────────────────────────────────────────────────────────────────────────

/-- Sucesor entero: z + 1. -/
def succZ (z : ℤ₀cls) : ℤ₀cls := Add.add z 1

/-- Predecesor entero: z − 1. -/
def predZ (z : ℤ₀cls) : ℤ₀cls := Add.add z (-1)

theorem succZ_pred (z : ℤ₀cls) : predZ (succZ z) = z := by
  simp only [succZ, predZ]
  rw [add_assoc, add_neg_self, add_zero]

theorem predZ_succ (z : ℤ₀cls) : succZ (predZ z) = z := by
  simp only [succZ, predZ]
  rw [add_assoc, neg_add_self, add_zero]

-- ─────────────────────────────────────────────────────────────────────────────
-- powZ
-- ─────────────────────────────────────────────────────────────────────────────

/-- Potencia entera: z^n para n : ℕ₀. -/
def powZ (z : ℤ₀cls) : ℕ₀ → ℤ₀cls
  | .zero   => 1
  | .succ n => Mul.mul (powZ z n) z

theorem powZ_zero (z : ℤ₀cls) : powZ z 𝟘 = 1 := rfl

theorem powZ_succ (z : ℤ₀cls) (n : ℕ₀) : powZ z (σ n) = Mul.mul (powZ z n) z := rfl

theorem powZ_one (z : ℤ₀cls) : powZ z 𝟙 = z := by
  rw [show (𝟙 : ℕ₀) = σ 𝟘 from rfl, powZ_succ, powZ_zero, one_mul]

-- ─────────────────────────────────────────────────────────────────────────────
-- Lemas para Racionales (Rationals)
-- ─────────────────────────────────────────────────────────────────────────────

theorem eq_ofNat_toNat_abs_or_neg (a : ℤ₀cls) :
  a = ofNat (toNat (abs a)) ∨ a = Neg.neg (ofNat (toNat (abs a))) := by
  have habs : abs a = ofNat (toNat (abs a)) := nonneg_eq_ofNat (abs_nonneg a)
  by_cases h : (0 : ℤ₀cls) ≤ a
  · have haa : abs a = a := by unfold abs; rw [if_pos h]
    exact Or.inl (haa.symm.trans habs)
  · have haa : abs a = -a := by unfold abs; rw [if_neg h]
    have hkey : -a = ofNat (toNat (abs a)) := haa.symm.trans habs
    have hkey2 : a = - (ofNat (toNat (abs a))) := by
      calc a = - (-a) := (neg_neg a).symm
           _ = - (ofNat (toNat (abs a))) := by rw [hkey]
    exact Or.inr hkey2

theorem ofNat_eq_neg_ofNat_implies_zero (A C : ℕ₀) (h : ofNat A = - ofNat C) : A = 𝟘 ∧ C = 𝟘 := by
  have h_add : Add.add (ofNat A) (ofNat C) = 0 := by
    rw [h, neg_add_self]
  rw [← ofNat_add] at h_add
  have h_add2 : add A C = 𝟘 := ofNat_injective h_add
  cases A with
  | zero => 
    rw [Peano.Add.zero_add] at h_add2
    exact ⟨rfl, h_add2⟩
  | succ a' => 
    exfalso
    rw [succ_add] at h_add2
    exact succ_neq_zero (add a' C) h_add2

theorem peano_bound_eq (a c : ℤ₀cls) (b d : ℕ₁)
    (h : Mul.mul a (ℤ₀cls.ofNat d.val) = Mul.mul c (ℤ₀cls.ofNat b.val)) :
    div (ℤ₀cls.toNat (ℤ₀cls.abs a)) b.val = div (ℤ₀cls.toNat (ℤ₀cls.abs c)) d.val := by
  have ha := eq_ofNat_toNat_abs_or_neg a
  have hc := eq_ofNat_toNat_abs_or_neg c
  cases ha with
  | inl ha_pos =>
    cases hc with
    | inl hc_pos =>
      rw [ha_pos, hc_pos] at h
      rw [← ofNat_mul, ← ofNat_mul] at h
      have h_nat : mul (toNat (abs a)) d.val = mul (toNat (abs c)) b.val := ofNat_injective h
      exact div_eq_of_mul_eq (toNat (abs a)) b.val (toNat (abs c)) d.val b.property d.property h_nat
    | inr hc_neg =>
      rw [ha_pos, hc_neg] at h
      rw [← ofNat_mul, neg_mul, ← ofNat_mul] at h
      have h_zero := ofNat_eq_neg_ofNat_implies_zero (mul (toNat (abs a)) d.val) (mul (toNat (abs c)) b.val) h
      have hAd : mul (toNat (abs a)) d.val = 𝟘 := h_zero.1
      have hA : toNat (abs a) = 𝟘 := (mul_eq_zero (toNat (abs a)) d.val).mp hAd |>.resolve_right d.property
      have hCb : mul (toNat (abs c)) b.val = 𝟘 := h_zero.2
      have hC : toNat (abs c) = 𝟘 := (mul_eq_zero (toNat (abs c)) b.val).mp hCb |>.resolve_right b.property
      rw [hA, hC]
      have h_zero_mul : mul 𝟘 d.val = mul 𝟘 b.val := by rw [Peano.Mul.zero_mul, Peano.Mul.zero_mul]
      exact div_eq_of_mul_eq 𝟘 b.val 𝟘 d.val b.property d.property h_zero_mul
  | inr ha_neg =>
    cases hc with
    | inl hc_pos =>
      rw [ha_neg, hc_pos] at h
      rw [neg_mul, ← ofNat_mul, ← ofNat_mul] at h
      have h_symm : ofNat (mul (toNat (abs c)) b.val) = - ofNat (mul (toNat (abs a)) d.val) := h.symm
      have h_zero := ofNat_eq_neg_ofNat_implies_zero (mul (toNat (abs c)) b.val) (mul (toNat (abs a)) d.val) h_symm
      have hCb : mul (toNat (abs c)) b.val = 𝟘 := h_zero.1
      have hC : toNat (abs c) = 𝟘 := (mul_eq_zero (toNat (abs c)) b.val).mp hCb |>.resolve_right b.property
      have hAd : mul (toNat (abs a)) d.val = 𝟘 := h_zero.2
      have hA : toNat (abs a) = 𝟘 := (mul_eq_zero (toNat (abs a)) d.val).mp hAd |>.resolve_right d.property
      rw [hA, hC]
      have h_zero_mul : mul 𝟘 d.val = mul 𝟘 b.val := by rw [Peano.Mul.zero_mul, Peano.Mul.zero_mul]
      exact div_eq_of_mul_eq 𝟘 b.val 𝟘 d.val b.property d.property h_zero_mul
    | inr hc_neg =>
      rw [ha_neg, hc_neg] at h
      rw [neg_mul, ← ofNat_mul, neg_mul, ← ofNat_mul] at h
      have h_pos : ofNat (mul (toNat (abs a)) d.val) = ofNat (mul (toNat (abs c)) b.val) := by
        calc ofNat (mul (toNat (abs a)) d.val) = - (- ofNat (mul (toNat (abs a)) d.val)) := (neg_neg _).symm
             _ = - (- ofNat (mul (toNat (abs c)) b.val)) := by rw [h]
             _ = ofNat (mul (toNat (abs c)) b.val) := neg_neg _
      have h_nat : mul (toNat (abs a)) d.val = mul (toNat (abs c)) b.val := ofNat_injective h_pos
      exact div_eq_of_mul_eq (toNat (abs a)) b.val (toNat (abs c)) d.val b.property d.property h_nat

end ℤ₀cls
