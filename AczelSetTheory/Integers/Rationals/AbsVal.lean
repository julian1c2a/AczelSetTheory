/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- AczelSetTheory/Integers/Rationals/AbsVal.lean
-- Valor absoluto sobre ℚ₀ y propiedades básicas (M2B, parcial).
--
-- API entregada:
--   absVal              : ℚ₀ → ℚ₀
--   absVal_zero         : absVal 0 = 0
--   absVal_of_nonneg    : 0 ≤ q → absVal q = q
--   absVal_of_nonpos    : q ≤ 0 → absVal q = -q
--   absVal_nonneg       : 0 ≤ absVal q
--   absVal_neg          : absVal (-q) = absVal q
--   absVal_zero_iff     : absVal q = 0 ↔ q = 0
--   absVal_idempotent   : absVal (absVal q) = absVal q
--   absVal_sub_comm     : absVal (a - b) = absVal (b - a)
--   absVal_mul          : absVal (a * b) = absVal a * absVal b
--   absVal_add_le       : absVal (a + b) ≤ absVal a + absVal b   (triangular)
--
-- Dependencies: AczelSetTheory.Integers.Rationals
-- @axiom_system: ZF (sin elección)
-- @importance: high

import AczelSetTheory.Integers.Rationals

namespace ℚ₀

-- ============================================================
-- Sección 1: Definición de valor absoluto
-- ============================================================

/-- Valor absoluto en ℚ₀: `q` si `0 ≤ q`, `-q` en caso contrario. Computable
gracias a `instDecidableLE`. -/
def absVal (q : ℚ₀) : ℚ₀ := if 0 ≤ q then q else -q

-- ============================================================
-- Sección 2: Propiedades de casos
-- ============================================================

theorem absVal_of_nonneg {q : ℚ₀} (h : 0 ≤ q) : absVal q = q := by
  simp [absVal, h]

theorem absVal_of_nonpos {q : ℚ₀} (h : q ≤ 0) : absVal q = -q := by
  by_cases hpos : (0 : ℚ₀) ≤ q
  · -- q = 0
    have hzero : q = 0 := le_antisymm h hpos
    rw [absVal, if_pos hpos, hzero, neg_zero]
  · simp [absVal, hpos]

theorem absVal_zero : absVal (0 : ℚ₀) = 0 := by
  rw [absVal_of_nonneg (le_refl 0)]

-- ============================================================
-- Sección 3: No-negatividad e idempotencia
-- ============================================================

theorem absVal_nonneg (q : ℚ₀) : 0 ≤ absVal q := by
  by_cases h : (0 : ℚ₀) ≤ q
  · rw [absVal_of_nonneg h]; exact h
  · -- ¬(0 ≤ q) ⇒ q ≤ 0 (por totalidad), luego absVal q = -q ≥ 0
    have hle : q ≤ 0 := (le_total 0 q).resolve_left h
    rw [absVal_of_nonpos hle]
    -- 0 ≤ -q  ⟺  -0 ≤ -q  (ya que neg_zero), y neg_le_neg de q ≤ 0 da -0 ≤ -q.
    have := neg_le_neg hle
    rwa [neg_zero] at this

theorem absVal_idempotent (q : ℚ₀) : absVal (absVal q) = absVal q :=
  absVal_of_nonneg (absVal_nonneg q)

-- ============================================================
-- Sección 4: Simetría bajo negación
-- ============================================================

theorem absVal_neg (q : ℚ₀) : absVal (Neg.neg q) = absVal q := by
  by_cases hq : (0 : ℚ₀) ≤ q
  · -- q ≥ 0 ⇒ -q ≤ 0
    have hnq : Neg.neg q ≤ 0 := by
      have := neg_le_neg hq
      rwa [neg_zero] at this
    rw [absVal_of_nonneg hq, absVal_of_nonpos hnq, neg_neg]
  · -- ¬(0 ≤ q) ⇒ q ≤ 0, y -q ≥ 0
    have hqle : q ≤ 0 := (le_total 0 q).resolve_left hq
    have hnq : 0 ≤ Neg.neg q := by
      have := neg_le_neg hqle
      rwa [neg_zero] at this
    rw [absVal_of_nonpos hqle, absVal_of_nonneg hnq]

-- ============================================================
-- Sección 5: Caracterización del cero
-- ============================================================

theorem absVal_zero_iff (q : ℚ₀) : absVal q = 0 ↔ q = 0 := by
  refine ⟨fun h => ?_, fun h => h ▸ absVal_zero⟩
  by_cases hq : (0 : ℚ₀) ≤ q
  · -- absVal q = q, luego q = 0
    rw [absVal_of_nonneg hq] at h; exact h
  · -- ¬(0 ≤ q), q ≤ 0, absVal q = -q = 0 ⇒ -(-q) = -0 ⇒ q = 0
    have hqle : q ≤ 0 := (le_total 0 q).resolve_left hq
    rw [absVal_of_nonpos hqle] at h
    have : Neg.neg (Neg.neg q) = Neg.neg 0 := congrArg Neg.neg h
    rw [neg_neg, neg_zero] at this
    exact this

-- ============================================================
-- Sección 6: Sub-conmutatividad, producto y desigualdad triangular
-- ============================================================

theorem absVal_sub_comm (a b : ℚ₀) : absVal (a - b) = absVal (b - a) := by
  have hkey : Neg.neg (b + Neg.neg a) = a + Neg.neg b := by
    have h1 : Neg.neg (b + Neg.neg a) = Neg.neg b + Neg.neg (Neg.neg a) :=
      neg_add b (Neg.neg a)
    have h2 : Neg.neg (Neg.neg a) = a := neg_neg a
    rw [h1, h2]
    exact add_comm (Neg.neg b) a
  have hsc : absVal (a - b) = absVal (Neg.neg (b - a)) := by
    show absVal (a + Neg.neg b) = absVal (Neg.neg (b + Neg.neg a))
    congr 1
    exact hkey.symm
  rw [hsc, absVal_neg]

theorem absVal_mul (a b : ℚ₀) : absVal (a * b) = absVal a * absVal b := by
  rcases le_total 0 a with ha | ha <;> rcases le_total 0 b with hb | hb
  · -- 0 ≤ a, 0 ≤ b
    have hab : 0 ≤ a * b := mul_nonneg ha hb
    rw [absVal_of_nonneg hab, absVal_of_nonneg ha, absVal_of_nonneg hb]
  · -- 0 ≤ a, b ≤ 0
    have hab : a * b ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ha hb
    rw [absVal_of_nonpos hab, absVal_of_nonneg ha, absVal_of_nonpos hb, mul_neg]
  · -- a ≤ 0, 0 ≤ b
    have hab : a * b ≤ 0 := by
      rw [mul_comm]; exact mul_nonpos_of_nonneg_of_nonpos hb ha
    rw [absVal_of_nonpos hab, absVal_of_nonpos ha, absVal_of_nonneg hb, neg_mul]
  · -- a ≤ 0, b ≤ 0
    have hab : 0 ≤ a * b := mul_nonneg_of_nonpos_of_nonpos ha hb
    rw [absVal_of_nonneg hab, absVal_of_nonpos ha, absVal_of_nonpos hb,
        neg_mul, mul_neg, neg_neg]

end ℚ₀

-- ============================================================
-- Sección 3: le_absVal y absVal_add_le
-- Dentro del namespace ℚ₀ la notación + resuelve a ℚ₀.instAdd
-- (backtracking desde la notación global de Peano). Los helpers
-- q0_add_le_add_* del nivel raíz ya no son necesarios.
-- ============================================================

namespace ℚ₀

private theorem le_absVal (q : ℚ₀) : q ≤ absVal q := by
  by_cases h : (0 : ℚ₀) ≤ q
  · rw [absVal_of_nonneg h]; exact le_refl q
  · have hle : q ≤ 0 := (le_total 0 q).resolve_left h
    rw [absVal_of_nonpos hle]
    have h0nq : (0 : ℚ₀) ≤ -q := by
      have := neg_le_neg hle; rwa [neg_zero] at this
    exact le_trans hle h0nq

theorem absVal_add_le (a b : ℚ₀) :
    absVal (a + b) ≤ absVal a + absVal b := by
  by_cases h : (0 : ℚ₀) ≤ a + b
  · rw [absVal_of_nonneg h]
    exact le_trans
      (add_le_add_left (le_absVal b) a)
      (add_le_add_right (le_absVal a) (absVal b))
  · have hle := (le_total (0 : ℚ₀) _).resolve_left h
    rw [absVal_of_nonpos hle]
    have h1 : -a ≤ absVal a := by
      have h' := le_absVal (-a); rwa [absVal_neg] at h'
    have h2 : -b ≤ absVal b := by
      have h' := le_absVal (-b); rwa [absVal_neg] at h'
    -- -(a+b) es definitionally Neg.neg (Add.add a b); evitar notación + en calc
    have hstep : Neg.neg (Add.add a b) = Add.add (Neg.neg a) (Neg.neg b) := neg_add a b
    exact le_trans (hstep ▸ le_refl _)
      (le_trans (add_le_add_right h1 _) (add_le_add_left h2 _))

end ℚ₀
