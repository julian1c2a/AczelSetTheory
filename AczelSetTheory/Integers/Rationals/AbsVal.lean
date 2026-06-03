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
--
-- A desarrollar en sesiones futuras (ver §6):
--   absVal_sub_comm, absVal_mul, absVal_add_le (triangular)
--   — requieren `neg_add` en ℤ₀/ℚ₀ y análisis de casos sobre signos.
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
-- Sección 6: A desarrollar en sesiones futuras
-- ============================================================
-- A desarrollar (requieren helpers `neg_add`, `mul_pos_pos`, etc. en ℤ₀/ℚ₀):
--   absVal_sub_comm  : absVal (a - b) = absVal (b - a)
--   absVal_mul       : absVal (a * b) = absVal a * absVal b
--   absVal_add_le    : absVal (a + b) ≤ absVal a + absVal b   (triangular)

end ℚ₀
