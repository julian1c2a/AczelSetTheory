/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- AczelSetTheory/Rationals.lean
-- Barrel del subsistema ℚ₀ (números racionales), par de `Integers.lean` y `Reals.lean`.
-- ℚ₀ se construye como cociente de `ℤ₀ × ℕ₁` (ℕ₁ = positivos de peanolib, ADR-019).
-- Cadena: peanolib → … → Integers (ℤ₀) → Rationals (ℚ₀) → Reals (ℝ₀).

import AczelSetTheory.Rationals.Basic
import AczelSetTheory.Rationals.AbsVal
import AczelSetTheory.Rationals.IsCauchy
import AczelSetTheory.Rationals.Density
