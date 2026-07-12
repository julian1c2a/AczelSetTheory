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
import AczelSetTheory.Rationals.CauchySeqAlgebra
import AczelSetTheory.Rationals.Canonical
import AczelSetTheory.Rationals.Convergence
import AczelSetTheory.Rationals.Bisection
import AczelSetTheory.Rationals.Roots
import AczelSetTheory.Rationals.PowOrder
import AczelSetTheory.Rationals.RationalLog
import AczelSetTheory.Rationals.HFRat
import AczelSetTheory.Rationals.MinAdd
import AczelSetTheory.Rationals.Series
import AczelSetTheory.Rationals.Polynomial
import AczelSetTheory.Rationals.HFRatCauchy
import AczelSetTheory.Rationals.HFRatCauchyAlgebra
import AczelSetTheory.Rationals.Archimedean
import AczelSetTheory.Rationals.Irrational
