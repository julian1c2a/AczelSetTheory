/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- AczelSetTheory/Rationals.lean
-- Barrel del subsistema ℚ₀cls (números racionales), par de `Integers.lean` y `Reals.lean`.
-- ℚ₀cls se construye como cociente de `ℤ₀cls × ℕ₁` (ℕ₁ = positivos de peanolib, ADR-019).
-- Cadena: peanolib → … → Integers (ℤ₀cls) → Rationals (ℚ₀cls) → Reals (ℝ₀).

import AczelSetTheory.Rationals.Basic
import AczelSetTheory.Rationals.Inv
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
import AczelSetTheory.Rationals.Q0
import AczelSetTheory.Rationals.Q0Ops
import AczelSetTheory.Rationals.MinAdd
import AczelSetTheory.Rationals.Series
import AczelSetTheory.Rationals.Polynomial
import AczelSetTheory.Rationals.Q0Cauchy
import AczelSetTheory.Rationals.Q0CauchyAlgebra
import AczelSetTheory.Rationals.Archimedean
import AczelSetTheory.Rationals.Irrational
