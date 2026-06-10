/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- AczelSetTheory/Rationals/Density.lean
-- Densidad de ℚ₀ en sí mismo (entre dos racionales hay un tercero).
--
-- ESTADO: esqueleto creado en FASE B / M2B (2026-06-05). Cuerpo a desarrollar.
--
-- API planificada (ver PLANNING-FASE-B.md §4.2):
--   midpoint        : ℚ₀ → ℚ₀ → ℚ₀
--   lt_midpoint     : a < b → a < midpoint a b
--   midpoint_lt     : a < b → midpoint a b < b
--   exists_between  : a < b → ∃ c : ℚ₀, a < c ∧ c < b
--
-- Dependencies: AczelSetTheory.Rationals.Basic, AczelSetTheory.Rationals.AbsVal
-- @axiom_system: ZF (sin elección)
-- @importance: high

import AczelSetTheory.Rationals.Basic
import AczelSetTheory.Rationals.AbsVal

namespace ℚ₀

-- ============================================================
-- Sección 1: Punto medio y densidad
-- ============================================================
-- a desarrollar: M2B introducirá `midpoint`, `exists_between` y compañía.

end ℚ₀
