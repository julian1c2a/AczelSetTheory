/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- AczelSetTheory/Reals/IsCauchy.lean
-- Sucesiones de Cauchy en ℚ₀: definición clásica e infraestructura
-- diádica para números computables.
--
-- ESTADO: esqueleto creado en FASE B / M3B (2026-06-05). Cuerpo a desarrollar.
--
-- API planificada (ver PLANNING-FASE-B.md §4.3):
--   IsCauchy        : (ℕ₀ → ℚ₀) → Prop          -- ε > 0 clásico
--   IsCauchy₂       : (ℕ₀ → ℚ₀) → Prop          -- ε = 1/2^δ diádico (canónico computable)
--   pow2            : ℕ₀ → ℕ₀
--   pow2_pos        : ∀ n, 𝟘 < pow2 n
--   pow2_succ       : ∀ n, pow2 (suc n) = mul (suc (suc 𝟘)) (pow2 n)
--   one_div_pow2_pos
--   isCauchy_of_isCauchy₂ : IsCauchy₂ s → IsCauchy s
--   isCauchy₂_of_isCauchy : IsCauchy s → IsCauchy₂ s
--
-- Dependencies: AczelSetTheory.Rationals.Basic, AczelSetTheory.Rationals.AbsVal
-- @axiom_system: ZF (sin elección)
-- @importance: high

import AczelSetTheory.Rationals.Basic
import AczelSetTheory.Rationals.AbsVal

namespace ℝ₀

-- ============================================================
-- Sección 1: ε-Cauchy clásico
-- ============================================================
-- a desarrollar: M3B introducirá `IsCauchy` y lemas estructurales.

-- ============================================================
-- Sección 2: Cauchy diádico (ε = 1/2^δ)
-- ============================================================
-- a desarrollar: M3B introducirá `IsCauchy₂`, `pow2`, equivalencia con `IsCauchy`.

end ℝ₀
