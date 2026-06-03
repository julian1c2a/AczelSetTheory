/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- AczelSetTheory/Integers/Canonical.lean
-- Representante canónico único para ℤ₀: `(0, n)` o `(n, 0)`.
--
-- ESTADO: esqueleto creado en FASE B / M4B (2026-06-05). Cuerpo a desarrollar.
--
-- DECISIÓN: ADR-014 (en preparación) — opción B: NO se introduce un tipo `HFInt`
-- separado; ℤ₀ = Quotient intSetoid se mantiene como único entero, pero se
-- añade un representante canónico único para igualdad decidible eficiente.
--
-- API planificada (ver PLANNING-FASE-B.md §4.4):
--   canonicalRep            : ℕ₀ × ℕ₀ → ℕ₀ × ℕ₀
--   canonicalRep_idempotent : ∀ p, canonicalRep (canonicalRep p) = canonicalRep p
--   canonicalRep_equiv      : ∀ p, intEq p (canonicalRep p)
--   canonicalRep_unique     : ∀ p q, intEq p q → canonicalRep p = canonicalRep q
--   ℤ₀.repr                 : ℤ₀ → ℕ₀ × ℕ₀     (lift de canonicalRep)
--   ℤ₀.mk_repr              : ∀ z, mk (ℤ₀.repr z) = z
--
-- Dependencies: AczelSetTheory.Integers.Basic
-- @axiom_system: ZF (sin elección)
-- @importance: high

import AczelSetTheory.Integers.Basic

namespace ℤ₀

-- ============================================================
-- Sección 1: Función canonicalRep
-- ============================================================
-- a desarrollar: M4B introducirá la definición por casos según `b ≤ a`.

-- ============================================================
-- Sección 2: Lift al cociente
-- ============================================================
-- a desarrollar: M4B definirá `repr` y la sección `mk_repr`.

end ℤ₀
