/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- AczelSetTheory/Integers/ZModN.lean
-- Anillos cociente ℤ₀/nℤ₀ y campo ℤ₀/pℤ₀ para p primo.
--
-- ESTADO: esqueleto creado en FASE B / M5B (2026-06-05). Cuerpo a desarrollar.
--
-- API planificada (ver PLANNING-FASE-B.md §4.5):
--   ZModN n             : Type                   -- cociente por nℤ₀
--   ZModN.mk            : ℤ₀ → ZModN n
--   instAddZModN, instMulZModN, instNegZModN, instZeroZModN, instOneZModN
--   ZModN.ringStructure : IsCommRing (ZModN n)
--   ZModN.inv           : Prime p → ZModN p → ZModN p     -- vía bezout (M5B.0)
--   ZModN.fieldStructure: Prime p → IsField (ZModN p)
--
-- Dependencies: AczelSetTheory.Integers.Basic, AczelSetTheory.Integers.Bezout,
--               AczelSetTheory.Algebra.Ring, AczelSetTheory.Algebra.Field
-- @axiom_system: ZF (sin elección)
-- @importance: high

import AczelSetTheory.Integers.Basic
import AczelSetTheory.Integers.Bezout

namespace ℤ₀

-- ============================================================
-- Sección 1: Cociente ℤ₀/nℤ₀
-- ============================================================
-- a desarrollar: M5B introducirá `ZModN n` como Quotient sobre la relación
-- de congruencia mod n.

-- ============================================================
-- Sección 2: Estructura de cuerpo cuando n = p primo
-- ============================================================
-- a desarrollar: M5B usará `bezout` (M5B.0) para construir el inverso
-- multiplicativo de cualquier representante no nulo en ZModN p.

end ℤ₀
