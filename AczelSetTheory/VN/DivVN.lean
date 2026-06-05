/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- AczelSetTheory/VN/DivVN.lean
-- Transporte de la división euclidiana de Peano a HFSet mediante vN.
--
-- Peano proporciona división y módulo con:
--   div (a b : ℕ₀) : ℕ₀   (cociente)
--   mod (a b : ℕ₀) : ℕ₀   (resto)
-- junto con el teorema de la división: a = q·b + r con r < b (si b ≠ 0).
--
-- Este módulo transpone los resultados a imágenes bajo vN.
-- Los hechos sobre div/mod son directamente ℕ₀ (no necesitan ser
-- convertidos a HFSet), pero se exportan para uniformidad con el resto
-- de la biblioteca VN.
--
-- Contenido:
--   vN_divMod_spec    : b ≠ 𝟘 → vN a = vN (add (mul (div a b) b) (mod a b))
--   div_le_vN_self    : b ≠ 𝟘 → le₀ (div a b) a
--   div_lt_vN_self    : 𝟙 < b → a ≠ 𝟘 → lt₀ (div a b) a
--   mod_lt_vN         : b ≠ 𝟘 → lt₀ (mod a b) b
--   mod_of_lt_vN      : a < b → mod a b = a
--   div_of_lt_vN      : a < b → div a b = 𝟘

import AczelSetTheory.VN.PeanoArith
open Peano

namespace VN

-- ─────────────────────────────────────────────────────────────────
-- Teorema de la división euclidiana transportado vía vN
-- ─────────────────────────────────────────────────────────────────

/-- Algoritmo de la división: si `b ≠ 𝟘`, entonces
    `vN a = vN (add (mul (div a b) b) (mod a b))`. -/
theorem vN_divMod_spec (a b : ℕ₀) (h : b ≠ 𝟘) :
    vN a = vN (add (mul (div a b) b) (mod a b)) := by
  have := divMod_spec a b h
  -- divMod_spec : a = add (mul (divMod a b).1 b) (divMod a b).2
  -- y (divMod a b).1 = div a b, .2 = mod a b por definición
  simp only [div, mod] at *
  exact congrArg vN this

/-- El cociente no excede el dividendo: `b ≠ 𝟘 → le₀ (div a b) a`. -/
theorem div_le_vN_self (a b : ℕ₀) (h : b ≠ 𝟘) : le₀ (div a b) a :=
  div_le_self a b h

/-- El cociente es estrictamente menor que el dividendo si `b > 𝟙` y `a ≠ 𝟘`. -/
theorem div_lt_vN_self (a b : ℕ₀) (h_b : lt₀ 𝟙 b) (h_a : a ≠ 𝟘) : lt₀ (div a b) a :=
  div_lt_self a b h_b h_a

/-- El resto es estrictamente menor que el divisor: `b ≠ 𝟘 → lt₀ (mod a b) b`. -/
theorem mod_lt_vN (a b : ℕ₀) (h : b ≠ 𝟘) : lt₀ (mod a b) b :=
  mod_lt a b h

/-- Si `a < b`, el resto es `a`: `mod a b = a`. -/
theorem mod_of_lt_vN (a b : ℕ₀) (h : lt₀ a b) : mod a b = a :=
  mod_of_lt a b h

/-- Si `a < b`, el cociente es cero: `div a b = 𝟘`. -/
theorem div_of_lt_vN (a b : ℕ₀) (h : lt₀ a b) : div a b = 𝟘 :=
  div_of_lt a b h

end VN
