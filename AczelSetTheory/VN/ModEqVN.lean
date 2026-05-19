/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- AczelSetTheory/VN/ModEqVN.lean
-- Transporte de propiedades del módulo y congruencia modular de Peano a HFSet vía vN.
--
-- Contenido:
--   ModEq_HF         : HFSet → HFSet → HFSet → Prop   (a ≡ b [MODHF n])
--   vN_modEq_iff     : vN a ≡ vN b [MODHF vN n] ↔ ModEq n a b
--   vN_modEq_refl    : a ≡ a [MODHF n]
--   vN_modEq_symm    : a ≡ b → b ≡ a
--   vN_modEq_trans   : transitivity
--   vN_modEq_add     : congruencias compatibles con suma
--   vN_modEq_mul     : congruencias compatibles con producto
--   vN_modEq_pow     : congruencias compatibles con potencia
--   vN_mod_eq_zero_iff_dvd : mod a n = 0 ↔ n ∣ a  (en HFSet)
--   vN_modEq_mod     : a ≡ mod a n [MOD n]
--   vN_modEq_one     : todo a ≡ b [MOD 1]
--   vN_modEq_add_right : a ≡ a + n [MOD n]

import AczelSetTheory.VN.PeanoArith
import AczelSetTheory.VN.CardVN
import Peano.PeanoNat.NumberTheory.ModEq

open Peano Peano.ModEq

namespace VN

-- ─────────────────────────────────────────────────────────────────
-- Propiedades del módulo (valores ℕ₀ → HFSet)
-- ─────────────────────────────────────────────────────────────────

theorem vN_mod_zero_right (a : ℕ₀) : vN (mod a 𝟘) = vN 𝟘 :=
  congrArg vN (mod_zero_right a)

theorem vN_mod_zero_left (n : ℕ₀) : vN (mod 𝟘 n) = vN 𝟘 :=
  congrArg vN (mod_zero_left n)

theorem vN_mod_self (n : ℕ₀) : vN (mod n n) = vN 𝟘 :=
  congrArg vN (mod_self n)

theorem vN_mod_mod (a n : ℕ₀) : vN (mod (mod a n) n) = vN (mod a n) :=
  congrArg vN (mod_mod a n)

theorem vN_add_mod (a b n : ℕ₀) :
    vN (mod (add a b) n) = vN (mod (add (mod a n) (mod b n)) n) :=
  congrArg vN (add_mod a b n)

theorem vN_mul_mod (a b n : ℕ₀) :
    vN (mod (mul a b) n) = vN (mod (mul (mod a n) (mod b n)) n) :=
  congrArg vN (mul_mod a b n)

-- ─────────────────────────────────────────────────────────────────
-- Congruencia modular en HFSet
-- ─────────────────────────────────────────────────────────────────

/-- Congruencia modular en HFSet: `a ≡ b (mod n)`, definida vía `card`.
    Los tres argumentos deben ser naturales de Von Neumann. -/
def ModEq_HF (n a b : HFSet) : Prop :=
  HFSet.isNat n ∧ HFSet.isNat a ∧ HFSet.isNat b ∧
  Peano.ModEq.ModEq (HFSet.card n) (HFSet.card a) (HFSet.card b)

notation:50 a " ≡ₕ " b " [MODHF " n "]" => ModEq_HF n a b

/-- Conexión: congruencia HFSet en `vN n`, `vN a`, `vN b` ↔ congruencia Peano. -/
theorem vN_modEq_iff {n a b : ℕ₀} :
    vN a ≡ₕ vN b [MODHF vN n] ↔ Peano.ModEq.ModEq n a b := by
  simp [ModEq_HF, isNat_vN, card_vN]

-- ─────────────────────────────────────────────────────────────────
-- Congruencia como relación de equivalencia
-- ─────────────────────────────────────────────────────────────────

theorem vN_modEq_refl (n a : ℕ₀) : vN a ≡ₕ vN a [MODHF vN n] :=
  vN_modEq_iff.mpr (modEq_refl n a)

theorem vN_modEq_symm {n a b : ℕ₀} (h : vN a ≡ₕ vN b [MODHF vN n]) :
    vN b ≡ₕ vN a [MODHF vN n] :=
  vN_modEq_iff.mpr (modEq_symm (vN_modEq_iff.mp h))

theorem vN_modEq_trans {n a b c : ℕ₀}
    (h1 : vN a ≡ₕ vN b [MODHF vN n]) (h2 : vN b ≡ₕ vN c [MODHF vN n]) :
    vN a ≡ₕ vN c [MODHF vN n] :=
  vN_modEq_iff.mpr (modEq_trans (vN_modEq_iff.mp h1) (vN_modEq_iff.mp h2))

-- ─────────────────────────────────────────────────────────────────
-- Compatibilidad con operaciones
-- ─────────────────────────────────────────────────────────────────

theorem vN_modEq_add {n a b c d : ℕ₀}
    (h1 : vN a ≡ₕ vN b [MODHF vN n]) (h2 : vN c ≡ₕ vN d [MODHF vN n]) :
    vN (add a c) ≡ₕ vN (add b d) [MODHF vN n] :=
  vN_modEq_iff.mpr (modEq_add (vN_modEq_iff.mp h1) (vN_modEq_iff.mp h2))

theorem vN_modEq_mul {n a b c d : ℕ₀}
    (h1 : vN a ≡ₕ vN b [MODHF vN n]) (h2 : vN c ≡ₕ vN d [MODHF vN n]) :
    vN (mul a c) ≡ₕ vN (mul b d) [MODHF vN n] :=
  vN_modEq_iff.mpr (modEq_mul (vN_modEq_iff.mp h1) (vN_modEq_iff.mp h2))

theorem vN_modEq_pow {n a b : ℕ₀} (k : ℕ₀)
    (h : vN a ≡ₕ vN b [MODHF vN n]) :
    vN (pow a k) ≡ₕ vN (pow b k) [MODHF vN n] :=
  vN_modEq_iff.mpr (modEq_pow k (vN_modEq_iff.mp h))

-- ─────────────────────────────────────────────────────────────────
-- Relación con divisibilidad
-- ─────────────────────────────────────────────────────────────────

theorem vN_mod_eq_zero_iff_dvd {a n : ℕ₀} (hn : n ≠ 𝟘) :
    vN (mod a n) = vN 𝟘 ↔ n ∣ a := by
  constructor
  · intro h; exact (mod_eq_zero_iff_dvd hn).mp (vN_injective h)
  · intro h; exact congrArg vN ((mod_eq_zero_iff_dvd hn).mpr h)

-- ─────────────────────────────────────────────────────────────────
-- Lemas adicionales
-- ─────────────────────────────────────────────────────────────────

theorem vN_modEq_mod (a n : ℕ₀) : vN a ≡ₕ vN (mod a n) [MODHF vN n] :=
  vN_modEq_iff.mpr (modEq_mod a n)

theorem vN_modEq_one (a b : ℕ₀) : vN a ≡ₕ vN b [MODHF vN 𝟙] :=
  vN_modEq_iff.mpr (modEq_one a b)

theorem vN_modEq_add_right (a n : ℕ₀) : vN a ≡ₕ vN (add a n) [MODHF vN n] :=
  vN_modEq_iff.mpr (modEq_add_right a n)

end VN
