/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- AczelSetTheory/VN/PowVN.lean
-- Transporte de la potenciación de Peano a HFSet mediante vN.
--
-- Contenido:
--   powVN                      : ℕ₀ → ℕ₀ → HFSet   (imagen directa de vN)
--   powVN_def                  : powVN m n = vN (m ^ n)
--   powVN_zero                 : powVN m 𝟘 = vN 𝟙
--   powVN_succ                 : powVN m (σ n) = vN (mul (m ^ n) m)
--   vN_pow                     : vN (m ^ n) = powVN m n
--   vN_pow_zero                : vN (m ^ 𝟘) = vN 𝟙
--   vN_pow_succ                : vN (m ^ σ n) = vN (mul (m ^ n) m)
--   vN_pow_one                 : vN (m ^ 𝟙) = vN m
--   vN_one_pow                 : vN (𝟙 ^ n) = vN 𝟙
--   vN_zero_pow                : n ≠ 𝟘 → vN (𝟘 ^ n) = vN 𝟘
--   vN_pow_add                 : vN (m ^ add n k) = vN (mul (m ^ n) (m ^ k))
--   vN_mul_pow                 : vN (mul (m ^ k) (n ^ k)) = vN ((mul m n) ^ k)
--   vN_pow_pow                 : vN ((m ^ n) ^ k) = vN (m ^ mul n k)
--   vN_pow_two                 : vN (m ^ 𝟚) = vN (mul m m)
--   vN_pow_ne_zero             : m ≠ 𝟘 → vN (m ^ n) ≠ vN 𝟘

import AczelSetTheory.VN.PeanoArith

open Peano

namespace VN

-- ─────────────────────────────────────────────────────────────────
-- Potenciación set-teorética: imagen de vN en la potenciación Peano
-- ─────────────────────────────────────────────────────────────────

/-- Potenciación set-teorética: imagen directa de la potenciación de Peano
    bajo el embedding de Von Neumann.

    `powVN m n = vN (m ^ n)` -/
def powVN (m n : ℕ₀) : HFSet := vN (m ^ n)

@[simp]
theorem powVN_def (m n : ℕ₀) : powVN m n = vN (m ^ n) := rfl

@[simp]
theorem powVN_zero (m : ℕ₀) : powVN m 𝟘 = vN 𝟙 := by
  simp [powVN, pow_zero]

@[simp]
theorem powVN_succ (m n : ℕ₀) : powVN m (σ n) = vN (mul (m ^ n) m) := by
  simp [powVN, pow_succ]

-- ─────────────────────────────────────────────────────────────────
-- Transporte principal
-- ─────────────────────────────────────────────────────────────────

/-- Transporte: la potenciación de Peano coincide con `powVN` bajo `vN`. -/
theorem vN_pow (m n : ℕ₀) : vN (m ^ n) = powVN m n := rfl

-- ─────────────────────────────────────────────────────────────────
-- Ecuaciones definitionales transportadas
-- ─────────────────────────────────────────────────────────────────

/-- Caso base: `vN (m ^ 𝟘) = vN 𝟙`. -/
theorem vN_pow_zero (m : ℕ₀) : vN (m ^ 𝟘) = vN 𝟙 :=
  congrArg vN (pow_zero m)

/-- Caso sucesor: `vN (m ^ σ n) = vN (mul (m ^ n) m)`. -/
theorem vN_pow_succ (m n : ℕ₀) : vN (m ^ σ n) = vN (mul (m ^ n) m) :=
  congrArg vN (pow_succ m n)

-- ─────────────────────────────────────────────────────────────────
-- Leyes de la potenciación transportadas vía vN
-- ─────────────────────────────────────────────────────────────────

/-- Elemento neutro a la derecha: `vN (m ^ 𝟙) = vN m`. -/
theorem vN_pow_one (m : ℕ₀) : vN (m ^ 𝟙) = vN m :=
  congrArg vN (pow_one m)

/-- Potencia de uno: `vN (𝟙 ^ n) = vN 𝟙`. -/
theorem vN_one_pow (n : ℕ₀) : vN (𝟙 ^ n) = vN 𝟙 :=
  congrArg vN (one_pow n)

/-- Potencia de cero (exponente no nulo): `vN (𝟘 ^ n) = vN 𝟘`. -/
theorem vN_zero_pow {n : ℕ₀} (h : n ≠ 𝟘) : vN (𝟘 ^ n) = vN 𝟘 :=
  congrArg vN (zero_pow h)

/-- Distributividad de la potenciación sobre la adición del exponente:
    `vN (m ^ add n k) = vN (mul (m ^ n) (m ^ k))`. -/
theorem vN_pow_add (m n k : ℕ₀) :
    vN (m ^ add n k) = vN (mul (m ^ n) (m ^ k)) :=
  congrArg vN (pow_add_eq_mul_pow m n k)

/-- Distributividad de la potenciación sobre el producto de la base:
    `vN (mul (m ^ k) (n ^ k)) = vN ((mul m n) ^ k)`. -/
theorem vN_mul_pow (m n k : ℕ₀) :
    vN (mul (m ^ k) (n ^ k)) = vN ((mul m n) ^ k) :=
  congrArg vN (mul_pow_n_m_pow_k_m_eq_pow_nk_m m n k)

/-- Potencia de potencia: `vN ((m ^ n) ^ k) = vN (m ^ mul n k)`. -/
theorem vN_pow_pow (m n k : ℕ₀) :
    vN ((m ^ n) ^ k) = vN (m ^ mul n k) :=
  congrArg vN (pow_pow_eq_pow_mul m n k)

/-- Cuadrado: `vN (m ^ 𝟚) = vN (mul m m)`. -/
theorem vN_pow_two (m : ℕ₀) : vN (m ^ 𝟚) = vN (mul m m) :=
  congrArg vN (pow_two m)

/-- Potencia de no-cero: si `m ≠ 𝟘` entonces `vN (m ^ n) ≠ vN 𝟘`. -/
theorem vN_pow_ne_zero {m : ℕ₀} (h : m ≠ 𝟘) (n : ℕ₀) :
    vN (m ^ n) ≠ vN 𝟘 := by
  intro heq
  have : m ^ n = 𝟘 := vN_injective heq
  exact pow_ne_zero h n this

end VN
