/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- AczelSetTheory/Rationals/RationalLog.lean
-- Logaritmo de un racional `r > 0` como sucesión de Cauchy de ℚ₀, por la serie
-- del `artanh` con reducción de argumento:
--
--   ln r = ln n + 2·Σ_{k≥0} u^(2k+1)/(2k+1),   u = (r-n)/(r+n),   n ∈ ℕ elegido.
--
-- Si `|u| ≤ 1/2` (garantizado eligiendo `n ≈ r`), las sumas parciales cumplen la
-- cota diádica directamente y `isCauchy_of_dyadic_step` da Cauchy.
--
-- ESTADO: base (definiciones + puente `(1/2)^m = 1/2^m` + cota geométrica).
--
-- Dependencies: Rationals.PowOrder, Rationals.Bisection, Rationals.Inv
-- @axiom_system: ZF (sin elección)
-- @importance: high

import AczelSetTheory.Rationals.PowOrder
import AczelSetTheory.Rationals.Bisection
import AczelSetTheory.Rationals.Inv

namespace ℚ₀

-- ============================================================
-- Sección 1: Puente entre pow2 y pow (1/2)
-- ============================================================

/-- `1/2^0 = 1`. -/
theorem pow2_zero : pow2 𝟘 = 1 := by
  show mk (ℤ₀.ofNat (σ 𝟘)) (pow2_den 𝟘) = 1
  have hden : pow2_den 𝟘 = den1 := by
    apply Subtype.ext
    show Peano.Pow.pow (σ (σ 𝟘)) 𝟘 = 𝟙
    rfl
  rw [hden]
  rfl

/-- `(1/2)^m = 1/2^m`. -/
theorem pow_pow2_one (m : ℕ₀) : pow (pow2 𝟙) m = pow2 m := by
  induction m with
  | zero => rw [pow_zero, pow2_zero]
  | succ k ih =>
    rw [pow_succ, ih]
    show Mul.mul (pow2 𝟙) (pow2 k) = pow2 (σ k)
    rw [← pow2_add]
    congr 1
    show Peano.Add.add 𝟙 k = σ k
    rw [show (𝟙 : ℕ₀) = σ 𝟘 from rfl, Peano.Add.succ_add, Peano.Add.zero_add]

-- ============================================================
-- Sección 2: Cota geométrica de las potencias de |u| ≤ 1/2
-- ============================================================

/-- Si `|u| ≤ 1/2`, entonces `|u|^m ≤ 1/2^m` para todo `m`. -/
theorem pow_absVal_le_pow2 {u : ℚ₀} (hu : absVal u ≤ pow2 𝟙) (m : ℕ₀) :
    pow (absVal u) m ≤ pow2 m := by
  have h := pow_le_pow_left (absVal_nonneg u) hu m
  rwa [pow_pow2_one] at h

-- ============================================================
-- Sección 3: Serie del artanh (definiciones)
-- ============================================================

/-- Exponente/denominador `2j+1` del `j`-ésimo término de la serie del artanh. -/
def oddIdx (j : ℕ₀) : ℕ₀ := σ (Peano.Mul.mul (σ (σ 𝟘)) j)

/-- `j`-ésimo término de la serie del artanh: `u^(2j+1)/(2j+1)`. -/
def artanhTerm (u : ℚ₀) (j : ℕ₀) : ℚ₀ :=
  Mul.mul (pow u (oddIdx j)) (inv (ofNat₀ (oddIdx j)))

/-- Sumas parciales de `Σ_{j=0}^{k} u^(2j+1)/(2j+1)`. -/
def artanhSeq (u : ℚ₀) : ℕ₀ → ℚ₀
  | 𝟘 => artanhTerm u 𝟘
  | σ k => Add.add (artanhSeq u k) (artanhTerm u (σ k))

end ℚ₀
