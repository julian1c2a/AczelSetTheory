/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- AczelSetTheory/Integers/HFIntOps.lean
--
-- Operaciones analíticas y aritméticas sobre HFInt (wrapper estructurado).
-- Eleva las funciones de ℤ₀ (sign, abs, toNat, succZ, predZ, powZ, divZ, modZ,
-- gcdZ, lcmZ, isPrimeZ, bezoutCoeffs) al tipo HFInt.

import AczelSetTheory.Integers.HFInt
import AczelSetTheory.Integers.Functions
import AczelSetTheory.Integers.Arithmetic
import AczelSetTheory.Integers.Bezout

namespace HFInt

open Peano

-- ─────────────────────────────────────────────────────────────────────────────
-- Funciones Básicas (de Functions.lean)
-- ─────────────────────────────────────────────────────────────────────────────

/-- Signo de z: 1 si z > 0, −1 si z < 0, 0 si z = 0. -/
def sign (a : HFInt) : HFInt := ofZ0 (ℤ₀.sign a.cls)

/-- Valor absoluto: a si a ≥ 0, −a si a < 0. -/
def abs (a : HFInt) : HFInt := ofZ0 (ℤ₀.abs a.cls)

/-- Parte positiva del representante canónico (cero si z ≤ 0). -/
def toNat (a : HFInt) : ℕ₀ := ℤ₀.toNat a.cls

/-- Sucesor entero: a + 1. -/
def succ (a : HFInt) : HFInt := ofZ0 (ℤ₀.succZ a.cls)

/-- Predecesor entero: a − 1. -/
def pred (a : HFInt) : HFInt := ofZ0 (ℤ₀.predZ a.cls)

/-- Potencia entera: a^n para n : ℕ₀. -/
def pow (a : HFInt) (n : ℕ₀) : HFInt := ofZ0 (ℤ₀.powZ a.cls n)

-- Lemas básicos elevados
theorem sign_zero : sign 0 = 0 := by
  apply ext; exact ℤ₀.sign_zero

theorem sign_ofNat (n : ℕ₀) (hn : n ≠ 𝟘) : sign (ofNat n) = 1 := by
  apply ext; exact ℤ₀.sign_ofNat n hn

theorem sign_neg (a : HFInt) (ha : a < 0) : sign a = -1 := by
  apply ext; exact ℤ₀.sign_neg a.cls ha

theorem abs_ofNat (n : ℕ₀) : abs (ofNat n) = ofNat n := by
  apply ext; exact ℤ₀.abs_ofNat n

theorem abs_nonneg (a : HFInt) : 0 ≤ abs a :=
  ℤ₀.abs_nonneg a.cls

theorem abs_neg (a : HFInt) : abs (-a) = abs a := by
  apply ext; exact ℤ₀.abs_neg a.cls

theorem toNat_ofNat (n : ℕ₀) : toNat (ofNat n) = n :=
  ℤ₀.toNat_ofNat n

theorem toNat_neg (n : ℕ₀) : toNat (- ofNat n) = 𝟘 :=
  ℤ₀.toNat_neg n

theorem succ_pred (a : HFInt) : pred (succ a) = a := by
  apply ext; exact ℤ₀.succZ_pred a.cls

theorem pred_succ (a : HFInt) : succ (pred a) = a := by
  apply ext; exact ℤ₀.predZ_succ a.cls

theorem pow_zero (a : HFInt) : pow a 𝟘 = 1 := by
  apply ext; exact ℤ₀.powZ_zero a.cls

theorem pow_succ (a : HFInt) (n : ℕ₀) : pow a (σ n) = Mul.mul (pow a n) a := by
  apply ext; exact ℤ₀.powZ_succ a.cls n

theorem pow_one (a : HFInt) : pow a 𝟙 = a := by
  apply ext; exact ℤ₀.powZ_one a.cls

-- ─────────────────────────────────────────────────────────────────────────────
-- Aritmética (de Arithmetic.lean)
-- ─────────────────────────────────────────────────────────────────────────────

/-- División entera de a entre b (truncada hacia cero). -/
def div (a b : HFInt) : HFInt := ofZ0 (ℤ₀.divZ a.cls b.cls)

/-- Resto de la división entera. -/
def mod (a b : HFInt) : HFInt := ofZ0 (ℤ₀.modZ a.cls b.cls)

/-- Máximo común divisor de enteros (siempre ≥ 0). -/
def gcd (a b : HFInt) : HFInt := ofZ0 (ℤ₀.gcdZ a.cls b.cls)

/-- Máximo común divisor de entero y natural. -/
def gcdNatRight (a : HFInt) (b : ℕ₀) : HFInt := gcd a (ofNat b)

/-- Máximo común divisor de natural y entero. -/
def gcdNatLeft (a : ℕ₀) (b : HFInt) : HFInt := gcd (ofNat a) b

/-- Mínimo común múltiplo de enteros (siempre ≥ 0). -/
def lcm (a b : HFInt) : HFInt := ofZ0 (ℤ₀.lcmZ a.cls b.cls)

/-- Mínimo común múltiplo de entero y natural. -/
def lcmNatRight (a : HFInt) (b : ℕ₀) : HFInt := lcm a (ofNat b)

/-- Mínimo común múltiplo de natural y entero. -/
def lcmNatLeft (a : ℕ₀) (b : HFInt) : HFInt := lcm (ofNat a) b

/-- Un entero es primo si su parte positiva es un primo natural. -/
def isPrime (a : HFInt) : Prop := ℤ₀.isPrimeZ a.cls

-- Lemas aritméticos elevados
theorem div_zero_right (a : HFInt) : div a 0 = 0 := by
  apply ext; exact ℤ₀.divZ_zero_right a.cls

theorem div_zero_left (b : HFInt) : div 0 b = 0 := by
  apply ext; exact ℤ₀.divZ_zero_left b.cls

theorem gcd_comm (a b : HFInt) : gcd a b = gcd b a := by
  apply ext; exact ℤ₀.gcdZ_comm a.cls b.cls

theorem gcd_ofNat (m n : ℕ₀) : gcd (ofNat m) (ofNat n) = ofNat (Peano.Arith.gcd m n) := by
  apply ext; exact ℤ₀.gcdZ_ofNat m n

theorem gcd_zero_right (n : ℕ₀) : gcd (ofNat n) 0 = ofNat n := by
  apply ext; exact ℤ₀.gcdZ_zero_right n

theorem gcd_zero_left (n : ℕ₀) : gcd 0 (ofNat n) = ofNat n := by
  apply ext; exact ℤ₀.gcdZ_zero_left n

theorem lcm_comm (a b : HFInt) : lcm a b = lcm b a := by
  apply ext; exact ℤ₀.lcmZ_comm a.cls b.cls

theorem lcm_ofNat (m n : ℕ₀) : lcm (ofNat m) (ofNat n) = ofNat (Peano.Arith.lcm m n) := by
  apply ext; exact ℤ₀.lcmZ_ofNat m n

theorem isPrime_ofNat (n : ℕ₀) : isPrime (ofNat n) ↔ Peano.Arith.Prime n :=
  ℤ₀.isPrimeZ_ofNat n

-- ─────────────────────────────────────────────────────────────────────────────
-- Identidad de Bézout (de Bezout.lean)
-- ─────────────────────────────────────────────────────────────────────────────

/-- Coeficientes de Bézout para enteros HFInt. -/
def bezoutCoeffs (a b : HFInt) : HFInt × HFInt :=
  let p := ℤ₀.bezoutCoeffs a.cls b.cls
  (ofZ0 p.1, ofZ0 p.2)

/-- Coeficientes de Bézout de entero y natural. -/
def bezoutCoeffsNatRight (a : HFInt) (b : ℕ₀) : HFInt × HFInt :=
  bezoutCoeffs a (ofNat b)

/-- Coeficientes de Bézout de natural y entero. -/
def bezoutCoeffsNatLeft (a : ℕ₀) (b : HFInt) : HFInt × HFInt :=
  bezoutCoeffs (ofNat a) b

/-- Identidad de Bézout para enteros: a·x + b·y = gcd a b. -/
theorem bezout (a b : HFInt) : ∃ x y : HFInt, Add.add (Mul.mul a x) (Mul.mul b y) = gcd a b := by
  obtain ⟨x, y, hxy⟩ := ℤ₀.bezout a.cls b.cls
  exact ⟨ofZ0 x, ofZ0 y, by apply ext; exact hxy⟩

/-- Si gcd a b = 1, existen x, y tales que a·x + b·y = 1. -/
theorem bezout_coprime {a b : HFInt} (h : gcd a b = 1) : ∃ x y : HFInt, Add.add (Mul.mul a x) (Mul.mul b y) = 1 := by
  have h_cls : ℤ₀.gcdZ a.cls b.cls = 1 := by
    change (gcd a b).cls = (1 : HFInt).cls
    rw [h]
  obtain ⟨x, y, hxy⟩ := ℤ₀.bezout_coprime h_cls
  exact ⟨ofZ0 x, ofZ0 y, by apply ext; exact hxy⟩

end HFInt
