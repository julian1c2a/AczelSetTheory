/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- AczelSetTheory/Integers/Z0Ops.lean
--
-- Operaciones analíticas y aritméticas sobre ℤ₀ (wrapper estructurado).
-- Eleva las funciones de ℤ₀cls (sign, abs, toNat, succZ, predZ, powZ, divZ, modZ,
-- gcdZ, lcmZ, isPrimeZ, bezoutCoeffs) al tipo ℤ₀.

import AczelSetTheory.Integers.Z0
import AczelSetTheory.Integers.Functions
import AczelSetTheory.Integers.Arithmetic
import AczelSetTheory.Integers.Bezout

namespace ℤ₀

open Peano

-- ─────────────────────────────────────────────────────────────────────────────
-- Funciones Básicas (de Functions.lean)
-- ─────────────────────────────────────────────────────────────────────────────

/-- Signo de z: 1 si z > 0, −1 si z < 0, 0 si z = 0. -/
def sign (a : ℤ₀) : ℤ₀ := ofCls (ℤ₀cls.sign a.cls)

/-- Valor absoluto: a si a ≥ 0, −a si a < 0. -/
def abs (a : ℤ₀) : ℤ₀ := ofCls (ℤ₀cls.abs a.cls)

/-- Parte positiva del representante canónico (cero si z ≤ 0). -/
def toNat (a : ℤ₀) : ℕ₀ := ℤ₀cls.toNat a.cls

/-- Sucesor entero: a + 1. -/
def succ (a : ℤ₀) : ℤ₀ := ofCls (ℤ₀cls.succZ a.cls)

/-- Predecesor entero: a − 1. -/
def pred (a : ℤ₀) : ℤ₀ := ofCls (ℤ₀cls.predZ a.cls)

/-- Potencia entera: a^n para n : ℕ₀. -/
def pow (a : ℤ₀) (n : ℕ₀) : ℤ₀ := ofCls (ℤ₀cls.powZ a.cls n)

-- Lemas básicos elevados
theorem sign_zero : sign 0 = 0 := by
  apply ext; exact ℤ₀cls.sign_zero

theorem sign_ofNat (n : ℕ₀) (hn : n ≠ 𝟘) : sign (ofNat n) = 1 := by
  apply ext; exact ℤ₀cls.sign_ofNat n hn

theorem sign_neg (a : ℤ₀) (ha : a < 0) : sign a = -1 := by
  apply ext; exact ℤ₀cls.sign_neg a.cls ha

theorem abs_ofNat (n : ℕ₀) : abs (ofNat n) = ofNat n := by
  apply ext; exact ℤ₀cls.abs_ofNat n

theorem abs_nonneg (a : ℤ₀) : 0 ≤ abs a :=
  ℤ₀cls.abs_nonneg a.cls

theorem abs_neg (a : ℤ₀) : abs (-a) = abs a := by
  apply ext; exact ℤ₀cls.abs_neg a.cls

theorem toNat_ofNat (n : ℕ₀) : toNat (ofNat n) = n :=
  ℤ₀cls.toNat_ofNat n

theorem toNat_neg (n : ℕ₀) : toNat (- ofNat n) = 𝟘 :=
  ℤ₀cls.toNat_neg n

theorem succ_pred (a : ℤ₀) : pred (succ a) = a := by
  apply ext; exact ℤ₀cls.succZ_pred a.cls

theorem pred_succ (a : ℤ₀) : succ (pred a) = a := by
  apply ext; exact ℤ₀cls.predZ_succ a.cls

theorem pow_zero (a : ℤ₀) : pow a 𝟘 = 1 := by
  apply ext; exact ℤ₀cls.powZ_zero a.cls

theorem pow_succ (a : ℤ₀) (n : ℕ₀) : pow a (σ n) = Mul.mul (pow a n) a := by
  apply ext; exact ℤ₀cls.powZ_succ a.cls n

theorem pow_one (a : ℤ₀) : pow a 𝟙 = a := by
  apply ext; exact ℤ₀cls.powZ_one a.cls

-- ─────────────────────────────────────────────────────────────────────────────
-- Aritmética (de Arithmetic.lean)
-- ─────────────────────────────────────────────────────────────────────────────

/-- División entera de a entre b (truncada hacia cero). -/
def div (a b : ℤ₀) : ℤ₀ := ofCls (ℤ₀cls.divZ a.cls b.cls)

/-- Resto de la división entera. -/
def mod (a b : ℤ₀) : ℤ₀ := ofCls (ℤ₀cls.modZ a.cls b.cls)

/-- Máximo común divisor de enteros (siempre ≥ 0). -/
def gcd (a b : ℤ₀) : ℤ₀ := ofCls (ℤ₀cls.gcdZ a.cls b.cls)

/-- Máximo común divisor de entero y natural. -/
def gcdNatRight (a : ℤ₀) (b : ℕ₀) : ℤ₀ := gcd a (ofNat b)

/-- Máximo común divisor de natural y entero. -/
def gcdNatLeft (a : ℕ₀) (b : ℤ₀) : ℤ₀ := gcd (ofNat a) b

/-- Mínimo común múltiplo de enteros (siempre ≥ 0). -/
def lcm (a b : ℤ₀) : ℤ₀ := ofCls (ℤ₀cls.lcmZ a.cls b.cls)

/-- Mínimo común múltiplo de entero y natural. -/
def lcmNatRight (a : ℤ₀) (b : ℕ₀) : ℤ₀ := lcm a (ofNat b)

/-- Mínimo común múltiplo de natural y entero. -/
def lcmNatLeft (a : ℕ₀) (b : ℤ₀) : ℤ₀ := lcm (ofNat a) b

/-- Un entero es primo si su parte positiva es un primo natural. -/
def isPrime (a : ℤ₀) : Prop := ℤ₀cls.isPrimeZ a.cls

-- Lemas aritméticos elevados
theorem div_zero_right (a : ℤ₀) : div a 0 = 0 := by
  apply ext; exact ℤ₀cls.divZ_zero_right a.cls

theorem div_zero_left (b : ℤ₀) : div 0 b = 0 := by
  apply ext; exact ℤ₀cls.divZ_zero_left b.cls

theorem gcd_comm (a b : ℤ₀) : gcd a b = gcd b a := by
  apply ext; exact ℤ₀cls.gcdZ_comm a.cls b.cls

theorem gcd_ofNat (m n : ℕ₀) : gcd (ofNat m) (ofNat n) = ofNat (Peano.Arith.gcd m n) := by
  apply ext; exact ℤ₀cls.gcdZ_ofNat m n

theorem gcd_zero_right (n : ℕ₀) : gcd (ofNat n) 0 = ofNat n := by
  apply ext; exact ℤ₀cls.gcdZ_zero_right n

theorem gcd_zero_left (n : ℕ₀) : gcd 0 (ofNat n) = ofNat n := by
  apply ext; exact ℤ₀cls.gcdZ_zero_left n

theorem lcm_comm (a b : ℤ₀) : lcm a b = lcm b a := by
  apply ext; exact ℤ₀cls.lcmZ_comm a.cls b.cls

theorem lcm_ofNat (m n : ℕ₀) : lcm (ofNat m) (ofNat n) = ofNat (Peano.Arith.lcm m n) := by
  apply ext; exact ℤ₀cls.lcmZ_ofNat m n

theorem isPrime_ofNat (n : ℕ₀) : isPrime (ofNat n) ↔ Peano.Arith.Prime n :=
  ℤ₀cls.isPrimeZ_ofNat n

-- ─────────────────────────────────────────────────────────────────────────────
-- Identidad de Bézout (de Bezout.lean)
-- ─────────────────────────────────────────────────────────────────────────────

/-- Coeficientes de Bézout para enteros ℤ₀. -/
def bezoutCoeffs (a b : ℤ₀) : ℤ₀ × ℤ₀ :=
  let p := ℤ₀cls.bezoutCoeffs a.cls b.cls
  (ofCls p.1, ofCls p.2)

/-- Coeficientes de Bézout de entero y natural. -/
def bezoutCoeffsNatRight (a : ℤ₀) (b : ℕ₀) : ℤ₀ × ℤ₀ :=
  bezoutCoeffs a (ofNat b)

/-- Coeficientes de Bézout de natural y entero. -/
def bezoutCoeffsNatLeft (a : ℕ₀) (b : ℤ₀) : ℤ₀ × ℤ₀ :=
  bezoutCoeffs (ofNat a) b

/-- Identidad de Bézout para enteros: a·x + b·y = gcd a b. -/
theorem bezout (a b : ℤ₀) : ∃ x y : ℤ₀, Add.add (Mul.mul a x) (Mul.mul b y) = gcd a b := by
  obtain ⟨x, y, hxy⟩ := ℤ₀cls.bezout a.cls b.cls
  exact ⟨ofCls x, ofCls y, by apply ext; exact hxy⟩

/-- Si gcd a b = 1, existen x, y tales que a·x + b·y = 1. -/
theorem bezout_coprime {a b : ℤ₀} (h : gcd a b = 1) : ∃ x y : ℤ₀, Add.add (Mul.mul a x) (Mul.mul b y) = 1 := by
  have h_cls : ℤ₀cls.gcdZ a.cls b.cls = 1 := by
    change (gcd a b).cls = (1 : ℤ₀).cls
    rw [h]
  obtain ⟨x, y, hxy⟩ := ℤ₀cls.bezout_coprime h_cls
  exact ⟨ofCls x, ofCls y, by apply ext; exact hxy⟩

end ℤ₀
