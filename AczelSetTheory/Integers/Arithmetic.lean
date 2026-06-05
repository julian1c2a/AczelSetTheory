/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- AczelSetTheory/Integers/Arithmetic.lean
-- Aritmética entera: división, módulo, gcd, lcm, primalidad.
--
-- Público:
--   ℤ₀.divZ     : ℤ₀ → ℤ₀ → ℤ₀   (división truncada hacia cero)
--   ℤ₀.modZ     : ℤ₀ → ℤ₀ → ℤ₀   (resto T-división)
--   ℤ₀.gcdZ     : ℤ₀ → ℤ₀ → ℤ₀   (GCD, siempre ≥ 0)
--   ℤ₀.lcmZ     : ℤ₀ → ℤ₀ → ℤ₀   (LCM, siempre ≥ 0)
--   ℤ₀.isPrimeZ : ℤ₀ → Prop
--   Lemas: divZ_zero_right, divZ_zero_left
--          gcdZ_comm, gcdZ_ofNat, gcdZ_zero_right, gcdZ_zero_left
--          lcmZ_comm, lcmZ_ofNat
--          isPrimeZ_ofNat

import AczelSetTheory.Integers.Functions
import Peano.PeanoNat.Div
import Peano.PeanoNat.Arith

namespace ℤ₀

open Peano Peano.Add Peano.Sub Peano.Mul

-- ─────────────────────────────────────────────────────────────────────────────
-- divZ / modZ
-- ─────────────────────────────────────────────────────────────────────────────

/-- División entera de a entre b (truncada hacia cero). -/
def divZ (a b : ℤ₀) : ℤ₀ :=
  Mul.mul (Mul.mul (sign a) (sign b))
          (ofNat (Peano.Div.div (toNat (abs a)) (toNat (abs b))))

/-- Resto de la división entera (relación: a = divZ a b * b + modZ a b). -/
def modZ (a b : ℤ₀) : ℤ₀ :=
  Add.add a (Neg.neg (Mul.mul (divZ a b) b))

theorem divZ_zero_right (z : ℤ₀) : divZ z 0 = 0 := by
  simp only [divZ, sign_zero, mul_zero, zero_mul]

theorem divZ_zero_left (b : ℤ₀) : divZ 0 b = 0 := by
  simp only [divZ, sign_zero, zero_mul]

-- ─────────────────────────────────────────────────────────────────────────────
-- gcdZ
-- ─────────────────────────────────────────────────────────────────────────────

/-- Máximo común divisor de enteros (siempre ≥ 0, definido sobre valores absolutos). -/
def gcdZ (a b : ℤ₀) : ℤ₀ :=
  ofNat (Peano.Arith.gcd (toNat (abs a)) (toNat (abs b)))

theorem gcdZ_comm (a b : ℤ₀) : gcdZ a b = gcdZ b a := by
  simp only [gcdZ, Peano.Arith.gcd_comm]

theorem gcdZ_ofNat (m n : ℕ₀) :
    gcdZ (ofNat m) (ofNat n) = ofNat (Peano.Arith.gcd m n) := by
  simp [gcdZ, abs_ofNat, toNat_ofNat]

theorem gcdZ_zero_right (n : ℕ₀) : gcdZ (ofNat n) 0 = ofNat n := by
  have h0 : (0 : ℤ₀) = ofNat 𝟘 := rfl
  rw [h0, gcdZ_ofNat, Peano.Arith.gcd_zero_right]

theorem gcdZ_zero_left (n : ℕ₀) : gcdZ 0 (ofNat n) = ofNat n := by
  have h0 : (0 : ℤ₀) = ofNat 𝟘 := rfl
  rw [h0, gcdZ_ofNat, Peano.Arith.gcd_zero_left]

-- ─────────────────────────────────────────────────────────────────────────────
-- lcmZ
-- ─────────────────────────────────────────────────────────────────────────────

/-- Mínimo común múltiplo de enteros (siempre ≥ 0, definido sobre valores absolutos). -/
def lcmZ (a b : ℤ₀) : ℤ₀ :=
  ofNat (Peano.Arith.lcm (toNat (abs a)) (toNat (abs b)))

theorem lcmZ_comm (a b : ℤ₀) : lcmZ a b = lcmZ b a := by
  simp only [lcmZ, Peano.Arith.lcm_comm]

theorem lcmZ_ofNat (m n : ℕ₀) :
    lcmZ (ofNat m) (ofNat n) = ofNat (Peano.Arith.lcm m n) := by
  simp [lcmZ, abs_ofNat, toNat_ofNat]

-- ─────────────────────────────────────────────────────────────────────────────
-- isPrimeZ
-- ─────────────────────────────────────────────────────────────────────────────

/-- Un entero es primo si su parte positiva es un primo natural. -/
def isPrimeZ (z : ℤ₀) : Prop := Peano.Arith.Prime (toNat z)

theorem isPrimeZ_ofNat (n : ℕ₀) : isPrimeZ (ofNat n) ↔ Peano.Arith.Prime n := by
  simp [isPrimeZ, toNat_ofNat]

end ℤ₀
