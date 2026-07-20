/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- AczelSetTheory/Integers/Z0NumberTheory.lean
-- Paridad del entero empaquetado ℤ₀ con la teoría de números de ℤ₀cls:
-- Möbius/Liouville (MobiusLiouville.lean), la biyección ℤ₀ ≃ ℕ₀ (Bijection.lean) y los dos
-- lemas de valor absoluto que faltaban de Functions.lean. Todo son bridges triviales sobre
-- ℤ₀cls (ADR-023, migración de tipos): las funciones se definen como `ofCls (ℤ₀cls.f …)`, así
-- que `.cls` conmuta por `rfl`, y con `@[ext]` cada hecho de la clase pasa al struct en 1 línea.

import AczelSetTheory.Integers.Z0Ops
import AczelSetTheory.Integers.MobiusLiouville
import AczelSetTheory.Integers.Bijection

open Peano

namespace ℤ₀

-- ─────────────────────────────────────────────────────────────────────────────
-- Completar Functions: |z| = 0 ↔ z = 0 y la descomposición ±|z|
-- ─────────────────────────────────────────────────────────────────────────────

theorem abs_eq_zero_iff {z : ℤ₀} : abs z = 0 ↔ z = 0 :=
  ⟨fun h => ext z 0 (ℤ₀cls.abs_eq_zero_iff.mp (congrArg ℤ₀.cls h)),
   fun h => ext _ _ (ℤ₀cls.abs_eq_zero_iff.mpr (congrArg ℤ₀.cls h))⟩

theorem eq_ofNat_toNat_abs_or_neg (a : ℤ₀) :
    a = ofNat (toNat (abs a)) ∨ a = Neg.neg (ofNat (toNat (abs a))) := by
  rcases ℤ₀cls.eq_ofNat_toNat_abs_or_neg a.cls with h | h
  · exact Or.inl (ext _ _ h)
  · exact Or.inr (ext _ _ h)

-- ─────────────────────────────────────────────────────────────────────────────
-- Möbius y Liouville (ℕ₀ → ℤ₀)
-- ─────────────────────────────────────────────────────────────────────────────

/-- Potencia de −1 sobre el entero empaquetado: `(-1)^k`. -/
def negOnePow (k : ℕ₀) : ℤ₀ := ofCls (ℤ₀cls.negOnePow k)

/-- Función de Möbius con valores en `ℤ₀`. -/
def mobius (n : ℕ₀) : ℤ₀ := ofCls (ℤ₀cls.mobius n)

/-- Función de Liouville con valores en `ℤ₀`. -/
def liouville (n : ℕ₀) : ℤ₀ := ofCls (ℤ₀cls.liouville n)

@[simp] theorem cls_negOnePow (k : ℕ₀) : (negOnePow k).cls = ℤ₀cls.negOnePow k := rfl
@[simp] theorem cls_mobius (n : ℕ₀)    : (mobius n).cls   = ℤ₀cls.mobius n := rfl
@[simp] theorem cls_liouville (n : ℕ₀) : (liouville n).cls = ℤ₀cls.liouville n := rfl

theorem negOnePow_zero : negOnePow 𝟘 = 1 := ext _ _ ℤ₀cls.negOnePow_zero
theorem negOnePow_succ (k : ℕ₀) : negOnePow (σ k) = Neg.neg (negOnePow k) :=
  ext _ _ (ℤ₀cls.negOnePow_succ k)
theorem negOnePow_one : negOnePow 𝟙 = negOne := ext _ _ ℤ₀cls.negOnePow_one
theorem negOnePow_two : negOnePow 𝟚 = 1 := ext _ _ ℤ₀cls.negOnePow_two
theorem negOnePow_add (a b : ℕ₀) :
    negOnePow (Peano.Add.add a b) = Mul.mul (negOnePow a) (negOnePow b) :=
  ext _ _ (ℤ₀cls.negOnePow_add a b)
theorem negOnePow_mul_self (k : ℕ₀) : Mul.mul (negOnePow k) (negOnePow k) = 1 :=
  ext _ _ (ℤ₀cls.negOnePow_mul_self k)

theorem mobius_one : mobius 𝟙 = 1 := ext _ _ ℤ₀cls.mobius_one
theorem mobius_prime {p : ℕ₀} (hp : Peano.Arith.Prime p) : mobius p = negOne :=
  ext _ _ (ℤ₀cls.mobius_prime hp)
theorem mobius_prime_sq {p : ℕ₀} (hp : Peano.Arith.Prime p) :
    mobius (Peano.Mul.mul p p) = 0 := ext _ _ (ℤ₀cls.mobius_prime_sq hp)

theorem liouville_one : liouville 𝟙 = 1 := ext _ _ ℤ₀cls.liouville_one
theorem liouville_prime {p : ℕ₀} (hp : Peano.Arith.Prime p) : liouville p = negOne :=
  ext _ _ (ℤ₀cls.liouville_prime hp)
theorem liouville_sq (n : ℕ₀) : Mul.mul (liouville n) (liouville n) = 1 :=
  ext _ _ (ℤ₀cls.liouville_sq n)
theorem liouville_ne_zero (n : ℕ₀) : liouville n ≠ 0 :=
  ne_zero_iff_cls.mpr (ℤ₀cls.liouville_ne_zero n)
theorem mobius_eq_liouville_of_squarefree {n : ℕ₀} (h : squarefree n) :
    mobius n = liouville n := ext _ _ (ℤ₀cls.mobius_eq_liouville_of_squarefree h)
theorem liouville_mul {m n : ℕ₀} (hm : m ≠ 𝟘) (hn : n ≠ 𝟘) :
    liouville (Peano.Mul.mul m n) = Mul.mul (liouville m) (liouville n) :=
  ext _ _ (ℤ₀cls.liouville_mul hm hn)
theorem liouville_prime_pow {p k : ℕ₀} (hp : Peano.Arith.Prime p) :
    liouville (Peano.Pow.pow p k) = negOnePow k :=
  ext _ _ (ℤ₀cls.liouville_prime_pow hp)

-- ─────────────────────────────────────────────────────────────────────────────
-- Biyección ℤ₀ ≃ ℕ₀ (codificación de Cantor sobre el representante)
-- ─────────────────────────────────────────────────────────────────────────────

/-- Codifica un entero empaquetado como natural. -/
def encode (z : ℤ₀) : ℕ₀ := ℤ₀cls.encode z.cls

/-- Decodifica un natural a entero empaquetado. -/
def decode (n : ℕ₀) : ℤ₀ := ofCls (ℤ₀cls.decode n)

@[simp] theorem encode_eq (z : ℤ₀) : encode z = ℤ₀cls.encode z.cls := rfl
@[simp] theorem cls_decode (n : ℕ₀) : (decode n).cls = ℤ₀cls.decode n := rfl

theorem decode_encode (z : ℤ₀) : decode (encode z) = z :=
  ext _ _ (ℤ₀cls.decode_encode z.cls)
theorem encode_injective {a b : ℤ₀} (h : encode a = encode b) : a = b :=
  ext a b (ℤ₀cls.encode_injective h)

end ℤ₀
