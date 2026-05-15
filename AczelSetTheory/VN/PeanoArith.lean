/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- AczelSetTheory/VN/PeanoArith.lean
-- Transporte de la aritmética de Peano a HFSet mediante vN.
--
-- Define la adición set-teorética addVN como iteración de HFSet.succ,
-- prueba su equivalencia con la adición de Peano, y exporta las leyes
-- algebraicas transportadas vía vN.
--
-- Contenido:
--   addVN             : HFSet → ℕ₀ → HFSet   (iteración de succ)
--   addVN_zero        : addVN A 𝟘 = A
--   addVN_succ        : addVN A (σ n) = HFSet.succ (addVN A n)
--   vN_add            : vN (add m n) = addVN (vN m) n
--   vN_add_comm       : vN (add m n) = vN (add n m)
--   vN_add_assoc      : vN (add (add m n) k) = vN (add m (add n k))
--   vN_add_zero       : vN (add m 𝟘) = vN m
--   vN_zero_add       : vN (add 𝟘 m) = vN m
--   vN_mul_comm       : vN (mul m n) = vN (mul n m)
--   vN_mul_assoc      : vN (mul (mul m n) k) = vN (mul m (mul n k))
--   vN_mul_zero       : vN (mul m 𝟘) = vN 𝟘
--   vN_zero_mul       : vN (mul 𝟘 m) = vN 𝟘
--   vN_mul_one        : vN (mul m 𝟙) = vN m
--   vN_one_mul        : vN (mul 𝟙 m) = vN m
--   vN_mul_add        : vN (mul m (add n k)) = vN (add (mul m n) (mul m k))
--   vN_add_mul        : vN (mul (add m n) k) = vN (add (mul m k) (mul n k))

import AczelSetTheory.VN.Arithmetic
import AczelSetTheory.VN.PeanoAxioms

open Peano

namespace VN

-- ─────────────────────────────────────────────────────────────────
-- Adición set-teorética: iterar HFSet.succ n veces desde A
-- ─────────────────────────────────────────────────────────────────

/-- Adición set-teorética: aplica `HFSet.succ` exactamente `n` veces a `A`. -/
def addVN (A : HFSet) : ℕ₀ → HFSet
  | .zero   => A
  | .succ n => HFSet.succ (addVN A n)

@[simp]
theorem addVN_zero (A : HFSet) : addVN A 𝟘 = A := rfl

@[simp]
theorem addVN_succ (A : HFSet) (n : ℕ₀) :
    addVN A (σ n) = HFSet.succ (addVN A n) := rfl

-- ─────────────────────────────────────────────────────────────────
-- Transporte: vN (add m n) = addVN (vN m) n
-- ─────────────────────────────────────────────────────────────────

/-- El transporte central: la adición de Peano corresponde a
    iterar `HFSet.succ` en la imagen de `vN`. -/
theorem vN_add (m n : ℕ₀) : vN (add m n) = addVN (vN m) n := by
  induction n with
  | zero    => simp [add_zero]
  | succ k ih => simp [add_succ, vN_succ, ih]

-- ─────────────────────────────────────────────────────────────────
-- Leyes de la adición transportadas vía vN
-- ─────────────────────────────────────────────────────────────────

/-- Conmutatividad de la adición: `vN (m + n) = vN (n + m)`. -/
theorem vN_add_comm (m n : ℕ₀) : vN (add m n) = vN (add n m) :=
  congrArg vN (add_comm m n)

/-- Asociatividad de la adición. -/
theorem vN_add_assoc (m n k : ℕ₀) :
    vN (add (add m n) k) = vN (add m (add n k)) :=
  congrArg vN (add_assoc m n k).symm

/-- Elemento neutro a la derecha: `vN (m + 𝟘) = vN m`. -/
theorem vN_add_zero (m : ℕ₀) : vN (add m 𝟘) = vN m :=
  congrArg vN (add_zero m)

/-- Elemento neutro a la izquierda: `vN (𝟘 + m) = vN m`. -/
theorem vN_zero_add (m : ℕ₀) : vN (add 𝟘 m) = vN m :=
  congrArg vN (zero_add m)

-- ─────────────────────────────────────────────────────────────────
-- Leyes de la multiplicación transportadas vía vN
-- ─────────────────────────────────────────────────────────────────

/-- Conmutatividad de la multiplicación. -/
theorem vN_mul_comm (m n : ℕ₀) : vN (mul m n) = vN (mul n m) :=
  congrArg vN (mul_comm m n)

/-- Asociatividad de la multiplicación. -/
theorem vN_mul_assoc (m n k : ℕ₀) :
    vN (mul (mul m n) k) = vN (mul m (mul n k)) :=
  congrArg vN (mul_assoc n m k)

/-- Aniquilación a la derecha: `vN (m · 𝟘) = vN 𝟘`. -/
theorem vN_mul_zero (m : ℕ₀) : vN (mul m 𝟘) = vN 𝟘 :=
  congrArg vN (mul_zero m)

/-- Aniquilación a la izquierda: `vN (𝟘 · m) = vN 𝟘`. -/
theorem vN_zero_mul (m : ℕ₀) : vN (mul 𝟘 m) = vN 𝟘 :=
  congrArg vN (zero_mul m)

/-- Elemento neutro a la derecha: `vN (m · 𝟙) = vN m`. -/
theorem vN_mul_one (m : ℕ₀) : vN (mul m 𝟙) = vN m :=
  congrArg vN (mul_one m)

/-- Elemento neutro a la izquierda: `vN (𝟙 · m) = vN m`. -/
theorem vN_one_mul (m : ℕ₀) : vN (mul 𝟙 m) = vN m :=
  congrArg vN (one_mul m)

/-- Distributividad de la multiplicación sobre la adición (izquierda). -/
theorem vN_mul_add (m n k : ℕ₀) :
    vN (mul m (add n k)) = vN (add (mul m n) (mul m k)) :=
  congrArg vN (mul_add m n k)

/-- Distributividad de la multiplicación sobre la adición (derecha). -/
theorem vN_add_mul (m n k : ℕ₀) :
    vN (mul (add m n) k) = vN (add (mul m k) (mul n k)) :=
  congrArg vN (add_mul m n k)

end VN
