/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- AczelSetTheory/Algebra/Ring.lean
-- Anillos nativos en HFSet: estructura HFRing y lemas derivados.
--
-- Público:
--   HFRing                    : anillo unitario (no necesariamente commutativo)
--   HFRing.add_zero           : a + 0 = a
--   HFRing.add_neg            : a + (-a) = 0
--   HFRing.toAdditiveHFGroup  : grupo aditivo (ℤ-módulo subyacente)
--   HFRing.neg_neg            : -(-a) = a
--   HFRing.zero_mul           : 0·a = 0
--   HFRing.mul_zero           : a·0 = 0
--   HFRing.neg_mul            : (-a)·b = -(a·b)
--   HFRing.mul_neg            : a·(-b) = -(a·b)

import AczelSetTheory.Algebra.Group

namespace HFAlgebra

-- ─────────────────────────────────────────────────────────────────
-- Estructura principal
-- ─────────────────────────────────────────────────────────────────

/-- Anillo unitario sobre HFSet.
    Grupo aditivo abeliano (axiomas izquierdos + conmutatividad)
    y monoide multiplicativo unitario, con distributividad bilateral. -/
structure HFRing where
  R   : HFSet
  add : HFSet → HFSet → HFSet
  mul : HFSet → HFSet → HFSet
  zero : HFSet
  one  : HFSet
  neg  : HFSet → HFSet
  -- pertenencia
  zero_mem   : zero ∈ R
  one_mem    : one ∈ R
  add_closed : ∀ {a b : HFSet}, a ∈ R → b ∈ R → add a b ∈ R
  mul_closed : ∀ {a b : HFSet}, a ∈ R → b ∈ R → mul a b ∈ R
  neg_closed : ∀ {a : HFSet}, a ∈ R → neg a ∈ R
  -- grupo aditivo abeliano (axiomas izquierdos + comm)
  add_assoc : ∀ {a b c : HFSet}, a ∈ R → b ∈ R → c ∈ R →
                add (add a b) c = add a (add b c)
  add_comm  : ∀ {a b : HFSet}, a ∈ R → b ∈ R → add a b = add b a
  zero_add  : ∀ {a : HFSet}, a ∈ R → add zero a = a
  neg_add   : ∀ {a : HFSet}, a ∈ R → add (neg a) a = zero
  -- monoide multiplicativo unitario
  mul_assoc : ∀ {a b c : HFSet}, a ∈ R → b ∈ R → c ∈ R →
                mul (mul a b) c = mul a (mul b c)
  mul_one   : ∀ {a : HFSet}, a ∈ R → mul a one = a
  one_mul   : ∀ {a : HFSet}, a ∈ R → mul one a = a
  -- distributividad
  left_distrib  : ∀ {a b c : HFSet}, a ∈ R → b ∈ R → c ∈ R →
                    mul a (add b c) = add (mul a b) (mul a c)
  right_distrib : ∀ {a b c : HFSet}, a ∈ R → b ∈ R → c ∈ R →
                    mul (add a b) c = add (mul a c) (mul b c)

namespace HFRing

variable (rng : HFRing)

-- ─────────────────────────────────────────────────────────────────
-- Identidad e inverso derechos (derivados de comm + axiomas izq.)
-- ─────────────────────────────────────────────────────────────────

theorem add_zero {a : HFSet} (ha : a ∈ rng.R) : rng.add a rng.zero = a := by
  rw [rng.add_comm ha rng.zero_mem, rng.zero_add ha]

theorem add_neg {a : HFSet} (ha : a ∈ rng.R) : rng.add a (rng.neg a) = rng.zero := by
  rw [rng.add_comm ha (rng.neg_closed ha), rng.neg_add ha]

-- ─────────────────────────────────────────────────────────────────
-- Grupo aditivo subyacente
-- ─────────────────────────────────────────────────────────────────

/-- El grupo aditivo de `rng`: axiomas mínimos izquierdos verificados. -/
def toAdditiveHFGroup : HFGroup where
  G           := rng.R
  op          := rng.add
  e           := rng.zero
  inv         := rng.neg
  e_mem       := rng.zero_mem
  op_closed   := rng.add_closed
  inv_closed  := rng.neg_closed
  op_assoc    := rng.add_assoc
  op_id_left  := rng.zero_add
  op_inv_left := rng.neg_add

-- ─────────────────────────────────────────────────────────────────
-- Doble negación
-- ─────────────────────────────────────────────────────────────────

theorem neg_neg {a : HFSet} (ha : a ∈ rng.R) : rng.neg (rng.neg a) = a :=
  rng.toAdditiveHFGroup.inv_inv ha

-- ─────────────────────────────────────────────────────────────────
-- Anulación por cero: 0·a = 0
-- ─────────────────────────────────────────────────────────────────

theorem zero_mul {a : HFSet} (ha : a ∈ rng.R) : rng.mul rng.zero a = rng.zero := by
  have hx : rng.mul rng.zero a ∈ rng.R := rng.mul_closed rng.zero_mem ha
  -- 0·a + 0·a = (0+0)·a = 0·a
  have hxx : rng.add (rng.mul rng.zero a) (rng.mul rng.zero a) = rng.mul rng.zero a :=
    (rng.right_distrib rng.zero_mem rng.zero_mem ha).symm.trans
      (by rw [rng.zero_add rng.zero_mem])
  -- left_cancel en el grupo aditivo: 0·a + 0·a = 0·a + 0  →  0·a = 0
  apply rng.toAdditiveHFGroup.left_cancel hx hx rng.zero_mem
  show rng.add (rng.mul rng.zero a) (rng.mul rng.zero a) =
       rng.add (rng.mul rng.zero a) rng.zero
  rw [hxx, rng.add_zero hx]

-- ─────────────────────────────────────────────────────────────────
-- Anulación por cero: a·0 = 0
-- ─────────────────────────────────────────────────────────────────

theorem mul_zero {a : HFSet} (ha : a ∈ rng.R) : rng.mul a rng.zero = rng.zero := by
  have hx : rng.mul a rng.zero ∈ rng.R := rng.mul_closed ha rng.zero_mem
  -- a·0 + a·0 = a·(0+0) = a·0
  have hxx : rng.add (rng.mul a rng.zero) (rng.mul a rng.zero) = rng.mul a rng.zero :=
    (rng.left_distrib ha rng.zero_mem rng.zero_mem).symm.trans
      (by rw [rng.zero_add rng.zero_mem])
  apply rng.toAdditiveHFGroup.left_cancel hx hx rng.zero_mem
  show rng.add (rng.mul a rng.zero) (rng.mul a rng.zero) =
       rng.add (rng.mul a rng.zero) rng.zero
  rw [hxx, rng.add_zero hx]

-- ─────────────────────────────────────────────────────────────────
-- Distribución del negativo: (-a)·b = -(a·b)
-- ─────────────────────────────────────────────────────────────────

theorem neg_mul {a b : HFSet} (ha : a ∈ rng.R) (hb : b ∈ rng.R) :
    rng.mul (rng.neg a) b = rng.neg (rng.mul a b) := by
  have hnab : rng.mul (rng.neg a) b ∈ rng.R := rng.mul_closed (rng.neg_closed ha) hb
  have hab  : rng.mul a b ∈ rng.R           := rng.mul_closed ha hb
  -- (-a)·b + a·b = (-a + a)·b = 0·b = 0
  have hkey : rng.add (rng.mul (rng.neg a) b) (rng.mul a b) = rng.zero :=
    calc rng.add (rng.mul (rng.neg a) b) (rng.mul a b)
        = rng.mul (rng.add (rng.neg a) a) b := (rng.right_distrib (rng.neg_closed ha) ha hb).symm
      _ = rng.mul rng.zero b               := by rw [rng.neg_add ha]
      _ = rng.zero                         := rng.zero_mul hb
  exact rng.toAdditiveHFGroup.unique_inv hab hnab hkey

-- ─────────────────────────────────────────────────────────────────
-- Distribución del negativo: a·(-b) = -(a·b)
-- ─────────────────────────────────────────────────────────────────

theorem mul_neg {a b : HFSet} (ha : a ∈ rng.R) (hb : b ∈ rng.R) :
    rng.mul a (rng.neg b) = rng.neg (rng.mul a b) := by
  have hanb : rng.mul a (rng.neg b) ∈ rng.R := rng.mul_closed ha (rng.neg_closed hb)
  have hab  : rng.mul a b ∈ rng.R           := rng.mul_closed ha hb
  -- a·(-b) + a·b = a·(-b + b) = a·0 = 0
  have hkey : rng.add (rng.mul a (rng.neg b)) (rng.mul a b) = rng.zero :=
    calc rng.add (rng.mul a (rng.neg b)) (rng.mul a b)
        = rng.mul a (rng.add (rng.neg b) b) := (rng.left_distrib ha (rng.neg_closed hb) hb).symm
      _ = rng.mul a rng.zero               := by rw [rng.neg_add hb]
      _ = rng.zero                         := rng.mul_zero ha
  exact rng.toAdditiveHFGroup.unique_inv hab hanb hkey

end HFRing

end HFAlgebra
