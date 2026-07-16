/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- AczelSetTheory/Rationals/Q0CauchyAlgebra.lean
-- Álgebra de sucesiones de Cauchy en ℚ₀ sin usar cocientes.

import AczelSetTheory.Rationals.Q0Cauchy
import AczelSetTheory.Rationals.CauchySeqAlgebra
import AczelSetTheory.Rationals.Q0Ops
import Peano.PeanoNat.Arith

open Peano

namespace ℚ₀

-- ============================================================
-- Relaciones de Equivalencia
-- ============================================================

/-- Equivalencia de Cauchy (límite de la diferencia es 0). -/
def CauchySeq.Equiv (f g : CauchySeq) : Prop :=
  ∀ k : ℕ₀, ∃ N : ℕ₀, ∀ m : ℕ₀, Peano.Order.le₀ N m → absVal (f.val m - g.val m) ≤ pow2 k

/-- Convergencia a un racional exacto. -/
def CauchySeq.ConvergesTo (f : CauchySeq) (q : ℚ₀) : Prop :=
  ∀ k : ℕ₀, ∃ N : ℕ₀, ∀ m : ℕ₀, Peano.Order.le₀ N m → absVal (f.val m - q) ≤ pow2 k

-- ============================================================
-- Puentes con ℚ₀cls.CauchySeq
-- ============================================================

def toClsCauchySeq (f : CauchySeq) : ℚ₀cls.CauchySeq :=
  ⟨toClsSeq f.val, (isCauchy_iff_q0_isCauchy f.val).mp f.property⟩

theorem toClsSeq_add (f g : ℕ₀ → ℚ₀) : 
    toClsSeq (fun n => f n + g n) = fun n => toClsSeq f n + toClsSeq g n := by
  funext n
  rfl

theorem toClsSeq_neg (f : ℕ₀ → ℚ₀) : 
    toClsSeq (fun n => -f n) = fun n => -toClsSeq f n := by
  funext n
  rfl

theorem toClsSeq_sub (f g : ℕ₀ → ℚ₀) : 
    toClsSeq (fun n => f n - g n) = fun n => toClsSeq f n - toClsSeq g n := by
  funext n
  rfl

-- ============================================================
-- Aritmética (Suma, Negación, Resta)
-- ============================================================

def CauchySeq.add (f g : CauchySeq) : CauchySeq :=
  ⟨fun n => f.val (σ n) + g.val (σ n), by
    rw [isCauchy_iff_q0_isCauchy]
    exact (toClsCauchySeq f + toClsCauchySeq g).property⟩

instance : _root_.Add CauchySeq where add := CauchySeq.add

def CauchySeq.neg (f : CauchySeq) : CauchySeq :=
  ⟨fun n => -f.val n, by
    rw [isCauchy_iff_q0_isCauchy]
    exact (-toClsCauchySeq f).property⟩

instance : _root_.Neg CauchySeq where neg := CauchySeq.neg

def CauchySeq.sub (f g : CauchySeq) : CauchySeq :=
  f + (-g)

instance : _root_.Sub CauchySeq where sub := CauchySeq.sub

-- ============================================================
-- Multiplicación
-- ============================================================

def CauchySeq.mulBound (f g : CauchySeq) : ℕ₀ :=
  ℚ₀cls.CauchySeq.mulBound (toClsCauchySeq f) (toClsCauchySeq g)

def CauchySeq.mul (f g : CauchySeq) : CauchySeq :=
  let K := CauchySeq.mulBound f g
  ⟨fun n => f.val (Peano.Add.add n K) * g.val (Peano.Add.add n K), by
    rw [isCauchy_iff_q0_isCauchy]
    exact (toClsCauchySeq f * toClsCauchySeq g).property⟩

instance : _root_.Mul CauchySeq where mul := CauchySeq.mul

-- ============================================================
-- Positividad, Inverso y División
-- ============================================================

structure CauchySeq.Pos (f : CauchySeq) where
  k : ℕ₀
  N : ℕ₀
  proof : ∀ m, Peano.Order.le₀ N m → pow2 k ≤ f.val m

def CauchySeq.ApartZero (f : CauchySeq) : Type :=
  Sum (CauchySeq.Pos f) (CauchySeq.Pos (-f))

def toClsPos {f : CauchySeq} (p : CauchySeq.Pos f) : ℚ₀cls.CauchySeq.Pos (toClsCauchySeq f) :=
  ⟨p.k, p.N, p.proof⟩

def toClsApartZero {f : CauchySeq} (h : CauchySeq.ApartZero f) : ℚ₀cls.CauchySeq.ApartZero (toClsCauchySeq f) :=
  match h with
  | Sum.inl p => Sum.inl (toClsPos p)
  | Sum.inr p => Sum.inr (toClsPos p)

def CauchySeq.invBound (f : CauchySeq) (h : CauchySeq.ApartZero f) : ℕ₀ :=
  ℚ₀cls.CauchySeq.invBound (toClsCauchySeq f) (toClsApartZero h)

def CauchySeq.inv (f : CauchySeq) (h : CauchySeq.ApartZero f) : CauchySeq :=
  let K := CauchySeq.invBound f h
  ⟨fun n => (f.val (Peano.Add.add n K))⁻¹, by
    rw [isCauchy_iff_q0_isCauchy]
    exact (ℚ₀cls.CauchySeq.inv (toClsCauchySeq f) (toClsApartZero h)).property⟩

def CauchySeq.div (f g : CauchySeq) (h : CauchySeq.ApartZero g) : CauchySeq :=
  f * CauchySeq.inv g h

end ℚ₀
