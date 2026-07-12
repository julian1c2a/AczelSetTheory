/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- AczelSetTheory/Rationals/HFRatCauchyAlgebra.lean
-- Álgebra de sucesiones de Cauchy en HFRat sin usar cocientes.

import AczelSetTheory.Rationals.HFRatCauchy
import AczelSetTheory.Rationals.CauchySeqAlgebra
import AczelSetTheory.Rationals.HFRatOps
import Peano.PeanoNat.Arith

open Peano

namespace HFRat

-- ============================================================
-- Relaciones de Equivalencia
-- ============================================================

/-- Equivalencia de Cauchy (límite de la diferencia es 0). -/
def CauchySeq.Equiv (f g : CauchySeq) : Prop :=
  ∀ k : ℕ₀, ∃ N : ℕ₀, ∀ m : ℕ₀, Peano.Order.le₀ N m → absVal (f.val m - g.val m) ≤ pow2 k

/-- Convergencia a un racional exacto. -/
def CauchySeq.ConvergesTo (f : CauchySeq) (q : HFRat) : Prop :=
  ∀ k : ℕ₀, ∃ N : ℕ₀, ∀ m : ℕ₀, Peano.Order.le₀ N m → absVal (f.val m - q) ≤ pow2 k

-- ============================================================
-- Puentes con ℚ₀.CauchySeq
-- ============================================================

def toQ0CauchySeq (f : CauchySeq) : ℚ₀.CauchySeq :=
  ⟨toQ0Seq f.val, (isCauchy_iff_q0_isCauchy f.val).mp f.property⟩

theorem toQ0Seq_add (f g : ℕ₀ → HFRat) : 
    toQ0Seq (fun n => f n + g n) = fun n => toQ0Seq f n + toQ0Seq g n := by
  funext n
  rfl

theorem toQ0Seq_neg (f : ℕ₀ → HFRat) : 
    toQ0Seq (fun n => -f n) = fun n => -toQ0Seq f n := by
  funext n
  rfl

theorem toQ0Seq_sub (f g : ℕ₀ → HFRat) : 
    toQ0Seq (fun n => f n - g n) = fun n => toQ0Seq f n - toQ0Seq g n := by
  funext n
  rfl

-- ============================================================
-- Aritmética (Suma, Negación, Resta)
-- ============================================================

def CauchySeq.add (f g : CauchySeq) : CauchySeq :=
  ⟨fun n => f.val (σ n) + g.val (σ n), by
    rw [isCauchy_iff_q0_isCauchy]
    exact (toQ0CauchySeq f + toQ0CauchySeq g).property⟩

instance : _root_.Add CauchySeq where add := CauchySeq.add

def CauchySeq.neg (f : CauchySeq) : CauchySeq :=
  ⟨fun n => -f.val n, by
    rw [isCauchy_iff_q0_isCauchy]
    exact (-toQ0CauchySeq f).property⟩

instance : _root_.Neg CauchySeq where neg := CauchySeq.neg

def CauchySeq.sub (f g : CauchySeq) : CauchySeq :=
  f + (-g)

instance : _root_.Sub CauchySeq where sub := CauchySeq.sub

-- ============================================================
-- Multiplicación
-- ============================================================

def CauchySeq.mulBound (f g : CauchySeq) : ℕ₀ :=
  ℚ₀.CauchySeq.mulBound (toQ0CauchySeq f) (toQ0CauchySeq g)

def CauchySeq.mul (f g : CauchySeq) : CauchySeq :=
  let K := CauchySeq.mulBound f g
  ⟨fun n => f.val (Peano.Add.add n K) * g.val (Peano.Add.add n K), by
    rw [isCauchy_iff_q0_isCauchy]
    exact (toQ0CauchySeq f * toQ0CauchySeq g).property⟩

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

def toQ0Pos {f : CauchySeq} (p : CauchySeq.Pos f) : ℚ₀.CauchySeq.Pos (toQ0CauchySeq f) :=
  ⟨p.k, p.N, p.proof⟩

def toQ0ApartZero {f : CauchySeq} (h : CauchySeq.ApartZero f) : ℚ₀.CauchySeq.ApartZero (toQ0CauchySeq f) :=
  match h with
  | Sum.inl p => Sum.inl (toQ0Pos p)
  | Sum.inr p => Sum.inr (toQ0Pos p)

def CauchySeq.invBound (f : CauchySeq) (h : CauchySeq.ApartZero f) : ℕ₀ :=
  ℚ₀.CauchySeq.invBound (toQ0CauchySeq f) (toQ0ApartZero h)

def CauchySeq.inv (f : CauchySeq) (h : CauchySeq.ApartZero f) : CauchySeq :=
  let K := CauchySeq.invBound f h
  ⟨fun n => (f.val (Peano.Add.add n K))⁻¹, by
    rw [isCauchy_iff_q0_isCauchy]
    exact (ℚ₀.CauchySeq.inv (toQ0CauchySeq f) (toQ0ApartZero h)).property⟩

def CauchySeq.div (f g : CauchySeq) (h : CauchySeq.ApartZero g) : CauchySeq :=
  f * CauchySeq.inv g h

end HFRat
