/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- AczelSetTheory/Algebra/RingHom.lean
-- Homomorfismos de anillos y subanillos.
--
-- Público:
--   HFRingHom               : homomorfismo de anillos unitarios f : R → S
--   HFRingHom.hom_zero      : f(0R) = 0S
--   HFRingHom.hom_neg       : f(-a) = -f(a)
--   HFRingHom.comp          : composición de homomorfismos
--   HFSubring               : subanillo de HFRing
--   HFSubring.toHFRing      : subanillo como HFRing
--   HFSubring.inter         : intersección de subanillos

import AczelSetTheory.Algebra.Ring
import AczelSetTheory.Axioms.Intersection

namespace HFAlgebra

-- ─────────────────────────────────────────────────────────────────
-- Homomorfismo de anillos
-- ─────────────────────────────────────────────────────────────────

/-- Homomorfismo de HFRing unitario.
    Preserva suma, producto y unidad.
    La preservación del cero es derivable de `f_add`; la del uno es axioma. -/
structure HFRingHom (R S : HFRing) where
  f     : HFSet → HFSet
  f_mem : ∀ {a : HFSet}, a ∈ R.R → f a ∈ S.R
  f_add : ∀ {a b : HFSet}, a ∈ R.R → b ∈ R.R → f (R.add a b) = S.add (f a) (f b)
  f_mul : ∀ {a b : HFSet}, a ∈ R.R → b ∈ R.R → f (R.mul a b) = S.mul (f a) (f b)
  f_one : f R.one = S.one

namespace HFRingHom

variable {R S T : HFRing} (φ : HFRingHom R S)

-- ─────────────────────────────────────────────────────────────────
-- f(0R) = 0S
-- ─────────────────────────────────────────────────────────────────

theorem hom_zero : φ.f R.zero = S.zero := by
  -- f(0+0) = f(0) + f(0),  f(0+0) = f(0)  →  f(0) + f(0) = f(0) + 0
  have hfz : φ.f R.zero ∈ S.R := φ.f_mem R.zero_mem
  apply S.toAdditiveHFGroup.left_cancel hfz hfz S.zero_mem
  show S.add (φ.f R.zero) (φ.f R.zero) = S.add (φ.f R.zero) S.zero
  calc S.add (φ.f R.zero) (φ.f R.zero)
      = φ.f (R.add R.zero R.zero) := (φ.f_add R.zero_mem R.zero_mem).symm
    _ = φ.f R.zero                := by rw [R.zero_add R.zero_mem]
    _ = S.add (φ.f R.zero) S.zero := (S.add_zero hfz).symm

-- ─────────────────────────────────────────────────────────────────
-- f(-a) = -f(a)
-- ─────────────────────────────────────────────────────────────────

theorem hom_neg {a : HFSet} (ha : a ∈ R.R) : φ.f (R.neg a) = S.neg (φ.f a) := by
  have hfa  : φ.f a ∈ S.R         := φ.f_mem ha
  have hfna : φ.f (R.neg a) ∈ S.R := φ.f_mem (R.neg_closed ha)
  -- f(neg a) + f(a) = f(neg a + a) = f(0) = 0
  have hkey : S.add (φ.f (R.neg a)) (φ.f a) = S.zero :=
    calc S.add (φ.f (R.neg a)) (φ.f a)
        = φ.f (R.add (R.neg a) a) := (φ.f_add (R.neg_closed ha) ha).symm
      _ = φ.f R.zero              := by rw [R.neg_add ha]
      _ = S.zero                  := φ.hom_zero
  exact S.toAdditiveHFGroup.unique_inv hfa hfna hkey

-- ─────────────────────────────────────────────────────────────────
-- Identidad y composición
-- ─────────────────────────────────────────────────────────────────

/-- La identidad es un homomorfismo de anillos. -/
def id (R : HFRing) : HFRingHom R R where
  f     := fun a => a
  f_mem := fun ha => ha
  f_add := fun _ _ => rfl
  f_mul := fun _ _ => rfl
  f_one := rfl

/-- Composición de homomorfismos de anillos. -/
def comp (ψ : HFRingHom S T) (φ : HFRingHom R S) : HFRingHom R T where
  f     := fun a => ψ.f (φ.f a)
  f_mem := fun ha => ψ.f_mem (φ.f_mem ha)
  f_add := fun ha hb => by rw [φ.f_add ha hb, ψ.f_add (φ.f_mem ha) (φ.f_mem hb)]
  f_mul := fun ha hb => by rw [φ.f_mul ha hb, ψ.f_mul (φ.f_mem ha) (φ.f_mem hb)]
  f_one := by rw [φ.f_one, ψ.f_one]

end HFRingHom

-- ─────────────────────────────────────────────────────────────────
-- Subanillo
-- ─────────────────────────────────────────────────────────────────

/-- Subanillo de un HFRing: subconjunto cerrado bajo suma, producto y negación,
    que contiene al cero y al uno. -/
structure HFSubring (rng : HFRing) where
  S          : HFSet
  S_sub      : ∀ {x : HFSet}, x ∈ S → x ∈ rng.R
  zero_mem   : rng.zero ∈ S
  one_mem    : rng.one ∈ S
  add_closed : ∀ {a b : HFSet}, a ∈ S → b ∈ S → rng.add a b ∈ S
  mul_closed : ∀ {a b : HFSet}, a ∈ S → b ∈ S → rng.mul a b ∈ S
  neg_closed : ∀ {a : HFSet}, a ∈ S → rng.neg a ∈ S

namespace HFSubring

variable {rng : HFRing}

/-- Todo subanillo es un anillo, heredando las operaciones del anillo ambiente. -/
def toHFRing (sub : HFSubring rng) : HFRing where
  R             := sub.S
  add           := rng.add
  mul           := rng.mul
  zero          := rng.zero
  one           := rng.one
  neg           := rng.neg
  zero_mem      := sub.zero_mem
  one_mem       := sub.one_mem
  add_closed    := sub.add_closed
  mul_closed    := sub.mul_closed
  neg_closed    := sub.neg_closed
  add_assoc     := fun ha hb hc =>
    rng.add_assoc (sub.S_sub ha) (sub.S_sub hb) (sub.S_sub hc)
  add_comm      := fun ha hb =>
    rng.add_comm (sub.S_sub ha) (sub.S_sub hb)
  zero_add      := fun ha => rng.zero_add (sub.S_sub ha)
  neg_add       := fun ha => rng.neg_add (sub.S_sub ha)
  mul_assoc     := fun ha hb hc =>
    rng.mul_assoc (sub.S_sub ha) (sub.S_sub hb) (sub.S_sub hc)
  mul_one       := fun ha => rng.mul_one (sub.S_sub ha)
  one_mul       := fun ha => rng.one_mul (sub.S_sub ha)
  left_distrib  := fun ha hb hc =>
    rng.left_distrib (sub.S_sub ha) (sub.S_sub hb) (sub.S_sub hc)
  right_distrib := fun ha hb hc =>
    rng.right_distrib (sub.S_sub ha) (sub.S_sub hb) (sub.S_sub hc)

/-- La intersección de dos subanillos del mismo anillo es un subanillo. -/
def inter (sub₁ sub₂ : HFSubring rng) : HFSubring rng where
  S          := HFSet.inter sub₁.S sub₂.S
  S_sub      := fun hx => by rw [HFSet.mem_inter] at hx; exact sub₁.S_sub hx.1
  zero_mem   := by rw [HFSet.mem_inter]; exact ⟨sub₁.zero_mem, sub₂.zero_mem⟩
  one_mem    := by rw [HFSet.mem_inter]; exact ⟨sub₁.one_mem, sub₂.one_mem⟩
  add_closed := fun ha hb => by
    rw [HFSet.mem_inter] at ha hb ⊢
    exact ⟨sub₁.add_closed ha.1 hb.1, sub₂.add_closed ha.2 hb.2⟩
  mul_closed := fun ha hb => by
    rw [HFSet.mem_inter] at ha hb ⊢
    exact ⟨sub₁.mul_closed ha.1 hb.1, sub₂.mul_closed ha.2 hb.2⟩
  neg_closed := fun ha => by
    rw [HFSet.mem_inter] at ha ⊢
    exact ⟨sub₁.neg_closed ha.1, sub₂.neg_closed ha.2⟩

end HFSubring

end HFAlgebra
