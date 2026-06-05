/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- AczelSetTheory/Algebra/Monoid.lean
-- Monoides nativos en HFSet: estructura, homomorfismos y submonoides.
--
-- Público:
--   HFMonoid                  : monoide (asociatividad + neutro bilateral)
--   HFMonoid.unique_id        : unicidad del neutro
--   HFMonoid.toHFMonoid       : submonoide como HFMonoid
--   HFMonoidHom               : homomorfismo de monoides f : M → N
--   HFMonoidHom.hom_e         : f(eM) = eN  (axioma explícito)
--   HFMonoidHom.comp          : composición de homomorfismos
--   HFSubmonoid               : submonoide de HFMonoid
--   HFSubmonoid.toHFMonoid    : submonoide como HFMonoid
--   HFSubmonoid.inter         : intersección de submonoides

import AczelSetTheory.HFSets
import AczelSetTheory.Axioms.Intersection

namespace HFAlgebra

-- ─────────────────────────────────────────────────────────────────
-- Estructura principal
-- ─────────────────────────────────────────────────────────────────

/-- Monoide algebraico nativo en HFSet.
    Axiomas: asociatividad, identidad bilateral.
    Nota: en un monoide sin inversos no puede derivarse la identidad
    derecha de la izquierda, por lo que ambas son axiomas explícitos. -/
structure HFMonoid where
  M   : HFSet
  op  : HFSet → HFSet → HFSet
  e   : HFSet
  e_mem       : e ∈ M
  op_closed   : ∀ {a b : HFSet}, a ∈ M → b ∈ M → op a b ∈ M
  op_assoc    : ∀ {a b c : HFSet}, a ∈ M → b ∈ M → c ∈ M →
                  op (op a b) c = op a (op b c)
  op_id_left  : ∀ {a : HFSet}, a ∈ M → op e a = a
  op_id_right : ∀ {a : HFSet}, a ∈ M → op a e = a

namespace HFMonoid

variable (mon : HFMonoid)

-- ─────────────────────────────────────────────────────────────────
-- Unicidad del neutro
-- ─────────────────────────────────────────────────────────────────

/-- Si `e'` es un neutro bilateral en `M`, entonces `e' = e`. -/
theorem unique_id {e' : HFSet} (he' : e' ∈ mon.M)
    (_hL : ∀ {a : HFSet}, a ∈ mon.M → mon.op e' a = a)
    (hR : ∀ {a : HFSet}, a ∈ mon.M → mon.op a e' = a) : e' = mon.e :=
  (mon.op_id_left he').symm.trans (hR mon.e_mem)

end HFMonoid

-- ─────────────────────────────────────────────────────────────────
-- Homomorfismo de monoides
-- ─────────────────────────────────────────────────────────────────

/-- Homomorfismo de HFMonoid.
    Los homomorfismos de monoides deben preservar el neutro de forma
    explícita: no es derivable de `f_hom` sin inversos. -/
structure HFMonoidHom (M N : HFMonoid) where
  f     : HFSet → HFSet
  f_mem : ∀ {a : HFSet}, a ∈ M.M → f a ∈ N.M
  f_hom : ∀ {a b : HFSet}, a ∈ M.M → b ∈ M.M → f (M.op a b) = N.op (f a) (f b)
  f_one : f M.e = N.e

namespace HFMonoidHom

variable {M N P : HFMonoid}

/-- La identidad es un homomorfismo de monoides. -/
def id (M : HFMonoid) : HFMonoidHom M M where
  f     := fun a => a
  f_mem := fun ha => ha
  f_hom := fun _ _ => rfl
  f_one := rfl

/-- Composición de homomorfismos de monoides. -/
def comp (ψ : HFMonoidHom N P) (φ : HFMonoidHom M N) : HFMonoidHom M P where
  f     := fun a => ψ.f (φ.f a)
  f_mem := fun ha => ψ.f_mem (φ.f_mem ha)
  f_hom := fun ha hb => by rw [φ.f_hom ha hb, ψ.f_hom (φ.f_mem ha) (φ.f_mem hb)]
  f_one := by rw [φ.f_one, ψ.f_one]

end HFMonoidHom

-- ─────────────────────────────────────────────────────────────────
-- Submonoide
-- ─────────────────────────────────────────────────────────────────

/-- Submonoide de un HFMonoid:
    subconjunto cerrado bajo la operación y que contiene al neutro. -/
structure HFSubmonoid (mon : HFMonoid) where
  S         : HFSet
  S_sub     : ∀ {x : HFSet}, x ∈ S → x ∈ mon.M
  e_mem     : mon.e ∈ S
  op_closed : ∀ {a b : HFSet}, a ∈ S → b ∈ S → mon.op a b ∈ S

namespace HFSubmonoid

variable {mon : HFMonoid}

/-- Todo submonoide es un monoide, heredando la operación del ambiente. -/
def toHFMonoid (sub : HFSubmonoid mon) : HFMonoid where
  M           := sub.S
  op          := mon.op
  e           := mon.e
  e_mem       := sub.e_mem
  op_closed   := sub.op_closed
  op_assoc    := fun ha hb hc =>
    mon.op_assoc (sub.S_sub ha) (sub.S_sub hb) (sub.S_sub hc)
  op_id_left  := fun ha => mon.op_id_left (sub.S_sub ha)
  op_id_right := fun ha => mon.op_id_right (sub.S_sub ha)

/-- La intersección de dos submonoides del mismo monoide es un submonoide. -/
def inter (sub₁ sub₂ : HFSubmonoid mon) : HFSubmonoid mon where
  S         := HFSet.inter sub₁.S sub₂.S
  S_sub     := fun hx => by rw [HFSet.mem_inter] at hx; exact sub₁.S_sub hx.1
  e_mem     := by rw [HFSet.mem_inter]; exact ⟨sub₁.e_mem, sub₂.e_mem⟩
  op_closed := fun ha hb => by
    rw [HFSet.mem_inter] at ha hb ⊢
    exact ⟨sub₁.op_closed ha.1 hb.1, sub₂.op_closed ha.2 hb.2⟩

end HFSubmonoid

end HFAlgebra
