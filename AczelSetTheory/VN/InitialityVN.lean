/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- AczelSetTheory/VN/InitialityVN.lean
--
-- Iniciality de ℕ₀ como sistema de Peano en el contexto de von Neumann.
-- Construye el subtipo HFNat de naturales de von Neumann (= {x : HFSet // isNat x}),
-- le da estructura de PeanoSystem, y exhibe el embedding vN como el único
-- morfismo de Peano ℕ₀_PeanoSystem → HFNatPeanoSystem.
--
-- Contenido:
--   HFNat              : Type  ({x : HFSet // HFSet.isNat x})
--   HFNat.zero         : HFNat
--   HFNat.succ         : HFNat → HFNat
--   HFNat.succ_injective
--   HFNat.zero_ne_succ
--   HFNatPeanoSystem   : PeanoSystem  (HFNat con sus operaciones)
--   vN_nat             : ℕ₀ → HFNat  (embedding)
--   vN_nat_zero        : vN_nat 𝟘 = HFNat.zero
--   vN_nat_succ        : vN_nat (σ n) = HFNat.succ (vN_nat n)
--   vN_morph           : PeanoMorphism ℕ₀_PeanoSystem HFNatPeanoSystem
--   vN_morph_unique    : unicidad del morfismo

import AczelSetTheory.VN.IsNat
import AczelSetTheory.VN.Injective
import AczelSetTheory.VN.CardVN
import Peano.PeanoNat.Foundation.PeanoSystem
import Peano.PeanoNat.Foundation.Initiality

open Peano Peano.Foundation

namespace VN

-- ─────────────────────────────────────────────────────────────────
-- Subtipo de naturales de von Neumann
-- ─────────────────────────────────────────────────────────────────

/-- Los naturales de von Neumann como subtipo de HFSet. -/
def HFNat : Type := {x : HFSet // HFSet.isNat x}

namespace HFNat

/-- El cero de von Neumann (= conjunto vacío). -/
def zero : HFNat := ⟨HFSet.empty, HFSet.isNat_zero⟩

/-- El sucesor de von Neumann. -/
def succ (n : HFNat) : HFNat := ⟨HFSet.succ n.1, HFSet.isNat_succ n.2⟩

theorem succ_injective : ∀ a b : HFNat, succ a = succ b → a = b := by
  intro ⟨x, _⟩ ⟨y, _⟩ h
  exact Subtype.ext (HFSet.succ_injective _ _ (congrArg Subtype.val h))

theorem zero_ne_succ : ∀ n : HFNat, zero ≠ succ n := by
  intro ⟨x, _⟩ h
  have heq := congrArg Subtype.val h
  simp only [zero, succ] at heq
  exact HFSet.succ_ne_empty x heq.symm

end HFNat

-- ─────────────────────────────────────────────────────────────────
-- Función auxiliar de recursión
-- (ℕ₀_rec_fn en Initiality.lean es private, así que definimos la nuestra)
-- ─────────────────────────────────────────────────────────────────

private def hfnat_rec_aux {A : Type 0} (a : A) (f : A → A) : ℕ₀ → A
  | .zero   => a
  | .succ n => f (hfnat_rec_aux a f n)

/-- La función recursiva canónica sobre HFNat, definida via card. -/
private def hfnat_rec {A : Type 0} (a : A) (f : A → A) (n : HFNat) : A :=
  hfnat_rec_aux a f (HFSet.card n.1)

-- ─────────────────────────────────────────────────────────────────
-- HFNatPeanoSystem
-- ─────────────────────────────────────────────────────────────────

/-- HFNat con cero, sucesor de von Neumann y los tres axiomas de Peano. -/
def HFNatPeanoSystem : PeanoSystem where
  N        := HFNat
  zero     := HFNat.zero
  succ     := HFNat.succ
  inj      := HFNat.succ_injective
  discr    := HFNat.zero_ne_succ
  ind      := fun P h0 hs ⟨n, hn⟩ =>
    (HFSet.isNat_induction
      (fun x => ∀ hx : HFSet.isNat x, P ⟨x, hx⟩)
      (fun _ => h0)
      (fun k hk ih hsucc => hs ⟨k, hk⟩ (ih hk))
      hn) hn
  prim_rec := fun {A} a f => by
    refine ⟨hfnat_rec a f, ⟨?_, ?_⟩, ?_⟩
    · -- hfnat_rec a f HFNat.zero = a
      show hfnat_rec_aux a f (HFSet.card HFSet.empty) = a
      rw [HFSet.card_empty]; rfl
    · -- ∀ n, hfnat_rec a f (HFNat.succ n) = f (hfnat_rec a f n)
      intro ⟨x, _⟩
      show hfnat_rec_aux a f (HFSet.card (HFSet.succ x)) = f (hfnat_rec_aux a f (HFSet.card x))
      rw [HFSet.card_succ]; rfl
    · -- unicidad
      intro h' ⟨h'0, h'succ⟩
      funext ⟨n, hn⟩
      show h' ⟨n, hn⟩ = hfnat_rec_aux a f (HFSet.card n)
      apply (HFSet.isNat_induction
        (fun x => ∀ hx : HFSet.isNat x, h' ⟨x, hx⟩ = hfnat_rec_aux a f (HFSet.card x))
        (fun _ => by
          show h' ⟨HFSet.empty, _⟩ = hfnat_rec_aux a f (HFSet.card HFSet.empty)
          rw [HFSet.card_empty]
          exact h'0)
        (fun k hk ih hsucc => by
          show h' ⟨HFSet.succ k, _⟩ = hfnat_rec_aux a f (HFSet.card (HFSet.succ k))
          rw [HFSet.card_succ]
          show h' ⟨HFSet.succ k, _⟩ = f (hfnat_rec_aux a f (HFSet.card k))
          rw [← ih hk]
          exact h'succ ⟨k, hk⟩)
        hn) hn

-- ─────────────────────────────────────────────────────────────────
-- El embedding vN como morfismo de Peano
-- ─────────────────────────────────────────────────────────────────

/-- El embedding de ℕ₀ en HFNat vía vN. -/
def vN_nat (n : ℕ₀) : HFNat := ⟨vN n, isNat_vN n⟩

theorem vN_nat_zero : vN_nat 𝟘 = HFNat.zero :=
  Subtype.ext vN_zero

theorem vN_nat_succ (n : ℕ₀) : vN_nat (σ n) = HFNat.succ (vN_nat n) :=
  Subtype.ext (vN_succ n)

/-- vN como morfismo de álgebras de Peano ℕ₀_PeanoSystem → HFNatPeanoSystem. -/
def vN_morph : PeanoMorphism ℕ₀_PeanoSystem HFNatPeanoSystem where
  map       := vN_nat
  pres_zero := vN_nat_zero
  pres_succ := vN_nat_succ

/-- Unicidad: cualquier morfismo que preserva cero y sucesor coincide con vN_nat. -/
theorem vN_morph_unique (h : ℕ₀ → HFNat)
    (h0 : h 𝟘 = HFNat.zero)
    (hs : ∀ n, h (σ n) = HFNat.succ (h n)) :
    h = vN_nat := by
  funext n
  induction n with
  | zero   => rw [h0, vN_nat_zero]
  | succ k ih =>
    rw [hs k, ih]
    exact (vN_nat_succ k).symm

end VN
