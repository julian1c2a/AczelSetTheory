/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- AczelSetTheory/VN/HFGroupVN.lean
-- Instanciación de FinGroup HFSet y transporte de gpow/order vía vN.
--
-- Público:
--   imageGroup         : ℕ₀FinGroup → FinGroup HFSet
--   vN_mem_imageGroup  : n ∈ G.carrier.elems → vN n ∈ (imageGroup G).carrier.elems
--   imageGroup_gpow    : gpow (imageGroup G) (vN g) n = vN (gpow G g n)
--   imageGroup_order   : order (imageGroup G) (vN g) _ = order G g hg

import AczelSetTheory.VN.Injective
import AczelSetTheory.VN.CardVN
import AczelSetTheory.Axioms.LinearOrder
import Peano.PeanoNat.Combinatorics.Group

open Peano Peano.FSet Peano.FSetFunction Peano.Group VN

namespace HFSet

-- ─────────────────────────────────────────────────────────────────
-- Auxiliar: conversión entre ∈ (FSet.image …).elems y mem_image_iff
--
-- La instancia Membership α (FSet α) es @[reducible], así que
-- x ∈ s ≡ x ∈ s.elems definitoriamente.
-- `change` aprovecha esta equivalencia; `rw [mem_image_iff]` requiere
-- que el patrón esté en forma de Membership (no de .elems).
-- ─────────────────────────────────────────────────────────────────

private theorem card_mem_of_mem_image {G : ℕ₀FinGroup} {x : HFSet}
    (hx : x ∈ (FSet.image vN G.carrier).elems) :
    HFSet.card x ∈ G.carrier.elems ∧ vN (HFSet.card x) = x := by
  -- change convierte .elems a la forma Membership para que rw funcione
  have hmem : x ∈ FSet.image vN G.carrier := hx
  rw [mem_image_iff] at hmem
  obtain ⟨n, hn, rfl⟩ := hmem
  rw [card_vN]
  exact ⟨hn, rfl⟩

-- Versión para goal: convierte ∈ .elems a ∈ FSet.image para usar mpr
private theorem mem_imageVN {G : ℕ₀FinGroup} {n : ℕ₀}
    (hn : n ∈ G.carrier.elems) :
    vN n ∈ (FSet.image vN G.carrier).elems := by
  have : vN n ∈ FSet.image vN G.carrier := mem_image_iff.mpr ⟨n, hn, rfl⟩
  exact this

-- ─────────────────────────────────────────────────────────────────
-- imageGroup : ℕ₀FinGroup → FinGroup HFSet
-- ─────────────────────────────────────────────────────────────────

/-- Transporta un grupo finito sobre ℕ₀ a FinGroup HFSet vía vN.
    El portador es la imagen de G.carrier bajo vN. -/
def imageGroup (G : ℕ₀FinGroup) : FinGroup HFSet where
  carrier := FSet.image vN G.carrier
  id      := vN G.id
  op      :=
    { toFun      := fun x y => vN (G.op (HFSet.card x) (HFSet.card y))
      map_carrier := fun x y hx hy =>
        mem_imageVN (G.op.map_carrier _ _
          (card_mem_of_mem_image hx).1
          (card_mem_of_mem_image hy).1) }
  inv     :=
    { toFun      := fun x => vN (G.inv (HFSet.card x))
      map_carrier := fun x hx =>
        mem_imageVN (G.inv.map_carrier _ (card_mem_of_mem_image hx).1) }
  id_in   := mem_imageVN G.id_in
  op_assoc := fun a b c ha hb hc => by
    show vN (G.op (HFSet.card (vN (G.op (HFSet.card a) (HFSet.card b)))) (HFSet.card c)) =
         vN (G.op (HFSet.card a) (HFSet.card (vN (G.op (HFSet.card b) (HFSet.card c)))))
    rw [card_vN, card_vN]
    exact congrArg vN (G.op_assoc _ _ _
      (card_mem_of_mem_image ha).1
      (card_mem_of_mem_image hb).1
      (card_mem_of_mem_image hc).1)
  op_id   := fun a ha => by
    obtain ⟨ha_mem, ha_eq⟩ := card_mem_of_mem_image ha
    exact ⟨by show vN (G.op (HFSet.card a) (HFSet.card (vN G.id))) = a
              rw [card_vN, (G.op_id _ ha_mem).1, ha_eq],
           by show vN (G.op (HFSet.card (vN G.id)) (HFSet.card a)) = a
              rw [card_vN, (G.op_id _ ha_mem).2, ha_eq]⟩
  op_inv  := fun a ha => by
    obtain ⟨ha_mem, _⟩ := card_mem_of_mem_image ha
    exact ⟨by show vN (G.op (HFSet.card a) (HFSet.card (vN (G.inv (HFSet.card a))))) = vN G.id
              rw [card_vN, (G.op_inv _ ha_mem).1],
           by show vN (G.op (HFSet.card (vN (G.inv (HFSet.card a)))) (HFSet.card a)) = vN G.id
              rw [card_vN, (G.op_inv _ ha_mem).2]⟩

-- ─────────────────────────────────────────────────────────────────
-- Membresía: vN n ∈ (imageGroup G).carrier.elems
-- ─────────────────────────────────────────────────────────────────

theorem vN_mem_imageGroup {G : ℕ₀FinGroup} {n : ℕ₀}
    (hn : n ∈ G.carrier.elems) :
    vN n ∈ (imageGroup G).carrier.elems :=
  mem_imageVN hn

-- ─────────────────────────────────────────────────────────────────
-- Transport de gpow
-- ─────────────────────────────────────────────────────────────────

/-- gpow en imageGroup G coincide con vN de gpow en G. -/
theorem imageGroup_gpow (G : ℕ₀FinGroup) {g : ℕ₀} (hg : g ∈ G.carrier.elems) :
    ∀ n : ℕ₀, gpow (imageGroup G) (vN g) n = vN (gpow G g n)
  | .zero   => rfl
  | .succ n => by
      rw [gpow_succ, imageGroup_gpow G hg n, gpow_succ]
      change vN (G.op (HFSet.card (vN (gpow G g n))) (HFSet.card (vN g))) =
             vN (G.op (gpow G g n) g)
      rw [card_vN, card_vN]

-- ─────────────────────────────────────────────────────────────────
-- Transport de order
-- ─────────────────────────────────────────────────────────────────

/-- El orden de vN g en imageGroup G coincide con el orden de g en G. -/
theorem imageGroup_order (G : ℕ₀FinGroup) {g : ℕ₀} (hg : g ∈ G.carrier.elems) :
    order (imageGroup G) (vN g) (vN_mem_imageGroup hg) = order G g hg := by
  apply le_antisymm
  · apply order_minimal
    · exact order_pos G g hg
    · rw [imageGroup_gpow G hg, gpow_order_eq_id G g hg]; rfl
  · apply order_minimal
    · exact order_pos (imageGroup G) (vN g) (vN_mem_imageGroup hg)
    · have h : vN (gpow G g (order (imageGroup G) (vN g) (vN_mem_imageGroup hg))) = vN G.id := by
        have h0 := gpow_order_eq_id (imageGroup G) (vN g) (vN_mem_imageGroup hg)
        rw [imageGroup_gpow G hg] at h0
        exact h0
      exact vN_injective h

end HFSet
