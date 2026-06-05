/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- AczelSetTheory/Algebra/GroupHom.lean
-- Homomorfismos de grupos, núcleo e imagen.
--
-- Público:
--   HFGroupHom              : homomorfismo de grupos f : G → H
--   HFGroupHom.hom_e        : f(eG) = eH
--   HFGroupHom.hom_inv      : f(a⁻¹) = H.inv(f a)
--   HFGroupHom.ker          : ker φ como HFSubgroup G
--   HFGroupHom.image        : im φ como HFSubgroup H

import AczelSetTheory.Algebra.Subgroup

namespace HFAlgebra

-- ─────────────────────────────────────────────────────────────────
-- Estructura principal
-- ─────────────────────────────────────────────────────────────────

/-- Homomorfismo de HFGroup: función que preserva la operación. -/
structure HFGroupHom (G H : HFGroup) where
  f     : HFSet → HFSet
  f_mem : ∀ {a : HFSet}, a ∈ G.G → f a ∈ H.G
  f_hom : ∀ {a b : HFSet}, a ∈ G.G → b ∈ G.G → f (G.op a b) = H.op (f a) (f b)

namespace HFGroupHom

variable {G H : HFGroup} (φ : HFGroupHom G H)

-- ─────────────────────────────────────────────────────────────────
-- f(eG) = eH
-- ─────────────────────────────────────────────────────────────────

theorem hom_e : φ.f G.e = H.e := by
  apply H.left_cancel (φ.f_mem G.e_mem) (φ.f_mem G.e_mem) H.e_mem
  rw [← φ.f_hom G.e_mem G.e_mem, G.op_id_left G.e_mem, H.op_id_right (φ.f_mem G.e_mem)]

-- ─────────────────────────────────────────────────────────────────
-- f(a⁻¹) = H.inv(f a)
-- ─────────────────────────────────────────────────────────────────

theorem hom_inv {a : HFSet} (ha : a ∈ G.G) : φ.f (G.inv a) = H.inv (φ.f a) := by
  apply H.right_cancel (φ.f_mem ha) (φ.f_mem (G.inv_closed ha)) (H.inv_closed (φ.f_mem ha))
  rw [H.op_inv_left (φ.f_mem ha), ← φ.f_hom (G.inv_closed ha) ha,
      G.op_inv_left ha, φ.hom_e]

-- ─────────────────────────────────────────────────────────────────
-- Núcleo: ker φ = { a ∈ G | f a = eH }
-- ─────────────────────────────────────────────────────────────────

/-- El núcleo de φ es un subgrupo de G. -/
def ker : HFSubgroup G where
  H          := HFSet.sep G.G (fun a => φ.f a = H.e)
  H_sub      := fun hx => by rw [HFSet.mem_sep] at hx; exact hx.1
  e_mem      := by
    rw [HFSet.mem_sep]
    exact ⟨G.e_mem, φ.hom_e⟩
  op_closed  := fun ha hb => by
    rw [HFSet.mem_sep] at ha hb ⊢
    exact ⟨G.op_closed ha.1 hb.1,
           by rw [φ.f_hom ha.1 hb.1, ha.2, hb.2, H.op_id_left H.e_mem]⟩
  inv_closed := fun ha => by
    rw [HFSet.mem_sep] at ha ⊢
    exact ⟨G.inv_closed ha.1, by rw [φ.hom_inv ha.1, ha.2, H.inv_e]⟩

-- ─────────────────────────────────────────────────────────────────
-- Imagen: im φ = { b ∈ H | ∃ a ∈ G, f a = b }
-- ─────────────────────────────────────────────────────────────────

/-- La imagen de φ es un subgrupo de H. -/
def image : HFSubgroup H where
  H          := HFSet.sep H.G (fun b => ∃ a ∈ G.G, φ.f a = b)
  H_sub      := fun hx => by rw [HFSet.mem_sep] at hx; exact hx.1
  e_mem      := by
    rw [HFSet.mem_sep]
    exact ⟨H.e_mem, G.e, G.e_mem, φ.hom_e⟩
  op_closed  := fun hx hy => by
    rw [HFSet.mem_sep] at hx hy ⊢
    obtain ⟨hx_mem, a, haG, rfl⟩ := hx
    obtain ⟨hy_mem, b, hbG, rfl⟩ := hy
    exact ⟨H.op_closed hx_mem hy_mem, G.op a b, G.op_closed haG hbG, φ.f_hom haG hbG⟩
  inv_closed := fun hx => by
    rw [HFSet.mem_sep] at hx ⊢
    obtain ⟨hx_mem, a, haG, rfl⟩ := hx
    exact ⟨H.inv_closed hx_mem, G.inv a, G.inv_closed haG, φ.hom_inv haG⟩

end HFGroupHom

end HFAlgebra
