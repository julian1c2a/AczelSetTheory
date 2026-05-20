/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- AczelSetTheory/Algebra/Subgroup.lean
-- Subgrupos, intersección, cosetes derechos y equivalencia de cosetes.
--
-- Público:
--   HFSubgroup                            : subgrupo de HFGroup
--   HFSubgroup.toHFGroup                  : subgrupo como HFGroup
--   HFSubgroup.inter                      : intersección de subgrupos
--   HFSubgroup.rightCoset                 : cosete derecho Ha
--   HFSubgroup.mem_rightCoset             : x ∈ Ha ↔ ∃ h ∈ H, x = h·a
--   HFSubgroup.cosetEq                    : b·a⁻¹ ∈ H
--   HFSubgroup.cosetEq_refl               : reflexividad
--   HFSubgroup.cosetEq_symm               : simetría
--   HFSubgroup.cosetEq_trans              : transitividad
--   HFSubgroup.cosetEq_iff_rightCoset_eq  : Ha = Hb ↔ b·a⁻¹ ∈ H

import AczelSetTheory.Algebra.Group
import AczelSetTheory.Axioms.Separation
import AczelSetTheory.Axioms.Decidable
import AczelSetTheory.Axioms.OrdinalNat
import AczelSetTheory.Axioms.Intersection

namespace HFAlgebra

-- ─────────────────────────────────────────────────────────────────
-- Estructura principal
-- ─────────────────────────────────────────────────────────────────

/-- Subgrupo de un HFGroup con axiomas mínimos:
    contención en G, neutro, clausura bajo op e inv. -/
structure HFSubgroup (grp : HFGroup) where
  H          : HFSet
  H_sub      : ∀ {x : HFSet}, x ∈ H → x ∈ grp.G
  e_mem      : grp.e ∈ H
  op_closed  : ∀ {a b : HFSet}, a ∈ H → b ∈ H → grp.op a b ∈ H
  inv_closed : ∀ {a : HFSet}, a ∈ H → grp.inv a ∈ H

namespace HFSubgroup

variable {grp : HFGroup}

-- ─────────────────────────────────────────────────────────────────
-- Subgrupo como grupo
-- ─────────────────────────────────────────────────────────────────

/-- Todo subgrupo es un grupo, heredando la operación del grupo ambiente. -/
def toHFGroup (sub : HFSubgroup grp) : HFGroup where
  G           := sub.H
  op          := grp.op
  e           := grp.e
  inv         := grp.inv
  e_mem       := sub.e_mem
  op_closed   := sub.op_closed
  inv_closed  := sub.inv_closed
  op_assoc    := fun ha hb hc =>
    grp.op_assoc (sub.H_sub ha) (sub.H_sub hb) (sub.H_sub hc)
  op_id_left  := fun ha => grp.op_id_left (sub.H_sub ha)
  op_inv_left := fun ha => grp.op_inv_left (sub.H_sub ha)

-- ─────────────────────────────────────────────────────────────────
-- Intersección de subgrupos
-- ─────────────────────────────────────────────────────────────────

/-- La intersección de dos subgrupos del mismo grupo es un subgrupo. -/
def inter (sub₁ sub₂ : HFSubgroup grp) : HFSubgroup grp where
  H          := HFSet.inter sub₁.H sub₂.H
  H_sub      := fun hx => by rw [HFSet.mem_inter] at hx; exact sub₁.H_sub hx.1
  e_mem      := by rw [HFSet.mem_inter]; exact ⟨sub₁.e_mem, sub₂.e_mem⟩
  op_closed  := fun ha hb => by
    rw [HFSet.mem_inter] at ha hb ⊢
    exact ⟨sub₁.op_closed ha.1 hb.1, sub₂.op_closed ha.2 hb.2⟩
  inv_closed := fun ha => by
    rw [HFSet.mem_inter] at ha ⊢
    exact ⟨sub₁.inv_closed ha.1, sub₂.inv_closed ha.2⟩

-- ─────────────────────────────────────────────────────────────────
-- Cosete derecho Ha = { h·a | h ∈ H }
-- ─────────────────────────────────────────────────────────────────

/-- Cosete derecho de `a` en `sub`: `{ x ∈ G | ∃ h ∈ H, x = h·a }`. -/
def rightCoset (sub : HFSubgroup grp) (a : HFSet) : HFSet :=
  HFSet.sep grp.G (fun x => ∃ h ∈ sub.H, x = grp.op h a)

theorem mem_rightCoset (sub : HFSubgroup grp) {a x : HFSet} (ha : a ∈ grp.G) :
    x ∈ sub.rightCoset a ↔ ∃ h ∈ sub.H, x = grp.op h a := by
  show x ∈ HFSet.sep grp.G (fun x => ∃ h ∈ sub.H, x = grp.op h a) ↔ _
  rw [HFSet.mem_sep]
  constructor
  · intro ⟨_, hx⟩; exact hx
  · intro hx
    refine ⟨?_, hx⟩
    obtain ⟨h, hh, rfl⟩ := hx
    exact grp.op_closed (sub.H_sub hh) ha

-- ─────────────────────────────────────────────────────────────────
-- Relación de cosetes: cosetEq a b ↔ b·a⁻¹ ∈ H
-- ─────────────────────────────────────────────────────────────────

/-- `a` y `b` pertenecen al mismo cosete derecho iff `b · a⁻¹ ∈ H`. -/
def cosetEq (sub : HFSubgroup grp) (a b : HFSet) : Prop :=
  grp.op b (grp.inv a) ∈ sub.H

theorem cosetEq_refl (sub : HFSubgroup grp) {a : HFSet} (ha : a ∈ grp.G) :
    sub.cosetEq a a := by
  show grp.op a (grp.inv a) ∈ sub.H
  rw [grp.op_inv_right ha]
  exact sub.e_mem

theorem cosetEq_symm (sub : HFSubgroup grp) {a b : HFSet}
    (ha : a ∈ grp.G) (hb : b ∈ grp.G) (h : sub.cosetEq a b) : sub.cosetEq b a := by
  show grp.op a (grp.inv b) ∈ sub.H
  have hinva : grp.inv a ∈ grp.G := grp.inv_closed ha
  -- inv(b · inv a) = inv(inv a) · inv b = a · inv b
  have heq : grp.inv (grp.op b (grp.inv a)) = grp.op a (grp.inv b) := by
    rw [grp.inv_op hb hinva, grp.inv_inv ha]
  rw [← heq]
  exact sub.inv_closed h

theorem cosetEq_trans (sub : HFSubgroup grp) {a b c : HFSet}
    (ha : a ∈ grp.G) (hb : b ∈ grp.G) (hc : c ∈ grp.G)
    (hab : sub.cosetEq a b) (hbc : sub.cosetEq b c) : sub.cosetEq a c := by
  -- hab : b·inv a ∈ H,  hbc : c·inv b ∈ H,  goal : c·inv a ∈ H
  show grp.op c (grp.inv a) ∈ sub.H
  have hinva : grp.inv a ∈ grp.G := grp.inv_closed ha
  have hinvb : grp.inv b ∈ grp.G := grp.inv_closed hb
  -- (c·inv b)·(b·inv a) = c·inv a
  have key : grp.op (grp.op c (grp.inv b)) (grp.op b (grp.inv a)) = grp.op c (grp.inv a) :=
    calc grp.op (grp.op c (grp.inv b)) (grp.op b (grp.inv a))
        = grp.op c (grp.op (grp.inv b) (grp.op b (grp.inv a))) :=
              grp.op_assoc hc hinvb (grp.op_closed hb hinva)
      _ = grp.op c (grp.op (grp.op (grp.inv b) b) (grp.inv a)) := by
              rw [← grp.op_assoc hinvb hb hinva]
      _ = grp.op c (grp.op grp.e (grp.inv a)) := by rw [grp.op_inv_left hb]
      _ = grp.op c (grp.inv a) := by rw [grp.op_id_left hinva]
  rw [← key]
  exact sub.op_closed hbc hab

-- ─────────────────────────────────────────────────────────────────
-- cosetEq ↔ igualdad de cosetes derechos
-- ─────────────────────────────────────────────────────────────────

theorem cosetEq_iff_rightCoset_eq (sub : HFSubgroup grp) {a b : HFSet}
    (ha : a ∈ grp.G) (hb : b ∈ grp.G) :
    sub.cosetEq a b ↔ sub.rightCoset a = sub.rightCoset b := by
  constructor
  · intro hab
    have hinva : grp.inv a ∈ grp.G := grp.inv_closed ha
    have hinvb : grp.inv b ∈ grp.G := grp.inv_closed hb
    -- a·inv b ∈ H  (desde b·inv a ∈ H, tomando inverso)
    have hab' : grp.op a (grp.inv b) ∈ sub.H := by
      have : grp.inv (grp.op b (grp.inv a)) = grp.op a (grp.inv b) := by
        rw [grp.inv_op hb hinva, grp.inv_inv ha]
      rw [← this]; exact sub.inv_closed hab
    apply HFSet.extensionality
    intro x
    rw [sub.mem_rightCoset ha, sub.mem_rightCoset hb]
    constructor
    · -- Ha ⊆ Hb: x = h·a, h' = h·(a·inv b), h'·b = h·a = x
      intro ⟨h, hh, hx⟩
      refine ⟨grp.op h (grp.op a (grp.inv b)), sub.op_closed hh hab', ?_⟩
      subst hx
      calc grp.op h a
          = grp.op h (grp.op a grp.e)                 := by rw [grp.op_id_right ha]
        _ = grp.op h (grp.op a (grp.op (grp.inv b) b)) := by rw [grp.op_inv_left hb]
        _ = grp.op h (grp.op (grp.op a (grp.inv b)) b) := by rw [grp.op_assoc ha hinvb hb]
        _ = grp.op (grp.op h (grp.op a (grp.inv b))) b :=
                (grp.op_assoc (sub.H_sub hh) (grp.op_closed ha hinvb) hb).symm
    · -- Hb ⊆ Ha: x = h·b, h' = h·(b·inv a), h'·a = h·b = x
      intro ⟨h, hh, hx⟩
      refine ⟨grp.op h (grp.op b (grp.inv a)), sub.op_closed hh hab, ?_⟩
      subst hx
      calc grp.op h b
          = grp.op h (grp.op b grp.e)                 := by rw [grp.op_id_right hb]
        _ = grp.op h (grp.op b (grp.op (grp.inv a) a)) := by rw [grp.op_inv_left ha]
        _ = grp.op h (grp.op (grp.op b (grp.inv a)) a) := by rw [grp.op_assoc hb hinva ha]
        _ = grp.op (grp.op h (grp.op b (grp.inv a))) a :=
                (grp.op_assoc (sub.H_sub hh) (grp.op_closed hb hinva) ha).symm
  · intro heq
    -- a ∈ Ha = e·a
    have ha_in_Ha : a ∈ sub.rightCoset a := by
      rw [sub.mem_rightCoset ha]
      exact ⟨grp.e, sub.e_mem, (grp.op_id_left ha).symm⟩
    -- a ∈ Hb (por Ha = Hb)
    obtain ⟨h, hh, hhb⟩ := (sub.mem_rightCoset hb).mp (heq ▸ ha_in_Ha)
    -- a = h·b  →  b·inv a = b·inv(h·b) = b·(inv b·inv h) = inv h ∈ H
    have hba : grp.op b (grp.inv a) = grp.inv h := by
      rw [hhb, grp.inv_op (sub.H_sub hh) hb,
          ← grp.op_assoc hb (grp.inv_closed hb) (grp.inv_closed (sub.H_sub hh)),
          grp.op_inv_right hb, grp.op_id_left (grp.inv_closed (sub.H_sub hh))]
    show grp.op b (grp.inv a) ∈ sub.H
    rw [hba]
    exact sub.inv_closed hh

end HFSubgroup

end HFAlgebra
