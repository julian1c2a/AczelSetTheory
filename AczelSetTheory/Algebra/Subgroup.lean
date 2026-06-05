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
import AczelSetTheory.Axioms.CardImage

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
-- Conjugación de subgrupos
-- ─────────────────────────────────────────────────────────────────

/-- Subgrupo conjugado `gHg⁻¹ = { x ∈ G | ∃ h ∈ H, x = g·h·g⁻¹ }`. -/
def conjugate (sub : HFSubgroup grp) (g : HFSet) (hg : g ∈ grp.G) : HFSubgroup grp where
  H := HFSet.sep grp.G (fun x => ∃ h ∈ sub.H, x = grp.op (grp.op g h) (grp.inv g))
  H_sub := fun hx => by
    rw [HFSet.mem_sep] at hx
    exact hx.1
  e_mem := by
    rw [HFSet.mem_sep]
    refine ⟨grp.e_mem, grp.e, sub.e_mem, ?_⟩
    calc grp.e
        = grp.op g (grp.inv g) := (grp.op_inv_right hg).symm
      _ = grp.op (grp.op g grp.e) (grp.inv g) := by rw [grp.op_id_right hg]
  op_closed := by
    intro a b ha hb
    rw [HFSet.mem_sep] at ha hb ⊢
    obtain ⟨haG, h₁, hh₁, rfl⟩ := ha
    obtain ⟨hbG, h₂, hh₂, rfl⟩ := hb
    refine ⟨grp.op_closed haG hbG, grp.op h₁ h₂, sub.op_closed hh₁ hh₂, ?_⟩
    have hh₁G : h₁ ∈ grp.G := sub.H_sub hh₁
    have hh₂G : h₂ ∈ grp.G := sub.H_sub hh₂
    have hgi : grp.inv g ∈ grp.G := grp.inv_closed hg
    have hcancel :
        grp.op (grp.inv g) (grp.op (grp.op g h₂) (grp.inv g)) = grp.op h₂ (grp.inv g) := by
      calc
        grp.op (grp.inv g) (grp.op (grp.op g h₂) (grp.inv g))
            = grp.op (grp.op (grp.inv g) (grp.op g h₂)) (grp.inv g) :=
                (grp.op_assoc hgi (grp.op_closed hg hh₂G) hgi).symm
        _ = grp.op h₂ (grp.inv g) := by rw [grp.op_inv_left_apply hg hh₂G]
    calc grp.op (grp.op (grp.op g h₁) (grp.inv g)) (grp.op (grp.op g h₂) (grp.inv g))
        = grp.op (grp.op g h₁)
                 (grp.op (grp.inv g) (grp.op (grp.op g h₂) (grp.inv g))) :=
            grp.op_assoc (grp.op_closed hg hh₁G) hgi (grp.op_closed (grp.op_closed hg hh₂G) hgi)
      _ = grp.op (grp.op g h₁) (grp.op h₂ (grp.inv g)) := by rw [hcancel]
      _ = grp.op g (grp.op h₁ (grp.op h₂ (grp.inv g))) :=
            grp.op_assoc hg hh₁G (grp.op_closed hh₂G hgi)
      _ = grp.op g (grp.op (grp.op h₁ h₂) (grp.inv g)) := by
            rw [grp.op_assoc hh₁G hh₂G hgi]
      _ = grp.op (grp.op g (grp.op h₁ h₂)) (grp.inv g) :=
            (grp.op_assoc hg (grp.op_closed hh₁G hh₂G) hgi).symm
  inv_closed := by
    intro a ha
    rw [HFSet.mem_sep] at ha ⊢
    obtain ⟨haG, h, hh, rfl⟩ := ha
    have hhG : h ∈ grp.G := sub.H_sub hh
    refine ⟨grp.inv_closed haG, grp.inv h, sub.inv_closed hh, ?_⟩
    calc grp.inv (grp.op (grp.op g h) (grp.inv g))
        = grp.op (grp.inv (grp.inv g)) (grp.inv (grp.op g h)) :=
            grp.inv_op (grp.op_closed hg hhG) (grp.inv_closed hg)
      _ = grp.op g (grp.op (grp.inv h) (grp.inv g)) := by
            rw [grp.inv_inv hg, grp.inv_op hg hhG]
      _ = grp.op (grp.op g (grp.inv h)) (grp.inv g) :=
            (grp.op_assoc hg (grp.inv_closed hhG) (grp.inv_closed hg)).symm

/-- Caracterización de membresía en el subgrupo conjugado. -/
theorem mem_conjugate_iff (sub : HFSubgroup grp) {g x : HFSet} (hg : g ∈ grp.G) :
    x ∈ (sub.conjugate g hg).H ↔
      ∃ h ∈ sub.H, x = grp.op (grp.op g h) (grp.inv g) := by
  show x ∈ HFSet.sep grp.G (fun y => ∃ h ∈ sub.H, y = grp.op (grp.op g h) (grp.inv g)) ↔ _
  rw [HFSet.mem_sep]
  constructor
  · intro hx
    exact hx.2
  · intro hx
    obtain ⟨h, hh, rfl⟩ := hx
    refine ⟨?_, ⟨h, hh, rfl⟩⟩
    exact grp.op_closed (grp.op_closed hg (sub.H_sub hh)) (grp.inv_closed hg)

/-- La conjugación preserva cardinalidad: `card(gHg⁻¹) = card(H)`. -/
theorem conjugate_card_eq (sub : HFSubgroup grp) {g : HFSet} (hg : g ∈ grp.G) :
    HFSet.card (sub.conjugate g hg).H = HFSet.card sub.H := by
  let f : HFSet → HFSet := fun h => grp.op (grp.op g h) (grp.inv g)
  have hf_into : ∀ x, x ∈ sub.H → f x ∈ (sub.conjugate g hg).H := by
    intro x hx
    rw [sub.mem_conjugate_iff hg]
    exact ⟨x, hx, rfl⟩
  have hf_inj : ∀ x y, x ∈ sub.H → y ∈ sub.H → f x = f y → x = y := by
    intro x y hx hy hxy
    have hxG : x ∈ grp.G := sub.H_sub hx
    have hyG : y ∈ grp.G := sub.H_sub hy
    have hgi : grp.inv g ∈ grp.G := grp.inv_closed hg
    have hleft : grp.op g x = grp.op g y :=
      grp.right_cancel hgi (grp.op_closed hg hxG) (grp.op_closed hg hyG) hxy
    exact grp.left_cancel hg hxG hyG hleft
  have hf_surj : ∀ y, y ∈ (sub.conjugate g hg).H → ∃ x ∈ sub.H, y = f x := by
    intro y hy
    rw [sub.mem_conjugate_iff hg] at hy
    obtain ⟨x, hx, hxy⟩ := hy
    exact ⟨x, hx, hxy⟩
  have hcard : HFSet.card sub.H = HFSet.card (sub.conjugate g hg).H :=
    HFSet.card_eq_of_classBij hf_into hf_inj hf_surj
  exact hcard.symm

/-- Si dos subgrupos tienen el mismo portador, sus conjugados (por un `g` fijo)
    también tienen el mismo portador. -/
theorem conjugate_carrier_congr (sub₁ sub₂ : HFSubgroup grp)
    (hH : sub₁.H = sub₂.H) {g : HFSet} (hg : g ∈ grp.G) :
    (sub₁.conjugate g hg).H = (sub₂.conjugate g hg).H := by
  apply HFSet.extensionality
  intro x
  rw [sub₁.mem_conjugate_iff hg, sub₂.mem_conjugate_iff hg, hH]

/-- Conjugar por el neutro no cambia el portador del subgrupo. -/
theorem conjugate_e_carrier_eq (sub : HFSubgroup grp) :
    (sub.conjugate grp.e grp.e_mem).H = sub.H := by
  apply HFSet.extensionality
  intro x
  constructor
  · intro hx
    rw [sub.mem_conjugate_iff grp.e_mem] at hx
    obtain ⟨h, hh, hxeq⟩ := hx
    have hhG : h ∈ grp.G := sub.H_sub hh
    have : x = h := by
      calc
        x = grp.op (grp.op grp.e h) (grp.inv grp.e) := hxeq
        _ = grp.op h (grp.inv grp.e) := by rw [grp.op_id_left hhG]
        _ = grp.op h grp.e := by rw [grp.inv_e]
        _ = h := grp.op_id_right hhG
    rw [this]
    exact hh
  · intro hx
    rw [sub.mem_conjugate_iff grp.e_mem]
    refine ⟨x, hx, ?_⟩
    have hxG : x ∈ grp.G := sub.H_sub hx
    calc
      x = grp.op x grp.e := (grp.op_id_right hxG).symm
      _ = grp.op x (grp.inv grp.e) := by rw [grp.inv_e]
      _ = grp.op (grp.op grp.e x) (grp.inv grp.e) := by rw [grp.op_id_left hxG]


/-- Ley de composición de conjugación en el portador:
    `h(gHg⁻¹)h⁻¹ = (hg)H(hg)⁻¹`. -/
theorem conjugate_conjugate_carrier_eq (sub : HFSubgroup grp)
    {g h : HFSet} (hg : g ∈ grp.G) (hh : h ∈ grp.G) :
    ((sub.conjugate g hg).conjugate h hh).H =
      (sub.conjugate (grp.op h g) (grp.op_closed hh hg)).H := by
  apply HFSet.extensionality
  intro x
  constructor
  · intro hx
    rw [HFSubgroup.mem_conjugate_iff (sub := sub.conjugate g hg) hh] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    rw [sub.mem_conjugate_iff hg] at hy
    obtain ⟨a, ha, rfl⟩ := hy
    have haG : a ∈ grp.G := sub.H_sub ha
    have hgi : grp.inv g ∈ grp.G := grp.inv_closed hg
    have hhi : grp.inv h ∈ grp.G := grp.inv_closed hh
    rw [HFSubgroup.mem_conjugate_iff (sub := sub) (hg := grp.op_closed hh hg)]
    refine ⟨a, ha, ?_⟩
    calc
      grp.op (grp.op h (grp.op (grp.op g a) (grp.inv g))) (grp.inv h)
          = grp.op (grp.op (grp.op h (grp.op g a)) (grp.inv g)) (grp.inv h) := by
              rw [← grp.op_assoc hh (grp.op_closed hg haG) hgi]
      _ = grp.op (grp.op (grp.op (grp.op h g) a) (grp.inv g)) (grp.inv h) := by
            rw [← grp.op_assoc hh hg haG]
      _ = grp.op (grp.op (grp.op h g) a) (grp.op (grp.inv g) (grp.inv h)) := by
            rw [grp.op_assoc (grp.op_closed (grp.op_closed hh hg) haG) hgi hhi]
      _ = grp.op (grp.op (grp.op h g) a) (grp.inv (grp.op h g)) := by
            rw [← grp.inv_op hh hg]
  · intro hx
    rw [HFSubgroup.mem_conjugate_iff (sub := sub) (hg := grp.op_closed hh hg)] at hx
    obtain ⟨a, ha, rfl⟩ := hx
    have haG : a ∈ grp.G := sub.H_sub ha
    have hgi : grp.inv g ∈ grp.G := grp.inv_closed hg
    have hhi : grp.inv h ∈ grp.G := grp.inv_closed hh
    rw [HFSubgroup.mem_conjugate_iff (sub := sub.conjugate g hg) (hg := hh)]
    refine ⟨grp.op (grp.op g a) (grp.inv g), ?_, ?_⟩
    · rw [sub.mem_conjugate_iff hg]
      exact ⟨a, ha, rfl⟩
    · calc
        grp.op (grp.op (grp.op h g) a) (grp.inv (grp.op h g))
            = grp.op (grp.op (grp.op h g) a) (grp.op (grp.inv g) (grp.inv h)) := by
                rw [grp.inv_op hh hg]
        _ = grp.op (grp.op (grp.op (grp.op h g) a) (grp.inv g)) (grp.inv h) := by
              rw [(grp.op_assoc (grp.op_closed (grp.op_closed hh hg) haG) hgi hhi).symm]
        _ = grp.op (grp.op (grp.op h (grp.op g a)) (grp.inv g)) (grp.inv h) := by
              rw [grp.op_assoc hh hg haG]
        _ = grp.op (grp.op h (grp.op (grp.op g a) (grp.inv g))) (grp.inv h) := by
              rw [grp.op_assoc hh (grp.op_closed hg haG) hgi]

/-- Conjugar por `g` y luego por `g⁻¹` devuelve el portador original. -/
theorem conjugate_then_inv_carrier_eq (sub : HFSubgroup grp)
    {g : HFSet} (hg : g ∈ grp.G) :
    ((sub.conjugate g hg).conjugate (grp.inv g) (grp.inv_closed hg)).H = sub.H := by
  have hOp : grp.op (grp.inv g) g = grp.e := grp.op_inv_left hg
  have hOpG : grp.op (grp.inv g) g ∈ grp.G := grp.op_closed (grp.inv_closed hg) hg
  have hConj :
      ((sub.conjugate g hg).conjugate (grp.inv g) (grp.inv_closed hg)).H =
        (sub.conjugate (grp.op (grp.inv g) g) hOpG).H :=
    sub.conjugate_conjugate_carrier_eq hg (grp.inv_closed hg)
  have hMid :
      (sub.conjugate (grp.op (grp.inv g) g) hOpG).H = (sub.conjugate grp.e grp.e_mem).H := by
    apply HFSet.extensionality
    intro x
    constructor
    · intro hx
      rw [sub.mem_conjugate_iff (hg := hOpG)] at hx
      obtain ⟨a, ha, hxa⟩ := hx
      rw [sub.mem_conjugate_iff (hg := grp.e_mem)]
      refine ⟨a, ha, ?_⟩
      calc
        x = grp.op (grp.op (grp.op (grp.inv g) g) a) (grp.inv (grp.op (grp.inv g) g)) := hxa
        _ = grp.op (grp.op grp.e a) (grp.inv grp.e) := by rw [hOp]
    · intro hx
      rw [sub.mem_conjugate_iff (hg := grp.e_mem)] at hx
      obtain ⟨a, ha, hxa⟩ := hx
      rw [sub.mem_conjugate_iff (hg := hOpG)]
      refine ⟨a, ha, ?_⟩
      calc
        x = grp.op (grp.op grp.e a) (grp.inv grp.e) := hxa
        _ = grp.op (grp.op (grp.op (grp.inv g) g) a) (grp.inv (grp.op (grp.inv g) g)) := by
              rw [hOp]
  exact hConj.trans (hMid.trans sub.conjugate_e_carrier_eq)

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

-- ─────────────────────────────────────────────────────────────────
-- Extras (pasos 1–8 del plan de trabajo)
-- ─────────────────────────────────────────────────────────────────

/-- (1) Todo cosete derecho `Ha` es no vacío: contiene a `a`.
    Forma fuerte (elemento explícito). -/
theorem rightCoset_self_mem (sub : HFSubgroup grp) {a : HFSet} (ha : a ∈ grp.G) :
    a ∈ sub.rightCoset a := by
  rw [sub.mem_rightCoset ha]
  exact ⟨grp.e, sub.e_mem, (grp.op_id_left ha).symm⟩

/-- (1, versión existencial) Todo cosete derecho `Ha` es no vacío. -/
theorem rightCoset_nonempty (sub : HFSubgroup grp) {a : HFSet} (ha : a ∈ grp.G) :
    ∃ x, x ∈ sub.rightCoset a :=
  ⟨a, sub.rightCoset_self_mem ha⟩

/-- (2) Alias estándar `_iff` para membresía en cosete derecho. -/
theorem mem_rightCoset_iff (sub : HFSubgroup grp) {a x : HFSet} (ha : a ∈ grp.G) :
    x ∈ sub.rightCoset a ↔ ∃ h ∈ sub.H, x = grp.op h a :=
  sub.mem_rightCoset ha

/-- (3) Reescritura simétrica: igualdad de cosetes iff `cosetEq`. -/
theorem rightCoset_eq_iff (sub : HFSubgroup grp) {a b : HFSet}
    (ha : a ∈ grp.G) (hb : b ∈ grp.G) :
    sub.rightCoset a = sub.rightCoset b ↔ sub.cosetEq a b :=
  (sub.cosetEq_iff_rightCoset_eq ha hb).symm

/-- (4) `cosetEq` es una relación de equivalencia al restringir a `G`. -/
theorem cosetEq_is_equiv_on_G (sub : HFSubgroup grp) :
    (∀ {a : HFSet}, a ∈ grp.G → sub.cosetEq a a) ∧
    (∀ {a b : HFSet}, a ∈ grp.G → b ∈ grp.G → sub.cosetEq a b → sub.cosetEq b a) ∧
    (∀ {a b c : HFSet},
      a ∈ grp.G → b ∈ grp.G → c ∈ grp.G →
      sub.cosetEq a b → sub.cosetEq b c → sub.cosetEq a c) := by
  refine ⟨?_, ?_, ?_⟩
  · intro a ha
    exact sub.cosetEq_refl ha
  · intro a b ha hb hab
    exact sub.cosetEq_symm ha hb hab
  · intro a b c ha hb hc hab hbc
    exact sub.cosetEq_trans ha hb hc hab hbc

/-- (5) Cerradura por multiplicación izquierda de elementos de `H` dentro del cosete `Ha`. -/
theorem rightCoset_mul_mem (sub : HFSubgroup grp) {a h x : HFSet}
    (ha : a ∈ grp.G) (hh : h ∈ sub.H) (hx : x ∈ sub.rightCoset a) :
    grp.op h x ∈ sub.rightCoset a := by
  rw [sub.mem_rightCoset ha] at hx ⊢
  obtain ⟨h₀, hh₀, rfl⟩ := hx
  refine ⟨grp.op h h₀, sub.op_closed hh hh₀, ?_⟩
  exact (grp.op_assoc (sub.H_sub hh) (sub.H_sub hh₀) ha).symm

/-- Si `a ∈ H`, entonces el cosete derecho `Ha` coincide con `H`. -/
theorem rightCoset_eq_subgroup_of_mem (sub : HFSubgroup grp) {a : HFSet}
    (haG : a ∈ grp.G) (haH : a ∈ sub.H) :
    sub.rightCoset a = sub.H := by
  apply HFSet.extensionality
  intro x
  rw [sub.mem_rightCoset haG]
  constructor
  · intro hx
    obtain ⟨h, hh, rfl⟩ := hx
    exact sub.op_closed hh haH
  · intro hxH
    refine ⟨grp.op x (grp.inv a), sub.op_closed hxH (sub.inv_closed haH), ?_⟩
    -- (x·a⁻¹)·a = x
    calc x
        = grp.op x grp.e := (grp.op_id_right (sub.H_sub hxH)).symm
      _ = grp.op x (grp.op (grp.inv a) a) := by rw [grp.op_inv_left haG]
      _ = grp.op (grp.op x (grp.inv a)) a := (grp.op_assoc (sub.H_sub hxH) (grp.inv_closed haG) haG).symm

/-- (6) Versión base de equinumerosidad: si `a ∈ H`, entonces `card(Ha)=card(H)`. -/
theorem rightCoset_equinumerous_H (sub : HFSubgroup grp) {a : HFSet}
    (haG : a ∈ grp.G) (haH : a ∈ sub.H) :
    HFSet.card (sub.rightCoset a) = HFSet.card sub.H := by
  rw [sub.rightCoset_eq_subgroup_of_mem haG haH]

/-- Lema técnico: un punto en la intersección de cosetes produce `cosetEq`. -/
theorem cosetEq_of_mem_inter_rightCoset (sub : HFSubgroup grp)
    {a b x : HFSet} (ha : a ∈ grp.G) (hb : b ∈ grp.G)
    (hx : x ∈ HFSet.inter (sub.rightCoset a) (sub.rightCoset b)) :
    sub.cosetEq a b := by
  rw [HFSet.mem_inter] at hx
  obtain ⟨hxa, hxb⟩ := hx
  rw [sub.mem_rightCoset ha] at hxa
  rw [sub.mem_rightCoset hb] at hxb
  obtain ⟨h₁, hh₁, hx1⟩ := hxa
  obtain ⟨h₂, hh₂, hx2⟩ := hxb
  have hh₁G : h₁ ∈ grp.G := sub.H_sub hh₁
  have hh₂G : h₂ ∈ grp.G := sub.H_sub hh₂
  have hEq : grp.op h₁ a = grp.op h₂ b := hx1.symm.trans hx2
  -- b = ((h₂)⁻¹·h₁)·a
  have hb_eq : b = grp.op (grp.op (grp.inv h₂) h₁) a := by
    calc b
        = grp.op grp.e b := (grp.op_id_left hb).symm
      _ = grp.op (grp.op (grp.inv h₂) h₂) b := by rw [grp.op_inv_left hh₂G]
      _ = grp.op (grp.inv h₂) (grp.op h₂ b) := grp.op_assoc (grp.inv_closed hh₂G) hh₂G hb
      _ = grp.op (grp.inv h₂) (grp.op h₁ a) := by rw [hEq.symm]
      _ = grp.op (grp.op (grp.inv h₂) h₁) a := (grp.op_assoc (grp.inv_closed hh₂G) hh₁G ha).symm
  -- por tanto b·a⁻¹ = (h₂)⁻¹·h₁ ∈ H
  have hmem : grp.op (grp.inv h₂) h₁ ∈ sub.H :=
    sub.op_closed (sub.inv_closed hh₂) hh₁
  have hba : grp.op b (grp.inv a) = grp.op (grp.inv h₂) h₁ := by
    calc grp.op b (grp.inv a)
        = grp.op (grp.op (grp.op (grp.inv h₂) h₁) a) (grp.inv a) := by rw [hb_eq]
      _ = grp.op (grp.op (grp.inv h₂) h₁) (grp.op a (grp.inv a)) :=
            grp.op_assoc (grp.op_closed (grp.inv_closed hh₂G) hh₁G) ha (grp.inv_closed ha)
      _ = grp.op (grp.op (grp.inv h₂) h₁) grp.e := by rw [grp.op_inv_right ha]
      _ = grp.op (grp.inv h₂) h₁ := grp.op_id_right (grp.op_closed (grp.inv_closed hh₂G) hh₁G)
  show grp.op b (grp.inv a) ∈ sub.H
  rw [hba]
  exact hmem

/-- (7) Cobertura de `G` por cosetes derechos: cada `x ∈ G` está en `Hx`. -/
theorem rightCosets_cover_G (sub : HFSubgroup grp) {x : HFSet} (hx : x ∈ grp.G) :
    x ∈ sub.rightCoset x :=
  sub.rightCoset_self_mem hx

/-- (8) Dos cosetes derechos son iguales o disjuntos. -/
theorem rightCoset_eq_or_disjoint (sub : HFSubgroup grp) {a b : HFSet}
    (ha : a ∈ grp.G) (hb : b ∈ grp.G) :
    sub.rightCoset a = sub.rightCoset b ∨
      HFSet.inter (sub.rightCoset a) (sub.rightCoset b) = HFSet.empty := by
  by_cases heq : sub.rightCoset a = sub.rightCoset b
  · exact Or.inl heq
  · right
    apply HFSet.extensionality
    intro x
    constructor
    · intro hx
      have hcos : sub.cosetEq a b := sub.cosetEq_of_mem_inter_rightCoset ha hb hx
      have : sub.rightCoset a = sub.rightCoset b :=
        (sub.cosetEq_iff_rightCoset_eq ha hb).mp hcos
      exact False.elim (heq this)
    · intro hx
      exact False.elim (HFSet.not_mem_empty _ hx)

end HFSubgroup

end HFAlgebra
