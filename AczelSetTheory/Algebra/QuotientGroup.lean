/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- AczelSetTheory/Algebra/QuotientGroup.lean
-- Grupo cociente G/H para H ⊴ G (sobre HFGroup abstracto).
--
-- Diseño:
--   • Portador = sub.cosets (cosetes derechos, ya definidos en CosetCount).
--   • Bajo normalidad, leftCoset g = rightCoset g, por lo que la operación
--     (Hg)(Hh) := H(gh) está bien definida.
--   • Representante: Classical.choose sobre ∃ g ∈ G, C = Hg.
--
-- Público:
--   HFSubgroup.cosetOf            : g ↦ Hg como función G → cosets
--   HFSubgroup.cosetRep           : Classical.choose representante de C ∈ cosets
--   HFSubgroup.cosetRep_mem_G     : cosetRep C ∈ G
--   HFSubgroup.cosetRep_rightCoset_eq : H·(cosetRep C) = C
--   HFSubgroup.quotientOp_welldefined : (a·b) define Hg·Hh bajo normalidad
--   HFSubgroup.quotientOp         : operación binaria sobre cosets (noncomputable)
--   HFSubgroup.quotientInv        : inversión sobre cosets (noncomputable)
--   HFSubgroup.quotientOp_cosetOf : quotientOp (Hg) (Hh) = H(g·h)
--   HFSubgroup.quotientInv_cosetOf: quotientInv (Hg) = H(g⁻¹)
--   quotientGroup grp sub hn       : HFGroup sobre sub.cosets
--   quotientHom grp sub hn         : HFGroupHom grp (quotientGroup grp sub hn)
--   quotientHom_f_eq               : (quotientHom ...).f g = sub.rightCoset g
--   ker_quotientHom_eq             : ker (quotientHom ...) = sub  (igualdad como HFSet)
--
-- Correspondencia con Peano/GroupTheory/QuotientGroup.lean:
--   Peano quotientCarrier G H      → sub.cosets
--   Peano cosetRepOf G H C         → sub.cosetRep C
--   Peano quotientOp_welldefined   → HFSubgroup.quotientOp_welldefined
--   Peano quotientOp G H hn        → HFSubgroup.quotientOp
--   Peano quotientGroup G H hn     → quotientGroup grp sub hn
--   Peano quotientHomomorphism     → quotientHom grp sub hn

import AczelSetTheory.Algebra.NormalSubgroup
import AczelSetTheory.Algebra.CosetCount

namespace HFAlgebra

open HFSet

variable {grp : HFGroup}

namespace HFSubgroup

-- ─────────────────────────────────────────────────────────────────
-- §1. cosetOf y representantes
-- ─────────────────────────────────────────────────────────────────

/-- Coseto de `g`: `Hg` (cosete derecho). -/
def cosetOf (sub : HFSubgroup grp) (g : HFSet) : HFSet := sub.rightCoset g

theorem cosetOf_mem_cosets (sub : HFSubgroup grp) {g : HFSet} (hg : g ∈ grp.G) :
    sub.cosetOf g ∈ sub.cosets := by
  rw [mem_cosets]; exact ⟨g, hg, rfl⟩

/-- Caracterización: `C ∈ cosets` produce existencia de representante. -/
theorem exists_rep_of_mem_cosets (sub : HFSubgroup grp) {C : HFSet}
    (hC : C ∈ sub.cosets) : ∃ g, g ∈ grp.G ∧ C = sub.rightCoset g :=
  (mem_cosets.mp hC)

/-- Representante canónico de un coseto (vía elección clásica). -/
noncomputable def cosetRep (sub : HFSubgroup grp) (C : HFSet) : HFSet :=
  if h : ∃ g, g ∈ grp.G ∧ C = sub.rightCoset g then h.choose else grp.e

theorem cosetRep_mem_G (sub : HFSubgroup grp) {C : HFSet}
    (hC : C ∈ sub.cosets) : sub.cosetRep C ∈ grp.G := by
  have hex := sub.exists_rep_of_mem_cosets hC
  unfold cosetRep
  rw [dif_pos hex]
  exact hex.choose_spec.1

theorem cosetRep_rightCoset_eq (sub : HFSubgroup grp) {C : HFSet}
    (hC : C ∈ sub.cosets) : sub.rightCoset (sub.cosetRep C) = C := by
  have hex := sub.exists_rep_of_mem_cosets hC
  unfold cosetRep
  rw [dif_pos hex]
  exact hex.choose_spec.2.symm

-- ─────────────────────────────────────────────────────────────────
-- §2. Bien-definición de la operación bajo normalidad
-- ─────────────────────────────────────────────────────────────────

/-- Bajo normalidad: si `Hg₁ = Hg₂` entonces `(b·g₁⁻¹)·(g₁ ·...·) `…
    forma técnica: el conjugado de un elemento de H sigue en H. -/
private theorem conj_mem_of_normal (sub : HFSubgroup grp) (hn : sub.isNormal)
    {g h : HFSet} (hg : g ∈ grp.G) (hh : h ∈ sub.H) :
    grp.op (grp.op (grp.inv g) h) g ∈ sub.H := by
  have := hn (grp.inv g) h (grp.inv_closed hg) hh
  rwa [grp.inv_inv hg] at this

/-- Bien-definición: si `Hg = Hg'` y `Hh = Hh'`, entonces `H(g·h) = H(g'·h')`
    (necesita normalidad para mover h al frente). -/
theorem quotientOp_welldefined (sub : HFSubgroup grp) (hn : sub.isNormal)
    {g g' h h' : HFSet}
    (hg : g ∈ grp.G) (hg' : g' ∈ grp.G) (hh : h ∈ grp.G) (hh' : h' ∈ grp.G)
    (hgg' : sub.rightCoset g = sub.rightCoset g')
    (hhh' : sub.rightCoset h = sub.rightCoset h') :
    sub.rightCoset (grp.op g h) = sub.rightCoset (grp.op g' h') := by
  -- Vía cosetEq: g'·g⁻¹ ∈ H y h'·h⁻¹ ∈ H ⟹ (g'·h')·(g·h)⁻¹ ∈ H
  have heq_g : grp.op g' (grp.inv g) ∈ sub.H :=
    (sub.cosetEq_iff_rightCoset_eq hg hg').mpr hgg'
  have heq_h : grp.op h' (grp.inv h) ∈ sub.H :=
    (sub.cosetEq_iff_rightCoset_eq hh hh').mpr hhh'
  apply (sub.cosetEq_iff_rightCoset_eq (grp.op_closed hg hh) (grp.op_closed hg' hh')).mp
  show grp.op (grp.op g' h') (grp.inv (grp.op g h)) ∈ sub.H
  -- (g'·h')·(g·h)⁻¹ = g'·h'·h⁻¹·g⁻¹ = g'·(h'·h⁻¹)·g⁻¹ = (g'·g⁻¹)·(g·(h'·h⁻¹)·g⁻¹)
  have hghinv : grp.inv (grp.op g h) = grp.op (grp.inv h) (grp.inv g) := grp.inv_op hg hh
  have hh_h' := grp.op_closed hh' (grp.inv_closed hh)  -- h'·h⁻¹ ∈ G
  have hgconj : grp.op (grp.op g (grp.op h' (grp.inv h))) (grp.inv g) ∈ sub.H :=
    hn g (grp.op h' (grp.inv h)) hg heq_h
  -- (g'·g⁻¹) · (g·(h'·h⁻¹)·g⁻¹) ∈ H
  have hprod : grp.op (grp.op g' (grp.inv g))
                      (grp.op (grp.op g (grp.op h' (grp.inv h))) (grp.inv g)) ∈ sub.H :=
    sub.op_closed heq_g hgconj
  -- Igualdad algebraica
  have key : grp.op (grp.op g' h') (grp.op (grp.inv h) (grp.inv g)) =
             grp.op (grp.op g' (grp.inv g))
                    (grp.op (grp.op g (grp.op h' (grp.inv h))) (grp.inv g)) := by
    have hgi := grp.inv_closed hg
    have hhi := grp.inv_closed hh
    -- LHS = g'·h'·h⁻¹·g⁻¹
    -- RHS = g'·g⁻¹·g·(h'·h⁻¹)·g⁻¹ = g'·(h'·h⁻¹)·g⁻¹  (tras simplificar g⁻¹·g)
    calc grp.op (grp.op g' h') (grp.op (grp.inv h) (grp.inv g))
        = grp.op g' (grp.op h' (grp.op (grp.inv h) (grp.inv g))) :=
              grp.op_assoc hg' hh' (grp.op_closed hhi hgi)
      _ = grp.op g' (grp.op (grp.op h' (grp.inv h)) (grp.inv g)) := by
              rw [← grp.op_assoc hh' hhi hgi]
      _ = grp.op g' (grp.op grp.e (grp.op (grp.op h' (grp.inv h)) (grp.inv g))) := by
              rw [grp.op_id_left (grp.op_closed (grp.op_closed hh' hhi) hgi)]
      _ = grp.op g' (grp.op (grp.op (grp.inv g) g)
                            (grp.op (grp.op h' (grp.inv h)) (grp.inv g))) := by
              rw [← grp.op_inv_left hg]
      _ = grp.op g' (grp.op (grp.inv g)
                            (grp.op g (grp.op (grp.op h' (grp.inv h)) (grp.inv g)))) := by
              rw [grp.op_assoc hgi hg (grp.op_closed (grp.op_closed hh' hhi) hgi)]
      _ = grp.op (grp.op g' (grp.inv g))
                 (grp.op g (grp.op (grp.op h' (grp.inv h)) (grp.inv g))) :=
              (grp.op_assoc hg' hgi (grp.op_closed hg
                (grp.op_closed (grp.op_closed hh' hhi) hgi))).symm
      _ = grp.op (grp.op g' (grp.inv g))
                 (grp.op (grp.op g (grp.op h' (grp.inv h))) (grp.inv g)) := by
              rw [grp.op_assoc hg (grp.op_closed hh' hhi) hgi]
  rw [hghinv, key]
  exact hprod

-- ─────────────────────────────────────────────────────────────────
-- §3. Operación e inversión sobre cosets
-- ─────────────────────────────────────────────────────────────────

/-- Operación cociente: `C₁ · C₂ := H·(rep C₁ · rep C₂)`. -/
abbrev quotientOp (sub : HFSubgroup grp) (C₁ C₂ : HFSet) : HFSet :=
  sub.rightCoset (grp.op (sub.cosetRep C₁) (sub.cosetRep C₂))

/-- Inversión cociente: `C⁻¹ := H·(rep C)⁻¹`. -/
abbrev quotientInv (sub : HFSubgroup grp) (C : HFSet) : HFSet :=
  sub.rightCoset (grp.inv (sub.cosetRep C))

/-- Identidad cociente: `H` (el coseto del neutro). -/
def quotientId (sub : HFSubgroup grp) : HFSet := sub.rightCoset grp.e

-- ─────────────────────────────────────────────────────────────────
-- §4. Ecuaciones clave: cosetOf es morfismo
-- ─────────────────────────────────────────────────────────────────

theorem quotientOp_cosetOf (sub : HFSubgroup grp) (hn : sub.isNormal)
    {g h : HFSet} (hg : g ∈ grp.G) (hh : h ∈ grp.G) :
    sub.quotientOp (sub.cosetOf g) (sub.cosetOf h) = sub.cosetOf (grp.op g h) := by
  unfold quotientOp cosetOf
  apply sub.quotientOp_welldefined hn
    (sub.cosetRep_mem_G (sub.cosetOf_mem_cosets hg))
    hg
    (sub.cosetRep_mem_G (sub.cosetOf_mem_cosets hh))
    hh
  · exact sub.cosetRep_rightCoset_eq (sub.cosetOf_mem_cosets hg)
  · exact sub.cosetRep_rightCoset_eq (sub.cosetOf_mem_cosets hh)

theorem quotientInv_cosetOf (sub : HFSubgroup grp) (hn : sub.isNormal)
    {g : HFSet} (hg : g ∈ grp.G) :
    sub.quotientInv (sub.cosetOf g) = sub.cosetOf (grp.inv g) := by
  unfold quotientInv cosetOf
  -- Necesitamos: rightCoset(inv (rep Hg)) = rightCoset(inv g)
  -- Por bien-definición aplicada a g₁=rep(Hg), g₂=g, h₁=h₂=e... no, mejor directo
  -- Tenemos rightCoset (rep Hg) = Hg. Queremos rightCoset(inv(rep Hg)) = rightCoset(inv g).
  -- Es decir: cosetEq (inv (rep Hg)) (inv g): (inv g) · (rep Hg) ∈ H.
  have hrep := sub.cosetRep_mem_G (sub.cosetOf_mem_cosets hg)
  have hreq : sub.rightCoset (sub.cosetRep (sub.cosetOf g)) = sub.rightCoset g :=
    sub.cosetRep_rightCoset_eq (sub.cosetOf_mem_cosets hg)
  -- De `Hg' = Hg` (donde g' = rep Hg) sacamos `g · g'⁻¹ ∈ H` o `g'·g⁻¹ ∈ H`
  -- cosetEq g g' ↔ g'·g⁻¹ ∈ H
  have hcoseq : grp.op g (grp.inv (sub.cosetRep (sub.cosetOf g))) ∈ sub.H := by
    -- de Hg' = Hg, por cosetEq_iff_rightCoset_eq g' g
    have := (sub.cosetEq_iff_rightCoset_eq hrep hg).mpr hreq
    -- this : cosetEq g' g = g · g'⁻¹ ∈ H. ¡Exacto!
    exact this
  -- Objetivo: rightCoset (inv g') = rightCoset (inv g)
  -- cosetEq_iff: (inv g) · (inv (inv g')) = (inv g)·g' ∈ H
  apply (sub.cosetEq_iff_rightCoset_eq (grp.inv_closed hrep) (grp.inv_closed hg)).mp
  show grp.op (grp.inv g) (grp.inv (grp.inv (sub.cosetRep (sub.cosetOf g)))) ∈ sub.H
  rw [grp.inv_inv hrep]
  -- (inv g)·g' ∈ H. Por normalidad: g·(g·g'⁻¹⁻¹)·g⁻¹ … más simple:
  -- (inv g)·g' = (inv g)·g'·g·(inv g) · ... no. Directo:
  -- (inv g)·g' = (inv g)·(g·g'⁻¹)⁻¹·(g'⁻¹)⁻¹... más simple:
  -- (inv g)·g' = (inv g)·(g·g'⁻¹)⁻¹·g = inv g · g·g'⁻¹⁻¹·g  no, vamos:
  -- Sabemos g·g'⁻¹ ∈ H. Por normalidad inv g · (g·g'⁻¹) · g ∈ H
  -- = (inv g·g)·g'⁻¹·g = g'⁻¹·g. Pero queremos (inv g)·g'.
  -- Mejor: usar inverso. (g·g'⁻¹)⁻¹ = g'·g⁻¹ ∈ H (sub.inv_closed).
  -- Por normalidad: (inv g)·(g'·g⁻¹)·g ∈ H, igual a (inv g)·g'·g⁻¹·g = (inv g)·g'.
  have hinv_in : grp.op (sub.cosetRep (sub.cosetOf g)) (grp.inv g) ∈ sub.H := by
    have := sub.inv_closed hcoseq
    rwa [grp.inv_op hg (grp.inv_closed hrep), grp.inv_inv hrep] at this
  -- aplicar normalidad: inv g · (g'·g⁻¹) · g  (es (inv g)·...·(inv (inv g)))
  have hconj :
      grp.op (grp.op (grp.inv g) (grp.op (sub.cosetRep (sub.cosetOf g)) (grp.inv g))) g ∈ sub.H :=
    sub.conj_mem_of_normal hn hg hinv_in
  -- Simplificar: (inv g)·(g'·g⁻¹)·g = (inv g)·g'·(g⁻¹·g) = (inv g)·g'
  have hsimp : grp.op (grp.op (grp.inv g) (grp.op (sub.cosetRep (sub.cosetOf g)) (grp.inv g))) g =
               grp.op (grp.inv g) (sub.cosetRep (sub.cosetOf g)) := by
    have hgi := grp.inv_closed hg
    calc grp.op (grp.op (grp.inv g) (grp.op (sub.cosetRep (sub.cosetOf g)) (grp.inv g))) g
        = grp.op (grp.op (grp.op (grp.inv g) (sub.cosetRep (sub.cosetOf g))) (grp.inv g)) g := by
              rw [grp.op_assoc hgi hrep hgi]
      _ = grp.op (grp.op (grp.inv g) (sub.cosetRep (sub.cosetOf g))) (grp.op (grp.inv g) g) :=
              grp.op_assoc (grp.op_closed hgi hrep) hgi hg
      _ = grp.op (grp.op (grp.inv g) (sub.cosetRep (sub.cosetOf g))) grp.e := by
              rw [grp.op_inv_left hg]
      _ = grp.op (grp.inv g) (sub.cosetRep (sub.cosetOf g)) :=
              grp.op_id_right (grp.op_closed hgi hrep)
  rw [hsimp] at hconj
  exact hconj

-- ─────────────────────────────────────────────────────────────────
-- §5. Estructura HFGroup sobre G/H
-- ─────────────────────────────────────────────────────────────────

end HFSubgroup

/-- El grupo cociente `G/H` para `H ⊴ G`. -/
abbrev quotientGroup (grp : HFGroup) (sub : HFSubgroup grp)
    (hn : sub.isNormal) : HFGroup where
  G   := sub.cosets
  op  := sub.quotientOp
  e   := sub.quotientId
  inv := sub.quotientInv
  e_mem := by
    unfold HFSubgroup.quotientId
    exact sub.cosetOf_mem_cosets grp.e_mem
  op_closed := by
    intro C₁ C₂ hC₁ hC₂
    show sub.quotientOp C₁ C₂ ∈ sub.cosets
    unfold HFSubgroup.quotientOp
    rw [HFSubgroup.mem_cosets]
    exact ⟨grp.op (sub.cosetRep C₁) (sub.cosetRep C₂),
            grp.op_closed (sub.cosetRep_mem_G hC₁) (sub.cosetRep_mem_G hC₂), rfl⟩
  inv_closed := by
    intro C hC
    show sub.quotientInv C ∈ sub.cosets
    unfold HFSubgroup.quotientInv
    rw [HFSubgroup.mem_cosets]
    exact ⟨grp.inv (sub.cosetRep C), grp.inv_closed (sub.cosetRep_mem_G hC), rfl⟩
  op_assoc := by
    intro C₁ C₂ C₃ h₁ h₂ h₃
    have hr₁ := sub.cosetRep_mem_G h₁
    have hr₂ := sub.cosetRep_mem_G h₂
    have hr₃ := sub.cosetRep_mem_G h₃
    have e₁ : sub.rightCoset (sub.cosetRep C₁) = C₁ := sub.cosetRep_rightCoset_eq h₁
    have e₂ : sub.rightCoset (sub.cosetRep C₂) = C₂ := sub.cosetRep_rightCoset_eq h₂
    have e₃ : sub.rightCoset (sub.cosetRep C₃) = C₃ := sub.cosetRep_rightCoset_eq h₃
    show sub.quotientOp (sub.quotientOp C₁ C₂) C₃ = sub.quotientOp C₁ (sub.quotientOp C₂ C₃)
    calc sub.quotientOp (sub.quotientOp C₁ C₂) C₃
        = sub.quotientOp (sub.quotientOp (sub.cosetOf (sub.cosetRep C₁))
                                          (sub.cosetOf (sub.cosetRep C₂)))
                          (sub.cosetOf (sub.cosetRep C₃)) := by
              show _ = sub.quotientOp (sub.quotientOp (sub.rightCoset (sub.cosetRep C₁))
                                          (sub.rightCoset (sub.cosetRep C₂)))
                                          (sub.rightCoset (sub.cosetRep C₃))
              rw [e₁, e₂, e₃]
      _ = sub.quotientOp (sub.cosetOf (grp.op (sub.cosetRep C₁) (sub.cosetRep C₂)))
                         (sub.cosetOf (sub.cosetRep C₃)) := by
              rw [sub.quotientOp_cosetOf hn hr₁ hr₂]
      _ = sub.cosetOf (grp.op (grp.op (sub.cosetRep C₁) (sub.cosetRep C₂)) (sub.cosetRep C₃)) :=
              sub.quotientOp_cosetOf hn (grp.op_closed hr₁ hr₂) hr₃
      _ = sub.cosetOf (grp.op (sub.cosetRep C₁) (grp.op (sub.cosetRep C₂) (sub.cosetRep C₃))) := by
              rw [grp.op_assoc hr₁ hr₂ hr₃]
      _ = sub.quotientOp (sub.cosetOf (sub.cosetRep C₁))
                         (sub.cosetOf (grp.op (sub.cosetRep C₂) (sub.cosetRep C₃))) :=
              (sub.quotientOp_cosetOf hn hr₁ (grp.op_closed hr₂ hr₃)).symm
      _ = sub.quotientOp (sub.cosetOf (sub.cosetRep C₁))
                         (sub.quotientOp (sub.cosetOf (sub.cosetRep C₂))
                                          (sub.cosetOf (sub.cosetRep C₃))) := by
              rw [sub.quotientOp_cosetOf hn hr₂ hr₃]
      _ = sub.quotientOp C₁ (sub.quotientOp C₂ C₃) := by
              show sub.quotientOp (sub.rightCoset (sub.cosetRep C₁))
                                   (sub.quotientOp (sub.rightCoset (sub.cosetRep C₂))
                                                    (sub.rightCoset (sub.cosetRep C₃))) = _
              rw [e₁, e₂, e₃]
  op_id_left := by
    intro C hC
    have hr := sub.cosetRep_mem_G hC
    have er : sub.rightCoset (sub.cosetRep C) = C := sub.cosetRep_rightCoset_eq hC
    show sub.quotientOp sub.quotientId C = C
    unfold HFSubgroup.quotientId
    calc sub.quotientOp (sub.rightCoset grp.e) C
        = sub.quotientOp (sub.cosetOf grp.e) (sub.cosetOf (sub.cosetRep C)) := by
              show _ = sub.quotientOp (sub.rightCoset grp.e) (sub.rightCoset (sub.cosetRep C))
              rw [er]
      _ = sub.cosetOf (grp.op grp.e (sub.cosetRep C)) :=
              sub.quotientOp_cosetOf hn grp.e_mem hr
      _ = sub.cosetOf (sub.cosetRep C) := by rw [grp.op_id_left hr]
      _ = C := er
  op_inv_left := by
    intro C hC
    have hr := sub.cosetRep_mem_G hC
    have er : sub.rightCoset (sub.cosetRep C) = C := sub.cosetRep_rightCoset_eq hC
    show sub.quotientOp (sub.quotientInv C) C = sub.quotientId
    unfold HFSubgroup.quotientInv HFSubgroup.quotientId
    calc sub.quotientOp (sub.rightCoset (grp.inv (sub.cosetRep C))) C
        = sub.quotientOp (sub.cosetOf (grp.inv (sub.cosetRep C)))
                          (sub.cosetOf (sub.cosetRep C)) := by
              show _ = sub.quotientOp (sub.rightCoset (grp.inv (sub.cosetRep C)))
                                       (sub.rightCoset (sub.cosetRep C))
              rw [er]
      _ = sub.cosetOf (grp.op (grp.inv (sub.cosetRep C)) (sub.cosetRep C)) :=
              sub.quotientOp_cosetOf hn (grp.inv_closed hr) hr
      _ = sub.cosetOf grp.e := by rw [grp.op_inv_left hr]
      _ = sub.rightCoset grp.e := rfl

namespace HFSubgroup

-- ─────────────────────────────────────────────────────────────────
-- §6. Homomorfismo canónico π : G → G/H
-- ─────────────────────────────────────────────────────────────────

end HFSubgroup

/-- El homomorfismo canónico `π : G → G/H`, definido por `π(g) = Hg`. -/
abbrev quotientHom (grp : HFGroup) (sub : HFSubgroup grp)
    (hn : sub.isNormal) : HFGroupHom grp (quotientGroup grp sub hn) where
  f      := sub.cosetOf
  f_mem  := fun hg => sub.cosetOf_mem_cosets hg
  f_hom  := fun ha hb => (sub.quotientOp_cosetOf hn ha hb).symm

/-- El homomorfismo canónico evalúa `g ↦ rightCoset g`. -/
theorem quotientHom_f_eq (grp : HFGroup) (sub : HFSubgroup grp)
    (hn : sub.isNormal) (g : HFSet) :
    (quotientHom grp sub hn).f g = sub.rightCoset g := rfl

/-- El núcleo del homomorfismo canónico es `H` (como HFSet). -/
theorem ker_quotientHom_eq (grp : HFGroup) (sub : HFSubgroup grp)
    (hn : sub.isNormal) :
    ((quotientHom grp sub hn).ker).H = sub.H := by
  apply HFSet.extensionality
  intro x
  -- ker.H = sep G.G (fun a => π(a) = quotientId), quotientId = sub.rightCoset e = H
  -- π(a) = rightCoset a. Así a ∈ ker ↔ a ∈ G ∧ rightCoset a = H.
  -- rightCoset a = H ↔ a ∈ H (lema rightCoset_eq_subgroup_of_mem en una dir; otra dir: e ∈ Ha = H ⟹ a = e·... ∈ H).
  constructor
  · intro hx
    have hx' : x ∈ HFSet.sep grp.G (fun a => (quotientHom grp sub hn).f a =
                                              (quotientGroup grp sub hn).e) :=
      hx
    rw [HFSet.mem_sep] at hx'
    obtain ⟨hxG, hxe⟩ := hx'
    -- hxe : rightCoset x = quotientId = rightCoset e
    have hxe' : sub.rightCoset x = sub.rightCoset grp.e := hxe
    -- Usar cosetEq_iff: cosetEq x e ↔ rightCoset x = rightCoset e
    -- cosetEq x e := e · inv x ∈ H, equivalente a inv x ∈ H, equiv a x ∈ H (cerradura).
    have hcoseq : grp.op grp.e (grp.inv x) ∈ sub.H :=
      (sub.cosetEq_iff_rightCoset_eq hxG grp.e_mem).mpr hxe'
    rw [grp.op_id_left (grp.inv_closed hxG)] at hcoseq
    -- inv x ∈ H ⟹ x = inv(inv x) ∈ H
    have := sub.inv_closed hcoseq
    rwa [grp.inv_inv hxG] at this
  · intro hxH
    have hxG : x ∈ grp.G := sub.H_sub hxH
    show x ∈ HFSet.sep grp.G (fun a => (quotientHom grp sub hn).f a =
                                       (quotientGroup grp sub hn).e)
    rw [HFSet.mem_sep]
    refine ⟨hxG, ?_⟩
    show sub.rightCoset x = sub.rightCoset grp.e
    apply (sub.cosetEq_iff_rightCoset_eq hxG grp.e_mem).mp
    show grp.op grp.e (grp.inv x) ∈ sub.H
    rw [grp.op_id_left (grp.inv_closed hxG)]
    exact sub.inv_closed hxH

end HFAlgebra
