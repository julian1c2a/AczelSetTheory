/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- AczelSetTheory/Algebra/FirstIsomorphism.lean
-- Primer Teorema de Isomorfía: G/ker φ ≅ im φ.
--
-- Diseño:
--   • Injective/Surjective/Bijective como Props sobre HFGroupHom.
--   • imageInclusion : im φ ↪ H (homomorfismo inyectivo).
--   • quotientHom_surjective : π : G → G/N es sobreyectivo (cualquier N ⊴ G).
--   • firstIsoMap : G/ker φ → im φ, C ↦ φ(cosetRep C).
--   • Bien-definida, homomorfismo, biyectiva.
--
-- Público:
--   HFGroupHom.Injective         : Prop
--   HFGroupHom.Surjective        : Prop
--   HFGroupHom.Bijective         : Prop
--   quotientHom_surjective       : π es sobreyectiva
--   HFGroupHom.imageInclusion    : im φ → H
--   imageInclusion_injective     : inclusión inyectiva
--   HFGroupHom.firstIsoMap       : G/ker φ → im φ
--   firstIsoMap_welldefined      : φ(Hg) = φ.f g
--   firstIsoMap_injective        : φ inyectiva
--   firstIsoMap_surjective       : φ sobreyectiva
--   firstIsoMap_bijective        : φ biyectiva  -- 1er Teorema de Isomorfía

import AczelSetTheory.Algebra.QuotientGroup

namespace HFAlgebra

open HFSet

-- ─────────────────────────────────────────────────────────────────
-- §1. Inyectividad, sobreyectividad, biyectividad
-- ─────────────────────────────────────────────────────────────────

namespace HFGroupHom

variable {G H : HFGroup} (φ : HFGroupHom G H)

/-- Homomorfismo inyectivo. -/
def Injective : Prop :=
  ∀ ⦃a b : HFSet⦄, a ∈ G.G → b ∈ G.G → φ.f a = φ.f b → a = b

/-- Homomorfismo sobreyectivo (sobre el grupo de llegada). -/
def Surjective : Prop :=
  ∀ ⦃y : HFSet⦄, y ∈ H.G → ∃ x, x ∈ G.G ∧ φ.f x = y

/-- Homomorfismo biyectivo. -/
def Bijective : Prop := φ.Injective ∧ φ.Surjective

end HFGroupHom

-- ─────────────────────────────────────────────────────────────────
-- §2. π : G → G/N es sobreyectivo
-- ─────────────────────────────────────────────────────────────────

/-- La proyección canónica `π : G → G/N` es sobreyectiva: todo coseto tiene preimagen. -/
theorem quotientHom_surjective (grp : HFGroup) (sub : HFSubgroup grp)
    (hn : sub.isNormal) : (quotientHom grp sub hn).Surjective := by
  intro C hC
  refine ⟨sub.cosetRep C, sub.cosetRep_mem_G hC, ?_⟩
  -- (quotientHom ...).f = sub.cosetOf = sub.rightCoset
  show sub.rightCoset (sub.cosetRep C) = C
  exact sub.cosetRep_rightCoset_eq hC

-- ─────────────────────────────────────────────────────────────────
-- §3. ι : im φ ↪ H (inclusión)
-- ─────────────────────────────────────────────────────────────────

namespace HFGroupHom

variable {G H : HFGroup} (φ : HFGroupHom G H)

/-- La inclusión `ι : im φ → H` como homomorfismo de grupos. -/
def imageInclusion : HFGroupHom φ.image.toHFGroup H where
  f      := fun y => y
  f_mem  := fun hy => φ.image.H_sub hy
  f_hom  := fun _ _ => rfl

theorem imageInclusion_injective : φ.imageInclusion.Injective :=
  fun _ _ _ _ heq => heq

end HFGroupHom

-- ─────────────────────────────────────────────────────────────────
-- §4. φ̄ : G/ker φ → im φ — el isomorfismo
-- ─────────────────────────────────────────────────────────────────

namespace HFGroupHom

variable {G H : HFGroup} (φ : HFGroupHom G H)

/-- La función subyacente `f̄ : C ↦ φ(cosetRep C)`, que enviará un coseto a su imagen. -/
private abbrev firstIsoFun (C : HFSet) : HFSet :=
  φ.f (φ.ker.cosetRep C)

/-- **Bien-definición** sobre representantes: si `g ∈ G`,
    `f̄(Hg) = φ(g)`. La elección del representante no afecta. -/
theorem firstIsoFun_eq {g : HFSet} (hg : g ∈ G.G) :
    φ.firstIsoFun (φ.ker.rightCoset g) = φ.f g := by
  unfold firstIsoFun
  -- r = cosetRep (rightCoset g); rightCoset r = rightCoset g ⟹ g · r⁻¹ ∈ ker
  have hC_mem : φ.ker.rightCoset g ∈ φ.ker.cosets :=
    φ.ker.cosetOf_mem_cosets hg
  have hr_G : φ.ker.cosetRep (φ.ker.rightCoset g) ∈ G.G :=
    φ.ker.cosetRep_mem_G hC_mem
  have hreq : φ.ker.rightCoset (φ.ker.cosetRep (φ.ker.rightCoset g))
              = φ.ker.rightCoset g :=
    φ.ker.cosetRep_rightCoset_eq hC_mem
  -- De rightCoset r = rightCoset g, deducimos g · r⁻¹ ∈ ker
  have hgr : G.op g (G.inv (φ.ker.cosetRep (φ.ker.rightCoset g))) ∈ φ.ker.H :=
    (φ.ker.cosetEq_iff_rightCoset_eq hr_G hg).mpr hreq
  -- ker.H = sep G.G (fun a => φ.f a = e_H)
  have hgr' : G.op g (G.inv (φ.ker.cosetRep (φ.ker.rightCoset g))) ∈
              HFSet.sep G.G (fun a => φ.f a = H.e) := hgr
  have hker' := (HFSet.mem_sep _ _ _).mp hgr'
  have hphi : φ.f (G.op g (G.inv (φ.ker.cosetRep (φ.ker.rightCoset g)))) = H.e :=
    hker'.2
  -- φ(g · r⁻¹) = φ(g) · φ(r)⁻¹
  rw [φ.f_hom hg (G.inv_closed hr_G), φ.hom_inv hr_G] at hphi
  -- φ(g) · φ(r)⁻¹ = e_H ⟹ φ(g) = φ(r)
  have hg_img := φ.f_mem hg
  have hr_img := φ.f_mem hr_G
  -- Multiplicar a la derecha por φ(r)
  have hmul :
      H.op (H.op (φ.f g) (H.inv (φ.f (φ.ker.cosetRep (φ.ker.rightCoset g)))))
           (φ.f (φ.ker.cosetRep (φ.ker.rightCoset g)))
      = H.op H.e (φ.f (φ.ker.cosetRep (φ.ker.rightCoset g))) := by
    rw [hphi]
  show φ.f (φ.ker.cosetRep (φ.ker.rightCoset g)) = φ.f g
  rw [H.op_assoc hg_img (H.inv_closed hr_img) hr_img,
      H.op_inv_left hr_img,
      H.op_id_right hg_img,
      H.op_id_left hr_img] at hmul
  exact hmul.symm

/-- El **mapa del Primer Teorema de Isomorfía**: φ̄ : G/ker φ → im φ. -/
abbrev firstIsoMap :
    HFGroupHom (quotientGroup G φ.ker φ.ker_isNormal) φ.image.toHFGroup where
  f      := φ.firstIsoFun
  f_mem  := by
    intro C hC
    show φ.firstIsoFun C ∈ φ.image.H
    unfold firstIsoFun
    show φ.f (φ.ker.cosetRep C) ∈ HFSet.sep H.G (fun b => ∃ a ∈ G.G, φ.f a = b)
    rw [HFSet.mem_sep]
    refine ⟨φ.f_mem (φ.ker.cosetRep_mem_G hC), ?_⟩
    exact ⟨φ.ker.cosetRep C, φ.ker.cosetRep_mem_G hC, rfl⟩
  f_hom  := by
    intro C₁ C₂ hC₁ hC₂
    have hr₁ := φ.ker.cosetRep_mem_G hC₁
    have hr₂ := φ.ker.cosetRep_mem_G hC₂
    show φ.firstIsoFun (φ.ker.quotientOp C₁ C₂) =
         H.op (φ.firstIsoFun C₁) (φ.firstIsoFun C₂)
    have hop : φ.ker.quotientOp C₁ C₂ =
        φ.ker.rightCoset (G.op (φ.ker.cosetRep C₁) (φ.ker.cosetRep C₂)) := rfl
    rw [hop, φ.firstIsoFun_eq (G.op_closed hr₁ hr₂), φ.f_hom hr₁ hr₂]

theorem firstIsoMap_welldefined {g : HFSet} (hg : g ∈ G.G) :
    φ.firstIsoMap.f (φ.ker.rightCoset g) = φ.f g :=
  φ.firstIsoFun_eq hg

/-- φ̄ es **inyectiva**. -/
theorem firstIsoMap_injective : φ.firstIsoMap.Injective := by
  intro C₁ C₂ hC₁ hC₂ heq
  -- heq : φ(rep C₁) = φ(rep C₂)
  have hr₁ := φ.ker.cosetRep_mem_G hC₁
  have hr₂ := φ.ker.cosetRep_mem_G hC₂
  have e₁ : φ.ker.rightCoset (φ.ker.cosetRep C₁) = C₁ :=
    φ.ker.cosetRep_rightCoset_eq hC₁
  have e₂ : φ.ker.rightCoset (φ.ker.cosetRep C₂) = C₂ :=
    φ.ker.cosetRep_rightCoset_eq hC₂
  rw [← e₁, ← e₂]
  -- Basta mostrar rightCoset r₁ = rightCoset r₂, vía cosetEq: r₂ · r₁⁻¹ ∈ ker
  apply (φ.ker.cosetEq_iff_rightCoset_eq hr₁ hr₂).mp
  show G.op (φ.ker.cosetRep C₂) (G.inv (φ.ker.cosetRep C₁)) ∈ φ.ker.H
  show G.op (φ.ker.cosetRep C₂) (G.inv (φ.ker.cosetRep C₁)) ∈
       HFSet.sep G.G (fun a => φ.f a = H.e)
  rw [HFSet.mem_sep]
  refine ⟨G.op_closed hr₂ (G.inv_closed hr₁), ?_⟩
  -- φ(r₂ · r₁⁻¹) = φ(r₂)·φ(r₁)⁻¹ = φ(r₁)·φ(r₁)⁻¹ = e_H   (por heq)
  rw [φ.f_hom hr₂ (G.inv_closed hr₁), φ.hom_inv hr₁]
  -- heq : φ.firstIsoMap.f C₁ = φ.firstIsoMap.f C₂
  -- φ.firstIsoMap.f Cᵢ = firstIsoFun Cᵢ = φ.f (rep Cᵢ)
  have heq' : φ.f (φ.ker.cosetRep C₁) = φ.f (φ.ker.cosetRep C₂) := heq
  rw [← heq', H.op_inv_right (φ.f_mem hr₁)]

/-- φ̄ es **sobreyectiva** sobre im φ. -/
theorem firstIsoMap_surjective : φ.firstIsoMap.Surjective := by
  intro y hy
  have hy_sep : y ∈ HFSet.sep H.G (fun b => ∃ a ∈ G.G, φ.f a = b) := hy
  have hy' := (HFSet.mem_sep _ _ _).mp hy_sep
  obtain ⟨a, haG, rfl⟩ := hy'.2
  refine ⟨φ.ker.rightCoset a, ?_, ?_⟩
  · exact φ.ker.cosetOf_mem_cosets haG
  · exact φ.firstIsoMap_welldefined haG

/-- **Primer Teorema de Isomorfía**: G/ker φ ≅ im φ. -/
theorem firstIsoMap_bijective : φ.firstIsoMap.Bijective :=
  ⟨φ.firstIsoMap_injective, φ.firstIsoMap_surjective⟩

end HFGroupHom

end HFAlgebra
