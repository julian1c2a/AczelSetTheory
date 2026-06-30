/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- AczelSetTheory/VN/SymGroupVN.lean
--
-- Grupo simétrico sobre el segmento inicial de Von Neumann.
-- Define el tipo de permutaciones de {0, 1, …, n-1} usando la infraestructura
-- de FunPerm de la biblioteca Peano.
--
-- Estado: ⚠️ Parcial.
--   ✅ vnSeg  : segmento {0,…,n-1} como ℕ₀FSet
--   ✅ SymVN  : tipo de permutaciones del segmento
--   ✅ SymVN.id   : permutación identidad
--   ✅ SymVN.comp : composición de permutaciones
--   ❌ Estructura FinGroup no incluida en este módulo (requiere enumerar todas las permutaciones)
--
-- Contenido:
--   vnSeg         : ℕ₀ → ℕ₀FSet   (segmento {0,…,n-1})
--   mem_vnSeg_iff : k ∈ (vnSeg n).elems ↔ lt₀ k n
--   vnSeg_card    : (vnSeg n).card = n
--   SymVN         : ℕ₀ → Type      (tipo de permutaciones del segmento)
--   SymVN.id      : SymVN n         (identidad)
--   SymVN.comp    : ℕ₀ → SymVN n → SymVN n → SymVN n

import AczelSetTheory.VN.Basic
import Peano.PeanoNat.Combinatorics.Perm
import AczelSetTheory.Axioms.Function
import AczelSetTheory.Operations.FunctionComp
import AczelSetTheory.Operations.Identity
import AczelSetTheory.Operations.Inverse
import AczelSetTheory.Algebra.Group

open Peano Peano.FSet Peano.FSetFunction
open HFSet

namespace VN

-- ─────────────────────────────────────────────────────────────────
-- Segmento inicial como ℕ₀FSet
-- ─────────────────────────────────────────────────────────────────

/-- El segmento inicial {0, 1, …, n-1} como ℕ₀FSet. -/
def vnSeg (n : ℕ₀) : ℕ₀FSet := ℕ₀FSet.Fin₀Set n

theorem mem_vnSeg_iff (n k : ℕ₀) :
    k ∈ (vnSeg n).elems ↔ lt₀ k n :=
  ℕ₀FSet.mem_Fin₀Set_iff n k

theorem vnSeg_card (n : ℕ₀) : (vnSeg n).card = n :=
  ℕ₀FSet.Fin₀Set_card n

-- ─────────────────────────────────────────────────────────────────
-- Teoría Nativa en HFSet: SymHF y SymHFGroup
-- ─────────────────────────────────────────────────────────────────

noncomputable section

/-- El conjunto de todas las biyecciones de A a A.
    Definido nativamente en HFSet mediante separación sobre 𝒫(A × A). -/
def SymHF (A : HFSet) : HFSet :=
  have : DecidablePred (fun f => isBijective f A A) := fun _ => Classical.propDecidable _
  HFSet.sep (HFSet.powerset (HFSet.cartProd A A))
    (fun f => isBijective f A A)

theorem mem_SymHF_iff (A f : HFSet) :
  f ∈ SymHF A ↔ f ⊆ HFSet.cartProd A A ∧ isBijective f A A := by
  have : DecidablePred (fun f => isBijective f A A) := fun _ => Classical.propDecidable _
  rw [SymHF, HFSet.mem_sep, HFSet.mem_powerset]
  rfl

theorem isBijective_subset_cartProd {f A B : HFSet} (hf : isBijective f A B) :
  f ⊆ HFSet.cartProd A B := by
  intro p hp
  have h_func := isBijective_isFunction hf
  have h_rel := h_func.1
  obtain ⟨a, b, rfl⟩ := h_rel p hp
  have h_dom : a ∈ domain f := mem_domain_of_mem f a b hp
  have h_ran : b ∈ range f := mem_range_of_mem f a b hp
  rw [isBijective_domain_eq hf] at h_dom
  rw [isBijective_range_eq hf] at h_ran
  exact mem_cartProd_pair a b A B h_dom h_ran
theorem funComp_assoc_symm (f g h : HFSet) : (f ∘f g) ∘f h = f ∘f (g ∘f h) := by
  apply extensionality; intro p
  constructor
  · intro hp
    obtain ⟨a, u, c, rfl, hau_h, huc_fg⟩ := mem_funComp.mp hp
    rw [mem_funComp_pair] at huc_fg
    obtain ⟨b, hub_g, hbc_f⟩ := huc_fg
    rw [mem_funComp_pair]
    exact ⟨b, mem_funComp_pair.mpr ⟨u, hau_h, hub_g⟩, hbc_f⟩
  · intro hp
    obtain ⟨a, b, c, rfl, hab_gh, hbc_f⟩ := mem_funComp.mp hp
    rw [mem_funComp_pair] at hab_gh
    obtain ⟨u, hau_h, hub_g⟩ := hab_gh
    rw [mem_funComp_pair]
    exact ⟨u, hau_h, mem_funComp_pair.mpr ⟨b, hub_g, hbc_f⟩⟩

theorem relInv_funComp_idFunc {f A B : HFSet} (hf : isBijective f A B) :
  (f⁻¹ᵣ) ∘f f = idFunc A := by
  apply extensionality; intro p
  constructor
  · intro hp
    obtain ⟨a, b, c, rfl, hab_f, hbc_inv⟩ := mem_funComp.mp hp
    rw [mem_relInv_pair] at hbc_inv
    have hac : a = c := hf.2.1 a c b hab_f hbc_inv
    subst hac
    rw [mem_idFunc_pair]
    have haA : a ∈ A := by rw [← hf.1.2.1]; exact mem_domain_of_mem f a b hab_f
    exact ⟨rfl, haA⟩
  · intro hp
    rw [mem_idFunc] at hp
    obtain ⟨a, haA, rfl⟩ := hp
    have hdom : a ∈ domain f := by rw [hf.1.2.1]; exact haA
    obtain ⟨b, hab_f⟩ := (mem_domain_iff f a).mp hdom
    apply mem_funComp.mpr
    exact ⟨a, b, a, rfl, hab_f, mem_relInv_pair.mpr hab_f⟩

/-- La estructura de grupo de las permutaciones de A,
    usando composición funcional e identidad funcional. -/
def SymHFGroup (A : HFSet) : HFAlgebra.HFGroup where
  G := SymHF A
  op := fun f g => f ∘f g
  e := HFSet.idFunc A
  inv := fun f => f⁻¹ᵣ
  e_mem := by
    rw [mem_SymHF_iff]
    exact ⟨isBijective_subset_cartProd isBijective_idFunc, isBijective_idFunc⟩
  op_closed := fun {f g} hf hg => by
    rw [mem_SymHF_iff] at hf hg ⊢
    have h_bij := isBijective_funComp hf.2 hg.2
    exact ⟨isBijective_subset_cartProd h_bij, h_bij⟩
  inv_closed := fun {f} hf => by
    rw [mem_SymHF_iff] at hf ⊢
    have h_bij := isBijective_relInv hf.2
    exact ⟨isBijective_subset_cartProd h_bij, h_bij⟩
  op_assoc := fun {f g h} _ _ _ => funComp_assoc_symm f g h
  op_id_left := fun {f} hf => by
    rw [mem_SymHF_iff] at hf
    exact idFunc_funComp_eq (isBijective_isTotalFunction hf.2)
  op_inv_left := fun {f} hf => by
    rw [mem_SymHF_iff] at hf
    exact relInv_funComp_idFunc hf.2

end

/-- El grupo simétrico concreto sobre el segmento de von Neumann S_n. -/
noncomputable def SymVN (n : ℕ₀) : HFAlgebra.HFGroup :=
  SymHFGroup (vN n)

-- ─────────────────────────────────────────────────────────────────
-- Puente con Peano (Fontanería)
-- ─────────────────────────────────────────────────────────────────

/-- Convierte un par clave-valor de FunTable de Peano a un par ordenado de HFSet. -/
def pair_to_HFSet (kv : ℕ₀ × ℕ₀) : HFSet :=
  HFSet.orderedPair (vN kv.1) (vN kv.2)

/-- Inyecta una permutación de Peano (Sym A) como una biyección nativa en HFSet. -/
def FunPerm_to_HFSet {n : ℕ₀} (f : Peano.Perm.Sym (vnSeg n)) : HFSet :=
  -- Extraemos la lista de pares de la tabla de la función de Peano
  let pairs : List (ℕ₀ × ℕ₀) := f.toFunTable.table.map (fun a => (a, f.applyElem a 𝟘))
  -- Convertimos la lista a un HFSet (unión de singletons)
  List.foldr (fun kv S => HFSet.union (HFSet.singleton (pair_to_HFSet kv)) S) HFSet.empty pairs

end VN
