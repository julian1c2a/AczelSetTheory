/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/
import AczelSetTheory.Operations.Identity
import AczelSetTheory.Axioms.Powerset
import AczelSetTheory.Axioms.Separation
import AczelSetTheory.Axioms.Pair
import AczelSetTheory.Axioms.Singleton
import AczelSetTheory.Axioms.OrderedPair
import AczelSetTheory.Axioms.FunctionComp
import AczelSetTheory.Axioms.Inverse

namespace HFSet

-- ==================================================================
-- Lema auxiliar de universo
-- ==================================================================

/-- Si a ∈ A entonces ⟪a, a⟫ ∈ 𝒫(𝒫(A)). -/
private theorem idFunc_mem_universe {A a : HFSet} (ha : a ∈ A) :
    ⟪a, a⟫ ∈ powerset (powerset A) := by
  rw [mem_powerset]
  intro x hx
  rw [mem_powerset]
  unfold orderedPair at hx
  rcases (mem_pair x (singleton a) (pair a a)).mp hx with rfl | rfl
  · -- x = {a}
    intro y hy
    rw [mem_singleton] at hy
    exact hy ▸ ha
  · -- x = {a, a}
    intro y hy
    have hya : y = a ∨ y = a := (mem_pair y a a).mp hy
    cases hya with
    | inl h => exact h ▸ ha
    | inr h => exact h ▸ ha

-- ==================================================================
-- Caracterización de idFunc
-- ==================================================================

/-- Caracterización de la función identidad:
    p ∈ idFunc A ↔ ∃ a ∈ A, p = ⟪a, a⟫. -/
theorem mem_idFunc {A p : HFSet} :
    p ∈ idFunc A ↔ ∃ a, a ∈ A ∧ p = ⟪a, a⟫ := by
  unfold HFSet.idFunc
  rw [mem_sep]
  constructor
  · rintro ⟨_, a, ha, rfl⟩; exact ⟨a, ha, rfl⟩
  · rintro ⟨a, ha, rfl⟩; exact ⟨idFunc_mem_universe ha, a, ha, rfl⟩

/-- Membresía en forma de par ordenado:
    ⟪a, b⟫ ∈ idFunc A ↔ a = b ∧ a ∈ A. -/
theorem mem_idFunc_pair {A a b : HFSet} :
    ⟪a, b⟫ ∈ idFunc A ↔ a = b ∧ a ∈ A := by
  rw [mem_idFunc]
  constructor
  · rintro ⟨c, hc, heq⟩
    have h := (orderedPair_eq_iff a b c c).mp heq
    -- h.1 : a = c, h.2 : b = c → a = b ∧ a ∈ A
    exact ⟨h.1.trans h.2.symm, h.1 ▸ hc⟩
  · rintro ⟨hab, ha⟩
    exact ⟨a, ha, hab ▸ rfl⟩

-- ==================================================================
-- idFunc es una relación y una función
-- ==================================================================

/-- La función identidad es una relación. -/
theorem idFunc_isRelation {A : HFSet} : isRelation (idFunc A) := by
  intro z hz
  obtain ⟨a, _, rfl⟩ := mem_idFunc.mp hz
  exact ⟨a, a, rfl⟩

/-- La función identidad es una función (univaluada). -/
theorem isFunction_idFunc {A : HFSet} : isFunction (idFunc A) := by
  refine ⟨idFunc_isRelation, ?_⟩
  intro a b₁ b₂ h₁ h₂
  have h₁' := mem_idFunc_pair.mp h₁   -- a = b₁ ∧ a ∈ A
  have h₂' := mem_idFunc_pair.mp h₂   -- a = b₂ ∧ a ∈ A
  exact h₁'.1.symm.trans h₂'.1

-- ==================================================================
-- Dominio y rango de idFunc
-- ==================================================================

/-- El dominio de la función identidad es A. -/
theorem domain_idFunc {A : HFSet} : domain (idFunc A) = A := by
  apply extensionality; intro a
  rw [mem_domain_iff]
  constructor
  · rintro ⟨b, hb⟩
    exact (mem_idFunc_pair.mp hb).2
  · intro ha
    exact ⟨a, mem_idFunc_pair.mpr ⟨rfl, ha⟩⟩

/-- El rango de la función identidad es A. -/
theorem range_idFunc {A : HFSet} : range (idFunc A) = A := by
  apply extensionality; intro b
  rw [mem_range_iff]
  constructor
  · rintro ⟨a, ha⟩
    have h := mem_idFunc_pair.mp ha   -- a = b ∧ a ∈ A
    exact h.1 ▸ h.2
  · intro hb
    exact ⟨b, mem_idFunc_pair.mpr ⟨rfl, hb⟩⟩

-- ==================================================================
-- idFunc como función total y biyección
-- ==================================================================

/-- La función identidad es una función total de A en A. -/
theorem isTotalFunction_idFunc {A : HFSet} : isTotalFunction (idFunc A) A A :=
  ⟨isFunction_idFunc, domain_idFunc, fun b hb => by rwa [range_idFunc] at hb⟩

/-- La función identidad es inyectiva. -/
theorem isInjective_idFunc {A : HFSet} : isInjective (idFunc A) := by
  intro a₁ a₂ b h₁ h₂
  have h₁' := mem_idFunc_pair.mp h₁   -- a₁ = b ∧ a₁ ∈ A
  have h₂' := mem_idFunc_pair.mp h₂   -- a₂ = b ∧ a₂ ∈ A
  exact h₁'.1.trans h₂'.1.symm

/-- La función identidad es sobreyectiva sobre A. -/
theorem isSurjective_idFunc {A : HFSet} : isSurjective (idFunc A) A := by
  intro b hb
  exact ⟨b, mem_idFunc_pair.mpr ⟨rfl, hb⟩⟩

/-- La función identidad es una biyección de A en A. -/
theorem isBijective_idFunc {A : HFSet} : isBijective (idFunc A) A A :=
  ⟨isTotalFunction_idFunc, isInjective_idFunc, isSurjective_idFunc⟩

-- ==================================================================
-- Leyes identidad para la composición funcional
-- ==================================================================

/-- Membresía en f ∘f idFunc A:
    ⟪a, c⟫ ∈ f ∘f idFunc A ↔ a ∈ A ∧ ⟪a, c⟫ ∈ f. -/
theorem mem_funComp_idFunc {f A a c : HFSet} :
    ⟪a, c⟫ ∈ f ∘f idFunc A ↔ a ∈ A ∧ ⟪a, c⟫ ∈ f := by
  rw [mem_funComp_pair]
  constructor
  · rintro ⟨b, hbA, hbf⟩
    have h := mem_idFunc_pair.mp hbA   -- a = b ∧ a ∈ A
    exact ⟨h.2, h.1 ▸ hbf⟩
  · rintro ⟨ha, hf⟩
    exact ⟨a, mem_idFunc_pair.mpr ⟨rfl, ha⟩, hf⟩

/-- Membresía en idFunc B ∘f f:
    ⟪a, c⟫ ∈ idFunc B ∘f f ↔ ⟪a, c⟫ ∈ f ∧ c ∈ B. -/
theorem mem_idFunc_funComp {f B a c : HFSet} :
    ⟪a, c⟫ ∈ idFunc B ∘f f ↔ ⟪a, c⟫ ∈ f ∧ c ∈ B := by
  rw [mem_funComp_pair]
  constructor
  · rintro ⟨b, hbf, hbB⟩
    have h := mem_idFunc_pair.mp hbB   -- b = c ∧ b ∈ B
    exact ⟨h.1 ▸ hbf, h.1 ▸ h.2⟩
  · rintro ⟨hf, hcB⟩
    exact ⟨c, hf, mem_idFunc_pair.mpr ⟨rfl, hcB⟩⟩

/-- Identidad por la derecha: f ∘f idFunc A = f
    cuando f es una función total con dominio A. -/
theorem funComp_idFunc_eq {f A B : HFSet} (hf : isTotalFunction f A B) :
    f ∘f idFunc A = f := by
  apply extensionality; intro z
  constructor
  · intro hz
    obtain ⟨a, b, c, rfl, hbg, hcf⟩ := mem_funComp.mp hz
    have h := mem_idFunc_pair.mp hbg   -- a = b ∧ a ∈ A
    exact h.1 ▸ hcf
  · intro hz
    obtain ⟨a, c, rfl⟩ := hf.1.1 z hz
    rw [mem_funComp]
    exact ⟨a, a, c, rfl,
           mem_idFunc_pair.mpr ⟨rfl, hf.2.1 ▸ mem_domain_of_mem f a c hz⟩,
           hz⟩

/-- Identidad por la izquierda: idFunc B ∘f f = f
    cuando f es una función total con rango ⊆ B. -/
theorem idFunc_funComp_eq {f A B : HFSet} (hf : isTotalFunction f A B) :
    idFunc B ∘f f = f := by
  apply extensionality; intro z
  constructor
  · intro hz
    obtain ⟨a, b, c, rfl, hbg, hcf⟩ := mem_funComp.mp hz
    -- hbg : ⟪a,b⟫ ∈ f, hcf : ⟪b,c⟫ ∈ idFunc B
    have h := mem_idFunc_pair.mp hcf   -- b = c ∧ b ∈ B
    exact h.1 ▸ hbg
  · intro hz
    obtain ⟨a, c, rfl⟩ := hf.1.1 z hz
    rw [mem_funComp]
    have hcB : c ∈ B := hf.2.2 c (mem_range_of_mem f a c hz)
    exact ⟨a, c, c, rfl, hz, mem_idFunc_pair.mpr ⟨rfl, hcB⟩⟩

-- ==================================================================
-- La función identidad es su propia inversa
-- ==================================================================

/-- La inversa relacional de la función identidad es ella misma. -/
theorem relInv_idFunc {A : HFSet} : (idFunc A)⁻¹ᵣ = idFunc A := by
  apply extensionality; intro z
  rw [mem_relInv]
  constructor
  · rintro ⟨a, b, hab, rfl⟩
    have h := mem_idFunc_pair.mp hab   -- a = b ∧ a ∈ A
    -- z = ⟪b, a⟫, y queremos ⟪b, a⟫ ∈ idFunc A
    -- b = a (h.1.symm) y b ∈ A (h.1 ▸ h.2)
    exact mem_idFunc_pair.mpr ⟨h.1.symm, h.1 ▸ h.2⟩
  · intro hz
    obtain ⟨a, ha, rfl⟩ := mem_idFunc.mp hz
    exact ⟨a, a, mem_idFunc.mpr ⟨a, ha, rfl⟩, rfl⟩

end HFSet
