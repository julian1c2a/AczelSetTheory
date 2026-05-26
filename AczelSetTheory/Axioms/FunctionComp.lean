/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/
import AczelSetTheory.Operations.FunctionComp
import AczelSetTheory.Axioms.Powerset
import AczelSetTheory.Axioms.Separation
import AczelSetTheory.Axioms.Union
import AczelSetTheory.Axioms.Pair
import AczelSetTheory.Axioms.Singleton
import AczelSetTheory.Axioms.OrderedPair
import AczelSetTheory.Axioms.Bijection
import AczelSetTheory.Axioms.Inverse

namespace HFSet

-- ==================================================================
-- Lema auxiliar de universo
-- ==================================================================

/-- Si ⟪a, b⟫ ∈ g y ⟪b, c⟫ ∈ f entonces ⟪a, c⟫ pertenece al universo de funComp. -/
private theorem funComp_mem_universe
    {f g a₀ b₀ c₀ : HFSet} (hg : ⟪a₀, b₀⟫ ∈ g) (hf : ⟪b₀, c₀⟫ ∈ f) :
    ⟪a₀, c₀⟫ ∈ powerset (powerset (union (sUnion (sUnion f)) (sUnion (sUnion g)))) := by
  have ha : a₀ ∈ sUnion (sUnion g) := fst_mem_sUnion_sUnion a₀ b₀ g hg
  have hc : c₀ ∈ sUnion (sUnion f) := snd_mem_sUnion_sUnion b₀ c₀ f hf
  rw [mem_powerset]
  intro x hx
  rw [mem_powerset]
  unfold orderedPair at hx
  rcases (mem_pair x (singleton a₀) (pair a₀ c₀)).mp hx with rfl | rfl
  · -- x = {a₀}
    intro y hy
    rw [mem_singleton] at hy
    exact (mem_union y _ _).mpr (Or.inr (hy ▸ ha))
  · -- x = {a₀, c₀}
    intro y hy
    have hya : y = a₀ ∨ y = c₀ := (mem_pair y a₀ c₀).mp hy
    cases hya with
    | inl h => rw [h]; exact (mem_union a₀ _ _).mpr (Or.inr ha)
    | inr h => rw [h]; exact (mem_union c₀ _ _).mpr (Or.inl hc)

-- ==================================================================
-- Caracterización de funComp
-- ==================================================================

/-- Caracterización de la composición funcional:
    p ∈ f ∘f g ↔ ∃ a b c, p = ⟪a, c⟫ ∧ ⟪a, b⟫ ∈ g ∧ ⟪b, c⟫ ∈ f. -/
theorem mem_funComp {f g p : HFSet} :
    p ∈ f ∘f g ↔ ∃ a b c, p = ⟪a, c⟫ ∧ ⟪a, b⟫ ∈ g ∧ ⟪b, c⟫ ∈ f := by
  unfold HFSet.funComp
  rw [mem_sep]
  constructor
  · rintro ⟨_, a, _, b, _, c, _, rfl, hg, hf⟩; exact ⟨a, b, c, rfl, hg, hf⟩
  · rintro ⟨a, b, c, rfl, hg, hf⟩
    exact ⟨funComp_mem_universe hg hf, a, fst_mem_sUnion_sUnion a b g hg,
           b, snd_mem_sUnion_sUnion a b g hg, c, snd_mem_sUnion_sUnion b c f hf,
           rfl, hg, hf⟩

/-- Membresía en forma de par ordenado:
    ⟪a, c⟫ ∈ f ∘f g ↔ ∃ b, ⟪a, b⟫ ∈ g ∧ ⟪b, c⟫ ∈ f. -/
theorem mem_funComp_pair {f g a c : HFSet} :
    ⟪a, c⟫ ∈ f ∘f g ↔ ∃ b, ⟪a, b⟫ ∈ g ∧ ⟪b, c⟫ ∈ f := by
  rw [mem_funComp]
  constructor
  · rintro ⟨a', b, c', heq, hg, hf⟩
    obtain ⟨rfl, rfl⟩ := (orderedPair_eq_iff a c a' c').mp heq
    exact ⟨b, hg, hf⟩
  · rintro ⟨b, hg, hf⟩; exact ⟨a, b, c, rfl, hg, hf⟩

-- ==================================================================
-- funComp es siempre una relación
-- ==================================================================

/-- La composición funcional de cualquier par de conjuntos es una relación. -/
theorem funComp_isRelation {f g : HFSet} : isRelation (f ∘f g) := by
  intro p hp
  obtain ⟨a, _, c, rfl, _, _⟩ := mem_funComp.mp hp
  exact ⟨a, c, rfl⟩

-- ==================================================================
-- La composición de funciones es función
-- ==================================================================

/-- La composición funcional de dos funciones es una función. -/
theorem isFunction_funComp
    {f g : HFSet} (hf : isFunction f) (hg : isFunction g) :
    isFunction (f ∘f g) := by
  refine ⟨funComp_isRelation, ?_⟩
  intro a c₁ c₂ h₁ h₂
  rw [mem_funComp_pair] at h₁ h₂
  obtain ⟨b₁, hb₁g, hb₁f⟩ := h₁
  obtain ⟨b₂, hb₂g, hb₂f⟩ := h₂
  -- g es función: b₁ = b₂
  have hb : b₁ = b₂ := hg.2 a b₁ b₂ hb₁g hb₂g
  subst hb
  -- f es función: c₁ = c₂
  exact hf.2 b₁ c₁ c₂ hb₁f hb₂f

-- ==================================================================
-- Dominio y rango de la composición
-- ==================================================================

/-- a ∈ domain (f ∘f g) ↔ a ∈ domain g ∧ ∃ b, ⟪a, b⟫ ∈ g ∧ b ∈ domain f. -/
theorem mem_domain_funComp {f g a : HFSet} :
    a ∈ domain (f ∘f g) ↔ ∃ b, ⟪a, b⟫ ∈ g ∧ ∃ c, ⟪b, c⟫ ∈ f := by
  rw [mem_domain_iff]
  constructor
  · rintro ⟨c, hac⟩
    rw [mem_funComp_pair] at hac
    obtain ⟨b, hg, hf⟩ := hac
    exact ⟨b, hg, c, hf⟩
  · rintro ⟨b, hg, c, hf⟩
    exact ⟨c, mem_funComp_pair.mpr ⟨b, hg, hf⟩⟩

/-- c ∈ range (f ∘f g) ↔ ∃ b ∈ range g, ⟪b, c⟫ ∈ f. -/
theorem mem_range_funComp {f g c : HFSet} :
    c ∈ range (f ∘f g) ↔ ∃ b, b ∈ range g ∧ ⟪b, c⟫ ∈ f := by
  rw [mem_range_iff]
  constructor
  · rintro ⟨a, hac⟩
    rw [mem_funComp_pair] at hac
    obtain ⟨b, hg, hf⟩ := hac
    exact ⟨b, (mem_range_iff g b).mpr ⟨a, hg⟩, hf⟩
  · rintro ⟨b, hbR, hf⟩
    obtain ⟨a, hg⟩ := (mem_range_iff g b).mp hbR
    exact ⟨a, mem_funComp_pair.mpr ⟨b, hg, hf⟩⟩

-- ==================================================================
-- Preservación de inyectividad y sobreyectividad
-- ==================================================================

/-- La composición de funciones inyectivas es inyectiva. -/
theorem isInjective_funComp
    {f g : HFSet} (hf : isInjective f) (hg : isInjective g) :
    isInjective (f ∘f g) := by
  intro a₁ a₂ c h₁ h₂
  rw [mem_funComp_pair] at h₁ h₂
  obtain ⟨b₁, hb₁g, hb₁f⟩ := h₁
  obtain ⟨b₂, hb₂g, hb₂f⟩ := h₂
  -- f inyectiva: b₁ = b₂
  have hb : b₁ = b₂ := hf b₁ b₂ c hb₁f hb₂f
  subst hb
  -- g inyectiva: a₁ = a₂
  exact hg a₁ a₂ b₁ hb₁g hb₂g

/-- La composición de funciones sobreyectivas es sobreyectiva sobre C,
    bajo la condición de que g sea sobreyectiva sobre el dominio de f. -/
theorem isSurjective_funComp
    {f g C : HFSet} (hf : isSurjective f C)
    (hg : isSurjective g (domain f)) :
    isSurjective (f ∘f g) C := by
  intro c hc
  obtain ⟨b, hbf⟩ := hf c hc
  -- b ∈ domain f
  have hb_dom : b ∈ domain f := mem_domain_of_mem f b c hbf
  obtain ⟨a, hag⟩ := hg b hb_dom
  exact ⟨a, mem_funComp_pair.mpr ⟨b, hag, hbf⟩⟩

-- ==================================================================
-- La composición de biyecciones es biyección
-- ==================================================================

/-- La composición funcional de dos funciones totales es una función total. -/
theorem isTotalFunction_funComp
    {f g A B C : HFSet}
    (hf : isTotalFunction f B C) (hg : isTotalFunction g A B) :
    isTotalFunction (f ∘f g) A C := by
  refine ⟨isFunction_funComp hf.1 hg.1, ?_, ?_⟩
  · -- domain (f ∘f g) = A
    apply extensionality; intro a
    rw [mem_domain_funComp]
    constructor
    · rintro ⟨b, hbg, _, _⟩
      rw [← hg.2.1]; exact mem_domain_of_mem g a b hbg
    · intro ha
      have ha' : a ∈ domain g := hg.2.1 ▸ ha
      obtain ⟨b, hbg⟩ := (mem_domain_iff g a).mp ha'
      have hb' : b ∈ domain f := by
        rw [hf.2.1]; exact hg.2.2 b (mem_range_of_mem g a b hbg)
      obtain ⟨c, hcf⟩ := (mem_domain_iff f b).mp hb'
      exact ⟨b, hbg, c, hcf⟩
  · -- ∀ c ∈ range (f ∘f g), c ∈ C
    intro c hc
    obtain ⟨a, hac⟩ := (mem_range_iff (f ∘f g) c).mp hc
    obtain ⟨b, _, hbcf⟩ := mem_funComp_pair.mp hac
    exact hf.2.2 c (mem_range_of_mem f b c hbcf)

/-- La composición funcional de dos biyecciones es una biyección. -/
theorem isBijective_funComp
    {f g A B C : HFSet}
    (hf : isBijective f B C) (hg : isBijective g A B) :
    isBijective (f ∘f g) A C :=
  ⟨isTotalFunction_funComp hf.1 hg.1,
   isInjective_funComp hf.2.1 hg.2.1,
   isSurjective_funComp hf.2.2 (hf.1.2.1.symm ▸ hg.2.2)⟩

end HFSet
