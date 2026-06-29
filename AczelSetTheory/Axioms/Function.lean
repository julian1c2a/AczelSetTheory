/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/
import AczelSetTheory.Operations.Function
import AczelSetTheory.Axioms.Relation
import AczelSetTheory.Axioms.Intersection
import AczelSetTheory.Axioms.Setminus

namespace HFSet

-- ==================================================================
-- El vacío es una función
-- ==================================================================

/-- El conjunto vacío es una función. -/
theorem isFunction_empty :
    isFunction empty
      := by
  refine ⟨isRelation_empty, ?_⟩
  intro a b₁ b₂ h₁ _
  exact absurd h₁ (not_mem_empty _)

-- ==================================================================
-- Inyectividad y sobreyectividad
-- ==================================================================

/-- f es inyectiva: si ⟪a₁, b⟫ ∈ f y ⟪a₂, b⟫ ∈ f, entonces a₁ = a₂. -/
def isInjective
  (f : HFSet) :
    Prop
      :=
  ∀ a₁ a₂ b, ⟪a₁, b⟫ ∈ f → ⟪a₂, b⟫ ∈ f → a₁ = a₂

/-- f es sobreyectiva sobre B: todo b ∈ B tiene un preimagen en f. -/
def isSurjective
  (f B : HFSet) :
    Prop
      :=
  ∀ b, b ∈ B → ∃ a, ⟪a, b⟫ ∈ f

/-- f es biyectiva sobre A y B si es una función con dominio A, sobreyectiva sobre B e inyectiva. -/
def isBijective
  (f A B : HFSet) :
    Prop
      :=
  isTotalFunction f A B ∧ isInjective f ∧ isSurjective f B

-- ==================================================================
-- Propiedades básicas de funciones
-- ==================================================================

/-- Si f es función y ⟪a, b₁⟫ ∈ f y ⟪a, b₂⟫ ∈ f, entonces b₁ = b₂. -/
theorem isFunction_unique
  (f a b₁ b₂ : HFSet) (hf : isFunction f) (h₁ : ⟪a, b₁⟫ ∈ f) (h₂ : ⟪a, b₂⟫ ∈ f) :
    b₁ = b₂
      :=
  hf.2 a b₁ b₂ h₁ h₂

/-- Si ⟪a, b⟫ ∈ f entonces a ∈ domain f. -/
theorem mem_domain_of_mem
  (f a b : HFSet) (h : ⟪a, b⟫ ∈ f) :
    a ∈ domain f
      :=
  (mem_domain_iff f a).mpr ⟨b, h⟩

/-- Si ⟪a, b⟫ ∈ f entonces b ∈ range f. -/
theorem mem_range_of_mem
  (f a b : HFSet) (h : ⟪a, b⟫ ∈ f) :
    b ∈ range f
      :=
  (mem_range_iff f b).mpr ⟨a, h⟩

-- ==================================================================
-- Especificación de apply
-- ==================================================================

theorem sInter_singleton_eq' (A : HFSet) : sInter (singleton A) = A :=
  extensionality _ _ fun x => by
    rw [mem_sInter]
    constructor
    · rintro ⟨_, h⟩
      exact h A ((mem_singleton A A).mpr rfl)
    · intro hx
      exact ⟨⟨A, (mem_singleton A A).mpr rfl⟩, fun B hB => by
        have heq : B = A := (mem_singleton B A).mp hB
        subst heq; exact hx⟩

theorem sInter_orderedPair_fst' (a b : HFSet) : sInter ⟪a, b⟫ = singleton a :=
  extensionality _ _ fun x => by
    rw [mem_sInter]
    constructor
    · rintro ⟨_, h⟩
      exact h (singleton a) ((mem_pair _ _ _).mpr (Or.inl rfl))
    · intro hx
      exact ⟨⟨singleton a, (mem_pair _ _ _).mpr (Or.inl rfl)⟩, fun B hB => by
        rcases (mem_pair B (singleton a) (pair a b)).mp hB with h1 | h2
        · rw [h1]; exact hx
        · rw [h2]; exact (mem_pair x a b).mpr (Or.inl ((mem_singleton x a).mp hx))⟩

theorem fst_orderedPair_eq' (a b : HFSet) : fst ⟪a, b⟫ = a := by
  show sInter (sInter ⟪a, b⟫) = a
  rw [sInter_orderedPair_fst', sInter_singleton_eq']

theorem snd_orderedPair_eq' (a b : HFSet) : snd ⟪a, b⟫ = b := by
  show (if ∀ x, x ∈ HFSet.sUnion ⟪a, b⟫ → x ∈ HFSet.sInter ⟪a, b⟫
        then HFSet.sInter (HFSet.sInter ⟪a, b⟫)
        else HFSet.sInter (HFSet.setminus (HFSet.sUnion ⟪a, b⟫) (HFSet.sInter ⟪a, b⟫))) = b
  rw [sInter_orderedPair_fst', sInter_singleton_eq']
  have hbu : b ∈ HFSet.sUnion ⟪a, b⟫ := by
    rw [mem_sUnion]
    exact ⟨pair a b, (mem_pair _ _ _).mpr (Or.inr rfl), (mem_pair b a b).mpr (Or.inr rfl)⟩
  by_cases h : (∀ x : HFSet, x ∈ HFSet.sUnion ⟪a, b⟫ → x ∈ singleton a)
  · rw [if_pos h]
    exact ((mem_singleton b a).mp (h b hbu)).symm
  · rw [if_neg h]
    have anb : a ≠ b := by
      intro heq; subst heq; apply h; intro x hx
      rw [mem_sUnion] at hx
      obtain ⟨S, hS, hxS⟩ := hx
      rcases (mem_pair S (singleton a) (pair a a)).mp hS with h1 | h2
      · rw [h1] at hxS; exact hxS
      · rcases (mem_pair x a a).mp (h2 ▸ hxS) with h3 | h4
        · exact (mem_singleton x a).mpr h3
        · exact (mem_singleton x a).mpr h4
    have hsetminus : HFSet.setminus (HFSet.sUnion ⟪a, b⟫) (singleton a) = singleton b :=
      extensionality _ _ fun x => by
        rw [mem_setminus]
        constructor
        · rintro ⟨hxu, hxni⟩
          rw [mem_sUnion] at hxu
          obtain ⟨S, hS, hxS⟩ := hxu
          rcases (mem_pair S (singleton a) (pair a b)).mp hS with h1 | h2
          · exact absurd (h1 ▸ hxS) hxni
          · rcases (mem_pair x a b).mp (h2 ▸ hxS) with h3 | h4
            · exact absurd ((mem_singleton x a).mpr h3) hxni
            · exact (mem_singleton x b).mpr h4
        · intro hxb
          have hxb' : x = b := (mem_singleton x b).mp hxb
          refine ⟨?_, ?_⟩
          · rw [hxb']; exact hbu
          · intro hxa
            exact anb (((mem_singleton x a).mp hxa).symm.trans hxb')
    rw [hsetminus, sInter_singleton_eq']

private theorem sep_function_eq_singleton (f a b : HFSet) (hf : isFunction f) (hab : ⟪a, b⟫ ∈ f) :
    sep f (fun p => fst p = a) = singleton ⟪a, b⟫ :=
  extensionality _ _ fun x => by
    rw [mem_sep, mem_singleton]
    constructor
    · rintro ⟨hxf, hfx⟩
      obtain ⟨a', b', rfl⟩ := hf.1 x hxf
      rw [fst_orderedPair_eq'] at hfx
      rw [hfx] at hxf ⊢
      exact congrArg (orderedPair a) (isFunction_unique f a b' b hf hxf hab)
    · rintro rfl
      exact ⟨hab, fst_orderedPair_eq' a b⟩

/-- Si f es función y ⟪a, b⟫ ∈ f, entonces apply f a = b. -/
theorem apply_eq_of_mem
    (f a b : HFSet) (hf : isFunction f) (hab : ⟪a, b⟫ ∈ f) :
    apply f a = b := by
  show snd (sInter (sep f (fun p => fst p = a))) = b
  rw [sep_function_eq_singleton f a b hf hab, sInter_singleton_eq', snd_orderedPair_eq']

/-- ⟪a, apply f a⟫ ∈ f cuando f es función y a está en el dominio de f. -/
theorem apply_mem
    (f a : HFSet) (hf : isFunction f) (h : ∃ b, ⟪a, b⟫ ∈ f) :
    ⟪a, apply f a⟫ ∈ f := by
  obtain ⟨b, hab⟩ := h
  rw [apply_eq_of_mem f a b hf hab]
  exact hab

/-- Si f es función total sobre A, entonces a ∈ A implica ⟪a, apply f a⟫ ∈ f. -/
theorem totalFunction_apply_mem
    (f A B a : HFSet) (hf : isTotalFunction f A B) (ha : a ∈ A) :
    ⟪a, apply f a⟫ ∈ f :=
  apply_mem f a hf.1 ((mem_domain_iff f a).mp (hf.2.1.symm ▸ ha))

end HFSet
