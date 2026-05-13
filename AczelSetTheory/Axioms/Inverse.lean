/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/
import AczelSetTheory.Operations.Inverse
import AczelSetTheory.Axioms.Relation
import AczelSetTheory.Axioms.Powerset
import AczelSetTheory.Axioms.Separation
import AczelSetTheory.Axioms.Pair
import AczelSetTheory.Axioms.Singleton
import AczelSetTheory.Axioms.OrderedPair
import AczelSetTheory.Axioms.Bijection

namespace HFSet

-- ==================================================================
-- Lema auxiliar de universo
-- ==================================================================

/-- Si ⟪a, b⟫ ∈ R entonces ⟪b, a⟫ ∈ 𝒫(𝒫(⋃⋃R)). -/
private theorem relInv_mem_universe
    (a b R : HFSet) (h : ⟪a, b⟫ ∈ R) :
    ⟪b, a⟫ ∈ powerset (powerset (sUnion (sUnion R))) := by
  have ha : a ∈ sUnion (sUnion R) := fst_mem_sUnion_sUnion a b R h
  have hb : b ∈ sUnion (sUnion R) := snd_mem_sUnion_sUnion a b R h
  rw [mem_powerset]
  intro x hx
  rw [mem_powerset]
  unfold orderedPair at hx
  rcases (mem_pair x (singleton b) (pair b a)).mp hx with rfl | rfl
  · -- x = {b}: todo y ∈ {b} satisface y = b ∈ U
    intro y hy
    rw [mem_singleton] at hy
    rw [hy]; exact hb
  · -- x = {b, a}: todo y ∈ {b, a} satisface y ∈ U
    intro y hy
    rcases (mem_pair y b a).mp hy with rfl | rfl
    · exact hb
    · exact ha

-- ==================================================================
-- Caracterización de la membresía en R⁻¹ᵣ
-- ==================================================================

/-- Caracterización de la relación inversa:
    p ∈ R⁻¹ᵣ ↔ ∃ a b, ⟪a, b⟫ ∈ R ∧ p = ⟪b, a⟫. -/
theorem mem_relInv {R p : HFSet} :
    p ∈ R⁻¹ᵣ ↔ ∃ a b, ⟪a, b⟫ ∈ R ∧ p = ⟪b, a⟫ := by
  unfold HFSet.relInv
  rw [mem_sep]
  constructor
  · rintro ⟨_, a, b, hab, rfl⟩; exact ⟨a, b, hab, rfl⟩
  · rintro ⟨a, b, hab, rfl⟩; exact ⟨relInv_mem_universe a b R hab, a, b, hab, rfl⟩

/-- Membresía en forma de par ordenado:
    ⟪b, a⟫ ∈ R⁻¹ᵣ ↔ ⟪a, b⟫ ∈ R. -/
theorem mem_relInv_pair {R a b : HFSet} :
    ⟪b, a⟫ ∈ R⁻¹ᵣ ↔ ⟪a, b⟫ ∈ R := by
  rw [mem_relInv]
  constructor
  · rintro ⟨a', b', hab', heq⟩
    obtain ⟨hb, ha⟩ := (orderedPair_eq_iff b a b' a').mp heq
    rw [← ha, ← hb] at hab'; exact hab'
  · intro h; exact ⟨a, b, h, rfl⟩

-- ==================================================================
-- R⁻¹ᵣ es siempre una relación
-- ==================================================================

/-- La relación inversa de cualquier conjunto es una relación. -/
theorem relInv_isRelation {R : HFSet} : isRelation (R⁻¹ᵣ) := by
  intro p hp
  obtain ⟨a, b, _, rfl⟩ := mem_relInv.mp hp
  exact ⟨b, a, rfl⟩

-- ==================================================================
-- Dominio y rango de R⁻¹ᵣ
-- ==================================================================

/-- El dominio de R⁻¹ᵣ es el rango de R. -/
theorem domain_relInv {R : HFSet} : domain (R⁻¹ᵣ) = range R := by
  apply extensionality; intro x
  rw [mem_domain_iff, mem_range_iff]
  constructor
  · rintro ⟨b, hxb⟩; exact ⟨b, mem_relInv_pair.mp hxb⟩
  · rintro ⟨a, hax⟩; exact ⟨a, mem_relInv_pair.mpr hax⟩

/-- El rango de R⁻¹ᵣ es el dominio de R. -/
theorem range_relInv {R : HFSet} : range (R⁻¹ᵣ) = domain R := by
  apply extensionality; intro x
  rw [mem_range_iff, mem_domain_iff]
  constructor
  · rintro ⟨b, hbx⟩; exact ⟨b, mem_relInv_pair.mp hbx⟩
  · rintro ⟨b, hxb⟩; exact ⟨b, mem_relInv_pair.mpr hxb⟩

-- ==================================================================
-- Doble inversa
-- ==================================================================

/-- La doble inversa de una relación es la relación original. -/
theorem relInv_relInv {R : HFSet} (hR : isRelation R) : (R⁻¹ᵣ)⁻¹ᵣ = R := by
  apply extensionality; intro p
  constructor
  · intro hp
    obtain ⟨c, d, hcd, rfl⟩ := mem_relInv.mp hp
    exact mem_relInv_pair.mp hcd
  · intro hp
    obtain ⟨a, b, rfl⟩ := hR p hp
    rw [mem_relInv]
    exact ⟨b, a, mem_relInv_pair.mpr hp, rfl⟩

-- ==================================================================
-- Propiedades funcionales de la inversa
-- ==================================================================

/-- Si f es inyectiva, entonces f⁻¹ᵣ es función. -/
theorem isFunction_relInv {f : HFSet}
    (hi : isInjective f) :
    isFunction (f⁻¹ᵣ) := by
  refine ⟨relInv_isRelation, ?_⟩
  intro a b₁ b₂ h₁ h₂
  rw [mem_relInv_pair] at h₁ h₂
  exact hi b₁ b₂ a h₁ h₂

/-- Si f es función, entonces f⁻¹ᵣ es inyectiva. -/
theorem isInjective_relInv {f : HFSet} (hf : isFunction f) :
    isInjective (f⁻¹ᵣ) := by
  intro a₁ a₂ b h₁ h₂
  rw [mem_relInv_pair] at h₁ h₂
  exact hf.2 b a₁ a₂ h₁ h₂

/-- f⁻¹ᵣ es sobreyectiva sobre el dominio de f. -/
theorem isSurjective_relInv {f A : HFSet}
    (hdom : domain f = A) :
    isSurjective (f⁻¹ᵣ) A := by
  intro a ha
  rw [← hdom, mem_domain_iff] at ha
  obtain ⟨b, hb⟩ := ha
  exact ⟨b, mem_relInv_pair.mpr hb⟩

-- ==================================================================
-- La inversa de una biyección es biyección
-- ==================================================================

/-- La inversa de una biyección f : A → B es una biyección f⁻¹ᵣ : B → A. -/
theorem isBijective_relInv {f A B : HFSet} (hf : isBijective f A B) :
    isBijective (f⁻¹ᵣ) B A := by
  have hfunc     := hf.1.1
  have hdom      := hf.1.2.1
  have hinj      := hf.2.1
  have hrange_eq := isBijective_range_eq hf
  refine ⟨⟨isFunction_relInv hinj, ?_, ?_⟩,
          isInjective_relInv hfunc,
          isSurjective_relInv hdom⟩
  · -- domain (f⁻¹ᵣ) = B
    rw [domain_relInv, hrange_eq]
  · -- ∀ a ∈ range (f⁻¹ᵣ), a ∈ A
    intro a ha
    rw [range_relInv] at ha
    rw [← hdom]; exact ha

end HFSet
