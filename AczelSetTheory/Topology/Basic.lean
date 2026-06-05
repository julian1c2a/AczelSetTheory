import AczelSetTheory.HFSets
import AczelSetTheory.Axioms.Union
import AczelSetTheory.Axioms.Intersection
import AczelSetTheory.Axioms.Setminus
import AczelSetTheory.Axioms.Subset
import AczelSetTheory.Axioms.Singleton

namespace HFTopology

/-!
# Espacios topológicos sobre HFSet

Un **espacio topológico** `(X, τ)` consiste en un conjunto `X` y una colección
`τ ⊆ 𝒫(X)` de *abiertos* que satisface:
1. `∅ ∈ τ` y `X ∈ τ`.
2. Unión arbitraria: si `F ⊆ τ` entonces `⋃F ∈ τ`.
3. Intersección finita: si `U, V ∈ τ` entonces `U ∩ V ∈ τ`.

Nota: sobre HFSet toda colección es finita, así que "uniones arbitrarias" son
en realidad uniones finitas.
-/

structure HFTopSpace where
  /-- Conjunto base del espacio. -/
  X          : HFSet
  /-- Colección de abiertos (cada `U ∈ τ` satisface `U ⊆ X`). -/
  τ          : HFSet
  τ_sub      : ∀ {U : HFSet}, U ∈ τ → U ⊆ X
  empty_mem  : HFSet.empty ∈ τ
  univ_mem   : X ∈ τ
  /-- Unión arbitraria de abiertos es abierta. -/
  sUnion_mem : ∀ {F : HFSet}, F ⊆ τ → HFSet.sUnion F ∈ τ
  /-- Intersección binaria de abiertos es abierta. -/
  inter_mem  : ∀ {U V : HFSet}, U ∈ τ → V ∈ τ → HFSet.inter U V ∈ τ

namespace HFTopSpace

variable (ts : HFTopSpace)

/-- Unión binaria de abiertos es abierta (se deduce de `sUnion_mem`). -/
theorem union_mem {U V : HFSet} (hU : U ∈ ts.τ) (hV : V ∈ ts.τ) :
    HFSet.union U V ∈ ts.τ := by
  have key : HFSet.union U V =
      HFSet.sUnion (HFSet.union (HFSet.singleton U) (HFSet.singleton V)) := by
    apply HFSet.extensionality
    intro x
    constructor
    · intro hx
      rw [HFSet.mem_sUnion]
      rw [HFSet.mem_union] at hx
      cases hx with
      | inl h =>
        exact ⟨U, by rw [HFSet.mem_union];
                     exact Or.inl ((HFSet.mem_singleton U U).mpr rfl), h⟩
      | inr h =>
        exact ⟨V, by rw [HFSet.mem_union];
                     exact Or.inr ((HFSet.mem_singleton V V).mpr rfl), h⟩
    · intro hx
      rw [HFSet.mem_sUnion] at hx
      obtain ⟨Y, hY, hxY⟩ := hx
      rw [HFSet.mem_union] at hY
      rw [HFSet.mem_union]
      cases hY with
      | inl h =>
        rw [HFSet.mem_singleton] at h
        exact Or.inl (h ▸ hxY)
      | inr h =>
        rw [HFSet.mem_singleton] at h
        exact Or.inr (h ▸ hxY)
  rw [key]
  apply ts.sUnion_mem
  intro W hW
  rw [HFSet.mem_union] at hW
  cases hW with
  | inl h =>
    rw [HFSet.mem_singleton] at h
    rw [h]; exact hU
  | inr h =>
    rw [HFSet.mem_singleton] at h
    rw [h]; exact hV

/-- El vacío es subconjunto de cada abierto. -/
theorem empty_sub {U : HFSet} : HFSet.empty ⊆ U :=
  HFSet.empty_subset U

/-! ### Cerrados -/

/-- `A` es cerrado si su complemento `X \ A` es abierto. -/
def isClosed (A : HFSet) : Prop := HFSet.setminus ts.X A ∈ ts.τ

theorem closed_empty : ts.isClosed HFSet.empty := by
  show HFSet.setminus ts.X HFSet.empty ∈ ts.τ
  have h : HFSet.setminus ts.X HFSet.empty = ts.X := by
    apply HFSet.extensionality
    intro x
    rw [HFSet.mem_setminus]
    exact ⟨And.left, fun hx => ⟨hx, HFSet.not_mem_empty x⟩⟩
  rw [h]; exact ts.univ_mem

theorem closed_univ : ts.isClosed ts.X := by
  show HFSet.setminus ts.X ts.X ∈ ts.τ
  have h : HFSet.setminus ts.X ts.X = HFSet.empty := by
    apply HFSet.extensionality
    intro x
    rw [HFSet.mem_setminus]
    exact ⟨fun ⟨hx, hn⟩ => absurd hx hn,
           fun he => absurd he (HFSet.not_mem_empty x)⟩
  rw [h]; exact ts.empty_mem

/-- Intersección de cerrados es cerrada. -/
theorem closed_inter {A B : HFSet} (hA : ts.isClosed A) (hB : ts.isClosed B) :
    ts.isClosed (HFSet.inter A B) := by
  show HFSet.setminus ts.X (HFSet.inter A B) ∈ ts.τ
  -- X \ (A ∩ B) = (X \ A) ∪ (X \ B)
  have key : HFSet.setminus ts.X (HFSet.inter A B) =
      HFSet.union (HFSet.setminus ts.X A) (HFSet.setminus ts.X B) := by
    apply HFSet.extensionality
    intro x
    rw [HFSet.mem_setminus, HFSet.mem_inter, HFSet.mem_union,
        HFSet.mem_setminus, HFSet.mem_setminus]
    constructor
    · rintro ⟨hx, h⟩
      by_cases ha : x ∈ A
      · exact Or.inr ⟨hx, fun hb => h ⟨ha, hb⟩⟩
      · exact Or.inl ⟨hx, ha⟩
    · rintro (⟨hx, ha⟩ | ⟨hx, hb⟩)
      · exact ⟨hx, fun ⟨ha', _⟩ => ha ha'⟩
      · exact ⟨hx, fun ⟨_, hb'⟩ => hb hb'⟩
  rw [key]
  exact ts.union_mem hA hB

/-- Unión binaria de cerrados es cerrada. -/
theorem closed_union {A B : HFSet} (hA : ts.isClosed A) (hB : ts.isClosed B) :
    ts.isClosed (HFSet.union A B) := by
  show HFSet.setminus ts.X (HFSet.union A B) ∈ ts.τ
  -- X \ (A ∪ B) = (X \ A) ∩ (X \ B)
  have key : HFSet.setminus ts.X (HFSet.union A B) =
      HFSet.inter (HFSet.setminus ts.X A) (HFSet.setminus ts.X B) := by
    apply HFSet.extensionality
    intro x
    rw [HFSet.mem_setminus, HFSet.mem_union, HFSet.mem_inter,
        HFSet.mem_setminus, HFSet.mem_setminus]
    constructor
    · rintro ⟨hx, h⟩
      exact ⟨⟨hx, fun ha => h (Or.inl ha)⟩, ⟨hx, fun hb => h (Or.inr hb)⟩⟩
    · rintro ⟨⟨hx, ha⟩, ⟨_, hb⟩⟩
      exact ⟨hx, fun h => Or.elim h ha hb⟩
  rw [key]
  exact ts.inter_mem hA hB

end HFTopSpace

end HFTopology
