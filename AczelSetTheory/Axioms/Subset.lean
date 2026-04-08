import AczelSetTheory.HFSets
import AczelSetTheory.Axioms.Union
import AczelSetTheory.Axioms.Intersection

namespace HFSet

/-- Subconjunto: A ⊆ B si todo elemento de A pertenece a B. -/
instance : HasSubset HFSet where
  Subset A B := ∀ x, x ∈ A → x ∈ B

theorem subset_iff (A B : HFSet) : A ⊆ B ↔ ∀ x, x ∈ A → x ∈ B := Iff.rfl

theorem subset_refl (A : HFSet) : A ⊆ A :=
  fun _ h => h

theorem subset_trans (A B C : HFSet) (h1 : A ⊆ B) (h2 : B ⊆ C) : A ⊆ C :=
  fun x hx => h2 x (h1 x hx)

theorem subset_antisymm (A B : HFSet) (h1 : A ⊆ B) (h2 : B ⊆ A) : A = B :=
  extensionality A B (fun x => ⟨h1 x, h2 x⟩)

theorem empty_subset (A : HFSet) : empty ⊆ A :=
  fun x hx => absurd hx (not_mem_empty x)

theorem subset_union_left (A B : HFSet) : A ⊆ union A B :=
  fun x hx => (mem_union x A B).mpr (Or.inl hx)

theorem subset_union_right (A B : HFSet) : B ⊆ union A B :=
  fun x hx => (mem_union x A B).mpr (Or.inr hx)

theorem inter_subset_left (A B : HFSet) : inter A B ⊆ A :=
  fun x hx => ((mem_inter A B x).mp hx).1

theorem inter_subset_right (A B : HFSet) : inter A B ⊆ B :=
  fun x hx => ((mem_inter A B x).mp hx).2

theorem subset_inter (A B C : HFSet) (h1 : A ⊆ B) (h2 : A ⊆ C) : A ⊆ inter B C :=
  fun x hx => (mem_inter B C x).mpr ⟨h1 x hx, h2 x hx⟩

end HFSet
