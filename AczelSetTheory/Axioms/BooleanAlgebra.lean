import AczelSetTheory.Axioms.Decidable
import AczelSetTheory.Axioms.Subset
import AczelSetTheory.Axioms.Lattice
import AczelSetTheory.Axioms.Setminus

namespace HFSet

-- ==================================================================
-- Definición de complemento relativo
-- ==================================================================

def compl (U X : HFSet) : HFSet := setminus U X

theorem mem_compl (U X x : HFSet) : x ∈ compl U X ↔ x ∈ U ∧ ¬ x ∈ X := by
  unfold compl; exact mem_setminus U X x

-- ==================================================================
-- Lemas auxiliares: inter con universo
-- ==================================================================

theorem inter_full (U A : HFSet) (hA : A ⊆ U) : inter A U = A :=
  extensionality _ _ fun x => by
    rw [mem_inter A U x]
    exact ⟨And.left, fun h => ⟨h, hA x h⟩⟩

theorem full_inter (U A : HFSet) (hA : A ⊆ U) : inter U A = A := by
  rw [inter_comm]; exact inter_full U A hA

-- ==================================================================
-- Postulados de Huntington para complemento
-- ==================================================================

theorem compl_mem_powerset (U X : HFSet) (_ : X ⊆ U) : compl U X ⊆ U :=
  fun x hx => ((mem_compl U X x).mp hx).1

theorem union_compl (U X : HFSet) (hX : X ⊆ U) : union X (compl U X) = U :=
  extensionality _ _ fun x => by
    rw [mem_union x X (compl U X), mem_compl U X x]
    constructor
    · exact fun h => h.elim (hX x) And.left
    · intro hU
      by_cases hx : x ∈ X
      · exact Or.inl hx
      · exact Or.inr ⟨hU, hx⟩

theorem inter_compl (U X : HFSet) (_ : X ⊆ U) : inter X (compl U X) = empty :=
  extensionality _ _ fun x => by
    rw [mem_inter X (compl U X) x, mem_compl U X x]
    exact ⟨fun ⟨hx, ⟨_, hnx⟩⟩ => absurd hx hnx,
           fun he => absurd he (not_mem_empty x)⟩

theorem compl_compl (U X : HFSet) (hX : X ⊆ U) : compl U (compl U X) = X :=
  extensionality _ _ fun x => by
    rw [mem_compl U (compl U X) x, mem_compl U X x]
    constructor
    · intro ⟨hU, hnn⟩
      by_cases hx : x ∈ X
      · exact hx
      · exact absurd ⟨hU, hx⟩ hnn
    · intro hx
      exact ⟨hX x hx, fun ⟨_, hn⟩ => hn hx⟩

theorem compl_empty (U : HFSet) : compl U empty = U := by
  unfold compl; exact setminus_empty U

theorem compl_self (U : HFSet) : compl U U = empty := by
  unfold compl; exact setminus_self U

-- ==================================================================
-- Leyes de De Morgan
-- ==================================================================

theorem compl_union (U A B : HFSet) (_ : A ⊆ U) (_ : B ⊆ U) :
    compl U (union A B) = inter (compl U A) (compl U B) :=
  extensionality _ _ fun x => by
    rw [mem_compl U (union A B) x, mem_union x A B,
        mem_inter (compl U A) (compl U B) x, mem_compl U A x, mem_compl U B x]
    constructor
    · intro ⟨hU, hn⟩
      exact ⟨⟨hU, fun ha => hn (Or.inl ha)⟩, ⟨hU, fun hb => hn (Or.inr hb)⟩⟩
    · intro ⟨⟨hU, hna⟩, ⟨_, hnb⟩⟩
      exact ⟨hU, fun h => h.elim hna hnb⟩

theorem compl_inter (U A B : HFSet) (_ : A ⊆ U) (_ : B ⊆ U) :
    compl U (inter A B) = union (compl U A) (compl U B) :=
  extensionality _ _ fun x => by
    rw [mem_compl U (inter A B) x, mem_inter A B x,
        mem_union x (compl U A) (compl U B), mem_compl U A x, mem_compl U B x]
    constructor
    · intro ⟨hU, hn⟩
      by_cases ha : x ∈ A
      · exact Or.inr ⟨hU, fun hb => hn ⟨ha, hb⟩⟩
      · exact Or.inl ⟨hU, ha⟩
    · intro h
      exact h.elim
        (fun ⟨hU, hna⟩ => ⟨hU, fun ⟨ha, _⟩ => hna ha⟩)
        (fun ⟨hU, hnb⟩ => ⟨hU, fun ⟨_, hb⟩ => hnb hb⟩)

-- ==================================================================
-- Propiedades adicionales del complemento
-- ==================================================================

theorem compl_subset_swap (U A B : HFSet) (hA : A ⊆ U) (_ : B ⊆ U) :
    A ⊆ B ↔ compl U B ⊆ compl U A := by
  constructor
  · intro hab x hx
    rw [mem_compl U A x]
    have h := (mem_compl U B x).mp hx
    exact ⟨h.1, fun ha => h.2 (hab x ha)⟩
  · intro hcomp x hxa
    by_cases hxb : x ∈ B
    · exact hxb
    · exact absurd hxa
        (((mem_compl U A x).mp (hcomp x ((mem_compl U B x).mpr ⟨hA x hxa, hxb⟩))).2)

theorem union_compl_inter (U A B : HFSet) (hA : A ⊆ U) (hB : B ⊆ U) :
    union (inter A B) (inter A (compl U B)) = A := by
  rw [← inter_union_distrib, union_compl U B hB, inter_full U A hA]

end HFSet
