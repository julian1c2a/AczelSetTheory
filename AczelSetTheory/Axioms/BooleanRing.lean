import AczelSetTheory.Axioms.Decidable
import AczelSetTheory.Axioms.Lattice
import AczelSetTheory.Axioms.BooleanAlgebra
import AczelSetTheory.Axioms.SymDiff

namespace HFSet

-- ==================================================================
-- Grupo abeliano (symDiff, ∅)
-- ==================================================================

theorem symDiff_comm (A B : HFSet) : symDiff A B = symDiff B A :=
  extensionality _ _ fun x => by
    rw [mem_symDiff A B x, mem_symDiff B A x, or_comm]

theorem symDiff_assoc (A B C : HFSet) :
    symDiff (symDiff A B) C = symDiff A (symDiff B C) :=
  extensionality _ _ fun x => by
    rw [mem_symDiff (symDiff A B) C x, mem_symDiff A B x,
        mem_symDiff A (symDiff B C) x, mem_symDiff B C x]
    by_cases hA : x ∈ A <;> by_cases hB : x ∈ B <;> by_cases hC : x ∈ C <;> simp_all

theorem symDiff_empty (A : HFSet) : symDiff A empty = A :=
  extensionality _ _ fun x => by
    rw [mem_symDiff A empty x]
    exact ⟨fun h => h.elim And.left (fun ⟨he, _⟩ => absurd he (not_mem_empty x)),
           fun hx => Or.inl ⟨hx, not_mem_empty x⟩⟩

theorem empty_symDiff (A : HFSet) : symDiff empty A = A := by
  rw [symDiff_comm]; exact symDiff_empty A

theorem symDiff_self (A : HFSet) : symDiff A A = empty :=
  extensionality _ _ fun x => by
    rw [mem_symDiff A A x]
    exact ⟨fun h => h.elim (fun ⟨hx, hn⟩ => absurd hx hn) (fun ⟨hx, hn⟩ => absurd hx hn),
           fun he => absurd he (not_mem_empty x)⟩

-- ==================================================================
-- Distributividad del producto sobre la suma
-- ==================================================================

theorem inter_symDiff_distrib (A B C : HFSet) :
    inter A (symDiff B C) = symDiff (inter A B) (inter A C) :=
  extensionality _ _ fun x => by
    rw [mem_inter A (symDiff B C) x, mem_symDiff B C x,
        mem_symDiff (inter A B) (inter A C) x, mem_inter A B x, mem_inter A C x]
    by_cases hA : x ∈ A <;> by_cases hB : x ∈ B <;> by_cases hC : x ∈ C <;> simp_all

-- ==================================================================
-- Conexión con álgebra de Boole
-- ==================================================================

theorem symDiff_eq_union_setminus (A B : HFSet) :
    symDiff A B = setminus (union A B) (inter A B) :=
  extensionality _ _ fun x => by
    rw [mem_symDiff A B x, mem_setminus (union A B) (inter A B) x,
        mem_union x A B, mem_inter A B x]
    constructor
    · intro h
      exact h.elim
        (fun ⟨ha, hnb⟩ => ⟨Or.inl ha, fun ⟨_, hb⟩ => hnb hb⟩)
        (fun ⟨hb, hna⟩ => ⟨Or.inr hb, fun ⟨ha, _⟩ => hna ha⟩)
    · intro ⟨hab, hnab⟩
      exact hab.elim
        (fun ha => Or.inl ⟨ha, fun hb => hnab ⟨ha, hb⟩⟩)
        (fun hb => Or.inr ⟨hb, fun ha => hnab ⟨ha, hb⟩⟩)

theorem symDiff_via_compl (U A B : HFSet) (hA : A ⊆ U) (hB : B ⊆ U) :
    symDiff A B = union (inter A (compl U B)) (inter B (compl U A)) :=
  extensionality _ _ fun x => by
    rw [mem_symDiff A B x,
        mem_union x (inter A (compl U B)) (inter B (compl U A)),
        mem_inter A (compl U B) x, mem_compl U B x,
        mem_inter B (compl U A) x, mem_compl U A x]
    constructor
    · intro h
      exact h.elim
        (fun ⟨ha, hnb⟩ => Or.inl ⟨ha, hA x ha, hnb⟩)
        (fun ⟨hb, hna⟩ => Or.inr ⟨hb, hB x hb, hna⟩)
    · intro h
      exact h.elim
        (fun ⟨ha, _, hnb⟩ => Or.inl ⟨ha, hnb⟩)
        (fun ⟨hb, _, hna⟩ => Or.inr ⟨hb, hna⟩)

end HFSet
