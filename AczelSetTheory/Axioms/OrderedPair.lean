import AczelSetTheory.Operations.OrderedPair
import AczelSetTheory.Axioms.Pair
import AczelSetTheory.Axioms.Singleton

namespace HFSet

/-- Lema auxiliar: singleton a = singleton b → a = b -/
private theorem singleton_injective {a b : HFSet} (h : singleton a = singleton b) : a = b := by
  have hmem : a ∈ singleton a := (mem_singleton a a).mpr rfl
  rw [h] at hmem
  exact (mem_singleton a b).mp hmem

/-- Lema auxiliar: singleton a = pair b c → b = a ∧ c = a -/
private theorem singleton_eq_pair {a b c : HFSet}
    (h : singleton a = pair b c) : b = a ∧ c = a := by
  have hb : b ∈ pair b c := (mem_pair b b c).mpr (Or.inl rfl)
  have hc : c ∈ pair b c := (mem_pair c b c).mpr (Or.inr rfl)
  rw [← h] at hb hc
  exact ⟨(mem_singleton b a).mp hb, (mem_singleton c a).mp hc⟩

/-- Inyectividad del par ordenado de Kuratowski:
    ⟪a, b⟫ = ⟪c, d⟫ ↔ a = c ∧ b = d -/
theorem orderedPair_eq_iff (a b c d : HFSet) :
    orderedPair a b = orderedPair c d ↔ a = c ∧ b = d := by
  constructor
  · intro heq
    -- Desplegar orderedPair para trabajar con pair y singleton
    have h : pair (singleton a) (pair a b) = pair (singleton c) (pair c d) := heq
    -- Paso 1: Probar a = c
    have hsa : singleton a ∈ pair (singleton c) (pair c d) := by
      rw [← h]; exact (mem_pair _ _ _).mpr (Or.inl rfl)
    have hac : a = c := by
      rcases (mem_pair _ _ _).mp hsa with h1 | h2
      · exact singleton_injective h1
      · exact (singleton_eq_pair h2).1.symm
    subst hac
    -- Ahora h : pair (singleton a) (pair a b) = pair (singleton a) (pair a d)
    -- Paso 2: Probar b = d
    have hab : pair a b ∈ pair (singleton a) (pair a d) := by
      rw [← h]; exact (mem_pair _ _ _).mpr (Or.inr rfl)
    have had : pair a d ∈ pair (singleton a) (pair a b) := by
      rw [h]; exact (mem_pair _ _ _).mpr (Or.inr rfl)
    refine ⟨rfl, ?_⟩
    rcases (mem_pair _ _ _).mp hab with hab1 | hab2
    · -- pair a b = singleton a → b = a
      have hba : b = a := (singleton_eq_pair hab1.symm).2
      rcases (mem_pair _ _ _).mp had with had1 | had2
      · -- pair a d = singleton a → d = a
        have hda : d = a := (singleton_eq_pair had1.symm).2
        rw [hba, hda]
      · -- pair a d = pair a b → d ∈ {a, b}
        have hd : d ∈ pair a b := by rw [← had2]; exact (mem_pair d a d).mpr (Or.inr rfl)
        rcases (mem_pair d a b).mp hd with hda | hdb
        · rw [hba, hda]
        · exact hdb.symm
    · -- pair a b = pair a d
      have hb : b ∈ pair a d := by rw [← hab2]; exact (mem_pair b a b).mpr (Or.inr rfl)
      have hd : d ∈ pair a b := by rw [hab2]; exact (mem_pair d a d).mpr (Or.inr rfl)
      rcases (mem_pair b a d).mp hb with hba | hbd
      · rcases (mem_pair d a b).mp hd with hda | hdb
        · rw [hba, hda]
        · exact hdb.symm
      · exact hbd
  · rintro ⟨rfl, rfl⟩; rfl

end HFSet
