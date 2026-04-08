import AczelSetTheory.Axioms.Union
import AczelSetTheory.Axioms.Intersection
import AczelSetTheory.Axioms.Setminus
import AczelSetTheory.Axioms.Subset

namespace HFSet

-- ==================================================================
-- Conmutatividad
-- ==================================================================

theorem union_comm
  (A B : HFSet) :
    union A B = union B A
      :=
  extensionality _ _ fun x => by
    rw [mem_union x A B, mem_union x B A, or_comm]

theorem inter_comm
  (A B : HFSet) :
    inter A B = inter B A
      :=
  extensionality _ _ fun x => by
    rw [mem_inter A B x, mem_inter B A x, and_comm]

-- ==================================================================
-- Asociatividad
-- ==================================================================

theorem union_assoc
  (A B C : HFSet) :
    union (union A B) C = union A (union B C)
      :=
  extensionality _ _ fun x => by
    rw [mem_union x (union A B) C, mem_union x A B,
        mem_union x A (union B C), mem_union x B C, or_assoc]

theorem inter_assoc
  (A B C : HFSet) :
    inter (inter A B) C = inter A (inter B C)
      :=
  extensionality _ _ fun x => by
    rw [mem_inter (inter A B) C x, mem_inter A B x,
        mem_inter A (inter B C) x, mem_inter B C x, and_assoc]

-- ==================================================================
-- Idempotencia
-- ==================================================================

theorem union_idem
  (A : HFSet) :
    union A A = A
      :=
  extensionality _ _ fun x => by
    rw [mem_union x A A, or_self]

theorem inter_idem
  (A : HFSet) :
    inter A A = A
      :=
  extensionality _ _ fun x => by
    rw [mem_inter A A x, and_self]

-- ==================================================================
-- Absorción (postulados de Huntington)
-- ==================================================================

theorem union_inter_absorb
  (A B : HFSet) :
    union A (inter A B) = A
      :=
  extensionality _ _ fun x => by
    rw [mem_union x A (inter A B), mem_inter A B x]
    exact ⟨fun h => h.elim id And.left, Or.inl⟩

theorem inter_union_absorb
  (A B : HFSet) :
    inter A (union A B) = A
      :=
  extensionality _ _ fun x => by
    rw [mem_inter A (union A B) x, mem_union x A B]
    exact ⟨And.left, fun h => ⟨h, Or.inl h⟩⟩

-- ==================================================================
-- Distributividad
-- ==================================================================

theorem union_inter_distrib
  (A B C : HFSet) :
    union A (inter B C) = inter (union A B) (union A C)
      :=
  extensionality _ _ fun x => by
    rw [mem_union x A (inter B C), mem_inter B C x,
        mem_inter (union A B) (union A C) x, mem_union x A B, mem_union x A C]
    exact ⟨fun h => h.elim (fun ha => ⟨Or.inl ha, Or.inl ha⟩)
                            (fun ⟨hb, hc⟩ => ⟨Or.inr hb, Or.inr hc⟩),
           fun ⟨hab, hac⟩ => hab.elim Or.inl
                              (fun hb => hac.elim Or.inl (fun hc => Or.inr ⟨hb, hc⟩))⟩

theorem inter_union_distrib
  (A B C : HFSet) :
    inter A (union B C) = union (inter A B) (inter A C)
      :=
  extensionality _ _ fun x => by
    rw [mem_inter A (union B C) x, mem_union x B C,
        mem_union x (inter A B) (inter A C), mem_inter A B x, mem_inter A C x]
    exact ⟨fun ⟨ha, hbc⟩ => hbc.elim (fun hb => Or.inl ⟨ha, hb⟩)
                                    (fun hc => Or.inr ⟨ha, hc⟩),
           fun h => h.elim (fun ⟨ha, hb⟩ => ⟨ha, Or.inl hb⟩)
                           (fun ⟨ha, hc⟩ => ⟨ha, Or.inr hc⟩)⟩

-- ==================================================================
-- Elemento neutro
-- ==================================================================

theorem union_empty
  (A : HFSet) :
    union A empty = A
      :=
  extensionality _ _ fun x => by
    rw [mem_union x A empty]
    exact ⟨fun h => h.elim id (fun he => absurd he (not_mem_empty x)), Or.inl⟩

theorem empty_union
  (A : HFSet) :
    union empty A = A
      := by
  rw [union_comm]; exact union_empty A

theorem inter_empty
  (A : HFSet) :
    inter A empty = empty
      :=
  extensionality _ _ fun x => by
    rw [mem_inter A empty x]
    exact ⟨fun ⟨_, he⟩ => absurd he (not_mem_empty x),
           fun he => absurd he (not_mem_empty x)⟩

theorem empty_inter
  (A : HFSet) :
    inter empty A = empty
      := by
  rw [inter_comm]; exact inter_empty A

-- ==================================================================
-- Setminus: propiedades básicas
-- ==================================================================

theorem setminus_self
  (A : HFSet) :
    setminus A A = empty
      :=
  extensionality _ _ fun x => by
    rw [mem_setminus A A x]
    exact ⟨fun ⟨h, hn⟩ => absurd h hn, fun he => absurd he (not_mem_empty x)⟩

theorem setminus_empty
  (A : HFSet) :
    setminus A empty = A
      :=
  extensionality _ _ fun x => by
    rw [mem_setminus A empty x]
    exact ⟨And.left, fun h => ⟨h, not_mem_empty x⟩⟩

theorem empty_setminus
  (A : HFSet) :
    setminus empty A = empty
      :=
  extensionality _ _ fun x => by
    rw [mem_setminus empty A x]
    exact ⟨fun ⟨he, _⟩ => absurd he (not_mem_empty x),
           fun he => absurd he (not_mem_empty x)⟩

end HFSet
