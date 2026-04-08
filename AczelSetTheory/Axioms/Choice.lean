/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/
import AczelSetTheory.Axioms.Function

namespace HFSet

open Classical

-- ==================================================================
-- Axioma de Elección para conjuntos hereditariamente finitos
-- ==================================================================

/-- Si A ≠ ∅, entonces A tiene al menos un elemento. -/
theorem nonempty_of_ne_empty
  (A : HFSet) (h : A ≠ empty) :
    ∃ x, x ∈ A
      := by
  rcases Quotient.exists_rep A with ⟨ac, rfl⟩
  match ac with
  | CList.mk [] => exact absurd rfl h
  | CList.mk (x :: xs) =>
    exact ⟨Quotient.mk CList.Setoid x,
           CList.mem_of_list_mem x (x :: xs) List.mem_cons_self⟩

-- ==================================================================
-- repr del vacío
-- ==================================================================

private theorem repr_empty_eq :
    repr empty = CList.empty
      := by
  unfold repr empty
  change CList.normalize CList.empty = CList.empty
  unfold CList.normalize CList.empty
  simp [CList.dedup, CList.dedupAux, CList.insertionSort]

private theorem repr_eq_empty_iff
  (A : HFSet) :
    A.repr = CList.empty → A = empty
      := by
  intro h
  exact (canonicalEq_iff_eq A empty).mp (by unfold canonicalEq; rw [h, repr_empty_eq])

-- ==================================================================
-- Función de elección computable
-- ==================================================================

/-- Extrae el head del representante canónico. Computable. -/
private def reprHead
  (c : CList) :
    CList
      :=
  match c with
  | CList.mk [] => CList.empty
  | CList.mk (x :: _) => x

/-- Función de elección computable: toma el primer elemento del representante
    canónico (normalizado y ordenado). -/
def choose
  (A : HFSet) (_ : A ≠ empty) :
    HFSet
      :=
  Quotient.mk CList.Setoid (reprHead A.repr)

/-- El head del representante canónico de A pertenece a A. -/
private theorem reprHead_mem_of_ne_empty
  (ac : CList) (h : Quotient.mk CList.Setoid ac ≠ empty) :
    CList.mem (reprHead (CList.normalize ac)) ac = true
      := by
  -- normalize ac no puede ser mk [] porque eso implicaría ac ~= empty
  match hn : CList.normalize ac with
  | CList.mk [] =>
    exfalso
    apply h
    apply (canonicalEq_iff_eq _ _).mp
    show repr (Quotient.mk CList.Setoid ac) = repr empty
    unfold repr
    change CList.normalize ac = CList.normalize CList.empty
    rw [hn]
    unfold CList.normalize CList.empty
    simp [CList.dedup, CList.dedupAux, CList.insertionSort]
  | CList.mk (x :: _) =>
    unfold reprHead
    -- x es miembro de normalize ac
    have hx_norm : CList.mem x (CList.normalize ac) = true := by
      rw [hn]; exact CList.mem_of_list_mem x (x :: _) List.mem_cons_self
    -- normalize ac es extEq a ac → subset (normalize ac) ac = true
    have h_ext : CList.extEq (CList.normalize ac) ac = true := by
      rw [CList.extEq_comm]; exact CList.extEq_normalize ac
    have h_sub : CList.subset (CList.normalize ac) ac = true := by
      rw [CList.extEq_def, Bool.and_eq_true] at h_ext; exact h_ext.1
    exact CList.mem_subset x (CList.normalize ac) ac hx_norm h_sub

/-- El elemento elegido pertenece al conjunto. -/
theorem choose_mem
  (A : HFSet) (h : A ≠ empty) :
    choose A h ∈ A
      := by
  unfold choose
  rcases Quotient.exists_rep A with ⟨ac, rfl⟩
  show CList.mem (reprHead (CList.normalize ac)) ac = true
  exact reprHead_mem_of_ne_empty ac h

/-- Principio de elección (meta-nivel): para toda familia F de conjuntos no vacíos,
    existe una función que selecciona un elemento de cada miembro. -/
theorem choice_principle
  (F : HFSet) (hne : ∀ A, A ∈ F → A ≠ empty) :
    ∃ f : HFSet → HFSet, ∀ A, A ∈ F → f A ∈ A
      :=
  ⟨fun A => if h : A = empty then empty else choose A h,
   fun A hA => by
    show (if h : A = empty then empty else choose A h) ∈ A
    rw [dif_neg (hne A hA)]
    exact choose_mem A (hne A hA)⟩

end HFSet
