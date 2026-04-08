/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/
import AczelSetTheory.Axioms.Function

namespace HFSet

-- ==================================================================
-- Axioma de Elección para conjuntos hereditariamente finitos
-- ==================================================================

/-- Si A ≠ ∅, entonces A tiene al menos un elemento. -/
theorem nonempty_of_ne_empty
  (A : HFSet) (h : A ≠ empty) :
    ∃ x, x ∈ A
      := by
  by_contra h_empty
  push_neg at h_empty
  exact h (extensionality A empty (fun x =>
    ⟨fun hx => absurd hx (h_empty x), fun hx => absurd hx (not_mem_empty x)⟩))

/-- Función de elección: dado un conjunto no vacío, selecciona un elemento.
    Noncomputable (Classical.choose). -/
noncomputable def choose
  (A : HFSet) (h : A ≠ empty) :
    HFSet
      :=
  Classical.choose (nonempty_of_ne_empty A h)

/-- El elemento elegido pertenece al conjunto. -/
theorem choose_mem
  (A : HFSet) (h : A ≠ empty) :
    choose A h ∈ A
      :=
  Classical.choose_spec (nonempty_of_ne_empty A h)

/-- Principio de elección (meta-nivel): para toda familia F de conjuntos no vacíos,
    existe una función que selecciona un elemento de cada miembro. -/
theorem choice_principle
  (F : HFSet) (hne : ∀ A, A ∈ F → A ≠ empty) :
    ∃ f : HFSet → HFSet, ∀ A, A ∈ F → f A ∈ A
      :=
  ⟨fun A => if h : A ≠ empty then choose A h else empty,
   fun A hA => by simp [hne A hA]; exact choose_mem A (hne A hA)⟩

end HFSet
