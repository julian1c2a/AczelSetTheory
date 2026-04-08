import AczelSetTheory.CList

-- ==========================================
-- HFSet: Tipo cociente sobre CList
-- ==========================================

-- El Setoid finalmente con reflexividad, simetría y transitividad
def CList.Setoid : Setoid CList where
  r A B := CList.extEq A B = true
  iseqv := {
    refl := CList.extEq_refl
    symm := fun {A B} h => by
      rw [CList.extEq_def] at h ⊢
      rwa [Bool.and_comm]
    trans := fun {A B C} h1 h2 => CList.extEq_trans A B C h1 h2
  }

def HFSet := Quotient CList.Setoid

namespace HFSet

open CList

/--
Esta es la función que extrae el representante canónico (una `CList` normalizada)
de un `HFSet` abstracto.
-/
def repr (s : HFSet) : CList :=
  Quotient.lift CList.normalize (fun _ _ h => normalize_eq_of_extEq h) s

/-- Igualdad canónica entre HFSets: coinciden sus formas normales (repr). -/
def canonicalEq (A B : HFSet) : Prop :=
  A.repr = B.repr

/-- La igualdad canónica es equivalente a la igualdad proposicional de HFSets. -/
theorem canonicalEq_iff_eq (A B : HFSet) : canonicalEq A B ↔ A = B := by
  constructor
  · intro h
    unfold canonicalEq at h
    rcases Quotient.exists_rep A with ⟨a, rfl⟩
    rcases Quotient.exists_rep B with ⟨b, rfl⟩
    apply Quotient.sound
    show extEq a b = true
    have h_norm : normalize a = normalize b := h
    exact extEq_iff_normalize_eq.mpr h_norm
  · intro h
    rw [h]
    unfold canonicalEq
    rfl

def empty : HFSet := Quotient.mk CList.Setoid CList.empty

-- ==================================================================
-- Pertenencia a nivel HFSet
-- ==================================================================

/-- mem respeta extEq en el segundo argumento. -/
theorem mem_resp_right (x A B : CList) (h : extEq A B = true) :
    mem x A = true → mem x B = true := by
  intro hm
  have hsub : subset A B = true := by
    rw [extEq_def, Bool.and_eq_true] at h; exact h.1
  exact mem_subset x A B hm hsub

/-- mem respeta extEq en el primer argumento (ambas direcciones). -/
theorem mem_resp_left (x y A : CList) (h : extEq x y = true) :
    mem x A = true ↔ mem y A = true := by
  constructor
  · intro hm
    have hyx : extEq y x = true := by rw [extEq_comm]; exact h
    exact mem_of_extEq y x A hyx hm
  · intro hm
    exact mem_of_extEq x y A h hm

/-- CList.mem respeta extEq en ambos argumentos (para Quotient.lift₂). -/
private theorem mem_respects (x₁ x₂ A₁ A₂ : CList)
    (hx : extEq x₁ x₂ = true) (hA : extEq A₁ A₂ = true) :
    CList.mem x₁ A₁ = CList.mem x₂ A₂ := by
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro h
    exact mem_resp_right x₂ A₁ A₂ hA ((mem_resp_left x₁ x₂ A₁ hx).mp h)
  · intro h
    have hx' : extEq x₂ x₁ = true := by rw [extEq_comm]; exact hx
    have hA' : extEq A₂ A₁ = true := by rw [extEq_comm]; exact hA
    exact mem_resp_right x₁ A₂ A₁ hA' ((mem_resp_left x₂ x₁ A₂ hx').mp h)

/-- Pertenencia sobre HFSet. -/
def Mem (x A : HFSet) : Prop :=
  Quotient.liftOn₂ x A (fun a b => CList.mem a b = true)
    (fun _ _ _ _ hx hA => propext (Bool.eq_iff_iff.mp (mem_respects _ _ _ _ hx hA)))

instance : Membership HFSet HFSet where
  mem A x := Mem x A

private def toHFSet (c : CList) : HFSet := Quotient.mk CList.Setoid c

/-- Reducción de la pertenencia al nivel CList. -/
theorem mem_mk (x A : CList) :
    (toHFSet x) ∈ (toHFSet A) ↔ CList.mem x A = true :=
  Iff.rfl

-- ==================================================================
-- Lemas auxiliares para subset ↔ forall mem
-- ==================================================================

theorem subset_iff_forall_mem_clist (A B : CList) :
    subset A B = true ↔ (∀ x : CList, mem x A = true → mem x B = true) := by
  match A with
  | mk xs =>
    constructor
    · intro hs x hm
      exact mem_subset x (mk xs) B hm hs
    · intro hf
      induction xs with
      | nil => exact subset_nil B
      | cons y ys ih =>
        rw [subset_cons, Bool.and_eq_true]
        constructor
        · exact hf y (by rw [mem_cons, extEq_refl, Bool.or_eq_true]; exact Or.inl rfl)
        · exact ih (fun x hm => hf x (by rw [mem_cons, Bool.or_eq_true]; exact Or.inr hm))

-- ==================================================================
-- Axioma de Extensionalidad
-- ==================================================================

/-- Axioma de Extensionalidad: dos HFSets con los mismos elementos son iguales. -/
theorem extensionality (A B : HFSet) (h : ∀ x : HFSet, x ∈ A ↔ x ∈ B) : A = B := by
  rcases Quotient.exists_rep A with ⟨a, rfl⟩
  rcases Quotient.exists_rep B with ⟨b, rfl⟩
  apply Quotient.sound
  show extEq a b = true
  rw [extEq_def, Bool.and_eq_true]
  constructor
  · rw [subset_iff_forall_mem_clist]
    intro x hm
    exact (h (toHFSet x)).mp hm
  · rw [subset_iff_forall_mem_clist]
    intro x hm
    exact (h (toHFSet x)).mpr hm

-- ==================================================================
-- Axioma del Conjunto Vacío
-- ==================================================================

/-- No hay elementos en el conjunto vacío. -/
theorem not_mem_empty (x : HFSet) : ¬ (x ∈ empty) := by
  rcases Quotient.exists_rep x with ⟨xc, rfl⟩
  show CList.mem xc CList.empty = true → False
  unfold CList.empty
  rw [mem_nil]; exact Bool.false_ne_true

