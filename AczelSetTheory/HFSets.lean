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

/-!
Dadas dos CList A y B que son extensionalmente iguales,
sus formas normales son idénticas.
-/

theorem normalize_eq_of_extEq {A B : CList} (h : CList.extEq A B = true) :
    CList.normalize A = CList.normalize B := by
  -- Inducción bien fundada en cSize A + cSize B
  match A, B with
  | CList.mk xs, CList.mk ys =>
    -- IH: para todo par (a, b) con cSize a + cSize b < cSize (mk xs) + cSize (mk ys),
    --     extEq a b = true → normalize a = normalize b
    simp only [CList.normalize]
    congr 1
    -- Goal: insertionSort (dedup (xs.map normalize)) = insertionSort (dedup (ys.map normalize))
    -- Usamos sorted_nodup_setEquiv_eq
    apply sorted_nodup_setEquiv_eq
    -- (1) Sorted
    · exact insertionSort_sorted _
    · exact insertionSort_sorted _
    -- (2) Nodup
    · exact insertionSort_nodup _ (dedup_nodup _)
    · exact insertionSort_nodup _ (dedup_nodup _)
    -- (3) SetEquiv
    · -- SetEquiv (insertionSort (dedup (xs.map normalize))) (insertionSort (dedup (ys.map normalize)))
      -- Cadena: insSort(dedup nxs) ≡ dedup nxs ≡ nxs ≡ nys ≡ dedup nys ≡ insSort(dedup nys)
      have h_nxs_nys : SetEquiv (xs.map normalize) (ys.map normalize) := by
        rw [extEq_mk_iff_setEquiv] at h
        intro z
        constructor
        · intro hz
          rw [List.any_eq_true] at hz ⊢
          obtain ⟨w, hw_mem, hw_eq⟩ := hz
          rw [List.mem_map] at hw_mem
          obtain ⟨xi, hxi_mem, rfl⟩ := hw_mem
          have hxi_in_ys := (h xi).mp (List.any_eq_true.mpr ⟨xi, hxi_mem, extEq_refl xi⟩)
          rw [List.any_eq_true] at hxi_in_ys
          obtain ⟨yj, hyj_mem, hyj_eq⟩ := hxi_in_ys
          have _hxi_lt := cSize_lt_of_mem hxi_mem
          have _hyj_lt := cSize_lt_of_mem hyj_mem
          have hIH : normalize xi = normalize yj := normalize_eq_of_extEq hyj_eq
          exact ⟨normalize yj, List.mem_map.mpr ⟨yj, hyj_mem, rfl⟩, hIH ▸ hw_eq⟩
        · intro hz
          rw [List.any_eq_true] at hz ⊢
          obtain ⟨w, hw_mem, hw_eq⟩ := hz
          rw [List.mem_map] at hw_mem
          obtain ⟨yj, hyj_mem, rfl⟩ := hw_mem
          have hyj_in_xs := (h yj).mpr (List.any_eq_true.mpr ⟨yj, hyj_mem, extEq_refl yj⟩)
          rw [List.any_eq_true] at hyj_in_xs
          obtain ⟨xi, hxi_mem, hxi_eq⟩ := hyj_in_xs
          have _hyj_lt := cSize_lt_of_mem hyj_mem
          have _hxi_lt := cSize_lt_of_mem hxi_mem
          have hIH : normalize yj = normalize xi := normalize_eq_of_extEq hxi_eq
          exact ⟨normalize xi, List.mem_map.mpr ⟨xi, hxi_mem, rfl⟩, hIH ▸ hw_eq⟩
      exact SetEquiv.trans (insertionSort_setEquiv _)
        (SetEquiv.trans (dedup_setEquiv_self _)
          (SetEquiv.trans h_nxs_nys
            (SetEquiv.trans (SetEquiv.symm (dedup_setEquiv_self _))
              (SetEquiv.symm (insertionSort_setEquiv _)))))
    -- (4) ∀ a ∈ insertionSort (dedup (xs.map normalize)),
    --     ∀ b ∈ insertionSort (dedup (ys.map normalize)),
    --     extEq a b = true → a = b
    · intro a ha b hb hab
      -- a es normalize xi para algún xi ∈ xs
      have ha' := insertionSort_mem_subset a _ ha
      have ha'' := mem_of_mem_dedup _ a ha'
      rw [List.mem_map] at ha''
      obtain ⟨xi, hxi_mem, rfl⟩ := ha''
      -- b es normalize yj para algún yj ∈ ys
      have hb' := insertionSort_mem_subset b _ hb
      have hb'' := mem_of_mem_dedup _ b hb'
      rw [List.mem_map] at hb''
      obtain ⟨yj, hyj_mem, rfl⟩ := hb''
      -- extEq (normalize xi) (normalize yj) = true
      -- Bound their sizes for termination
      have hxi_bound := cSize_lt_of_mem hxi_mem
      have hyj_bound := cSize_lt_of_mem hyj_mem
      have hxi_norm := normalize_cSize_le xi
      have hyj_norm := normalize_cSize_le yj
      -- Por IH: normalize (normalize xi) = normalize (normalize yj)
      have hIH := normalize_eq_of_extEq hab
      -- Por normalize_idem: normalize (normalize xi) = normalize xi
      rwa [normalize_idem, normalize_idem] at hIH
termination_by CList.cSize A + CList.cSize B
decreasing_by
  all_goals simp_wf
  all_goals simp only [CList.cSize] at *
  all_goals omega

/--
Esta es la función que extrae el representante canónico (una `CList` normalizada)
de un `HFSet` abstracto.
-/
def repr (s : HFSet) : CList :=
  Quotient.lift CList.normalize (fun _ _ h => normalize_eq_of_extEq h) s

def empty : HFSet := Quotient.mk CList.Setoid CList.empty

-- ==================================================================
-- Pertenencia a nivel HFSet
-- ==================================================================

/-- mem respeta extEq en el segundo argumento. -/
private theorem mem_resp_right (x A B : CList) (h : extEq A B = true) :
    mem x A = true → mem x B = true := by
  intro hm
  have hsub : subset A B = true := by
    rw [extEq_def, Bool.and_eq_true] at h; exact h.1
  exact mem_subset x A B hm hsub

/-- mem respeta extEq en el primer argumento (ambas direcciones). -/
private theorem mem_resp_left (x y A : CList) (h : extEq x y = true) :
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

private theorem subset_iff_forall_mem_clist (A B : CList) :
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

-- ==================================================================
-- Axioma de Pares
-- ==================================================================

/-- Construye el par {a, b} a nivel CList. -/
def mkPair (a b : CList) : CList := mk [a, b]

/-- El par {a, b} a nivel HFSet. -/
def pair (a b : HFSet) : HFSet :=
  Quotient.liftOn₂ a b
    (fun x y => toHFSet (mkPair x y))
    (fun x₁ y₁ x₂ y₂ hx hy => by
      apply Quotient.sound
      show extEq (mkPair x₁ y₁) (mkPair x₂ y₂) = true
      simp only [mkPair, extEq_def, Bool.and_eq_true]
      constructor
      · -- subset (mk [x₁, y₁]) (mk [x₂, y₂])
        rw [subset_cons, Bool.and_eq_true]
        constructor
        · rw [mem_cons, mem_cons, mem_nil, Bool.or_false, Bool.or_eq_true]
          exact Or.inl hx
        · rw [subset_cons, Bool.and_eq_true]
          constructor
          · rw [mem_cons, mem_cons, mem_nil, Bool.or_false, Bool.or_eq_true]
            exact Or.inr hy
          · exact subset_nil _
      · -- subset (mk [x₂, y₂]) (mk [x₁, y₁])
        rw [subset_cons, Bool.and_eq_true]
        constructor
        · rw [mem_cons, mem_cons, mem_nil, Bool.or_false, Bool.or_eq_true]
          have : extEq x₂ x₁ = true := by rw [extEq_comm]; exact hx
          exact Or.inl this
        · rw [subset_cons, Bool.and_eq_true]
          constructor
          · rw [mem_cons, mem_cons, mem_nil, Bool.or_false, Bool.or_eq_true]
            have : extEq y₂ y₁ = true := by rw [extEq_comm]; exact hy
            exact Or.inr this
          · exact subset_nil _)

/-- Axioma de Pares: x ∈ pair a b ↔ x = a ∨ x = b. -/
theorem mem_pair (x a b : HFSet) : x ∈ pair a b ↔ x = a ∨ x = b := by
  rcases Quotient.exists_rep x with ⟨xc, rfl⟩
  rcases Quotient.exists_rep a with ⟨ac, rfl⟩
  rcases Quotient.exists_rep b with ⟨bc, rfl⟩
  change CList.mem xc (mkPair ac bc) = true ↔ _
  simp only [mkPair, mem_cons, mem_nil, Bool.or_false, Bool.or_eq_true]
  constructor
  · rintro (hxa | hxb)
    · exact Or.inl (Quotient.sound hxa)
    · exact Or.inr (Quotient.sound hxb)
  · rintro (hxa | hxb)
    · exact Or.inl (Quotient.exact hxa)
    · exact Or.inr (Quotient.exact hxb)

end HFSet
