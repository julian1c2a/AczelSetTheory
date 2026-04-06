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

end HFSet
