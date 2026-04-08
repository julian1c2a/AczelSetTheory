import AczelSetTheory.CList.Sort

-- ==========================================
-- Normalización: cotas de tamaño, idempotencia,
-- sorted_nodup_setEquiv_eq
-- ==========================================

namespace CList

-- ==================================================================
-- Cotas de tamaño: normalize no aumenta el cSize
-- ==================================================================

private theorem cSizeList_orderedInsert_le
  (x : CList) (l : List CList) :
    cSizeList (orderedInsert x l) ≤ 1 + cSize x + cSizeList l
      := by
  induction l with
  | nil => simp [orderedInsert, cSizeList]
  | cons y ys ih =>
    unfold orderedInsert
    by_cases h1 : lt x y = true
    · rw [if_pos h1]; simp only [cSizeList]; omega
    · rw [if_neg h1]
      by_cases h2 : extEq x y = true
      · rw [if_pos h2]; simp only [cSizeList]; omega
      · rw [if_neg h2]; simp only [cSizeList]; omega

theorem cSizeList_dedup_le
  (l : List CList) :
    cSizeList (dedup l) ≤ cSizeList l
      := by
  suffices h : ∀ (l' vistos : List CList),
      cSizeList (dedupAux l' vistos) ≤ cSizeList l' from by
    unfold dedup; exact h l []
  intro l'
  induction l' with
  | nil => intros; simp [dedupAux, cSizeList]
  | cons x xs ih =>
    intro vistos
    unfold dedupAux
    by_cases h : (vistos.any fun y => extEq x y) = true
    · rw [if_pos h]; exact Nat.le_trans (ih vistos) (by simp [cSizeList])
    · rw [if_neg h]; simp only [cSizeList]
      exact Nat.le_trans (Nat.add_le_add_left (ih (x :: vistos)) _) (by omega)

theorem cSizeList_insertionSort_le
  (l : List CList) :
    cSizeList (insertionSort l) ≤ cSizeList l
      := by
  induction l with
  | nil => simp [insertionSort, cSizeList]
  | cons x xs ih =>
    unfold insertionSort
    have h1 := cSizeList_orderedInsert_le x (insertionSort xs)
    simp only [cSizeList]
    omega

mutual
  private theorem normalize_cSizeList_le :
      ∀ (xs : List CList),
        cSizeList (xs.map normalize) ≤ cSizeList xs
      | [] => by simp [cSizeList]
      | (x :: rest) => by
        simp only [List.map, cSizeList]
        have hx := normalize_cSize_le x
        have ih := normalize_cSizeList_le rest
        omega
  termination_by xs => cSizeList xs * 2 + 1
  decreasing_by
    all_goals simp_wf
    all_goals simp [cSizeList]
    all_goals omega

  theorem normalize_cSize_le
    (A : CList) :
      cSize (normalize A) ≤ cSize A
        :=
    match A with
    | mk xs => by
        have h_map := normalize_cSizeList_le xs
        have h_red := cSizeList_dedup_le (xs.map normalize)
        have h_ord := cSizeList_insertionSort_le (dedup (xs.map normalize))
        simp only [normalize, cSize]
        omega
  termination_by cSize A * 2
  decreasing_by
    all_goals simp_wf
    all_goals simp [cSize]
    all_goals omega
end

-- ==================================================================
-- Idempotencia de dedup e insertionSort
-- ==================================================================

theorem dedup_id_of_nodup
  (l : List CList) (h : Nodup l) :
    dedup l = l
      := by
  suffices ∀ (l' : List CList) (vistos : List CList),
      Nodup l' →
      (∀ x ∈ l', (vistos.any (fun v => extEq x v)) = false) →
      dedupAux l' vistos = l' by
    unfold dedup; exact this l [] h (by simp)
  intro l'
  induction l' with
  | nil => intros; rfl
  | cons x xs ih =>
    intro vistos hnd hfresh
    have hx_nd : ∀ b ∈ xs, extEq x b = false :=
      (List.pairwise_cons.mp hnd).1
    have hxs_nd : Nodup xs := (List.pairwise_cons.mp hnd).2
    have hx_fresh : (vistos.any (fun v => extEq x v)) = false :=
      hfresh x (List.mem_cons.mpr (Or.inl rfl))
    simp only [dedupAux, if_neg (Bool.eq_false_iff.mp hx_fresh)]
    congr 1
    apply ih (x :: vistos) hxs_nd
    intro y hy
    have hy_fresh := hfresh y (List.mem_cons_of_mem x hy)
    rw [List.any_cons, Bool.or_eq_false_iff]
    exact ⟨by rw [extEq_comm]; exact hx_nd y hy, hy_fresh⟩

theorem insertionSort_id_of_sorted_nodup
  (l : List CList) (hs : Sorted l) (hn : Nodup l) :
    insertionSort l = l
      := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    match xs, hs, hn with
    | [], _, _ => simp [insertionSort, orderedInsert]
    | y :: ys, hs, hn =>
      have hxy     : lt x y = true    := by simp only [Sorted] at hs; exact hs.1
      have hs_tail : Sorted (y :: ys) := by simp only [Sorted] at hs; exact hs.2
      have hn_tail : Nodup (y :: ys)  := (List.pairwise_cons.mp hn).2
      show orderedInsert x (insertionSort (y :: ys)) = x :: y :: ys
      rw [ih hs_tail hn_tail]
      unfold orderedInsert
      rw [if_pos hxy]

-- ==================================================================
-- Idempotencia de normalize
-- ==================================================================

-- Helper: l.map normalize = l cuando cada elemento es punto fijo
private theorem map_normalize_fixed
  (l : List CList) (h : ∀ y ∈ l, normalize y = y) :
    l.map normalize = l
      := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map, List.cons.injEq]
    exact ⟨h x (List.mem_cons.mpr (Or.inl rfl)),
           ih (fun y hy => h y (List.mem_cons_of_mem x hy))⟩

-- Helper: membresía proposicional en dedup
private theorem mem_of_mem_dedupAux :
    ∀ (l : List CList) (vistos : List CList) (y : CList),
    y ∈ dedupAux l vistos → y ∈ l
  | [], _, _, h => by simp [dedupAux] at h
  | x :: xs, vistos, y, h => by
      simp only [dedupAux] at h
      by_cases hseen : (vistos.any fun z => extEq x z) = true
      · rw [if_pos hseen] at h
        exact List.mem_cons_of_mem x (mem_of_mem_dedupAux xs vistos y h)
      · rw [if_neg hseen] at h
        simp only [List.mem_cons] at h
        rcases h with rfl | h
        · exact List.mem_cons.mpr (Or.inl rfl)
        · exact List.mem_cons_of_mem x (mem_of_mem_dedupAux xs (x :: vistos) y h)

theorem mem_of_mem_dedup
  (l : List CList) (y : CList) (h : y ∈ dedup l) :
    y ∈ l
      :=
  mem_of_mem_dedupAux l [] y h

mutual
  /-- normalize es idempotente: normalizar dos veces = normalizar una vez. -/
  theorem normalize_idem :
    (A : CList) → normalize (normalize A) = normalize A
    | mk xs => by
        -- Todos los elementos de ys = insertionSort (dedup (xs.map normalize)) son puntos fijos
        have h_fixed : ∀ y ∈ insertionSort (dedup (xs.map normalize)), normalize y = y := fun y hy =>
          normalize_idem_list xs y
            (mem_of_mem_dedup _ y (insertionSort_mem_subset y _ hy))
        have h_nodup  := insertionSort_nodup _ (dedup_nodup (xs.map normalize))
        have h_sorted := insertionSort_sorted (dedup (xs.map normalize))
        simp only [normalize]
        congr 1
        rw [map_normalize_fixed _ h_fixed,
            dedup_id_of_nodup _ h_nodup,
            insertionSort_id_of_sorted_nodup _ h_sorted h_nodup]
  termination_by A => cSize A * 2
  decreasing_by
    all_goals simp_wf
    all_goals simp [cSize]
    all_goals omega

  -- Lema auxiliar: cada elemento de xs.map normalize es punto fijo de normalize
  private theorem normalize_idem_list :
    (xs : List CList) → ∀ y ∈ xs.map normalize, normalize y = y
    | [] => by simp
    | x :: rest => by
        intro y hy
        simp only [List.map, List.mem_cons] at hy
        rcases hy with rfl | hy
        · exact normalize_idem x
        · exact normalize_idem_list rest y hy
  termination_by xs => cSizeList xs * 2 + 1
  decreasing_by
    all_goals simp_wf
    all_goals simp [cSizeList]
    all_goals omega
end

-- ==================================================================
-- Unicidad: sorted_nodup_setEquiv_eq
-- ==================================================================

/-- Si `a :: l` está ordenada, `l` también lo está. -/
private theorem Sorted.tail {a : CList} {l : List CList}
  (h : Sorted (a :: l)) :
    Sorted l
      := by
  match l with
  | [] => exact trivial
  | _ :: _ => exact h.2

/-- If a list is sorted and b is a member, then lt a b = true -/
private theorem sorted_mem_lt {a : CList} {l : List CList}
  (hs : Sorted (a :: l)) (hm : b ∈ l) :
    lt a b = true
      := by
  match l with
  | [] => simp at hm
  | c :: rest =>
    rcases List.mem_cons.mp hm with rfl | hrest
    · exact hs.1
    · exact lt_trans a c b hs.1 (sorted_mem_lt hs.2 hrest)

-- Unicidad: dos listas Sorted+Nodup+SetEquiv son iguales, dado que extEq implica eq en su contexto
theorem sorted_nodup_setEquiv_eq :
    ∀ (l₁ l₂ : List CList),
    Sorted l₁ → Sorted l₂ →
    Nodup l₁ → Nodup l₂ →
    SetEquiv l₁ l₂ →
    (∀ a ∈ l₁, ∀ b ∈ l₂, extEq a b = true → a = b) →
    l₁ = l₂
  | [], l₂, _, _, _, _, hequiv, _ => by
      rcases l₂ with _ | ⟨y, ys⟩
      · rfl
      · exfalso
        have := (hequiv y).mpr (by simp [List.any_cons, extEq_refl])
        simp at this
  | x :: xs, [], _, _, _, _, hequiv, _ => by
      exfalso
      have := (hequiv x).mp (by simp [List.any_cons, extEq_refl])
      simp at this
  | x :: xs, y :: ys, hs1, hs2, hn1, hn2, hequiv, hprop => by
      -- Paso 1: x = y
      have hxy_extEq : extEq x y = true := by
        have hx_in : (List.any (y :: ys) (fun z => extEq x z)) = true := by
          have := (hequiv x).mp (by simp [List.any_cons, extEq_refl])
          exact this
        simp only [List.any_cons, Bool.or_eq_true] at hx_in
        rcases hx_in with h | h
        · exact h
        · -- x está en ys; como l₂ está ordenada, y < z para z ∈ ys,
          -- pero x = y (primer elemento de l₁ y mínimo)
          -- Vía: l₁ también tiene y como miembro (por SetEquiv)
          have hy_in_l1 : (List.any (x :: xs) (fun z => extEq y z)) = true := by
            have := (hequiv y).mpr (by simp [List.any_cons, extEq_refl])
            exact this
          simp only [List.any_cons, Bool.or_eq_true] at hy_in_l1
          rcases hy_in_l1 with h_yx | h_yx
          · rwa [extEq_comm]
          · -- y ∈ xs y x ∈ ys: x < y (Sorted l₂) y y < x (Sorted l₁)
            -- Contradicción con lt_asymm
            -- First, derive y ∈ xs (literally) from h_yx and hprop
            have ⟨w, hw_mem, hw_eq⟩ := List.any_eq_true.mp h_yx
            have hw_eq_y : w = y := by
              have : extEq y w = true := hw_eq
              have hcomm : extEq w y = true := by rwa [extEq_comm]
              exact hprop w (List.mem_cons_of_mem x hw_mem) y
                (List.mem_cons.mpr (Or.inl rfl)) hcomm
            have hy_in_xs : y ∈ xs := hw_eq_y ▸ hw_mem
            -- Derive x ∈ ys (literally) from h and hprop
            have ⟨v, hv_mem, hv_eq⟩ := List.any_eq_true.mp h
            have hv_eq_x : x = v :=
              hprop x (List.mem_cons.mpr (Or.inl rfl)) v
                (List.mem_cons_of_mem y hv_mem) hv_eq
            have hx_in_ys : x ∈ ys := hv_eq_x ▸ hv_mem
            -- Now use sorted_mem_lt
            have hltxy : lt x y = true := sorted_mem_lt hs1 hy_in_xs
            have hltyx : lt y x = true := sorted_mem_lt hs2 hx_in_ys
            exact absurd hltyx (by rw [lt_asymm x y hltxy]; simp)
      have hxy_eq : x = y := hprop x List.mem_cons_self y (List.mem_cons.mpr (Or.inl rfl)) hxy_extEq
      -- Paso 2: las colas son SetEquiv
      have htail_equiv : SetEquiv xs ys := by
        intro z
        have hfull := hequiv z
        simp only [List.any_cons] at hfull
        constructor
        · intro hz_xs
          have := hfull.mp (by simp [hz_xs])
          simp only [Bool.or_eq_true] at this
          rcases this with h | h
          · -- extEq z y = true, pero z ∈ xs y Nodup (x :: xs) → contradicción
            exfalso
            obtain ⟨w, hw_mem, hw_eq⟩ := List.any_eq_true.mp hz_xs
            have hyz : extEq y z = true := by rwa [extEq_comm]
            have hxz : extEq x z = true := by rw [hxy_eq]; exact hyz
            have hxw : extEq x w = true := extEq_trans x z w hxz hw_eq
            have hxw_f := (List.pairwise_cons.mp hn1).1 w hw_mem
            simp [hxw] at hxw_f
          · exact h
        · intro hz_ys
          have := hfull.mpr (by simp [hz_ys])
          simp only [Bool.or_eq_true] at this
          rcases this with h | h
          · exfalso
            obtain ⟨w, hw_mem, hw_eq⟩ := List.any_eq_true.mp hz_ys
            have hzy : extEq z y = true := by rw [← hxy_eq]; exact h
            have hyz : extEq y z = true := by rwa [extEq_comm]
            have hyw : extEq y w = true := extEq_trans y z w hyz hw_eq
            have hyw_f := (List.pairwise_cons.mp hn2).1 w hw_mem
            simp [hyw] at hyw_f
          · exact h
      -- Paso 3: aplicar IH
      have hs1' : Sorted xs := hs1.tail
      have hs2' : Sorted ys := hs2.tail
      have hn1' : Nodup xs  := (List.pairwise_cons.mp hn1).2
      have hn2' : Nodup ys  := (List.pairwise_cons.mp hn2).2
      have hprop' : ∀ a ∈ xs, ∀ b ∈ ys, extEq a b = true → a = b :=
        fun a ha b hb hab => hprop a (List.mem_cons_of_mem x ha) b (List.mem_cons_of_mem y hb) hab
      rw [hxy_eq, sorted_nodup_setEquiv_eq xs ys hs1' hs2' hn1' hn2' htail_equiv hprop']

theorem extEq_normalize
  (A : CList) :
    extEq A (normalize A) = true
      := by
  match A with
  | mk xs =>
    simp only [normalize]
    rw [extEq_mk_iff_setEquiv]
    have ih_all : ∀ w ∈ xs, extEq w (normalize w) = true := fun w hw =>
      have : cSize w < cSize (mk xs) := cSize_lt_of_mem hw
      extEq_normalize w
    apply SetEquiv.trans (l₂ := xs.map normalize)
    · intro z
      constructor
      · intro hz
        obtain ⟨w, hw_mem, hw_eq⟩ := List.any_eq_true.mp hz
        apply List.any_eq_true.mpr
        have hw_ih : extEq w (normalize w) = true := ih_all w hw_mem
        exact ⟨normalize w, List.mem_map.mpr ⟨w, hw_mem, rfl⟩, extEq_trans z w (normalize w) hw_eq hw_ih⟩
      · intro hz
        obtain ⟨w_norm, hw_norm_mem, hw_norm_eq⟩ := List.any_eq_true.mp hz
        obtain ⟨w, hw_mem, rfl⟩ := List.mem_map.mp hw_norm_mem
        apply List.any_eq_true.mpr
        have hw_ih : extEq (normalize w) w = true := by rw [extEq_comm]; exact ih_all w hw_mem
        exact ⟨w, hw_mem, extEq_trans z (normalize w) w hw_norm_eq hw_ih⟩
    · apply SetEquiv.trans (l₂ := dedup (xs.map normalize))
      · exact SetEquiv.symm (dedup_setEquiv_self _)
      · exact SetEquiv.symm (insertionSort_setEquiv _)
termination_by cSize A
decreasing_by
  all_goals simp_wf
  all_goals exact cSize_lt_of_mem hw

/-!
Dadas dos CList A y B que son extensionalmente iguales,
sus formas normales son idénticas.
-/
theorem normalize_eq_of_extEq {A B : CList}
  (h : CList.extEq A B = true) :
    CList.normalize A = CList.normalize B
      := by
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
termination_by cSize A + cSize B
decreasing_by
  all_goals simp_wf
  all_goals simp only [cSize] at *
  all_goals omega

theorem extEq_iff_normalize_eq {A B : CList} :
    extEq A B = true ↔ normalize A = normalize B
      := by
  constructor
  · exact normalize_eq_of_extEq
  · intro h
    have ha : extEq A (normalize A) = true := extEq_normalize A
    have hb : extEq B (normalize B) = true := extEq_normalize B
    have hb_symm : extEq (normalize B) B = true := by rw [extEq_comm]; exact hb
    have h1 : extEq A (normalize B) = true := by rw [h] at ha; exact ha
    exact extEq_trans A (normalize B) B h1 hb_symm

end CList
