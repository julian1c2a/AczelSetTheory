import Init.Data.List.Basic

-- ==========================================
-- FASE 1: CList (La estructura computacional)
-- ==========================================

/--
Definición de nuestro pre-conjunto basado en listas.
-/
inductive CList : Type where
  | mk : List CList → CList
  deriving Repr, Inhabited

namespace CList

-- Función de tamaño personalizada (evita el _sizeOf_inst no compilable para inductivos anidados)
mutual
  def cSize : CList → Nat
    | mk xs => 1 + cSizeList xs
  def cSizeList : List CList → Nat
    | [] => 0
    | x :: xs => 1 + cSize x + cSizeList xs
end

/-- El conjunto vacío computacional -/
def empty : CList := mk []

-- 1. LÓGICA DE COMPARACIÓN BASE (Semántica de conjuntos)

inductive CListOp
| mem
| subset
| eq

@[simp] def opWeight : CListOp → Nat
| .mem => 0
| .subset => 1
| .eq => 2

set_option linter.unusedSimpArgs false in
/--
Motor lógico para la igualdad extensional.
Agrupamos estas tres para que Lean pueda verificar la terminación mutua.
-/
def evalOp (op : CListOp) (A B : CList) : Bool :=
  match op, A, B with
  | .mem, _, mk [] => false
  | .mem, x, mk (y :: ys) =>
      evalOp .eq x y || evalOp .mem x (mk ys)

  | .subset, mk [], _ => true
  | .subset, mk (x :: xs), B =>
      evalOp .mem x B && evalOp .subset (mk xs) B

  | .eq, A, B =>
      evalOp .subset A B && evalOp .subset B A
termination_by (((sizeOf A + sizeOf B) * 3) + opWeight op)
decreasing_by
  all_goals
    simp_wf
    try simp [opWeight, sizeOf]
    try simp_arith
    try omega

/-- Comprueba si un elemento mem a un conjunto. -/
def mem (x A : CList) : Bool := evalOp .mem x A

/-- Comprueba si A es subconjunto de B. -/
def subset (A B : CList) : Bool := evalOp .subset A B

/-- Comprueba la igualdad extensional (mismos elementos). -/
def extEq (A B : CList) : Bool := evalOp .eq A B

instance : BEq CList where beq := extEq

-- 2. ORDEN TOTAL (Para la canonización)

/-!
Define un orden total independiente de la igualdad para poder
ordenar las listas de forma única.
Nota: Usamos el tamaño estructural directo para garantizar la terminación.
-/
def lt (A B : CList) : Bool :=
  if cSize A < cSize B then true
  else if cSize A > cSize B then false
  else match A, B with
    | mk [], mk [] => false
    | mk [], mk (_::_) => true
    | mk (_::_), mk [] => false
    | mk (x::xs), mk (y::ys) =>
        if extEq x y then
          lt (mk xs) (mk ys)
        else
          lt x y
termination_by cSize A + cSize B
decreasing_by
  all_goals simp_wf
  all_goals simp [cSize, cSizeList]
  all_goals omega

-- 3. ALGORITMO DE REDUCCIÓN (Limpieza estructural)

/--
Función auxiliar que mantiene una lista de elementos 'vistos'
para ignorar las apariciones posteriores.
Es estructuralmente recursiva (recorre `l` reduciéndola en 1),
por lo que Lean la acepta instantáneamente sin pruebas matemáticas.
-/
def dedupAux (l : List CList) (vistos : List CList) : List CList :=
  match l with
  | [] => []
  | x :: xs =>
      if vistos.any (fun y => extEq x y) then
        -- Si ya lo vimos antes, lo ignoramos y seguimos
        dedupAux xs vistos
      else
        -- Si es nuevo, lo guardamos y lo añadimos a los 'vistos'
        x :: dedupAux xs (x :: vistos)

/--
Reduce los duplicados de una lista recorriéndola hacia adelante
y conservando solo la primera aparición de cada elemento.
-/
def dedup (l : List CList) : List CList :=
  dedupAux l []

-- 4. CANONIZACIÓN (Forma normal)

def orderedInsert (x : CList) : List CList → List CList
  | [] => [x]
  | y :: ys =>
      if lt x y then x :: y :: ys
      else if extEq x y then y :: ys
      else y :: orderedInsert x ys

def insertionSort : List CList → List CList
  | [] => []
  | x :: xs => orderedInsert x (insertionSort xs)

/--
Normalización canónica:
Aplica la normalización a los elementos, elimina duplicados y ordena.
-/
def normalize : CList → CList
  | mk xs =>
      let hijosNorm := xs.map normalize
      let sinDuplicados := dedup hijosNorm
      mk (insertionSort sinDuplicados)

-- PRUEBAS
def zero := empty
def one := mk [zero]
def two := mk [zero, one]
def three := mk [zero, one, two]
def dirty := mk [one, two, zero, three, one, zero, zero, two, three, two]

end CList

-- ==========================================
-- FASE 2: CSet (Tipo Cociente)
-- ==========================================

-- Si mk xs ⊆ mk ys, entonces mk xs ⊆ mk (y::ys)
theorem subset_mono (xs : List CList) (y : CList) (ys : List CList)
    (h : CList.evalOp .subset (CList.mk xs) (CList.mk ys) = true) :
    CList.evalOp .subset (CList.mk xs) (CList.mk (y :: ys)) = true := by
  induction xs with
  | nil => simp [CList.evalOp]
  | cons z zs ih =>
    simp only [CList.evalOp, Bool.and_eq_true] at h ⊢
    exact ⟨by simp [h.1], ih h.2⟩

-- A ⊆ A para todo CList (recursión bien fundada por cSize)
theorem subset_refl (A : CList) : CList.subset A A = true := by
  match A with
  | CList.mk [] => simp [CList.subset, CList.evalOp]
  | CList.mk (x :: xs) =>
    have hx  : CList.subset x x = true             := subset_refl x
    have hxs : CList.subset (CList.mk xs) (CList.mk xs) = true := subset_refl (CList.mk xs)
    simp only [CList.subset] at hx hxs
    simp only [CList.subset, CList.evalOp, Bool.and_eq_true]
    exact ⟨by simp [hx], subset_mono xs x xs hxs⟩
termination_by CList.cSize A
decreasing_by
  all_goals simp_wf
  all_goals simp [CList.cSize, CList.cSizeList]
  all_goals omega

-- extEq A A = true (no recursivo: usa subset_refl)
theorem extEq_refl (A : CList) : CList.extEq A A = true := by
  simp only [CList.extEq, CList.evalOp, Bool.and_eq_true]
  exact ⟨subset_refl A, subset_refl A⟩


-- ==============================================================
-- DEMOSTRACIÓN DE TRANSITIVIDAD (El Santo Grial Estructural)
-- ==============================================================
namespace CList

-- Lemas de apoyo genéricos
private def bool_and_split {a b : Bool} (h : a && b = true) : a = true ∧ b = true := by
  cases a <;> cases b <;> simp_all

private def bool_or_split {a b : Bool} (h : a || b = true) : a = true ∨ b = true := by
  cases a <;> cases b <;> simp_all

private def bool_and_join {a b : Bool} (ha : a = true) (hb : b = true) : a && b = true := by
  simp [ha, hb]

private def bool_or_join_left {a b : Bool} (ha : a = true) : a || b = true := by
  simp [ha]

private def bool_or_join_right {a b : Bool} (hb : b = true) : a || b = true := by
  simp [hb]

-- Lemas de reducción (necesarios porque evalOp usa recursión bien fundada)
theorem extEq_def (A B : CList) :
    extEq A B = (subset A B && subset B A) := by
  simp only [extEq, subset, evalOp]

theorem subset_nil (B : CList) :
    subset (mk []) B = true := by
  simp only [subset, evalOp]

theorem subset_cons (x : CList) (xs : List CList) (B : CList) :
    subset (mk (x :: xs)) B = (mem x B && subset (mk xs) B) := by
  simp only [subset, mem, evalOp]

theorem mem_nil (x : CList) :
    mem x (mk []) = false := by
  simp only [mem, evalOp]

theorem mem_cons (x y : CList) (ys : List CList) :
    mem x (mk (y :: ys)) = (extEq x y || mem x (mk ys)) := by
  simp only [mem, extEq, evalOp]

-- Transitividad mutua (tactic mode para compatibilidad con Lean 4.28)
mutual
  theorem extEq_trans :
    (A B C : CList) → (extEq A B = true) → (extEq B C = true) → (extEq A C = true)
    | A, B, C, h1, h2 => by
      simp only [extEq_def, Bool.and_eq_true] at h1 h2 ⊢
      exact ⟨subset_trans A B C h1.1 h2.1, subset_trans C B A h2.2 h1.2⟩
  termination_by A B C _ _ => (cSize A + cSize B + cSize C) * 2 + 1
  decreasing_by
    all_goals simp_wf
    all_goals try simp [cSize, cSizeList]
    all_goals try omega

  theorem subset_trans : (A B C : CList) → subset A B = true → subset B C = true → subset A C = true
    | mk [], _, _, _, _ => subset_nil _
    | mk (x :: xs), B, C, h1, h2 => by
      simp only [subset_cons, Bool.and_eq_true] at h1 ⊢
      exact ⟨mem_subset x B C h1.1 h2, subset_trans (mk xs) B C h1.2 h2⟩
  termination_by A B C _ _ => (cSize A + cSize B + cSize C) * 2
  decreasing_by
    all_goals simp_wf
    all_goals try simp [cSize, cSizeList]
    all_goals try omega

  theorem mem_subset : (x B C : CList) → mem x B = true → subset B C = true → mem x C = true
    | _, mk [], _, h1, _ => by simp [mem_nil] at h1
    | x, mk (y :: ys), C, h1, h2 => by
      simp only [mem_cons, Bool.or_eq_true] at h1
      simp only [subset_cons, Bool.and_eq_true] at h2
      cases h1 with
      | inl h1_eq => exact mem_of_extEq x y C h1_eq h2.1
      | inr h1_mem => exact mem_subset x (mk ys) C h1_mem h2.2
  termination_by x B C _ _ => (cSize x + cSize B + cSize C) * 2
  decreasing_by
    all_goals simp_wf
    all_goals try simp [cSize, cSizeList]
    all_goals try omega

  theorem mem_of_extEq : (x y C : CList) → extEq x y = true → mem y C = true → mem x C = true
    | _, _, mk [], _, h2 => by simp [mem_nil] at h2
    | x, y, mk (z :: zs), h1, h2 => by
      simp only [mem_cons, Bool.or_eq_true] at h2 ⊢
      cases h2 with
      | inl h2_eq => exact Or.inl (extEq_trans x y z h1 h2_eq)
      | inr h2_mem => exact Or.inr (mem_of_extEq x y (mk zs) h1 h2_mem)
  termination_by x y C _ _ => (cSize x + cSize y + cSize C) * 2
  decreasing_by
    all_goals simp_wf
    all_goals try simp [cSize, cSizeList]
    all_goals try omega
end

/--
Define la propiedad de que una lista no tiene duplicados según `extEq`.
-/
def Nodup (l : List CList) : Prop :=
  l.Pairwise (fun a b => extEq a b = false)

-- Lema: dedup produce una lista sin duplicados.
theorem dedup_nodup (l : List CList) : Nodup (dedup l) := by
  have stronger_lemma : ∀ (l' : List CList) (vistos : List CList),
    Nodup (dedupAux l' vistos) ∧
    (∀ y ∈ (dedupAux l' vistos), (vistos.any (fun z => extEq y z)) = false) := by
    intro l'
    induction l' with
    | nil =>
      intro _; simp [dedupAux, Nodup]
    | cons head tail IH =>
      intro vistos
      simp only [dedupAux]
      by_cases h_seen : (vistos.any fun y => extEq head y) = true
      · rw [if_pos h_seen]; exact IH vistos
      · rw [if_neg h_seen]
        have h_false : (vistos.any fun y => extEq head y) = false :=
          Bool.eq_false_iff.mpr (fun h => h_seen h)
        have ih_recursed := IH (head :: vistos)
        rcases ih_recursed with ⟨nodup_tail, tail_is_new⟩
        constructor
        · simp only [Nodup, List.pairwise_cons]
          constructor
          · have extEq_comm : ∀ a b, extEq a b = extEq b a := by
              intros a b; simp [extEq, evalOp, Bool.and_comm]
            intro y y_in_tail
            specialize tail_is_new y y_in_tail
            rw [List.any_cons, Bool.or_eq_false_iff] at tail_is_new
            rw [extEq_comm]; exact tail_is_new.1
          · exact nodup_tail
        · intro y y_in_list
          simp only [List.mem_cons] at y_in_list
          cases y_in_list with
          | inl h_y_eq_head =>
            rw [h_y_eq_head]; exact h_false
          | inr h_y_in_tail =>
            specialize tail_is_new y h_y_in_tail
            rw [List.any_cons, Bool.or_eq_false_iff] at tail_is_new
            exact tail_is_new.2
  rw [dedup]
  exact (stronger_lemma l []).1

/--
Define la equivalencia de conjuntos entre dos listas.
-/
def SetEquiv (l₁ l₂ : List CList) : Prop :=
  ∀ x, (l₁.any (fun y => extEq x y)) ↔ (l₂.any (fun y => extEq x y))

namespace SetEquiv

@[refl]
theorem refl (l : List CList) : SetEquiv l l := by
  intro _; exact Iff.rfl

@[symm]
theorem symm {l₁ l₂ : List CList} (h : SetEquiv l₁ l₂) : SetEquiv l₂ l₁ := by
  intro x; exact (h x).symm

theorem trans {l₁ l₂ l₃ : List CList} (h₁₂ : SetEquiv l₁ l₂) (h₂₃ : SetEquiv l₂ l₃) :
    SetEquiv l₁ l₃ := by
  intro x; exact (h₁₂ x).trans (h₂₃ x)

end SetEquiv

theorem mem_eq_any (x : CList) (l : List CList) :
    mem x (mk l) = l.any (fun y => extEq x y) := by
  induction l with
  | nil => simp [mem_nil]
  | cons y ys ih => simp [mem_cons, ih]

private theorem subset_iff_forall_mem (l₁ l₂ : List CList) :
    subset (mk l₁) (mk l₂) = true ↔ (∀ x ∈ l₁, mem x (mk l₂) = true) := by
  induction l₁ with
  | nil => simp [subset_nil]
  | cons x xs ih =>
    simp only [subset_cons, Bool.and_eq_true]
    constructor
    · intro ⟨h1, h2⟩ y hy
      simp only [List.mem_cons] at hy
      rcases hy with rfl | hy
      · exact h1
      · exact ih.mp h2 y hy
    · intro h
      exact ⟨h x List.mem_cons_self, ih.mpr (fun y hy => h y (List.mem_cons_of_mem _ hy))⟩

theorem extEq_mk_iff_setEquiv (l₁ l₂ : List CList) :
    extEq (mk l₁) (mk l₂) = true ↔ SetEquiv l₁ l₂ := by
  constructor
  · intro h
    unfold SetEquiv
    rw [extEq_def, Bool.and_eq_true] at h
    simp only [subset_iff_forall_mem, mem_eq_any] at h
    obtain ⟨h1, h2⟩ := h
    intro x
    constructor
    · intro hx
      rw [List.any_eq_true] at hx
      obtain ⟨z, hz, hxz⟩ := hx
      have hzl2 := h1 z hz
      rw [List.any_eq_true] at hzl2
      obtain ⟨w, hw, hzw⟩ := hzl2
      exact List.any_eq_true.mpr ⟨w, hw, extEq_trans x z w hxz hzw⟩
    · intro hx
      rw [List.any_eq_true] at hx
      obtain ⟨z, hz, hxz⟩ := hx
      have hzl1 := h2 z hz
      rw [List.any_eq_true] at hzl1
      obtain ⟨w, hw, hzw⟩ := hzl1
      exact List.any_eq_true.mpr ⟨w, hw, extEq_trans x z w hxz hzw⟩
  · intro h
    unfold SetEquiv at h
    rw [extEq_def, Bool.and_eq_true]
    simp only [subset_iff_forall_mem, mem_eq_any]
    exact ⟨fun x hx => (h x).mp  (List.any_eq_true.mpr ⟨x, hx, extEq_refl x⟩),
           fun x hx => (h x).mpr (List.any_eq_true.mpr ⟨x, hx, extEq_refl x⟩)⟩

-- Lema: `dedup` conserva el conjunto de elementos.
theorem dedup_setEquiv_self (l : List CList) : SetEquiv (dedup l) l := by
  intro x; constructor
  · intro h_mem_reduced
    rw [List.any_eq_true] at h_mem_reduced
    obtain ⟨z, z_in_reduced, xz_eq⟩ := h_mem_reduced
    have z_in_l_ext : (l.any (fun y => extEq z y)) = true := by
      have helper : ∀ (l' vistos : List CList), ∀ z' ∈ (dedupAux l' vistos),
          (l'.any (fun y => extEq z' y)) = true ∨ (vistos.any (fun y => extEq z' y)) = true := by
        intro l'
        induction l' with
        | nil => intro vistos z' h_mem; cases h_mem
        | cons head tail IH =>
          intro vistos z' h_mem
          unfold dedupAux at h_mem
          by_cases h_seen : (vistos.any (fun y => extEq head y)) = true
          · rw [if_pos h_seen] at h_mem
            rcases IH vistos z' h_mem with (h | h)
            · exact Or.inl (by simp [List.any_cons, h])
            · exact Or.inr h
          · rw [if_neg h_seen] at h_mem
            simp only [List.mem_cons] at h_mem
            rcases h_mem with (rfl | h_in_tail)
            · exact Or.inl (by simp [List.any_cons, extEq_refl])
            · rcases IH (head :: vistos) z' h_in_tail with (h_in_t | h_in_v)
              · exact Or.inl (by simp [List.any_cons, h_in_t])
              · rw [List.any_cons, Bool.or_eq_true] at h_in_v
                rcases h_in_v with (h_head | h_vis)
                · exact Or.inl (by simp [List.any_cons, h_head])
                · exact Or.inr h_vis
      rw [dedup] at z_in_reduced
      rcases helper l [] z z_in_reduced with (h | h)
      · exact h
      · simp at h
    rw [List.any_eq_true] at z_in_l_ext
    obtain ⟨w, w_in_l, zw_eq⟩ := z_in_l_ext
    exact List.any_eq_true.mpr ⟨w, w_in_l, CList.extEq_trans x z w xz_eq zw_eq⟩
  · intro h_mem_l
    rw [List.any_eq_true] at h_mem_l
    obtain ⟨z, z_in_l, xz_eq⟩ := h_mem_l
    have completeness_aux : ∀ z' ∈ l, (dedup l).any (fun y => extEq z' y) = true := by
      have helper : ∀ (l' vistos : List CList), ∀ z' ∈ l',
          (dedupAux l' vistos).any (fun y => extEq z' y) = true ∨
          (vistos.any (fun y => extEq z' y)) = true := by
        intro l'
        induction l' with
        | nil => intro vistos z' h_mem; cases h_mem
        | cons hd tail IH =>
          intro vistos z' h_mem
          simp only [dedupAux]
          rcases List.mem_cons.mp h_mem with (rfl | h_in_tail)
          · by_cases h_seen : (vistos.any (fun y => extEq z' y)) = true
            · rw [if_pos h_seen]; exact Or.inr h_seen
            · rw [if_neg h_seen]
              exact Or.inl (List.any_eq_true.mpr ⟨z', List.mem_cons_self, extEq_refl _⟩)
          · by_cases h_seen : (vistos.any (fun y => extEq hd y)) = true
            · rw [if_pos h_seen]; exact IH vistos z' h_in_tail
            · rw [if_neg h_seen]
              rcases IH (hd :: vistos) z' h_in_tail with (h_in_res | h_in_v_ext)
              · rw [List.any_eq_true] at h_in_res
                obtain ⟨w, hw, hwz⟩ := h_in_res
                exact Or.inl (List.any_eq_true.mpr ⟨w, List.mem_cons_of_mem hd hw, hwz⟩)
              · rw [List.any_cons, Bool.or_eq_true] at h_in_v_ext
                rcases h_in_v_ext with (h_hd | h_vis)
                · exact Or.inl (by simp [List.any_cons, h_hd])
                · exact Or.inr h_vis
      intro z' hz'
      rw [dedup]
      rcases helper l [] z' hz' with (h | h)
      · exact h
      · simp at h
    have hz := completeness_aux z z_in_l
    rw [List.any_eq_true] at hz
    obtain ⟨w, w_in_reduced, zw_eq⟩ := hz
    exact List.any_eq_true.mpr ⟨w, w_in_reduced, CList.extEq_trans x z w xz_eq zw_eq⟩


-- ==================================================================
-- TEOREMA 1: normalize no aumenta el tamaño (normalize_cSize_le)
-- ==================================================================

private theorem cSizeList_orderedInsert_le (x : CList) (l : List CList) :
    cSizeList (orderedInsert x l) ≤ 1 + cSize x + cSizeList l := by
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

theorem cSizeList_dedup_le (l : List CList) :
    cSizeList (dedup l) ≤ cSizeList l := by
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

theorem cSizeList_insertionSort_le (l : List CList) :
    cSizeList (insertionSort l) ≤ cSizeList l := by
  induction l with
  | nil => simp [insertionSort, cSizeList]
  | cons x xs ih =>
    unfold insertionSort
    have h1 := cSizeList_orderedInsert_le x (insertionSort xs)
    simp only [cSizeList]
    omega

mutual
  private theorem normalize_cSizeList_le : ∀ (xs : List CList),
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

  theorem normalize_cSize_le (A : CList) : cSize (normalize A) ≤ cSize A :=
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
-- PIEZA 4: Propiedades de lt
-- ==================================================================

theorem lt_irrefl (A : CList) : lt A A = false :=
  match A with
  | mk [] => by unfold lt; simp
  | mk (x :: xs) => by
      unfold lt
      simp only [Nat.lt_irrefl, ite_false, gt_iff_lt, extEq_refl, ite_true]
      exact lt_irrefl (mk xs)
termination_by cSize A
decreasing_by simp_wf; simp [cSize, cSizeList]; omega

theorem extEq_comm (A B : CList) : extEq A B = extEq B A := by
  simp [extEq_def, Bool.and_comm]

private theorem extEq_cons_equiv (x y : CList) (xs ys : List CList)
    (hxy : extEq x y = true) (hxsys : extEq (mk xs) (mk ys) = true) :
    extEq (mk (x :: xs)) (mk (y :: ys)) = true := by
  rw [extEq_mk_iff_setEquiv] at *
  intro z
  simp only [List.any_cons, Bool.or_eq_true]
  constructor
  · rintro (h | h)
    · exact Or.inl (extEq_trans z x y h hxy)
    · exact Or.inr ((hxsys z).mp h)
  · rintro (h | h)
    · have hyx : extEq y x = true := by rwa [extEq_comm] at hxy
      exact Or.inl (extEq_trans z y x h hyx)
    · exact Or.inr ((hxsys z).mpr h)

theorem lt_total (A B : CList) :
    extEq A B = false → lt A B = true ∨ lt B A = true := by
  intro h_neq
  by_cases hlt : cSize A < cSize B
  · left
    unfold lt
    simp [hlt]
  · by_cases hgt : cSize B < cSize A
    · right
      unfold lt
      simp [hgt]
    · have hsize : cSize A = cSize B :=
          Nat.le_antisymm (Nat.le_of_not_lt hgt) (Nat.le_of_not_lt hlt)
      match A, B with
      | mk [], mk [] => simp [extEq_refl] at h_neq
      | mk [], mk (_ :: _) => simp [cSize, cSizeList] at hsize
      | mk (_ :: _), mk [] => simp [cSize, cSizeList] at hsize
      | mk (x :: xs), mk (y :: ys) =>
          by_cases hxy : extEq x y = true
          · have h_tail : extEq (mk xs) (mk ys) = false := by
              rcases Bool.eq_false_or_eq_true (extEq (mk xs) (mk ys)) with h | h
              · have hcontra := extEq_cons_equiv x y xs ys hxy h
                rw [hcontra] at h_neq
                exact absurd h_neq (by decide)
              · exact h
            have hyx : extEq y x = true := by rwa [extEq_comm] at hxy
            rcases lt_total (mk xs) (mk ys) h_tail with h | h
            · left
              unfold lt
              rw [if_neg (show ¬ cSize (mk (x::xs)) < cSize (mk (y::ys)) from by omega)]
              rw [if_neg (show ¬ cSize (mk (x::xs)) > cSize (mk (y::ys)) from by omega)]
              show (if extEq x y = true then lt (mk xs) (mk ys) else lt x y) = true
              rw [if_pos hxy]; exact h
            · right
              unfold lt
              rw [if_neg (show ¬ cSize (mk (y::ys)) < cSize (mk (x::xs)) from by omega)]
              rw [if_neg (show ¬ cSize (mk (y::ys)) > cSize (mk (x::xs)) from by omega)]
              show (if extEq y x = true then lt (mk ys) (mk xs) else lt y x) = true
              rw [if_pos hyx]; exact h
          · rw [Bool.not_eq_true] at hxy
            have hyx : extEq y x = false := by rwa [extEq_comm] at hxy
            rcases lt_total x y hxy with h | h
            · left
              unfold lt
              rw [if_neg (show ¬ cSize (mk (x::xs)) < cSize (mk (y::ys)) from by omega)]
              rw [if_neg (show ¬ cSize (mk (x::xs)) > cSize (mk (y::ys)) from by omega)]
              show (if extEq x y = true then lt (mk xs) (mk ys) else lt x y) = true
              rw [if_neg (show ¬ extEq x y = true from by simp [hxy])]; exact h
            · right
              unfold lt
              rw [if_neg (show ¬ cSize (mk (y::ys)) < cSize (mk (x::xs)) from by omega)]
              rw [if_neg (show ¬ cSize (mk (y::ys)) > cSize (mk (x::xs)) from by omega)]
              show (if extEq y x = true then lt (mk ys) (mk xs) else lt y x) = true
              rw [if_neg (show ¬ extEq y x = true from by simp [hyx])]; exact h
termination_by cSize A + cSize B
decreasing_by
  all_goals simp_wf
  all_goals simp [cSize, cSizeList]
  all_goals omega

-- ==================================================================
-- PIEZA 2: Sorted, insertionSort_sorted, insertionSort_nodup
-- ==================================================================

def Sorted : List CList → Prop
  | []           => True
  | [_]          => True
  | a :: b :: rest => lt a b = true ∧ Sorted (b :: rest)

private theorem orderedInsert_sorted (x : CList) (l : List CList)
    (hs : Sorted l) : Sorted (orderedInsert x l) := by
  induction l with
  | nil => simp [orderedInsert, Sorted]
  | cons y ys ih =>
    simp only [orderedInsert]
    by_cases hxy : lt x y = true
    · rw [if_pos hxy]
      match ys with
      | []     => simp [Sorted, hxy]
      | z :: _ => exact ⟨hxy, hs⟩
    · rw [if_neg hxy]
      by_cases heq : extEq x y = true
      · rw [if_pos heq]; exact hs
      · rw [if_neg heq]
        have hyx : lt y x = true := by
          rcases lt_total x y (by simp [heq]) with h | h
          · exact absurd h (by simp [hxy])
          · exact h
        match ys with
        | [] => simp [orderedInsert, Sorted, hyx]
        | z :: rest =>
          obtain ⟨hyz, hs_rest⟩ := hs
          specialize ih hs_rest
          -- ih : Sorted (orderedInsert x (z :: rest))
          -- goal : Sorted (y :: orderedInsert x (z :: rest))
          by_cases hxz : lt x z = true
          · have hins : orderedInsert x (z :: rest) = x :: z :: rest := by
              unfold orderedInsert; rw [if_pos hxz]
            rw [hins] at ih ⊢
            exact ⟨hyx, hxz, hs_rest⟩
          · by_cases heqz : extEq x z = true
            · have hins : orderedInsert x (z :: rest) = z :: rest := by
                unfold orderedInsert; rw [if_neg hxz, if_pos heqz]
              rw [hins] at ih ⊢
              exact ⟨hyz, hs_rest⟩
            · have hins : orderedInsert x (z :: rest) = z :: orderedInsert x rest := by
                simp only [orderedInsert, if_neg hxz, if_neg heqz]
              rw [hins] at ih ⊢
              exact ⟨hyz, ih⟩

theorem insertionSort_sorted (l : List CList) : Sorted (insertionSort l) := by
  induction l with
  | nil => simp [insertionSort, Sorted]
  | cons x xs ih => exact orderedInsert_sorted x (insertionSort xs) ih

-- ==================================================================
-- PIEZA 3: insertionSort_nodup
-- ==================================================================

-- Elementos de (orderedInsert x l) son un subconjunto de {x} ∪ l
private theorem mem_of_mem_orderedInsert (x z : CList) (l : List CList) :
    z ∈ orderedInsert x l → z = x ∨ z ∈ l := by
  induction l with
  | nil =>
    simp [orderedInsert]
  | cons y ys ih =>
    simp only [orderedInsert]
    by_cases hlt : lt x y = true
    · rw [if_pos hlt]
      intro hmem
      simp only [List.mem_cons] at hmem
      rcases hmem with rfl | rfl | h
      · exact Or.inl rfl
      · exact Or.inr (List.mem_cons.mpr (Or.inl rfl))
      · exact Or.inr (List.mem_cons.mpr (Or.inr h))
    · rw [if_neg hlt]
      by_cases heq : extEq x y = true
      · rw [if_pos heq]
        intro hmem; exact Or.inr hmem
      · rw [if_neg heq]
        intro hmem
        simp only [List.mem_cons] at hmem
        rcases hmem with rfl | h
        · exact Or.inr (List.mem_cons.mpr (Or.inl rfl))
        · rcases ih h with rfl | h'
          · exact Or.inl rfl
          · exact Or.inr (List.mem_cons.mpr (Or.inr h'))

-- Elementos de (insertionSort l) son elementos de l
private theorem insertionSort_mem_subset (z : CList) (l : List CList) :
    z ∈ insertionSort l → z ∈ l := by
  induction l with
  | nil => simp [insertionSort]
  | cons y ys ih =>
    simp only [insertionSort]
    intro hmem
    rcases mem_of_mem_orderedInsert y z (insertionSort ys) hmem with rfl | h
    · exact List.mem_cons.mpr (Or.inl rfl)
    · exact List.mem_cons.mpr (Or.inr (ih h))

private theorem orderedInsert_nodup (x : CList) (l : List CList)
    (hxl : ∀ y ∈ l, extEq x y = false)
    (hl : Nodup l) : Nodup (orderedInsert x l) := by
  induction l with
  | nil => simp [orderedInsert, Nodup]
  | cons y ys ih =>
    have hxy : extEq x y = false := hxl y (List.mem_cons.mpr (Or.inl rfl))
    have hxys : ∀ w ∈ ys, extEq x w = false :=
      fun w hw => hxl w (List.mem_cons.mpr (Or.inr hw))
    simp only [Nodup, List.pairwise_cons] at hl
    obtain ⟨hyl, hys⟩ := hl
    simp only [orderedInsert]
    by_cases hlt : lt x y = true
    · rw [if_pos hlt]
      simp only [Nodup, List.pairwise_cons]
      refine ⟨fun b hb => ?_, hyl, hys⟩
      simp only [List.mem_cons] at hb
      rcases hb with rfl | hb
      · exact hxy
      · exact hxys b hb
    · rw [if_neg hlt]
      by_cases heq : extEq x y = true
      · exact absurd heq (by simp [hxy])
      · rw [if_neg heq]
        simp only [Nodup, List.pairwise_cons]
        refine ⟨fun z hz => ?_, ih hxys hys⟩
        rcases mem_of_mem_orderedInsert x z ys hz with rfl | h
        · rw [extEq_comm]; exact hxy
        · exact hyl z h

theorem insertionSort_nodup (l : List CList) (hl : Nodup l) :
    Nodup (insertionSort l) := by
  induction l with
  | nil => simp [insertionSort, Nodup]
  | cons x xs ih =>
    simp only [Nodup, List.pairwise_cons] at hl
    obtain ⟨hx, hxs⟩ := hl
    simp only [insertionSort]
    apply orderedInsert_nodup
    · intro y hy
      exact hx y (insertionSort_mem_subset y xs hy)
    · exact ih hxs

end CList


-- El Setoid finalmente con reflexividad, simetría y transitividad
def CList.Setoid : Setoid CList where
  r A B := CList.extEq A B = true
  iseqv := {
    refl := extEq_refl
    symm := fun {A B} h => by
      rw [CList.extEq_def] at h ⊢
      rwa [Bool.and_comm]
    trans := fun {A B C} h1 h2 => CList.extEq_trans A B C h1 h2
  }

def CSet := Quotient CList.Setoid

namespace CSet

open CList

/-!
Dadas dos CList A y B que son extensionalmente iguales ()
-/

theorem normalize_eq_of_extEq {A B : CList} (h : CList.extEq A B = true) :
    CList.normalize A = CList.normalize B := by
  sorry

/--
Esta es la función que extrae el representante canónico (una `CList` normalizada)
de un `CSet` abstracto.
-/
def repr (s : CSet) : CList :=
  Quotient.lift CList.normalize (fun A B h => normalize_eq_of_extEq h) s

def clist_sucia_1 := CList.mk [CList.one, CList.zero, CList.one]
def clist_sucia_2 := CList.mk [CList.zero, CList.one]

def mi_cset : CSet := Quotient.mk CList.Setoid clist_sucia_1
def mi_repr_canonico : CList := repr mi_cset

def empty : CSet := Quotient.mk CList.Setoid CList.empty

end CSet
