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
def vacio : CList := mk []

-- 1. LÓGICA DE COMPARACIÓN BASE (Semántica de conjuntos)

inductive CListOp
| pertenece
| esSubconjunto
| esIgual

@[simp] def opWeight : CListOp → Nat
| .pertenece => 0
| .esSubconjunto => 1
| .esIgual => 2

set_option linter.unusedSimpArgs false in
/--
Motor lógico para la igualdad extensional.
Agrupamos estas tres para que Lean pueda verificar la terminación mutua.
-/
def evalOp (op : CListOp) (A B : CList) : Bool :=
  match op, A, B with
  | .pertenece, _, mk [] => false
  | .pertenece, x, mk (y :: ys) =>
      evalOp .esIgual x y || evalOp .pertenece x (mk ys)

  | .esSubconjunto, mk [], _ => true
  | .esSubconjunto, mk (x :: xs), B =>
      evalOp .pertenece x B && evalOp .esSubconjunto (mk xs) B

  | .esIgual, A, B =>
      evalOp .esSubconjunto A B && evalOp .esSubconjunto B A
termination_by (((sizeOf A + sizeOf B) * 3) + opWeight op)
decreasing_by
  all_goals
    simp_wf
    try simp [opWeight, sizeOf]
    try simp_arith
    try omega

/-- Comprueba si un elemento pertenece a un conjunto. -/
def pertenece (x A : CList) : Bool := evalOp .pertenece x A

/-- Comprueba si A es subconjunto de B. -/
def esSubconjunto (A B : CList) : Bool := evalOp .esSubconjunto A B

/-- Comprueba la igualdad extensional (mismos elementos). -/
def esIgual (A B : CList) : Bool := evalOp .esIgual A B

-- Alias visibles solicitados
/-- Boolean In: Alias de pertenece -/
def BIn (x A : CList) : Bool := pertenece x A

/-- Boolean Subset: Alias de esSubconjunto -/
def BSbs (A B : CList) : Bool := esSubconjunto A B

instance : BEq CList where beq := esIgual

-- 2. ORDEN TOTAL (Para la canonización)

/-!
Define un orden total independiente de la igualdad para poder
ordenar las listas de forma única.
Nota: Usamos el tamaño estructural directo para garantizar la terminación.
-/
def esMenor (A B : CList) : Bool :=
  if cSize A < cSize B then true
  else if cSize A > cSize B then false
  else match A, B with
    | mk [], mk [] => false
    | mk [], mk (_::_) => true
    | mk (_::_), mk [] => false
    | mk (x::xs), mk (y::ys) =>
        if esIgual x y then
          esMenor (mk xs) (mk ys)
        else
          esMenor x y
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
def reducirDuplicadosAux (l : List CList) (vistos : List CList) : List CList :=
  match l with
  | [] => []
  | x :: xs =>
      if vistos.any (fun y => esIgual x y) then
        -- Si ya lo vimos antes, lo ignoramos y seguimos
        reducirDuplicadosAux xs vistos
      else
        -- Si es nuevo, lo guardamos y lo añadimos a los 'vistos'
        x :: reducirDuplicadosAux xs (x :: vistos)

/--
Reduce los duplicados de una lista recorriéndola hacia adelante
y conservando solo la primera aparición de cada elemento.
-/
def reducirDuplicados (l : List CList) : List CList :=
  reducirDuplicadosAux l []

-- 4. CANONIZACIÓN (Forma normal)

def insertarOrdenado (x : CList) : List CList → List CList
  | [] => [x]
  | y :: ys =>
      if esMenor x y then x :: y :: ys
      else if esIgual x y then y :: ys
      else y :: insertarOrdenado x ys

def ordenarLista : List CList → List CList
  | [] => []
  | x :: xs => insertarOrdenado x (ordenarLista xs)

/--
Normalización canónica:
Aplica la normalización a los elementos, elimina duplicados y ordena.
-/
def normalizar : CList → CList
  | mk xs =>
      let hijosNorm := xs.map normalizar
      let sinDuplicados := reducirDuplicados hijosNorm
      mk (ordenarLista sinDuplicados)

-- PRUEBAS
def cero := vacio
def uno := mk [cero]
def dos := mk [cero, uno]
def tres := mk [cero, uno, dos]
def sucio := mk [uno, dos, cero, tres, uno, cero, cero, dos, tres, dos]

end CList

-- ==========================================
-- FASE 2: CSet (Tipo Cociente)
-- ==========================================

-- Si mk xs ⊆ mk ys, entonces mk xs ⊆ mk (y::ys)
theorem subs_mono (xs : List CList) (y : CList) (ys : List CList)
    (h : CList.evalOp .esSubconjunto (CList.mk xs) (CList.mk ys) = true) :
    CList.evalOp .esSubconjunto (CList.mk xs) (CList.mk (y :: ys)) = true := by
  induction xs with
  | nil => simp [CList.evalOp]
  | cons z zs ih =>
    simp only [CList.evalOp, Bool.and_eq_true] at h ⊢
    exact ⟨by simp [h.1], ih h.2⟩

-- A ⊆ A para todo CList (recursión bien fundada por cSize)
theorem subs_refl (A : CList) : CList.esSubconjunto A A = true := by
  match A with
  | CList.mk [] => simp [CList.esSubconjunto, CList.evalOp]
  | CList.mk (x :: xs) =>
    have hx  : CList.esSubconjunto x x = true             := subs_refl x
    have hxs : CList.esSubconjunto (CList.mk xs) (CList.mk xs) = true := subs_refl (CList.mk xs)
    simp only [CList.esSubconjunto] at hx hxs
    simp only [CList.esSubconjunto, CList.evalOp, Bool.and_eq_true]
    exact ⟨by simp [hx], subs_mono xs x xs hxs⟩
termination_by CList.cSize A
decreasing_by
  all_goals simp_wf
  all_goals simp [CList.cSize, CList.cSizeList]
  all_goals omega

-- esIgual A A = true (no recursivo: usa subs_refl)
theorem esIgual_refl (A : CList) : CList.esIgual A A = true := by
  simp only [CList.esIgual, CList.evalOp, Bool.and_eq_true]
  exact ⟨subs_refl A, subs_refl A⟩


-- ==============================================================
-- DEMOSTRACIÓN DE TRANSITIVIDAD (El Santo Grial Estructural)
-- ==============================================================
namespace CList

-- Lemas de apoyo genéricos
def bool_and_split {a b : Bool} (h : a && b = true) : a = true ∧ b = true := by
  cases a <;> cases b <;> simp_all

def bool_or_split {a b : Bool} (h : a || b = true) : a = true ∨ b = true := by
  cases a <;> cases b <;> simp_all

def bool_and_join {a b : Bool} (ha : a = true) (hb : b = true) : a && b = true := by
  simp [ha, hb]

def bool_or_join_left {a b : Bool} (ha : a = true) : a || b = true := by
  simp [ha]

def bool_or_join_right {a b : Bool} (hb : b = true) : a || b = true := by
  simp [hb]

-- Lemas de reducción (necesarios porque evalOp usa recursión bien fundada)
theorem esIgual_def (A B : CList) :
    esIgual A B = (esSubconjunto A B && esSubconjunto B A) := by
  simp only [esIgual, esSubconjunto, evalOp]

theorem esSubconjunto_nil_def (B : CList) :
    esSubconjunto (mk []) B = true := by
  simp only [esSubconjunto, evalOp]

theorem esSubconjunto_cons_def (x : CList) (xs : List CList) (B : CList) :
    esSubconjunto (mk (x :: xs)) B = (pertenece x B && esSubconjunto (mk xs) B) := by
  simp only [esSubconjunto, pertenece, evalOp]

theorem pertenece_nil_def (x : CList) :
    pertenece x (mk []) = false := by
  simp only [pertenece, evalOp]

theorem pertenece_cons_def (x y : CList) (ys : List CList) :
    pertenece x (mk (y :: ys)) = (esIgual x y || pertenece x (mk ys)) := by
  simp only [pertenece, esIgual, evalOp]

-- Transitividad mutua (tactic mode para compatibilidad con Lean 4.28)
mutual
  theorem eq_trans :
    (A B C : CList) → (esIgual A B = true) → (esIgual B C = true) → (esIgual A C = true)
    | A, B, C, h1, h2 => by
      simp only [esIgual_def, Bool.and_eq_true] at h1 h2 ⊢
      exact ⟨subs_trans A B C h1.1 h2.1, subs_trans C B A h2.2 h1.2⟩
  termination_by A B C _ _ => (cSize A + cSize B + cSize C) * 2 + 1
  decreasing_by
    all_goals simp_wf
    all_goals try simp [cSize, cSizeList]
    all_goals try omega

  theorem subs_trans : (A B C : CList) → esSubconjunto A B = true → esSubconjunto B C = true → esSubconjunto A C = true
    | mk [], _, _, _, _ => esSubconjunto_nil_def _
    | mk (x :: xs), B, C, h1, h2 => by
      simp only [esSubconjunto_cons_def, Bool.and_eq_true] at h1 ⊢
      exact ⟨mem_subs x B C h1.1 h2, subs_trans (mk xs) B C h1.2 h2⟩
  termination_by A B C _ _ => (cSize A + cSize B + cSize C) * 2
  decreasing_by
    all_goals simp_wf
    all_goals try simp [cSize, cSizeList]
    all_goals try omega

  theorem mem_subs : (x B C : CList) → pertenece x B = true → esSubconjunto B C = true → pertenece x C = true
    | _, mk [], _, h1, _ => by simp [pertenece_nil_def] at h1
    | x, mk (y :: ys), C, h1, h2 => by
      simp only [pertenece_cons_def, Bool.or_eq_true] at h1
      simp only [esSubconjunto_cons_def, Bool.and_eq_true] at h2
      cases h1 with
      | inl h1_eq => exact eq_mem x y C h1_eq h2.1
      | inr h1_mem => exact mem_subs x (mk ys) C h1_mem h2.2
  termination_by x B C _ _ => (cSize x + cSize B + cSize C) * 2
  decreasing_by
    all_goals simp_wf
    all_goals try simp [cSize, cSizeList]
    all_goals try omega

  theorem eq_mem : (x y C : CList) → esIgual x y = true → pertenece y C = true → pertenece x C = true
    | _, _, mk [], _, h2 => by simp [pertenece_nil_def] at h2
    | x, y, mk (z :: zs), h1, h2 => by
      simp only [pertenece_cons_def, Bool.or_eq_true] at h2 ⊢
      cases h2 with
      | inl h2_eq => exact Or.inl (eq_trans x y z h1 h2_eq)
      | inr h2_mem => exact Or.inr (eq_mem x y (mk zs) h1 h2_mem)
  termination_by x y C _ _ => (cSize x + cSize y + cSize C) * 2
  decreasing_by
    all_goals simp_wf
    all_goals try simp [cSize, cSizeList]
    all_goals try omega
end

/--
Define la propiedad de que una lista no tiene duplicados según `esIgual`.
-/
def Nodup (l : List CList) : Prop :=
  l.Pairwise (fun a b => esIgual a b = false)

-- Lema: reducirDuplicados produce una lista sin duplicados.
theorem reducirDuplicados_nodup (l : List CList) : Nodup (reducirDuplicados l) := by
  have stronger_lemma : ∀ (l' : List CList) (vistos : List CList),
    Nodup (reducirDuplicadosAux l' vistos) ∧
    (∀ y ∈ (reducirDuplicadosAux l' vistos), (vistos.any (fun z => esIgual y z)) = false) := by
    intro l'
    induction l' with
    | nil =>
      intro _; simp [reducirDuplicadosAux, Nodup]
    | cons head tail IH =>
      intro vistos
      simp only [reducirDuplicadosAux]
      by_cases h_seen : (vistos.any fun y => esIgual head y) = true
      · rw [if_pos h_seen]; exact IH vistos
      · rw [if_neg h_seen]
        have h_false : (vistos.any fun y => esIgual head y) = false :=
          Bool.eq_false_iff.mpr (fun h => h_seen h)
        have ih_recursed := IH (head :: vistos)
        rcases ih_recursed with ⟨nodup_tail, tail_is_new⟩
        constructor
        · simp only [Nodup, List.pairwise_cons]
          constructor
          · have esIgual_comm : ∀ a b, esIgual a b = esIgual b a := by
              intros a b; simp [esIgual, evalOp, Bool.and_comm]
            intro y y_in_tail
            specialize tail_is_new y y_in_tail
            rw [List.any_cons, Bool.or_eq_false_iff] at tail_is_new
            rw [esIgual_comm]; exact tail_is_new.1
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
  rw [reducirDuplicados]
  exact (stronger_lemma l []).1

/--
Define la equivalencia de conjuntos entre dos listas.
-/
def SetEquiv (l₁ l₂ : List CList) : Prop :=
  ∀ x, (l₁.any (fun y => esIgual x y)) ↔ (l₂.any (fun y => esIgual x y))

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

theorem pertenece_eq_any (x : CList) (l : List CList) :
    pertenece x (mk l) = l.any (fun y => esIgual x y) := by
  induction l with
  | nil => simp [pertenece_nil_def]
  | cons y ys ih => simp [pertenece_cons_def, ih]

private theorem subs_iff_forall_mem_pertenece (l₁ l₂ : List CList) :
    esSubconjunto (mk l₁) (mk l₂) = true ↔ (∀ x ∈ l₁, pertenece x (mk l₂) = true) := by
  induction l₁ with
  | nil => simp [esSubconjunto_nil_def]
  | cons x xs ih =>
    simp only [esSubconjunto_cons_def, Bool.and_eq_true]
    constructor
    · intro ⟨h1, h2⟩ y hy
      simp only [List.mem_cons] at hy
      rcases hy with rfl | hy
      · exact h1
      · exact ih.mp h2 y hy
    · intro h
      exact ⟨h x List.mem_cons_self, ih.mpr (fun y hy => h y (List.mem_cons_of_mem _ hy))⟩

theorem esIgual_mk_iff_setEquiv (l₁ l₂ : List CList) :
    esIgual (mk l₁) (mk l₂) = true ↔ SetEquiv l₁ l₂ := by
  constructor
  · intro h
    unfold SetEquiv
    rw [esIgual_def, Bool.and_eq_true] at h
    simp only [subs_iff_forall_mem_pertenece, pertenece_eq_any] at h
    obtain ⟨h1, h2⟩ := h
    intro x
    constructor
    · intro hx
      rw [List.any_eq_true] at hx
      obtain ⟨z, hz, hxz⟩ := hx
      have hzl2 := h1 z hz
      rw [List.any_eq_true] at hzl2
      obtain ⟨w, hw, hzw⟩ := hzl2
      exact List.any_eq_true.mpr ⟨w, hw, eq_trans x z w hxz hzw⟩
    · intro hx
      rw [List.any_eq_true] at hx
      obtain ⟨z, hz, hxz⟩ := hx
      have hzl1 := h2 z hz
      rw [List.any_eq_true] at hzl1
      obtain ⟨w, hw, hzw⟩ := hzl1
      exact List.any_eq_true.mpr ⟨w, hw, eq_trans x z w hxz hzw⟩
  · intro h
    unfold SetEquiv at h
    rw [esIgual_def, Bool.and_eq_true]
    simp only [subs_iff_forall_mem_pertenece, pertenece_eq_any]
    exact ⟨fun x hx => (h x).mp  (List.any_eq_true.mpr ⟨x, hx, esIgual_refl x⟩),
           fun x hx => (h x).mpr (List.any_eq_true.mpr ⟨x, hx, esIgual_refl x⟩)⟩

-- Lema: `reducirDuplicados` conserva el conjunto de elementos.
theorem reducirDuplicados_set_equiv_self (l : List CList) : SetEquiv (reducirDuplicados l) l := by
  intro x; constructor
  · intro h_mem_reduced
    rw [List.any_eq_true] at h_mem_reduced
    obtain ⟨z, z_in_reduced, xz_eq⟩ := h_mem_reduced
    have z_in_l_ext : (l.any (fun y => esIgual z y)) = true := by
      have helper : ∀ (l' vistos : List CList), ∀ z' ∈ (reducirDuplicadosAux l' vistos),
          (l'.any (fun y => esIgual z' y)) = true ∨ (vistos.any (fun y => esIgual z' y)) = true := by
        intro l'
        induction l' with
        | nil => intro vistos z' h_mem; cases h_mem
        | cons head tail IH =>
          intro vistos z' h_mem
          unfold reducirDuplicadosAux at h_mem
          by_cases h_seen : (vistos.any (fun y => esIgual head y)) = true
          · rw [if_pos h_seen] at h_mem
            rcases IH vistos z' h_mem with (h | h)
            · exact Or.inl (by simp [List.any_cons, h])
            · exact Or.inr h
          · rw [if_neg h_seen] at h_mem
            simp only [List.mem_cons] at h_mem
            rcases h_mem with (rfl | h_in_tail)
            · exact Or.inl (by simp [List.any_cons, esIgual_refl])
            · rcases IH (head :: vistos) z' h_in_tail with (h_in_t | h_in_v)
              · exact Or.inl (by simp [List.any_cons, h_in_t])
              · rw [List.any_cons, Bool.or_eq_true] at h_in_v
                rcases h_in_v with (h_head | h_vis)
                · exact Or.inl (by simp [List.any_cons, h_head])
                · exact Or.inr h_vis
      rw [reducirDuplicados] at z_in_reduced
      rcases helper l [] z z_in_reduced with (h | h)
      · exact h
      · simp at h
    rw [List.any_eq_true] at z_in_l_ext
    obtain ⟨w, w_in_l, zw_eq⟩ := z_in_l_ext
    exact List.any_eq_true.mpr ⟨w, w_in_l, CList.eq_trans x z w xz_eq zw_eq⟩
  · intro h_mem_l
    rw [List.any_eq_true] at h_mem_l
    obtain ⟨z, z_in_l, xz_eq⟩ := h_mem_l
    have completeness_aux : ∀ z' ∈ l, (reducirDuplicados l).any (fun y => esIgual z' y) = true := by
      have helper : ∀ (l' vistos : List CList), ∀ z' ∈ l',
          (reducirDuplicadosAux l' vistos).any (fun y => esIgual z' y) = true ∨
          (vistos.any (fun y => esIgual z' y)) = true := by
        intro l'
        induction l' with
        | nil => intro vistos z' h_mem; cases h_mem
        | cons hd tail IH =>
          intro vistos z' h_mem
          simp only [reducirDuplicadosAux]
          rcases List.mem_cons.mp h_mem with (rfl | h_in_tail)
          · by_cases h_seen : (vistos.any (fun y => esIgual z' y)) = true
            · rw [if_pos h_seen]; exact Or.inr h_seen
            · rw [if_neg h_seen]
              exact Or.inl (List.any_eq_true.mpr ⟨z', List.mem_cons_self, esIgual_refl _⟩)
          · by_cases h_seen : (vistos.any (fun y => esIgual hd y)) = true
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
      rw [reducirDuplicados]
      rcases helper l [] z' hz' with (h | h)
      · exact h
      · simp at h
    have hz := completeness_aux z z_in_l
    rw [List.any_eq_true] at hz
    obtain ⟨w, w_in_reduced, zw_eq⟩ := hz
    exact List.any_eq_true.mpr ⟨w, w_in_reduced, CList.eq_trans x z w xz_eq zw_eq⟩


-- ==================================================================
-- TEOREMA 1: normalizar no aumenta el tamaño (normalizar_cSize_le)
-- ==================================================================

private theorem cSizeList_insertarOrdenado_le (x : CList) (l : List CList) :
    cSizeList (insertarOrdenado x l) ≤ 1 + cSize x + cSizeList l := by
  induction l with
  | nil => simp [insertarOrdenado, cSizeList]
  | cons y ys ih =>
    unfold insertarOrdenado
    by_cases h1 : esMenor x y = true
    · rw [if_pos h1]; simp only [cSizeList]; omega
    · rw [if_neg h1]
      by_cases h2 : esIgual x y = true
      · rw [if_pos h2]; simp only [cSizeList]; omega
      · rw [if_neg h2]; simp only [cSizeList]; omega

theorem cSizeList_reducirDuplicados_le (l : List CList) :
    cSizeList (reducirDuplicados l) ≤ cSizeList l := by
  suffices h : ∀ (l' vistos : List CList),
      cSizeList (reducirDuplicadosAux l' vistos) ≤ cSizeList l' from by
    unfold reducirDuplicados; exact h l []
  intro l'
  induction l' with
  | nil => intros; simp [reducirDuplicadosAux, cSizeList]
  | cons x xs ih =>
    intro vistos
    unfold reducirDuplicadosAux
    by_cases h : (vistos.any fun y => esIgual x y) = true
    · rw [if_pos h]; exact Nat.le_trans (ih vistos) (by simp [cSizeList])
    · rw [if_neg h]; simp only [cSizeList]
      exact Nat.le_trans (Nat.add_le_add_left (ih (x :: vistos)) _) (by omega)

theorem cSizeList_ordenarLista_le (l : List CList) :
    cSizeList (ordenarLista l) ≤ cSizeList l := by
  induction l with
  | nil => simp [ordenarLista, cSizeList]
  | cons x xs ih =>
    unfold ordenarLista
    have h1 := cSizeList_insertarOrdenado_le x (ordenarLista xs)
    simp only [cSizeList]
    omega

mutual
  private theorem normalizar_cSizeList_le : ∀ (xs : List CList),
      cSizeList (xs.map normalizar) ≤ cSizeList xs
    | [] => by simp [cSizeList]
    | (x :: rest) => by
        simp only [List.map, cSizeList]
        have hx := normalizar_cSize_le x
        have ih := normalizar_cSizeList_le rest
        omega
  termination_by xs => cSizeList xs * 2 + 1
  decreasing_by
    all_goals simp_wf
    all_goals simp [cSize, cSizeList]
    all_goals omega

  theorem normalizar_cSize_le (A : CList) : cSize (normalizar A) ≤ cSize A :=
    match A with
    | mk xs => by
        have h_map := normalizar_cSizeList_le xs
        have h_red := cSizeList_reducirDuplicados_le (xs.map normalizar)
        have h_ord := cSizeList_ordenarLista_le (reducirDuplicados (xs.map normalizar))
        simp only [normalizar, cSize]
        omega
  termination_by cSize A * 2
  decreasing_by
    all_goals simp_wf
    all_goals simp [cSize, cSizeList]
    all_goals omega
end


end CList


-- El Setoid finalmente con reflexividad, simetría y transitividad
def CList.Setoid : Setoid CList where
  r A B := CList.esIgual A B = true
  iseqv := {
    refl := esIgual_refl
    symm := fun {A B} h => by
      rw [CList.esIgual_def] at h ⊢
      rwa [Bool.and_comm]
    trans := fun {A B C} h1 h2 => CList.eq_trans A B C h1 h2
  }

def CSet := Quotient CList.Setoid

namespace CSet

open CList

/-!
Dadas dos CList A y B que son extensionalmente iguales ()
-/

theorem normalizar_eq_of_eq {A B : CList} (h : CList.esIgual A B = true) :
    CList.normalizar A = CList.normalizar B := by
  sorry

/--
Esta es la función que extrae el representante canónico (una `CList` normalizada)
de un `CSet` abstracto.
-/
def repr (s : CSet) : CList :=
  Quotient.lift CList.normalizar (fun A B h => normalizar_eq_of_eq h) s

def clist_sucia_1 := CList.mk [CList.uno, CList.cero, CList.uno]
def clist_sucia_2 := CList.mk [CList.cero, CList.uno]

def mi_cset : CSet := Quotient.mk CList.Setoid clist_sucia_1
def mi_repr_canonico : CList := repr mi_cset

def vacio : CSet := Quotient.mk CList.Setoid CList.vacio

end CSet
