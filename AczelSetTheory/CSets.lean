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
  -- Probamos una afirmación más fuerte sobre la función auxiliar por inducción.
  -- La propiedad `P(l', vistos)` es:
  --   1. El resultado no tiene duplicados (`Nodup`).
  --   2. Todos los elementos del resultado son "nuevos" con respecto a `vistos`.
  have stronger_lemma : ∀ (l' : List CList) (vistos : List CList),
    Nodup (reducirDuplicadosAux l' vistos) ∧
    (∀ y ∈ (reducirDuplicadosAux l' vistos), (vistos.any (fun z => esIgual y z)) = false) := by
    intro l'
    induction l' with
    | nil =>
      intro _; simp [reducirDuplicadosAux, Nodup]
    | head tail IH =>
      intro vistos
      simp only [reducirDuplicadosAux]
      by_cases h_seen : (vistos.any fun y => esIgual head y)
      -- Caso 1: `head` ya se ha visto. La llamada recursiva usa el mismo `vistos`.
      · simp [h_seen]; exact IH vistos
      -- Caso 2: `head` es nuevo. Se añade a `vistos` en la llamada recursiva.
      · simp [h_seen]
        -- Aplicamos la hipótesis de inducción con la lista de `vistos` actualizada.
        have ih_recursed := IH (head :: vistos)
        rcases ih_recursed with ⟨nodup_tail, tail_is_new⟩

        -- Probamos las dos propiedades para `head :: reducirDuplicadosAux ...`
        constructor
        -- Parte 1: Demostrar `Nodup (head :: ...)`
        · simp only [Nodup, List.pairwise_cons]
          constructor
          -- 1a: `head` no es igual a ningún elemento del resto.
          · have esIgual_comm : ∀ a b, esIgual a b = esIgual b a := by
              intros a b; simp [esIgual, esSubconjunto, evalOp, Bool.and_comm]
            intro y y_in_tail
            specialize tail_is_new y y_in_tail
            rw [List.any_cons, List.any_or, Bool.or_eq_false_iff] at tail_is_new
            rw [esIgual_comm]; exact tail_is_new.1
          -- 1b: El resto de la lista no tiene duplicados.
          · exact nodup_tail
        -- Parte 2: Demostrar que todos los elementos son nuevos para `vistos`.
        · intro y y_in_list
          simp only [List.mem_cons] at y_in_list
          cases y_in_list with
          | inl h_y_eq_head =>
            rw [h_y_eq_head]; exact h_seen
          | inr h_y_in_tail =>
            specialize tail_is_new y h_y_in_tail
            rw [List.any_cons, List.any_or, Bool.or_eq_false_iff] at tail_is_new
            exact tail_is_new.2
  -- Nuestro objetivo principal es la primera parte del lema, con `vistos` inicializado a `[]`.
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

@[trans]
theorem trans {l₁ l₂ l₃ : List CList} (h₁₂ : SetEquiv l₁ l₂) (h₂₃ : SetEquiv l₂ l₃) : SetEquiv l₁ l₃ := by
  intro x; exact (h₁₂ x).trans (h₂₃ x)

end SetEquiv



theorem pertenece_eq_any (x : CList) (l : List CList) :



    pertenece x (mk l) = l.any (fun y => esIgual x y) := by



  induction l with



  | nil => simp [pertenece_nil_def]



  | cons y ys ih => simp [pertenece_cons_def, ih]







theorem esIgual_mk_iff_setEquiv (l₁ l₂ : List CList) :
    esIgual (mk l₁) (mk l₂) = true ↔ SetEquiv l₁ l₂ := by
  have subs_iff_forall_mem_pertenece (l₁ l₂ : List CList) :
      esSubconjunto (mk l₁) (mk l₂) = true ↔ (∀ x ∈ l₁, pertenece x (mk l₂) = true) := by
    induction l₁ with
    | nil => simp [esSubconjunto_nil_def]
    | cons x xs ih =>
      simp only [esSubconjunto_cons_def, Bool.and_eq_true, List.mem_cons, forall_eq_or_imp]
      rw [ih]
  -- Main proof
  simp_rw [esIgual_def, Bool.and_eq_true, subs_iff_forall_mem_pertenece]
  unfold SetEquiv
  simp_rw [pertenece_eq_any, Bool.eq_true_iff_true]







  constructor



  · intro h x



    constructor



    · intro h_pert_l1



      rcases h_pert_l1 with ⟨z, z_in_l1, xz_eq⟩



      exact eq_mem x z (mk l₂) xz_eq (h.1 z z_in_l1)



    · intro h_pert_l2



      rcases h_pert_l2 with ⟨z, z_in_l2, xz_eq⟩



      exact eq_mem x z (mk l₁) xz_eq (h.2 z z_in_l2)



  · intro h



    constructor



    · intro x x_in_l1



      apply (h x).mp



      exact ⟨x, x_in_l1, esIgual_refl x⟩



    · intro x x_in_l2



      apply (h x).mpr



      exact ⟨x, x_in_l2, esIgual_refl x⟩



-- Lema: `reducirDuplicados` conserva el conjunto de elementos.

theorem reducirDuplicados_set_equiv_self (l : List CList) : SetEquiv (reducirDuplicados l) l := by
  intro x; constructor
  -- Parte 1: Soundness (`reducirDuplicados l` es un subconjunto de `l`)
  · intro h_mem_reduced
    -- `h_mem_reduced` significa `∃ z ∈ reducirDuplicados l, esIgual x z`
    rcases h_mem_reduced with ⟨z, z_in_reduced, xz_eq⟩
    -- Probamos que todo elemento de la lista reducida está en la original.
    have z_in_l_ext : (l.any (fun y => esIgual z y)) := by
      -- Esto se demuestra por inducción sobre la lista `l` en `reducirDuplicadosAux`.
      have helper : ∀ (l' vistos : List CList), ∀ z' ∈ (reducirDuplicadosAux l' vistos),
        (l'.any (fun y => esIgual z' y)) ∨ (vistos.any (fun y => esIgual z' y)) := by
        intro l'
        induction l' with
        | nil => intro vistos z' h_mem; cases h_mem
        | head tail IH =>
          intro vistos z' h_mem
          simp [reducirDuplicadosAux] at h_mem
          by_cases h_seen : (vistos.any (fun y => esIgual head y))
          · simp [h_seen] at h_mem; exact IH vistos z' h_mem
          · simp [h_seen] at h_mem
            rcases h_mem with (rfl | h_in_tail)
            · exact Or.inl ⟨head, List.mem_cons_self _ _, esIgual_refl head⟩
            · have := IH (head :: vistos) z' h_in_tail
              rcases this with (h_in_t | h_in_v)
              · exact Or.inl ⟨h_in_t.choose, List.mem_cons_of_mem _ h_in_t.choose_spec.1, h_in_t.choose_spec.2⟩
              · simp [List.any_cons, List.any_or] at h_in_v
                exact Or.inr h_in_v
      -- Aplicamos el helper al caso base.
      rw [reducirDuplicados] at z_in_reduced
      have := helper l [] z z_in_reduced
      cases this with
      | inl h => exact h
      | inr h => simp at h
    -- Usamos transitividad para conectar `x` con el elemento encontrado en `l`.
    rcases z_in_l_ext with ⟨w, w_in_l, zw_eq⟩
    exact ⟨w, w_in_l, CList.eq_trans x z w xz_eq zw_eq⟩
  -- Parte 2: Completeness (`l` es un subconjunto de `reducirDuplicados l`)
  · intro h_mem_l
    -- `h_mem_l` nos da `z` en `l` tal que `esIgual x z`.
    rcases h_mem_l with ⟨z, z_in_l, xz_eq⟩
    -- Probamos que `∀ z' ∈ l, Mem z' (reducirDuplicados l)`.
    have completeness_aux : ∀ z' ∈ l, (reducirDuplicados l).any (fun y => esIgual z' y) := by
      -- Esto se demuestra por inducción, probando que ningún elemento se pierde.
      have helper : ∀ (l' vistos : List CList), ∀ z' ∈ l',
        (reducirDuplicadosAux l' vistos).any (fun y => esIgual z' y) ∨ (vistos.any (fun y => esIgual z' y)) := by
        intro l'
        induction l' with
        | nil => intro vistos z' h_mem; cases h_mem
        | head tail IH =>
          intro vistos z' h_mem
          simp only [reducirDuplicadosAux]
          rcases (List.mem_cons.mp h_mem) with (rfl | h_in_tail)
          -- Caso 1: z' = head
          · by_cases h_seen : (vistos.any (fun y => esIgual head y))
            · simp [h_seen]; exact Or.inr h_seen
            · simp [h_seen]; exact Or.inl ⟨head, List.mem_cons_self _ _, esIgual_refl _⟩
          -- Caso 2: z' ∈ tail
          · have := IH (head :: vistos) z' h_in_tail
            by_cases h_seen : (vistos.any (fun y => esIgual head y))
            · simp [h_seen]
              -- `vistos` no cambia, así que la IH simple sobre `tail` es suficiente.
              exact IH vistos z' h_in_tail
            · simp [h_seen]
              -- `vistos` se actualiza. La IH fuerte nos da la propiedad para `tail` y `head::vistos`.
              rcases (IH (head :: vistos) z' h_in_tail) with (h_in_res | h_in_v_ext)
              -- Si `z'` está en el resultado recursivo, está en el resultado extendido.
              · exact Or.inl ⟨h_in_res.choose, List.mem_cons_of_mem _ h_in_res.choose_spec.1, h_in_res.choose_spec.2⟩
              -- Si `z'` estaba en `head::vistos`, hay que ver dónde.
              · simp [List.any_cons, List.any_or] at h_in_v_ext
                -- Si `esIgual z' head`, entonces está en el resultado (`head :: ...`).
                -- Si no, estaba en `vistos` y se cumple la segunda parte del `or`.
                cases h_in_v_ext with
                | inl h_eq_h => exact Or.inl ⟨head, List.mem_cons_self _ _, h_eq_h⟩
                | inr h_in_v => exact Or.inr h_in_v
      -- Aplicamos el helper al caso inicial y simplificamos.
      intro z' hz'
      rw [reducirDuplicados]
      have := helper l [] z' hz'
      simp at this; exact this
    -- Usamos transitividad para finalizar.
    have := completeness_aux z z_in_l
    rcases this with ⟨w, w_in_reduced, zw_eq⟩
    exact ⟨w, w_in_reduced, CList.eq_trans x z w xz_eq zw_eq⟩


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

/-!
Dadas dos CList A y B que son extensionalmente iguales ()
-/

theorem normalizar_eq_of_eq {A B : CList} (h : CList.esIgual A B = true) :
    CList.normalizar A = CList.normalizar B := by
  -- La prueba es por recursión bien fundada sobre el tamaño de los CList.
  -- Lean es capaz de deducir la terminación porque las llamadas recursivas
  -- se hacen sobre elementos internos, que son estructuralmente más pequeños.
  cases A with | mk Ax =>
  cases B with | mk Bx =>
  -- Desplegamos la definición de `normalizar`.
  -- La meta es `mk (...) = mk (...)`, por lo que podemos usar `congr`
  -- para probar que los argumentos de `mk` son iguales.
  simp only [normalizar]
  congr

  -- Lema clave 1: Si los CList son iguales, sus listas internas son SetEquiv.
  have h_equiv_Ax_Bx : SetEquiv Ax Bx := (esIgual_mk_iff_setEquiv Ax Bx).mp h

  -- Lema clave 2: `map normalizar` preserva SetEquiv.
  -- Esto funciona porque podemos aplicar la hipótesis de inducción (`normalizar_eq_of_eq`)
  -- a los elementos de las listas, que son más pequeños.
  have h_equiv_map : SetEquiv (Ax.map normalizar) (Bx.map normalizar) := by
    intro x
    constructor
    · rintro ⟨norm_a, ⟨a, ha, rfl⟩, hx_eq_norm_a⟩
      have ⟨b, hb, hab⟩ := (h_equiv_Ax_Bx a).mp ⟨a, ha, esIgual_refl a⟩
      have h_norm_eq : normalizar a = normalizar b := normalizar_eq_of_eq hab
      rw [h_norm_eq] at hx_eq_norm_a
      exact ⟨normalizar b, ⟨b, hb, rfl⟩, hx_eq_norm_a⟩
    · rintro ⟨norm_b, ⟨b, hb, rfl⟩, hx_eq_norm_b⟩
      have ⟨a, ha, hab⟩ := (h_equiv_Ax_Bx b).mpr ⟨b, hb, esIgual_refl b⟩
      have h_norm_eq : normalizar a = normalizar b := normalizar_eq_of_eq hab
      rw [←h_norm_eq] at hx_eq_norm_b
      exact ⟨normalizar a, ⟨a, ha, rfl⟩, hx_eq_norm_b⟩

  -- Lema clave 3: Las listas reducidas son SetEquiv.
  -- Usamos transitividad: A ≈ B, B ≈ C => A ≈ C
  have h_equiv_reduced : SetEquiv (reducirDuplicados (Ax.map normalizar)) (reducirDuplicados (Bx.map normalizar)) :=
    SetEquiv.trans (SetEquiv.symm (reducirDuplicados_set_equiv_self _)) (SetEquiv.trans h_equiv_map (reducirDuplicados_set_equiv_self _))

  -- Ahora sabemos que las listas que entran a `ordenarLista` son SetEquiv.
  -- También sabemos por `reducirDuplicados_nodup` que no tienen duplicados.
  have h_nodup1 : Nodup (reducirDuplicados (Ax.map normalizar)) := reducirDuplicados_nodup _
  have h_nodup2 : Nodup (reducirDuplicados (Bx.map normalizar)) := reducirDuplicados_nodup _

  -- El paso final: si dos listas sin duplicados son SetEquiv, `ordenarLista`
  -- debe producir el mismo resultado para ambas, ya que actúa como una
  -- función de canonización.
  -- Esta es la última pieza que falta por demostrar.
  have h_canon_eq : ordenarLista (reducirDuplicados (Ax.map normalizar)) = ordenarLista (reducirDuplicados (Bx.map normalizar)) := by
    sorry


  exact h_canon_eq
termination_by cSize A + cSize B
decreasing_by
  all_goals simp_wf
  all_goals simp [cSize, cSizeList]
  all_goals omega

/--
Esta es la función que extrae el representante canónico (una `CList` normalizada)
de un `CSet` abstracto.

Usa ``Quotient.lift``, que "levanta" una función del tipo base (`CList`)
al tipo cociente (`CSet`), siempre que la función respete la relación
de equivalencia (lo que demostramos con `normalizar_eq_of_eq`).
-/
def repr (s : CSet) : CList :=
  Quotient.lift CList.normalizar (fun A B h => normalizar_eq_of_eq h) s

-- EJEMPLO DE USO:

-- 1. Creamos dos CList "sucias" y distintas, pero extensionalmente iguales.
def clist_sucia_1 := CList.mk [CList.uno, CList.cero, CList.uno]
def clist_sucia_2 := CList.mk [CList.cero, CList.uno]

-- 2. "Subimos" una de ellas para crear un CSet abstracto.
--    ``Quotient.mk` `CList.Setoid` clist_sucia_1` y ``Quotient.mk` `CList.Setoid` clist_sucia_2`
--    producirían el *mismo* `CSet`.
def mi_cset : CSet := Quotient.mk CList.Setoid clist_sucia_1

-- 3. "Bajamos" del CSet abstracto a su representante canónico usando nuestra función.
def mi_repr_canonico : CList := repr mi_cset

-- El valor de `mi_repr_canonico` sería ``CList.mk` [`CList.cero`, `CList.uno`]`,
-- que es el resultado de aplicar ``CList.normalizar`` tanto a `clist_sucia_1`
-- como a `clist_sucia_2`.

def vacio : CSet := Quotient.mk CList.Setoid CList.vacio

end CSet
