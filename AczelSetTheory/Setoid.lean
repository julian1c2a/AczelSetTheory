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

end CList


-- El Setoid finalmente con transitividad total
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

def vacio : CSet := Quotient.mk CList.Setoid CList.vacio

end CSet
