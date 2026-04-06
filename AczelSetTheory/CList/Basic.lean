import Init.Data.List.Basic

-- ==========================================
-- CList: La estructura computacional (definiciones)
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

theorem cSize_lt_of_mem {x : CList} {xs : List CList} (h : x ∈ xs) :
    cSize x < cSize (mk xs) := by
  induction xs with
  | nil => simp at h
  | cons y ys ih =>
    simp only [cSize, cSizeList]
    rcases List.mem_cons.mp h with rfl | hys
    · omega
    · have := ih hys; simp [cSize] at this; omega

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
  match A, B with
  | mk [], mk [] => false
  | mk [], mk (_::_) => true
  | mk (_::_), mk [] => false
  | mk (x::xs), mk (y::ys) =>
      if lt x y then true
      else if lt y x then false
      else lt (mk xs) (mk ys)
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
