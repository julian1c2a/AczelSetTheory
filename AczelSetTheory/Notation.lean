import AczelSetTheory.HFSets
import AczelSetTheory.Operations.Pair

namespace HFSet

-- ==================================================================
-- Notación Fundamental: Conjunto Vacío y Pares
-- ==================================================================

/-- El conjunto vacío se denota con ∅ -/
notation "∅" => empty

/-- Construye el par estricto -/
macro "{[" a:term "," b:term "]}" : term => `(pair $a $b)

/-- Singleton {[x]} se define como el par {[x, x]} -/
def singleton (a : HFSet) : HFSet := pair a a

/-- Notación para el singleton -/
macro "{[" x:term "]}" : term => `(singleton $x)

-- ==================================================================
-- Unión y Adjunción (Insertar)
-- ==================================================================

-- Insertar es simplemente añadir al frente
def insertCList (x A : CList) : CList :=
  match A with
  | CList.mk ys => CList.mk (x :: ys)

theorem mem_insertCList_right (x₁ x₂ A₂ : CList) (hx : CList.extEq x₁ x₂ = true) :
    CList.mem x₁ (insertCList x₂ A₂) = true := by
  cases A₂ with | mk ys₂ =>
  simp only [insertCList, CList.mem_cons, hx, Bool.true_or]

theorem subset_insertCList_right (A₁ x₂ A₂ : CList) (hA : CList.subset A₁ A₂ = true) :
    CList.subset A₁ (insertCList x₂ A₂) = true := by
  cases A₂ with | mk ys₂ =>
  cases A₁ with | mk ys₁ =>
  exact CList.subset_mono ys₁ x₂ ys₂ hA

theorem insertCList_subset (x₁ A₁ x₂ A₂ : CList)
    (hx : CList.extEq x₁ x₂ = true) (hA : CList.subset A₁ A₂ = true) :
    CList.subset (insertCList x₁ A₁) (insertCList x₂ A₂) = true := by
  cases A₁ with | mk ys₁ =>
  cases A₂ with | mk ys₂ =>
  simp only [insertCList, CList.subset_cons, Bool.and_eq_true]
  exact ⟨mem_insertCList_right x₁ x₂ (CList.mk ys₂) hx, subset_insertCList_right (CList.mk ys₁) x₂ (CList.mk ys₂) hA⟩

theorem insertCList_extEq (x₁ A₁ x₂ A₂ : CList)
    (hx : CList.extEq x₁ x₂ = true) (hA : CList.extEq A₁ A₂ = true) :
    CList.extEq (insertCList x₁ A₁) (insertCList x₂ A₂) = true := by
  simp only [CList.extEq_def, Bool.and_eq_true] at hA ⊢
  exact ⟨insertCList_subset x₁ A₁ x₂ A₂ hx hA.1, insertCList_subset x₂ A₂ x₁ A₁ (CList.extEq_comm x₁ x₂ ▸ hx) hA.2⟩

/-- Inserta un elemento en un conjunto (x ∪ A) -/
def insert (x A : HFSet) : HFSet :=
  Quotient.liftOn₂ x A
    (fun a m => Quotient.mk CList.Setoid (insertCList a m))
    (fun x₁ A₁ x₂ A₂ hx hA => by
      apply Quotient.sound
      exact insertCList_extEq x₁ A₁ x₂ A₂ hx hA)

-- Extensión recursiva de conjuntos finitos con la nueva notación {[ ... ]}
syntax "{[" term "," term "," term,* "]}" : term
macro_rules
  | `({[$a, $b, $c]}) => `(insert $a {[$b, $c]})
  | `({[$a, $b, $c, $rest,*]}) => `(insert $a {[$b, $c, $rest,*]})

-- ==================================================================
-- Comprensión de Conjuntos: {[ x ∈ A | P(x) ]}
-- ==================================================================

/-- Filtra una lista nativa evaluando la proposición P bajada a Booleano en cada elemento -/
def filterCList (P : HFSet → Prop) [DecidablePred P] (A : CList) : CList :=
  match A with
  | CList.mk xs => CList.mk (xs.filter (fun c => decide (P (Quotient.mk CList.Setoid c))))

theorem filterCList_extEq_extEq (P : HFSet → Prop) [DecidablePred P] (A₁ A₂ : CList) (hA : CList.extEq A₁ A₂ = true) :
    CList.extEq (filterCList P A₁) (filterCList P A₂) = true := by
  cases A₁ with | mk xs₁ =>
  cases A₂ with | mk xs₂ =>
  have hP_resp : CList.P_respects (fun c => decide (P (Quotient.mk CList.Setoid c))) := by
    intro x y heq
    have hQuot : Quotient.mk CList.Setoid x = Quotient.mk CList.Setoid y := Quotient.sound heq
    simp only [hQuot]
  exact CList.extEq_filter (fun c => decide (P (Quotient.mk CList.Setoid c))) hP_resp xs₁ xs₂ hA

/-- Axioma de Separación (Subconjuntos) -/
def sep (A : HFSet) (P : HFSet → Prop) [DecidablePred P] : HFSet :=
  Quotient.liftOn A
    (fun a => Quotient.mk CList.Setoid (filterCList P a))
    (fun A₁ A₂ hA => by
      apply Quotient.sound
      exact filterCList_extEq_extEq P A₁ A₂ hA)

/-- Sintaxis de comprensión segura: {[ x ∈ A <|> P(x) ]} -/
syntax "{[" ident "∈" term "<|>" term "]}" : term
macro_rules
  | `({[$x:ident ∈ $A <|> $P]}) => `(sep $A (fun $x => $P))

-- ==================================================================
-- Numerales de von Neumann (0 a 9)
-- ==================================================================
def zero  : HFSet := ∅
def one   : HFSet := insert zero zero
def two   : HFSet := insert one one
def three : HFSet := insert two two
def four  : HFSet := insert three three
def five  : HFSet := insert four four
def six   : HFSet := insert five five
def seven : HFSet := insert six six
def eight : HFSet := insert seven seven
def nine  : HFSet := insert eight eight

instance : OfNat HFSet 0 where ofNat := zero
instance : OfNat HFSet 1 where ofNat := one
instance : OfNat HFSet 2 where ofNat := two
instance : OfNat HFSet 3 where ofNat := three
instance : OfNat HFSet 4 where ofNat := four
instance : OfNat HFSet 5 where ofNat := five
instance : OfNat HFSet 6 where ofNat := six
instance : OfNat HFSet 7 where ofNat := seven
instance : OfNat HFSet 8 where ofNat := eight
instance : OfNat HFSet 9 where ofNat := nine

end HFSet
