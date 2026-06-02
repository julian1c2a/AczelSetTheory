import AczelSetTheory.Topology.Basic
import AczelSetTheory.Axioms.Separation
import AczelSetTheory.Axioms.Intersection
import AczelSetTheory.Axioms.Setminus

namespace HFTopology

/-!
# Interior, adherencia, frontera y clasificación de puntos

Dado un espacio topológico `(X, τ)` y un subconjunto `A ⊆ X`:

- **Interior** `int(A)`: la unión de la familia de abiertos contenidos en `A`.
- **Clausura** (adherencia) `cl(A)`: el complemento del interior del complemento: `X \ int(X \ A)`.
- **Exterior** `ext(A)`: el interior del complemento: `int(X \ A)`.
- **Frontera** `∂A`: `cl(A) \ int(A)`.

Un punto `x ∈ X` se clasifica respecto a `A` según su relación con éstos:
- **Punto interior**: `x ∈ int(A)`.
- **Punto exterior**: `x ∈ ext(A)`.
- **Punto frontera**: `x ∉ int(A)` y `x ∉ ext(A)`.
- **Punto de acumulación**: cada entorno de `x` contiene un punto de `A` distinto de `x`.
- **Punto de adherencia**: cada entorno de `x` intersecta `A`.
- **Punto aislado**: `x ∈ A` y existe un entorno de `x` que no contiene otros puntos de `A`.
-/

variable {ts : HFTopSpace}

/-! ## Interior -/

/-- Interior de `A`: mayor abierto contenido en `A`. -/
def HFTopSpace.interior (ts : HFTopSpace) (A : HFSet) : HFSet :=
  HFSet.sUnion (HFSet.sep ts.τ (fun U => U ⊆ A))

theorem HFTopSpace.mem_interior (ts : HFTopSpace) (A x : HFSet) :
    x ∈ ts.interior A ↔ ∃ U, U ∈ ts.τ ∧ U ⊆ A ∧ x ∈ U := by
  unfold interior
  rw [HFSet.mem_sUnion]
  constructor
  · rintro ⟨U, hU, hxU⟩
    rw [HFSet.mem_sep] at hU
    exact ⟨U, hU.1, hU.2, hxU⟩
  · rintro ⟨U, hUτ, hUA, hxU⟩
    refine ⟨U, ?_, hxU⟩
    rw [HFSet.mem_sep]
    exact ⟨hUτ, hUA⟩

/-- El interior está contenido en `A`. -/
theorem HFTopSpace.interior_subset (ts : HFTopSpace) (A : HFSet) : ts.interior A ⊆ A := by
  intro x hx
  rw [ts.mem_interior] at hx
  obtain ⟨U, _, hUA, hxU⟩ := hx
  exact hUA x hxU

/-- El interior es un abierto. -/
theorem HFTopSpace.interior_open (ts : HFTopSpace) (A : HFSet) : ts.interior A ∈ ts.τ := by
  unfold interior
  apply ts.sUnion_mem
  rw [HFSet.subset_iff]
  intro U hU
  rw [HFSet.mem_sep] at hU
  exact hU.1

/-- El interior es el mayor abierto contenido en `A`. -/
theorem HFTopSpace.interior_largest (ts : HFTopSpace) (A : HFSet)
    {U : HFSet} (hUτ : U ∈ ts.τ) (hUA : U ⊆ A) : U ⊆ ts.interior A := by
  intro x hxU
  rw [ts.mem_interior]
  exact ⟨U, hUτ, hUA, hxU⟩

/-- Un abierto contenido en `A` coincide con su interior si y solo si es el interior. -/
theorem HFTopSpace.interior_eq_of_open (ts : HFTopSpace) {A : HFSet} (hA : A ∈ ts.τ) :
    ts.interior A = A := by
  apply HFSet.subset_antisymm
  · exact ts.interior_subset A
  · exact ts.interior_largest A hA (HFSet.subset_refl A)

/-! ## Clausura -/

/-- Clausura (adherencia) de `A`: menor cerrado que contiene a `A`. -/
def HFTopSpace.closure (ts : HFTopSpace) (A : HFSet) : HFSet :=
  HFSet.setminus ts.X (ts.interior (HFSet.setminus ts.X A))

/-- La clausura es un cerrado, i.e., su complemento es abierto. -/
theorem HFTopSpace.closure_closed (ts : HFTopSpace) (A : HFSet) :
    HFSet.setminus ts.X (ts.closure A) ∈ ts.τ := by
  -- X \ cl(A) = X \ (X \ int(X\A)) = int(X\A), que es abierto
  have hsub : ts.interior (HFSet.setminus ts.X A) ⊆ ts.X :=
    fun x hx => (HFSet.mem_setminus ts.X A x).mp (ts.interior_subset _ x hx) |>.1
  unfold closure
  rw [HFSet.setminus_setminus_of_subset hsub]
  exact ts.interior_open _

/-- `A` está contenido en su clausura. -/
theorem HFTopSpace.subset_closure (ts : HFTopSpace) {A : HFSet} (hA : A ⊆ ts.X) :
    A ⊆ ts.closure A := by
  intro x hxA
  unfold closure
  rw [HFSet.mem_setminus]
  constructor
  · exact hA x hxA
  · intro hxi
    rw [ts.mem_interior] at hxi
    obtain ⟨_, _, hUsub, hxU⟩ := hxi
    have hmem := hUsub x hxU
    rw [HFSet.mem_setminus] at hmem
    exact hmem.2 hxA

/-- Si `A` es cerrado entonces `cl(A) = A`. -/
theorem HFTopSpace.closure_eq_of_closed (ts : HFTopSpace) {A : HFSet}
    (hcl : ts.isClosed A) (hA : A ⊆ ts.X) :
    ts.closure A = A := by
  -- interior(X\A) = X\A (por isClosed); luego X\(X\A) = A (por hA)
  unfold closure
  rw [ts.interior_eq_of_open hcl]
  exact HFSet.setminus_setminus_of_subset hA

/-! ## Exterior -/

/-- Exterior de `A`: interior del complemento. -/
def HFTopSpace.exterior (ts : HFTopSpace) (A : HFSet) : HFSet :=
  ts.interior (HFSet.setminus ts.X A)

/-- El exterior es abierto. -/
theorem HFTopSpace.exterior_open (ts : HFTopSpace) (A : HFSet) : ts.exterior A ∈ ts.τ :=
  ts.interior_open _

/-! ## Frontera -/

/-- Frontera de `A`: clausura menos interior. -/
def HFTopSpace.boundary (ts : HFTopSpace) (A : HFSet) : HFSet :=
  HFSet.setminus (ts.closure A) (ts.interior A)

/-! ## Clasificación de puntos -/

/-- `x` es **punto interior** de `A` si existe un abierto `U` con `x ∈ U ⊆ A`. -/
def HFTopSpace.isInteriorPt (ts : HFTopSpace) (x A : HFSet) : Prop :=
  ∃ U, U ∈ ts.τ ∧ x ∈ U ∧ U ⊆ A

/-- `x` es punto interior de `A` si y solo si `x ∈ int(A)`. -/
theorem HFTopSpace.isInteriorPt_iff (ts : HFTopSpace) (x A : HFSet) :
    ts.isInteriorPt x A ↔ x ∈ ts.interior A := by
  rw [ts.mem_interior]
  exact ⟨fun ⟨U, hU, hxU, hUA⟩ => ⟨U, hU, hUA, hxU⟩,
         fun ⟨U, hU, hUA, hxU⟩ => ⟨U, hU, hxU, hUA⟩⟩

/-- `x` es **punto exterior** de `A` si es punto interior de `X \ A`. -/
def HFTopSpace.isExteriorPt (ts : HFTopSpace) (x A : HFSet) : Prop :=
  ts.isInteriorPt x (HFSet.setminus ts.X A)

/-- `x` es **punto de frontera** de `A` si no es interior ni exterior. -/
def HFTopSpace.isBoundaryPt (ts : HFTopSpace) (x A : HFSet) : Prop :=
  x ∈ ts.X ∧ ¬ts.isInteriorPt x A ∧ ¬ts.isExteriorPt x A

/-- `x` es **punto de acumulación** de `A` si cada abierto que contiene `x`
  intersecta `A` en algún punto distinto de `x`. -/
def HFTopSpace.isAccumulationPt (ts : HFTopSpace) (x A : HFSet) : Prop :=
  x ∈ ts.X ∧ ∀ U, U ∈ ts.τ → x ∈ U → ∃ y, y ∈ A ∧ y ≠ x ∧ y ∈ U

/-- `x` es **punto de adherencia** de `A` si cada abierto que contiene `x`
  intersecta `A` (posiblemente en `x` mismo). -/
def HFTopSpace.isAdherencePt (ts : HFTopSpace) (x A : HFSet) : Prop :=
  x ∈ ts.X ∧ ∀ U, U ∈ ts.τ → x ∈ U → ∃ y, y ∈ A ∧ y ∈ U

/-- `x` es **punto aislado** de `A` si `x ∈ A` y existe un abierto que contiene
  a `x` pero ningún otro punto de `A`. -/
def HFTopSpace.isIsolatedPt (ts : HFTopSpace) (x A : HFSet) : Prop :=
  x ∈ A ∧ ∃ U, U ∈ ts.τ ∧ x ∈ U ∧ ∀ {y : HFSet}, y ∈ U → y ∈ A → y = x

/-! ### Relaciones entre clasificaciones -/

/-- Los puntos de acumulación son puntos de adherencia. -/
theorem HFTopSpace.accumulation_is_adherence (ts : HFTopSpace) {x A : HFSet}
    (h : ts.isAccumulationPt x A) : ts.isAdherencePt x A :=
  ⟨h.1, fun U hUτ hxU =>
    let ⟨y, hyA, _, hyU⟩ := h.2 U hUτ hxU
    ⟨y, hyA, hyU⟩⟩

/-- Un punto aislado no es de acumulación. -/
theorem HFTopSpace.isolated_not_accumulation (ts : HFTopSpace) {x A : HFSet}
    (h : ts.isIsolatedPt x A) : ¬ts.isAccumulationPt x A := by
  intro ⟨_, hacc⟩
  obtain ⟨_, U, hUτ, hxU, hiso⟩ := h
  obtain ⟨y, hyA, hyx, hyU⟩ := hacc U hUτ hxU
  exact hyx (hiso hyU hyA)

/-- `x` es punto de adherencia de `A` si y solo si `x ∈ cl(A)`. -/
theorem HFTopSpace.isAdherencePt_iff_mem_closure (ts : HFTopSpace) {x A : HFSet}
    (_hA : A ⊆ ts.X) :
    ts.isAdherencePt x A ↔ x ∈ ts.closure A := by
  unfold isAdherencePt closure
  rw [HFSet.mem_setminus]
  constructor
  · intro ⟨hxX, hadh⟩
    refine ⟨hxX, ?_⟩
    rw [ts.mem_interior]
    intro ⟨U, hUτ, hUcomp, hxU⟩
    obtain ⟨y, hyA, hyU⟩ := hadh U hUτ hxU
    have := hUcomp y hyU
    rw [HFSet.mem_setminus] at this
    exact this.2 hyA
  · intro ⟨hxX, hni⟩
    refine ⟨hxX, ?_⟩
    intro U hUτ hxU
    -- Si U ∩ A = ∅ entonces U ⊆ X\A, luego x ∈ int(X\A); contradice hni
    apply Classical.byContradiction; intro hna
    have hUsub : U ⊆ HFSet.setminus ts.X A := by
      intro y hyU
      rw [HFSet.mem_setminus]
      exact ⟨ts.τ_sub hUτ y hyU, fun hyA => hna ⟨y, hyA, hyU⟩⟩
    exact hni (ts.interior_largest (HFSet.setminus ts.X A) hUτ hUsub x hxU)

/-! ### Partición: interior ∪ exterior ∪ frontera = X -/

/-- Cada punto de `X` es interior, exterior, o frontera de `A`. -/
theorem HFTopSpace.interior_exterior_boundary_partition (ts : HFTopSpace) {A : HFSet}
    (_hA : A ⊆ ts.X) :
    ∀ x, x ∈ ts.X →
      ts.isInteriorPt x A ∨ ts.isExteriorPt x A ∨ ts.isBoundaryPt x A := by
  intro x hxX
  by_cases hi : ts.isInteriorPt x A
  · exact Or.inl hi
  · by_cases he : ts.isExteriorPt x A
    · exact Or.inr (Or.inl he)
    · exact Or.inr (Or.inr ⟨hxX, hi, he⟩)

end HFTopology
