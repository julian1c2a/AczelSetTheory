# REFERENCE — Prelim

> **Proyecto**: Peano  
> **Rama**: `migracion_de_REFERENCE`  
> **Fecha**: 2026-05-10  
> **Nodo**: `doc/REFERENCE-Prelim.md`  
> **Volver al índice**: [REFERENCE.md](../REFERENCE.md)

---

## Módulos cubiertos

| Archivo | Namespace | Descripción |
|---|---|---|
| `Peano/Prelim/ExistsUnique.lean` | `Peano` | Existencia única constructiva |
| `Peano/Prelim/Classical.lean` | `Peano` | Elección clásica no constructiva |
| `Peano/Prelim.lean` | `Peano` | Fachada re-exportadora |

**Axioma**: `@axiom_system: Peano`  
**Dependencias externas**: `Init.Classical` (solo `Classical.lean`)

---

## §1. `ExistsUnique`

- **Tipo**: `def`
- **Módulo**: `Peano/Prelim/ExistsUnique.lean`
- **Namespace**: `Peano`
- **Importancia**: `@importance: high`
- **Computable**: — (proposición)
- **Firma Lean 4**:

  ```lean
  def ExistsUnique {α : Type} (p : α → Prop) : Prop :=
    ∃ x, (p x ∧ (∀ y, (p y → y = x)))
  ```

- **Notación matemática**: El predicado $\exists! x,\, p(x)$ — existe exactamente un $x$ que satisface $p$.
- **Notación Lean**: `∃¹ x, p x` (también `∃¹ (x : T), p x`)
- **Dependencias directas**: ninguna (constructiva pura)

---

## §2. `ExistsUnique.exists`

- **Tipo**: `def`
- **Módulo**: `Peano/Prelim/ExistsUnique.lean`
- **Namespace**: `Peano`
- **Importancia**: `@importance: medium`
- **Computable**: — (proposición)
- **Firma Lean 4**:

  ```lean
  def ExistsUnique.exists {α : Type} {p : α → Prop} (h : ExistsUnique p) : (∃ x, p x)
  ```

- **Notación matemática**: Si $\exists! x,\, p(x)$ entonces $\exists x,\, p(x)$.
- **Dependencias directas**: `ExistsUnique`

---

## §3. Notación `∃¹`

- **Tipo**: `syntax` + `macro_rules` (4 reglas)
- **Módulo**: `Peano/Prelim/ExistsUnique.lean`
- **Namespace**: `Peano`
- **Importancia**: `@importance: high`
- **Descripción**: Azúcar sintáctico para `ExistsUnique`. Formas soportadas:

  ```lean
  ∃¹ x, p x
  ∃¹ (x), p x
  ∃¹ (x : T), p x
  ∃¹ x : T, p x
  ```

  Todas se expanden a `ExistsUnique (fun x => p x)`.

---

## §4. `choose`

- **Tipo**: `noncomputable def`
- **Módulo**: `Peano/Prelim/Classical.lean`
- **Namespace**: `Peano`
- **Importancia**: `@importance: high`
- **Computable**: ❌ `noncomputable`
- **Firma Lean 4**:

  ```lean
  noncomputable def choose {α : Type} {p : α → Prop} (h : ∃ x, p x) : α
  ```

- **Notación matemática**: Operador de elección de Hilbert $\varepsilon x,\, p(x)$ — dado $\exists x,\, p(x)$, produce un testigo canónico.
- **Dependencias directas**: `Classical.indefiniteDescription` (de `Init.Classical`)

---

## §5. `choose_spec`

- **Tipo**: `theorem`
- **Módulo**: `Peano/Prelim/Classical.lean`
- **Namespace**: `Peano`
- **Importancia**: `@importance: high`
- **Computable**: — (proposición)
- **Firma Lean 4**:

  ```lean
  theorem choose_spec {α : Type} {p : α → Prop} (h : ∃ x, p x) : p (choose h)
  ```

- **Notación matemática**: El testigo elegido satisface la propiedad: $p(\varepsilon x,\, p(x))$.
- **Dependencias directas**: `choose`, `Classical.indefiniteDescription`

---

## §6. `choose_unique`

- **Tipo**: `noncomputable def`
- **Módulo**: `Peano/Prelim/Classical.lean`
- **Namespace**: `Peano`
- **Importancia**: `@importance: medium`
- **Computable**: ❌ `noncomputable`
- **Firma Lean 4**:

  ```lean
  noncomputable def choose_unique {α : Type} {p : α → Prop} (h : ExistsUnique p) : α
  ```

- **Notación matemática**: Dado $\exists! x,\, p(x)$, produce el único testigo.
- **Dependencias directas**: `choose`, `ExistsUnique.exists`

---

## §7. `choose_spec_unique`

- **Tipo**: `theorem`
- **Módulo**: `Peano/Prelim/Classical.lean`
- **Namespace**: `Peano`
- **Importancia**: `@importance: medium`
- **Computable**: — (proposición)
- **Firma Lean 4**:

  ```lean
  theorem choose_spec_unique {α : Type} {p : α → Prop}
      (h : ExistsUnique p) : p (choose_unique h)
  ```

- **Notación matemática**: El testigo único satisface $p$.
- **Dependencias directas**: `choose_unique`, `choose_spec`

---

## §8. `choose_uniq`

- **Tipo**: `theorem`
- **Módulo**: `Peano/Prelim/Classical.lean`
- **Namespace**: `Peano`
- **Importancia**: `@importance: medium`
- **Computable**: — (proposición)
- **Firma Lean 4**:

  ```lean
  theorem choose_uniq {α : Type} {p : α → Prop}
      (h : ExistsUnique p) {y : α} (hy : p y) :
      y = choose_unique h
  ```

- **Notación matemática**: Todo $y$ que satisface $p$ coincide con el testigo elegido: unicidad efectiva.
- **Dependencias directas**: `choose_unique`, `choose_spec_unique`

---

## Resumen de exports

| Símbolo | Archivo | Tipo | Importance |
|---|---|---|---|
| `ExistsUnique` | ExistsUnique.lean | `def` | high |
| `ExistsUnique.exists` | ExistsUnique.lean | `def` | medium |
| `∃¹` (notación) | ExistsUnique.lean | `syntax` | high |
| `choose` | Classical.lean | `noncomputable def` | high |
| `choose_spec` | Classical.lean | `theorem` | high |
| `choose_unique` | Classical.lean | `noncomputable def` | medium |
| `choose_spec_unique` | Classical.lean | `theorem` | medium |
| `choose_uniq` | Classical.lean | `theorem` | medium |
