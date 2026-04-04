# Plan de demostración: `normalize_eq_of_extEq` y lemmas auxiliares

## Estado actual del archivo (2026-04-04)

Build: **✅ compila** con 1 `sorry`. Todos los errores previos resueltos.

| Teorema | Estado | Línea aprox. |
|---|---|---|
| `dedup_nodup` | ✅ Completo | L303–341 |
| `SetEquiv.refl/symm/trans` | ✅ Completo | L349–363 |
| `mem_eq_any` | ✅ Completo | L365–369 |
| `extEq_mk_iff_setEquiv` | ✅ Completo | L386–415 |
| `dedup_setEquiv_self` | ✅ Completo | L418–491 |
| `normalize_cSize_le` | ✅ Completo | L537–565 |
| `lt_irrefl` | ✅ Completo | L572–580 |
| `extEq_comm` | ✅ Completo | L582–583 |
| `lt_total` | ✅ Completo | L600–658 |
| `orderedInsert_sorted` (private) | ✅ Completo | L669–708 |
| `insertionSort_sorted` | ✅ Completo | L710–713 |
| `insertionSort_nodup` | ✅ Completo | L790–801 |
| `CList.Setoid` | ✅ Completo | L807–815 |
| `normalize_eq_of_extEq` | ⚠️ Un `sorry` | L827–829 |
| `CSet.repr` | ✅ (depende del sorry) | L835–836 |

El único bloqueo es el `sorry` en `normalize_eq_of_extEq`:

```lean
theorem normalize_eq_of_extEq {A B : CList} (h : CList.extEq A B = true) :
    CList.normalize A = CList.normalize B := by
  sorry
```

---

## Análisis del problema

### Contexto disponible dentro del `sorry`

Al llegar a ese punto dentro de `normalize_eq_of_extEq` (caso `A = mk Ax`, `B = mk Bx`), tenemos:

- `h_equiv_Ax_Bx : SetEquiv Ax Bx`
- `h_equiv_map : SetEquiv (Ax.map normalize) (Bx.map normalize)`
- `h_equiv_reduced : SetEquiv l₁ l₂`
  donde `l₁ = dedup (Ax.map normalize)`, `l₂ = dedup (Bx.map normalize)`
- `h_nodup1 : Nodup l₁`, `h_nodup2 : Nodup l₂`
- **IH de `normalize_eq_of_extEq`**: para `a ∈ Ax, b ∈ Bx` con `extEq a b = true`,
  se tiene `normalize a = normalize b`

### ¿Por qué el `sorry` es difícil?

La dificultad central es que `lt` **no está bien definido en clases de equivalencia** de `extEq`.
Ejemplo: `A = mk [∅, {∅}]` y `A' = mk [{∅}, ∅]` tienen `extEq A A' = true` pero
estructuralmente son distintos, y `lt` puede dar distinto resultado comparándolos con terceros.

**La clave**: Los elementos de `l₁` y `l₂` son **todos outputs de `normalize`**.
Si probamos que `extEq na nb = true → na = nb` (igualdad proposicional) para elementos normalizados,
entonces `l₁` y `l₂` son permutaciones propositionales la una de la otra,
y `insertionSort` daría el mismo resultado.

---

## Estrategia de demostración

### Pieza 1: Idempotencia de `normalize`

```lean
theorem normalize_idem (A : CList) : normalize (normalize A) = normalize A
```

**Por qué es suficiente**: Con esto, dentro del caso inductivo:

- Sean `na = normalize a`, `nb = normalize b` con `a ∈ Ax`, `b ∈ Bx`.
- `cSize na ≤ cSize a < cSize A` (por `normalize_cSize_le`).
- Si `extEq na nb = true`, la IH da `normalize na = normalize nb`.
- Por idempotencia: `normalize na = na` y `normalize nb = nb`.
- Luego `na = nb` (proposicionalmente). ✓

**Prueba de idempotencia** (por inducción sobre `cSize A`):

`A = mk xs`:

1. `normalize A = mk ys` donde `ys = insertionSort (dedup (xs.map normalize))`.
2. `normalize (normalize A) = mk (insertionSort (dedup (ys.map normalize)))`.
3. Por IH sobre `x ∈ xs`: `normalize (normalize x) = normalize x`.
4. Cada `y ∈ ys` es de la forma `normalize x`, así que `normalize y = y`. **Conclusión**: `ys.map normalize = ys`.
5. `dedup (ys.map normalize) = dedup ys`.
6. `ys` es `Nodup` (por `insertionSort_nodup` + `dedup_nodup`).
7. Por **`dedup_id_of_nodup`**: `dedup ys = ys`.
8. `ys` es `Sorted` (por `insertionSort_sorted`).
9. Por **`insertionSort_id_of_sorted_nodup`**: `insertionSort ys = ys`.
10. Luego `normalize (normalize A) = mk ys = normalize A`. ✓

**Cota de terminación**: `cSize A`. Para `x ∈ xs`, `cSize x < cSize A`. ✓

---

### Pieza 2: Lemas auxiliares pendientes

#### L3: `dedup_id_of_nodup`

```lean
theorem dedup_id_of_nodup (l : List CList) (h : Nodup l) : dedup l = l
```

Prueba: Por inducción con el auxiliar paramétrico `dedupAux`:

```
∀ vistos, Nodup l → (∀ x ∈ l, l.any (fun v => extEq x v) = false [para vistos]) →
  dedupAux l vistos = l
```

#### L4: `insertionSort_id_of_sorted_nodup`

```lean
theorem insertionSort_id_of_sorted_nodup (l : List CList)
    (hs : Sorted l) (hn : Nodup l) : insertionSort l = l
```

Prueba: Por inducción.

- `l = []`: trivial.
- `l = [x]`: `orderedInsert x [] = [x]`. ✓
- `l = x :: y :: rest`:
  - `hs` da `lt x y = true` y `Sorted (y :: rest)`.
  - Por IH: `insertionSort (y :: rest) = y :: rest`.
  - `insertionSort l = orderedInsert x (y :: rest)`.
  - Como `lt x y = true`, `orderedInsert x (y :: rest) = x :: y :: rest = l`. ✓

---

### Pieza 5: Unicidad de listas ordenadas y sin duplicados

```lean
theorem sorted_nodup_setEquiv_eq (l₁ l₂ : List CList)
    (hs1 : Sorted l₁) (hs2 : Sorted l₂)
    (hn1 : Nodup l₁) (hn2 : Nodup l₂)
    (h : SetEquiv l₁ l₂) : l₁ = l₂
```

Con idempotencia (Pieza 1) establecida en el contexto del teorema principal:
- Para `x ∈ l₁` existe `y ∈ l₂` con `extEq x y = true`.
- Como `x, y` son normalizados, la IH da `normalize x = normalize y`. Por idempotencia `x = y`.
- Así `l₁` y `l₂` son el mismo conjunto proposicional.
- Con `Sorted` y `Nodup` y totalidad de `lt`, son la misma lista.

Demostración formal por inducción en `l₁`:

- `l₁ = []`: `SetEquiv [] l₂ → l₂ = []`.
- `l₁ = x :: xs`: `x` es el mínimo de `l₁` (por `Sorted`). Por `SetEquiv`, `x` aparece en `l₂`
  proposicionalmente. Como `l₂` está ordenada, `x` debe ser su primer elemento.
  Aplicar IH a las colas.

---

## Plan de implementación (orden de ataque)

```
Pendiente:
1. dedup_id_of_nodup                       (Pieza 2 / L3)

2. insertionSort_id_of_sorted_nodup        (Pieza 2 / L4)
   └── usa lt_total (ya demostrado ✅)

3. normalize_idem                          (Pieza 1)
   └── usa dedup_id_of_nodup (1)
   └── usa insertionSort_id_of_sorted_nodup (2)
   └── usa insertionSort_sorted ✅, insertionSort_nodup ✅
   └── usa normalize_cSize_le ✅

4. sorted_nodup_setEquiv_eq                (Pieza 5)
   └── usa normalize_idem (3) + IH del teorema principal
   └── usa lt_total ✅

5. normalize_eq_of_extEq (cerrar el sorry)
   └── usa normalize_idem (3)
   └── usa sorted_nodup_setEquiv_eq (4)
   └── usa dedup_nodup ✅, insertionSort_sorted ✅
```

---

## Problema de la medida de terminación en `normalize_eq_of_extEq`

La medida `termination_by cSize A + cSize B` es compatible con la IH aplicada a pares normalizados:

- Para `a ∈ Ax, b ∈ Bx` con `extEq a b = true`:
  - `cSize (normalize a) ≤ cSize a < cSize A`  (por `normalize_cSize_le` + `a ∈ Ax`)
  - `cSize (normalize b) ≤ cSize b < cSize B`
  - Luego `cSize (normalize a) + cSize (normalize b) < cSize A + cSize B`. ✓

Para `normalize_idem` se usará `cSize A` como medida (un solo argumento).

---

## Resumen: lo que bloquea el `sorry`

```
extEq A B = true  →  normalize A = normalize B

normalize A = mk (insertionSort (dedup (Ax.map normalize)))
normalize B = mk (insertionSort (dedup (Bx.map normalize)))

Necesitamos: insertionSort l₁ = insertionSort l₂
  donde l₁ ≈ l₂ (SetEquiv) y Nodup l₁, Nodup l₂

Paso clave: elementos de l₁ y l₂ son normalizados →
  extEq na nb = true → na = nb (proposicional)     [requiere normalize_idem]

Con eso: l₁ y l₂ tienen los mismos elementos proposicionalmente

Con sorted + nodup + lt_total: l₁ = l₂              [requiere sorted_nodup_setEquiv_eq]
Luego insertionSort l₁ = insertionSort l₂. ✓
```

Los dos grandes lemas a demostrar son:

1. **`normalize_idem`**: `normalize (normalize A) = normalize A`
   - Requiere: `dedup_id_of_nodup`, `insertionSort_id_of_sorted_nodup`

2. **`sorted_nodup_setEquiv_eq`**: unicidad de forma normal
   - Requiere: `lt_total` ✅ (ya demostrado)
