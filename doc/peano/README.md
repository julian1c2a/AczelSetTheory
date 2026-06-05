# Documentación heredada de Peano

> ← [Volver a doc/](../) | [REFERENCE.md raíz](../../REFERENCE.md)

Este directorio contiene documentos específicos del proyecto **Peano**
(`https://github.com/julian1c2a/Peano`), predecesor directo de AczelSetTheory.

Peano está en **feature-freeze** desde 2026-05-10. AczelSetTheory importa sus
módulos de Foundations y arithmetic y es la rama activa del desarrollo matemático.

---

## Índice

| Archivo | Contenido |
|---|---|
| [CAUCHY_MCKAY_PROOF.md](CAUCHY_MCKAY_PROOF.md) | Prueba del Teorema de Cauchy vía argumento de McKay |
| [FERMAT_PROOF.md](FERMAT_PROOF.md) | Prueba del Pequeño Teorema de Fermat |
| [INTUICIONES.md](INTUICIONES.md) | Notas de intuición matemática y diseño |
| [LISTS_FSETS_N_FSETFUNCTIONS.md](LISTS_FSETS_N_FSETFUNCTIONS.md) | Infraestructura List, FSet y FSetFunction |
| [ListasYConjuntos.md](ListasYConjuntos.md) | Relación entre listas y conjuntos en Peano |
| [PEANO_MATHLIB_COMPARE.md](PEANO_MATHLIB_COMPARE.md) | Comparación Peano vs Mathlib4 |

---

## Relación con AczelSetTheory

Los módulos técnicos de Peano se documentan en los archivos `doc/REFERENCE-*.md`
de la carpeta padre:

| Documento | Módulos cubiertos |
|---|---|
| [../REFERENCE-Foundation.md](../REFERENCE-Foundation.md) | Axiomas PA, PureAxioms, Foundation |
| [../REFERENCE-Arithmetic.md](../REFERENCE-Arithmetic.md) | Add, Sub, Mul, Div, Pow, Arith, Order |
| [../REFERENCE-ListsAndSets.md](../REFERENCE-ListsAndSets.md) | FSet, FSetFunction, EquivRel |
| [../REFERENCE-NumberTheory.md](../REFERENCE-NumberTheory.md) | ModEq, Totient, CRT, Fermat, Wilson |
| [../REFERENCE-Combinatorics.md](../REFERENCE-Combinatorics.md) | Factorial, Binom, NewtonBinom, Perm |
| [../REFERENCE-GroupTheory.md](../REFERENCE-GroupTheory.md) | Group, Subgroup, Cosets, Sylow I–III |
| [../REFERENCE-Prelim.md](../REFERENCE-Prelim.md) | Prelim, ExistsUnique, Tuples |

---

*Documentación migrada el 2026-05-22 como parte del handoff Peano → AczelSetTheory.*
