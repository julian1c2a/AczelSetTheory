# Thoughts — AczelSetTheory

**Last updated:** 2026-04-10 00:00
**Author**: Julián Calderón Almendros

> This is an informal design journal. Record ideas, alternatives considered,
> open questions, and future directions here. Not normative — purely exploratory.
> Useful for AI context on "why" decisions were made.

---

## Nuevos pensamientos

- **Powerset resuelto — filter como testigo de sublistas**: La clave para probar `powersetCList_extEq` fue demostrar primero `mem_powersetCList` (y ∈ powerset(A) ↔ y ⊆ A) como lema intermedio. La dirección difícil (←) se resolvió usando `xs.filter (fun z => mem z y)` como testigo sublista. Esta técnica reutiliza toda la infraestructura de `CList/Filter.lean` (`P_respects`, `extEq_filter`, `filter_in_sublists`) en lugar de intentar construir una correspondencia directa entre sublistas de A₁ y A₂. Lección: cuando la correspondencia directa es combinatoriamente compleja, buscar una **caracterización semántica** (aquí: subset) que simplifique la prueba de extEq a transitividad.
- **Separación Arquitectónica (Operations vs Axioms)**: Con la formalización de Union, Intersection, y Setminus, quedó claro que era beneficioso separar la definición de la operación computacional (Operations/) de los axiomas conceptuales tipo Zermelo (Axioms/). Esta estructura facilita la localización de fallos en Lean 4.
- **Setminus como herramienta para el Axioma de Regularidad / Buena Fundación**: Implementar la diferencia simétrica (Setminus) va a resultar esencial para enunciar la Regularidad, ya que este requiere quitar elementos (o calcular intersecciones vacías).
- **El reto de Powerset**: Al contrario que con Union que requiere "aplanar" listas, o Intersection que descarta elementos, el Conjunto Potencia (powersetCList) es constructivamente intensivo porque requiere construir explícitamente ${}^N$ sublistas y probar que extensionalmente se corresponden. Requerirá su propio módulo auxiliar.
- **Axioma de Elección**: Sigue estando la duda si el Axioma de Elección es derivable en sets hereditariamente finitos, tal cual pasa en ZF con modelos restringidos. Veremos.

---
