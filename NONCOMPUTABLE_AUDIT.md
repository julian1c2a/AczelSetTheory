# Auditoría de Computabilidad (`noncomputable`)

De acuerdo con el plan, he procedido a rastrear rigurosamente cualquier declaración que requiera de los axiomas clásicos de elección matemática para su ejecución dentro de los proyectos `AczelSetTheory` y `Peano`.

### Resultados en `AczelSetTheory` (Librería ZFC Computacional)

> [!SUCCESS] 100% de Computabilidad Alcanzada
> No existe **absolutamente ninguna** declaración `noncomputable` activa en todo el código base de `AczelSetTheory`. Se han examinado exhaustivamente los módulos de Números Reales, Racionales, Enteros, Matrices, Teoría de Grupos de Sylow, y finalmente el segmento conflictivo de Von Neumann (`VN`). 

El único rastro de la palabra `noncomputable` se encuentra en el archivo de comentario `Algebra/HFMatrix.lean:12` indicando que el módulo tiene "0 noncomputable def". El Axioma de Elección es totalmente inactivo o ha sido re-expresado constructivamente dentro de los límites finitarios.

### Resultados en `Peano` (Librería Base de Aritmética Primitiva)

La librería base de Peano conserva algunos marcadores de `noncomputable` encapsulados **por diseño**. Estos ocurren en dos frentes específicos:
1. **`Prelim/Classical.lean`**: Define explícitamente los axiomas del Operador de Elección Fuerte (`choose`, `choose_unique`) para cuando se necesite exportar matemáticas que genuinamente requieran constructos infinitos (aunque Aczel no los invoca).
2. **`GroupTheory/*`** y **`QuotientGroup.lean`**: En la aritmética abstracta de cocientes (mapas de isomorfismos, proyecciones de Sylow, `zassenhaus_map`, etc.) se declaran como `noncomputable` porque están definiendo homomorfismos grupales abstractos usando representaciones puramente algebraicas. Dado que el alcance algorítmico de los dominios abstractos de tipos puede ser infinito, Lean exige el marcador.
   - *Nota*: La adaptación de los grupos a `HFSet` (como acabamos de hacer en `VN`) sí hereda computabilidad plena.

---

### Siguientes pasos (Ruta Crítica)
Al haber completado los puntos **[1] Purga de noncomputable en Von Neumann** y **[2] Auditoría de computabilidad**, me propongo continuar con los pasos acordados:

- **[3]** Cota de iteración en `Roots.lean` (Newton-Raphson es una secuencia de Cauchy).
- **[4]** Lema de Separación en enteros ($|a^n - m \cdot b^n| \ge 1$).
- **[5]** Documentación final.
- **[6]** Git commit.
