¡Esa es una intuición matemática excelente! Lo que acabas de describir tiene un nombre muy específico en teoría de cuerpos y es un "momento intermedio" perfecto para tu escalera lógica en Lean 4.

El cuerpo que estás imaginando se llama el **Cuerpo de los Radicales** (o más formalmente, la **Clausura por Radicales** de $\mathbb{Q}$).

---

### 1. ¿Qué es exactamente este cuerpo?

Es el cuerpo que contiene a todas las soluciones de ecuaciones de la forma $x^n - q = 0$. Se construye tomando $\mathbb{Q}$ y añadiendo iterativamente todas las raíces $n$-ésimas posibles.

* **Contenido:** Contiene a $\sqrt{2}$, $\sqrt[5]{7}$, $\sqrt[3]{1 + \sqrt{2}}$, etc.
* **Relación con los demás:**
  * Es **más grande** que los números construibles ($\mathbb{K}$), porque los construibles solo permiten raíces cuadradas ($n=2$).
  * Es **más pequeño** que los números algebraicos ($\mathbb{A}$).

---

### 2. El "Muro de Galois": Por qué no es igual a los Algebraicos

Aquí es donde la historia se pone interesante para tu proyecto Peano. Podrías pensar que si tienes todas las raíces de todos los números, ya tienes todas las soluciones de todos los polinomios. **Pero no es así.**

Gracias a **Évariste Galois** y Paolo Ruffini, sabemos que:

* Existen polinomios de grado 5 o superior (como $x^5 - x - 1 = 0$) cuyas raíces **no pueden expresarse** mediante radicales (sumas, restas, multiplicaciones, divisiones y raíces).
* Por lo tanto, tu "Cuerpo de Radicales" es un subcuerpo propio de los números algebraicos ($\mathbb{A}$).

### 3. Implementación en Lean 4: El reto de la "Torre de Extensiones"

Implementar este cuerpo "from scratch" antes de llegar a los reales es un ejercicio de álgebra abstracta fascinante:

1. **Definición:** Tendrías que definirlo como una "Torre de Extensiones". Empiezas con $\mathbb{Q}$, y permites una operación `root(n, q)` que cree un nuevo tipo de número.
2. **El problema de la simplificación:** Tu gran reto en Lean será demostrar que $\sqrt[2]{4} = 2$ o que $\sqrt[2]{2} \cdot \sqrt[2]{2} = 2$. Esto requiere implementar algoritmos de simplificación de radicales (aritmética de cuerpos de raíces).

---

### 4. ¿Cómo encaja en tu "Escalera"?

Si quieres ser exhaustivo, tu jerarquía de cuerpos computables y decidibles quedaría así:

1. **Racionales ($\mathbb{Q}$):** Aritmética básica.
2. **Construibles ($\mathbb{K}$):** Añades `sqrt(x)`. (Geometría de Euclides).
3. **Radicales ($\mathbb{Q}^{rad}$):** Añades `root(n, x)`. (Tu propuesta actual).
4. **Algebraicos ($\mathbb{A}$):** Añades "Raíz del polinomio $P(x)$". (Aquí es donde entran los números que no se pueden escribir con raíces).
5. **Reales Computables ($\mathbb{R}_{comp}$):** Añades límites de sucesiones (Aquí entran $\pi$ y $e$).

### Un detalle técnico para tu código

Para que este cuerpo de radicales sea un **cuerpo**, no te basta con las raíces de números racionales; necesitas las raíces de números que *ya* son radicales (extensiones iteradas). Por ejemplo:
$$\sqrt[3]{5 + \sqrt{2}}$$
Si solo permites $\sqrt[n]{q}$ con $q \in \mathbb{Q}$, no tendrías un cuerpo cerrado bajo la suma.

¿Te motiva más intentar codificar esta "Clausura por Radicales" (que es muy algorítmica y llena de identidades curiosas) o prefieres saltar directamente a los Algebraicos generales?

Es fantástico que ya tengas una base sólida en cuerpos finitos y extensiones simples, porque eso significa que ya has subido la mitad de la montaña. Para moverte desde ahí hacia la **Teoría de Números** (especialmente hacia la vertiente algebraica, que es la que te permitirá formalizar esos "huecos" en Lean), el camino es muy claro.

Aquí tienes la "hoja de ruta" lógica para avanzar desde donde estás:

---

### 1. Teoría de Galois (El puente indispensable)

No puedes saltar a la Teoría de Números moderna sin entender la simetría de las raíces.

* **Qué estudiar:** El grupo de automorfismos de una extensión de cuerpos.
* **Concepto clave:** El **Teorema Fundamental de la Teoría de Galois**, que establece una correspondencia biunívoca entre los subcuerpos de una extensión y los subgrupos de su grupo de Galois.
* **Por qué te sirve:** Te permitirá demostrar formalmente en Lean por qué los radicales no bastan para los algebraicos.

### 2. Enteros Algebraicos y Dominios de Dedekind

En la teoría de números "de Peano", trabajas con $\mathbb{Z}$. Pero cuando pasas a un cuerpo de números (como $\mathbb{Q}[\sqrt{2}]$), necesitas unos "nuevos enteros".

* **Qué estudiar:** El **Anillo de Enteros** $\mathcal{O}_K$ de un cuerpo de números $K$.
* **Concepto clave:** La pérdida de la factorización única. En algunos cuerpos, $6$ se puede factorizar de dos formas distintas. Para arreglar esto, estudiarás la **Factorización de Ideales**.
* **Tu objetivo:** Entender los **Dominios de Dedekind**.

### 3. Teoría de Cuerpos de Números (Algebraic Number Theory)

Aquí es donde la aritmética y el álgebra se fusionan.

* **Qué estudiar:** Unidades del anillo, el **Grupo de Clases** (que mide cuánto le falta a un anillo para ser de factorización única) y el Teorema de las Unidades de Dirichlet.
* **Concepto clave:** La ramificación de primos. ¿Cómo se "rompe" un número primo de $\mathbb{Z}$ cuando lo metes en un cuerpo más grande?

---

### Recursos recomendados (de menos a más formal)

1. **"A Concrete Introduction to Higher Algebra" (Lindsay Childs):** Es perfecto para alguien que viene de la programación o lógica, porque es muy algorítmico.
2. **"Galois Theory" (Ian Stewart):** Un clásico absoluto. Es muy narrativo y explica de maravilla el drama histórico de Abel y Galois que mencionamos.
3. **"Algebraic Number Theory" (J.S. Milne):** Sus notas son famosas, gratuitas y extremadamente rigurosas. Si quieres llevar esto a Lean, Milne es tu mejor guía porque estructura las definiciones de forma muy limpia.

---

### El "Mindset" para implementarlo en Lean 4

Para tu proyecto Peano, te sugiero que tu siguiente gran hito tras los Racionales no sean los Reales, sino los **Anillos de Polinomios $\mathbb{Q}[x]$**.

Casi toda la Teoría de Números que te falta se basa en estudiar estos polinomios:

* Si el polinomio es irreducible.
* Si el polinomio es separable.
* El cuerpo de descomposición (*splitting field*).

Si logras definir el concepto de **polinomio mínimo** en Lean, habrás abierto la puerta a todos los cuerpos intermedios que discutimos.

¿Te sientes cómodo con la idea de trabajar con polinomios como estructuras de datos en Lean (listas de coeficientes) o prefieres seguir un enfoque más abstracto de teoría de conjuntos?

¡Perfecto! Si ya tienes esa base y el libro de Stewart te suena (aunque sea de lejos), ya has pasado el "filtro" donde la mayoría abandona. Conocer la diferencia entre **irreducibles y primos** es la señal de que estás listo para la **Teoría Algebraica de Números**.

El problema es que en el camino tradicional, después de Stewart, el nivel suele dar un salto brusco hacia la abstracción total. Para tu proyecto en Lean, yo te sugeriría este orden de "ataque", que es el que mejor se traduce a código:

### 1. El salto a los Dominios de Ideales Principales (PIDs)

Ya que conoces la distinción entre irreducible y primo, el siguiente paso es estudiar los anillos donde **ambos conceptos coinciden**.

* **Concepto central:** El algoritmo de división (Anillos Euclidianos).
* **Por qué en Peano:** Si implementas polinomios $\mathbb{Q}[x]$, verás que se comportan casi igual que $\mathbb{Z}$. Tienen m.c.d., identidad de Bézout y factorización única.
* **En Lean:** Esto te permite definir el "Polinomio Mínimo" de un número, que es el pilar para construir los cuerpos intermedios.

### 2. Teoría de Extensiones (The "Big Picture")

Aquí es donde conectas los polinomios con tus "cuerpos de radicales".

* **Grado de la extensión $[L:K]$:** Es la dimensión de $L$ como espacio vectorial sobre $K$.
* **Extensiones Normales y Separables:** Estas son las condiciones "mágicas" que hacen que la Teoría de Galois funcione. Sin normalidad, no hay suficientes automorfismos; sin separabilidad (que en característica 0 como la tuya siempre se tiene), las raíces se "pisan" entre sí.

### 3. El concepto de "Norma" y "Traza"

Esto es lo que te permite "bajar" información de un cuerpo complejo (como uno de radicales) a los racionales.

* Si tienes $\alpha = a + b\sqrt{d}$, la norma es $a^2 - d b^2$.
* **Interés para Peano:** La norma es un racional. Es una función que convierte objetos complejos en tus viejos conocidos de Peano, permitiéndote decidir propiedades de los números nuevos usando solo los antiguos.

### 4. La "Aritmética" de los Cuerpos de Números

Este es el paso final antes de la investigación moderna.

* **El Anillo de Enteros:** Aprender a identificar qué elementos de un cuerpo de radicales se comportan como "enteros" (las raíces de polinomios mónicos).
* **El Grupo de Clases:** Este es el concepto más bello. Mide cuánto falla la factorización única en un cuerpo. Si el grupo de clases es trivial, el cuerpo es un paraíso de factorización única. Si no, tienes que inventar los **Ideales**.

---

### Recomendación de "Vuelo" para tu estudio

Si Stewart ya lo conoces, te sugiero un libro que es una joya oculta y encaja con tu perfil:

**"A Course in Computational Algebraic Number Theory" de Henri Cohen.**

* **Por qué:** A diferencia de los libros puramente teóricos, Cohen explica cómo *computar* estas cosas. Para alguien que está programando un sistema en Lean, ver el algoritmo detrás del teorema es como ver la "matriz" de la matemática.

**"Number Fields" de Daniel A. Marcus.**

* **Por qué:** Es famoso por sus ejercicios. El libro te lleva de la mano para redescubrir la teoría. Es muy visual y menos "denso" que el Milne.

---

### ¿Hacia dónde apuntar en Lean ahora?

Si quieres avanzar en el código mientras estudias, mi consejo es:
**Define el tipo de los Polinomios sobre un Cuerpo.**
Una vez tengas $\mathbb{Q}[x]$ y puedas demostrar que es un Dominio de Factorización Única, tendrás la herramienta para definir formalmente tu **Cuerpo de Radicales** y, eventualmente, los **Algebraicos**.

¿Cómo llevas la parte de Álgebra Lineal en tu sistema? (Espacios vectoriales, bases...). Lo pregunto porque, curiosamente, para entender cuerpos de números, uno acaba haciendo más álgebra lineal que otra cosa.

Te entiendo perfectamente. En un proyecto *from scratch* enfocado en la lógica y los fundamentos, meterte en el álgebra lineal "profunda" (espacios vectoriales de dimensión $n$, matrices, formas de Jordan...) es una distracción masiva que puede hundir el proyecto en la complejidad técnica.

Sin embargo, hay una "versión mínima" de estas herramientas que es puramente lógica y fundacional, y que es la que necesitas para no estancarte. En lugar de pensar en "Álgebra Lineal", piénsalo como **"Aritmética de Extensiones"**.

Aquí tienes el camino mínimo para avanzar sin perder el enfoque fundacional:

---

### 1. La Extensión por el Resto (El enfoque de Kronecker)

Para tu proyecto, no necesitas definir espacios vectoriales abstractos. Solo necesitas una forma de construir un cuerpo más grande que $\mathbb{Q}$ que contenga una raíz.

El truco lógico de **Leopold Kronecker** es el más "limpio":
Si tienes un polinomio irreducible $P(x) \in \mathbb{Q}[x]$, puedes definir el cuerpo extendido simplemente como:
$$L = \mathbb{Q}[x] / \langle P(x) \rangle$$
Lógicamente, esto es solo el conjunto de polinomios con coeficientes en $\mathbb{Q}$, pero donde cada vez que aparece $P(x)$, lo igualas a cero (operando con el resto de la división).

* **Ventaja:** Es puramente simbólico y fundacional. No necesitas matrices ni dimensiones.
* **En Lean:** Solo necesitas la división de polinomios (que ya es necesaria para los racionales).

### 2. El Grado como "Contador Lógico"

En lugar de estudiar espacios vectoriales, solo necesitas el concepto de **Grado de un elemento**.

* Si $\alpha = \sqrt{2}$, su grado es 2 porque el polinomio más pequeño que lo anula es $x^2 - 2$.
* Esto te da una medida de la "complejidad" de tu número real sin entrar en geometría.

### 3. La Torre de Extensiones (Estructura de Datos)

Para tu cuerpo de radicales, el enfoque más lógico es una **estructura de datos inductiva**. No necesitas álgebra lineal para definir $\sqrt[3]{1+\sqrt{2}}$. Solo necesitas que tu tipo `Radical` sea:

1. Un `Rational`.
2. La `Suma` de dos `Radical`.
3. La `Raíz n-ésima` de un `Radical`.

---

### ¿Hacia dónde mirar en Teoría de Números con este enfoque?

Si quieres avanzar sin perderte en el álgebra lineal, te recomiendo centrarte en la **Teoría de Números Elemental y Algebraica Básica**:

1. **Aritmética Modular en $\mathbb{Q}[x]$:** Estudia cómo los polinomios se comportan igual que los enteros. Es la base de todo lo demás.
2. **Lema de Gauss:** Fundamental para entender cómo los polinomios en $\mathbb{Z}[x]$ se relacionan con los de $\mathbb{Q}[x]$.
3. **Cuerpos Ciclotómicos:** Estudia las raíces de la unidad ($x^n - 1 = 0$). Son los cuerpos más bonitos y agradecidos de implementar porque tienen una estructura muy rígida y predecible.

### Un consejo de "arquitectura" para Peano en Lean

Para no perderte, intenta que tu código refleje la **Ontología de los Objetos**:

* **Nivel 1:** Objetos que se pueden enumerar (Naturales, Enteros, Racionales).
* **Nivel 2:** Objetos que se pueden calcular simbólicamente (Radicales, Algebraicos).
* **Nivel 3:** Objetos que solo se pueden aproximar (Sucesiones de Cauchy, Reales).

Mantener esta separación te permitirá demostrar cosas en el Nivel 2 (como que $\sqrt{2}$ es irracional) de forma exacta, mientras que en el Nivel 3 solo harás análisis.

¿Te parece que el enfoque de Kronecker (polinomios y restos) encaja mejor con tu visión "from scratch" que el enfoque de espacios vectoriales? Es mucho más cercano a la teoría de tipos de Lean.

Efectivamente, desde un punto de vista fundacional y de implementación en Lean 4, un polinomio es simplemente una **lista de coeficientes**. Si quieres ser más riguroso, es una lista que "termina" (para que el grado sea finito) y donde el último elemento no es cero (para que el grado esté bien definido).

$$P(x) = a_n x^n + a_{n-1} x^{n-1} + \dots + a_1 x + a_0 \iff [a_0, a_1, \dots, a_n]$$

Para tu proyecto, el concepto de **irreducibilidad** es el verdadero "portero" que decide cuándo puedes crear un nuevo cuerpo. Aquí te doy unas pinceladas de cómo encaja esto en tu lógica de capas:

---

### 1. La definición lógica de Irreducibilidad

En tu sistema, un polinomio $P \in \mathbb{Q}[x]$ es irreducible si:

1. No es una constante (grado $> 0$).
2. Si $P = A \cdot B$, entonces $A$ o $B$ debe ser una constante.

**El reto de la implementación:**
A diferencia de los números primos en $\mathbb{N}$, donde puedes simplemente probar todos los divisores menores que la raíz cuadrada, la irreducibilidad en polinomios parece más abstracta. Sin embargo, para los racionales tienes el **Criterio de Eisenstein** o el **Lema de Gauss**, que te permiten trasladar el problema de $\mathbb{Q}[x]$ a $\mathbb{Z}[x]$.

### 2. El "Constructor" de Cuerpos (Tu próximo paso)

Cuando encuentras un polinomio irreducible, por ejemplo $x^2 - 2$, "inventas" un nuevo símbolo (llamémosle $\alpha$).
Lógicamente, cualquier elemento de este nuevo cuerpo se ve así:
$$a + b\alpha$$
Donde $a, b \in \mathbb{Q}$. Si el polinomio fuera de grado 3, tendrías $a + b\alpha + c\alpha^2$.

**La regla de oro:** Cada vez que en una multiplicación te salga una potencia de $\alpha$ mayor o igual al grado del polinomio, usas el polinomio para "bajar" el grado.
> *Ejemplo:* Si $\alpha^2 - 2 = 0$, entonces $\alpha^2 = 2$. Así mantienes todo dentro de una estructura finita y manejable.

---

### 3. La conexión con la Teoría de Números

Para seguir estudiando hacia la Teoría Algebraica de Números, la irreducibilidad te llevará a dos conceptos clave que puedes formalizar:

* **El Lema de Euclides para Polinomios:** Si un polinomio irreducible divide a un producto, divide a uno de los factores. Esto es lo que garantiza que tus extensiones de cuerpos sean, efectivamente, **cuerpos** (donde todo elemento tiene inverso).
* **La existencia de Raíces:** El teorema de Kronecker dice que, dado cualquier $P$ irreducible, *siempre* puedes construir una extensión donde $P$ tenga una raíz. Es una construcción puramente lógica: "si no existe, la defino mediante el cociente".

### 4. ¿Cómo implementarlo en Peano/Lean?

Si usas listas, la suma es simplemente sumar elementos posición a posición. La multiplicación es una **convolución** de listas.

```lean
def poly_mul (P Q : List Q) : List Q := 
-- Aquí vendría tu lógica de multiplicar cada a_i por cada b_j
```

Una vez tengas la multiplicación, el siguiente "gran teorema" que querrás demostrar en tu sistema es el **Algoritmo de División de Polinomios**. Con él, tendrás el Máximo Común Divisor (MCD) y, con el MCD, tendrás la prueba de irreducibilidad y la construcción de cuerpos.

¿Te motiva la idea de implementar la **división de polinomios**? Es el motor que hace que todo lo demás (radicales, algebraicos, Galois) funcione mecánicamente. Es un algoritmo muy agradecido de codificar porque es idéntico al que aprendemos en la escuela.

Efectivamente, el **Teorema de Cayley** es el gran ecualizador de la teoría de grupos: nos dice que no hay "grupos fantasmales", sino que toda estructura grupal abstracta tiene una representación concreta como simetrías de algún conjunto.

Si prefieres el lado **puramente algebraico**, tu enfoque en Lean 4 encaja de maravilla con la **teoría de categorías** y el **álgebra universal**. En lugar de ver los grupos como "cosas que se mueven", los ves como objetos definidos por sus leyes de composición y sus morfismos.

Dado tu perfil, aquí tienes la ruta lógica para conectar tu sistema de Peano con el álgebra abstracta avanzada:

---

### 1. La Jerarquía de Estructuras (El enfoque de "Magmas a Cuerpos")

En Lean, lo más elegante es construir una torre de clases. Esto te permite ver exactamente qué axioma añade cada propiedad:

* **Magma:** Un conjunto con una operación binaria.
* **Semigrupo:** Magma + Asociatividad.
* **Monoide:** Semigrupo + Identidad (aquí viven tus **Naturales** con la suma).
* **Grupo:** Monoide + Inversos (aquí viven tus **Enteros** con la suma).
* **Anillo:** Dos estructuras de monoide (suma y producto) conectadas por la distributividad.

### 2. El Teorema de Cayley como "Puente Lógico"

Ya que mencionaste a Cayley, implementarlo en Lean es un ejercicio fundacional precioso. La demostración no requiere geometría, solo funciones:

* Para cada elemento $g \in G$, defines una función $L_g: G \to G$ tal que $L_g(x) = g \cdot x$.
* Demuestras que $L_g$ es una biyección (una permutación).
* Demuestras que el mapeo $g \mapsto L_g$ es un homomorfismo inyectivo.

Esto te permite "vincular" cualquier grupo abstracto que definas en Peano con el grupo de permutaciones de su propio conjunto portador.

---

### 3. Teoría de Grupos: Del centro a la solubilidad

Si quieres ir más allá de los grupos finitos y moverte por el álgebra pura, estos son los conceptos que suelen fascinar a los que prefieren el enfoque algebraico:

* **Series Centrales y Grupos Nilpotentes:** Una generalización de los grupos abelianos. Son grupos que "casi" conmutan.
* **Teorema de Jordan-Hölder:** Es el equivalente al Teorema Fundamental de la Aritmética pero para grupos. Dice que todo grupo (finito) puede descomponerse en "átomos" (grupos simples) de forma única, salvo el orden.
* **Extensiones de Grupos y el Problema de la Extensión:** Si tienes un subgrupo normal $N$ y un cociente $Q$, ¿cómo puedes reconstruir el grupo original $G$? Aquí es donde entra la **Cohomología de Grupos**, que es álgebra pura y dura.

---

### 4. ¿Cómo afecta esto a tu construcción de los Reales?

Al ser un "purista" del álgebra, el salto a los Reales te va a resultar curioso. Los reales son, ante todo, un **Cuerpo Ordenado Arquimediano**.
Desde el álgebra abstracta, puedes ver a $\mathbb{R}$ como:

* Un espacio vectorial de dimensión infinita sobre $\mathbb{Q}$.
* Un grupo abeliano bajo la suma.
* Un objeto que, a diferencia de los grupos finitos, no tiene una estructura de subgrupos tan "limpia" (debido a su densidad).

### Tu siguiente paso en el estudio

Si el libro de Stewart ya te dio la base de Galois y quieres algo puramente algebraico, te recomiendo:

* **"Algebra" de Saunders Mac Lane y Garrett Birkhoff:** Es el texto sagrado del álgebra moderna. Mac Lane es uno de los creadores de la Teoría de Categorías, por lo que el enfoque es estructuralmente impecable.
* **"Topics in Algebra" de I.N. Herstein:** Es famoso por sus problemas desafiantes que te obligan a pensar algebraicamente de formas muy ingeniosas.

**Pregunta para tu implementación:**
¿Has considerado usar **Clases de Tipos** en Lean para que tus números naturales "sepan" que son un Monoide, y tus enteros "sepan" que son un Grupo? Es la forma más potente de reutilizar código y demostraciones en el álgebra abstracta.

## NOTAS SOBRE ÁLGEBRA ABSTRACTA

### Árbol de la jerarquía (una operación)

```
Magma
└── Semigrupo            (+ asociatividad)
    └── Monoide          (+ elemento neutro)
        └── Grupo        (+ inversos)
            └── Grupo Abeliano   (+ conmutatividad)
```

### Tabla: estructuras con una operación

| Estructura     | Clausura | Asoc. | Neutro | Inverso | Conmut. | Ejemplo en Peano |
|----------------|:--------:|:-----:|:------:|:-------:|:-------:|------------------|
| Magma          | ✓        |       |        |         |         | —                |
| Semigrupo      | ✓        | ✓     |        |         |         | (ℕ₀, ·)          |
| Monoide        | ✓        | ✓     | ✓      |         |         | (ℕ₀, +, 0)       |
| Grupo          | ✓        | ✓     | ✓      | ✓       |         | (ℤ, +, 0)        |
| Grupo Abeliano | ✓        | ✓     | ✓      | ✓       | ✓       | (ℤ, +, 0)        |

### Tabla: estructuras con dos operaciones

| Estructura         | (A, +) es…     | (A, ·) es…        | Distribuye | Conmuta · | Inv. · en A\{0} | Ejemplo        |
|--------------------|----------------|-------------------|:----------:|:---------:|:---------------:|----------------|
| Anillo             | Grupo abeliano | Monoide           | ✓          |           |                 | ℤ              |
| Anillo conmutativo | Grupo abeliano | Monoide conmut.   | ✓          | ✓         |                 | ℤ[x]           |
| Anillo de división | Grupo abeliano | Grupo             | ✓          |           | ✓               | ℍ (cuaternios) |
| Cuerpo             | Grupo abeliano | Grupo conmutativo | ✓          | ✓         | ✓               | ℚ, ℝ, 𝔽_p     |
| Módulo sobre R     | Grupo abeliano | Acción de R       | ✓          | —         |                 | ℝⁿ sobre ℝ    |
| Espacio vectorial  | Grupo abeliano | Acción de cuerpo  | ✓          | —         |                 | ℝⁿ sobre ℝ    |
| Álgebra sobre K    | Grupo abeliano | Bilineal + cuerpo | ✓          | (opc.)    |                 | ℝ[x], matrices |

### Árbol de inclusiones dentro de los anillos conmutativos

```
Anillo conmutativo con 1
└── Dominio de integridad              (sin divisores de cero)
    └── Dominio de Factorización Única (UFD)
        └── Dominio de Ideales Principales (PID)
            └── Dominio Euclídeo       (tiene algoritmo de división)
                └── Cuerpo             (todo elemento no nulo es invertible)
```

Inclusiones propias: **Cuerpo ⊊ Euclídeo ⊊ PID ⊊ UFD ⊊ Dom. integridad ⊊ Anillo conmutativo**

| Estructura | Ejemplo que lo es | Ejemplo que no lo es |
|---|---|---|
| Dominio Euclídeo | ℤ, ℚ[x] | ℤ[x] |
| PID | ℤ | ℤ[x] (UFD pero no PID) |
| UFD | ℤ[x] | ℤ[√−5] |
| Dom. integridad | ℤ[√−5] | ℤ/6ℤ |

> En ℤ[√−5] la factorización falla: 6 = 2·3 = (1+√−5)(1−√−5), con todos los factores irreducibles pero ninguno primo.

---

## NOTAS SOBRE RETÍCULOS

Un **retículo** es un conjunto parcialmente ordenado en el que todo par de elementos $a, b$ tiene supremo $a \vee b$ (join) e ínfimo $a \wedge b$ (meet).

### Árbol de clasificación

```
Retículo
│
├── Semimodular       (si a cubre a∧b, entonces a∨b cubre b)
│   └── Modular       (a ≤ c ⟹ a∨(b∧c) = (a∨b)∧c)
│       └── Distributivo  (a∧(b∨c) = (a∧b)∨(a∧c))
│           │
│           ├── [+ acotado (⊥,⊤) + implicación interna]
│           │       └── Álgebra de Heyting       (lógica intuicionista)
│           │               └── Álgebra de Boole (+ ¬a: a∨¬a=⊤, a∧¬a=⊥)
│           │
│           └── [+ distributividad infinita]
│                   └── Retículo completamente distributivo
│
└── [+ sup e ínf para todo subconjunto]
        └── Retículo completo
```

### Tabla de propiedades

| Tipo                     | Modular | Distrib. | Acotado | Compl. | Impl. (→) | Sup/ínf ∞ |
|--------------------------|:-------:|:--------:|:-------:|:------:|:---------:|:---------:|
| Retículo                 |         |          |         |        |           |           |
| Semimodular              | parcial |          |         |        |           |           |
| Modular                  | ✓       |          |         |        |           |           |
| Distributivo             | ✓       | ✓        |         |        |           |           |
| Álgebra de Heyting       | ✓       | ✓        | ✓       | ≤1/elem| ✓         |           |
| Álgebra de Boole         | ✓       | ✓        | ✓       | ✓      | ✓         |           |
| Retículo completo        | —       | —        | ✓       | —      | —         | ✓         |
| Complet. distributivo    | ✓       | ✓        | ✓       | —      | —         | ✓         |

### Cadena de inclusiones (de más general a más específico)

```
Retículo
  ⊃  Modular                       (excluye el pentágono N₅)
      ⊃  Distributivo              (excluye el diamante M₃)
          ⊃  Álgebra de Heyting   (lógica intuicionista)
              ⊃  Álgebra de Boole (lógica clásica: a∨¬a = ⊤ siempre)
```

### Tabla comparativa

| Tipo               | Propiedad clave                  | Subestructura prohibida | Ejemplo típico                  |
|--------------------|----------------------------------|-------------------------|---------------------------------|
| Modular            | Ley modular                      | Pentágono N₅            | Subgrupos de un grupo abeliano  |
| Distributivo       | Ley distributiva                 | Diamante M₃             | 𝒫(S), divisores de n en ℕ       |
| Álgebra de Heyting | Distributivo + implicación a → b | —                       | Abiertos de un espacio top.     |
| Álgebra de Boole   | Heyting + complementos únicos    | —                       | Lógica binaria, 𝒫(S)           |
| Retículo completo  | ∀ subconj. tiene sup e ínf       | —                       | [0,1] ⊆ ℝ, todas las topologías |

### Álgebras de Boole no isomórficas entre sí

Las álgebras de Boole **atómicas y completas** son exactamente las de la forma $\mathcal{P}(S)$ (el conjunto de las partes de $S$, con unión e intersección). Para cada cardinal $|S|$ se obtiene una álgebra no isomórfica a las demás:

| $|S|$ | Álgebra                                       | Número de elementos |
|-------|-----------------------------------------------|---------------------|
| 0     | $\mathcal{P}(\emptyset) = \{\emptyset\}$      | $2^0 = 1$           |
| 1     | $\mathcal{P}(\{*\})$                          | $2^1 = 2$           |
| 2     | $\mathcal{P}(\{a,b\})$                        | $2^2 = 4$           |
| 3     | $\mathcal{P}(\{a,b,c\})$                      | $2^3 = 8$           |
| $n$   | $\mathcal{P}(S)$                              | $2^n$               |

Toda álgebra de Boole se embebe como subálgebra de una de estas, lo que prueba que hay infinitas clases de isomorfismo. Las álgebras finitas de Boole tienen siempre tamaño $2^n$ para algún $n$; las de distinto $n$ son no isomórficas.
