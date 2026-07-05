# Construcción de Raíces y Prueba de Irracionalidad

## 1. El Enfoque Clásico y sus Limitaciones

La prueba clásica de que la raíz cuadrada (o n-ésima) de un número primo $p$ es irracional suele estructurarse como una demostración por reducción al absurdo:

Supongamos que existe un $r \in \mathbb{Q}_{\ge 0}$ tal que $r^n = p$.
Podemos escribir a $r = \frac{a}{b}$ con $a, b \in \mathbb{N}$ y $\gcd(a, b) = 1$.

Tenemos que:
$$ \left(\frac{a}{b}\right)^n = p \implies \frac{a^n}{b^n} = p \implies a^n = p \cdot b^n $$

Por lo tanto: $p \mid a^n$, lo que implica (por el Lema de Euclides) que $p \mid a$. 
Luego $a = p \cdot k$, y sustituyendo tenemos $p^n \cdot k^n = p \cdot b^n \implies p^{n-1} \cdot k^n = b^n$.
Esto implica que $p \mid b^n \implies p \mid b$, lo cual es una contradicción, ya que $a$ y $b$ eran coprimos ($\gcd(a,b)=1$).

### ¿Por qué buscar un enfoque constructivo?
Aunque en lógica intuicionista deducir una contradicción a partir de una premisa es la definición misma de negación ($P \implies \bot$ significa $\neg P$), este enfoque clásico nos dice lo que la raíz **no es** (no es un racional), pero falla en decirnos lo que la raíz **es**. En el espíritu de las matemáticas constructivas y la Teoría de Conjuntos de Aczel (CZF), queremos *construir* el número irracional y luego demostrar que se distingue (está estrictamente separado) de cualquier número racional.

---

## 2. El Enfoque Constructivo: Sucesiones de Cauchy y Newton-Raphson

En lugar de limitarnos a negar la existencia de un racional, vamos a **construir la raíz n-ésima** como un número real, esto es, como una **clase de equivalencia de sucesiones de Cauchy** de números racionales.

Para encontrar una sucesión que converja a $\sqrt[n]{m}$, buscamos la raíz de la función $f(x) = x^n - m$. Su derivada es $f'(x) = n \cdot x^{n-1}$. 
Aplicando el método de Newton-Raphson ($x_{k+1} = x_k - \frac{f(x_k)}{f'(x_k)}$), obtenemos la iteración:

$$ x_{k+1} := x_k - \frac{x_k^n - m}{n x_k^{n-1}} = \frac{1}{n} \left( (n-1) x_k + \frac{m}{x_k^{n-1}} \right) $$

### 2.1. Definición de la Sucesión $\nu_{\text{NR}}$

Sea $m \in \mathbb{N}$ un número natural (que no es una potencia n-ésima perfecta). Definimos la sucesión racional iterativa $\nu_{\text{NR}} : \mathbb{N}_0 \to \mathbb{Q}_{> 0}$ como:

$$
\begin{cases} 
\nu_{\text{NR}}(0) = m & \text{(Semilla inicial, asegurando cota superior)} \\
\nu_{\text{NR}}(k+1) = \frac{1}{n} \left( (n-1) \nu_{\text{NR}}(k) + \frac{m}{\nu_{\text{NR}}(k)^{n-1}} \right)
\end{cases}
$$

### 2.2. Demostración de que $\nu_{\text{NR}}$ es de Cauchy

Para que esta sucesión represente un número real válido en nuestro sistema, necesitamos dotarla de una función de convergencia (módulo de Cauchy) explícita. Necesitamos probar que para nuestra métrica de distancia, las diferencias se reducen exponencialmente.

El error cuadrático en Newton-Raphson tiene convergencia cuadrática. Sabemos que:
$$ \nu_{\text{NR}}(k+1) - \sqrt[n]{m} \approx C \cdot (\nu_{\text{NR}}(k) - \sqrt[n]{m})^2 $$

Para formalizar esto en Lean sin recurrir a los reales (pues apenas los estamos construyendo), debemos probar la contracción directamente sobre los racionales. Demostraremos que la diferencia entre términos sucesivos se hace menor que $\frac{1}{2^k}$:
$$ |\nu_{\text{NR}}(k+1) - \nu_{\text{NR}}(k)| < \frac{M}{2^k} $$

Lo que nos permitirá definir una cota explícita $\nu(\varepsilon)$ constructiva y declarar formalmente a $\nu_{\text{NR}}$ como un tipo `CauchySeq`.

---

## 3. Demostración de la Irracionalidad (Apartness)

Una vez construida la sucesión `x = CauchySeq.mk (ν_NR, bound)`, definimos a $\sqrt[n]{m}$ como la clase de equivalencia de esta sucesión en $\mathbb{R}$.

Para demostrar de forma puramente constructiva que $\sqrt[n]{m}$ es irracional, probaremos que su distancia a cualquier número racional $q \in \mathbb{Q}$ es estrictamente mayor que cero (lo que constructivamente se conoce como relación de "apartness" $x \mathrel{\#} q$).

El teorema final tomará la forma:
**Teorema:** Para cualquier racional $q = \frac{a}{b}$, existe un error mínimo $\delta > 0$ tal que a partir de cierto punto $N$, todos los términos de nuestra sucesión distan de $q$ más que $\delta$:
$$ \forall q \in \mathbb{Q}, \exists \delta \in \mathbb{Q}_{>0}, \exists N \in \mathbb{N}_0, \forall k \ge N, \quad |\nu_{\text{NR}}(k) - q| > \delta $$

### 3.1. El Lema de Separación

El corazón de esta prueba recae en que si $m$ no es una potencia perfecta de exponente $n$ (por ejemplo, si $m$ es primo $p$), la expresión $|a^n - m \cdot b^n|$ es un entero no nulo.
Como $a, b, m \in \mathbb{Z}$, la diferencia mínima admisible es 1:
$$ |a^n - m \cdot b^n| \ge 1 $$

Esto fuerza a que la distancia entre cualquier estimación racional $q = \frac{a}{b}$ y la verdadera raíz esté rígidamente acotada por debajo por un valor dependiente del denominador $b$, demostrando constructivamente que ningún racional puede ser límite de nuestra sucesión $\nu_{\text{NR}}$.