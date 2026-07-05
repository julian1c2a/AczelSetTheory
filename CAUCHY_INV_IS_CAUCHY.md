# Demostración: El inverso de una sucesión de Cauchy es de Cauchy

Sea la función (sucesión) $S$ (que sabemos que no es convergente a 0):

$$ S : \mathbb{N}_0 \to \mathbb{Q}_0 := n \mapsto S(n) $$

$S$ es de Cauchy si proporcionamos la función módulo de convergencia $\delta_S$:

$$ \delta_S : \mathbb{Q}_0 \to \mathbb{N}_0 $$

y la prueba $hC$ de que:

$$ \forall \varepsilon \in \mathbb{Q}_0, \varepsilon > 0, \forall n, m \in \mathbb{N}_0, n > \delta_S(\varepsilon), m > \delta_S(\varepsilon) \implies |S(n) - S(m)| < \varepsilon $$

Tenemos que $(S, \delta_S, hC)$ es una sucesión de Cauchy. Queremos demostrar que $S^{-1}$ es de Cauchy.

Para esto, llamaré $R$ a la sucesión:

$$ R : \mathbb{N}_0 \to \mathbb{Q}_0 := n \mapsto \begin{cases} \frac{1}{S(n)} & \text{si } S(n) \neq 0 \\ 0 & \text{si } S(n) = 0 \end{cases} $$

Se trata de ver que si $S$ no es convergente a 0, $R$ es de Cauchy.

Por comodidad llamaré $n_0 := \delta_S(\varepsilon)$.
Sean:
- $n := n_0 + a, \quad a \in \mathbb{N}_0, a > 0$
- $m := n_0 + b, \quad b \in \mathbb{N}_0, b > 0$

Evaluamos la distancia entre los términos de la sucesión inversa:

$$ \left| \frac{1}{S(n)} - \frac{1}{S(m)} \right| = \frac{|S(m) - S(n)|}{|S(n)| \cdot |S(m)|} < \frac{\varepsilon}{|S(n)| \cdot |S(m)|} $$

Pero sabemos que toda sucesión de Cauchy tiene una cota superior y una inferior:

$$ \forall c \in \mathbb{N}_0, |S(n_0 + c)| < B $$

Así:

$$ \frac{1}{|S(n)| \cdot |S(m)|} < \frac{1}{B^2} $$

y nos queda finalmente que:

$$ \left| \frac{1}{S(n)} - \frac{1}{S(m)} \right| < \frac{\varepsilon}{B^2} $$

La función delta a proporcionar de $R$ es:

$$ \delta_R(\varepsilon) := \delta_S\left(\frac{\varepsilon}{B^2}\right) \quad \text{para el mismo } n_0 $$

Solo nos falta sacar la cota superior $B$, que podría ser $|S(n_0)| + \varepsilon$.

---

## Comentarios y Correcciones (por Antigravity)

¡El planteamiento estructural es excelente y va por el camino exacto! Sin embargo, hay un **detalle crucial en la acotación de la fracción** que debemos corregir para que la demostración sea matemáticamente válida:

### 1. Necesitamos una cota INFERIOR, no superior
En tu esquema, dices que $|S(n)| < B$, lo cual es una **cota superior**. Sin embargo, fíjate en la fracción:
$$ \frac{1}{|S(n)| \cdot |S(m)|} $$
Para hacer que una fracción sea **más pequeña** (es decir, acotarla por arriba, que es lo que queremos con $< \frac{\varepsilon}{B^2}$), necesitamos hacer que su **denominador sea lo más pequeño posible**. 
Si usamos una cota superior $|S(n)| < B$, entonces $\frac{1}{|S(n)|} > \frac{1}{B}$, ¡la desigualdad se invierte!

Lo que realmente necesitamos es una **cota inferior** $C > 0$ tal que:
$$ |S(n)| > C \quad \text{para todo } n \text{ suficientemente grande.} $$
Entonces sí podremos afirmar que:
$$ \frac{1}{|S(n)| \cdot |S(m)|} < \frac{1}{C^2} $$

### 2. ¿De dónde sacamos la cota inferior $C$?
Aquí es donde entra en juego la hipótesis vital: **$S$ no converge a 0** (en Lean esto lo llamaremos `CauchySeq.Pos` o que está alejada de cero). 
Como $S$ es de Cauchy y no converge a $0$, sabemos (o podemos demostrar) que existe un momento $N$ y una constante positiva $C$ (por ejemplo, $C = \frac{1}{2^k}$) tal que para todo $n \ge N$:
$$ |S(n)| \ge C $$
Esa constante $C$ es la que asegura que los términos de $S$ nunca se acercan peligrosamente a $0$, lo que haría que $\frac{1}{S(n)}$ explotase a infinito.

### 3. La función $\delta_R$ correcta
Sabiendo que $|S(n)| \ge C$ para $n \ge N$, tu razonamiento encaja perfectamente:
$$ \left| \frac{1}{S(n)} - \frac{1}{S(m)} \right| = \frac{|S(m) - S(n)|}{|S(n)| \cdot |S(m)|} \le \frac{|S(m) - S(n)|}{C^2} $$
Para que esto sea menor que $\varepsilon$, necesitamos que $|S(m) - S(n)| < \varepsilon \cdot C^2$.
Por tanto, la función $\delta$ para la inversa será:
$$ \delta_R(\varepsilon) := \max\left(N, \delta_S(\varepsilon \cdot C^2)\right) $$
(Tomamos el máximo con $N$ para asegurarnos de que la cota inferior $C$ ya está en efecto).

### Resumen para nuestra implementación en Lean
En `CauchySeqAlgebra.lean`, este esquema se traducirá así:
1. Definiremos formalmente qué significa que $S$ no converja a 0 (por ejemplo, usando nuestra definición `CauchySeq.Pos (absVal S)`).
2. De esa positividad estricta extraeremos el índice $N$ y la cota $C = \frac{1}{2^k}$.
3. Usaremos $\delta_S(\varepsilon \cdot C^2)$ combinada con $N$ para definir el nuevo multiplicador del inverso, tal como has deducido magistralmente.
