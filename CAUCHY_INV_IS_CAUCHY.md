# Demostración: La sucesión inversa de una sucesión de Cauchy es de Cauchy

Sea la función (sucesión) $S$ (que sabemos que no es convergente a 0):

$$ S : \mathbb{N}_0 \to \mathbb{Q}_0 := n \mapsto S(n) $$

$S$ es de Cauchy si proporcionamos la función módulo de convergencia $\delta_S$:

$$ {\nu}_S : \mathbb{Q}_0 \to \mathbb{N}_0 $$

y la prueba $hC$ de que:

$$ \forall \varepsilon \in \mathbb{Q}_0, \varepsilon > 0, \forall n, m \in \mathbb{N}_0, n > \nu_S(\varepsilon), m > \nu_S(\varepsilon) \implies |S(n) - S(m)| < \varepsilon $$

Tenemos que $(S, \delta_S, hC)$ es una sucesión de Cauchy. Queremos demostrar que $S^{-1}$ es de Cauchy.

Para esto, llamaré $R$ a la sucesión:

$$ R : \mathbb{N}_0 \to \mathbb{Q}_0 := n \mapsto \begin{cases} \frac{1}{S(n)} & \text{si } S(n) \neq 0 \\ 0 & \text{si } S(n) = 0 \end{cases} $$

Se trata de ver que si $S$ no es convergente a 0, $R$ es de Cauchy.

Por comodidad llamaré $\nu_0 := \nu_S(\varepsilon)$.
Sean:
- $n := \nu_0 + a, \quad a \in \mathbb{N}_0, a > 0$
- $m := \nu_0 + b, \quad b \in \mathbb{N}_0, b > 0$

Evaluamos la distancia entre los términos de la sucesión inversa:

$$ \left| \frac{1}{S(n)} - \frac{1}{S(m)} \right| = \frac{|S(m) - S(n)|}{|S(n)| \cdot |S(m)|} < \frac{\varepsilon}{|S(n)| \cdot |S(m)|} $$

Pero sabemos que toda sucesión de Cauchy tiene una cota superior y una inferior, nos fijamos en la inferior que es la que nos va a servir:

$$ \forall c \in \mathbb{N}_0, |S(n_0 + c)| > B $$

Así:

$$ \frac{1}{|S(n)| \cdot |S(m)|} < \frac{1}{B^2} $$

y nos queda finalmente que:

$$ \left| \frac{1}{S(n)} - \frac{1}{S(m)} \right| < \frac{\varepsilon}{B^2} $$

La función delta a proporcionar de $R$ es:

$$ \nu_R(\varepsilon) := \nu_S\left(\frac{\varepsilon}{B^2}\right) \quad \text{para el mismo } \nu_0 $$

Solo nos falta sacar la cota superior $B$, que podría ser $|S(n_0)|/2^{\nu_0 + 1}$.

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

### 3. La función $\nu_R$ correcta
Sabiendo que $|S(n)| \ge C$ para $n \ge N$, tu razonamiento encaja perfectamente:
$$ \left| \frac{1}{S(n)} - \frac{1}{S(m)} \right| = \frac{|S(m) - S(n)|}{|S(n)| \cdot |S(m)|} \le \frac{|S(m) - S(n)|}{C^2} $$
Para que esto sea menor que $\varepsilon$, necesitamos que $|S(m) - S(n)| < \varepsilon \cdot C^2$.
Por tanto, la función $\nu_R$ para la inversa será:
$$ \nu_R(\varepsilon) := \max\left(N, \nu_S(\varepsilon \cdot C^2)\right) $$
(Tomamos el máximo con $N$ para asegurarnos de que la cota inferior $C$ ya está en efecto).

### Resumen de nuestra implementación en Lean (Grupo 2 Completado)
En `CauchySeqAlgebra.lean`, este esquema se ha traducido exactamente con la siguiente estructura magistral:

1. **Alejada de cero (`ApartZero f`)**: Nos garantiza que existe un $N$ y un $k$ tal que para todo $n \ge N$, $|f(n)| \ge 1/2^k$.
2. **El desfase $K$**: En Lean, nuestra convergencia está rígidamente fijada a $1/2^{\min(n, m)}$. Para lograr que la inversa converja a esta misma tasa, no podemos simplemente elegir un $\nu_S$ arbitrario. Lo que hacemos es **desfasar** la sucesión definiendo el inverso como $1/f(n + K)$.
3. **El valor mágico de $K$**: Definimos $K = N + 2k$. Esto cumple dos cosas vitales:
   - $K \ge N$, por lo que $n + K \ge N$ y sabemos que $|f(n+K)| \ge 1/2^k$ (nuestro denominador nunca explota).
   - El numerador de la distancia es $|f(n+K) - f(m+K)| \le 1/2^{\min(n+K, m+K)} = 1/2^{\min(n, m) + N + 2k} = 1/2^{\min(n, m)} \cdot 1/2^N \cdot 1/2^{2k}$.
4. **La magia de la cancelación**: Al dividir la distancia $|f(m+K) - f(n+K)|$ por $|f(n+K)| \cdot |f(m+K)|$, el denominador aporta un factor que es, como mucho, el inverso de $(1/2^k)^2 = 1/2^{2k}$, es decir, aporta un factor de crecimiento de $2^{2k}$.
   Pero en el numerador tenemos $1/2^{2k}$ libre gracias al desfase $K$ (ya que $K \ge 2k$). ¡Ambos se cancelan perfectamente!
   Y nos queda que la distancia es $\le 1/2^{\min(n, m)} \cdot 1/2^N \le 1/2^{\min(n, m)}$.

¡Esta es la prueba matemática precisa y limpia que ha quedado formalizada en Lean para cerrar la validez de la sucesión inversa de Cauchy!
