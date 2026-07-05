

Supongamos que $p \in \mathbb{N}_2$ y $\forall q \in \mathbb{N}_2, p \neq q \implies q \nmid p$.

Supongamos que existe un $r \in \mathbb{Q}_{\ge 0}$ tal que $r^2 = p$.
Podemos escribir a $r = \frac{a}{b}$ con $a, b \in \mathbb{N}_2$ y $a \land b = 1$.

Tenemos que:
$$ \left(\frac{a}{b}\right)^2 = p \implies \frac{a^2}{b^2} = p \implies a^2 = p b^2 $$

Por lo tanto: $b^2 \mid a^2$ que conlleva que $b \nmid a$, lo cual es una contradicción ya que $a \land b = 1$ implica que $b \nmid a$.

Supongamos ahora que suponemos que no es la raíz cuadrada si no la n-ésima raíz:

$$ \left(\frac{a}{b}\right)^n = p \implies \frac{a^n}{b^n} = p \implies a^n = p \cdot b^n $$

Por lo tanto: $b^n \mid a^n$ que conlleva que $b \nmid a$, lo cual es una contradicción ya que $a \land b = 1$ implica que $b \nmid a$.

Para lo anterior solo tenemos que suponer $n \in \mathbb{N}_2$ y $p \in \mathbb{P}$.

El único problema del anterior razonamiento es que es de tipo existencial y en este proyecto queremos una prueba que no use $\neg \neg P \implies P$ ni $P \lor \neg P$.

---

Vamos a desarrollar un algoritmo que nos de una sucesión de racionales que tienda a $\sqrt[n]{m}$, aunque por ahora no hemos demostrado que exista semejante cosa. La función inversa a esto sí que la tenemos en $\mathbb{N}$, $f_n(m) := m^n$. $f_n^\prime (m) = n \cdot m^{n-1}$, dónde $n \gt 1$.

El algoritmo que usaremos es (aparte de tomar una semilla inicial), el siguiente (Newton-Raphson):

$$ x_{k+1} := \frac{1}{n} \left( (n-1) x_k + \frac{m}{x_k^{n-1}} \right) $$

¿Cómo podríamos interpretarlo en términos de sucesiones? Tenemos: 

$$\nu_{\text{NR}} : \mathbb{N}_0 \to \mathbb{Q}_0 := k \mapsto \frac{1}{k} \left( (k-1) \nu_{\text{NR}}_k + \frac{m}{\nu_{\text{NR}}_k^{n-1}} \right)$$

y nos falta aún hallar el término $\nu_{\text{NR}}(0)$. Podríamos primero tomar una cota superior, $\nu_{\text{NR}}(0) := m$ por ejemplo. Con $\nu_{\text{NR}}(0) := m$ tenemos por ejemplo:

$$|\nu_{\text{NR}}(k) - \sqrt[n]{m}| \le |\nu_{\text{NR}}(k-1) - \sqrt[n]{m}|^n$$

Ahora nos falta dar una función $\nu : \mathbb{Q}_{>0} \to \mathbb{N}_0$ tal que: $\forall \varepsilon \in \mathbb{Q}_{>0}, \forall k,l \in \mathbb{N}_0, k l > \nu(\varepsilon) , l > \nu(\varepsilon) \implies |\nu_{\text{NR}}(k) - \nu_{\text{NR}}(l)| < \varepsilon$

---