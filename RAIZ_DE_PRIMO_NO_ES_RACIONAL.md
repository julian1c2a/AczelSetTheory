

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