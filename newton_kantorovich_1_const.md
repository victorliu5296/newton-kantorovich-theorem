**Theorem 5 (Newton–Kantorovich Theorem "with Only One Constant").**
Consider two Banach spaces $X$ and $Y$, an open subset $\Omega$ of $X$, a point $x_0 \in \Omega$, and a $C^1$ mapping $f: \Omega \to Y$. Assume $f'(x_0): X \to Y$ is bijective, implying the existence of $f'(x_0)^{-1}: Y \to X$.

Let $r > 0$ satisfy:
- $\overline{B(x_0; r)} \subset \Omega$,
- $\| f'(x_0)^{-1} f(x_0) \|_X \leq \frac{r}{2}$,
- $\| f'(x_0)^{-1} (f'(u) - f'(v)) \|_{\mathcal{L}(X)} \leq \frac{1}{r} \| u - v \|_X$ for all $u, v \in B(x_0; r)$.

Then, for each $x \in B(x_0; r)$, $f'(x)$ is bijective with $f'(x)^{-1} \in \mathcal{L}(Y; X)$ (vector space formed by all continuous linear operators). The sequence $(x_k)_{k=0}^{\infty}$, defined by $x_{k+1} = x_k - f'(x_k)^{-1} f(x_k)$, remains within $B(x_0; r)$ and converges to a zero $a$, which is the unique zero of $f$ in $\overline{B(x_0; r)}$, with $\| x_k - a \| \leq \frac{r}{2^k}$ for all $k \geq 0$.

---

Let $X$ be a Banach space, let $Y$ be a normed vector space, and let $A \in \mathcal{L}(X;Y)$ be one-to-one and onto, with a continuous inverse $A^{-1}$, i.e. $A^{-1} \in \mathcal{L}(Y;X)$. Then, any $B \in \mathcal{L}(X;Y)$ such that 
$$\|A^{-1}(B - A)\|_{\mathcal{L}(X)} < 1$$ 
is also one-to-one and onto, with a continuous inverse $B^{-1} \in \mathcal{L}(Y;X)$ that satisfies 
$$\|B^{-1}\|_{\mathcal{L}(Y;X)} \leq \frac{\|A^{-1}\|_{\mathcal{L}(Y;X)}}{1 - \|A^{-1}(B - A)\|_{\mathcal{L}(X)}}.$$

---

$$\textbf{Theorem 1 (Mean Value Theorem for Functions of Class $C^1$ with Values in a Banach Space).}$$ Let $\Omega$ be an open subset in a normed vector space $X$, let $Y$ be a Banach space, and let $f \in C^1(\Omega; Y)$. Then, given any closed segment $[a, b] \subset \Omega$,

$$
f(b) - f(a) = \int_0^1 f'((1-\theta)a + \theta b)(b-a) \, d\theta.
$$

---

**Theorem 5 (Newton–Kantorovich Theorem “with Only One Constant”).**

Let there be given two Banach spaces $X$ and $Y$, an open subset $\Omega$ of $X$, a point $x_0 \in \Omega$, and a mapping $f \in C^1(\Omega; Y)$ such that $f'(x_0) \in \mathcal{L}(X; Y)$ is one-to-one and onto (hence, $f'(x_0)^{-1} \in \mathcal{L}(Y; X)$).

Assume that there exists a constant $r > 0$ such that

$$
\overline{B(x_0; r)} \subset \Omega,
$$

$$
\| f'(x_0)^{-1} f(x_0) \|_X \leq \frac{r}{2},
$$

$$
\| f'(x_0)^{-1} (f'(u) - f'(v)) \|_{\mathcal{L}(X)} \leq \frac{1}{r} \| u - v \|_X \text{ for all } u, v \in B(x_0; r).
$$

Then, $f'(x) \in \mathcal{L}(X; Y)$ is one-to-one and onto and $f'(x)^{-1} \in \mathcal{L}(Y; X)$ at each $x \in B(x_0; r)$.

The sequence $(x_k)_{k=0}^{\infty}$ defined by

$$
x_{k+1} = x_k - (f'(x_k))^{-1} f(x_k), \quad k \geq 0,
$$

is such that $x_k \in B(x_0; r)$ for all $k \geq 0$ and converges to a zero $a \in \overline{B(x_0; r)}$ of $f$.

Besides, for each $k \geq 0$,

$$
\| x_k - a \| \leq \frac{r}{2^k},
$$

and the point $a \in \overline{B(x_0; r)}$ is the only zero of $f$ in $\overline{B(x_0; r)}$.


**Proof.** Like in the proofs of Theorems 3 and 4, we introduce the auxiliary function $h \in C^1(\Omega; X)$ defined by $h(x) := f'(x_0)^{-1} f(x), x \in \Omega$, so that $h'(x) = f'(x_0)^{-1} f'(x) \in \mathcal{L}(X; X), x \in \Omega$, and $h'(x_0) = \text{id}_X$. In terms of the function $h$, the assumptions of Theorem 5 therefore become

$$
\| h(x_0) \| \leq \frac{r}{2} \text{ and } \| h'(u) - h'(v) \| \leq \frac{1}{r} \| u - v \| \text{ for all } u, v \in B(x_0; r).
$$

(i) The following estimates hold:

$$
\| h'(x)^{-1} \| \leq \frac{1}{1 - \| x - x_0 \| / r} \text{ for all } x \in B(x_0; r),
$$

$$
\| h(b) - h(a) - h'(a)(b - a) \| \leq \frac{1}{2r} \| b - a \|^2 \text{ for all } b, a \in \overline{B(x_0; r)}.
$$

By assumption,

$$
\| h'(x) - h'(x_0) \| = \| h'(x) - \text{id}_X \|_{\mathcal{L}(X)} \leq \frac{1}{r} \| x - x_0 \| < 1 \text{ at each } x \in B(x_0; r).
$$

Therefore, at each $x \in B(x_0; r)$, $h'(x)$ is one-to-one and onto, and (Sec. 2.1)

$$
\| h'(x)^{-1} \| \leq \frac{\| h'(x_0)^{-1} \|}{1 - \| h'(x_0)^{-1} (h'(x) - h'(x_0)) \|}
$$

$$
= \frac{1}{1 - \| h'(x) - h'(x_0) \|} \leq \frac{1}{1 - \| x - x_0 \| / r}.
$$

Hence, the first estimate holds.

Using the mean value theorem (Theorem 1), we next have

$$
\| h(b) - h(a) - h'(a)(b - a) \| = \left\| \int_0^1 (h'(a + t(b - a)) - h'(a))(b - a) dt \right\|
$$

$$
\leq \left( \int_0^1 \| h'(a + t(b - a)) - h'(a) \| dt \right) \| b - a \|
$$

$$
\leq \left(\int_0^1 \frac{1}{r} \| (a + t(b - a) - a) \| dt \right) \| b - a \|
$$

$$
\leq \frac{1}{r} \left( \int_0^1 t dt \right) \| b - a \|^2
$$

$$
= \frac{1}{2r} \| b - a \|^2 \text{ for all } b, a \in B(x_0; r).
$$

But the above inequality holds as well for all $b$, $a \in \overline{B(x_0; r)}$ since the functions appearing on each side are continuous. Hence, the second estimate holds.

(ii) The Newton iterates $x_k, k \geq 0$, for the function $h$, which are the same as those for the function $f$, belong to the open ball $B(x_0; r)$ (hence, they are well defined) and they satisfy the following estimates for all $k \geq 1$:

$$
\| x_k - x_{k-1} \| \leq \frac{r}{2^k}, \quad \| x_k - x_0 \| \leq r \left( 1 - \frac{1}{2^k} \right),
$$

$$
\| h'(x_k)^{-1} \| \leq 2^k, \quad \| h(x_k) \| \leq \frac{r}{2^{2k+1}}.
$$

First, let us check that the above estimates hold for $k = 1$. Clearly, the point $u = x_0 - h'(x_0)^{-1} h(x_0) = x_0 - h(x_0)$ is well defined since $h'(x_0)$ is invertible.

Besides,

$$
\| u - x_0 \| = \| h(x_0) \| \leq \frac{r}{2},
$$

and, by (i),

$$
\| (h'(u))^{-1} \| \leq \frac{1}{1 - \| u - x_0 \| / r} \leq 2.
$$

By definition of $u$, and by (i) again,

$$
\| h(u) \| = \| h(u) - h(x_0) - h'(x_0)(u - x_0) \| \leq \frac{1}{2r} \| u - x_0 \|^2 = \frac{r}{2^3}.
$$

So, assume that the estimates hold for $k = 1, \ldots, n$ for some integer $n \geq 1$. The point $x_{n+1} = x_n - h'(x_n)^{-1} h(x_n)$ is thus well defined since $h'(x_n)$ is invertible.

Moreover, by the induction hypothesis and by the estimates of (i) (for the third and fourth estimates),

$$
\| x_{n+1} - x_n \| \leq \| h'(x_n)^{-1} \| \| h(x_n) \| \leq \frac{r}{2^{n+1}},
$$

$$
\| x_{n+1} - x_0 \| \leq \| x_n - x_0 \| + \| x_{n+1} - x_n \| \leq r \left( 1 - \frac{1}{2^n} \right) + \frac{r}{2^{n+1}} = r \left( 1 - \frac{1}{2^{n+1}} \right),
$$

$$
\| h'(x_{n+1})^{-1} \| \leq \frac{1}{1 - \| x_{n+1} - x_0 \| / r} \leq 2^{n+1},
$$

$$
\| h(x_{n+1}) \| = \| h(x_{n+1}) - h(x_n) - h'(x_n)(x_{n+1} - x_n) \| \leq \frac{1}{2r} \| x_{n+1} - x_n \|^2 \leq \frac{r}{2^{2(n+1)+1}}.
$$

Hence, the estimates also hold for $k = n + 1$.

(iii) The Newton iterates $x_k, k \geq 0$, converge to a zero $a$ of $h$, hence of $f$, which belongs to the closed ball $\overline{B(x_0; r)}$. Besides,

$$
\| x_k - a \| \leq \frac{r}{2^k} \text{ for all } k \geq 0.
$$

The estimates $\| x_k - x_{k-1} \| \leq r / 2^k, k \geq 1$, established in (ii) clearly imply that $(x_k)_{k=1}^{\infty}$ is a Cauchy sequence. Since $x_k \in B(x_0; r) \subset \overline{B(x_0; r)}$ and $\overline{B(x_0; r)}$ is a complete metric space (as a closed subset of the Banach space $X$), there exists $a \in \overline{B(x_0; r)}$ such that

$$
a = \lim_{k \to \infty} x_k.
$$

Since $\| h(x_k) \| \leq r / 2^{2k+1}, k \geq 1$, by (ii), and $h$ is a continuous function,

$$
h(a) = \lim_{k \to \infty} h(x_k) = 0.
$$

Hence, the point $a$ is a zero of $f$.

Given integers $k \geq 1$ and $\ell \geq 1$, we have, again by (ii),

$$
\| x_k - x_{k + \ell} \| \leq \sum_{j = k}^{k + \ell - 1} \| x_{j+1} - x_j \| \leq \sum_{j = k}^{\infty} \frac{r}{2^{j+1}} = \frac{r}{2^k},
$$

so that, for each $k \geq 1$,

$$
\| x_k - a \| = \lim_{\ell \to \infty} \| x_k - x_{k + \ell} \| \leq \frac{r}{2^k}.
$$

(iv) Uniqueness of a zero of $h$, hence of $f$, in the closed ball $\overline{B(x_0; r)}$.

We first show that, if $b \in \overline{B(x_0; r)}$ is such that $h(b) = 0$, then

$$
\| x_k - b \| \leq \frac{r}{2^k} \text{ for all } k \geq 0.
$$

Clearly, this is true if $k = 0$; so, assume that this inequality holds for $k = 1, \ldots, n$, for some integer $n \geq 0$. Noting that we can write

$$
x_{n+1} - b = x_n - h'(x_n)^{-1} h(x_n) - b = h'(x_n)^{-1} (h(b) - h(x_n) - h'(x_n)(b - x_n)),
$$

we infer from (i) and (ii) and from the induction hypothesis that

$$
\| x_{n+1} - b \| \leq \| h'(x_n)^{-1} \| \frac{1}{2r} \| b - x_n \|^2 \leq \frac{r}{2^{n+1}}.
$$

Hence, the inequality $\| x_k - b \| \leq r / 2^k$ holds for all $k \geq 1$. Consequently,

$$
\lim_{n \to \infty} \| x_k - b \| = \| a - b \| = 0,
$$

which shows that $b = a$. This completes the proof. $\quad \square$
