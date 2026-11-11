# DWeakContFun

A Lean 4 formalization of the moving-tent counterexample showing that a sequence in
`C([0,1], ℝ)` can converge `d`-weakly to zero while its sup norms are unbounded.

The formalization follows the counterexample argument of Gutiérrez and Nevanlinna:
choose pairwise disjoint closed intervals in `[0,1]`, put a continuous nonnegative
spike on each interval with maximum `n`, and prove that every metric functional is
negative on at most one spike. The latter implies eventual nonnegativity and hence
nonnegative liminf. The published counterexample uses the same two key ingredients:
pairwise disjoint intervals and spikes with maximum value `n`. See Theorem 1.3 and
its proof in the authors' September 2026 preprint, *A Weak Topology on Metric Spaces*.

> **Note on this README:** the mathematical statements below are written in
> KaTeX-compatible Markdown. GitHub, GitLab, and many Markdown renderers support
> the displayed `$$...$$` form; the Lean source itself remains independent of the
> renderer.

## 1. Mathematical setting

Let

$$
X=C([0,1],\mathbb R)
$$

with the sup norm and its induced metric

$$
d(f,g)=\lVert f-g\rVert_\infty.
$$

Fix the base point

$$
o=0.
$$

For a point $w\in X$, the corresponding internal metric functional is

$$
h_w(f)=d(f,w)-d(0,w)
      =\lVert f-w\rVert_\infty-\lVert w\rVert_\infty.
$$

The project formalizes a metric functional as a pointwise limit of such internal
metric functionals along a directed net.

The central conclusion is

$$
f_n\xrightarrow{d\text{-weak}}0
\qquad\text{while}\qquad
\lVert f_n\rVert_\infty\ge n.
$$

Thus the sequence is `d`-weakly convergent but not norm bounded.

---

## 2. Project structure

| File | Mathematical role |
|---|---|
| `NormSupport.lean` | Norm attainment and support lemmas for internal metric functionals |
| `MetricFunctional.lean` | Formal definition of metric functionals and finite-point approximation |
| `DWeak.lean` | Abstract `d`-weak convergence argument |
| `Tent.lean` | Explicit intervals, tent functions, spikes, support and norm estimates |
| `DWeakContFun.lean` | Final counterexample theorem |
| `Main.lean` | Lightweight entry point |

The dependency chain is

$$
\texttt{NormSupport}
\longrightarrow
\texttt{MetricFunctional}
\longrightarrow
\texttt{DWeak}
\longrightarrow
\texttt{Tent}
\longrightarrow
\texttt{DWeakContFun}.
$$

---

# 3. Norm attainment and support: `NormSupport.lean`

## `norm_attains_at_point`

**Mathematics.** If $g\in C(K,\mathbb R)$ and $K$ is compact and nonempty, then the
continuous function $x\mapsto |g(x)|$ attains its maximum. Hence there exists
$x\in K$ such that

$$
|g(x)|=\lVert g\rVert.
$$

This is the point at which an internal metric functional will be tested.

## `internal_negative_imp_mem_support`

Suppose $x$ is a norm-attaining point for $g$:

$$
|g(x)|=\lVert g\rVert.
$$

If the internal metric functional is negative at $f$,

$$
\lVert f-g\rVert-\lVert g\rVert<0,
$$

then $f(x)\ne0$.

Indeed, if $f(x)=0$, then

$$
\lVert g\rVert=|g(x)|=|(f-g)(x)|
\le \lVert f-g\rVert,
$$

contradicting the strict negativity. Therefore

$$
x\in\operatorname{supp}(f).
$$

## `internal_negative_at_most_one`

Assume the supports of $f_m$ and $f_n$ are disjoint whenever $m\ne n$. A fixed
internal functional can be negative on at most one sequence term.

If it were negative on both $f_m$ and $f_n$, choose a norm-attaining point $x$ of
the function $g$ generating the internal functional. The previous lemma puts $x$
in both supports, contradicting disjointness.

## `disjoint_supports_of_subset`

This is the elementary set-theoretic transfer lemma:

$$
\operatorname{supp}(f_n)\subseteq I_n
$$

and pairwise disjointness of the $I_n$ imply pairwise disjointness of the supports.

---

# 4. Metric functionals: `MetricFunctional.lean`

## `MetricFunctionalWitness`

A witness consists of a directed nonempty index type $\iota$, a net

$$
w:\iota\to X,
$$

and the pointwise convergence statement

$$
d(x,w_i)-d(o,w_i)\longrightarrow h(x)
$$

for every $x\in X$.

Thus `IsMetricFunctional o h` says that $h$ is the pointwise limit of internal
metric functionals based at $o$.

This is the net formulation of the pointwise closure description of metric
functionals used in the mathematical argument.

## `metric_functional_basepoint`

Every internal metric functional vanishes at its base point:

$$
d(o,w)-d(o,w)=0.
$$

Pointwise convergence therefore gives

$$
h(o)=0.
$$

This is used at the final `dWeaklyConverges_of_disjoint_supports` step.

## `metric_functional_two_point_approx`

Suppose $h$ is represented by a directed net of internal metric functionals. For
any two points $x_1,x_2$ and any $\varepsilon>0$, convergence at each point gives
eventual inequalities

$$
|h_{w_i}(x_1)-h(x_1)|<\varepsilon,
\qquad
|h_{w_i}(x_2)-h(x_2)|<\varepsilon.
$$

Directedness supplies a single index at which both inequalities hold. This is the
finite-point approximation principle needed to pass the internal “negative at most
once” property to arbitrary metric functionals.

---

# 5. The abstract `d`-weak argument: `DWeak.lean`

## `metric_functional_negative_at_most_one`

Let $h$ be an arbitrary metric functional. Suppose, for contradiction, that

$$
h(f_m)<0,\qquad h(f_n)<0,\qquad m\ne n.
$$

Choose

$$
\varepsilon
=\frac12\min\{-h(f_m),-h(f_n)\}>0.
$$

The two-point approximation lemma gives one internal functional $h_{w_i}$ close
enough to $h$ at both $f_m$ and $f_n$. Consequently,

$$
h_{w_i}(f_m)<0,
\qquad
h_{w_i}(f_n)<0,
$$

contradicting the internal negative-at-most-one lemma. Hence

$$
\#\{n:h(f_n)<0\}\le1.
$$

This is the central abstract lemma.

## `eventually_nonneg_of_negative_at_most_one`

A real sequence which is negative at most once is eventually nonnegative. If the
unique possible negative term occurs at index $m$, then every $n\ge m+1$ is
nonnegative.

## `liminf_nonneg_of_eventually_nonneg`

If $a_n\ge0$ eventually, then

$$
\liminf_{n\to\infty}a_n\ge0.
$$

The Lean proof unfolds `Filter.liminf` in terms of the supremum of eventual lower
bounds and explicitly handles the bounded-above and unbounded-above cases.

## `metric_functional_eventually_nonneg`

Combining the previous two lemmas with
`metric_functional_negative_at_most_one` gives

$$
\exists N\;\forall n\ge N,\quad h(f_n)\ge0.
$$

## `metric_functional_liminf_nonneg`

Consequently, for every metric functional $h$,

$$
0\le\liminf_{n\to\infty}h(f_n).
$$

## `DWeaklyConverges`

The project specializes the notion of `d`-weak convergence to sequences:

$$
x_n\xrightarrow{d\text{-weak}}z
$$

means that for every metric functional $h$ based at $o$,

$$
h(z)\le\liminf_{n\to\infty}h(x_n).
$$

The underlying paper states the notion for nets; the counterexample here is a
sequence, so `DWeaklyConverges` uses `ℕ` as its index type.

## `dWeaklyConverges_of_disjoint_supports`

For a sequence with pairwise disjoint supports, every metric functional satisfies

$$
0=h(0)\le\liminf_{n\to\infty}h(f_n).
$$

Therefore the sequence converges `d`-weakly to zero.

---

# 6. The explicit tent construction: `Tent.lean`

## `continuous_tent`

For real numbers $a\le b$, define

$$
T_{a,b}(x)=\max\{0,\min(x-a,b-x)\}.
$$

This is continuous because it is obtained from continuous affine functions using
`min` and `max`.

## `tent`

`tent a b hab` packages $T_{a,b}$ as a continuous map

$$
[0,1]\to\mathbb R.
$$

## `tent_apply`

This is the evaluation formula for the packaged continuous map.

## `tent_nonneg`

By construction,

$$
T_{a,b}(x)\ge0.
$$

## `unbounded_of_norm_ge`

If

$$
 n\le\lVert f_n\rVert
$$

for every $n$, then the norms cannot be bounded above by a fixed real constant.

## `tent_eq_zero_of_not_mem_Icc`

If $x\notin[a,b]$, then at least one of $x-a$ and $b-x$ is nonpositive, so

$$
T_{a,b}(x)=0.
$$

## `tent_support_subset`

Hence

$$
\operatorname{supp}(T_{a,b})
\subseteq
[a,b]
$$

after pulling the interval back to the subtype $[0,1]$.

---

# 7. Pairwise-disjoint intervals

Define

$$
a_n=\frac1{2n+2},
\qquad
b_n=\frac1{2n+1},
\qquad
I_n=[a_n,b_n].
$$

## `tentLeft_le_tentRight`

Since $2n+1<2n+2$ and both denominators are positive,

$$
\frac1{2n+2}\le\frac1{2n+1}.
$$

Thus $I_n$ is a genuine interval.

## `tentInterval_subset_Icc`

Every endpoint lies in $[0,1]$, hence

$$
I_n\subseteq[0,1].
$$

## `tentRight_lt_tentLeft_of_lt`

If $m<n$, then

$$
2m+2<2n+1,
$$

so reciprocal reversal gives

$$
\frac1{2n+1}<\frac1{2m+2},
$$

i.e.

$$
b_n<a_m.
$$

## `tentInterval_disjoint_of_lt`

The strict separation

$$
b_n<a_m
$$

implies

$$
I_n\cap I_m=\varnothing
$$

when $m<n$.

## `tentInterval_disjoint`

By considering either $m<n$ or $n<m$, the intervals are pairwise disjoint:

$$
m\ne n\implies I_m\cap I_n=\varnothing.
$$

---

# 8. Scaling the tents

Define the midpoint

$$
c_n=\frac{a_n+b_n}{2}.
$$

## `tentMid_mem_Icc`

Because $c_n$ lies between $a_n$ and $b_n$, and $I_n\subseteq[0,1]$,

$$
c_n\in[0,1].
$$

## `tent_at_mid`

At the midpoint,

$$
T_{a_n,b_n}(c_n)
=\frac{b_n-a_n}{2}.
$$

Since

$$
b_n-a_n
=\frac1{2n+1}-\frac1{2n+2}
=\frac1{(2n+1)(2n+2)},
$$

we get

$$
T_{a_n,b_n}(c_n)
=\frac1{2(2n+1)(2n+2)}.
$$

## `spike`

The nth spike is the scaled tent

$$
 f_n
=
2n(2n+1)(2n+2)\,T_{a_n,b_n}.
$$

The factor is chosen precisely to make the midpoint value equal to $n$.

## `spike_at_mid`

Combining the scaling with the previous midpoint formula gives

$$
 f_n(c_n)=n.
$$

## `spike_norm_ge`

Since the sup norm dominates the absolute value at every point,

$$
 n=|f_n(c_n)|\le\lVert f_n\rVert_\infty.
$$

Thus the sequence is norm-unbounded.

---

# 9. Supports of the spikes

The support is naturally a subset of the subtype `[0,1]`, so the project defines

$$
\widetilde I_n
=\{x\in[0,1]:x\in I_n\}.
$$

This is `spikeInterval` in Lean.

## `spike_support_subset`

Multiplying a tent by a scalar cannot create nonzero values outside the original
tent support. Therefore

$$
\operatorname{supp}(f_n)\subseteq\widetilde I_n.
$$

## `spikeInterval_disjoint`

Disjointness of the real intervals $I_n$ transfers to their pullbacks
$\widetilde I_n$ inside `[0,1]`.

## `spike_disjoint_supports`

By support containment and the ambient disjointness lemma,

$$
 m\ne n
\implies
\operatorname{supp}(f_m)\cap\operatorname{supp}(f_n)=\varnothing.
$$

This is exactly the hypothesis required by the abstract argument in `DWeak.lean`.

---

# 10. Final theorem

`DWeakContFun.lean` proves

```lean
 theorem spike_counterexample :
     DWeaklyConverges
         (0 : C(Set.Icc (0 : ℝ) 1, ℝ))
         spike
         0 ∧
       ¬ ∃ C : ℝ, ∀ n, ‖spike n‖ ≤ C
```

Mathematically this says

$$
 f_n\xrightarrow{d\text{-weak}}0
$$

and simultaneously

$$
\sup_n\lVert f_n\rVert_\infty=+\infty.
$$

The first conjunct follows from pairwise disjoint supports and the abstract
metric-functional argument. The second follows from

$$
\lVert f_n\rVert_\infty\ge n.
$$

This is the formalized counterexample to the boundedness conjecture discussed by
the authors. Their September 2026 preprint explicitly states that the conjecture
is false and gives the same `C[0,1]` construction with pairwise disjoint intervals
and spikes of maximum value `n`.

---

# 11. Soundness review

The source was reviewed lemma-by-lemma with the following conclusions.

### Mathematically sound components

1. **Norm attainment:** the compactness argument correctly produces a norm-attaining
   point.
2. **Internal negativity:** the contradiction at a norm-attaining point is valid.
3. **At most one negative spike:** disjoint supports give the required contradiction.
4. **Passage to arbitrary metric functionals:** simultaneous approximation at two
   points correctly uses directedness of the net.
5. **Eventual nonnegativity:** “negative at most once” implies eventual nonnegativity.
6. **Liminf:** eventual nonnegativity implies nonnegative liminf.
7. **Tent construction:** the intervals are genuinely pairwise disjoint and lie in
   `[0,1]`.
8. **Scaling:** the chosen factor gives midpoint value exactly `n`.
9. **Unboundedness:** the pointwise value `n` gives the norm lower bound.
10. **Final assembly:** the hypotheses of the abstract convergence theorem are
    supplied by the concrete support construction.

### Scope of the formalization

The project formalizes **sequences** using `ℕ`, whereas the general mathematical
notion of `d`-weak convergence can be formulated for nets. This is intentional:
the target counterexample is a sequence.

The project also formalizes metric functionals through an explicit net witness
(`MetricFunctionalWitness`). This is the net-based pointwise-limit formulation of
metric functionals used by the proof. The witness index type is universe-aligned
with the ambient metric space; this is sufficient for the present development but
is a narrower API than a completely universe-polymorphic general theory of nets.

### Proof-engineering observations

- `T2Space K` is not essential to the norm-attainment argument itself, but retaining
  it is harmless and consistent with the usual compact Hausdorff setting.
- `continuous_tent` does not actually need the assumption `a ≤ b`; the argument only
  proves continuity. The inequality is nevertheless useful elsewhere, so carrying it
  through the definition is reasonable.
- The support lemmas deliberately prove only support **containment**, which is all
  the counterexample needs; proving the exact support would add unnecessary work.
- The spike sequence starts at `n = 0`. Then `spike 0 = 0`, which causes no problem:
  its support is empty and the norm bound `0 ≤ ‖spike 0‖` is valid. The published
  exposition starts its displayed sequence at positive indices, but the Lean
  indexing choice is mathematically harmless.

---

# 12. Building the project

The project uses Lean `v4.35.0-rc2` and Mathlib `v4.35.0-rc2` as specified by
`lean-toolchain` and `lakefile.toml`.

From the project root:

```bash
lake build
```

The main theorem is in `DWeakContFun.lean`:

```lean
#check spike_counterexample
```

`Main.lean` imports `Tent` as a lightweight entry point; the library roots are
listed explicitly in `lakefile.toml`.


## References

- A. W. Gutiérrez and O. Nevanlinna, *Metric functionals and weak convergence*,
  Z. Anal. Anwend. (2026), arXiv:2506.04154.
- A. W. Gutiérrez and O. Nevanlinna, *A Weak Topology on Metric Spaces*,
  arXiv:2609.19368, September 2026. The second paper contains the explicit
  `C[0,1]` counterexample formalized here (Theorem 1.3 and its proof).
