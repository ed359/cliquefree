# Weighted independent sets in clique-free graphs

This Lean project proves a weighted independent-set existence bound for every finite
simple graph excluding a clique of a prescribed order. The coefficient is an explicit
positive rational of order `1/r`, uniformly in the graph and its two weight vectors.
The existence statements are in [Challenge.lean](Challenge.lean), with proofs in
[Solution.lean](Solution.lean); [comparator.json](comparator.json) selects the two
declarations described below. Build and audit instructions are in the
[repository README](../README.md).

## Exact mathematical claim

Let $r\ge4$ be an integer and let $G=(V,E)$ be a finite simple $K_r$-free graph:
no $r$ distinct vertices are pairwise adjacent. Choose a positive real degree-weight
vector $s$ and an independently chosen nonnegative real objective-weight vector $a$.
For the open neighborhood $N(v)$, define

$$
d_{G,s}(v)=\frac{\sum_{x\in N(v)}s_x}{s_v},\qquad
f(d)=\frac{d\log d-d+1}{(d-1)^2}\quad(d>0,\ d\ne1),
$$

with $f(0)=1$ and $f(1)=1/2$. The logarithm is natural. Positivity of $s_v$
makes the denominator nonzero, and all degrees used in the theorem are nonnegative.
The two declarations use these explicit definitions and Mathlib's
`SimpleGraph.CliqueFree` and `SimpleGraph.IsIndepSet`.

`CliquefreeResults.weighted_existence` asserts the existence of one rational family
$(c_r)$ and absolute real constants $A,B>0$ such that, for every $r\ge4$,

$$
0<c_r,\qquad \frac{A}{r}\le c_r\le\frac{B}{r},
$$

and for every graph and weights as above there is an independent set $I\subseteq V$
with

$$
\sum_{v\in I}a_v\ \ge\ c_r\sum_{v\in V}a_v f\bigl(d_{G,s}(v)\bigr).
$$

The family and comparison constants are chosen before the graph and weights, so they
are uniform in those inputs. The independent set may depend on both weight vectors.

`CliquefreeResults.weighted_existence_explicit` gives the same existence inequality
and positivity for the particular rational coefficient

$$
c_r=\frac{1}{1+1152B_0r},\qquad
B_0=2^X,\qquad
X=\bigl(100\cdot24\cdot(20+12\cdot24^2+1)\bigr)^4.
$$

Here $B_0$ is one fixed absolute integer, represented symbolically in Lean. The
inverse-linear comparison in the first theorem can use
$A=(1+1152B_0)^{-1}$ and $B=(1152B_0)^{-1}$.

The statements permit the empty graph, isolated vertices, zero objective weights,
and irrational weights. On the empty graph both sums vanish; at an isolated vertex
the degree is zero and the benchmark uses $f(0)=1$. Both weight vectors may have
arbitrary normalization.

## Special cases and sources

Taking $s_v=a_v=1$ gives the degree-sequence lower bound
$|I|\ge c_r\sum_v f(\deg_G(v))$. For a $d$-regular graph, this becomes
$|I|\ge c_r|V|f(d)$; the explicit formula for $f$ has logarithmic-over-degree
growth as $d\to\infty$. The degree weights and objective weights can vary independently.

The mathematical sources are used as follows.

- James B. Shearer, *A note on the independence number of triangle-free graphs*,
  Discrete Mathematics 46(1), 83–87 (1983),
  [DOI:10.1016/0012-365X(83)90273-X](https://doi.org/10.1016/0012-365X(83)90273-X).
  This is background for the scalar function $f$ and the logarithmic improvement
  over reciprocal-degree bounds.
- Ewan Davies, *Random independent sets and local sparsity* (2026),
  [arXiv:2609.04654v1, Section 1.1](https://arxiv.org/html/2609.04654v1#S1.SS1).
  The weighted-degree formulation and Shearer benchmark are adapted from this
  setting.
- OpenAI, *A logarithmic independence bound for clique-free graphs*, preprint dated
  25 September 2026,
  [source at commit `adc7f1241b42e322a6451854ab7e4b4c146bf78a`](https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-Logarithmic-Independence-Bound-for-Clique-Free-Graphs-September-25-2026).
  The triangle-control mechanism in Sections 3–5 is adapted: pruning, neighborhood
  walks, entropy estimates, coupled labels, and vertex splitting with injective
  directed-edge projection. This development allows vertex-dependent scales and
  uses a scalar variational transform of $f$.
- Ross J. Kang, *Ode to the Ajtai–Erdős–Komlós–Szemerédi conjecture* (13 October 2026),
  [DOI:10.5281/zenodo.23351325](https://doi.org/10.5281/zenodo.23351325).
  The repeated neighborhood restriction in the proof of Lemma 3.1, step 1, is
  adapted into `Cliquefree.exists_sparseRestriction`. It supplies the linear clique
  scale used in the stationary-improvement argument.

## Proof implemented in Lean

The [blueprint](../blueprint/src/content.tex) follows the dependency closure of
`Cliquefree.existenceTheorem`. Scalar analysis of $f$ defines
$U_a(x)=\inf_{d>0}(af(d)+dx^2)$ for positive $x$, with value zero at $x=0$.
The graph potential is the sum of these scalar contributions minus twice the
unordered edge mass. Its derivative identities and tangent-loss bound relate
potential maximization to the prescribed-weight benchmark.

The triangle dichotomy bounds triangle mass unless a strong cross-mass witness
exists. Its proof uses finite laws, entropy estimates, grand coupling, pruning,
and repeated vertex splitting. In a clique-free graph, disjointification and
sparse restriction turn such a witness at a positive stationary maximizer into a
strict potential improvement. This excludes the witness and yields a triangle
bound at scale $24r$.

The averaged closed-neighborhood deletion identity then gives a vertex with a
nonnegative deletion reward. Compactness, boundary limits, and induction on the
number of vertices handle the existence of maximizers and degeneracies, including
zero objective weights and isolated vertices. The final argument produces the
independent set in the two existence theorems.

## Verification

The proof is in `Cliquefree/`. Mathlib supplies
the underlying graph theory, analysis, and Lean infrastructure; LeanArchitect
supplies blueprint metadata.

`Challenge.lean` contains two admitted statements for Comparator to check against
the independently proved statements in `Solution.lean`. The permitted proof axioms
are `propext`, `Quot.sound`, and `Classical.choice`. The local axiom audit checks
the proof declarations for any other axiom, including `sorryAx`; Comparator and
its independent NanoDa replay provide the separate statement-and-proof check.

Authorship, mathematical sources, tools, review status, and licensing are recorded
in [formalization.yaml](formalization.yaml).
