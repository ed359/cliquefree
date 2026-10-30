module

public import Architect
public import Cliquefree

/-!
# Blueprint of the existence theorem

Selected checked declarations from the proof of `Cliquefree.existenceTheorem`.
The metadata records the main mathematical dependencies of that proof.
-/

namespace Cliquefree

attribute [blueprint "thm:existence"
  (title := /-- Existence -/)
  (statement := /-- There is a family of positive rational constants $c_r$ for $r\ge4$,
    with $c_r=\Theta(r^{-1})$, such that every finite $K_r$-free graph $G$ and
    real weights $s>0$, $u\ge0$ satisfy
    \[
      \alpha_u(G)\ge c_r\Phi_{G,u}(s).
    \]
    One may take $c_r=1/(1+1152B_0r)$. -/)
  (uses := ["bp:constant-bounds", "lean:weighted-bound", "lean:independence-attained"])
  (latexEnv := "theorem")]
  existenceTheorem

attribute [blueprint "bp:triangle-constants"
  (title := /-- Absolute triangle constants -/)
  (statement := /-- Set $C_*=24$, $A_*=20+12C_*^2$, $a_*=24(A_*+1)$,
    $X=(100a_*)^4$, and $B_0=2^X$. -/)]
  triangleBoundConstant

attribute [blueprint "bp:constants"
  (title := /-- The common coefficient -/)
  (statement := /-- For integer $r\ge0$, put $K=24r$ and
    $c_r=(1+48B_0K)^{-1}=(1+1152B_0r)^{-1}$. -/)
  (uses := ["bp:triangle-constants"])]
  linearExistenceConstant

attribute [blueprint "bp:constant-bounds"
  (title := /-- Inverse-linear coefficient bounds -/)
  (statement := /-- There are absolute real constants $A,B>0$ such that, for every integer $r\ge4$,
    $A/r\le c_r\le B/r$. -/)
  (uses := ["bp:constants"])
  (latexEnv := "lemma")]
  linearExistenceConstant_order_inverse

attribute [blueprint "lean:shearer-f"
  (title := /-- Shearer's function -/)
  (statement := /-- Set $f(0)=1$, $f(1)=1/2$, and
    $f(d)=(d\log d-d+1)/(d-1)^2$ away from these endpoints. -/)]
  shearerF

attribute [blueprint "bp:weighted-degree"
  (title := /-- Weighted degree -/)
  (statement := /-- For positive vertex weights $s$, put $d_{G,s}(v)=s(N(v))/s_v$. -/)]
  weightedDegree

attribute [blueprint "bp:objective"
  (title := /-- Weighted benchmark -/)
  (statement := /-- Set $\Phi_{G,u}(s)=\sum_vu_vf(d_{G,s}(v))$. -/)
  (uses := ["bp:weighted-degree", "lean:shearer-f"])
  (latexEnv := "definition")]
  benchmark

attribute [blueprint "lean:independence-attained"
  (title := /-- An independent set attains the optimum -/)
  (statement := /-- There exists an independent set $I$ with $u(I)=\alpha_u(G)$. -/)]
  independenceWeight_attained

attribute [blueprint "bp:extremal-benchmark"
  (title := /-- Extremal benchmark -/)
  (statement := /-- Define $F(G,u)=\sup_{s>0}\Phi_{G,u}(s)$. -/)
  (uses := ["bp:objective"])]
  extremalBenchmark

attribute [blueprint "bp:graph-masses"
  (title := /-- Graph masses -/)
  (statement := /-- Write $\Lambda_v=w(N(v))$,
    $M_G(w)=\frac12\sum_{x,y:x\sim y}w_xw_y$, and
    $T_G(w)=\frac16\sum_{x,y,z:x\sim y,\,y\sim z,\,z\sim x}w_xw_yw_z$.
    The factors remove the two orientations of an edge and six orderings of a triangle. -/)]
  triangleMass

attribute [blueprint "bp:scalar-potential"
  (title := /-- Scalar potential -/)
  (statement := /-- For $a\ge0$ and $x>0$, set
    $U_a(x)=\inf_{d>0}\{af(d)+dx^2\}$, with $U_a(0)=0$.
    In particular, $U_0(x)=0$ for every $x\ge0$.
    For $a,x>0$, define $\xi_a(x)=U_a(x)-xU'_a(x)$. -/)
  (uses := ["lean:shearer-f"])]
  scalarXi

attribute [blueprint "bp:graph-potential"
  (title := /-- Graph potential -/)
  (statement := /-- Define $\mathcal U_{G,u}(w)=\sum_v U_{u_v}(w_v)-2M_G(w)$,
    including nonnegative auxiliary vectors. -/)
  (uses := ["bp:scalar-potential", "bp:graph-masses"])]
  graphPotential

attribute [blueprint "bp:residual-reward"
  (title := /-- Residuals and deletion reward -/)
  (statement := /-- Write $\xi_v=\xi_{u_v}(w_v)$,
    $\zeta_v=U_{u_v}^\prime(w_v)-2\Lambda_v$, and $S=\sum_vu_vw_v$. For
    $G_x=G-N[x]$, put $R_x=u_x+c\mathcal U_{G_x,u}(w)-c\mathcal U_{G,u}(w)$.
    In Lean, deletion zeroes the closed-neighborhood coordinates. -/)
  (uses := ["bp:graph-potential"])
  (latexEnv := "definition")]
  deletionReward

attribute [blueprint "bp:triangle-scales"
  (title := /-- Scaled degree budget -/)
  (statement := /-- For scales $\theta$, write $b(A)=\sum_{v\in A}\theta_vw_v$ and
    $D_\theta=\sum_v\theta_vw_v\Lambda_v$. -/)
  (uses := ["bp:graph-masses"])
  (latexEnv := "definition")]
  scaledDegreeBudget

attribute [blueprint "bp:witness"
  (title := /-- Strong witness -/)
  (statement := /-- A witness consists of vertex sets $A,B$ (which may overlap),
    an integer $p\ge1$, and a scale $\rho=\theta_v$ for some vertex $v$,
    satisfying $w(A),w(B)\le\rho2^p$, $b(B)\le\rho^22^{2p}$, and
    $\Xi_w(A,B)>24(pb(A)+\rho^22^{-p})$. -/)
  (uses := ["bp:triangle-scales", "bp:graph-masses"])]
  TriangleWitness

attribute [blueprint "lean:f-continuous"
  (title := /-- Continuity of the benchmark function -/)
  (statement := /-- The explicitly extended function $f$ is continuous on $[0,\infty)$. -/)
  (uses := ["lean:shearer-f"])
  (proof := /-- Use continuity of $d\log d$ at zero and l'Hopital's rule at one. -/)]
  shearerF_continuous

attribute [blueprint "lean:f-limit"
  (title := /-- Limit at infinity -/)
  (statement := /-- As $d\to\infty$, $f(d)\to0$. -/)
  (uses := ["lean:shearer-f"])]
  shearerF_tendsto_atTop

attribute [blueprint "lean:f-integral"
  (title := /-- Integral representation on the unit interval -/)
  (statement := /-- For $d>0$,
    $f(d)=\int_0^1(1-t)/(1+(d-1)t)\,dt$. -/)
  (uses := ["lean:shearer-f"])]
  shearerF_eq_integral

attribute [blueprint "lean:optimizer-equation"
  (title := /-- Optimizer equation -/)
  (statement := /-- For $a,x>0$, let $d_*(a,x)$ denote the unique positive solution of
    $x^2=-af'(d_*)$. It attains the scalar infimum:
    $U_a(x)=af(d_*)+d_*x^2$. -/)
  (uses := ["bp:scalar-potential", "lean:f-integral"])]
  scalarOptimizer_spec

attribute [blueprint "lean:envelope-derivative"
  (title := /-- Envelope derivative -/)
  (statement := /-- For $a,x>0$, $U'_a(x)=2d_*(a,x)x$. -/)
  (uses := ["bp:scalar-potential", "lean:optimizer-equation"])]
  scalarPotential_hasDerivAt

attribute [blueprint "lean:potential-continuous"
  (title := /-- Continuity of the scalar potential -/)
  (statement := /-- For $a>0$, the scalar potential is continuous, including at zero. -/)
  (uses := ["bp:scalar-potential", "lean:optimizer-equation", "lean:f-limit"])]
  scalarPotential_continuous

attribute [blueprint "lean:xi-positive"
  (title := /-- Positivity of the scalar remainder -/)
  (statement := /-- For $a,x>0$, $\xi_a(x)>0$. -/)
  (uses := ["bp:scalar-potential", "lean:envelope-derivative", "lean:f-integral"])]
  scalarXi_pos

attribute [blueprint "bp:scalar-ode"
  (title := /-- Scalar cancellation identity -/)
  (statement := /-- For $a,x>0$ and $d=d_*(a,x)$, $(1+d)\xi_a(x)+2dx^2=a$. -/)
  (uses := ["bp:scalar-potential", "lean:optimizer-equation", "lean:envelope-derivative"])
  (latexEnv := "lemma")]
  scalarOptimizer_ode

attribute [blueprint "bp:scalar-loss"
  (title := /-- Tangent-loss bound -/)
  (statement := /-- For $a,x>0$ and $\lambda\ge1$,
    \[U_a(x)+U_a^\prime(x)(\lambda x-x)-U_a(\lambda x)
      \le4\xi_a(x)(\lambda-1)\log\lambda.\] -/)
  (uses := ["bp:scalar-potential", "lean:envelope-derivative", "lean:xi-positive"])
  (latexEnv := "lemma")]
  scalarPotential_tangent_loss

attribute [blueprint "bp:potential-comparison"
  (title := /-- Potential comparison -/)
  (statement := /-- For $u\ge0$ and $w>0$,
    $\mathcal U_{G,u}(w)\le\Phi_{G,u}(w)$. -/)
  (uses := ["bp:graph-potential", "bp:objective"])
  (proof := /-- Test the scalar infimum at the nonnegative weighted degree,
    sum the inequalities, and cancel the weighted edge term. -/)
  (latexEnv := "lemma")]
  graphPotential_le_benchmark

attribute [blueprint "lem:lift"
  (title := /-- Lifting the prescribed weights -/)
  (statement := /-- Suppose $G$ has no isolated vertices and $s,u>0$.
    Set $q_v=\sqrt{-u_vf'(d_{G,s}(v))}$. Then
    $\Phi_{G,u}(s)\le\mathcal U_{G,u}(q)$. -/)
  (uses := ["bp:graph-potential", "bp:objective", "lean:f-integral"])
  (proof := /-- Positive weighted degrees give positive lift coordinates. Convexity makes
    each prescribed degree attain its scalar infimum; the remaining graph discrepancy is
    a sum of squares over edges. -/)
  (latexEnv := "lemma")]
  benchmark_le_lifted_potential

attribute [blueprint "cor:transfer"
  (title := /-- Transferring a maximizer -/)
  (statement := /-- Suppose $G$ has no isolated vertices and $u>0$.
    If $s>0$ maximizes $\Phi_{G,u}$ over positive vectors, its lift
    $q_v=\sqrt{-u_vf'(d_{G,s}(v))}$ maximizes $\mathcal U_{G,u}$
    over all nonnegative vectors. -/)
  (uses := ["lem:lift", "bp:potential-comparison", "lean:potential-continuous",
    "lean:envelope-derivative"])
  (proof := /-- The lift and comparison force equality of the attained values.
    Continuity extends maximality to nonnegative competitors. -/)
  (latexEnv := "corollary")]
  lift_maximizes_nonnegativePotential

attribute [blueprint "lean:maximizer-stationary"
  (title := /-- Stationarity at a positive maximizer -/)
  (statement := /-- If $u,w>0$ and $w$ maximizes $\mathcal U_{G,u}$
    over positive vectors, then $\zeta_v=0$ for every vertex. -/)
  (uses := ["bp:residual-reward", "lean:envelope-derivative"])
  (latexEnv := "lemma")]
  positive_maximizer_stationary

attribute [blueprint "lean:pruning"
  (title := /-- Finite edge pruning -/)
  (statement := /-- For nonnegative weights and scales and $t>0$, there is a spanning
    subgraph $H\le G$ whose common-neighbor mass
    $C^H_{xy}=w(N_H(x)\cap N_H(y))$ satisfies
    $C^H_{xy}\ge\max(\theta_x,\theta_y)/t$ on each remaining edge,
    $T_H\ge T_G-D_G/t$, $D_H\le D_G$, and $\Lambda^H_v\le\Lambda^G_v$,
    where $D_H$ and $D_G$ are the scaled degree budgets in the indicated graphs.
    The construction terminates by induction on the number of edges. -/)
  (uses := ["bp:graph-masses", "bp:triangle-scales"])
  (latexEnv := "lemma")]
  exists_prepared_subgraph

attribute [blueprint "lean:grand-coupling"
  (title := /-- Finite grand coupling -/)
  (statement := /-- A finite family of probability vectors $(p_i)$ on a finite set admits
    a joint finite law on labels $(Y_i)$ with marginals $p_i$ and
    $\mathbb P(Y_i\ne Y_j)\le2\|p_i-p_j\|_{\mathrm{TV}}$ for every pair,
    where $\|p-q\|_{\mathrm{TV}}=\frac12\sum_z|p(z)-q(z)|$. -/)
  (latexEnv := "lemma")]
  exists_grand_coupling

attribute [blueprint "bp:triangle-reduction"
  (title := /-- Triangle reduction step -/)
  (statement := /-- Let $t>X$ be an integer and let $w,\theta>0$.
    If $\Lambda_v\le2^t\theta_v$ for all $v$ and $T_G(w)>2D_\theta$,
    either there is a strong witness, or there is a finite graph $H$
    with a vertex map $\pi:V(H)\to V(G)$ that preserves adjacency and is
    injective on directed edges, meaning that distinct ordered adjacent pairs
    have distinct images. With inherited weights $w\circ\pi$, $\theta\circ\pi$,
    this graph satisfies
    \[\Lambda^H_v\le2^{t^\prime}\theta_{\pi(v)},\qquad
      T_H\ge(1-\delta(t))T_G-D_\theta/t,\]
    where $t^\prime=\lceil\sqrt t\rceil$ and
    $\delta(t)=2a_*\lceil\log_2t\rceil/\lfloor\sqrt t\rfloor$. -/)
  (uses := ["bp:triangle-constants", "bp:witness", "bp:triangle-scales", "lean:pruning",
    "lean:grand-coupling"])
  (latexEnv := "lemma")]
  triangle_reduction_step

attribute [blueprint "lem:triangle-test"
  (title := /-- Real-weight triangle dichotomy -/)
  (statement := /-- On every finite graph with positive real $w,\theta$, either
    $T_G(w)\le B_0D_\theta$ or a strong witness $(A,B,p,\rho)$ exists. -/)
  (uses := ["bp:triangle-reduction", "bp:witness", "bp:triangle-constants"])
  (latexEnv := "lemma")]
  triangle_dichotomy

attribute [blueprint "bp:disjointification"
  (title := /-- Disjointifying a strong witness -/)
  (statement := /-- For $b_v\ge0$, put $b(A)=\sum_{v\in A}b_v$.
    Let $p\ge0$ and $\delta>0$, and suppose $\Xi_w(A,B)>24(pb(A)+\delta)$.
    There are nonempty disjoint $A^\prime\subseteq A$, $B^\prime\subseteq B$ with
    \[\Xi_w(A^\prime,B^\prime)-pb(A^\prime)>\tfrac{11}{2}pb(A)+6\delta.\] -/)
  (uses := ["bp:graph-masses"])
  (latexEnv := "lemma")]
  exists_disjoint_strong_witness

attribute [blueprint "lem:sparse-restriction"
  (title := /-- Sparse restriction -/)
  (statement := /-- Let $r\ge2$, let $G$ be a finite $K_r$-free graph with
    positive real weights $w$, let $H\subseteq V(G)$ be nonempty, and let $Q\ge1$.
    There is a nonempty set $C\subseteq H$ such that
    \[
      w(C)\ge Q^{-(r-2)}w(H),\qquad
      w(N(v)\cap C)\le w(C)/Q\quad(v\in C).
    \] -/)
  (proof := /-- If the degree bound fails, restrict to a heavy neighborhood.
    Each restriction decreases the forbidden clique order and retains more than
    a $1/Q$ fraction of the weight. At order two the induced graph is edgeless. -/)
  (latexEnv := "lemma")]
  exists_sparseRestriction

attribute [blueprint "lem:improvement"
  (title := /-- Strict stationary improvement with linear clique scale -/)
  (statement := /-- Let $r\ge2$, let $G$ be $K_r$-free, and let $u,w,\theta>0$.
    Suppose $\zeta=0$ and $\theta_vw_v\ge24r\xi_v$ at every vertex.
    A strong witness yields a nonnegative vector $q$ with
    $\mathcal U_{G,u}(w)<\mathcal U_{G,u}(q)$. -/)
  (uses := ["bp:witness", "bp:graph-potential", "bp:residual-reward", "bp:scalar-loss",
    "lem:sparse-restriction", "bp:disjointification", "bp:constants"])
  (latexEnv := "lemma")]
  exists_stationary_linear_improvement

attribute [blueprint "lean:stationary-budget"
  (title := /-- Degree budget at stationarity -/)
  (statement := /-- If $u,w>0$, $K\ge0$, and $\zeta=0$, put
    $\theta_v=K\xi_v/w_v$. Then $D_\theta\le K\sum_vu_vw_v=KS$. -/)
  (uses := ["bp:triangle-scales", "bp:residual-reward", "bp:scalar-ode",
    "lean:envelope-derivative"])]
  stationary_degree_budget_le

attribute [blueprint "cor:stationary"
  (title := /-- Triangles at a maximizer -/)
  (statement := /-- Let $r\ge2$, $K=24r$, and let $G$ be $K_r$-free with $u>0$.
    If $w>0$ globally maximizes $\mathcal U_{G,u}$ over nonnegative vectors, then
    for $\theta_v=K\xi_v/w_v$,
    \[
      T_G(w)\le B_0D_\theta\le B_0KS.
    \] -/)
  (uses := ["lem:triangle-test", "lem:improvement", "lean:stationary-budget", "lean:xi-positive",
    "lean:maximizer-stationary", "bp:constants"])
  (latexEnv := "corollary")]
  linear_triangles_at_maximizer

attribute [blueprint "lem:deletion"
  (title := /-- Averaged deletion reward -/)
  (statement := /-- For $u,w>0$ and every real $c$, without stationarity,
    \[\sum_xw_xR_x=(1-c)S-6cT_G(w)
      -c\sum_v\zeta_v(w_v\Lambda_v-\xi_v/2).\] -/)
  (uses := ["bp:residual-reward", "bp:scalar-ode"])
  (proof := /-- Expand the deletion cost, average the closed-neighborhood terms,
    and apply the scalar cancellation equation at each vertex. -/)
  (latexEnv := "lemma")]
  averaged_deletion_reward

attribute [blueprint "lean:deletion-slack"
  (title := /-- Nonnegative deletion margin -/)
  (statement := /-- For every integer $r\ge0$, $1-c_r-6c_rB_0K\ge0$, where $K=24r$. -/)
  (uses := ["bp:constants"])
  (latexEnv := "lemma")]
  linearExistenceConstant_real_existence_slack

attribute [blueprint "lean:deletion-pivot"
  (title := /-- A stationary triangle bound gives a deletion pivot -/)
  (statement := /-- Let $r\ge0$ be an integer and put $K=24r$.
    On a nonempty graph with $u,w>0$ and $\zeta=0$, assume $T_G(w)\le B_0KS$.
    Then some vertex has $R_x\ge0$ for $c=c_r$. -/)
  (uses := ["bp:constants", "bp:residual-reward", "lem:deletion", "lean:deletion-slack"])]
  linear_exists_nonnegative_deletionReward

attribute [blueprint "bp:maximizing-sequence"
  (title := /-- A normalized maximizing limit -/)
  (statement := /-- On a nonempty finite graph with $u\ge0$, there are positive vectors $s_n$
    of total mass one and a nonnegative vector $s_0$ of total mass one such that
    $s_n\to s_0$ and $\Phi_{G,u}(s_n)\to F(G,u)$. -/)
  (uses := ["bp:extremal-benchmark"])
  (latexEnv := "lemma")]
  exists_normalized_maximizing_limit

attribute [blueprint "bp:boundary-decomposition"
  (title := /-- Boundary decomposition -/)
  (statement := /-- Let $u\ge0$ and let positive vectors $s_n$ converge to $s_0\ge0$ with
    $\Phi_{G,u}(s_n)\to F(G,u)$. Put $A=\{v:s_0(v)>0\}$ and $B=V\setminus N[A]$. Then
    \[F(G,u)\le F(G[A],u|_A)+F(G[B],u|_B).\] -/)
  (uses := ["bp:extremal-benchmark", "lean:f-continuous", "lean:f-limit"])
  (latexEnv := "lemma")]
  boundary_decomposition

attribute [blueprint "lean:compactness-reduction"
  (title := /-- Existence reduced to the stationary triangle estimate -/)
  (statement := /-- Fix an integer $r\ge0$ and put $K=24r$.
    Assume that, on every finite $K_r$-free graph with $u>0$, every $w>0$ that maximizes
    $\mathcal U_{G,u}$ over nonnegative vectors satisfies $T_G(w)\le B_0KS$.
    Then every finite $K_r$-free graph with $u\ge0$ satisfies
    $c_r F(G,u)\le\alpha_u(G)$. -/)
  (uses := ["bp:extremal-benchmark", "bp:constants", "cor:transfer", "lean:deletion-pivot",
    "bp:maximizing-sequence", "bp:boundary-decomposition"])
  (latexEnv := "theorem")]
  linear_extremal_bound_of_stationary_triangle_bound

attribute [blueprint "lean:weighted-bound"
  (title := /-- The prescribed-weight inequality -/)
  (statement := /-- For $r\ge2$, a finite $K_r$-free graph, $u\ge0$, and $s>0$,
    $c_r\Phi_{G,u}(s)\le\alpha_u(G)$. -/)
  (uses := ["cor:stationary", "lean:compactness-reduction", "bp:objective"])
  (latexEnv := "lemma")]
  linear_weighted_independence_bound

end Cliquefree
