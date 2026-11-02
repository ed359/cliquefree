# Weighted independent sets in clique-free graphs

A mathematical blueprint and Lean proof of a weighted independent-set bound for
finite $K_r$-free graphs, with an explicit rational coefficient of order $1/r$.
The blueprint presents the theorem labelled `thm:existence` and its prerequisites.

The [mathematical account](lean/README.md) states the existence theorems and
explains their proof and mathematical sources. [Project metadata](lean/formalization.yaml)
records authorship, sources, tools, and review status.
The project is licensed under [Apache-2.0](LICENSE).

## Layout

- `lean/`: Lean package, with mathematics in `Cliquefree/` and metadata in
  `Cliquefree/Blueprint.lean`.
- `lean/Challenge.lean`: independent, Mathlib-only statements of the existence theorems;
  `lean/Solution.lean` proves the matching statements from the formalization.
- `blueprint/src/`: printable and interactive blueprint of the checked existence proof.
  Every node names a declaration used by `Cliquefree.existenceTheorem`.
- `site/index.html`: landing page for the published blueprint and Lean API documentation.
- `lean/formalization.yaml`: theorem, source, authorship, and review metadata.
- `scripts/`: blueprint consistency checks and the local Comparator runner.

Dependencies are pinned in `lean/lake-manifest.json`: Lean **4.35.0**, mathlib **v4.35.0**, and
LeanArchitect **v4.35.0**.

## Build

```sh
cd lean
lake exe cache get
lake build
lake build +Cliquefree.Blueprint:blueprint +Cliquefree.Blueprint:blueprintJson
lake env lean AxiomAudit.lean
lake lint
cd ..
python3 scripts/check-blueprint-labels.py --dependencies lean/.lake/build/existence-dependencies.json
```

For the blueprint PDF and website, install `leanblueprint==0.0.20`, Graphviz, and a TeX
distribution including XeLaTeX and latexmk, then run:

```sh
cd blueprint/src
mkdir -p ../print ../web
latexmk -output-directory=../print
plastex -c plastex.cfg web.tex
```

## Auditing the existence statements

[`lean/Challenge.lean`](lean/Challenge.lean) states the weighted existence theorem with rational
coefficients of order `1/r` and the explicit coefficient, using Mathlib graphs, independent
sets, finite sums, and an explicit Shearer function.
The two statements in `Challenge` have admitted proofs for Comparator to check against
the independently proved statements in [`lean/Solution.lean`](lean/Solution.lean).
The proof axiom audit and lint check `Solution` and the `Cliquefree` development.

[`lean/comparator.json`](lean/comparator.json) selects both existence declarations and permits
only `propext`, `Quot.sound`, and `Classical.choice`. Comparator checks that the statements and
their definitions match, checks the proof axioms, and replays the proofs in Lean and NanoDa.
The [Comparator workflow](.github/workflows/comparator.yml) runs this check on Linux
for pushes to `main` and `sani`, pull requests, and manual runs. It uses the
Comparator and kernel checkers bundled with the pinned Lean toolchain.
To run that same check on a suitable Linux host:

```sh
./scripts/verify-comparator.sh
```

The sandboxed runner requires Linux; local Lean builds and the axiom audit above
remain available on macOS.

## Proof

The proof uses a deterministic neighborhood restriction adapted from Kang's
*Ode to the Ajtai–Erdős–Komlós–Szemerédi conjecture*. The Lean existence theorem uses
`linearCliqueScale r = 24r` and the positive rational coefficient
`linearExistenceConstant r = 1/(1 + 1152 B₀ r)`, with proved inverse-linear bounds.
The checked proof includes sparse restriction, a strict improvement at a stationary
point, the real-weight triangle dichotomy, and compactness induction. The main
`existenceTheorem` covers arbitrary positive real degree weights and nonnegative real
objective weights.

The axiom audit traces the type and proof of `Cliquefree.existenceTheorem` and verifies
that every mathematical module contributes to its proof and every blueprint node belongs
to its dependency closure. The blueprint label check verifies that every displayed node
leads to the existence theorem.
