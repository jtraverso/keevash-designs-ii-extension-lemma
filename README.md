# Keevash, *The existence of designs II*, Lemma 3.8 (`ext*`) in Lean 4

A Lean 4 / Mathlib formalization of Lemma 3.8 of P. Keevash,
[*The existence of designs II*](https://arxiv.org/abs/1802.05900): in the random algebraic template,
extensions of a configuration whose atoms are covered by the template are, with high probability,
as many as expected.

* **Challenge:** [`DesignsIIExtChallenge.lean`](DesignsIIExtChallenge.lean) — the definitions
  (labelled complexes, adapted complexes, extendability, vector systems, molecules and atoms, the
  template probability space and the template `M*`) and the statement
  `DesignsII.TParams.lemma_3_8`, with explicit rates.
* **Solution:** [`DesignsIIExtSolution.lean`](DesignsIIExtSolution.lean), proved by
  `DesignsII.TParams.ext_star_paper` in [`DesignsII/ExtPaper.lean`](DesignsII/ExtPaper.lean).
* The definitions are those of [`DesignsII/ExtDefs.lean`](DesignsII/ExtDefs.lean), repeated verbatim
  in the challenge.

## Structure of the proof

| File | Content |
|---|---|
| `Template`, `TemplateProb`, `TemplateSpace`, `Joint` | generic matrices, Designs I Lemma 3.3, the template space, joint independence of edge-disjoint copies |
| `Lipschitz`, `TwoStage`, `Counting`, `CondPerm`, `CondCert`, `Stage2Cert` | Lemma `lip3`, two-stage exposure, certificate Lipschitz bounds, conditioned permutations |
| `CondCompat`, `CondCopy`, `AffineCount`, `ESlice`, `Degenerate`, `ManyDeg` | Lemma `e|E`: conditional passing probabilities given the fixed vertices; degenerate colours |
| `CondCover`, `ExtCert`, `ExtConc`, `ExtStar`, `PassAsymp`, `ExtAsymp`, `ExtFinal` | the covering count: mean, certificates, concentration, `ext*` with explicit rates |
| `Orbits`, `AtomDecomp`, `AtomEq`, `AtomLe`, `LabelledExt` | orbits, atoms, Lemma 2.21, the labelled form `γ(ψ) ≤_γ ∂^γ M*` |
| `SimpleExt`, `ExtCand`, `ExtTuples`, `ConfigCount`, `ExtPaper` | candidate copies from extendability, good tuples, configuration counts, Lemma 3.8 |

Corrections to the paper's sketch (the concentration of `ext*`) are described in
[`formalization.yaml`](formalization.yaml).

Lean `v4.35.0-rc3`, Mathlib `c55e6e786f49471c72fbddbec5415808896aec1e`. Depends on
[keevash-triangle-decompositions](https://github.com/jtraverso/keevash-triangle-decompositions)
(PALOMAR-2026-11-14-000022 v2) for the concentration inequality for random permutations.

License: Apache 2.0. Author: Juan Pablo Traverso Gianini.
