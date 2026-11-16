/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import DesignsII.VDecomp

/-!
# Atoms, types, elementary systems and regularity (Keevash, *Existence of designs II*, §2.5)

Fix a permutation group `Σ ≤ Sym(R)` and a vector system `(A, γ)` with values in `Γ = ℤ^D`.

* `typeVec S Σ i θ B` : `γ^θ ∈ Γ^{Σ}`, `σ ↦ γ_{θσ}` for `θ ∈ (A i)_B` (Definition 2.24; indexed by
  `σ ∈ Σ` instead of `Σ^B`, which only repeats coordinates);
* `IsElementary S Σ` : for every `r`-set `B` the nonzero `γ^θ` are linearly independent
  (equivalent to the linear independence of all atoms, remark after Lemma 2.26);
* `orbitVec Σ J ψ B` : `f_B(J)_ψ ∈ Γ^{Σ}`, `σ ↦ J_{ψσ}` (Definition 2.25);
* `IsRegular S Σ Φ G c ω` : Definition 2.31, with the atom coefficients expressed through the
  unique (by elementarity) representations of `f_B(∂y)_ψ` and `f_B(G)_ψ` in the nonzero `γ^θ`.
-/

@[expose] public section

namespace DesignsII

open Finset

variable {R V ι : Type*} [DecidableEq R] {D r : ℕ}

/-- The relabelling of a map with domain `B` by `σ`, with domain `σ⁻¹(B)`. -/
def relabelInv (θ : R → Option V) (σ : Equiv.Perm R) (B : Finset R) : R → Option V :=
  relabel θ σ (B.map σ.symm.toEmbedding)

/-- `γ^θ`: `σ ↦ γ_{θσ}` (Definition 2.24). -/
def typeVec (S : VSystem R ι (Fin D → ℤ) r) (Sg : Subgroup (Equiv.Perm R)) (i : ι)
    (θ : R → Option R) (B : Finset R) : Sg → (Fin D → ℤ) :=
  fun σ => S.γ i (relabelInv θ σ B)

/-- The nonzero type vectors at `B`. -/
def typeVecs (S : VSystem R ι (Fin D → ℤ) r) (Sg : Subgroup (Equiv.Perm R)) (B : Finset R) :
    Set (Sg → (Fin D → ℤ)) :=
  {g | g ≠ 0 ∧ ∃ i, ∃ θ ∈ (S.A i).maps B, g = typeVec S Sg i θ B}

/-- `γ` is elementary: for every `r`-set `B` the nonzero `γ^θ` are linearly independent. -/
def IsElementary (S : VSystem R ι (Fin D → ℤ) r) (Sg : Subgroup (Equiv.Perm R)) : Prop :=
  ∀ B : Finset R, B.card = r →
    LinearIndependent ℤ (Subtype.val : typeVecs S Sg B → (Sg → (Fin D → ℤ)))

/-- `f_B(J)_ψ`: `σ ↦ J_{ψσ}` (Definition 2.25). -/
def orbitVec {M : Type*} (Sg : Subgroup (Equiv.Perm R)) (J : (R → Option V) → M)
    (ψ : R → Option V) (B : Finset R) : Sg → M :=
  fun σ => J (relabelInv ψ σ B)

/-- `G` is `(γ, c, ω)`-regular in `Φ` (Definition 2.31): there are weights
`y_φ ∈ [ω n^{r-q}, ω⁻¹ n^{r-q}]` on the embeddings `φ` of members of the family into `Φ` whose
molecules lie below `G` (`allowed`), such that for every `ψ ∈ Φ_B` (`|B| = r`) the coefficients of
`f_B(∑ y_φ γ(φ))_ψ` in the nonzero type vectors are within a factor `1 ± c` of those of
`f_B(G)_ψ`. Here `n = |V(Φ)|` and `q = |R|`. -/
def IsRegular [Fintype R] [Fintype V] [DecidableEq V] (S : VSystem R ι (Fin D → ℤ) r)
    (Sg : Subgroup (Equiv.Perm R)) (Φ : RSystem R V) (G : (R → Option V) → (Fin D → ℤ))
    (allowed : Finset (ι × (R → V))) (c ω : ℝ) : Prop :=
  ∃ y : ι × (R → V) → ℝ,
    (∀ p ∈ allowed, ω * (Fintype.card V : ℝ) ^ ((r : ℤ) - Fintype.card R) ≤ y p ∧
      y p ≤ ω⁻¹ * (Fintype.card V : ℝ) ^ ((r : ℤ) - Fintype.card R)) ∧
    ∀ B : Finset R, B.card = r → ∀ ψ ∈ Φ.maps B,
      ∃ (a : typeVecs S Sg B → ℝ) (b : typeVecs S Sg B → ℤ),
        (∀ (σ : Sg) d, ∑ p ∈ allowed, y p * (S.molecule p.1 p.2 (relabelInv ψ σ B) d : ℝ) =
          ∑ᶠ g, a g * ((g : Sg → (Fin D → ℤ)) σ d : ℝ)) ∧
        (∀ (σ : Sg) d, orbitVec Sg G ψ B σ d = ∑ᶠ g, b g * (g : Sg → (Fin D → ℤ)) σ d) ∧
        ∀ g, |a g - b g| ≤ c * |(b g : ℝ)|

end DesignsII
