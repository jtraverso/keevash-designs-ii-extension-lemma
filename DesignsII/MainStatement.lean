/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import DesignsII.ExtDefs
public import DesignsII.Atoms

/-!
# The statement of the main theorem (Keevash, *The existence of designs II*, Theorem 3.1)

* `sigmaLe Σ` : the `R`-complex `Σ^≤` of restrictions of elements of `Σ` (Definition 2.10);
* `atoms S Σ Φ` : the `γ`-atoms `γ(φ)^O ≠ 0` (Definition 2.21);
* `LeGamma S Σ Φ H G` : `H ≤_γ G` (`G - H` is a sum of atoms);
* `moleculeP S i ψ` : `γ(ψ)` for a partial map `ψ ∈ A(Φ)^≤` (Definition 2.22);
* `IsExtendableRel Φ Φ' ω s` : `(Φ, Φ')`-extendability (Definition 2.9) for a family `Φ'` of
  restrictions of `Φ_r`;
* `MainTheoremStatement` : Theorem 3.1.

The statement is recorded as a `Prop` (no proof yet); it is the target of Phases 2–3 of the
blueprint.
-/

@[expose] public section

namespace DesignsII

open Finset

variable {R V ι : Type*} [DecidableEq R] {D r : ℕ}

variable [Fintype V] [DecidableEq V]

end DesignsII

namespace DesignsII

open Finset

open Classical in
/-- **Keevash, *The existence of designs II*, Theorem 3.1.** For any `q ≥ r` and `D` there are
`ω₀ > 0` and `n₀` such that for `n > n₀`, `h = 2^{50q³}`, `δ = 2^{-10³ q⁵}`, `n^{-δ} < ω < ω₀` and
`c ≤ ω^{h^{20}}`: if `𝒜` is a `Σ^≤`-family with `Σ ≤ S_q`, `γ ∈ (ℤ^D)^{𝒜_r}` is elementary, `Φ` is
a `Σ`-adapted `[q]`-complex on `[n]`, `G ∈ ⟨γ(Φ)⟩` is `(γ, c, ω)`-regular in `Φ` and
`(Φ, γ[G])` is `(ω, h)`-extendable, then `G` has a `γ(Φ)`-decomposition. -/
def MainTheoremStatement : Prop :=
  ∀ q r D : ℕ, r ≤ q → ∃ ω₀ : ℝ, 0 < ω₀ ∧ ∃ n₀ : ℕ, ∀ n : ℕ, n₀ < n →
    ∀ ω c : ℝ, (n : ℝ) ^ (-((2 : ℝ) ^ (-(10 ^ 3 * (q : ℝ) ^ 5)))) < ω → ω < ω₀ →
      c ≤ ω ^ ((2 ^ (50 * q ^ 3)) ^ 20 : ℕ) →
    ∀ (Sg : Subgroup (Equiv.Perm (Fin q))) (ι : Type) [Fintype ι]
      (S : VSystem (Fin q) ι (Fin D → ℤ) r),
      (∀ i, S.A i = sigmaLe Sg) → IsElementary S Sg →
    ∀ Φ : RSystem (Fin q) (Fin n), Φ.IsComplex → IsAdapted Φ Sg →
    ∀ G : (Fin q → Option (Fin n)) → (Fin D → ℤ), G ∈ S.lattice Φ →
      IsRegular S Sg Φ G (univ.filter fun p : ι × (Fin q → Fin n) =>
        IsEmbedding (S.A p.1) Φ p.2 ∧ LeGamma S Sg Φ (S.molecule p.1 p.2) G) c ω →
      IsExtendableRel (r := r) Φ (gammaG S Sg Φ G) ω (2 ^ (50 * q ^ 3)) →
      ∃ Ψ : Finset (ι × (Fin q → Fin n)), S.IsDecomp Φ G Ψ

end DesignsII
