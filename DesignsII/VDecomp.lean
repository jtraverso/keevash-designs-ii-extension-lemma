/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import DesignsII.ExtDefs
public import DesignsII.Extension
public import DesignsII.Adapted

/-!
# Vector-valued decompositions (Keevash, *The existence of designs II*, §2.4)

A `Σ^≤`-family is a family `(A i)_{i ∈ ι}` of copies of `Σ^≤`; each `A i` is an `R`-complex with
vertex set `R`. A `Γ`-system assigns `γ i θ ∈ Γ` to every `θ ∈ (A i)_r`. For a `Φ`-embedding `φ`
of `A i`, the molecule `γ(φ) ∈ Γ^{Φ_r}` has `γ(φ)_{φ ∘ θ} = γ i θ` (Definition 2.17). A
`γ(Φ)`-decomposition of `G ∈ Γ^{Φ_r}` is a finite set `Ψ` of embeddings whose molecules sum to
`G`; an integral decomposition allows integer multiplicities.

* `VSystem R ι Γ r` : the data `(A, γ)` with uniformity `r`;
* `VSystem.molecule` : `γ(φ)`;
* `VSystem.IsDecomp`, `VSystem.IsIntDecomp`, `VSystem.lattice` : decompositions and the
  decomposition lattice `⟨γ(Φ)⟩`.
-/

@[expose] public section

namespace DesignsII

open Finset

variable {R V ι Γ : Type*} [DecidableEq R]

namespace VSystem

variable {r : ℕ} (S : VSystem R ι Γ r)

variable [AddCommMonoid Γ]

/-- `Ψ` is a `γ(Φ)`-decomposition of `G`: a finite set of `Φ`-embeddings of members of the family
whose molecules sum to `G` (on `Φ_r`). -/
def IsDecomp (Φ : RSystem R V) (G : (R → Option V) → Γ) (Ψ : Finset (ι × (R → V))) : Prop :=
  (∀ p ∈ Ψ, IsEmbedding (S.A p.1) Φ p.2) ∧ S.boundary Ψ = G

end VSystem

section Int

variable {r : ℕ} [AddCommGroup Γ] (S : VSystem R ι Γ r)

/-- An integral `γ(Φ)`-decomposition: integer multiplicities on finitely many embeddings. -/
def VSystem.IsIntDecomp (Φ : RSystem R V) (G : (R → Option V) → Γ)
    (Ψ : (ι × (R → V)) →₀ ℤ) : Prop :=
  (∀ p ∈ Ψ.support, IsEmbedding (S.A p.1) Φ p.2) ∧
    (fun ψ => Ψ.sum fun p m => m • S.molecule p.1 p.2 ψ) = G

/-- The decomposition lattice `⟨γ(Φ)⟩`: the vectors with an integral decomposition. -/
def VSystem.lattice (Φ : RSystem R V) : Set ((R → Option V) → Γ) :=
  {G | ∃ Ψ, S.IsIntDecomp Φ G Ψ}

theorem VSystem.zero_mem_lattice (Φ : RSystem R V) : (0 : (R → Option V) → Γ) ∈ S.lattice Φ :=
  ⟨0, by simp, by funext ψ; simp⟩

end Int

end DesignsII
