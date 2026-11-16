/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import DesignsII.ExtDefs
public import DesignsII.Complex

/-!
# Embeddings, extensions and extendability (Keevash, *The existence of designs II*, §2.2)

* `vertices Φ` : `V(Φ)`, the values of the maps of `Φ`;
* `IsEmbedding H Φ f` : `f` is a `Φ`-embedding of `H` (injective on `V(H)`, and `f ∘ ψ ∈ Φ` for
  every `ψ ∈ H`);
* `partiteMaps R S` : the complex `R(S)` of partite maps `R → R × S`;
* `extCount H F φ Φ` : `X_E(Φ)` for the extension `E = (H, F, φ)`, the number of `Φ`-embeddings of
  `H` that agree with `φ` on `F` (counted on `V(H)`);
* `IsExtendable Φ ω s` : every `Φ`-extension of rank `s` is `ω`-dense (Definition 2.8).

Embeddings are total maps `W → V`; only their values on `V(H)` matter, and `extCount` counts
their restrictions to `V(H)`.
-/

@[expose] public section

namespace DesignsII

open Finset

variable {R V W : Type*} [DecidableEq R]

omit [DecidableEq R] in
theorem dom_comp (f : W → V) (ψ : R → Option W) : dom (comp f ψ) = dom ψ := by
  ext x
  simp [dom, comp]

theorem partiteMaps_isComplex (S : Type*) : (partiteMaps R S).IsComplex := by
  intro B B' hB ψ hψ
  refine ⟨dom_restrict hψ.1 hB, fun i p hp => ?_⟩
  unfold restrict at hp
  split_ifs at hp
  exact hψ.2 i p hp

variable [Fintype W] [DecidableEq W] [Fintype V] [DecidableEq V]

open Classical in
/-- `X_E(Φ)` for `E = (H, F, φ)`: the number of `Φ`-embeddings of `H` agreeing with `φ` on `F`,
counted by their restrictions to `V(H) = VH`. -/
noncomputable def extCount (H : RSystem R W) (VH F : Finset W) (φ : W → V) (Φ : RSystem R V) :
    ℕ :=
  ((univ.filter fun f : W → V => IsEmbedding H Φ f ∧ ∀ w ∈ F, f w = φ w).image
    fun f (w : VH) => f w).card

open Classical in
/-- `Φ` is `(ω, s)`-extendable: for every complex `H ⊆ R(Fin s)` (with vertex set `VH`), every
`F ⊆ V(H)` and every `Φ`-embedding `φ` of `H[F]`, `X_E(Φ) ≥ ω |V(Φ)|^{|V(H) ∖ F|}`. -/
def IsExtendable [Fintype R] (Φ : RSystem R V) (ω : ℝ) (s : ℕ) : Prop :=
  ∀ (H : RSystem R (R × Fin s)) (VH F : Finset (R × Fin s)) (φ : R × Fin s → V),
    H.IsComplex → (∀ B, H.maps B ⊆ (partiteMaps R (Fin s)).maps B) →
    vertices H = VH → F ⊆ VH → IsEmbedding (H.induce F) Φ φ →
    ω * ((vertices Φ).toFinset.card : ℝ) ^ (VH \ F).card ≤
      extCount H VH F φ Φ

end DesignsII
