/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import DesignsII.AtomDecomp

/-!
# Atoms of copies extending a map (Lemma 2.21 (ii))

For the family member `A = Σ^≤` and an injective `φ : R → V`, the restriction of the molecule
`γ(φ)` to the orbit of `ψ = φ|_B` (`|B| = r`) is the atom `γ(ψ)` (`moleculeP`):
`onOrbit_molecule_restrict`. In Lemma `ext*` this shows that every copy `φ` with `a₀ φ = A`
extending the labelled map `ψ_{b,i}` satisfies the witness predicate `atomQ`.
-/

@[expose] public section

namespace DesignsII

open Finset

variable {R V ι : Type*} [DecidableEq R] {D r : ℕ}

/-- The labelled map `φ|_B`. -/
def restrictT (φ : R → V) (B : Finset R) : R → Option V := restrict (fun x => some (φ x)) B

theorem mem_sigmaLe {Sg : Subgroup (Equiv.Perm R)} {B' : Finset R} {θ : R → Option R} :
    θ ∈ (sigmaLe Sg).maps B' ↔ ∃ σ ∈ Sg, θ = restrict (fun x => some (σ x)) B' := Iff.rfl

variable (S : VSystem R ι (Fin D → ℤ) r) (Sg : Subgroup (Equiv.Perm R)) {i : ι}
  (hA : S.A i = sigmaLe Sg) {φ : R → V} (hφ : Function.Injective φ) {B : Finset R}

include hA in
theorem mapsR_sigmaLe {θ : R → Option R} :
    θ ∈ S.mapsR i ↔ ∃ B' : Finset R, B'.card = r ∧ ∃ σ ∈ Sg,
      θ = restrict (fun x => some (σ x)) B' := by
  simp only [VSystem.mapsR, Set.mem_ofPred_eq, hA, mem_sigmaLe]

/-- `compP ψ θ` for `θ = σ|_{B'}`. -/
theorem compP_restrict (ψ : R → Option V) (σ : Equiv.Perm R) (B' : Finset R) :
    compP ψ (restrict (fun x => some (σ x)) B') = relabel ψ σ B' := by
  funext x
  simp only [compP, restrict, relabel]
  split_ifs <;> simp

/-- `comp φ θ` for `θ = σ|_{B'}`. -/
theorem comp_restrict (σ : Equiv.Perm R) (B' : Finset R) :
    comp φ (restrict (fun x => some (σ x)) B') = relabel (fun x => some (φ x)) σ B' := by
  funext x
  simp only [comp, restrict, relabel]
  split_ifs <;> simp

/-- If `σ` maps `B'` into `B`, relabelling `φ|_B` agrees with relabelling `φ`. -/
theorem relabel_restrictT {σ : Equiv.Perm R} {B' : Finset R}
    (h : ∀ x ∈ B', σ x ∈ B) :
    relabel (restrictT φ B) σ B' = relabel (fun x => some (φ x)) σ B' := by
  funext x
  simp only [relabel, restrictT, restrict]
  split_ifs with h1 h2 <;> simp_all

theorem map_eq_of_subset {σ : Equiv.Perm R} {B' : Finset R} (h : ∀ x ∈ B', σ x ∈ B)
    (hcard : B'.card = B.card) : B'.map σ.toEmbedding = B := by
  refine eq_of_subset_of_card_le (fun y hy => ?_) (by rw [card_map, hcard])
  obtain ⟨x, hx, rfl⟩ := mem_map.1 hy
  exact h x hx

include hA hφ in
/-- **Lemma 2.21 (ii).** -/
theorem onOrbit_molecule_restrict (hB : B.card = r) :
    onOrbit Sg (S.molecule i φ) (restrictT φ B) B = moleculeP S i (restrictT φ B) := by
  classical
  funext χ
  unfold onOrbit
  split_ifs with hχ
  · -- inside the orbit: the index sets coincide
    obtain ⟨τ, hτ, B'', hB'', rfl⟩ := hχ
    unfold VSystem.molecule moleculeP
    refine finsum_mem_congr ?_ fun _ _ => rfl
    ext θ
    simp only [Set.mem_ofPred_eq]
    constructor
    · rintro ⟨hθ, hcomp⟩
      obtain ⟨B', hB', σ, hσ, rfl⟩ := (mapsR_sigmaLe S Sg hA).1 hθ
      have hτB : ∀ x ∈ B'', τ x ∈ B := fun x hx => hB'' ▸ mem_map_of_mem _ hx
      have hsub : ∀ x ∈ B', σ x ∈ B := by
        intro x hx
        have h1 := congrFun hcomp x
        rw [comp_restrict, relabel_restrictT hτB] at h1
        simp only [relabel, hx, if_true] at h1
        split_ifs at h1 with hx''
        · rw [hφ (Option.some.inj h1)]; exact hτB x hx''
      refine ⟨hθ, fun x a hxa => ?_, ?_⟩
      · simp only [restrict] at hxa
        split_ifs at hxa with hx
        · obtain rfl := Option.some.inj hxa
          simp [restrictT, restrict, hsub x hx]
      · rw [compP_restrict, relabel_restrictT hsub, ← comp_restrict, hcomp,
          relabel_restrictT hτB]
    · rintro ⟨hθ, hdom, hcomp⟩
      obtain ⟨B', hB', σ, hσ, rfl⟩ := (mapsR_sigmaLe S Sg hA).1 hθ
      have hsub : ∀ x ∈ B', σ x ∈ B := by
        intro x hx
        have := hdom x (σ x) (by simp [restrict, hx])
        by_contra hn
        exact this (by simp [restrictT, restrict, hn])
      refine ⟨hθ, ?_⟩
      rw [comp_restrict, ← relabel_restrictT hsub, ← compP_restrict, hcomp]
  · -- outside the orbit: no index
    unfold moleculeP
    rw [show {θ | θ ∈ S.mapsR i ∧ (∀ x a, θ x = some a → restrictT φ B a ≠ none) ∧
        compP (restrictT φ B) θ = χ} = (∅ : Set (R → Option R)) from ?_]
    · exact finsum_mem_empty.symm
    refine Set.eq_empty_of_forall_notMem fun θ ⟨hθ, hdom, hcomp⟩ => hχ ?_
    obtain ⟨B', hB', σ, hσ, rfl⟩ := (mapsR_sigmaLe S Sg hA).1 hθ
    have hsub : ∀ x ∈ B', σ x ∈ B := by
      intro x hx
      have := hdom x (σ x) (by simp [restrict, hx])
      by_contra hn
      exact this (by simp [restrictT, restrict, hn])
    refine ⟨σ, hσ, B', map_eq_of_subset hsub (by rw [hB', hB]), ?_⟩
    rw [← hcomp, compP_restrict]

end DesignsII
