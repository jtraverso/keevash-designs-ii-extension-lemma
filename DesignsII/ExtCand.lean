/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import DesignsII.SimpleExt
public import DesignsII.AtomLe
public import DesignsII.ConfigCount
public import DesignsII.ExtTuples

/-!
# Candidate copies from extendability

For a configuration edge `ψ ∈ Φ_B` (`|B| = r`), `candSet` is the set of copies `φ : [q] → [n]`
with `φ ∈ Φ_{[q]}`, `φ|_B = ψ`, every other `r`-restriction in `γ[G]^A`, and no vertex outside
`B` mapped into the fixed set `U`. By extendability (`card_extensions_ge`) and
`card_fix_hit_le` it has at least `ω |V(Φ)|^{q-r} - (q-r) |U| n^{q-r-1}` elements
(`card_candSet_ge`), and at most `n^{q-r}` (`card_candSet_le`). Its members are injective
`Φ`-embeddings of `Σ^≤` (`isEmbedding_sigmaLe`).
-/

@[expose] public section

namespace DesignsII

open Finset

section General

variable {R V : Type*} [DecidableEq R] [Fintype R] [Fintype V] [DecidableEq V]

omit [Fintype V] [DecidableEq V] in
theorem injective_of_maps_univ {Φ : RSystem R V} {φ : R → V}
    (h : restrictT φ univ ∈ Φ.maps univ) : Function.Injective φ := by
  intro x y hxy
  exact Φ.inj univ _ h x y (by simp [restrictT, restrict])
    (by simp [restrictT, restrict, hxy])

omit [Fintype V] [DecidableEq V] in
/-- A map in `Φ_R` of a complex adapted to `Σ` is an embedding of `Σ^≤`. -/
theorem isEmbedding_sigmaLe {Φ : RSystem R V} {Sg : Subgroup (Equiv.Perm R)}
    (hΦc : Φ.IsComplex) (hΦa : IsAdapted Φ Sg) {φ : R → V}
    (h : restrictT φ univ ∈ Φ.maps univ) : IsEmbedding (sigmaLe Sg) Φ φ := by
  refine ⟨(injective_of_maps_univ h).injOn, fun B θ hθ => ?_⟩
  obtain ⟨σ, hσ, rfl⟩ := hθ
  have h1 := hΦc univ (B.map σ.toEmbedding) (subset_univ _) _ h
  have h2 := hΦa σ hσ B _ h1
  convert h2 using 1
  funext x
  by_cases hx : x ∈ B
  · have : σ x ∈ B.map σ.toEmbedding := mem_map_of_mem _ hx
    simp [comp, restrict, relabel, restrictT, hx, this]
  · simp [comp, restrict, relabel, hx]

omit [Fintype R] [Fintype V] [DecidableEq V] in
theorem eq_restrictT {ψ : R → Option V} {B : Finset R} (hd : dom ψ = B) {φ : R → V}
    (h : ∀ x ∈ B, ψ x = some (φ x)) : ψ = restrictT φ B := by
  funext x
  by_cases hx : x ∈ B
  · simp [restrictT, restrict, hx, h x hx]
  · have : x ∉ dom ψ := by rw [hd]; exact hx
    simp only [dom, Set.mem_ofPred_eq, ne_eq, not_not] at this
    simp [restrictT, restrict, hx, this]

end General

namespace TParams

variable {P : TParams} {D r : ℕ}

open Classical in
/-- The candidate copies for a configuration edge `ψ ∈ Φ_B`. -/
noncomputable def candSet (S : VSystem (Fin P.q) (Fin P.NA) (Fin D → ℤ) r)
    (Sg : Subgroup (Equiv.Perm (Fin P.q))) (Φ : RSystem (Fin P.q) (Fin P.n))
    (G : (Fin P.q → Option (Fin P.n)) → (Fin D → ℤ)) (A : Fin P.NA) (U : Finset (Fin P.n))
    (B : Finset (Fin P.q)) (ψ : Fin P.q → Option (Fin P.n)) : Finset (Fin P.q → Fin P.n) :=
  univ.filter fun φ => (restrictT φ univ ∈ Φ.maps univ ∧ (∀ x ∈ B, ψ x = some (φ x)) ∧
    ∀ B' : Finset (Fin P.q), B'.card = r → ¬ B' ⊆ B → restrictT φ B' ∈ gammaG S Sg Φ G A) ∧
      ∀ x ∉ B, φ x ∉ U

open Classical in
/-- **Many candidate copies.** -/
theorem card_candSet_ge (S : VSystem (Fin P.q) (Fin P.NA) (Fin D → ℤ) r)
    (Sg : Subgroup (Equiv.Perm (Fin P.q))) (Φ : RSystem (Fin P.q) (Fin P.n)) (hΦc : Φ.IsComplex)
    (G : (Fin P.q → Option (Fin P.n)) → (Fin D → ℤ)) {ω : ℝ} {hh : ℕ} (hh0 : 0 < hh)
    (hext : IsExtendableRel (r := r) Φ (gammaG S Sg Φ G) ω hh) (A : Fin P.NA)
    (U : Finset (Fin P.n)) {B : Finset (Fin P.q)} {ψ : Fin P.q → Option (Fin P.n)}
    (hψ : ψ ∈ Φ.maps B) (hn : 0 < P.n) :
    ω * ((vertices Φ).toFinset.card : ℝ) ^ (P.q - B.card) -
        ((P.q - B.card) * (U.card * P.n ^ (P.q - B.card - 1)) : ℕ) ≤
      ((candSet S Sg Φ G A U B ψ).card : ℝ) := by
  set v₀ : Fin P.n := ⟨0, hn⟩
  have h1 := card_extensions_ge Φ hΦc (gammaG S Sg Φ G) hh0 hext A hψ v₀
  rw [Fintype.card_fin] at h1
  set c : Fin P.q → Fin P.n := fun x => (ψ x).getD v₀
  have h2 := card_fix_hit_le B c U
  rw [Fintype.card_fin, Fintype.card_fin] at h2
  have hsub : (univ.filter fun φ : Fin P.q → Fin P.n => restrictT φ univ ∈ Φ.maps univ ∧
      (∀ x ∈ B, ψ x = some (φ x)) ∧
      ∀ B' : Finset (Fin P.q), B'.card = r → ¬ B' ⊆ B → restrictT φ B' ∈ gammaG S Sg Φ G A) ⊆
      candSet S Sg Φ G A U B ψ ∪
        univ.filter fun g : Fin P.q → Fin P.n => (∀ w ∈ B, g w = c w) ∧ ∃ x ∉ B, g x ∈ U := by
    intro φ hφ
    have hφ' := (mem_filter.1 hφ).2
    by_cases hU : ∀ x ∉ B, φ x ∉ U
    · exact mem_union_left _ (mem_filter.2 ⟨mem_univ _, hφ', hU⟩)
    · push Not at hU
      refine mem_union_right _ (mem_filter.2 ⟨mem_univ _, fun w hw => ?_, hU⟩)
      simp [c, hφ'.2.1 w hw]
  have h2' : (univ.filter fun g : Fin P.q → Fin P.n =>
      (∀ w ∈ B, g w = c w) ∧ ∃ x ∉ B, g x ∈ U).card ≤
      (P.q - B.card) * (U.card * P.n ^ (P.q - B.card - 1)) := by
    convert h2 using 2; ext; simp only [mem_filter]
  have h3 := (card_le_card hsub).trans (card_union_le _ _)
  have h3' : ((univ.filter fun φ : Fin P.q → Fin P.n => restrictT φ univ ∈ Φ.maps univ ∧
      (∀ x ∈ B, ψ x = some (φ x)) ∧
      ∀ B' : Finset (Fin P.q), B'.card = r → ¬ B' ⊆ B → restrictT φ B' ∈ gammaG S Sg Φ G A).card
        : ℝ) ≤ ((candSet S Sg Φ G A U B ψ).card : ℝ) +
          ((P.q - B.card) * (U.card * P.n ^ (P.q - B.card - 1)) : ℕ) := by
    exact_mod_cast h3.trans (Nat.add_le_add_left h2' _)
  have h1' : ω * ((vertices Φ).toFinset.card : ℝ) ^ (P.q - B.card) ≤
      ((univ.filter fun φ : Fin P.q → Fin P.n => restrictT φ univ ∈ Φ.maps univ ∧
      (∀ x ∈ B, ψ x = some (φ x)) ∧
      ∀ B' : Finset (Fin P.q), B'.card = r → ¬ B' ⊆ B → restrictT φ B' ∈ gammaG S Sg Φ G A).card
        : ℝ) := by
    convert h1 using 3; ext; simp only [mem_filter]
  linarith

open Classical in
/-- At most `n^{q-|B|}` candidates. -/
theorem card_candSet_le (S : VSystem (Fin P.q) (Fin P.NA) (Fin D → ℤ) r)
    (Sg : Subgroup (Equiv.Perm (Fin P.q))) (Φ : RSystem (Fin P.q) (Fin P.n))
    (G : (Fin P.q → Option (Fin P.n)) → (Fin D → ℤ)) (A : Fin P.NA) (U : Finset (Fin P.n))
    (B : Finset (Fin P.q)) (ψ : Fin P.q → Option (Fin P.n)) (hn : 0 < P.n) :
    (candSet S Sg Φ G A U B ψ).card ≤ P.n ^ (P.q - B.card) := by
  set c : Fin P.q → Fin P.n := fun x => (ψ x).getD ⟨0, hn⟩
  have := card_fix_on B c
  rw [Fintype.card_fin, Fintype.card_fin] at this
  refine (card_le_card fun φ hφ => ?_).trans this.le
  simp only [mem_filter]
  refine ⟨mem_univ _, fun w hw => ?_⟩
  simp [c, (mem_filter.1 hφ).2.1.2.1 w hw]

end TParams

end DesignsII
