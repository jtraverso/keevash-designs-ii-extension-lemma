/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import DesignsII.ExtDefs
public import DesignsII.Complex

/-!
# Adapted complexes (Keevash, *The existence of designs II*, §2.3)

For a permutation group `Σ ≤ Sym(R)` and a labelled map `φ` with domain `σ(B)`, the relabelling
`φσ = φ ∘ σ|_B` has domain `B`. An `R`-complex is `Σ`-adapted if it is closed under relabelling
(Definition 2.11). The orbit of `ψ` is `{ψσ : σ ∈ Σ, σ(B) = dom ψ}` (Definition 2.12).

* `relabel φ σ B` : `φσ` restricted to `B` (only meaningful when `dom φ = σ(B)`);
* `IsAdapted Φ Σ` : Definition 2.11;
* `nhood_isAdapted` : Lemma 2.14 for the stabiliser of `B*`, acting on labels outside `B*`.
-/

@[expose] public section

namespace DesignsII

open Finset

variable {R V : Type*} [DecidableEq R]

theorem dom_relabel {φ : R → Option V} {σ : Equiv.Perm R} {B : Finset R}
    (hφ : dom φ = B.map σ.toEmbedding) : dom (relabel φ σ B) = B := by
  ext x
  simp only [dom, relabel, Set.mem_ofPred_eq, mem_coe]
  by_cases h : x ∈ B
  · simp only [h, ite_true, ne_eq]
    have : σ x ∈ dom φ := by
      rw [hφ, coe_map]; exact ⟨x, h, rfl⟩
    exact iff_true_intro this
  · simp [h]

theorem injOnDom_relabel {φ : R → Option V} (hφ : InjOnDom φ) (σ : Equiv.Perm R)
    (B : Finset R) : InjOnDom (relabel φ σ B) := by
  intro x y hx hxy
  unfold relabel at hx hxy
  by_cases h1 : x ∈ B
  · by_cases h2 : y ∈ B
    · simp only [h1, h2, ite_true] at hx hxy
      exact σ.injective (hφ _ _ hx hxy)
    · simp only [h1, h2, ite_true, ite_false] at hx hxy
      exact absurd hxy hx
  · simp [h1] at hx

/-- The stabiliser of `B*` in `Σ` (pointwise), acting on the labels outside `B*`. -/
def fixing (Sg : Subgroup (Equiv.Perm R)) (Bs : Finset R) : Subgroup (Equiv.Perm R) where
  carrier := {σ | σ ∈ Sg ∧ ∀ x ∈ Bs, σ x = x}
  mul_mem' ha hb := ⟨Sg.mul_mem ha.1 hb.1, fun x hx => by
    simp [Equiv.Perm.mul_apply, hb.2 x hx, ha.2 x hx]⟩
  one_mem' := ⟨Sg.one_mem, fun _ _ => rfl⟩
  inv_mem' ha := ⟨Sg.inv_mem ha.1, fun x hx => by
    rw [Equiv.Perm.inv_eq_iff_eq]; exact (ha.2 x hx).symm⟩

theorem map_union_fixing {σ : Equiv.Perm R} {Bs : Finset R} (hσ : ∀ x ∈ Bs, σ x = x)
    (B : Finset R) : (B ∪ Bs).map σ.toEmbedding = B.map σ.toEmbedding ∪ Bs := by
  rw [map_union]
  congr 1
  ext y
  simp only [mem_map, Equiv.coe_toEmbedding]
  constructor
  · rintro ⟨x, hx, rfl⟩; rw [hσ x hx]; exact hx
  · intro hy; exact ⟨y, hy, hσ y hy⟩

/-- **Lemma 2.14**: the neighbourhood of a `Σ`-adapted complex is adapted to the pointwise
stabiliser of `B*`. -/
theorem nhood_isAdapted {Φ : RSystem R V} {Sg : Subgroup (Equiv.Perm R)} (hΦ : IsAdapted Φ Sg)
    (Bs : Finset R) (φs : R → Option V) : IsAdapted (Φ.nhood Bs φs) (fixing Sg Bs) := by
  intro σ hσ B ψ hψ
  obtain ⟨hdisj, φ, hφ, hφs, rfl⟩ := hψ
  have hdisjB : Disjoint B Bs := by
    rw [disjoint_left] at hdisj ⊢
    intro x hx hxs
    exact hdisj (mem_map.2 ⟨x, hx, by simpa using hσ.2 x hxs⟩) hxs
  rw [← map_union_fixing hσ.2] at hφ
  refine ⟨hdisjB, relabel φ σ (B ∪ Bs), hΦ σ hσ.1 _ φ hφ, ?_, ?_⟩
  · rw [← hφs]
    funext x
    unfold restrict relabel
    by_cases hx : x ∈ Bs
    · simp [hx, hσ.2 x hx]
    · simp [hx]
  · funext x
    unfold restrict relabel
    by_cases hx : x ∈ B
    · simp [hx]
    · simp [hx]

end DesignsII
