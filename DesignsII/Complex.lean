/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import DesignsII.ExtDefs
public import Mathlib

/-!
# Labelled complexes (Keevash, *The existence of designs II*, §2.1)

A labelled map with labels in `R` and values in `V` is a partial map `φ : R → Option V`; its
domain is `dom φ = {x | φ x ≠ none}` and it is injective on its domain. An `R`-system on `V`
assigns to every finite `B ⊆ R` a set `Φ B` of injective labelled maps with domain `B`; it is an
`R`-complex if it is closed under restriction (Definition 2.1).

* `restrict φ B` : the restriction of `φ` to `B`;
* `RSystem.restrictTo Φ Φ'` : `Φ[Φ']` (Definition 2.2), an `R`-complex (Lemma 2.3);
* `RSystem.nhood Φ φ*` : the neighbourhood `Φ/φ*` (Definition 2.5), an `(R ∖ B*)`-complex
  (Lemma 2.6), here with labels in `R` and domains disjoint from `B*`.
-/

@[expose] public section

namespace DesignsII

open Finset

variable {R V : Type*} [DecidableEq R]

theorem restrict_restrict (φ : R → Option V) (B B' : Finset R) :
    restrict (restrict φ B) B' = restrict φ (B ∩ B') := by
  funext x
  unfold restrict
  by_cases h : x ∈ B <;> by_cases h' : x ∈ B' <;> simp [h, h']

theorem mem_dom_restrict (φ : R → Option V) (B : Finset R) (x : R) :
    x ∈ dom (restrict φ B) ↔ x ∈ B ∧ x ∈ dom φ := by
  unfold dom restrict
  by_cases h : x ∈ B <;> simp [h]

theorem dom_restrict {φ : R → Option V} {B B' : Finset R} (hφ : dom φ = B) (hB' : B' ⊆ B) :
    dom (restrict φ B') = B' := by
  ext x
  rw [mem_dom_restrict, hφ, mem_coe, mem_coe]
  exact ⟨fun h => h.1, fun h => ⟨h, hB' h⟩⟩

namespace RSystem

/-- `Φ[Φ']` (Definition 2.2): the maps of `Φ` all of whose restrictions to sets `B'` on which
`Φ'` is defined (`def' B'`) lie in `Φ'`. -/
def restrictTo (Φ : RSystem R V) (Φ' : Finset R → Set (R → Option V))
    (def' : Finset R → Prop) : RSystem R V where
  maps B := {φ | φ ∈ Φ.maps B ∧ ∀ B', B' ⊆ B → def' B' → restrict φ B' ∈ Φ' B'}
  dom_eq B φ h := Φ.dom_eq B φ h.1
  inj B φ h := Φ.inj B φ h.1

/-- **Lemma 2.3**: `Φ[Φ']` is an `R`-complex. -/
theorem restrictTo_isComplex {Φ : RSystem R V} (hΦ : Φ.IsComplex)
    (Φ' : Finset R → Set (R → Option V)) (def' : Finset R → Prop) :
    (Φ.restrictTo Φ' def').IsComplex := by
  intro B B' hB φ hφ
  refine ⟨hΦ B B' hB φ hφ.1, fun B'' hB'' hdef => ?_⟩
  rw [restrict_restrict, inter_eq_right.2 hB'']
  exact hφ.2 B'' (hB''.trans hB) hdef

/-- The neighbourhood `Φ/φ*` (Definition 2.5): for `B` disjoint from `B* = dom φ*`, the
restrictions to `B` of the maps of `Φ` on `B ∪ B*` extending `φ*`. -/
def nhood (Φ : RSystem R V) (Bs : Finset R) (φs : R → Option V) : RSystem R V where
  maps B := {ψ | Disjoint B Bs ∧ ∃ φ ∈ Φ.maps (B ∪ Bs), restrict φ Bs = φs ∧ ψ = restrict φ B}
  dom_eq B ψ h := by
    obtain ⟨-, φ, hφ, -, rfl⟩ := h
    exact dom_restrict (Φ.dom_eq _ φ hφ) subset_union_left
  inj B ψ h := by
    obtain ⟨-, φ, hφ, -, rfl⟩ := h
    exact injOnDom_restrict (Φ.inj _ φ hφ) B

/-- **Lemma 2.6**: `Φ/φ*` is a complex. -/
theorem nhood_isComplex {Φ : RSystem R V} (hΦ : Φ.IsComplex) (Bs : Finset R)
    (φs : R → Option V) : (Φ.nhood Bs φs).IsComplex := by
  intro B B' hB ψ hψ
  obtain ⟨hdisj, φ, hφ, hφs, rfl⟩ := hψ
  refine ⟨hdisj.mono_left hB, restrict φ (B' ∪ Bs),
    hΦ _ _ (union_subset_union hB subset_rfl) φ hφ, ?_, ?_⟩
  · rw [restrict_restrict, inter_eq_right.2 subset_union_right, hφs]
  · rw [restrict_restrict, restrict_restrict, inter_eq_right.2 hB,
      inter_eq_right.2 subset_union_left]

end RSystem

end DesignsII
