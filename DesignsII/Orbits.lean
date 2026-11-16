/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import DesignsII.Adapted

/-!
# Orbits of labelled maps form a partition

For a permutation group `Σ` the orbits `orbit Σ ψ B` (`ψ` with domain `B`) are the classes of an
equivalence relation:

* `relabel_relabel`, `relabel_one`: relabelling is a right action;
* `mem_orbit_self`, `orbit_relabel`: `ψ ∈ orbit ψ`, and the orbit of any member is the same set;
* `orbit_eq_of_mem_both`: two orbits sharing a map coincide.
-/

@[expose] public section

namespace DesignsII

open Finset

variable {R V : Type*} [DecidableEq R]

theorem relabel_relabel (ψ : R → Option V) (σ τ : Equiv.Perm R) {B' B'' : Finset R}
    (h : B''.map τ.toEmbedding = B') :
    relabel (relabel ψ σ B') τ B'' = relabel ψ (σ * τ) B'' := by
  funext x
  unfold relabel
  by_cases hx : x ∈ B''
  · have : τ x ∈ B' := h ▸ mem_map_of_mem _ hx
    simp [hx, this, Equiv.Perm.mul_apply]
  · simp [hx]

theorem relabel_one {ψ : R → Option V} {B : Finset R} (h : dom ψ = B) :
    relabel ψ 1 B = ψ := by
  funext x
  unfold relabel
  by_cases hx : x ∈ B
  · simp [hx]
  · have : x ∉ dom ψ := by rw [h]; exact hx
    simp only [dom, Set.mem_setOf_eq, ne_eq, not_not] at this
    simp [hx, this]

theorem map_mul_toEmbedding (σ τ : Equiv.Perm R) (B : Finset R) :
    B.map (σ * τ).toEmbedding = (B.map τ.toEmbedding).map σ.toEmbedding := by
  rw [map_map]
  rfl

theorem mem_orbit_self (Sg : Subgroup (Equiv.Perm R)) {ψ : R → Option V} {B : Finset R}
    (h : dom ψ = B) : ψ ∈ orbit Sg ψ B :=
  ⟨1, Sg.one_mem, B, by ext x; rw [mem_map_equiv]; rfl, (relabel_one h).symm⟩

/-- **The orbit of a member is the same orbit.** -/
theorem orbit_relabel (Sg : Subgroup (Equiv.Perm R)) {ψ : R → Option V} {σ : Equiv.Perm R}
    (hσ : σ ∈ Sg) {B B' : Finset R} (hB' : B'.map σ.toEmbedding = B) :
    orbit Sg (relabel ψ σ B') B' = orbit Sg ψ B := by
  ext χ
  constructor
  · rintro ⟨τ, hτ, B'', hB'', rfl⟩
    refine ⟨σ * τ, Sg.mul_mem hσ hτ, B'', ?_, relabel_relabel ψ σ τ hB''⟩
    rw [map_mul_toEmbedding, hB'', hB']
  · rintro ⟨ρ, hρ, B'', hB'', rfl⟩
    refine ⟨σ⁻¹ * ρ, Sg.mul_mem (Sg.inv_mem hσ) hρ, B'', ?_, ?_⟩
    · rw [map_mul_toEmbedding, hB'', ← hB', ← map_mul_toEmbedding, inv_mul_cancel]
      ext x; rw [mem_map_equiv]; rfl
    · rw [relabel_relabel ψ σ _ (by
        rw [map_mul_toEmbedding, hB'', ← hB', ← map_mul_toEmbedding, inv_mul_cancel]
        ext x; rw [mem_map_equiv]; rfl), mul_inv_cancel_left]

/-- **Orbits sharing a map coincide.** -/
theorem orbit_eq_of_mem_both (Sg : Subgroup (Equiv.Perm R)) {ψ ψ' χ : R → Option V}
    {B B' : Finset R} (hψ : dom ψ = B) (hψ' : dom ψ' = B')
    (h : χ ∈ orbit Sg ψ B) (h' : χ ∈ orbit Sg ψ' B') : orbit Sg ψ B = orbit Sg ψ' B' := by
  obtain ⟨σ, hσ, B₁, hB₁, rfl⟩ := h
  obtain ⟨σ', hσ', B₂, hB₂, he⟩ := h'
  have hd1 : dom (relabel ψ σ B₁) = B₁ := dom_relabel (by rw [hψ, hB₁])
  have hd2 : dom (relabel ψ' σ' B₂) = B₂ := dom_relabel (by rw [hψ', hB₂])
  have hB : B₁ = B₂ := by
    have := hd1; rw [he, hd2] at this; exact_mod_cast this.symm
  subst hB
  rw [← orbit_relabel Sg hσ hB₁, ← orbit_relabel Sg hσ' hB₂, he]

end DesignsII
