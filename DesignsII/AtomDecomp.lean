/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import DesignsII.Orbits
public import DesignsII.MainStatement

/-!
# Molecules are sums of atoms

* `sum_onOrbit_rep`: any vector `J` on labelled maps is the sum of its restrictions to the orbits
  of a set of orbit representatives of its support;
* `molecule_isAtomSum`: for a `Φ`-embedding `φ` of `A i` into a `Σ`-adapted complex, the molecule
  `γ(φ)` is a sum of `γ`-atoms (its nonzero restrictions to orbits);
* `leGamma_onOrbit_boundary`: **the template bridge** — if `p₀ ∈ M*` then every restriction
  `γ(p₀)^{ψΣ}` of its molecule to an orbit satisfies `γ(p₀)^{ψΣ} ≤_γ ∂^γ M*`. In Lemma `ext*` this
  turns "the copy covering `Im(φ⁺ψ')` has atom `γ(φ⁺ψ')` there" into
  `φ⁺ψ' ∈ γ[∂^γ M*]`.
-/

@[expose] public section

namespace DesignsII

open Finset

variable {R V ι : Type*} [DecidableEq R] [Fintype R] [Fintype V] [DecidableEq V] {D r : ℕ}

/-- The domain of a labelled map, as a finset. -/
def domF (ψ : R → Option V) : Finset R := univ.filter fun x => ψ x ≠ none

omit [DecidableEq V] in
theorem dom_eq_domF (ψ : R → Option V) : dom ψ = (domF ψ : Set R) := by
  ext x; simp [dom, domF]

omit [DecidableEq V] in
theorem domF_eq {ψ : R → Option V} {B : Finset R} (h : dom ψ = B) : domF ψ = B := by
  rw [dom_eq_domF] at h; exact_mod_cast h

variable (Sg : Subgroup (Equiv.Perm R))

/-- A canonical representative of the orbit of `ψ`. -/
noncomputable def rep (ψ : R → Option V) : R → Option V :=
  Classical.epsilon fun χ => χ ∈ orbit Sg ψ (domF ψ)

omit [DecidableEq V] in
theorem rep_mem (ψ : R → Option V) : rep Sg ψ ∈ orbit Sg ψ (domF ψ) :=
  Classical.epsilon_spec ⟨ψ, mem_orbit_self Sg (dom_eq_domF ψ)⟩

omit [DecidableEq V] in
theorem orbit_rep (ψ : R → Option V) :
    orbit Sg (rep Sg ψ) (domF (rep Sg ψ)) = orbit Sg ψ (domF ψ) :=
  orbit_eq_of_mem_both Sg (dom_eq_domF _) (dom_eq_domF _)
    (mem_orbit_self Sg (dom_eq_domF _)) (rep_mem Sg ψ)

omit [DecidableEq V] in
theorem rep_eq {ψ ψ' : R → Option V} (h : orbit Sg ψ (domF ψ) = orbit Sg ψ' (domF ψ')) :
    rep Sg ψ = rep Sg ψ' := by
  unfold rep; rw [h]

omit [DecidableEq V] in
/-- `ψ ∈ orbit ρ` forces `ρ`'s representative to be `ψ`'s. -/
theorem rep_eq_of_mem {ψ χ : R → Option V} (h : ψ ∈ orbit Sg (rep Sg χ) (domF (rep Sg χ))) :
    rep Sg ψ = rep Sg χ := by
  refine rep_eq Sg ?_
  rw [← orbit_rep Sg χ]
  exact orbit_eq_of_mem_both Sg (dom_eq_domF _) (dom_eq_domF _)
    (mem_orbit_self Sg (dom_eq_domF ψ)) h

omit [DecidableEq V] in
theorem mem_orbit_rep (ψ : R → Option V) : ψ ∈ orbit Sg (rep Sg ψ) (domF (rep Sg ψ)) := by
  rw [orbit_rep]; exact mem_orbit_self Sg (dom_eq_domF ψ)

/-- **Decomposition into orbit pieces.** -/
theorem sum_onOrbit_rep {M : Type*} [AddCommMonoid M] [DecidableEq M] (J : (R → Option V) → M) :
    J = ∑ ρ ∈ (univ.filter fun χ => J χ ≠ 0).image (rep Sg),
      onOrbit Sg J ρ (domF ρ) := by
  funext ψ
  rw [Finset.sum_apply]
  unfold onOrbit
  by_cases hJ : J ψ = 0
  · rw [hJ]
    exact (sum_eq_zero fun ρ _ => by simp [hJ]).symm
  · rw [sum_eq_single (rep Sg ψ)]
    · simp [mem_orbit_rep Sg ψ]
    · intro ρ hρ hne
      obtain ⟨χ, -, rfl⟩ := mem_image.1 hρ
      have : ψ ∉ orbit Sg (rep Sg χ) (domF (rep Sg χ)) := fun h =>
        hne (rep_eq_of_mem Sg h).symm
      simp [this]
    · intro h
      exact absurd (mem_image_of_mem (rep Sg) (mem_filter.2 ⟨mem_univ ψ, hJ⟩)) h

/-! ### Atom sums -/

variable (S : VSystem R ι (Fin D → ℤ) r) (Φ : RSystem R V)

/-- `v` is the sum of a list of `γ`-atoms. -/
def IsAtomSum (v : (R → Option V) → (Fin D → ℤ)) : Prop :=
  ∃ l : List ((R → Option V) → (Fin D → ℤ)), (∀ a ∈ l, a ∈ atoms S Sg Φ) ∧ v = l.sum

theorem isAtomSum_zero : IsAtomSum Sg S Φ 0 := ⟨[], by simp, by simp⟩

theorem IsAtomSum.add {v w : (R → Option V) → (Fin D → ℤ)} (hv : IsAtomSum Sg S Φ v)
    (hw : IsAtomSum Sg S Φ w) : IsAtomSum Sg S Φ (v + w) := by
  obtain ⟨l, hl, rfl⟩ := hv
  obtain ⟨l', hl', rfl⟩ := hw
  exact ⟨l ++ l', fun a ha => (List.mem_append.1 ha).elim (hl a) (hl' a), by simp⟩

theorem isAtomSum_of {a : (R → Option V) → (Fin D → ℤ)} (h : a = 0 ∨ a ∈ atoms S Sg Φ) :
    IsAtomSum Sg S Φ a := by
  rcases h with rfl | h
  · exact isAtomSum_zero Sg S Φ
  · exact ⟨[a], by simpa using h, by simp⟩

theorem isAtomSum_sum {α : Type*} (s : Finset α) (f : α → (R → Option V) → (Fin D → ℤ))
    (h : ∀ x ∈ s, IsAtomSum Sg S Φ (f x)) : IsAtomSum Sg S Φ (∑ x ∈ s, f x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using isAtomSum_zero Sg S Φ
  | insert x s hx ih =>
    rw [sum_insert hx]
    exact (h x (mem_insert_self _ _)).add Sg S Φ (ih fun y hy => h y (mem_insert_of_mem hy))

omit [Fintype R] [Fintype V] [DecidableEq V] in
/-- The support of a molecule consists of the maps `φ ∘ θ`, `θ ∈ (A i)_r`. -/
theorem exists_of_molecule_ne_zero {i : ι} {φ : R → V} {χ : R → Option V}
    (h : S.molecule i φ χ ≠ 0) : ∃ θ ∈ S.mapsR i, comp φ θ = χ := by
  by_contra hn
  push Not at hn
  apply h
  unfold VSystem.molecule
  rw [show {θ | θ ∈ S.mapsR i ∧ comp φ θ = χ} = (∅ : Set (R → Option R)) from
    Set.eq_empty_of_forall_notMem fun θ hθ => hn θ hθ.1 hθ.2]
  exact finsum_mem_empty

/-- **A molecule of an embedding is a sum of atoms.** -/
theorem molecule_isAtomSum (hΦ : IsAdapted Φ Sg) {i : ι} {φ : R → V}
    (hφ : IsEmbedding (S.A i) Φ φ) : IsAtomSum Sg S Φ (S.molecule i φ) := by
  rw [sum_onOrbit_rep Sg (S.molecule i φ)]
  refine isAtomSum_sum Sg S Φ _ _ fun ρ hρ => isAtomSum_of Sg S Φ ?_
  by_cases h0 : onOrbit Sg (S.molecule i φ) ρ (domF ρ) = 0
  · exact Or.inl h0
  refine Or.inr ⟨h0, i, φ, hφ, domF ρ, ?_, ρ, ?_, rfl⟩
  all_goals
    obtain ⟨χ, hχ, rfl⟩ := mem_image.1 hρ
    obtain ⟨θ, ⟨B, hB, hθ⟩, hθχ⟩ := exists_of_molecule_ne_zero S (mem_filter.1 hχ).2
    have hχΦ : χ ∈ Φ.maps B := hθχ ▸ hφ.2 B θ hθ
    have hdχ : dom χ = B := Φ.dom_eq B χ hχΦ
    obtain ⟨σ, hσ, B', hB', hrep⟩ := rep_mem Sg χ
    rw [domF_eq hdχ] at hB'
    have hdrep : domF (rep Sg χ) = B' := by
      rw [hrep]; exact domF_eq (dom_relabel (by rw [hdχ, hB']))
  · rw [hdrep, ← hB, ← hB', card_map]
  · rw [hdrep, hrep]
    exact hΦ σ hσ B' χ (by rw [hB']; exact hχΦ)

/-- **The template bridge**: a restriction of the molecule of `p₀ ∈ M*` to an orbit is
`≤_γ ∂^γ M*`. -/
theorem leGamma_onOrbit_boundary [DecidableEq ι] (hΦ : IsAdapted Φ Sg) (Mst : Finset (ι × (R → V)))
    (hM : ∀ p ∈ Mst, IsEmbedding (S.A p.1) Φ p.2) {p₀ : ι × (R → V)} (hp₀ : p₀ ∈ Mst)
    (ψ : R → Option V) :
    LeGamma S Sg Φ (onOrbit Sg (S.molecule p₀.1 p₀.2) ψ (domF ψ)) (S.boundary Mst) := by
  set J := S.molecule p₀.1 p₀.2
  set Reps := (univ.filter fun χ => J χ ≠ 0).image (rep Sg)
  have hbd : S.boundary Mst = J + ∑ p ∈ Mst.erase p₀, S.molecule p.1 p.2 := by
    funext χ
    simp only [VSystem.boundary, Pi.add_apply, Finset.sum_apply]
    rw [← add_sum_erase _ _ hp₀]
  have hrest : IsAtomSum Sg S Φ (∑ p ∈ Mst.erase p₀, S.molecule p.1 p.2) :=
    isAtomSum_sum Sg S Φ _ _ fun p hp =>
      molecule_isAtomSum Sg S Φ hΦ (hM p (mem_of_mem_erase hp))
  have hpieces : ∀ ρ ∈ Reps, IsAtomSum Sg S Φ (onOrbit Sg J ρ (domF ρ)) := by
    intro ρ hρ
    by_cases h0 : onOrbit Sg J ρ (domF ρ) = 0
    · rw [h0]; exact isAtomSum_zero Sg S Φ
    refine isAtomSum_of Sg S Φ (Or.inr ⟨h0, p₀.1, p₀.2, hM p₀ hp₀, domF ρ, ?_, ρ, ?_, rfl⟩)
    all_goals
      obtain ⟨χ, hχ, rfl⟩ := mem_image.1 hρ
      obtain ⟨θ, ⟨B, hB, hθ⟩, hθχ⟩ := exists_of_molecule_ne_zero S (mem_filter.1 hχ).2
      have hχΦ : χ ∈ Φ.maps B := hθχ ▸ (hM p₀ hp₀).2 B θ hθ
      have hdχ : dom χ = B := Φ.dom_eq B χ hχΦ
      obtain ⟨σ, hσ, B', hB', hrep⟩ := rep_mem Sg χ
      rw [domF_eq hdχ] at hB'
      have hdrep : domF (rep Sg χ) = B' := by
        rw [hrep]; exact domF_eq (dom_relabel (by rw [hdχ, hB']))
    · rw [hdrep, ← hB, ← hB', card_map]
    · rw [hdrep, hrep]
      exact hΦ σ hσ B' χ (by rw [hB']; exact hχΦ)
  have hpiece_eq : onOrbit Sg J ψ (domF ψ) = onOrbit Sg J (rep Sg ψ) (domF (rep Sg ψ)) := by
    unfold onOrbit; rw [orbit_rep]
  have hdecomp := sum_onOrbit_rep Sg J
  obtain ⟨l, hl, hsum⟩ : IsAtomSum Sg S Φ (S.boundary Mst - onOrbit Sg J ψ (domF ψ)) := by
    by_cases hmem : rep Sg ψ ∈ Reps
    · have : S.boundary Mst - onOrbit Sg J ψ (domF ψ) =
          (∑ ρ ∈ Reps.erase (rep Sg ψ), onOrbit Sg J ρ (domF ρ)) +
            ∑ p ∈ Mst.erase p₀, S.molecule p.1 p.2 := by
        have key : J = onOrbit Sg J (rep Sg ψ) (domF (rep Sg ψ)) +
            ∑ ρ ∈ Reps.erase (rep Sg ψ), onOrbit Sg J ρ (domF ρ) := by
          exact hdecomp.trans (add_sum_erase Reps (fun ρ => onOrbit Sg J ρ (domF ρ)) hmem).symm
        rw [hbd, hpiece_eq]
        nth_rw 1 [key]
        abel
      rw [this]
      exact (isAtomSum_sum Sg S Φ _ _ fun ρ hρ => hpieces ρ (mem_of_mem_erase hρ)).add
        Sg S Φ hrest
    · have hzero : onOrbit Sg J ψ (domF ψ) = 0 := by
        funext χ
        unfold onOrbit
        split_ifs with hχ
        · by_contra hJχ
          apply hmem
          have : rep Sg χ = rep Sg ψ := by
            refine rep_eq Sg ?_
            exact orbit_eq_of_mem_both Sg (dom_eq_domF _) (dom_eq_domF _)
              (mem_orbit_self Sg (dom_eq_domF χ)) hχ
          rw [← this]
          exact mem_image_of_mem _ (mem_filter.2 ⟨mem_univ _, hJχ⟩)
        · rfl
      rw [hzero, sub_zero, hbd]
      nth_rw 1 [hdecomp]
      exact (isAtomSum_sum Sg S Φ _ _ fun ρ hρ => hpieces ρ hρ).add Sg S Φ hrest
  exact ⟨l, hl, hsum⟩

end DesignsII
