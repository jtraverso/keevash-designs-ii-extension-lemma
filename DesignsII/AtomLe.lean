/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import DesignsII.AtomEq

/-!
# `γ(φ) ≤_γ G` from its restrictions

For `A = Σ^≤`, an injective `Φ`-embedding `φ` of `A` into a `Σ`-adapted complex and any `G`:
if `γ(φ|_B) ≤_γ G` for every `r`-set `B` of labels (and there is one), then `γ(φ) ≤_γ G`
(`leGamma_molecule_of_restrict`). In Lemma `ext*` this turns `(ω, h)`-extendability of
`(Φ, γ[G])` into copies `φ ∈ 𝒜(Φ, G)`.

Tools: restriction to an orbit (`onOrbit`) is linear, idempotent, maps an atom to itself or `0`,
hence maps atom sums to atom sums; vectors decompose over any set of canonical representatives
covering their support (`sum_onOrbit_of`).
-/

@[expose] public section

namespace DesignsII

open Finset

variable {R V ι : Type*} [DecidableEq R] [Fintype R] [Fintype V] [DecidableEq V] {D r : ℕ}
  (Sg : Subgroup (Equiv.Perm R))

omit [DecidableEq V] in
theorem rep_rep (χ : R → Option V) : rep Sg (rep Sg χ) = rep Sg χ := rep_eq Sg (orbit_rep Sg χ)

/-- Decomposition over any set of canonical representatives covering the support. -/
theorem sum_onOrbit_of {M : Type*} [AddCommMonoid M] (X : (R → Option V) → M)
    (T : Finset (R → Option V)) (hT : ∀ ρ ∈ T, rep Sg ρ = ρ)
    (hsupp : ∀ χ, X χ ≠ 0 → rep Sg χ ∈ T) :
    X = ∑ ρ ∈ T, onOrbit Sg X ρ (domF ρ) := by
  classical
  funext ψ
  rw [Finset.sum_apply]
  unfold onOrbit
  by_cases hX : X ψ = 0
  · rw [hX]; exact (sum_eq_zero fun ρ _ => by simp [hX]).symm
  · rw [sum_eq_single (rep Sg ψ)]
    · simp [mem_orbit_rep Sg ψ]
    · intro ρ hρ hne
      have : ψ ∉ orbit Sg ρ (domF ρ) := fun h => by
        rw [← hT ρ hρ] at h
        exact hne ((rep_eq_of_mem Sg h).trans (hT ρ hρ)).symm
      simp [this]
    · intro h; exact absurd (hsupp ψ hX) h

variable {M : Type*} [AddCommGroup M]

theorem onOrbit_sub (X Y : (R → Option V) → M) (ρ : R → Option V) (B : Finset R) :
    onOrbit Sg (X - Y) ρ B = onOrbit Sg X ρ B - onOrbit Sg Y ρ B := by
  classical
  funext x; unfold onOrbit; by_cases hx : x ∈ orbit Sg ρ B <;> simp [hx]

theorem onOrbit_add (X Y : (R → Option V) → M) (ρ : R → Option V) (B : Finset R) :
    onOrbit Sg (X + Y) ρ B = onOrbit Sg X ρ B + onOrbit Sg Y ρ B := by
  classical
  funext x; unfold onOrbit; by_cases hx : x ∈ orbit Sg ρ B <;> simp [hx]

theorem onOrbit_zero (ρ : R → Option V) (B : Finset R) :
    onOrbit Sg (0 : (R → Option V) → M) ρ B = 0 := by
  classical
  funext x; unfold onOrbit; by_cases hx : x ∈ orbit Sg ρ B <;> simp [hx]

theorem onOrbit_list_sum (l : List ((R → Option V) → M)) (ρ : R → Option V) (B : Finset R) :
    onOrbit Sg l.sum ρ B = (l.map fun a => onOrbit Sg a ρ B).sum := by
  induction l with
  | nil => simpa using onOrbit_zero Sg ρ B
  | cons a l ih => simp [onOrbit_add, ih]

theorem onOrbit_idem (X : (R → Option V) → M) (ρ : R → Option V) (B : Finset R) :
    onOrbit Sg (onOrbit Sg X ρ B) ρ B = onOrbit Sg X ρ B := by
  classical
  funext x; unfold onOrbit; by_cases hx : x ∈ orbit Sg ρ B <;> simp [hx]

/-- Restricting a restriction to a different orbit gives `0`, to the same orbit itself. -/
theorem onOrbit_onOrbit (X : (R → Option V) → M) (ψ ρ : R → Option V)
    (hψ : dom ψ = (domF ψ : Set R)) :
    onOrbit Sg (onOrbit Sg X ψ (domF ψ)) ρ (domF ρ) = onOrbit Sg X ψ (domF ψ) ∨
      onOrbit Sg (onOrbit Sg X ψ (domF ψ)) ρ (domF ρ) = 0 := by
  classical
  by_cases h : orbit Sg ρ (domF ρ) = orbit Sg ψ (domF ψ)
  · left; unfold onOrbit; rw [h]; funext x
    by_cases hx : x ∈ orbit Sg ψ (domF ψ) <;> simp [hx]
  · right
    funext x
    unfold onOrbit
    split_ifs with h1 h2
    · exact absurd (orbit_eq_of_mem_both Sg (dom_eq_domF ρ) hψ h1 h2) h
    · rfl
    · rfl

variable (S : VSystem R ι (Fin D → ℤ) r) (Φ : RSystem R V)

/-- **Restriction to an orbit of an atom sum is an atom sum.** -/
theorem IsAtomSum.onOrbit {v : (R → Option V) → (Fin D → ℤ)} (hv : IsAtomSum Sg S Φ v)
    (ρ : R → Option V) : IsAtomSum Sg S Φ (DesignsII.onOrbit Sg v ρ (domF ρ)) := by
  obtain ⟨l, hl, rfl⟩ := hv
  rw [onOrbit_list_sum]
  induction l with
  | nil => simpa using isAtomSum_zero Sg S Φ
  | cons a l ih =>
    rw [List.map_cons, List.sum_cons]
    refine IsAtomSum.add Sg S Φ ?_ (ih fun b hb => hl b (List.mem_cons_of_mem _ hb))
    obtain ⟨-, i, φ, -, B, -, ψ, hψ, rfl⟩ := hl a List.mem_cons_self
    have hd : dom ψ = B := Φ.dom_eq B ψ hψ
    rw [← domF_eq hd]
    rcases onOrbit_onOrbit Sg (S.molecule i φ) ψ ρ (dom_eq_domF ψ) with h | h <;> rw [h]
    · exact isAtomSum_of Sg S Φ (Or.inr (by rw [domF_eq hd]; exact hl _ List.mem_cons_self))
    · exact isAtomSum_zero Sg S Φ
omit [Fintype R] [Fintype V] [DecidableEq V] in
theorem dom_restrictT_eq (φ : R → V) (B : Finset R) : dom (restrictT φ B) = B := by
  ext x; by_cases hx : x ∈ B <;> simp [dom, restrictT, restrict, hx]

/-- **`γ(φ) ≤_γ G` from the restrictions.** -/
theorem leGamma_molecule_of_restrict (hΦ : IsAdapted Φ Sg) {i : ι} (hA : S.A i = sigmaLe Sg)
    {φ : R → V} (hφinj : Function.Injective φ) (hφ : IsEmbedding (S.A i) Φ φ)
    (G : (R → Option V) → (Fin D → ℤ)) {B₀ : Finset R} (hB₀ : B₀.card = r)
    (h : ∀ B : Finset R, B.card = r → LeGamma S Sg Φ (moleculeP S i (restrictT φ B)) G) :
    LeGamma S Sg Φ (S.molecule i φ) G := by
  classical
  set J := S.molecule i φ
  have hpiece : ∀ B : Finset R, B.card = r →
      onOrbit Sg J (restrictT φ B) B = moleculeP S i (restrictT φ B) :=
    fun B hB => onOrbit_molecule_restrict S Sg hA hφinj hB
  have hmemΦ : ∀ B : Finset R, restrictT φ B ∈ Φ.maps B := by
    intro B
    have hθ : restrict (fun x => some ((1 : Equiv.Perm R) x)) B ∈ (S.A i).maps B := by
      rw [hA]; exact ⟨1, Sg.one_mem, rfl⟩
    have := hφ.2 B _ hθ
    convert this using 1
    funext x; simp [comp, restrict, restrictT]
  have hpieceAS : ∀ B : Finset R, B.card = r → IsAtomSum Sg S Φ (moleculeP S i (restrictT φ B)) := by
    intro B hB
    rw [← hpiece B hB]
    by_cases h0 : onOrbit Sg J (restrictT φ B) B = 0
    · rw [h0]; exact isAtomSum_zero Sg S Φ
    · exact isAtomSum_of Sg S Φ (Or.inr ⟨h0, i, φ, hφ, B, hB, restrictT φ B, hmemΦ B, rfl⟩)
  -- `G` itself is an atom sum
  have hGas : IsAtomSum Sg S Φ G := by
    obtain ⟨l, hl, hsum⟩ := h B₀ hB₀
    have : G = moleculeP S i (restrictT φ B₀) + l.sum := by rw [← hsum]; abel
    rw [this]
    exact (hpieceAS B₀ hB₀).add Sg S Φ ⟨l, hl, rfl⟩
  set T := (univ.filter fun χ => G χ ≠ 0 ∨ J χ ≠ 0).image (rep Sg)
  have hT : ∀ ρ ∈ T, rep Sg ρ = ρ := by
    intro ρ hρ
    obtain ⟨χ, -, rfl⟩ := mem_image.1 hρ
    exact rep_rep Sg χ
  have eG := sum_onOrbit_of Sg G T hT fun χ hχ =>
    mem_image_of_mem _ (mem_filter.2 ⟨mem_univ _, Or.inl hχ⟩)
  have eJ := sum_onOrbit_of Sg J T hT fun χ hχ =>
    mem_image_of_mem _ (mem_filter.2 ⟨mem_univ _, Or.inr hχ⟩)
  have hdiff : G - J = ∑ ρ ∈ T, (onOrbit Sg G ρ (domF ρ) - onOrbit Sg J ρ (domF ρ)) := by
    rw [sum_sub_distrib, ← eG, ← eJ]
  show IsAtomSum Sg S Φ (G - J)
  rw [hdiff]
  refine isAtomSum_sum Sg S Φ _ _ fun ρ _ => ?_
  by_cases hJρ : onOrbit Sg J ρ (domF ρ) = 0
  · rw [hJρ, sub_zero]; exact hGas.onOrbit Sg S Φ ρ
  obtain ⟨x, hx⟩ := Function.ne_iff.1 hJρ
  have hxo : x ∈ orbit Sg ρ (domF ρ) := by
    by_contra hn; apply hx; unfold onOrbit; simp [hn]
  have hJx : J x ≠ 0 := by
    intro h0; apply hx; unfold onOrbit; simp [h0]
  obtain ⟨θ, hθ, hθx⟩ := exists_of_molecule_ne_zero S hJx
  obtain ⟨B'', hB'', σ, hσ, rfl⟩ := (mapsR_sigmaLe S Sg hA).1 hθ
  set B' := B''.map σ.toEmbedding
  have hB' : B'.card = r := by rw [card_map, hB'']
  have hsub : ∀ y ∈ B'', σ y ∈ B' := fun y hy => mem_map_of_mem _ hy
  have hxB' : x ∈ orbit Sg (restrictT φ B') B' := by
    refine ⟨σ, hσ, B'', rfl, ?_⟩
    rw [← hθx, comp_restrict, relabel_restrictT hsub]
  have horb : orbit Sg ρ (domF ρ) = orbit Sg (restrictT φ B') B' :=
    orbit_eq_of_mem_both Sg (dom_eq_domF ρ) (dom_restrictT_eq φ B') hxo hxB'
  have hJρ' : onOrbit Sg J ρ (domF ρ) = moleculeP S i (restrictT φ B') := by
    have := hpiece B' hB'
    unfold onOrbit at this ⊢
    rw [horb]; exact this
  have e1 : onOrbit Sg J ρ (domF ρ) =
      onOrbit Sg (moleculeP S i (restrictT φ B')) ρ (domF ρ) := by
    rw [← hJρ', onOrbit_idem]
  rw [e1, ← onOrbit_sub]
  obtain ⟨l', hl', hsum⟩ := h B' hB'
  rw [hsum]
  exact IsAtomSum.onOrbit Sg S Φ ⟨l', hl', rfl⟩ ρ

end DesignsII
