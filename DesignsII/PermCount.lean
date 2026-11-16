/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib

/-!
# Counting permutations with prescribed values

* `card_perm_fix`: for injections `w, u : [k] ↪ [m]`, exactly `(m - k)!` permutations `σ` of `[m]`
  satisfy `σ (w x) = u x` for all `x`;
* `card_perm_restrict_mem`: the number of `σ` whose restriction `σ ∘ w` lies in a set `U` of
  injections is `|U| (m - k)!`; so the restriction of a uniform permutation to `k` positions is a
  uniform injection (`k`-tuple of distinct values);
* `card_pi_filter`: events on distinct coordinates of a product are independent.

These are the basic probability computations for the random template (uniform injections
`f_j : [n] → 𝔽_{p^a}`, colours `T_e`, orderings `π_e`, …), modelled by independent uniform
permutations.
-/

@[expose] public section

namespace DesignsII

open Finset Equiv

/-- Left multiplication by a permutation moving `u` to `u'` matches the fibres. -/
theorem card_perm_fix_eq {k m : ℕ} (w u u' : Fin k ↪ Fin m) :
    (univ.filter fun σ : Perm (Fin m) => ∀ x, σ (w x) = u x).card =
      (univ.filter fun σ : Perm (Fin m) => ∀ x, σ (w x) = u' x).card := by
  classical
  let e : {y // y ∈ Set.range u} ≃ {y // y ∈ Set.range u'} :=
    (Equiv.ofInjective u u.injective).symm.trans (Equiv.ofInjective u' u'.injective)
  set τ : Perm (Fin m) := e.extendSubtype
  have hτ : ∀ x, τ (u x) = u' x := by
    intro x
    rw [Equiv.extendSubtype_apply_of_mem e (u x) ⟨x, rfl⟩]
    simp only [e, Equiv.trans_apply]
    have : (Equiv.ofInjective u u.injective).symm ⟨u x, ⟨x, rfl⟩⟩ = x :=
      (Equiv.ofInjective u u.injective).symm_apply_eq.2 rfl
    rw [this]; rfl
  refine card_bij (fun σ _ => τ * σ) (fun σ hσ => ?_) (fun σ _ σ' _ h => mul_left_cancel h)
    (fun σ hσ => ⟨τ⁻¹ * σ, ?_, by simp⟩)
  · simp only [mem_filter, mem_univ, true_and] at hσ ⊢
    intro x; rw [Perm.mul_apply, hσ, hτ]
  · simp only [mem_filter, mem_univ, true_and] at hσ ⊢
    intro x
    rw [Perm.mul_apply, hσ, Perm.inv_eq_iff_eq, hτ]

/-- **`(m - k)!` permutations take prescribed values at prescribed positions.** -/
theorem card_perm_fix {k m : ℕ} (w u : Fin k ↪ Fin m) :
    (univ.filter fun σ : Perm (Fin m) => ∀ x, σ (w x) = u x).card = (m - k).factorial := by
  classical
  have hkm : k ≤ m := by simpa using Fintype.card_le_of_embedding w
  set c := (univ.filter fun σ : Perm (Fin m) => ∀ x, σ (w x) = u x).card
  -- every permutation lies in exactly one fibre, indexed by `σ ∘ w`
  have htot : (univ : Finset (Perm (Fin m))).card =
      ∑ v : Fin k ↪ Fin m, (univ.filter fun σ : Perm (Fin m) => ∀ x, σ (w x) = v x).card := by
    rw [card_eq_sum_card_fiberwise (f := fun σ : Perm (Fin m) => w.trans σ.toEmbedding)
      (t := univ) (fun _ _ => mem_univ _)]
    refine sum_congr rfl fun v _ => congrArg card ?_
    ext σ
    simp only [mem_filter, mem_univ, true_and]
    constructor
    · rintro rfl x; rfl
    · intro h; ext x; simp [h x]
  rw [sum_congr rfl fun v _ => (card_perm_fix_eq w u v).symm, sum_const, card_univ,
    card_univ, Fintype.card_perm, Fintype.card_fin, Fintype.card_embedding_eq,
    Fintype.card_fin, Fintype.card_fin, smul_eq_mul] at htot
  have hpos : 0 < m.descFactorial k := Nat.descFactorial_pos.2 hkm
  have h2 := Nat.factorial_mul_descFactorial hkm
  have : c * m.descFactorial k = (m - k).factorial * m.descFactorial k := by
    rw [h2, htot, mul_comm]
  exact Nat.eq_of_mul_eq_mul_right hpos this

/-- The number of permutations whose restriction to the positions `w` lies in `U`. -/
theorem card_perm_restrict_mem {k m : ℕ} (w : Fin k ↪ Fin m) (U : Finset (Fin k ↪ Fin m)) :
    (univ.filter fun σ : Perm (Fin m) => w.trans σ.toEmbedding ∈ U).card =
      U.card * (m - k).factorial := by
  classical
  rw [card_eq_sum_card_fiberwise (s := univ.filter fun σ : Perm (Fin m) => w.trans σ.toEmbedding ∈ U)
    (f := fun σ : Perm (Fin m) => w.trans σ.toEmbedding) (t := U)
    (fun σ hσ => (mem_filter.1 hσ).2)]
  rw [← smul_eq_mul, ← sum_const]
  refine sum_congr rfl fun v hv => ?_
  rw [← card_perm_fix w v]
  congr 1
  ext σ
  simp only [mem_filter, mem_univ, true_and]
  constructor
  · rintro ⟨-, rfl⟩ x; rfl
  · intro h
    have : w.trans σ.toEmbedding = v := by ext x; simp [h x]
    exact ⟨this ▸ hv, this⟩

/-- **Independence of coordinates**: in a finite product, the number of points satisfying an event
on every coordinate is the product of the coordinate counts. -/
theorem card_pi_filter {ι : Type*} [Fintype ι] [DecidableEq ι] {Ω : ι → Type*}
    [∀ i, Fintype (Ω i)] [∀ i, DecidableEq (Ω i)] (E : ∀ i, Ω i → Prop) [∀ i, DecidablePred (E i)] :
    (univ.filter fun σ : (∀ i, Ω i) => ∀ i, E i (σ i)).card =
      ∏ i, (univ.filter (E i)).card := by
  rw [← Fintype.card_piFinset]
  congr 1
  ext σ
  simp [Fintype.mem_piFinset]

end DesignsII
