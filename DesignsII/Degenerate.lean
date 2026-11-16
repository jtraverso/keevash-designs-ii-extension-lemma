/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import DesignsII.CandCount
public import DesignsII.CondPerm

/-!
# Degenerate revealed values

* `card_dependent_le`: at most `|F|^u N^{u-1}` tuples `x ∈ K^u` are `F`-linearly dependent (each
  nontrivial relation `∑ λ_k x_k = 0` cuts out a hyperplane);
* `probG_le_of_cond_except`: the law of total probability over the conditioning values, with an
  exceptional set of values: `P(E) ≤ P(ω|_S ∈ Bad) + ε` if `P(E | ω|_S = v) ≤ ε` for all `v ∉ Bad`.

In Lemma `ext*` the values of `f_j` at the fixed vertices are degenerate with probability
`O(|F|^u / N)` per colour; colours are independent, so few colours are degenerate
(BLUEPRINT, "Lemma `e|E` and the fixed vertices").
-/

@[expose] public section

namespace DesignsII

open Finset Equiv

variable {F K : Type*} [Field F] [Fintype F] [DecidableEq F] [Field K] [Algebra F K] [Fintype K]
  [DecidableEq K]

open Classical in
/-- **Dependent tuples are rare**: at most `|F|^u N^{u-1}` tuples in `K^u` are `F`-dependent. -/
theorem card_dependent_le (u : ℕ) :
    (univ.filter fun x : Fin u → K => ¬ LinearIndependent F x).card ≤
      Fintype.card F ^ u * Fintype.card K ^ (u - 1) := by
  classical
  have hsub : (univ.filter fun x : Fin u → K => ¬ LinearIndependent F x) ⊆
      (univ.filter fun lam : Fin u → F => lam ≠ 0).biUnion fun lam =>
        univ.filter fun x : Fin u → K => ∑ k, algebraMap F K (lam k) * x k = 0 := by
    intro x hx
    have := (mem_filter.1 hx).2
    rw [Fintype.not_linearIndependent_iff] at this
    obtain ⟨lam, hlam, k, hk⟩ := this
    refine mem_biUnion.2 ⟨lam, mem_filter.2 ⟨mem_univ _, fun h => hk (by simp [h])⟩,
      mem_filter.2 ⟨mem_univ _, ?_⟩⟩
    simpa [Algebra.smul_def] using hlam
  refine (card_le_card hsub).trans (card_biUnion_le.trans ?_)
  calc ∑ lam ∈ univ.filter (fun lam : Fin u → F => lam ≠ 0),
        (univ.filter fun x : Fin u → K => ∑ k, algebraMap F K (lam k) * x k = 0).card
      ≤ ∑ _lam ∈ univ.filter (fun lam : Fin u → F => lam ≠ 0), Fintype.card K ^ (u - 1) := by
        refine sum_le_sum fun lam hlam => ?_
        obtain ⟨k, hk⟩ := Function.ne_iff.1 (mem_filter.1 hlam).2
        exact card_affine_le (c := fun l => algebraMap F K (lam l)) ((map_ne_zero _).2 hk) 0
    _ ≤ Fintype.card F ^ u * Fintype.card K ^ (u - 1) := by
        rw [sum_const, smul_eq_mul]
        gcongr
        refine (card_le_card (filter_subset _ _)).trans ?_
        simp

section Except

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {a : ι → ℕ} (S : ∀ c, Finset (Fin (a c)))

open Classical in
/-- **Total probability with exceptional conditioning values.** -/
theorem probG_le_of_cond_except (E : (∀ c, Perm (Fin (a c))) → Prop)
    (Bad : (∀ c, S c ↪ Fin (a c)) → Prop) {ε : ℝ} (hε : 0 ≤ ε)
    (h : ∀ v, ¬ Bad v →
      probG (a := fun c => a c - (S c).card) (fun τ => E (liftPi S v τ)) ≤ ε) :
    probG (a := a) E ≤ probG (a := a) (fun ω => Bad (restrS S ω)) + ε := by
  have h' : ∀ v, probG (a := fun c => a c - (S c).card)
      (fun τ => E (liftPi S v τ) ∧ ¬ Bad (restrS S (liftPi S v τ))) ≤ ε := by
    intro v
    by_cases hv : Bad v
    · refine (probG_mono (B := fun _ => False) fun τ hτ =>
        hτ.2 (by rw [restrS_liftPi]; exact hv)).trans (le_trans (le_of_eq ?_) hε)
      unfold probG
      simp
    · refine le_trans (probG_mono fun τ hτ => hτ.1) (h v hv)
  have := probG_le_of_cond S (fun ω => E ω ∧ ¬ Bad (restrS S ω)) h'
  calc probG (a := a) E
      ≤ probG (a := a) (fun ω => Bad (restrS S ω) ∨ (E ω ∧ ¬ Bad (restrS S ω))) :=
        probG_mono fun ω hω => by by_cases hb : Bad (restrS S ω) <;> simp_all
    _ ≤ probG (a := a) (fun ω => Bad (restrS S ω)) +
          probG (a := a) (fun ω => E ω ∧ ¬ Bad (restrS S ω)) := probG_or_le _ _
    _ ≤ _ := by linarith

end Except

end DesignsII
