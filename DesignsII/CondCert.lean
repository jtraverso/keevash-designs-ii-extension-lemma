/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import DesignsII.CondPerm

/-!
# Certificate Lipschitz bounds in the conditioned space

In the space conditioned on the values at the positions `S`, a transposition of values of `τ c`
is a transposition of two values outside `v(S c)` in `liftPi S v τ`, which moves only two
positions outside `S c`. Hence the certificate Lipschitz bound only needs the witness counts at
non-conditioned positions (`cond_countVar_lipschitz_cert`): in Lemma `ext*` these are the
positions of non-fixed vertices, where the counts are small.
-/

@[expose] public section

namespace DesignsII

open Finset Equiv

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {a : ι → ℕ} {β : Type*}

omit [Fintype ι] in
open Classical in
/-- One step of the certificate argument: if `ω₁` agrees with `ω₀` outside the positions
`p₁, p₂` of coordinate `c`, the count grows by at most the number of events of `ω₁` whose
certificate contains `p₁` or `p₂`. -/
theorem cert_step (C : Finset β) (G : β → (∀ c, Perm (Fin (a c))) → Prop)
    (W : β → (∀ c, Perm (Fin (a c))) → Finset (Σ c, Fin (a c)))
    (hW : ∀ b ∈ C, ∀ ω ω', G b ω → AgreeAt (W b ω) ω ω' → G b ω')
    (ω₀ ω₁ : ∀ c, Perm (Fin (a c))) (c : ι) (p₁ p₂ : Fin (a c))
    (hag : ∀ D : Finset (Σ c, Fin (a c)), (⟨c, p₁⟩ : Σ c, Fin (a c)) ∉ D →
      (⟨c, p₂⟩ : Σ c, Fin (a c)) ∉ D → AgreeAt D ω₁ ω₀) :
    countVar C G ω₁ - countVar C G ω₀ ≤
      ((C.filter fun b => G b ω₁ ∧ (⟨c, p₁⟩ : Σ c, Fin (a c)) ∈ W b ω₁).card : ℝ) +
        (C.filter fun b => G b ω₁ ∧ (⟨c, p₂⟩ : Σ c, Fin (a c)) ∈ W b ω₁).card := by
  unfold countVar
  have hsub : (C.filter fun b => G b ω₁) \ (C.filter fun b => G b ω₀) ⊆
      (C.filter fun b => G b ω₁ ∧ (⟨c, p₁⟩ : Σ c, Fin (a c)) ∈ W b ω₁) ∪
        C.filter fun b => G b ω₁ ∧ (⟨c, p₂⟩ : Σ c, Fin (a c)) ∈ W b ω₁ := by
    intro b hb
    obtain ⟨h1, h0⟩ := mem_sdiff.1 hb
    obtain ⟨hbC, hG1⟩ := mem_filter.1 h1
    by_contra hn
    simp only [mem_union, mem_filter, not_or, not_and] at hn
    exact h0 (mem_filter.2 ⟨hbC, hW b hbC ω₁ ω₀ hG1
      (hag _ (hn.1 hbC hG1) (hn.2 hbC hG1))⟩)
  have h1 : ((C.filter fun b => G b ω₁).card : ℝ) ≤
      (((C.filter fun b => G b ω₁) \ (C.filter fun b => G b ω₀)).card : ℝ) +
        (C.filter fun b => G b ω₀).card := by
    exact_mod_cast card_le_card_sdiff_add_card
  have h23 : (((C.filter fun b => G b ω₁) \ (C.filter fun b => G b ω₀)).card : ℝ) ≤
      ((C.filter fun b => G b ω₁ ∧ (⟨c, p₁⟩ : Σ c, Fin (a c)) ∈ W b ω₁).card : ℝ) +
        (C.filter fun b => G b ω₁ ∧ (⟨c, p₂⟩ : Σ c, Fin (a c)) ∈ W b ω₁).card := by
    exact_mod_cast (card_le_card hsub).trans (card_union_le _ _)
  linarith

variable (S : ∀ c, Finset (Fin (a c))) (v : ∀ c, S c ↪ Fin (a c))

omit [Fintype ι] in
theorem liftPi_symm_not_mem (τ : ∀ c, Perm (Fin (a c - (S c).card))) (c : ι)
    (x : Fin (a c - (S c).card)) :
    (liftPi S v τ c).symm (eVal (S c) (v c) x) ∉ S c := by
  intro h
  have := liftC_apply_mem (S c) (v c) (τ c) h
  simp only [liftPi] at this
  rw [Equiv.apply_symm_apply] at this
  apply eVal_not_mem_vImg (S c) (v c) x
  rw [this]; simp [vImg]

omit [Fintype ι] in
open Classical in
/-- **Certificate Lipschitz bound in the conditioned space**: only the witness counts at
non-conditioned positions matter. -/
theorem cond_countVar_lipschitz_cert (C : Finset β) (G : β → (∀ c, Perm (Fin (a c))) → Prop)
    (W : β → (∀ c, Perm (Fin (a c))) → Finset (Σ c, Fin (a c)))
    (hW : ∀ b ∈ C, ∀ ω ω', G b ω → AgreeAt (W b ω) ω ω' → G b ω') (L : ι → ℝ)
    (hL : ∀ ω c (p : Fin (a c)), p ∉ S c →
      ((C.filter fun b => G b ω ∧ (⟨c, p⟩ : Σ c, Fin (a c)) ∈ W b ω).card : ℝ) ≤ L c) :
    IsLipschitzG (a := fun c => a c - (S c).card) (fun τ => countVar C G (liftPi S v τ))
      (fun c => 2 * L c) := by
  intro τ c x y
  simp only
  rw [liftPi_update_swap]
  set ω := liftPi S v τ
  set X := (eVal (S c) (v c) x : Fin (a c))
  set Y := (eVal (S c) (v c) y : Fin (a c))
  set ω' := Function.update ω c (swap X Y * ω c)
  have hx : (ω c).symm X ∉ S c := liftPi_symm_not_mem S v τ c x
  have hy : (ω c).symm Y ∉ S c := liftPi_symm_not_mem S v τ c y
  have hx' : (ω' c).symm X ∉ S c := by rw [(symm_swap_update ω c X Y).1]; exact hy
  have hy' : (ω' c).symm Y ∉ S c := by rw [(symm_swap_update ω c X Y).2]; exact hx
  rw [abs_le]
  constructor
  · have := cert_step C G W hW ω' ω c ((ω c).symm X) ((ω c).symm Y)
      fun D h1 h2 => agreeAt_swap ω c X Y D h1 h2
    linarith [hL ω c _ hx, hL ω c _ hy]
  · have hω : Function.update ω' c (swap X Y * ω' c) = ω := by
      funext c'
      by_cases hc : c' = c
      · subst hc; simp [ω', ← mul_assoc]
      · simp [ω', Function.update_of_ne hc]
    have := cert_step C G W hW ω ω' c ((ω' c).symm X) ((ω' c).symm Y) fun D h1 h2 => by
      have h := agreeAt_swap ω' c X Y D h1 h2
      rwa [hω] at h
    linarith [hL ω' c _ hx', hL ω' c _ hy']

end DesignsII
