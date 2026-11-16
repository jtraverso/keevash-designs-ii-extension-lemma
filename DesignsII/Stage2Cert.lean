/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import DesignsII.CondCert
public import DesignsII.TwoStage

/-!
# Certificate Lipschitz bounds for the second stage

In the conditioned space, for a fixed first-stage outcome `ω₁`, the second-stage function
`ω₂ ↦ X(liftPi (merge ω₁ ω₂))` is Lipschitz with constants `2 L c` as soon as the witness counts
are bounded by `L c` on the configurations `liftPi (merge ω₁ ω₂)` only
(`stage₂_lipschitz_cert`): a second-stage transposition keeps the first-stage coordinates. This
allows constants depending on `ω₁` (in Lemma `ext*`: on the colours).
-/

@[expose] public section

namespace DesignsII

open Finset Equiv

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {a : ι → ℕ} {β : Type*}
  {p : ι → Prop} [DecidablePred p]
  (S : ∀ c, Finset (Fin (a c))) (v : ∀ c, S c ↪ Fin (a c))

omit [Fintype ι] in
open Classical in
/-- **Certificate Lipschitz bound for the second stage.** -/
theorem stage₂_lipschitz_cert (C : Finset β) (G : β → (∀ c, Perm (Fin (a c))) → Prop)
    (W : β → (∀ c, Perm (Fin (a c))) → Finset (Σ c, Fin (a c)))
    (hW : ∀ b ∈ C, ∀ ω ω', G b ω → AgreeAt (W b ω) ω ω' → G b ω')
    (ω₁ : Ω₁ (a := fun c => a c - (S c).card) p) (L : {c // ¬ p c} → ℝ)
    (hL : ∀ (ω₂ : Ω₂ (a := fun c => a c - (S c).card) p) (c : {c // ¬ p c}) (pp : Fin (a c)),
      pp ∉ S c →
      ((C.filter fun b => G b (liftPi S v (merge ω₁ ω₂)) ∧
        (⟨c, pp⟩ : Σ c, Fin (a c)) ∈ W b (liftPi S v (merge ω₁ ω₂))).card : ℝ) ≤ L c) :
    IsLipschitzG (a := fun c : {c // ¬ p c} => a c - (S c).card)
      (fun ω₂ => countVar C G (liftPi S v (merge ω₁ ω₂))) (fun c => 2 * L c) := by
  intro ω₂ c x y
  simp only
  set ω₂' := Function.update ω₂ c (swap x y * ω₂ c)
  have hm : merge ω₁ ω₂' = Function.update (merge ω₁ ω₂) c.1 (swap x y * merge ω₁ ω₂ c.1) := by
    rw [merge_update₂]
    congr 2
    simp [merge, c.2]
  set τ := merge ω₁ ω₂
  have hω' : liftPi S v (merge ω₁ ω₂') = Function.update (liftPi S v τ) c.1
      (swap (eVal (S c) (v c) x : Fin (a c)) (eVal (S c) (v c) y) * liftPi S v τ c.1) := by
    rw [hm]; exact liftPi_update_swap S v τ c.1 x y
  rw [hω']
  set ω := liftPi S v τ
  set X := (eVal (S c) (v c) x : Fin (a c))
  set Y := (eVal (S c) (v c) y : Fin (a c))
  set ω' := Function.update ω c.1 (swap X Y * ω c.1)
  have hx : (ω c.1).symm X ∉ S c := liftPi_symm_not_mem S v τ c.1 x
  have hy : (ω c.1).symm Y ∉ S c := liftPi_symm_not_mem S v τ c.1 y
  have hx' : (ω' c.1).symm X ∉ S c := by rw [(symm_swap_update ω c.1 X Y).1]; exact hy
  have hy' : (ω' c.1).symm Y ∉ S c := by rw [(symm_swap_update ω c.1 X Y).2]; exact hx
  have hLω : ∀ pp, pp ∉ S c → ((C.filter fun b => G b ω ∧
      (⟨c.1, pp⟩ : Σ c, Fin (a c)) ∈ W b ω).card : ℝ) ≤ L c := fun pp hp => hL ω₂ c pp hp
  have hLω' : ∀ pp, pp ∉ S c → ((C.filter fun b => G b ω' ∧
      (⟨c.1, pp⟩ : Σ c, Fin (a c)) ∈ W b ω').card : ℝ) ≤ L c := fun pp hp => by
    have h := hL ω₂' c pp hp
    rwa [hω'] at h
  rw [abs_le]
  constructor
  · have := cert_step C G W hW ω' ω c.1 ((ω c.1).symm X) ((ω c.1).symm Y)
      fun D h1 h2 => agreeAt_swap ω c.1 X Y D h1 h2
    linarith [hLω _ hx, hLω _ hy]
  · have hω : Function.update ω' c.1 (swap X Y * ω' c.1) = ω := by
      funext c'
      by_cases hc : c' = c.1
      · subst hc; simp [ω', ← mul_assoc]
      · simp [ω', Function.update_of_ne hc]
    have := cert_step C G W hW ω ω' c.1 ((ω' c.1).symm X) ((ω' c.1).symm Y) fun D h1 h2 => by
      have h := agreeAt_swap ω' c.1 X Y D h1 h2
      rwa [hω] at h
    linarith [hLω' _ hx', hLω' _ hy']

end DesignsII
