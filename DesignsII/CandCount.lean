/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import DesignsII.TemplateProb

/-!
# Candidate template copies through a point (deterministic bounds)

For an injection `f : [n] → K` (`|K| = N`) and a matrix `M ∈ F^{q×r}` with nonzero rows, the maps
`φ : [q] → [n]` with `f ∘ φ = M y` for some `y` and `x ∈ φ([q])` are at most `q N^{r-1}`
(`card_cand_through_le`): `φ` is determined by `y`, and `(M y)_i = f(x)` is an affine hyperplane.
This bounds the Lipschitz constants of the template counting variables in the `f_j` coordinates
(concentration plan for Lemma `ext*`).
-/

@[expose] public section

namespace DesignsII

open Finset Matrix

variable {F K : Type*} [Field F] [Field K] [Algebra F K] [Fintype K] [DecidableEq K] {q r n : ℕ}

/-- A nonzero affine form over `K` takes a given value on at most `N^{r-1}` vectors. -/
theorem card_affine_le {c : Fin r → K} {k : Fin r} (hk : c k ≠ 0) (v : K) :
    (univ.filter fun y : Fin r → K => ∑ l, c l * y l = v).card ≤ Fintype.card K ^ (r - 1) := by
  classical
  have hinj : Set.InjOn (fun y : Fin r → K => fun l : {l // l ≠ k} => y l)
      (univ.filter fun y : Fin r → K => ∑ l, c l * y l = v : Set (Fin r → K)) := by
    intro y hy y' hy' h
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hy hy'
    have hl : ∀ l, l ≠ k → y l = y' l := fun l hl => congrFun h ⟨l, hl⟩
    funext l
    by_cases hlk : l = k
    · subst hlk
      have e1 := hy; have e2 := hy'
      rw [← add_sum_erase _ _ (mem_univ l)] at e1 e2
      have : ∑ x ∈ univ.erase l, c x * y x = ∑ x ∈ univ.erase l, c x * y' x :=
        sum_congr rfl fun x hx => by rw [hl x (ne_of_mem_erase hx)]
      rw [this] at e1
      have : c l * (y l - y' l) = 0 := by linear_combination e1 - e2
      exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_left hk)
    · exact hl l hlk
  calc _ ≤ (univ : Finset ({l // l ≠ k} → K)).card :=
        card_le_card_of_injOn _ (fun _ _ => mem_coe.2 (mem_univ _)) hinj
    _ = Fintype.card K ^ (r - 1) := by
        rw [card_univ, Fintype.card_fun, Fintype.card_subtype_compl, Fintype.card_fin,
          Fintype.card_subtype_eq]

/-- **Candidate copies through a point.** -/
theorem card_cand_through_le {M : Matrix (Fin q) (Fin r) F} (hM : ∀ i, M i ≠ 0)
    {f : Fin n → K} (hf : Function.Injective f) (x : Fin n) :
    (univ.filter fun φ : Fin q → Fin n =>
      (∃ y, ∀ i, f (φ i) = mvec M y i) ∧ x ∈ univ.image φ).card ≤
      q * Fintype.card K ^ (r - 1) := by
  classical
  -- each such `φ` comes from a `y` with `(M y)_i = f x` for some `i`
  have hex : ∀ φ ∈ (univ.filter fun φ : Fin q → Fin n =>
      (∃ y, ∀ i, f (φ i) = mvec M y i) ∧ x ∈ univ.image φ),
      ∃ y ∈ (univ : Finset (Fin q)).biUnion (fun i => univ.filter fun y : Fin r → K =>
        mvec M y i = f x), ∀ i, f (φ i) = mvec M y i := by
    intro φ hφ
    obtain ⟨⟨y, hy⟩, hx⟩ := (mem_filter.1 hφ).2
    obtain ⟨i, -, hi⟩ := mem_image.1 hx
    exact ⟨y, mem_biUnion.2 ⟨i, mem_univ _, mem_filter.2 ⟨mem_univ _, by rw [← hy i, hi]⟩⟩, hy⟩
  choose! g hg hgφ using hex
  have hginj : Set.InjOn g (univ.filter fun φ : Fin q → Fin n =>
      (∃ y, ∀ i, f (φ i) = mvec M y i) ∧ x ∈ univ.image φ : Set (Fin q → Fin n)) := by
    intro φ hφ φ' hφ' h
    funext i
    apply hf
    rw [hgφ φ hφ i, hgφ φ' hφ' i, h]
  refine (card_le_card_of_injOn g (fun φ hφ => hg φ hφ) hginj).trans
    (card_biUnion_le.trans ?_)
  calc ∑ i : Fin q, (univ.filter fun y : Fin r → K => mvec M y i = f x).card
      ≤ ∑ _i : Fin q, Fintype.card K ^ (r - 1) := by
        refine sum_le_sum fun i _ => ?_
        obtain ⟨k, hk⟩ := Function.ne_iff.1 (hM i)
        have hk' : algebraMap F K (M i k) ≠ 0 := (map_ne_zero _).2 hk
        convert card_affine_le (c := fun l => algebraMap F K (M i l)) hk' (f x) using 3
        simp [mvec, mulVec, dotProduct]
    _ = q * Fintype.card K ^ (r - 1) := by simp

end DesignsII
