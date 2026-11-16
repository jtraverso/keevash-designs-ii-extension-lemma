/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import DesignsII.ExtDefs
public import DesignsII.Template
public import DesignsII.PermCount

/-!
# The probability that a copy is compatible with `f_j` (Keevash, *Designs II*, proof of Lemma
`e|E`)

Let `K` be a finite field with `N` elements, identified with `[N]` by `κ`, `F ⊆ K` a subfield and
`M ∈ F^{q × r}` generic with pairwise distinct rows. A uniformly random injection `f_j` is
modelled by a uniform permutation `σ` of `[N]` (`f_j(x) = κ(σ x)`). For fixed distinct positions
`w : [q] ↪ [N]`:

* `card_compat`: the number of `σ` with `κ ∘ σ ∘ w = M y` for some `y ∈ K^r` is
  `#{y : My injective} · (N - q)!`;
* `card_y_not_inj_le`: at most `q² N^{r-1}` vectors `y` have `My` non-injective;

so the probability is `(1 ± q²/N) N^r / (N)_q`, i.e. `(1 + O(n^{-1})) (p^{-a})^{q-r}` as in the
paper.
-/

@[expose] public section

namespace DesignsII

open Finset Matrix Equiv

variable {F K : Type*} [Field F] [Field K] [Algebra F K] [Fintype K] [DecidableEq K] {q r N : ℕ}

/-- A nonzero linear form over `K` vanishes on at most `N^{r-1}` vectors. -/
theorem card_ker_le {c : Fin r → K} {k : Fin r} (hk : c k ≠ 0) :
    (univ.filter fun y : Fin r → K => ∑ l, c l * y l = 0).card ≤
      Fintype.card K ^ (r - 1) := by
  classical
  have hinj : Set.InjOn (fun y : Fin r → K => fun l : {l // l ≠ k} => y l)
      (univ.filter fun y : Fin r → K => ∑ l, c l * y l = 0 : Set (Fin r → K)) := by
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

/-- At most `q² N^{r-1}` vectors `y` have `M y` non-injective. -/
theorem card_y_not_inj_le {M : Matrix (Fin q) (Fin r) F} (hM : DistinctRows M) :
    (univ.filter fun y : Fin r → K => ¬ Function.Injective (mvec M y)).card ≤
      q ^ 2 * Fintype.card K ^ (r - 1) := by
  classical
  have hsub : (univ.filter fun y : Fin r → K => ¬ Function.Injective (mvec M y)) ⊆
      (univ.filter fun p : Fin q × Fin q => p.1 ≠ p.2).biUnion fun p =>
        univ.filter fun y : Fin r → K =>
          ∑ l, (algebraMap F K (M p.1 l) - algebraMap F K (M p.2 l)) * y l = 0 := by
    intro y hy
    simp only [mem_filter, mem_univ, true_and, Function.Injective, not_forall] at hy
    obtain ⟨i, i', hii, hne⟩ := hy
    simp only [mem_biUnion, mem_filter, mem_univ, true_and]
    refine ⟨(i, i'), hne, ?_⟩
    simp only [mvec, mulVec, dotProduct, map_apply] at hii
    simp only [sub_mul, sum_sub_distrib, hii, sub_self]
  refine (card_le_card hsub).trans (card_biUnion_le.trans ?_)
  calc ∑ p ∈ univ.filter (fun p : Fin q × Fin q => p.1 ≠ p.2),
        (univ.filter fun y : Fin r → K =>
          ∑ l, (algebraMap F K (M p.1 l) - algebraMap F K (M p.2 l)) * y l = 0).card
      ≤ ∑ _p ∈ univ.filter (fun p : Fin q × Fin q => p.1 ≠ p.2), Fintype.card K ^ (r - 1) := by
        refine sum_le_sum fun p hp => ?_
        have hne : M p.1 ≠ M p.2 := fun h => (mem_filter.1 hp).2 (hM h)
        obtain ⟨k, hk⟩ := Function.ne_iff.1 hne
        exact card_ker_le (k := k) (by
          rw [sub_ne_zero]; exact fun h => hk ((algebraMap F K).injective h))
    _ ≤ q ^ 2 * Fintype.card K ^ (r - 1) := by
        rw [sum_const, smul_eq_mul]
        gcongr
        calc _ ≤ (univ : Finset (Fin q × Fin q)).card := card_le_card (filter_subset _ _)
          _ = q ^ 2 := by simp [sq]

/-- **The number of permutations compatible with `M` at the positions `w`.** -/
theorem card_compat {M : Matrix (Fin q) (Fin r) F} (hM : IsGeneric M) (hrq : r ≤ q)
    (κ : Fin N ≃ K) (w : Fin q ↪ Fin N) :
    (univ.filter fun σ : Perm (Fin N) => ∃ y, ∀ i, κ (σ (w i)) = mvec M y i).card =
      (univ.filter fun y : Fin r → K => Function.Injective (mvec M y)).card *
        (N - q).factorial := by
  classical
  obtain ⟨B, -, hB⟩ := exists_subset_card_eq (s := (univ : Finset (Fin q))) (n := r)
    (by simpa using hrq)
  set Y := univ.filter fun y : Fin r → K => Function.Injective (mvec M y)
  set u : Y → (Fin q ↪ Fin N) := fun y =>
    ⟨fun i => κ.symm (mvec M y.1 i), fun i i' h => (mem_filter.1 y.2).2 (κ.symm.injective h)⟩
  have hset : (univ.filter fun σ : Perm (Fin N) => ∃ y, ∀ i, κ (σ (w i)) = mvec M y i) =
      Y.attach.biUnion fun y => univ.filter fun σ : Perm (Fin N) => ∀ i, σ (w i) = u y i := by
    ext σ
    simp only [mem_filter, mem_univ, true_and, mem_biUnion, mem_attach]
    constructor
    · rintro ⟨y, hy⟩
      have hyinj : Function.Injective (mvec M y) := by
        intro i i' h
        rw [← hy i, ← hy i'] at h
        exact w.injective (σ.injective (κ.injective h))
      refine ⟨⟨y, mem_filter.2 ⟨mem_univ _, hyinj⟩⟩, ?_⟩
      intro i
      show σ (w i) = κ.symm (mvec M y i)
      rw [← hy i, κ.symm_apply_apply]
    · rintro ⟨y, hy⟩
      refine ⟨y.1, fun i => ?_⟩
      rw [hy i]
      exact κ.apply_symm_apply _
  rw [hset, card_biUnion]
  · rw [sum_congr rfl fun y _ => card_perm_fix w (u y), sum_const, card_attach, smul_eq_mul]
  · intro y _ y' _ hyy
    rw [Function.onFun, disjoint_left]
    intro σ h1 h2
    simp only [mem_filter, mem_univ, true_and] at h1 h2
    apply hyy
    apply Subtype.ext
    refine generic_rows_inj hM hB fun i _ => ?_
    have := (h1 i).symm.trans (h2 i)
    exact κ.symm.injective this

end DesignsII
