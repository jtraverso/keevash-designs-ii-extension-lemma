/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib

/-!
# Maps whose image contains a given set

`card_image_supset_le`: at most `q^{|S|} n^{q - |S|}` maps `ψ : [q] → [n]` have `S ⊆ ψ([q])`.

(Union bound over the positions `g : S ↪ [q]` of the elements of `S`: the maps with
`ψ (g s) = s` are free on the other `q - |S|` positions.)
-/

@[expose] public section

namespace DesignsII

open Finset

variable {q n : ℕ}

/-- Maps with prescribed values on the range of an injection `g : S ↪ [q]`. -/
theorem card_maps_fix (S : Finset (Fin n)) (g : S ↪ Fin q) :
    (univ.filter fun ψ : Fin q → Fin n => ∀ s : S, ψ (g s) = s).card = n ^ (q - S.card) := by
  classical
  set T : Fin q → Finset (Fin n) := fun k =>
    if h : ∃ s : S, g s = k then {(Classical.choose h : S).1} else univ
  have hset : (univ.filter fun ψ : Fin q → Fin n => ∀ s : S, ψ (g s) = s) =
      Fintype.piFinset T := by
    ext ψ
    simp only [mem_filter, mem_univ, true_and, Fintype.mem_piFinset, T]
    constructor
    · intro h k
      split_ifs with hk
      · have hs := Classical.choose_spec hk
        rw [mem_singleton]
        conv_lhs => rw [← hs]
        exact h _
      · exact mem_univ _
    · intro h s
      have hk : ∃ s' : S, g s' = g s := ⟨s, rfl⟩
      have := h (g s)
      rw [dif_pos hk, mem_singleton] at this
      rw [this]
      congr 1
      exact g.injective (Classical.choose_spec hk)
  rw [hset, Fintype.card_piFinset]
  have hrange : (univ.filter fun k : Fin q => ∃ s : S, g s = k).card = S.card := by
    rw [show (univ.filter fun k : Fin q => ∃ s : S, g s = k) = univ.map g by
      ext k; simp [eq_comm]]
    simp
  rw [← prod_filter_mul_prod_filter_not univ (fun k : Fin q => ∃ s : S, g s = k)]
  have hT1 : ∀ k, (∃ s : S, g s = k) → (T k).card = 1 := fun k hk => by
    simp only [T, dif_pos hk, card_singleton]
  have hT2 : ∀ k, ¬(∃ s : S, g s = k) → (T k).card = n := fun k hk => by
    simp only [T, dif_neg hk, card_univ, Fintype.card_fin]
  rw [prod_congr rfl fun k hk => hT1 k (mem_filter.1 hk).2,
    prod_congr rfl fun k hk => hT2 k (mem_filter.1 hk).2, prod_const_one, one_mul, prod_const]
  congr 1
  rw [filter_not, card_sdiff_of_subset (filter_subset _ _), hrange, card_univ, Fintype.card_fin]

/-- **At most `q^{|S|} n^{q-|S|}` maps `[q] → [n]` have image containing `S`.** -/
theorem card_image_supset_le (S : Finset (Fin n)) :
    (univ.filter fun ψ : Fin q → Fin n => S ⊆ univ.image ψ).card ≤
      q ^ S.card * n ^ (q - S.card) := by
  classical
  calc _ ≤ ∑ g : S ↪ Fin q, (univ.filter fun ψ : Fin q → Fin n => ∀ s : S, ψ (g s) = s).card := by
        refine (card_le_card fun ψ hψ => ?_).trans card_biUnion_le
        have hS : ∀ s : S, ∃ k, ψ k = s := fun s => by
          obtain ⟨k, -, hk⟩ := mem_image.1 ((mem_filter.1 hψ).2 s.2)
          exact ⟨k, hk⟩
        choose g hg using hS
        have hginj : Function.Injective g := fun s s' h => Subtype.ext (by rw [← hg, ← hg, h])
        exact mem_biUnion.2 ⟨⟨g, hginj⟩, mem_univ _, mem_filter.2 ⟨mem_univ _, hg⟩⟩
    _ = Fintype.card (S ↪ Fin q) * n ^ (q - S.card) := by
        rw [sum_congr rfl fun g _ => card_maps_fix S g, sum_const, card_univ, smul_eq_mul]
    _ ≤ q ^ S.card * n ^ (q - S.card) := by
        gcongr
        rw [Fintype.card_embedding_eq, Fintype.card_fin, Fintype.card_coe]
        exact Nat.descFactorial_le_pow q S.card

end DesignsII
