/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib

/-!
# Counting tuples with a conflicting pair

For finite sets `S_1, …, S_m` and a relation `R i i'` ("conflict", e.g. two covering copies that
coincide or share an edge), the number of tuples `(x_i) ∈ ∏ S_i` having a conflicting pair is at
most `∑_{i ≠ i'} #{(x, y) ∈ S_i × S_{i'} : R i i' x y} · ∏_{l ≠ i, i'} |S_l|` (`card_bad_tuples_le`).
Used to show that almost all tuples of covering copies in Lemma `ext*` are edge-disjoint.
-/

@[expose] public section

namespace DesignsII

open Finset

variable {m : ℕ} {α : Type*} [DecidableEq α]

/-- The number of tuples with prescribed entries `x` at `i` and `y` at `i' ≠ i`. -/
theorem card_tuples_fix2 (S : Fin m → Finset α) {i i' : Fin m} (hii : i ≠ i') {x y : α}
    (hx : x ∈ S i) (hy : y ∈ S i') :
    ((Fintype.piFinset S).filter fun φ => φ i = x ∧ φ i' = y).card =
      ∏ l ∈ (univ.erase i).erase i', (S l).card := by
  classical
  set S' : Fin m → Finset α := fun l => if l = i then {x} else if l = i' then {y} else S l
  have hset : ((Fintype.piFinset S).filter fun φ => φ i = x ∧ φ i' = y) =
      Fintype.piFinset S' := by
    ext φ
    simp only [mem_filter, Fintype.mem_piFinset, S']
    constructor
    · rintro ⟨h, rfl, rfl⟩ l
      by_cases h1 : l = i
      · subst h1; simp
      · by_cases h2 : l = i'
        · subst h2; simp [h1]
        · simp [h1, h2, h l]
    · intro h
      have hxi := h i
      have hyi := h i'
      simp only [if_true, mem_singleton] at hxi
      simp only [if_neg hii.symm, if_true, mem_singleton] at hyi
      refine ⟨fun l => ?_, hxi, hyi⟩
      by_cases h1 : l = i
      · subst h1; rw [hxi]; exact hx
      · by_cases h2 : l = i'
        · subst h2; rw [hyi]; exact hy
        · have := h l; simpa [h1, h2] using this
  rw [hset, Fintype.card_piFinset, ← mul_prod_erase univ _ (mem_univ i),
    ← mul_prod_erase (univ.erase i) _ (mem_erase.2 ⟨hii.symm, mem_univ i'⟩)]
  simp only [S', if_true, if_neg hii.symm, card_singleton, one_mul]
  refine prod_congr rfl fun l hl => ?_
  have h2 : l ≠ i' := ne_of_mem_erase hl
  have h1 : l ≠ i := ne_of_mem_erase (mem_of_mem_erase hl)
  simp [h1, h2]

/-- **Union bound for tuples with a conflicting pair.** -/
theorem card_bad_tuples_le (S : Fin m → Finset α) (R : Fin m → Fin m → α → α → Prop)
    [∀ i i', DecidableRel (R i i')] :
    ((Fintype.piFinset S).filter fun φ => ∃ i i', i ≠ i' ∧ R i i' (φ i) (φ i')).card ≤
      ∑ p ∈ univ.filter (fun p : Fin m × Fin m => p.1 ≠ p.2),
        ((S p.1 ×ˢ S p.2).filter fun xy => R p.1 p.2 xy.1 xy.2).card *
          ∏ l ∈ (univ.erase p.1).erase p.2, (S l).card := by
  classical
  calc _ ≤ ∑ p ∈ univ.filter (fun p : Fin m × Fin m => p.1 ≠ p.2),
        ((Fintype.piFinset S).filter fun φ => R p.1 p.2 (φ p.1) (φ p.2)).card := by
        refine (card_le_card ?_).trans card_biUnion_le
        intro φ hφ
        obtain ⟨hS, i, i', hii, hR⟩ := by simpa only [mem_filter] using hφ
        exact mem_biUnion.2 ⟨(i, i'), by simpa using hii, mem_filter.2 ⟨hS, hR⟩⟩
    _ ≤ _ := by
        refine sum_le_sum fun p hp => ?_
        have hp' : p.1 ≠ p.2 := (mem_filter.1 hp).2
        rw [card_eq_sum_card_fiberwise (f := fun φ : Fin m → α => (φ p.1, φ p.2))
          (t := (S p.1 ×ˢ S p.2).filter fun xy => R p.1 p.2 xy.1 xy.2) (fun φ hφ => by
            obtain ⟨hS, hR⟩ := mem_filter.1 hφ
            exact mem_filter.2 ⟨mem_product.2 ⟨Fintype.mem_piFinset.1 hS _,
              Fintype.mem_piFinset.1 hS _⟩, hR⟩)]
        rw [← smul_eq_mul, ← sum_const]
        refine sum_le_sum fun xy hxy => ?_
        obtain ⟨hxy1, -⟩ := mem_filter.1 hxy
        obtain ⟨hx, hy⟩ := mem_product.1 hxy1
        rw [← card_tuples_fix2 S hp' hx hy]
        refine card_le_card fun φ hφ => ?_
        obtain ⟨h1, h2⟩ := mem_filter.1 hφ
        refine mem_filter.2 ⟨(mem_filter.1 h1).1, ?_⟩
        simp only [Prod.ext_iff] at h2
        exact h2

end DesignsII
