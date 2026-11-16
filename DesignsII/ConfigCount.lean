/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Counting configurations of an extension

Configurations of an extension `E = (H, F, φ)` are maps `b : NV → V` on the new vertices. If the
new vertices `W i ⊆ NV` of the `i`-th edge are mapped into the edge `e b i` (an `r`-set), then
the configurations with a given `i`-th edge number at most `r^{|W i|} |V|^{|NV| - |W i|}`
(`card_config_edge_le`), i.e. `D_i ≤ r^r n^{v-(r-f_i)}` in Lemma `ext*`.
-/

@[expose] public section

namespace DesignsII

open Finset

variable {α V : Type*} [Fintype α] [DecidableEq α] [Fintype V] [DecidableEq V]

/-- Maps with prescribed values on `W` constrained to `E`. -/
theorem card_fun_constrained (W : Finset α) (E : Finset V) :
    (univ.filter fun g : α → V => ∀ w ∈ W, g w ∈ E).card =
      E.card ^ W.card * Fintype.card V ^ (Fintype.card α - W.card) := by
  classical
  rw [← Fintype.card_subtype]
  rw [Fintype.card_congr (Equiv.subtypePiEquivPi (p := fun a v => a ∈ W → v ∈ E)),
    Fintype.card_pi]
  have h : ∀ a, Fintype.card {v // a ∈ W → v ∈ E} = if a ∈ W then E.card else Fintype.card V := by
    intro a
    split_ifs with ha
    · rw [Fintype.card_subtype]; simp [ha]
    · rw [Fintype.card_subtype]; simp [ha]
  rw [Fintype.prod_congr _ _ h, prod_ite, prod_const, prod_const]
  congr 2
  · simp
  · have := card_filter_add_card_filter_not (s := (univ : Finset α)) (fun a => a ∈ W)
    rw [card_univ] at this
    have hW : (univ.filter fun a => a ∈ W).card = W.card := by
      congr 1; ext; simp
    omega

/-- **Configurations with a given `i`-th edge.** -/
theorem card_config_edge_le {m r : ℕ} (C : Finset (α → V)) (e : (α → V) → Fin m → Finset V)
    (W : Fin m → Finset α) (hW : ∀ b ∈ C, ∀ i, ∀ w ∈ W i, b w ∈ e b i)
    (hcard : ∀ b ∈ C, ∀ i, (e b i).card = r) (i : Fin m) (e' : Finset V) :
    (C.filter fun b => e b i = e').card ≤
      r ^ (W i).card * Fintype.card V ^ (Fintype.card α - (W i).card) := by
  classical
  by_cases hex : ∃ b ∈ C, e b i = e'
  · obtain ⟨b₀, hb₀, he₀⟩ := hex
    have hr : e'.card = r := he₀ ▸ hcard b₀ hb₀ i
    rw [← hr, ← card_fun_constrained (W i) e']
    refine card_le_card fun b hb => ?_
    obtain ⟨hbC, hbe⟩ := mem_filter.1 hb
    exact mem_filter.2 ⟨mem_univ _, fun w hw => hbe ▸ hW b hbC i w hw⟩
  · push Not at hex
    rw [filter_false_of_mem fun b hb h => hex b hb h, card_empty]
    exact Nat.zero_le _

/-- At most `|V|^{|NV|}` configurations. -/
theorem card_config_le (C : Finset (α → V)) : C.card ≤ Fintype.card V ^ Fintype.card α := by
  simpa [Fintype.card_fun] using card_le_univ C
/-- Maps with prescribed values on `W`. -/
theorem card_fix_on (W : Finset α) (c : α → V) :
    (univ.filter fun g : α → V => ∀ w ∈ W, g w = c w).card =
      Fintype.card V ^ (Fintype.card α - W.card) := by
  classical
  have h := card_fun_constrained (V := V) W
  set T : α → Finset V := fun y => if y ∈ W then {c y} else univ
  have hset : (univ.filter fun g : α → V => ∀ w ∈ W, g w = c w) = Fintype.piFinset T := by
    ext g
    simp only [mem_filter, mem_univ, true_and, Fintype.mem_piFinset, T]
    constructor
    · intro hg y; split_ifs with hy
      · simp [hg y hy]
      · exact mem_univ _
    · intro hg w hw; have := hg w; simp only [hw, if_true, mem_singleton] at this; exact this
  rw [hset, Fintype.card_piFinset]
  have hT : ∀ y, (T y).card = if y ∈ W then 1 else Fintype.card V := by
    intro y; simp only [T]; split_ifs <;> simp
  rw [Fintype.prod_congr _ _ hT, prod_ite, prod_const, prod_const, one_pow, one_mul]
  congr 1
  have := card_filter_add_card_filter_not (s := (univ : Finset α)) (fun a => a ∈ W)
  rw [card_univ] at this
  have hW : (univ.filter fun a => a ∈ W).card = W.card := by congr 1; ext; simp
  omega

/-- **Maps fixed on `B` sending some other point into `U`.** -/
theorem card_fix_hit_le (B : Finset α) (c : α → V) (U : Finset V) :
    (univ.filter fun g : α → V => (∀ w ∈ B, g w = c w) ∧ ∃ x ∉ B, g x ∈ U).card ≤
      (Fintype.card α - B.card) * (U.card * Fintype.card V ^ (Fintype.card α - B.card - 1)) := by
  classical
  have hsub : (univ.filter fun g : α → V => (∀ w ∈ B, g w = c w) ∧ ∃ x ∉ B, g x ∈ U) ⊆
      (univ \ B).biUnion fun x => U.biUnion fun u =>
        univ.filter fun g : α → V => ∀ w ∈ insert x B, g w = Function.update c x u w := by
    intro g hg
    obtain ⟨hB, x, hx, hU⟩ := (mem_filter.1 hg).2
    refine mem_biUnion.2 ⟨x, mem_sdiff.2 ⟨mem_univ _, hx⟩, mem_biUnion.2 ⟨g x, hU,
      mem_filter.2 ⟨mem_univ _, fun w hw => ?_⟩⟩⟩
    rcases mem_insert.1 hw with rfl | hw
    · simp
    · rw [Function.update_of_ne (fun h : w = x => hx (h ▸ hw)), hB w hw]
  refine (card_le_card hsub).trans (card_biUnion_le.trans ?_)
  calc ∑ x ∈ univ \ B, (U.biUnion fun u => univ.filter fun g : α → V =>
        ∀ w ∈ insert x B, g w = Function.update c x u w).card
      ≤ ∑ _x ∈ univ \ B, U.card * Fintype.card V ^ (Fintype.card α - B.card - 1) := by
        refine sum_le_sum fun x hx => card_biUnion_le.trans ?_
        have hxB : x ∉ B := (mem_sdiff.1 hx).2
        refine le_of_eq ?_
        calc ∑ u ∈ U, (univ.filter fun g : α → V =>
              ∀ w ∈ insert x B, g w = Function.update c x u w).card
            = ∑ _u ∈ U, Fintype.card V ^ (Fintype.card α - B.card - 1) := by
              refine sum_congr rfl fun u _ => ?_
              rw [card_fix_on, card_insert_of_notMem hxB, Nat.sub_sub]
          _ = U.card * Fintype.card V ^ (Fintype.card α - B.card - 1) := sum_const _
    _ = _ := by
        rw [sum_const, card_sdiff_of_subset (subset_univ _), card_univ]; rfl

end DesignsII
