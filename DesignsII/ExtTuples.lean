/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import DesignsII.Tuples
public import DesignsII.ConflictCount
public import DesignsII.TemplateSpace

/-!
# Candidate tuples for Lemma `ext*`

Given per-edge sets `A i` of injective copies having the distinct `r`-sets `e i` as edges, the
tuples `φ ∈ ∏ A i` that are injective with pairwise edge-disjoint copies (the sets `T_b` of
`ext_star`) miss at most `∑_{i ≠ i'} K ∏_{l ≠ i, i'} |A l|` tuples, with
`K = q^{r+1} n^{q-r-1} · q^r n^{q-r} · (1 + C(q,r))` (`card_goodTuples_ge`).
-/

@[expose] public section

namespace DesignsII

open Finset

namespace TParams

variable {P : TParams}

open Classical in
/-- The good tuples: injective, with pairwise edge-disjoint copies. -/
noncomputable def goodTuples {m : ℕ} (A : Fin m → Finset (Fin P.q → Fin P.n)) :
    Finset (Fin m → Fin P.q → Fin P.n) :=
  (Fintype.piFinset A).filter fun φ =>
    Function.Injective φ ∧ ∀ i i', i ≠ i' → Disjoint (edges (φ i)) (edges (φ i'))

open Classical in
/-- **Almost all tuples are good.** -/
theorem card_goodTuples_ge {m : ℕ} (e : Fin m → Finset (Fin P.n)) (he : ∀ i, (e i).card = P.r)
    (heinj : Function.Injective e) (A : Fin m → Finset (Fin P.q → Fin P.n))
    (hAe : ∀ i, ∀ φ ∈ A i, e i ∈ edges φ) :
    ∏ i, (A i).card ≤ (goodTuples A).card +
      ∑ p ∈ univ.filter (fun p : Fin m × Fin m => p.1 ≠ p.2),
        P.q ^ (P.r + 1) * P.n ^ (P.q - (P.r + 1)) * (P.q ^ P.r * P.n ^ (P.q - P.r)) *
          (1 + P.q.choose P.r) * ∏ l ∈ (univ.erase p.1).erase p.2, (A l).card := by
  set R : Fin m → Fin m → (Fin P.q → Fin P.n) → (Fin P.q → Fin P.n) → Prop := fun _ _ x y =>
    ∃ f : Finset (Fin P.n), f.card = P.r ∧ f ⊆ univ.image x ∧ f ⊆ univ.image y
  have hsplit : Fintype.piFinset A ⊆ goodTuples A ∪
      (Fintype.piFinset A).filter fun φ => ∃ i i', i ≠ i' ∧ R i i' (φ i) (φ i') := by
    intro φ hφ
    by_cases hg : Function.Injective φ ∧ ∀ i i', i ≠ i' → Disjoint (edges (φ i)) (edges (φ i'))
    · exact mem_union_left _ (mem_filter.2 ⟨hφ, hg⟩)
    refine mem_union_right _ (mem_filter.2 ⟨hφ, ?_⟩)
    have hmem : ∀ i, φ i ∈ A i := fun i => Fintype.mem_piFinset.1 hφ i
    rw [not_and_or] at hg
    rcases hg with hinj | hdisj
    · simp only [Function.Injective, not_forall] at hinj
      obtain ⟨i, i', hii, hne⟩ := hinj
      have he' := mem_powersetCard.1 (hAe i _ (hmem i))
      exact ⟨i, i', hne, e i, he i, he'.1, hii ▸ he'.1⟩
    · push Not at hdisj
      obtain ⟨i, i', hne, hnd⟩ := hdisj
      obtain ⟨f, hf1, hf2⟩ := not_disjoint_iff.1 hnd
      exact ⟨i, i', hne, f, (mem_powersetCard.1 hf1).2, (mem_powersetCard.1 hf1).1,
        (mem_powersetCard.1 hf2).1⟩
  calc ∏ i, (A i).card = (Fintype.piFinset A).card := (Fintype.card_piFinset A).symm
    _ ≤ (goodTuples A).card + ((Fintype.piFinset A).filter fun φ =>
          ∃ i i', i ≠ i' ∧ R i i' (φ i) (φ i')).card :=
        (card_le_card hsplit).trans (card_union_le _ _)
    _ ≤ _ := by
        refine Nat.add_le_add_left ((card_bad_tuples_le A R).trans (sum_le_sum fun p hp => ?_)) _
        refine Nat.mul_le_mul_right _ ?_
        have hne : p.1 ≠ p.2 := (mem_filter.1 hp).2
        refine (card_le_card ?_).trans (card_conflict_pairs_le (q := P.q) (he p.1) (he p.2)
          fun h => hne (heinj h))
        intro xy hxy
        obtain ⟨hprod, hR⟩ := mem_filter.1 hxy
        obtain ⟨h1, h2⟩ := mem_product.1 hprod
        refine mem_filter.2 ⟨mem_product.2 ⟨?_, ?_⟩, hR⟩
        · exact mem_filter.2 ⟨mem_univ _, (mem_powersetCard.1 (hAe p.1 _ h1)).1⟩
        · exact mem_filter.2 ⟨mem_univ _, (mem_powersetCard.1 (hAe p.2 _ h2)).1⟩

end TParams

end DesignsII
