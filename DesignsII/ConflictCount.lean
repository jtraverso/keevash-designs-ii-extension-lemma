/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import DesignsII.ImageCount

/-!
# Pairs of covering copies sharing an edge

For `r`-sets `e ≠ e'` of `[n]` let `A e` be the maps `ψ : [q] → [n]` with `e ⊆ ψ([q])`. The pairs
`(ψ, ψ') ∈ A e × A e'` whose images share an `r`-set are at most
`q^{r+1} n^{q-r-1} · q^r n^{q-r} · (1 + C(q, r))` (`card_conflict_pairs_le`), a factor `n` fewer
than all pairs. (Either `e' ⊆ ψ([q])`, so `ψ([q])` contains an `(r+1)`-set `e ∪ {x}`; or the
shared `r`-set `f ≠ e'` of `ψ([q])` gives an `(r+1)`-set `e' ∪ {x} ⊆ ψ'([q])`.)
-/

@[expose] public section

namespace DesignsII

open Finset

variable {q n r : ℕ}

/-- The maps whose image contains `e`. -/
def covMaps (q : ℕ) (e : Finset (Fin n)) : Finset (Fin q → Fin n) :=
  univ.filter fun ψ => e ⊆ univ.image ψ

theorem card_covMaps_le (e : Finset (Fin n)) :
    (covMaps q e).card ≤ q ^ e.card * n ^ (q - e.card) :=
  card_image_supset_le e

theorem covMaps_anti {e e' : Finset (Fin n)} (h : e ⊆ e') : covMaps q e' ⊆ covMaps q e :=
  fun _ hψ => mem_filter.2 ⟨mem_univ _, h.trans (mem_filter.1 hψ).2⟩

/-- Some element of `f` outside `e'` (if any). -/
noncomputable def extraPt (f e' : Finset (Fin n)) : Finset (Fin n) := by
  classical
  exact if h : ∃ x ∈ f, x ∉ e' then insert (Classical.choose h) e' else e'

theorem card_extraPt {f e' : Finset (Fin n)} (h : ∃ x ∈ f, x ∉ e') :
    (extraPt f e').card = e'.card + 1 := by
  classical
  unfold extraPt
  rw [dif_pos h, card_insert_of_notMem (Classical.choose_spec h).2]

theorem extraPt_subset {f e' X : Finset (Fin n)} (h : ∃ x ∈ f, x ∉ e') (hf : f ⊆ X)
    (he' : e' ⊆ X) : extraPt f e' ⊆ X := by
  classical
  unfold extraPt
  rw [dif_pos h]
  exact insert_subset (hf (Classical.choose_spec h).1) he'

theorem exists_outside {f e' : Finset (Fin n)} (hc : f.card = e'.card) (hne : f ≠ e') :
    ∃ x ∈ f, x ∉ e' := by
  by_contra h
  push Not at h
  exact hne (eq_of_subset_of_card_le h hc.ge)

/-- **Few pairs of covering copies share an `r`-set.** -/
theorem card_conflict_pairs_le {e e' : Finset (Fin n)} (he : e.card = r) (he' : e'.card = r)
    (hne : e ≠ e') :
    ((covMaps q e ×ˢ covMaps q e').filter fun p =>
        ∃ f : Finset (Fin n), f.card = r ∧ f ⊆ univ.image p.1 ∧ f ⊆ univ.image p.2).card ≤
      q ^ (r + 1) * n ^ (q - (r + 1)) * (q ^ r * n ^ (q - r)) * (1 + q.choose r) := by
  classical
  obtain ⟨x, hx, hxe⟩ := exists_outside (he'.trans he.symm) hne.symm
  set caseA := covMaps q (insert x e) ×ˢ covMaps q e'
  set caseB := (covMaps q e).biUnion fun ψ =>
    (((univ.image ψ).powersetCard r).filter (· ≠ e')).biUnion fun f =>
      ({ψ} : Finset (Fin q → Fin n)) ×ˢ covMaps q (extraPt f e')
  have hsub : ((covMaps q e ×ˢ covMaps q e').filter fun p =>
      ∃ f : Finset (Fin n), f.card = r ∧ f ⊆ univ.image p.1 ∧ f ⊆ univ.image p.2) ⊆
      caseA ∪ caseB := by
    rintro ⟨ψ, ψ'⟩ hp
    obtain ⟨hp1, f, hfc, hf1, hf2⟩ := mem_filter.1 hp
    obtain ⟨hψ, hψ'⟩ := mem_product.1 hp1
    have hψ_e : e ⊆ univ.image ψ := (mem_filter.1 hψ).2
    have hψ'_e : e' ⊆ univ.image ψ' := (mem_filter.1 hψ').2
    by_cases hfe : f = e'
    · subst hfe
      refine mem_union_left _ (mem_product.2 ⟨mem_filter.2 ⟨mem_univ _, ?_⟩, hψ'⟩)
      exact insert_subset (hf1 hx) hψ_e
    · refine mem_union_right _ (mem_biUnion.2 ⟨ψ, hψ, mem_biUnion.2 ⟨f, ?_, ?_⟩⟩)
      · exact mem_filter.2 ⟨mem_powersetCard.2 ⟨hf1, hfc⟩, hfe⟩
      · refine mem_product.2 ⟨mem_singleton_self _, mem_filter.2 ⟨mem_univ _, ?_⟩⟩
        exact extraPt_subset (exists_outside (hfc.trans he'.symm) hfe) hf2 hψ'_e
  refine (card_le_card hsub).trans ((card_union_le _ _).trans ?_)
  have hA : caseA.card ≤ q ^ (r + 1) * n ^ (q - (r + 1)) * (q ^ r * n ^ (q - r)) := by
    rw [card_product]
    have h1 := card_covMaps_le (q := q) (insert x e)
    rw [card_insert_of_notMem hxe, he] at h1
    have h2 := card_covMaps_le (q := q) e'
    rw [he'] at h2
    exact Nat.mul_le_mul h1 h2
  have hB : caseB.card ≤ q ^ (r + 1) * n ^ (q - (r + 1)) * (q ^ r * n ^ (q - r)) * q.choose r := by
    refine card_biUnion_le.trans ?_
    calc ∑ ψ ∈ covMaps q e, ((((univ.image ψ).powersetCard r).filter (· ≠ e')).biUnion fun f =>
          ({ψ} : Finset (Fin q → Fin n)) ×ˢ covMaps q (extraPt f e')).card
        ≤ ∑ _ψ ∈ covMaps q e, q.choose r * (q ^ (r + 1) * n ^ (q - (r + 1))) := by
          refine sum_le_sum fun ψ _ => card_biUnion_le.trans ?_
          calc _ ≤ ∑ _f ∈ ((univ.image ψ).powersetCard r).filter (· ≠ e'),
                q ^ (r + 1) * n ^ (q - (r + 1)) := by
                refine sum_le_sum fun f hf => ?_
                obtain ⟨hf1, hfe⟩ := mem_filter.1 hf
                have hfc := (mem_powersetCard.1 hf1).2
                rw [card_product, card_singleton, one_mul]
                have := card_covMaps_le (q := q) (extraPt f e')
                rwa [card_extraPt (exists_outside (hfc.trans he'.symm) hfe), he'] at this
            _ ≤ q.choose r * (q ^ (r + 1) * n ^ (q - (r + 1))) := by
                rw [sum_const, smul_eq_mul]
                gcongr
                refine (card_le_card (filter_subset _ _)).trans ?_
                rw [card_powersetCard]
                exact Nat.choose_le_choose r (card_image_le.trans (by simp))
      _ ≤ _ := by
          rw [sum_const, smul_eq_mul]
          have := card_covMaps_le (q := q) e
          rw [he] at this
          calc (covMaps q e).card * (q.choose r * (q ^ (r + 1) * n ^ (q - (r + 1))))
              ≤ (q ^ r * n ^ (q - r)) * (q.choose r * (q ^ (r + 1) * n ^ (q - (r + 1)))) :=
                Nat.mul_le_mul_right _ this
            _ = _ := by ring
  calc caseA.card + caseB.card ≤ _ + _ := Nat.add_le_add hA hB
    _ = _ := by ring

end DesignsII
