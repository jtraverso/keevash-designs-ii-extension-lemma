/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import DesignsII.ESlice

/-!
# Candidate copies containing a prescribed set

`card_cand_supset_le`: for an injection `f : [n] → K`, a generic `M` and a set `A ⊆ [n]` with
`|A| ≤ r ≤ q`, at most `q^{|A|} N^{r - |A|}` maps `ψ : [q] → [n]` satisfy `f ∘ ψ = M y` for some
`y` and `A ⊆ ψ([q])`. (Union over the positions `g : A ↪ [q]`; for fixed `g`, `y` lies in the affine
slice `(M y)_{g a} = f a`, of size `N^{r-|A|}` by `card_slice`, and determines `ψ`.)

In Lemma `ext*` this is applied with `A = F_i ∪ {x}` (the fixed part of an edge plus one more
vertex): it bounds the Lipschitz constants of the covering count in the `f_j` coordinates by
`≈ n^{v-1}` (BLUEPRINT, concentration plan).
-/

@[expose] public section

namespace DesignsII

open Finset Matrix

variable {F K : Type*} [Field F] [Field K] [Algebra F K] [Fintype K] [DecidableEq K] {q r n : ℕ}

/-- Candidates with prescribed positions `g` of the points of `A`. -/
theorem card_cand_fixed_pos {M : Matrix (Fin q) (Fin r) F} (hM : IsGeneric M) (hrq : r ≤ q)
    {f : Fin n → K} (hf : Function.Injective f) (A : Finset (Fin n)) (hA : A.card ≤ r)
    (g : A ↪ Fin q) :
    (univ.filter fun ψ : Fin q → Fin n =>
      (∃ y, ∀ i, f (ψ i) = mvec M y i) ∧ ∀ a : A, ψ (g a) = a).card ≤
      Fintype.card K ^ (r - A.card) := by
  classical
  set c : Fin q → K := fun i => if h : ∃ a : A, g a = i then f (Classical.choose h).1 else 0
  have hc : ∀ a : A, c (g a) = f a := by
    intro a
    have h : ∃ a' : A, g a' = g a := ⟨a, rfl⟩
    simp only [c, dif_pos h]
    rw [g.injective (Classical.choose_spec h)]
  have hI : (univ.map g).card = A.card := by simp
  rw [← hI, ← card_slice hM hrq (univ.map g) (by rw [hI]; exact hA) c]
  -- `ψ ↦ y` (chosen) is injective into the slice
  have hex : ∀ ψ ∈ (univ.filter fun ψ : Fin q → Fin n =>
      (∃ y, ∀ i, f (ψ i) = mvec M y i) ∧ ∀ a : A, ψ (g a) = a),
      ∃ y, ∀ i, f (ψ i) = mvec M y i := fun ψ hψ => (mem_filter.1 hψ).2.1
  choose! yy hyy using hex
  refine card_le_card_of_injOn yy (fun ψ hψ => ?_) (fun ψ hψ ψ' hψ' h => ?_)
  · refine mem_filter.2 ⟨mem_univ _, fun i hi => ?_⟩
    obtain ⟨a, -, rfl⟩ := mem_map.1 hi
    rw [hc, ← hyy ψ hψ, (mem_filter.1 hψ).2.2 a]
  · funext i
    apply hf
    rw [hyy ψ hψ, hyy ψ' hψ', h]

/-- **Candidate copies whose image contains `A`.** -/
theorem card_cand_supset_le {M : Matrix (Fin q) (Fin r) F} (hM : IsGeneric M) (hrq : r ≤ q)
    {f : Fin n → K} (hf : Function.Injective f) (A : Finset (Fin n)) (hA : A.card ≤ r) :
    (univ.filter fun ψ : Fin q → Fin n =>
      (∃ y, ∀ i, f (ψ i) = mvec M y i) ∧ A ⊆ univ.image ψ).card ≤
      q ^ A.card * Fintype.card K ^ (r - A.card) := by
  classical
  have hsub : (univ.filter fun ψ : Fin q → Fin n =>
      (∃ y, ∀ i, f (ψ i) = mvec M y i) ∧ A ⊆ univ.image ψ) ⊆
      (univ : Finset (A ↪ Fin q)).biUnion fun g => univ.filter fun ψ : Fin q → Fin n =>
        (∃ y, ∀ i, f (ψ i) = mvec M y i) ∧ ∀ a : A, ψ (g a) = a := by
    intro ψ hψ
    obtain ⟨hy, hA⟩ := (mem_filter.1 hψ).2
    have hpre : ∀ a : A, ∃ i, ψ i = a := fun a => by
      obtain ⟨i, -, hi⟩ := mem_image.1 (hA a.2); exact ⟨i, hi⟩
    choose g hg using hpre
    refine mem_biUnion.2 ⟨⟨g, fun a a' h => Subtype.ext (by rw [← hg a, ← hg a', h])⟩,
      mem_univ _, mem_filter.2 ⟨mem_univ _, hy, hg⟩⟩
  refine (card_le_card hsub).trans (card_biUnion_le.trans ?_)
  calc _ ≤ ∑ _g : A ↪ Fin q, Fintype.card K ^ (r - A.card) :=
        sum_le_sum fun g _ => card_cand_fixed_pos hM hrq hf A hA g
    _ ≤ q ^ A.card * Fintype.card K ^ (r - A.card) := by
        rw [sum_const, card_univ, smul_eq_mul]
        gcongr
        rw [Fintype.card_embedding_eq, Fintype.card_fin, Fintype.card_coe]
        exact Nat.descFactorial_le_pow q A.card

end DesignsII
