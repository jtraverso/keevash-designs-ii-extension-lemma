/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import DesignsII.TemplateProb

/-!
# Affine slices of the template parametrisation (algebraic core of Lemma `e|E`)

When the values of `f_j` at the fixed vertices of a copy are revealed, the copies `φ` with
`f_j ∘ φ = M y` correspond to the `y` in the affine slice `{y : (M y)_i = c_i, i ∈ I₀}`, where
`I₀` are the positions of the fixed vertices.

`card_slice`: for `M` generic and `|I₀| ≤ r ≤ q`, the slice has exactly `N^{r - |I₀|}` points
(extend `I₀` to `r` rows `B`; `y ↦ (M y)|_B` is a bijection `K^r → K^B`).
-/

@[expose] public section

namespace DesignsII

open Finset Matrix

variable {F K : Type*} [Field F] [Field K] [Algebra F K] [Fintype K] [DecidableEq K] {q r : ℕ}

omit [DecidableEq K] in
/-- `y ↦ (M y)|_B` along an enumeration of `r` rows is a bijection. -/
theorem rowsMap_bijective {M : Matrix (Fin q) (Fin r) F} (hM : IsGeneric M) {B : Finset (Fin q)}
    (hB : B.card = r) :
    Function.Bijective fun y : Fin r → K => fun k : Fin r => mvec M y (B.orderEmbOfFin hB k) := by
  refine (Fintype.bijective_iff_injective_and_card _).2 ⟨fun y y' h => ?_, rfl⟩
  refine generic_rows_inj hM hB fun i hi => ?_
  obtain ⟨k, hk⟩ : ∃ k, B.orderEmbOfFin hB k = i := by
    have := (B.orderIsoOfFin hB).surjective ⟨i, hi⟩
    obtain ⟨k, hk⟩ := this
    exact ⟨k, by rw [← coe_orderIsoOfFin_apply, hk]⟩
  have := congrFun h k
  simp only [hk] at this
  exact this

/-- **The affine slice has `N^{r - |I₀|}` points.** -/
theorem card_slice {M : Matrix (Fin q) (Fin r) F} (hM : IsGeneric M) (hrq : r ≤ q)
    (I₀ : Finset (Fin q)) (hI₀ : I₀.card ≤ r) (c : Fin q → K) :
    (univ.filter fun y : Fin r → K => ∀ i ∈ I₀, mvec M y i = c i).card =
      Fintype.card K ^ (r - I₀.card) := by
  classical
  -- extend `I₀` to `r` rows
  obtain ⟨B, hIB, hB⟩ := exists_superset_card_eq (s := I₀) (n := r) hI₀ (by simpa using hrq)
  set b := B.orderEmbOfFin hB
  set Φ := fun y : Fin r → K => fun k : Fin r => mvec M y (b k)
  have hΦ : Function.Bijective Φ := rowsMap_bijective hM hB
  set T : Fin r → Finset K := fun k => if b k ∈ I₀ then {c (b k)} else univ
  have hbij : (univ.filter fun y : Fin r → K => ∀ i ∈ I₀, mvec M y i = c i).card =
      (Fintype.piFinset T).card := by
    refine card_bij (fun y _ => Φ y) (fun y hy => ?_) (fun y _ y' _ h => hΦ.1 h)
      (fun z hz => ?_)
    · rw [Fintype.mem_piFinset]
      intro k
      simp only [T]
      split_ifs with hk
      · exact mem_singleton.2 ((mem_filter.1 hy).2 _ hk)
      · exact mem_univ _
    · obtain ⟨y, rfl⟩ := hΦ.2 z
      refine ⟨y, mem_filter.2 ⟨mem_univ _, fun i hi => ?_⟩, rfl⟩
      obtain ⟨k, hk⟩ : ∃ k, b k = i := by
        obtain ⟨k, hk⟩ := (B.orderIsoOfFin hB).surjective ⟨i, hIB hi⟩
        exact ⟨k, by rw [← coe_orderIsoOfFin_apply, hk]⟩
      have := Fintype.mem_piFinset.1 hz k
      simp only [T, hk, hi, if_true, mem_singleton] at this
      have h' : mvec M y (b k) = c i := this
      rw [hk] at h'; exact h'
  rw [hbij, Fintype.card_piFinset]
  rw [← prod_filter_mul_prod_filter_not univ (fun k => b k ∈ I₀)]
  have h1 : ∀ k ∈ univ.filter (fun k => b k ∈ I₀), (T k).card = 1 := fun k hk => by
    simp [T, (mem_filter.1 hk).2]
  have h2 : ∀ k ∈ univ.filter (fun k => b k ∉ I₀), (T k).card = Fintype.card K := fun k hk => by
    simp [T, (mem_filter.1 hk).2]
  rw [prod_congr rfl h1, prod_congr rfl h2, prod_const_one, one_mul, prod_const]
  congr 1
  have hcount : (univ.filter fun k : Fin r => b k ∈ I₀).card = I₀.card := by
    rw [← card_map b.toEmbedding]
    congr 1
    ext i
    simp only [mem_map, mem_filter, mem_univ, true_and, RelEmbedding.coe_toEmbedding]
    constructor
    · rintro ⟨k, hk, rfl⟩; exact hk
    · intro hi
      obtain ⟨k, hk⟩ := (B.orderIsoOfFin hB).surjective ⟨i, hIB hi⟩
      exact ⟨k, by rw [show b k = i by rw [← coe_orderIsoOfFin_apply, hk]]; exact hi,
        by rw [← coe_orderIsoOfFin_apply, hk]⟩
  rw [filter_not, card_sdiff_of_subset (filter_subset _ _), hcount, card_univ, Fintype.card_fin]

end DesignsII
