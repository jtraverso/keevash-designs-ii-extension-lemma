/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import DesignsII.ESlice

/-!
# Affine systems with `F`-independent rows over an extension field

`card_affine_indep`: if `ρ_1, …, ρ_s ∈ F^r` are linearly independent over `F` and `K ⊇ F` has `N`
elements, then for any `c ∈ K^s` the system `ρ_k · y = c_k` (`k ≤ s`) has exactly `N^{r-s}`
solutions `y ∈ K^r`.

Proof: complete the rows by standard basis vectors to an invertible `r × r` matrix over `F`
(`exists_square_completion`); its determinant stays nonzero over `K`, so `y ↦ R y` is a bijection
of `K^r`, and the constraints fix `s` coordinates of `R y`.

Used for the collisions inside the affine slices of Lemma `e|E` (BLUEPRINT).
-/

@[expose] public section

namespace DesignsII

open Finset Matrix

variable {F K : Type*} [Field F] [Field K] [Algebra F K] [Fintype K] [DecidableEq K]

/-- Some standard basis vector lies outside the span of fewer than `r` vectors. -/
theorem exists_single_not_mem_span {r s : ℕ} (hs : s < r) (v : Fin s → Fin r → F) :
    ∃ k : Fin r, Pi.single k 1 ∉ Submodule.span F (Set.range v) := by
  by_contra h
  push Not at h
  have htop : Submodule.span F (Set.range v) = ⊤ := by
    rw [eq_top_iff, ← (Pi.basisFun F (Fin r)).span_eq, Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    simpa using h k
  have h1 := finrank_range_le_card (R := F) v
  unfold Set.finrank at h1
  rw [htop, finrank_top, Module.finrank_fin_fun, Fintype.card_fin] at h1
  omega

/-- **Completion to a square invertible matrix.** `F`-independent rows `v : Fin s → F^r` extend to
`r` independent rows whose first `s` are the given ones. -/
theorem exists_square_completion : ∀ (d : ℕ) {r s : ℕ} (_hd : s + d = r) (v : Fin s → Fin r → F),
    LinearIndependent F v →
    ∃ w : Fin r → Fin r → F, LinearIndependent F w ∧ ∀ k : Fin s, w (Fin.castLE (by omega) k) = v k
  | 0, r, s, hd, v, hv => by
    subst hd
    exact ⟨v, hv, fun k => rfl⟩
  | d + 1, r, s, hd, v, hv => by
    obtain ⟨k, hk⟩ := exists_single_not_mem_span (show s < r by omega) v
    have hv' : LinearIndependent F (Fin.snoc v (Pi.single k 1) : Fin (s + 1) → Fin r → F) :=
      (linearIndependent_finSnoc).2 ⟨hv, hk⟩
    obtain ⟨w, hw, hwv⟩ := exists_square_completion d (show s + 1 + d = r by omega) _ hv'
    refine ⟨w, hw, fun j => ?_⟩
    have := hwv (Fin.castSucc j)
    simp only [Fin.snoc_castSucc] at this
    rw [← this]
    rfl

omit [DecidableEq K] in
/-- An invertible matrix over `F` acts bijectively on `K^r`. -/
theorem mulVec_map_bijective {r : ℕ} {R : Matrix (Fin r) (Fin r) F}
    (hR : LinearIndependent F (fun k => R k)) :
    Function.Bijective fun y : Fin r → K => R.map (algebraMap F K) *ᵥ y := by
  have hdet : R.det ≠ 0 := by
    have := (Matrix.linearIndependent_rows_iff_isUnit (A := R)).1 hR
    exact (Matrix.isUnit_iff_isUnit_det R).1 this |>.ne_zero
  have hdetK : (R.map (algebraMap F K)).det ≠ 0 := by
    have : (R.map (algebraMap F K)).det = algebraMap F K R.det :=
      ((algebraMap F K).map_det R).symm
    rw [this]; exact (map_ne_zero _).2 hdet
  have hinj : Function.Injective fun y : Fin r → K => R.map (algebraMap F K) *ᵥ y := by
    intro y y' h
    have : R.map (algebraMap F K) *ᵥ (y - y') = 0 := by
      rw [mulVec_sub]; exact sub_eq_zero.2 h
    exact sub_eq_zero.1 (eq_zero_of_mulVec_eq_zero hdetK this)
  exact (Fintype.bijective_iff_injective_and_card _).2 ⟨hinj, rfl⟩

/-- **Affine systems with `F`-independent rows** have `N^{r-s}` solutions. -/
theorem card_affine_indep {r s : ℕ} (hsr : s ≤ r) (v : Fin s → Fin r → F)
    (hv : LinearIndependent F v) (c : Fin s → K) :
    (univ.filter fun y : Fin r → K =>
      ∀ k, ∑ l, algebraMap F K (v k l) * y l = c k).card = Fintype.card K ^ (r - s) := by
  classical
  obtain ⟨w, hw, hwv⟩ := exists_square_completion (r - s) (show s + (r - s) = r by omega) v hv
  set R : Matrix (Fin r) (Fin r) F := Matrix.of w
  have hΦ := mulVec_map_bijective (K := K) (R := R) hw
  set Φ := fun y : Fin r → K => R.map (algebraMap F K) *ᵥ y
  set T : Fin r → Finset K := fun j => if h : (j : ℕ) < s then {c ⟨j, h⟩} else univ
  have hΦk : ∀ (y : Fin r → K) (k : Fin s),
      Φ y (Fin.castLE hsr k) = ∑ l, algebraMap F K (v k l) * y l := by
    intro y k
    simp only [Φ, mulVec, dotProduct, map_apply, R, of_apply]
    rw [hwv k]
  have hbij : (univ.filter fun y : Fin r → K =>
      ∀ k, ∑ l, algebraMap F K (v k l) * y l = c k).card = (Fintype.piFinset T).card := by
    refine card_bij (fun y _ => Φ y) (fun y hy => ?_) (fun y _ y' _ h => hΦ.1 h)
      (fun z hz => ?_)
    · rw [Fintype.mem_piFinset]
      intro j
      simp only [T]
      split_ifs with hj
      · refine mem_singleton.2 ?_
        have := hΦk y ⟨j, hj⟩
        simp only [Fin.castLE_mk] at this
        rw [this]; exact (mem_filter.1 hy).2 _
      · exact mem_univ _
    · obtain ⟨y, rfl⟩ := hΦ.2 z
      refine ⟨y, mem_filter.2 ⟨mem_univ _, fun k => ?_⟩, rfl⟩
      have := Fintype.mem_piFinset.1 hz (Fin.castLE hsr k)
      simp only [T, Fin.coe_castLE, k.2, dif_pos, mem_singleton] at this
      rw [← hΦk y k, this]
  rw [hbij, Fintype.card_piFinset]
  rw [← prod_filter_mul_prod_filter_not univ (fun j : Fin r => (j : ℕ) < s)]
  have h1 : ∀ j ∈ univ.filter (fun j : Fin r => (j : ℕ) < s), (T j).card = 1 := fun j hj => by
    simp [T, (mem_filter.1 hj).2]
  have h2 : ∀ j ∈ univ.filter (fun j : Fin r => ¬ (j : ℕ) < s), (T j).card = Fintype.card K :=
    fun j hj => by simp [T, (mem_filter.1 hj).2]
  rw [prod_congr rfl h1, prod_congr rfl h2, prod_const_one, one_mul, prod_const]
  congr 1
  rw [filter_not, card_sdiff_of_subset (filter_subset _ _), card_univ, Fintype.card_fin]
  have : (univ.filter fun j : Fin r => (j : ℕ) < s).card = s := by
    rw [show (univ.filter fun j : Fin r => (j : ℕ) < s) = univ.map (Fin.castLEEmb hsr) by
      ext j; simp only [mem_filter, mem_univ, true_and, mem_map, Fin.castLEEmb_apply]
      constructor
      · intro h; exact ⟨⟨j, h⟩, rfl⟩
      · rintro ⟨k, rfl⟩; simp]
    simp
  rw [this]


/-- **One extra affine condition.** On the solution set of an `F`-independent system, a further
condition `d · y = w` holds on at most `N^{r-s-1}` points, unless `d ∈ span(v)` and `w` equals
the forced value `∑ λ_k c_k`. -/
theorem card_affine_extra_le {r s : ℕ} (hsr : s + 1 ≤ r) (v : Fin s → Fin r → F)
    (hv : LinearIndependent F v) (c : Fin s → K) (d : Fin r → F) (w : K)
    (hd : ∀ lam : Fin s → F, d = ∑ k, lam k • v k → ∑ k, algebraMap F K (lam k) * c k ≠ w) :
    (univ.filter fun y : Fin r → K =>
      (∀ k, ∑ l, algebraMap F K (v k l) * y l = c k) ∧
        ∑ l, algebraMap F K (d l) * y l = w).card ≤ Fintype.card K ^ (r - s - 1) := by
  classical
  by_cases hspan : d ∈ Submodule.span F (Set.range v)
  · obtain ⟨lam, hlam⟩ := (Submodule.mem_span_range_iff_exists_fun F).1 hspan
    -- on the solution set `d · y` is forced
    have : (univ.filter fun y : Fin r → K =>
        (∀ k, ∑ l, algebraMap F K (v k l) * y l = c k) ∧
          ∑ l, algebraMap F K (d l) * y l = w) = ∅ := by
      refine filter_false_of_mem fun y _ ⟨h1, h2⟩ => hd lam hlam.symm ?_
      rw [← h2, ← hlam]
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum, map_mul, sum_mul]
      rw [sum_comm]
      refine sum_congr rfl fun k _ => ?_
      rw [← h1 k, mul_sum]
      exact sum_congr rfl fun l _ => by ring
    rw [this, card_empty]; exact Nat.zero_le _
  · have hv' : LinearIndependent F (Fin.snoc v d : Fin (s + 1) → Fin r → F) :=
      linearIndependent_finSnoc.2 ⟨hv, hspan⟩
    have h := card_affine_indep (K := K) hsr _ hv' (Fin.snoc c w)
    have heq : (univ.filter fun y : Fin r → K =>
        (∀ k, ∑ l, algebraMap F K (v k l) * y l = c k) ∧
          ∑ l, algebraMap F K (d l) * y l = w) =
        univ.filter fun y : Fin r → K => ∀ k : Fin (s + 1),
          ∑ l, algebraMap F K ((Fin.snoc v d : Fin (s + 1) → Fin r → F) k l) * y l =
            (Fin.snoc c w : Fin (s + 1) → K) k := by
      ext y
      simp only [mem_filter, mem_univ, true_and]
      constructor
      · rintro ⟨h1, h2⟩ k
        refine Fin.lastCases ?_ (fun k => ?_) k
        · simpa using h2
        · simpa using h1 k
      · intro h
        exact ⟨fun k => by simpa using h (Fin.castSucc k), by simpa using h (Fin.last s)⟩
    rw [heq, h]
    exact le_of_eq (by congr 1)

end DesignsII
