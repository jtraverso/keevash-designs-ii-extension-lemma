/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import DesignsII.AffineCount
public import DesignsII.CondPerm

/-!
# Compatibility with `f_j` given the values at the fixed vertices (Lemma `e|E`)

* `generic_rows_indep`: for generic `M`, any `s ≤ r` rows are linearly independent over `F`;
* `card_perm_fix'`: `card_perm_fix` for an arbitrary finite domain;
* `card_cond_compat`: in the conditioned space (values `v` prescribed at the positions `S`), the
  number of `τ` making the copy at positions `w` compatible with `M` is `#Y' · (N - |S| - |I₁|)!`,
  where `I₀ = {i : w i ∈ S}`, `I₁ = I₀ᶜ` and `Y'` is the set of `y` with `(My)_i = κ(v(w i))` on
  `I₀`, `My` injective and `(My)_i ∉ κ(v(S))` on `I₁`.
-/

@[expose] public section

namespace DesignsII

open Finset Matrix Equiv

variable {F K : Type*} [Field F] [Field K] [Algebra F K] [Fintype K] [DecidableEq K] {q r : ℕ}

omit [Fintype K] [DecidableEq K] in
/-- **Any `s ≤ r` rows of a generic matrix are independent.** -/
theorem generic_rows_indep {M : Matrix (Fin q) (Fin r) F} (hM : IsGeneric M) (hrq : r ≤ q)
    {s : ℕ} (e : Fin s ↪ Fin q) (hs : s ≤ r) : LinearIndependent F fun k => M (e k) := by
  classical
  obtain ⟨B, hIB, hB⟩ := exists_superset_card_eq (s := univ.map e) (n := r)
    (by simpa using hs) (by simpa using hrq)
  set b := B.orderEmbOfFin hB
  have hdet : (M.submatrix b id).det ≠ 0 := hM ⟨b, b.injective⟩
  have hind : LinearIndependent F fun k : Fin r => (M.submatrix b id) k :=
    Matrix.linearIndependent_rows_of_det_ne_zero hdet
  -- each `e k` is some `b (j k)`
  have hj : ∀ k, ∃ j, b j = e k := fun k => by
    obtain ⟨j, hj⟩ := (B.orderIsoOfFin hB).surjective ⟨e k, hIB (mem_map_of_mem _ (mem_univ k))⟩
    exact ⟨j, by rw [← coe_orderIsoOfFin_apply, hj]⟩
  choose j hjk using hj
  have hjinj : Function.Injective j := fun k k' h => e.injective (by rw [← hjk, ← hjk, h])
  have := hind.comp j hjinj
  convert this using 1
  funext k
  funext l
  simp only [Function.comp, submatrix_apply, id]
  rw [hjk k]

/-- `card_perm_fix` for an arbitrary finite domain. -/
theorem card_perm_fix' {α : Type*} [Fintype α] [DecidableEq α] {m : ℕ} (w u : α ↪ Fin m) :
    (univ.filter fun σ : Perm (Fin m) => ∀ x, σ (w x) = u x).card =
      (m - Fintype.card α).factorial := by
  classical
  set e := Fintype.equivFin α
  rw [← card_perm_fix ((e.symm.toEmbedding).trans w) ((e.symm.toEmbedding).trans u)]
  congr 1
  ext σ
  simp only [mem_filter, mem_univ, true_and, Function.Embedding.trans_apply,
    Equiv.coe_toEmbedding]
  constructor
  · intro h x; exact h _
  · intro h x; simpa using h (e x)


section Cond

variable {N : ℕ} (S : Finset (Fin N)) (v : S ↪ Fin N) (κ : Fin N ≃ K)
  (M : Matrix (Fin q) (Fin r) F) (w : Fin q ↪ Fin N)

/-- The revealed value `κ(v(w i))` at a fixed position. -/
noncomputable def cval (i : Fin q) : K := if h : w i ∈ S then κ (v ⟨w i, h⟩) else 0

/-- The forbidden values `κ(v(S))` for the new positions. -/
def forb : Finset K := (vImg S v).image κ

/-- The admissible parameters `y`. -/
noncomputable def Yc : Finset (Fin r → K) := by
  classical
  exact univ.filter fun y : Fin r → K => (∀ i, w i ∈ S → mvec M y i = cval S v κ w i) ∧
    Function.Injective (mvec M y) ∧ ∀ i, w i ∉ S → mvec M y i ∉ forb S v κ

/-- The new positions, as positions of the conditioned permutation. -/
noncomputable def newPos : {i // w i ∉ S} ↪ Fin (N - S.card) :=
  ⟨fun i => (ePos S).symm ⟨w i, mem_compl.2 i.2⟩, fun _ _ h => Subtype.ext (w.injective
    (Subtype.ext_iff.1 ((ePos S).symm.injective h)))⟩

theorem not_mem_vImg_of_Yc {y : Fin r → K} (hy : y ∈ Yc S v κ M w) (i : {i // w i ∉ S}) :
    κ.symm (mvec M y i) ∉ vImg S v := by
  classical
  intro h
  have := ((mem_filter.1 hy).2.2.2 i i.2)
  exact this (mem_image.2 ⟨_, h, by simp⟩)

/-- The prescribed values of `τ` at the new positions. -/
noncomputable def newVal (y : Yc S v κ M w) : {i // w i ∉ S} ↪ Fin (N - S.card) := by
  classical
  exact ⟨fun i => (eVal S v).symm ⟨κ.symm (mvec M y.1 i), mem_compl.2 (not_mem_vImg_of_Yc S v κ M w
    y.2 i)⟩, fun _ _ h => Subtype.ext ((mem_filter.1 y.2).2.2.1 (κ.symm.injective
      (Subtype.ext_iff.1 ((eVal S v).symm.injective h))))⟩

/-- **Compatibility count in the conditioned space** (Lemma `e|E`, algebraic part). -/
theorem card_cond_compat {M : Matrix (Fin q) (Fin r) F} (hM : IsGeneric M) (hrq : r ≤ q) :
    (univ.filter fun τ : Perm (Fin (N - S.card)) =>
      ∃ y, ∀ i, κ (liftC S v τ (w i)) = mvec M y i).card =
      (Yc S v κ M w).card * (N - S.card - Fintype.card {i // w i ∉ S}).factorial := by
  classical
  obtain ⟨B, -, hB⟩ := exists_subset_card_eq (s := (univ : Finset (Fin q))) (n := r)
    (by simpa using hrq)
  have hset : (univ.filter fun τ : Perm (Fin (N - S.card)) =>
      ∃ y, ∀ i, κ (liftC S v τ (w i)) = mvec M y i) =
      (Yc S v κ M w).attach.biUnion fun y => univ.filter fun τ : Perm (Fin (N - S.card)) =>
        ∀ i, τ (newPos S w i) = newVal S v κ M w y i := by
    ext τ
    simp only [mem_filter, mem_univ, true_and, mem_biUnion, mem_attach]
    constructor
    · rintro ⟨y, hy⟩
      have hYc : y ∈ Yc S v κ M w := by
        refine mem_filter.2 ⟨mem_univ _, fun i hi => ?_, fun i i' h => ?_, fun i hi => ?_⟩
        · rw [← hy i, liftC_apply_mem S v τ hi]; simp [cval, hi]
        · rw [← hy i, ← hy i'] at h
          exact w.injective ((liftC S v τ).injective (κ.injective h))
        · rw [← hy i, liftC_apply_not_mem S v τ hi]
          intro hf
          obtain ⟨x, hx, hxe⟩ := mem_image.1 hf
          exact eVal_not_mem_vImg S v _ (κ.injective hxe ▸ hx)
      refine ⟨⟨y, hYc⟩, fun i => ?_⟩
      have h1 := hy i
      rw [liftC_apply_not_mem S v τ i.2] at h1
      show τ ((ePos S).symm ⟨w i, mem_compl.2 i.2⟩) = (eVal S v).symm ⟨κ.symm (mvec M y i), _⟩
      symm
      rw [OrderIso.symm_apply_eq]
      exact Subtype.ext (by show κ.symm (mvec M y i) = _; rw [← h1, κ.symm_apply_apply])
    · rintro ⟨y, hy⟩
      refine ⟨y.1, fun i => ?_⟩
      by_cases hi : w i ∈ S
      · rw [liftC_apply_mem S v τ hi, (mem_filter.1 y.2).2.1 i hi]; simp [cval, hi]
      · rw [liftC_apply_not_mem S v τ hi]
        have := hy ⟨i, hi⟩
        change τ ((ePos S).symm ⟨w i, mem_compl.2 hi⟩) = (eVal S v).symm ⟨_, _⟩ at this
        rw [this]; simp
  rw [hset, card_biUnion]
  · rw [sum_congr rfl fun y _ => card_perm_fix' (newPos S w) (newVal S v κ M w y), sum_const,
      card_attach, smul_eq_mul]
  · intro y _ y' _ hyy
    rw [Function.onFun, disjoint_left]
    intro τ h1 h2
    simp only [mem_filter, mem_univ, true_and] at h1 h2
    apply hyy
    apply Subtype.ext
    -- `M y` and `M y'` agree everywhere
    have hagree : ∀ i, mvec M y.1 i = mvec M y'.1 i := by
      intro i
      by_cases hi : w i ∈ S
      · rw [(mem_filter.1 y.2).2.1 i hi, (mem_filter.1 y'.2).2.1 i hi]
      · have e1 := h1 ⟨i, hi⟩
        have e2 := h2 ⟨i, hi⟩
        rw [e1] at e2
        have := Subtype.ext_iff.1 ((eVal S v).symm.injective e2)
        exact κ.symm.injective this
    exact generic_rows_inj hM hB fun i _ => hagree i

end Cond


section Bounds

variable {N : ℕ} (S : Finset (Fin N)) (v : S ↪ Fin N) (κ : Fin N ≃ K)
  (M : Matrix (Fin q) (Fin r) F) (w : Fin q ↪ Fin N)

/-- The fixed positions of the copy. -/
def I₀ : Finset (Fin q) := by
  classical
  exact univ.filter fun i => w i ∈ S

omit [Fintype K] [DecidableEq K] in
theorem mvec_eq_sum (y : Fin r → K) (i : Fin q) :
    mvec M y i = ∑ l, algebraMap F K (M i l) * y l := by
  simp [mvec, mulVec, dotProduct]

theorem card_Yc_le {M : Matrix (Fin q) (Fin r) F} (hM : IsGeneric M) (hrq : r ≤ q)
    (hI : (I₀ S w).card ≤ r) :
    (Yc S v κ M w).card ≤ Fintype.card K ^ (r - (I₀ S w).card) := by
  classical
  rw [← card_slice hM hrq (I₀ S w) hI (cval S v κ w)]
  refine card_le_card fun y hy => mem_filter.2 ⟨mem_univ _, fun i hi => ?_⟩
  exact (mem_filter.1 hy).2.1 i (by simpa [I₀] using hi)

/-- **Lower bound for the admissible parameters** (non-degenerate revealed values). -/
theorem card_Yc_ge {M : Matrix (Fin q) (Fin r) F} (hM : IsGeneric M) (hrq : r ≤ q)
    (hrows : DistinctRows M) (hI : (I₀ S w).card + 1 ≤ r)
    (hc : LinearIndependent F fun k : Fin (I₀ S w).card =>
      cval S v κ w ((I₀ S w).orderEmbOfFin rfl k)) :
    Fintype.card K ^ (r - (I₀ S w).card) ≤
      (Yc S v κ M w).card + (q ^ 2 + q * S.card) * Fintype.card K ^ (r - (I₀ S w).card - 1) := by
  classical
  set s := (I₀ S w).card
  set e := (I₀ S w).orderEmbOfFin (rfl : (I₀ S w).card = s)
  have he : ∀ k, e k ∈ I₀ S w := fun k => (I₀ S w).orderEmbOfFin_mem rfl k
  have hrowsI : LinearIndependent F fun k => M (e k) :=
    generic_rows_indep hM hrq e.toEmbedding (by omega)
  -- the slice in the form of `card_affine_extra_le`
  set slice := univ.filter fun y : Fin r → K => ∀ i ∈ I₀ S w, mvec M y i = cval S v κ w i
  have hslice : ∀ y ∈ slice, ∀ k, ∑ l, algebraMap F K (M (e k) l) * y l = cval S v κ w (e k) :=
    fun y hy k => by rw [← mvec_eq_sum]; exact (mem_filter.1 hy).2 _ (he k)
  have hcard : slice.card = Fintype.card K ^ (r - s) := card_slice hM hrq _ (by omega) _
  -- bad parameters
  set Coll := (univ.filter fun p : Fin q × Fin q => p.1 ≠ p.2).biUnion fun p =>
    univ.filter fun y : Fin r → K =>
      (∀ k, ∑ l, algebraMap F K (M (e k) l) * y l = cval S v κ w (e k)) ∧
        ∑ l, algebraMap F K ((M p.1 - M p.2) l) * y l = 0
  set Forb := ((univ.filter fun i => w i ∉ S) ×ˢ forb S v κ).biUnion fun p =>
    univ.filter fun y : Fin r → K =>
      (∀ k, ∑ l, algebraMap F K (M (e k) l) * y l = cval S v κ w (e k)) ∧
        ∑ l, algebraMap F K (M p.1 l) * y l = p.2
  have hsub : slice ⊆ Yc S v κ M w ∪ (Coll ∪ Forb) := by
    intro y hy
    by_cases hY : y ∈ Yc S v κ M w
    · exact mem_union_left _ hY
    refine mem_union_right _ ?_
    have hy0 : ∀ i, w i ∈ S → mvec M y i = cval S v κ w i :=
      fun i hi => (mem_filter.1 hy).2 i (by simpa [I₀] using hi)
    simp only [Yc, mem_filter, mem_univ, true_and, not_and, not_forall] at hY
    by_cases hinj : Function.Injective (mvec M y)
    · obtain ⟨i, hi, hf⟩ := by simpa using hY hy0 hinj
      refine mem_union_right _ (mem_biUnion.2 ⟨(i, mvec M y i), mem_product.2
        ⟨by simpa using hi, hf⟩, mem_filter.2 ⟨mem_univ _, hslice y hy, ?_⟩⟩)
      rw [mvec_eq_sum]
    · simp only [Function.Injective, not_forall] at hinj
      obtain ⟨i, i', hii, hne⟩ := hinj
      refine mem_union_left _ (mem_biUnion.2 ⟨(i, i'), by simpa using hne,
        mem_filter.2 ⟨mem_univ _, hslice y hy, ?_⟩⟩)
      simp only [Pi.sub_apply, map_sub, sub_mul, sum_sub_distrib, ← mvec_eq_sum, hii, sub_self]
  -- each bad set is small
  have hextra : ∀ (d : Fin r → F) (x : K),
      (∀ lam : Fin s → F, d = ∑ k, lam k • M (e k) →
        ∑ k, algebraMap F K (lam k) * cval S v κ w (e k) ≠ x) →
      (univ.filter fun y : Fin r → K =>
        (∀ k, ∑ l, algebraMap F K (M (e k) l) * y l = cval S v κ w (e k)) ∧
          ∑ l, algebraMap F K (d l) * y l = x).card ≤ Fintype.card K ^ (r - s - 1) :=
    fun d x hd => card_affine_extra_le (by omega) (fun k => M (e k)) hrowsI _ d x hd
  have hColl : Coll.card ≤ q ^ 2 * Fintype.card K ^ (r - s - 1) := by
    refine card_biUnion_le.trans ?_
    calc _ ≤ ∑ _p ∈ univ.filter (fun p : Fin q × Fin q => p.1 ≠ p.2),
          Fintype.card K ^ (r - s - 1) := by
          refine sum_le_sum fun p hp => hextra _ _ fun lam hlam hsum => ?_
          have hp' : p.1 ≠ p.2 := (mem_filter.1 hp).2
          -- `λ = 0` by independence of the revealed values, contradicting distinct rows
          have hlam0 : ∀ k, lam k = 0 := by
            have : ∑ k, lam k • cval S v κ w (e k) = 0 := by
              rw [← hsum]; simp [Algebra.smul_def]
            exact (Fintype.linearIndependent_iff.1 hc) lam (by simpa using this)
          apply hp'
          apply hrows
          have : M p.1 - M p.2 = 0 := by rw [hlam]; simp [hlam0]
          exact sub_eq_zero.1 this
      _ ≤ q ^ 2 * Fintype.card K ^ (r - s - 1) := by
          rw [sum_const, smul_eq_mul]
          gcongr
          exact (card_le_card (filter_subset _ _)).trans (by simp [sq])
  have hForb : Forb.card ≤ q * S.card * Fintype.card K ^ (r - s - 1) := by
    refine card_biUnion_le.trans ?_
    calc _ ≤ ∑ _p ∈ (univ.filter fun i => w i ∉ S) ×ˢ forb S v κ,
          Fintype.card K ^ (r - s - 1) := by
          refine sum_le_sum fun p hp => hextra _ _ fun lam hlam _ => ?_
          obtain ⟨hp1, -⟩ := mem_product.1 hp
          have hpi : w p.1 ∉ S := (mem_filter.1 hp1).2
          -- `M_i ∈ span(M_{I₀})` contradicts the independence of `s + 1 ≤ r` rows
          have hnot : p.1 ∉ Set.range e := by
            rintro ⟨k, hk⟩; exact hpi (by have := he k; rw [hk] at this; simpa [I₀] using this)
          set e' : Fin (s + 1) → Fin q := Fin.snoc (fun k => e k) p.1
          have he' : Function.Injective e' := by
            intro a b hab
            induction a using Fin.lastCases with
            | last =>
              induction b using Fin.lastCases with
              | last => rfl
              | cast b =>
                simp only [e', Fin.snoc_last, Fin.snoc_castSucc] at hab
                exact absurd ⟨b, hab.symm⟩ hnot
            | cast a =>
              induction b using Fin.lastCases with
              | last =>
                simp only [e', Fin.snoc_last, Fin.snoc_castSucc] at hab
                exact absurd ⟨a, hab⟩ hnot
              | cast b =>
                simp only [e', Fin.snoc_castSucc] at hab
                rw [e.injective hab]
          have hind := generic_rows_indep hM hrq ⟨e', he'⟩ (by omega)
          have hsnoc : (fun k => M ((⟨e', he'⟩ : Fin (s + 1) ↪ Fin q) k)) =
              (Fin.snoc (fun k => M (e k)) (M p.1) : Fin (s + 1) → Fin r → F) := by
            funext k
            refine Fin.lastCases ?_ (fun k => ?_) k <;> simp [e']
          rw [hsnoc] at hind
          exact (linearIndependent_finSnoc.1 hind).2
            (hlam ▸ Submodule.sum_mem _ fun k _ =>
              Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩))
      _ ≤ q * S.card * Fintype.card K ^ (r - s - 1) := by
          rw [sum_const, smul_eq_mul, card_product]
          gcongr
          · exact (card_le_card (filter_subset _ _)).trans (by simp)
          · exact card_image_le.trans (by rw [card_vImg])
  have := card_le_card hsub
  rw [hcard] at this
  calc Fintype.card K ^ (r - s) ≤ (Yc S v κ M w ∪ (Coll ∪ Forb)).card := this
    _ ≤ (Yc S v κ M w).card + (Coll.card + Forb.card) :=
        (card_union_le _ _).trans (Nat.add_le_add_left (card_union_le _ _) _)
    _ ≤ _ := by
        have := Nat.add_le_add hColl hForb
        nlinarith

end Bounds

end DesignsII
