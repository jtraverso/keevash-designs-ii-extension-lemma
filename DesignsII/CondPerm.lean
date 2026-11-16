/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import DesignsII.TwoStage

/-!
# Conditioned uniform permutations

A uniform permutation `σ` of `[m]` conditioned on prescribed values `σ s = v s` at the positions
`s ∈ S` is a uniform permutation of the remaining `m - |S|` positions and values. We realise this
by the bijection `liftC S v : Perm (Fin (m - |S|)) → {σ : σ|_S = v}` built from the order
isomorphisms `Fin (m - |S|) ≃o Sᶜ` (positions) and `Fin (m - |S|) ≃o v(S)ᶜ` (values):

* `liftC_apply_mem`, `liftC_apply_not_mem`: the values of `liftC S v τ`;
* `liftC_mul_swap`: a transposition of values of `τ` is a transposition of values of `liftC τ`;
* `exists_liftC`: every `σ` with `σ|_S = v` is some `liftC τ` (and `liftC` is injective);
* `rank_lt`: positions `t ∉ S` with `t < k` become positions `< #{x ∉ S : x < k}`.

`cond_lipschitz_tail` transports Lemma `lip3` to the conditioned product space: conditioning on
the values at the fixed vertices (Lemma `e|E`, BLUEPRINT "obstruction at the fixed vertices").
-/

@[expose] public section

namespace DesignsII

open Finset Equiv

section Single

variable {m : ℕ} (S : Finset (Fin m)) (v : S ↪ Fin m)

/-- The prescribed values `v(S)`. -/
def vImg : Finset (Fin m) := univ.map v

theorem card_vImg : (vImg S v).card = S.card := by simp [vImg]

theorem card_compl_S : (Sᶜ).card = m - S.card := by rw [card_compl, Fintype.card_fin]

theorem card_compl_vImg : ((vImg S v)ᶜ).card = m - S.card := by
  rw [card_compl, Fintype.card_fin, card_vImg]

/-- Positions outside `S`, in increasing order. -/
noncomputable def ePos : Fin (m - S.card) ≃o (Sᶜ : Finset (Fin m)) :=
  (Sᶜ).orderIsoOfFin (card_compl_S S)

/-- Values outside `v(S)`, in increasing order. -/
noncomputable def eVal : Fin (m - S.card) ≃o ((vImg S v)ᶜ : Finset (Fin m)) :=
  ((vImg S v)ᶜ).orderIsoOfFin (card_compl_vImg S v)

/-- `S ≃ v(S)`. -/
noncomputable def eIn : {x // x ∈ S} ≃ {x // x ∈ vImg S v} :=
  Equiv.ofBijective (fun s => ⟨v s, by simp [vImg]⟩)
    ⟨fun s s' h => v.injective (Subtype.ext_iff.1 h), fun y => by
      obtain ⟨s, -, hs⟩ := mem_map.1 y.2
      exact ⟨s, Subtype.ext hs⟩⟩

/-- `Sᶜ ≃ v(S)ᶜ` through `τ`. -/
noncomputable def eOut (τ : Perm (Fin (m - S.card))) : {x // x ∉ S} ≃ {x // x ∉ vImg S v} :=
  (Equiv.subtypeEquivRight fun x => (mem_compl (s := S) (a := x)).symm).trans
    ((ePos S).symm.toEquiv.trans (τ.trans ((eVal S v).toEquiv.trans
      (Equiv.subtypeEquivRight fun x => mem_compl (s := vImg S v) (a := x)))))

/-- The conditioned permutation. -/
noncomputable def liftC (τ : Perm (Fin (m - S.card))) : Perm (Fin m) :=
  Equiv.subtypeCongr (eIn S v) (eOut S v τ)

theorem subtypeCongr_apply' {α : Type*} {p q : α → Prop} [DecidablePred p] [DecidablePred q]
    (e : {x // p x} ≃ {x // q x}) (f : {x // ¬ p x} ≃ {x // ¬ q x}) (x : α) :
    Equiv.subtypeCongr e f x = if h : p x then (e ⟨x, h⟩ : α) else f ⟨x, h⟩ := by
  by_cases h : p x
  · simp [Equiv.subtypeCongr, h, sumCompl_symm_apply_of_pos h]
  · simp [Equiv.subtypeCongr, h, sumCompl_symm_apply_of_neg h]

theorem liftC_apply_mem (τ : Perm (Fin (m - S.card))) {s : Fin m} (hs : s ∈ S) :
    liftC S v τ s = v ⟨s, hs⟩ := by
  rw [liftC, subtypeCongr_apply', dif_pos hs]
  rfl

theorem liftC_apply_not_mem (τ : Perm (Fin (m - S.card))) {t : Fin m} (ht : t ∉ S) :
    liftC S v τ t = (eVal S v (τ ((ePos S).symm ⟨t, mem_compl.2 ht⟩)) : Fin m) := by
  rw [liftC, subtypeCongr_apply', dif_neg ht]
  rfl

theorem eVal_not_mem_vImg (i : Fin (m - S.card)) : (eVal S v i : Fin m) ∉ vImg S v :=
  mem_compl.1 (eVal S v i).2

theorem liftC_mul_swap (τ : Perm (Fin (m - S.card))) (x y : Fin (m - S.card)) :
    liftC S v (swap x y * τ) =
      swap (eVal S v x : Fin m) (eVal S v y) * liftC S v τ := by
  ext t
  have hg : Function.Injective fun i : Fin (m - S.card) => (eVal S v i : Fin m) :=
    Subtype.val_injective.comp (eVal S v).injective
  by_cases ht : t ∈ S
  · rw [Perm.mul_apply, liftC_apply_mem S v _ ht, liftC_apply_mem S v _ ht]
    have hv : v ⟨t, ht⟩ ∈ vImg S v := by simp [vImg]
    rw [swap_apply_of_ne_of_ne (fun h => eVal_not_mem_vImg S v x (by rw [← h]; exact hv))
      (fun h => eVal_not_mem_vImg S v y (by rw [← h]; exact hv))]
  · rw [Perm.mul_apply, liftC_apply_not_mem S v _ ht, liftC_apply_not_mem S v _ ht,
      Perm.mul_apply]
    exact congrArg Fin.val (hg.swap_apply x y _).symm

theorem liftC_injective : Function.Injective (liftC S v) := by
  intro τ τ' h
  ext i
  have ht : ((ePos S i : Fin m)) ∉ S := mem_compl.1 (ePos S i).2
  have := congrArg (fun σ : Perm (Fin m) => σ (ePos S i)) h
  simp only [liftC_apply_not_mem S v _ ht] at this
  have h2 : (ePos S).symm ⟨(ePos S i : Fin m), mem_compl.2 ht⟩ = i := by
    rw [OrderIso.symm_apply_eq]
  rw [h2] at this
  exact congrArg Fin.val ((eVal S v).injective (Subtype.ext this))

/-- Every permutation with the prescribed values on `S` is a conditioned lift. -/
theorem exists_liftC (σ : Perm (Fin m)) (hσ : ∀ s (hs : s ∈ S), σ s = v ⟨s, hs⟩) :
    ∃ τ, liftC S v τ = σ := by
  classical
  -- `σ` maps `Sᶜ` into `v(S)ᶜ`
  have hout : ∀ t, t ∉ S → σ t ∉ vImg S v := by
    intro t ht hv
    obtain ⟨s, -, hs⟩ := mem_map.1 hv
    have := hσ s s.2
    rw [Subtype.coe_eta] at this
    exact ht (σ.injective (this.trans hs) ▸ s.2)
  have hin : ∀ w, w ∉ vImg S v → σ.symm w ∉ S := by
    intro w hw hs
    apply hw
    have := hσ _ hs
    rw [Equiv.apply_symm_apply] at this
    rw [this]; simp [vImg]
  let τf : Fin (m - S.card) → Fin (m - S.card) := fun i =>
    (eVal S v).symm ⟨σ (ePos S i), mem_compl.2 (hout _ (mem_compl.1 (ePos S i).2))⟩
  let τg : Fin (m - S.card) → Fin (m - S.card) := fun i =>
    (ePos S).symm ⟨σ.symm (eVal S v i), mem_compl.2 (hin _ (mem_compl.1 (eVal S v i).2))⟩
  have h1 : Function.LeftInverse τg τf := by
    intro i
    simp [τf, τg]
  have h2 : Function.RightInverse τg τf := by
    intro i
    simp [τf, τg]
  refine ⟨⟨τf, τg, h1, h2⟩, ?_⟩
  ext t
  by_cases ht : t ∈ S
  · rw [liftC_apply_mem S v _ ht, hσ t ht]
  · rw [liftC_apply_not_mem S v _ ht]
    simp [τf]

/-- Ranks are monotone: positions `t ∉ S` below `k` get indices below `#{x ∉ S : x < k}`. -/
theorem rank_lt {t : Fin m} (ht : t ∉ S) {k : ℕ} (htk : (t : ℕ) < k) :
    (((ePos S).symm ⟨t, mem_compl.2 ht⟩ : Fin (m - S.card)) : ℕ) <
      ((Sᶜ).filter fun x : Fin m => (x : ℕ) < k).card := by
  classical
  set i := (ePos S).symm ⟨t, mem_compl.2 ht⟩
  have hit : (ePos S i : Fin m) = t := by simp [i]
  -- the indices `j < i` give elements of `Sᶜ` below `t`
  have hinj : Set.InjOn (fun j : Fin (m - S.card) => (ePos S j : Fin m))
      ((univ.filter fun j : Fin (m - S.card) => j < i) : Set (Fin (m - S.card))) :=
    fun j _ j' _ h => (ePos S).injective (Subtype.ext h)
  have hmaps : ∀ j ∈ (univ.filter fun j : Fin (m - S.card) => j < i),
      (ePos S j : Fin m) ∈ ((Sᶜ).filter fun x : Fin m => (x : ℕ) < k).erase t := by
    intro j hj
    have hji : j < i := (mem_filter.1 hj).2
    have hlt : (ePos S j : Fin m) < t := by
      rw [← hit]; exact (ePos S).strictMono hji
    refine mem_erase.2 ⟨ne_of_lt hlt, mem_filter.2 ⟨(ePos S j).2, ?_⟩⟩
    exact lt_trans (Fin.lt_def.1 hlt) htk
  have hcard := card_le_card_of_injOn _ hmaps hinj
  have hi : (univ.filter fun j : Fin (m - S.card) => j < i).card = (i : ℕ) := by
    rw [show (univ.filter fun j : Fin (m - S.card) => j < i) = Iio i by ext; simp]
    exact Fin.card_Iio i
  have hmem : t ∈ (Sᶜ).filter fun x : Fin m => (x : ℕ) < k := mem_filter.2 ⟨mem_compl.2 ht, htk⟩
  rw [hi, card_erase_of_mem hmem] at hcard
  have hpos : 0 < ((Sᶜ).filter fun x : Fin m => (x : ℕ) < k).card := card_pos.2 ⟨t, hmem⟩
  omega

end Single


section Product

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {a : ι → ℕ}
  (S : ∀ c, Finset (Fin (a c))) (v : ∀ c, S c ↪ Fin (a c))

/-- The conditioned lift of a tuple of permutations. -/
noncomputable def liftPi (τ : ∀ c, Perm (Fin (a c - (S c).card))) : ∀ c, Perm (Fin (a c)) :=
  fun c => liftC (S c) (v c) (τ c)

omit [Fintype ι] in
theorem liftPi_update_swap (τ : ∀ c, Perm (Fin (a c - (S c).card))) (c : ι)
    (x y : Fin (a c - (S c).card)) :
    liftPi S v (Function.update τ c (swap x y * τ c)) =
      Function.update (liftPi S v τ) c
        (swap (eVal (S c) (v c) x : Fin (a c)) (eVal (S c) (v c) y) * liftPi S v τ c) := by
  funext c'
  by_cases h : c' = c
  · subst h; simp [liftPi, liftC_mul_swap]
  · simp [liftPi, Function.update_of_ne h]

omit [Fintype ι] in
/-- The conditioned function is Lipschitz with the same constants. -/
theorem lipschitz_liftPi {f : (∀ c, Perm (Fin (a c))) → ℝ} {b : ι → ℝ} (hf : IsLipschitzG f b) :
    IsLipschitzG (a := fun c => a c - (S c).card) (fun τ => f (liftPi S v τ)) b := by
  intro τ c x y
  simp only
  rw [liftPi_update_swap]
  exact hf _ c _ _

omit [Fintype ι] [DecidableEq ι] in
/-- The conditioned function depends on the first `#{x ∉ S c : x < k c}` positions. -/
theorem depends_liftPi {f : (∀ c, Perm (Fin (a c))) → ℝ} {k : ι → ℕ} (hf : DependsFirstG f k) :
    DependsFirstG (a := fun c => a c - (S c).card) (fun τ => f (liftPi S v τ))
      (fun c => ((S c)ᶜ.filter fun x : Fin (a c) => (x : ℕ) < k c).card) := by
  intro τ τ' h
  refine hf _ _ fun c t ht => ?_
  by_cases hs : t ∈ S c
  · simp only [liftPi]; rw [liftC_apply_mem _ _ _ hs, liftC_apply_mem _ _ _ hs]
  · simp only [liftPi]
    rw [liftC_apply_not_mem _ _ _ hs, liftC_apply_not_mem _ _ _ hs,
      h c _ (rank_lt (S c) hs ht)]

/-- **Lemma `lip3` on the conditioned product space.** -/
theorem cond_lipschitz_tail (f : (∀ c, Perm (Fin (a c))) → ℝ) (b : ι → ℝ) (hb : ∀ c, 0 ≤ b c)
    (hf : IsLipschitzG f b) (k : ι → ℕ) (hd : DependsFirstG f k) {B t : ℝ}
    (hB : B = ∑ c, (((S c)ᶜ.filter fun x : Fin (a c) => (x : ℕ) < k c).card : ℝ) * b c ^ 2)
    (hB0 : 0 < B) (ht : 0 < t) :
    probG (a := fun c => a c - (S c).card)
      (fun τ => t < |f (liftPi S v τ) - meanG (a := fun c => a c - (S c).card)
        (fun τ => f (liftPi S v τ))|) ≤ 2 * Real.exp (-(t ^ 2 / (2 * B))) :=
  lipschitz_tail_general _ _ b hb (lipschitz_liftPi S v hf) (depends_liftPi S v hd) hB hB0 ht

end Product


section Total

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {a : ι → ℕ} (S : ∀ c, Finset (Fin (a c)))

/-- The restriction of `σ` to the positions `S` (as embeddings). -/
def restrS (σ : ∀ c, Perm (Fin (a c))) : ∀ c, S c ↪ Fin (a c) :=
  fun c => ⟨fun s => σ c s, fun _ _ h => Subtype.ext ((σ c).injective h)⟩

omit [Fintype ι] [DecidableEq ι] in
theorem restrS_liftPi (v : ∀ c, S c ↪ Fin (a c)) (τ : ∀ c, Perm (Fin (a c - (S c).card))) :
    restrS S (liftPi S v τ) = v := by
  funext c
  ext s
  simp [restrS, liftPi, liftC_apply_mem _ _ _ s.2]

omit [Fintype ι] [DecidableEq ι] in
theorem liftPi_injective (v : ∀ c, S c ↪ Fin (a c)) : Function.Injective (liftPi S v) := by
  intro τ τ' h
  funext c
  exact liftC_injective (S c) (v c) (congrFun h c)

open Classical in
/-- **Law of total probability over the conditioning values.** If the conditioned probability of
`E` is at most `ε` for every assignment of values at the positions `S`, then `P(E) ≤ ε`. -/
theorem probG_le_of_cond (E : (∀ c, Perm (Fin (a c))) → Prop) {ε : ℝ}
    (h : ∀ v : ∀ c, S c ↪ Fin (a c),
      probG (a := fun c => a c - (S c).card) (fun τ => E (liftPi S v τ)) ≤ ε) :
    probG (a := a) E ≤ ε := by
  have hP := prod_pos (s := univ) fun c (_ : c ∈ univ) =>
    (by exact_mod_cast Nat.factorial_pos (a c - (S c).card) : (0 : ℝ) < (a c - (S c).card).factorial)
  have hcnt : ((univ.filter E).card : ℝ) ≤
      ∑ v : (∀ c, S c ↪ Fin (a c)), ε * ∏ c, ((a c - (S c).card).factorial : ℝ) := by
    rw [card_eq_sum_card_fiberwise (f := restrS S) (t := univ) (fun _ _ => mem_univ _)]
    push_cast
    refine sum_le_sum fun v _ => ?_
    have hv := h v
    unfold probG at hv
    rw [div_le_iff₀ hP] at hv
    refine le_trans ?_ hv
    -- the fibre over `v` is the image of the conditioned event under `liftPi`
    have : ((univ.filter E).filter fun σ => restrS S σ = v) ⊆
        (univ.filter fun τ : (∀ c, Perm (Fin (a c - (S c).card))) => E (liftPi S v τ)).map
          ⟨liftPi S v, liftPi_injective S v⟩ := by
      intro σ hσ
      obtain ⟨h1, h2⟩ := mem_filter.1 hσ
      have hσc : ∀ c, ∃ τc, liftC (S c) (v c) τc = σ c := fun c =>
        exists_liftC (S c) (v c) (σ c) fun s hs => by
          have := congrFun h2 c
          exact congrArg (fun e : S c ↪ Fin (a c) => e ⟨s, hs⟩) this
      choose τ hτ using hσc
      have hlift : liftPi S v τ = σ := funext hτ
      refine mem_map.2 ⟨τ, mem_filter.2 ⟨mem_univ _, ?_⟩, hlift⟩
      rw [hlift]; exact (mem_filter.1 h1).2
    have := card_le_card this
    rw [card_map] at this
    exact_mod_cast this
  unfold probG
  rw [div_le_iff₀ (prod_pos fun c _ => by exact_mod_cast Nat.factorial_pos _)]
  refine hcnt.trans (le_of_eq ?_)
  rw [sum_const, card_univ, nsmul_eq_mul, Fintype.card_pi]
  have hfac : ∀ c, ((Fintype.card (S c ↪ Fin (a c)) : ℝ)) * ((a c - (S c).card).factorial : ℝ) =
      ((a c).factorial : ℝ) := by
    intro c
    rw [Fintype.card_embedding_eq, Fintype.card_fin, Fintype.card_coe]
    have hle : (S c).card ≤ a c := by simpa using card_le_univ (S c)
    exact_mod_cast (by rw [mul_comm]; exact Nat.factorial_mul_descFactorial hle)
  push_cast
  rw [← mul_assoc, mul_comm _ ε, mul_assoc, ← prod_mul_distrib]
  simp_rw [hfac]

end Total


section Count

variable {m : ℕ} (S : Finset (Fin m)) (v : S ↪ Fin m)

open Classical in
/-- **Conditioned counts**: events on the conditioned lift are events on the permutations with the
prescribed values. -/
theorem card_liftC (E : Perm (Fin m) → Prop) :
    (univ.filter fun τ : Perm (Fin (m - S.card)) => E (liftC S v τ)).card =
      (univ.filter fun σ : Perm (Fin m) => (∀ s (hs : s ∈ S), σ s = v ⟨s, hs⟩) ∧ E σ).card := by
  refine card_bij (fun τ _ => liftC S v τ) (fun τ hτ => ?_)
    (fun τ _ τ' _ h => liftC_injective S v h) (fun σ hσ => ?_)
  · exact mem_filter.2 ⟨mem_univ _, fun s hs => liftC_apply_mem S v τ hs, (mem_filter.1 hτ).2⟩
  · obtain ⟨h1, h2⟩ := (mem_filter.1 hσ).2
    obtain ⟨τ, rfl⟩ := exists_liftC S v σ h1
    exact ⟨τ, mem_filter.2 ⟨mem_univ _, h2⟩, rfl⟩

open Classical in
/-- With no conditioning (`S = ∅`) the ratios are unchanged. -/
theorem ratio_liftC_empty (v : (∅ : Finset (Fin m)) ↪ Fin m) (E : Perm (Fin m) → Prop) :
    ((univ.filter fun τ : Perm (Fin (m - (∅ : Finset (Fin m)).card)) =>
        E (liftC ∅ v τ)).card : ℝ) / ((m - (∅ : Finset (Fin m)).card).factorial : ℝ) =
      ((univ.filter E).card : ℝ) / (m.factorial : ℝ) := by
  rw [card_liftC]
  simp

end Count

end DesignsII
