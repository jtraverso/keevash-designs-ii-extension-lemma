/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import DesignsII.Joint

/-!
# Concentration of counting variables in the template space

Let `X(ω) = #{b ∈ C : G_b(ω)}` count the members of a finite family whose events hold, where each
`G_b` only depends on the values `ω c p` at a finite set `D b` of positions `⟨c, p⟩`, all among the
first `a' c` positions of their coordinate. Then

* `meanG_count`: `𝔼 X = ∑_{b ∈ C} P(G_b)`;
* `count_tail`: `P(|X - 𝔼 X| > t) ≤ 2 exp(-t² / 2B)` with
  `B = ∑_{c relevant} a' c (2 maxDep c + 1)²`, `maxDep c = max_p #{b ∈ C : ⟨c, p⟩ ∈ D b}`

(Lemma `lip3`: a transposition in coordinate `c` changes the values at exactly two positions, so
it changes at most `2 maxDep c` events). This is
the concentration step of Lemmas `ext*`, `nibble` and `cover` (Designs II, §3).
-/

@[expose] public section

namespace DesignsII

open Finset Equiv

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {a : ι → ℕ} {β : Type*}

open Classical in
/-- The counting variable `X(ω) = #{b ∈ C : G_b(ω)}`. -/
noncomputable def countVar (C : Finset β) (G : β → (∀ c, Perm (Fin (a c))) → Prop)
    (ω : ∀ c, Perm (Fin (a c))) : ℝ :=
  ((C.filter fun b => G b ω).card : ℝ)

open Classical in
theorem meanG_count (C : Finset β) (G : β → (∀ c, Perm (Fin (a c))) → Prop) :
    meanG (countVar C G) = ∑ b ∈ C, probG (a := a) (G b) := by
  unfold meanG countVar probG
  rw [← sum_div]
  congr 1
  simp_rw [card_filter, Nat.cast_sum]
  rw [sum_comm]

/-- `ω` and `ω'` agree at the positions `D` (pairs `⟨c, p⟩` of a coordinate and a position). -/
def AgreeAt (D : Finset (Σ c, Fin (a c))) (ω ω' : ∀ c, Perm (Fin (a c))) : Prop :=
  ∀ cp ∈ D, ω cp.1 cp.2 = ω' cp.1 cp.2

/-- The relevant coordinates. -/
def relCoords (C : Finset β) (D : β → Finset (Σ c, Fin (a c))) : Finset ι :=
  (C.biUnion D).image Sigma.fst

open Classical in
/-- The maximal number of events depending on one position of coordinate `c`. -/
noncomputable def maxDep (C : Finset β) (D : β → Finset (Σ c, Fin (a c))) (c : ι) : ℕ :=
  univ.sup fun p : Fin (a c) => (C.filter fun b => (⟨c, p⟩ : Σ c, Fin (a c)) ∈ D b).card

/-- The Lipschitz constant `2 · maxDep + 1`. -/
noncomputable def lipConst (C : Finset β) (D : β → Finset (Σ c, Fin (a c))) (c : ι) : ℝ :=
  2 * (maxDep C D c : ℝ) + 1

omit [Fintype ι] in
open Classical in
theorem countVar_lipschitz (C : Finset β) (G : β → (∀ c, Perm (Fin (a c))) → Prop)
    (D : β → Finset (Σ c, Fin (a c)))
    (hG : ∀ b ∈ C, ∀ ω ω', AgreeAt (D b) ω ω' → (G b ω ↔ G b ω')) :
    IsLipschitzG (countVar C G) (lipConst C D) := by
  intro ω c x y
  set ω' := Function.update ω c (swap x y * ω c)
  set px := (ω c).symm x
  set py := (ω c).symm y
  set Bad := C.filter fun b => (⟨c, px⟩ : Σ c, Fin (a c)) ∈ D b ∨ (⟨c, py⟩ : Σ c, Fin (a c)) ∈ D b
  have hsame : ∀ b ∈ C, b ∉ Bad → (G b ω' ↔ G b ω) := by
    intro b hb hbad
    refine hG b hb ω' ω fun cp hcp => ?_
    rcases cp with ⟨c', p⟩
    by_cases hc : c' = c
    · subst hc
      simp only [ω', Function.update_self, Perm.mul_apply]
      refine swap_apply_of_ne_of_ne ?_ ?_
      · intro h; apply hbad; refine mem_filter.2 ⟨hb, Or.inl ?_⟩
        have : p = px := by simp [px, ← h]
        exact this ▸ hcp
      · intro h; apply hbad; refine mem_filter.2 ⟨hb, Or.inr ?_⟩
        have : p = py := by simp [py, ← h]
        exact this ▸ hcp
    · simp [ω', Function.update_of_ne hc]
  unfold countVar lipConst
  have hsplit : ∀ ω₀ : ∀ c, Perm (Fin (a c)), ((C.filter fun b => G b ω₀).card : ℝ) =
      ((Bad.filter fun b => G b ω₀).card : ℝ) +
        (((C \ Bad).filter fun b => G b ω₀).card : ℝ) := by
    intro ω₀
    rw [← Nat.cast_add, ← card_union_of_disjoint (disjoint_filter_filter disjoint_sdiff)]
    congr 2
    rw [← filter_union, union_sdiff_of_subset (filter_subset _ _)]
  have hrest : ((C \ Bad).filter fun b => G b ω') = (C \ Bad).filter fun b => G b ω := by
    refine filter_congr fun b hb => ?_
    exact hsame b (mem_sdiff.1 hb).1 (mem_sdiff.1 hb).2
  rw [hsplit ω', hsplit ω, hrest, add_sub_add_right_eq_sub]
  have hBad : (Bad.card : ℝ) ≤ 2 * maxDep C D c := by
    have h1 : Bad ⊆ (C.filter fun b => (⟨c, px⟩ : Σ c, Fin (a c)) ∈ D b) ∪
        C.filter fun b => (⟨c, py⟩ : Σ c, Fin (a c)) ∈ D b := by
      intro b hb; simp only [Bad, mem_filter, mem_union] at hb ⊢; tauto
    have h2 := (card_le_card h1).trans (card_union_le _ _)
    have hx : (C.filter fun b => (⟨c, px⟩ : Σ c, Fin (a c)) ∈ D b).card ≤ maxDep C D c :=
      le_sup (f := fun p : Fin (a c) => (C.filter fun b => (⟨c, p⟩ : Σ c, Fin (a c)) ∈ D b).card)
        (mem_univ px)
    have hy : (C.filter fun b => (⟨c, py⟩ : Σ c, Fin (a c)) ∈ D b).card ≤ maxDep C D c :=
      le_sup (f := fun p : Fin (a c) => (C.filter fun b => (⟨c, p⟩ : Σ c, Fin (a c)) ∈ D b).card)
        (mem_univ py)
    exact_mod_cast h2.trans (by omega)
  have h1 : ((Bad.filter fun b => G b ω').card : ℝ) ≤ Bad.card := by
    exact_mod_cast card_le_card (filter_subset _ _)
  have h2 : ((Bad.filter fun b => G b ω).card : ℝ) ≤ Bad.card := by
    exact_mod_cast card_le_card (filter_subset _ _)
  rw [abs_le]
  constructor <;> linarith [(Nat.cast_nonneg _ : (0 : ℝ) ≤ (Bad.filter fun b => G b ω).card),
    (Nat.cast_nonneg _ : (0 : ℝ) ≤ (Bad.filter fun b => G b ω').card)]

omit [Fintype ι] in
open Classical in
theorem countVar_depends (C : Finset β) (G : β → (∀ c, Perm (Fin (a c))) → Prop)
    (D : β → Finset (Σ c, Fin (a c))) (a' : ι → ℕ)
    (hpos : ∀ b ∈ C, ∀ cp ∈ D b, (cp.2 : ℕ) < a' cp.1)
    (hG : ∀ b ∈ C, ∀ ω ω', AgreeAt (D b) ω ω' → (G b ω ↔ G b ω')) :
    DependsFirstG (countVar C G) (fun c => if c ∈ relCoords C D then a' c else 0) := by
  intro ω ω' h
  unfold countVar
  congr 2
  refine filter_congr fun b hb => hG b hb ω ω' fun cp hcp => h cp.1 cp.2 ?_
  have : cp.1 ∈ relCoords C D := mem_image.2 ⟨cp, mem_biUnion.2 ⟨b, hb, hcp⟩, rfl⟩
  simpa [this] using hpos b hb cp hcp

open Classical in
/-- **Concentration of counting variables** (Lemma `lip3` for `X = #{b ∈ C : G_b}`), with
`B = ∑_{c relevant} a' c (2 maxDep c + 1)²`. -/
theorem count_tail (C : Finset β) (G : β → (∀ c, Perm (Fin (a c))) → Prop)
    (D : β → Finset (Σ c, Fin (a c))) (a' : ι → ℕ)
    (hpos : ∀ b ∈ C, ∀ cp ∈ D b, (cp.2 : ℕ) < a' cp.1)
    (hG : ∀ b ∈ C, ∀ ω ω', AgreeAt (D b) ω ω' → (G b ω ↔ G b ω'))
    {B t : ℝ} (hB : B = ∑ c ∈ relCoords C D, (a' c : ℝ) * lipConst C D c ^ 2) (hB0 : 0 < B)
    (ht : 0 < t) :
    probG (a := a) (fun ω => t < |countVar C G ω - ∑ b ∈ C, probG (a := a) (G b)|) ≤
      2 * Real.exp (-(t ^ 2 / (2 * B))) := by
  rw [← meanG_count]
  refine lipschitz_tail_general _ (countVar C G) (lipConst C D)
    (fun c => by unfold lipConst; positivity) (countVar_lipschitz C G D hG)
    (countVar_depends C G D a' hpos hG) ?_ hB0 ht
  rw [hB, ← sum_filter_add_sum_filter_not univ (· ∈ relCoords C D)]
  rw [sum_eq_zero (s := univ.filter fun c => c ∉ relCoords C D) fun c hc => by
    simp [(mem_filter.1 hc).2]]
  rw [add_zero, filter_mem_eq_inter, univ_inter]
  refine sum_congr rfl fun c hc => ?_
  simp [hc]


namespace TParams

variable {P : TParams} {F K : Type*} [Field F] [Field K] [Algebra F K]

/-- The positions read by the template tests of `φ` with colour `j`. -/
def copyDeps (j : Fin P.z) (φ : Fin P.q → Fin P.n) : Finset (Σ c : P.Coord, Fin (P.size c)) :=
  ((univ.image fun i : Fin P.q => (⟨.inl j, Fin.castLE P.hnN (φ i)⟩ : Σ c : P.Coord,
      Fin (P.size c))) ∪
    (edges φ).image fun e => (⟨.inr (.inl e), ⟨0, P.hz⟩⟩ : Σ c : P.Coord, Fin (P.size c))) ∪
  (((edges φ ×ˢ (univ : Finset (Fin P.r))).image fun ex =>
      (⟨.inr (.inr (.inl ex.1)), Fin.castLE P.hrq ex.2⟩ : Σ c : P.Coord, Fin (P.size c))) ∪
    {(⟨.inr (.inr (.inr (.inl φ))), ⟨0, P.hNA⟩⟩ : Σ c : P.Coord, Fin (P.size c)),
      ⟨.inr (.inr (.inr (.inr φ))), ⟨0, P.hNact⟩⟩})

theorem copyOK_of_agree (M : Matrix (Fin P.q) (Fin P.r) F) (κ : Fin P.N ≃ K) (j : Fin P.z)
    (a₀ : Fin P.NA) (k : ℕ) (φ : Fin P.q → Fin P.n) {ω ω' : P.Ω}
    (h : AgreeAt (copyDeps j φ) ω ω') (hc : CopyOK M κ j a₀ k φ ω) :
    CopyOK M κ j a₀ k φ ω' := by
  classical
  have hmem : ∀ cp, cp ∈ copyDeps j φ → ω cp.1 cp.2 = ω' cp.1 cp.2 := h
  obtain ⟨hA, hact, hT, hpi, y, hy⟩ := hc
  refine ⟨?_, ?_, fun e he => ?_, fun e he i hi => ?_, y, fun i => ?_⟩
  · rw [← hA]
    exact (hmem ⟨.inr (.inr (.inr (.inl φ))), ⟨0, P.hNA⟩⟩
      (mem_union_right _ (mem_union_right _ (mem_insert_self _ _)))).symm
  · unfold Active at hact ⊢
    rw [← hmem ⟨.inr (.inr (.inr (.inr φ))), ⟨0, P.hNact⟩⟩
      (mem_union_right _ (mem_union_right _ (mem_insert_of_mem (mem_singleton_self _))))]
    exact hact
  · rw [← hT e he]
    exact (hmem ⟨.inr (.inl e), ⟨0, P.hz⟩⟩
      (mem_union_left _ (mem_union_right _ (mem_image_of_mem _ he)))).symm
  · have hc : e.card = P.r := (mem_powersetCard.1 he).2
    have := hpi e he i hi
    unfold pival at this ⊢
    rw [dif_pos ⟨hc, hi⟩] at this ⊢
    rw [← this]
    exact congrArg some (hmem ⟨.inr (.inr (.inl e)), _⟩
      (mem_union_right _ (mem_union_left _ (mem_image_of_mem
        (fun ex : Finset (Fin P.n) × Fin P.r =>
          (⟨.inr (.inr (.inl ex.1)), Fin.castLE P.hrq ex.2⟩ : Σ c : P.Coord, Fin (P.size c)))
        (show (e, (e.orderIsoOfFin hc).symm ⟨φ i, hi⟩) ∈ edges φ ×ˢ univ from
          mem_product.2 ⟨he, mem_univ _⟩))))).symm
  · rw [← hy i]
    unfold fval
    rw [hmem ⟨.inl j, Fin.castLE P.hnN (φ i)⟩
      (mem_union_left _ (mem_union_left _ (mem_image_of_mem _ (mem_univ i))))]

theorem copyOK_iff_of_agree (M : Matrix (Fin P.q) (Fin P.r) F) (κ : Fin P.N ≃ K)
    (j : Fin P.z) (a₀ : Fin P.NA) (k : ℕ) (φ : Fin P.q → Fin P.n) {ω ω' : P.Ω}
    (h : AgreeAt (copyDeps j φ) ω ω') :
    CopyOK M κ j a₀ k φ ω ↔ CopyOK M κ j a₀ k φ ω' :=
  ⟨copyOK_of_agree M κ j a₀ k φ h,
    copyOK_of_agree M κ j a₀ k φ fun cp hcp => (h cp hcp).symm⟩

end TParams

section Certificate

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {a : ι → ℕ} {β : Type*}

omit [Fintype ι] in
/-- A transposition at coordinate `c` only changes the two positions holding `x` and `y`. -/
theorem agreeAt_swap (ω : ∀ c, Perm (Fin (a c))) (c : ι) (x y : Fin (a c))
    (D : Finset (Σ c, Fin (a c))) (hx : (⟨c, (ω c).symm x⟩ : Σ c, Fin (a c)) ∉ D)
    (hy : (⟨c, (ω c).symm y⟩ : Σ c, Fin (a c)) ∉ D) :
    AgreeAt D ω (Function.update ω c (swap x y * ω c)) := by
  rintro ⟨c', p⟩ hp
  by_cases hc : c' = c
  · subst hc
    simp only [Function.update_self, Perm.mul_apply]
    refine (swap_apply_of_ne_of_ne ?_ ?_).symm
    · intro h; apply hx; have : p = (ω c').symm x := by simp [← h]
      exact this ▸ hp
    · intro h; apply hy; have : p = (ω c').symm y := by simp [← h]
      exact this ▸ hp
  · simp [Function.update_of_ne hc]

omit [Fintype ι] in
/-- The positions changed by the transposition are the same seen from the new point. -/
theorem symm_swap_update (ω : ∀ c, Perm (Fin (a c))) (c : ι) (x y : Fin (a c)) :
    ((Function.update ω c (swap x y * ω c)) c).symm x = (ω c).symm y ∧
      ((Function.update ω c (swap x y * ω c)) c).symm y = (ω c).symm x := by
  simp only [Function.update_self]
  constructor <;> simp [Equiv.Perm.mul_def]

omit [Fintype ι] in
open Classical in
/-- **Certificate Lipschitz bound.** If `G_b ω` is certified by the positions `W b ω` (any `ω'`
agreeing with `ω` there also satisfies `G_b`), a transposition at coordinate `c` changes
`X = #{b ∈ C : G_b}` by at most `2 L c`, where `L c` bounds the number of `b` with `G_b ω` whose
certificate contains a given position of `c`. -/
theorem countVar_lipschitz_cert (C : Finset β) (G : β → (∀ c, Perm (Fin (a c))) → Prop)
    (W : β → (∀ c, Perm (Fin (a c))) → Finset (Σ c, Fin (a c)))
    (hW : ∀ b ∈ C, ∀ ω ω', G b ω → AgreeAt (W b ω) ω ω' → G b ω') (L : ι → ℝ)
    (hL : ∀ ω c (p : Fin (a c)),
      ((C.filter fun b => G b ω ∧ (⟨c, p⟩ : Σ c, Fin (a c)) ∈ W b ω).card : ℝ) ≤ L c) :
    IsLipschitzG (countVar C G) (fun c => 2 * L c) := by
  -- one direction, for an arbitrary pair `ω₀ → ω₁` differing at two positions `p₁, p₂` of `c`
  have key : ∀ (ω₀ ω₁ : ∀ c, Perm (Fin (a c))) (c : ι) (p₁ p₂ : Fin (a c)),
      (∀ D : Finset (Σ c, Fin (a c)), (⟨c, p₁⟩ : Σ c, Fin (a c)) ∉ D →
        (⟨c, p₂⟩ : Σ c, Fin (a c)) ∉ D → AgreeAt D ω₁ ω₀) →
      countVar C G ω₁ - countVar C G ω₀ ≤ 2 * L c := by
    intro ω₀ ω₁ c p₁ p₂ hag
    unfold countVar
    have hsub : (C.filter fun b => G b ω₁) \ (C.filter fun b => G b ω₀) ⊆
        (C.filter fun b => G b ω₁ ∧ (⟨c, p₁⟩ : Σ c, Fin (a c)) ∈ W b ω₁) ∪
          C.filter fun b => G b ω₁ ∧ (⟨c, p₂⟩ : Σ c, Fin (a c)) ∈ W b ω₁ := by
      intro b hb
      obtain ⟨h1, h0⟩ := mem_sdiff.1 hb
      obtain ⟨hbC, hG1⟩ := mem_filter.1 h1
      by_contra hn
      simp only [mem_union, mem_filter, not_or, not_and] at hn
      exact h0 (mem_filter.2 ⟨hbC, hW b hbC ω₁ ω₀ hG1
        (hag _ (hn.1 hbC hG1) (hn.2 hbC hG1))⟩)
    have h1 : ((C.filter fun b => G b ω₁).card : ℝ) ≤
        (((C.filter fun b => G b ω₁) \ (C.filter fun b => G b ω₀)).card : ℝ) +
          (C.filter fun b => G b ω₀).card := by
      exact_mod_cast card_le_card_sdiff_add_card
    have h2 := card_le_card hsub
    have h3 := card_union_le (C.filter fun b => G b ω₁ ∧ (⟨c, p₁⟩ : Σ c, Fin (a c)) ∈ W b ω₁)
      (C.filter fun b => G b ω₁ ∧ (⟨c, p₂⟩ : Σ c, Fin (a c)) ∈ W b ω₁)
    have h4 := hL ω₁ c p₁
    have h5 := hL ω₁ c p₂
    have h23 : (((C.filter fun b => G b ω₁) \ (C.filter fun b => G b ω₀)).card : ℝ) ≤
        ((C.filter fun b => G b ω₁ ∧ (⟨c, p₁⟩ : Σ c, Fin (a c)) ∈ W b ω₁).card : ℝ) +
          (C.filter fun b => G b ω₁ ∧ (⟨c, p₂⟩ : Σ c, Fin (a c)) ∈ W b ω₁).card := by
      exact_mod_cast h2.trans h3
    linarith
  intro ω c x y
  set ω' := Function.update ω c (swap x y * ω c)
  rw [abs_le]
  constructor
  · have := key ω' ω c ((ω c).symm x) ((ω c).symm y) fun D hx hy =>
      agreeAt_swap ω c x y D hx hy
    linarith
  · refine key ω ω' c ((ω c).symm y) ((ω c).symm x) fun D hx hy => ?_
    have h := agreeAt_swap ω' c x y D
      (by rw [(symm_swap_update ω c x y).1]; exact hx)
      (by rw [(symm_swap_update ω c x y).2]; exact hy)
    have hω : Function.update ω' c (swap x y * ω' c) = ω := by
      funext c'
      by_cases hc : c' = c
      · subst hc; simp [ω', ← mul_assoc]
      · simp [ω', Function.update_of_ne hc]
    rw [hω] at h
    exact h

end Certificate

end DesignsII
