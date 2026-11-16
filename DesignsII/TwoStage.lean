/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import DesignsII.Counting

/-!
# Two-stage concentration

Split the coordinates of `Ω = ∏_c S_{a c}` by a predicate `p` into `Ω₁` (`p c`) and `Ω₂`
(`¬ p c`), and write `ω = merge ω₁ ω₂`. For `X : Ω → ℝ` let `condMean X ω` be the mean of `X` over
`Ω₂` with the `Ω₁`-coordinates of `ω` fixed (`𝔼[X | ω₁]`).

* `meanG_condMean`: `𝔼[𝔼[X | ω₁]] = 𝔼 X`;
* `two_stage_tail`: `P(|X - 𝔼X| > t₁ + t₂) ≤ P(|𝔼[X | ω₁] - 𝔼X| > t₁) + ε₂` whenever, for every
  `ω₁`, `P_{ω₂}(|X - 𝔼[X | ω₁]| > t₂) ≤ ε₂`.

In the template space, `Ω₁` = (f, T, π) and `Ω₂` = (A_φ, act_φ): given `ω₁` only the copies
compatible with (f, T, π) matter, which makes the Lipschitz constants on `Ω₂` small
(concentration plan for Lemma `ext*`, BLUEPRINT).
-/

@[expose] public section

namespace DesignsII

open Finset Equiv

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {a : ι → ℕ} (p : ι → Prop) [DecidablePred p]

/-- The first-stage coordinates. -/
abbrev Ω₁ : Type _ := ∀ c : {c // p c}, Perm (Fin (a c))

/-- The second-stage coordinates. -/
abbrev Ω₂ : Type _ := ∀ c : {c // ¬ p c}, Perm (Fin (a c))

variable {p}

/-- Recombine the two stages. -/
def merge (ω₁ : Ω₁ (a := a) p) (ω₂ : Ω₂ (a := a) p) : ∀ c, Perm (Fin (a c)) :=
  fun c => if h : p c then ω₁ ⟨c, h⟩ else ω₂ ⟨c, h⟩

/-- The first-stage part of `ω`. -/
def part₁ (ω : ∀ c, Perm (Fin (a c))) : Ω₁ (a := a) p := fun c => ω c

omit [Fintype ι] [DecidableEq ι] in
theorem merge_part (ω : ∀ c, Perm (Fin (a c))) (ω₂ : Ω₂ (a := a) p) (c : ι) (h : p c) :
    merge (part₁ ω) ω₂ c = ω c := by
  simp [merge, part₁, h]

/-- `merge` as an equivalence `Ω₁ × Ω₂ ≃ Ω`. -/
def mergeEquiv : (Ω₁ (a := a) p × Ω₂ (a := a) p) ≃ ∀ c, Perm (Fin (a c)) where
  toFun x := merge x.1 x.2
  invFun ω := (fun c => ω c, fun c => ω c)
  left_inv x := by
    rcases x with ⟨ω₁, ω₂⟩
    ext1
    · funext c; simp [merge, c.2]
    · funext c; simp [merge, c.2]
  right_inv ω := by
    funext c
    by_cases h : p c <;> simp [merge, h]

theorem sum_merge (f : (∀ c, Perm (Fin (a c))) → ℝ) :
    ∑ ω, f ω = ∑ ω₁ : Ω₁ (a := a) p, ∑ ω₂ : Ω₂ (a := a) p, f (merge ω₁ ω₂) := by
  rw [← (mergeEquiv (a := a) (p := p)).sum_comp, Fintype.sum_prod_type]
  rfl

omit [DecidableEq ι] in
theorem prod_factorial_split :
    ∏ c, ((a c).factorial : ℝ) =
      (∏ c : {c // p c}, ((a c).factorial : ℝ)) * ∏ c : {c // ¬ p c}, ((a c).factorial : ℝ) :=
  (Fintype.prod_subtype_mul_prod_subtype p fun c => ((a c).factorial : ℝ)).symm

/-- `𝔼[X | ω₁]`: average over the second-stage coordinates. -/
noncomputable def condMean (X : (∀ c, Perm (Fin (a c))) → ℝ) (ω : ∀ c, Perm (Fin (a c))) : ℝ :=
  (∑ ω₂ : Ω₂ (a := a) p, X (merge (part₁ ω) ω₂)) / ∏ c : {c // ¬ p c}, ((a c).factorial : ℝ)

theorem condMean_merge (X : (∀ c, Perm (Fin (a c))) → ℝ) (ω₁ : Ω₁ (a := a) p)
    (ω₂ : Ω₂ (a := a) p) :
    condMean (p := p) X (merge ω₁ ω₂) =
      (∑ ω₂' : Ω₂ (a := a) p, X (merge ω₁ ω₂')) / ∏ c : {c // ¬ p c}, ((a c).factorial : ℝ) := by
  unfold condMean
  congr 2
  funext ω₂'
  congr 1
  funext c
  by_cases h : p c <;> simp [merge, part₁, h]

omit [DecidableEq ι] in
theorem prod_pos_sub (q : ι → Prop) [DecidablePred q] : (0 : ℝ) < ∏ c : {c // q c}, ((a c).factorial : ℝ) :=
  prod_pos fun c _ => by exact_mod_cast Nat.factorial_pos _

/-- The tower property. -/
theorem meanG_condMean (X : (∀ c, Perm (Fin (a c))) → ℝ) :
    meanG (condMean (p := p) X) = meanG X := by
  unfold meanG
  rw [sum_merge (p := p), sum_merge (p := p) X]
  simp_rw [condMean_merge]
  rw [sum_congr rfl fun ω₁ _ => sum_const _, prod_factorial_split (p := p)]
  have h2 := prod_pos_sub (a := a) fun c => ¬ p c
  simp only [card_univ, nsmul_eq_mul]
  have hcard : (Fintype.card (Ω₂ (a := a) p) : ℝ) = ∏ c : {c // ¬ p c}, ((a c).factorial : ℝ) := by
    rw [Fintype.card_pi]; push_cast; simp [Fintype.card_perm]
  rw [hcard]
  congr 1
  exact sum_congr rfl fun ω₁ _ => by field_simp

/-- Union bound. -/
theorem probG_or_le (A B : (∀ c, Perm (Fin (a c))) → Prop) :
    probG (a := a) (fun ω => A ω ∨ B ω) ≤ probG (a := a) A + probG (a := a) B := by
  classical
  unfold probG
  rw [← add_div]
  refine div_le_div_of_nonneg_right ?_ (prod_nonneg fun c _ => by positivity)
  norm_cast
  calc _ ≤ (@Finset.filter _ A (Classical.decPred _) univ ∪
        @Finset.filter _ B (Classical.decPred _) univ).card :=
        card_le_card fun ω hω => by
          simp only [mem_filter, mem_union, mem_univ, true_and] at hω ⊢; exact hω
    _ ≤ _ := card_union_le _ _

open Classical in
/-- **Two-stage tail bound.** -/
theorem two_stage_tail (X : (∀ c, Perm (Fin (a c))) → ℝ) {t₁ t₂ ε₂ : ℝ}
    (h₂ : ∀ ω₁ : Ω₁ (a := a) p, probG (a := fun c : {c // ¬ p c} => a c)
      (fun ω₂ => t₂ < |X (merge ω₁ ω₂) - condMean (p := p) X (merge ω₁ ω₂)|) ≤ ε₂) :
    probG (a := a) (fun ω => t₁ + t₂ < |X ω - meanG X|) ≤
      probG (a := a) (fun ω => t₁ < |condMean (p := p) X ω - meanG X|) + ε₂ := by
  have hsub : ∀ ω, t₁ + t₂ < |X ω - meanG X| →
      (t₁ < |condMean (p := p) X ω - meanG X| ∨ t₂ < |X ω - condMean (p := p) X ω|) := by
    intro ω h
    by_contra hn
    push Not at hn
    have := abs_sub_le (X ω) (condMean (p := p) X ω) (meanG X)
    linarith [hn.1, hn.2]
  -- the second-stage part
  have hP := prod_pos_sub (a := a) fun c => p c
  have hQ := prod_pos_sub (a := a) fun c => ¬ p c
  have hsecond : probG (a := a) (fun ω => t₂ < |X ω - condMean (p := p) X ω|) ≤ ε₂ := by
    unfold probG
    rw [div_le_iff₀ (prod_pos fun c _ => by exact_mod_cast Nat.factorial_pos _),
      prod_factorial_split (p := p)]
    have hcnt : ((univ.filter fun ω => t₂ < |X ω - condMean (p := p) X ω|).card : ℝ) =
        ∑ ω₁ : Ω₁ (a := a) p, ((univ.filter fun ω₂ : Ω₂ (a := a) p =>
          t₂ < |X (merge ω₁ ω₂) - condMean (p := p) X (merge ω₁ ω₂)|).card : ℝ) := by
      rw [card_filter, Nat.cast_sum, sum_merge (p := p)]
      simp_rw [card_filter, Nat.cast_sum]
    rw [hcnt]
    calc ∑ ω₁ : Ω₁ (a := a) p, ((univ.filter fun ω₂ : Ω₂ (a := a) p =>
          t₂ < |X (merge ω₁ ω₂) - condMean (p := p) X (merge ω₁ ω₂)|).card : ℝ)
        ≤ ∑ _ω₁ : Ω₁ (a := a) p, ε₂ * ∏ c : {c // ¬ p c}, ((a c).factorial : ℝ) := by
          refine sum_le_sum fun ω₁ _ => ?_
          have := h₂ ω₁
          unfold probG at this
          exact (div_le_iff₀ hQ).1 this
      _ = ε₂ * ((∏ c : {c // p c}, ((a c).factorial : ℝ)) *
            ∏ c : {c // ¬ p c}, ((a c).factorial : ℝ)) := by
          rw [sum_const, card_univ, nsmul_eq_mul, Fintype.card_pi]
          push_cast
          simp only [Fintype.card_perm, Fintype.card_fin]
          ring
  calc probG (a := a) (fun ω => t₁ + t₂ < |X ω - meanG X|)
      ≤ probG (a := a) (fun ω => t₁ < |condMean (p := p) X ω - meanG X| ∨
          t₂ < |X ω - condMean (p := p) X ω|) := probG_mono fun ω h => hsub ω h
    _ ≤ probG (a := a) (fun ω => t₁ < |condMean (p := p) X ω - meanG X|) +
          probG (a := a) (fun ω => t₂ < |X ω - condMean (p := p) X ω|) := probG_or_le _ _
    _ ≤ _ := by linarith


omit [Fintype ι] in
theorem merge_update₂ (ω₁ : Ω₁ (a := a) p) (ω₂ : Ω₂ (a := a) p) (c : {c // ¬ p c})
    (v : Perm (Fin (a c))) :
    merge ω₁ (Function.update ω₂ c v) = Function.update (merge ω₁ ω₂) c.1 v := by
  funext c'
  by_cases h : c' = c.1
  · subst h; simp [merge, c.2]
  · by_cases hp : p c'
    · simp [merge, hp, Function.update_of_ne h]
    · have : (⟨c', hp⟩ : {c // ¬ p c}) ≠ c := fun h' => h (congrArg Subtype.val h')
      simp [merge, hp, Function.update_of_ne h, Function.update_of_ne this]

omit [Fintype ι] in
theorem update_merge₁ (ω : ∀ c, Perm (Fin (a c))) (ω₂ : Ω₂ (a := a) p) (c : ι) (hc : p c)
    (v : Perm (Fin (a c))) :
    merge (part₁ (Function.update ω c v)) ω₂ = Function.update (merge (part₁ ω) ω₂) c v := by
  funext c'
  by_cases h : c' = c
  · subst h; simp [merge, part₁, hc]
  · by_cases hp : p c'
    · simp [merge, part₁, hp, Function.update_of_ne h]
    · simp [merge, hp, Function.update_of_ne h]

omit [Fintype ι] in
/-- The second-stage restriction is Lipschitz with the same constants. -/
theorem lipschitz_stage₂ {X : (∀ c, Perm (Fin (a c))) → ℝ} {b : ι → ℝ} (hX : IsLipschitzG X b)
    (ω₁ : Ω₁ (a := a) p) :
    IsLipschitzG (a := fun c : {c // ¬ p c} => a c) (fun ω₂ => X (merge ω₁ ω₂))
      (fun c => b c.1) := by
  intro ω₂ c x y
  simp only
  rw [merge_update₂]
  have : (merge ω₁ ω₂) c.1 = ω₂ c := by simp [merge, c.2]
  have h := hX (merge ω₁ ω₂) c.1 x y
  rwa [this] at h

/-- **The conditional mean is Lipschitz** with the first-stage constants (and constant `0` in the
second-stage coordinates, on which it does not depend). -/
theorem lipschitz_condMean {X : (∀ c, Perm (Fin (a c))) → ℝ} {b : ι → ℝ}
    (hX : IsLipschitzG X b) :
    IsLipschitzG (condMean (p := p) X) (fun c => if p c then b c else 0) := by
  intro ω c x y
  have hQ := prod_pos_sub (a := a) fun c => ¬ p c
  show _ ≤ if p c then b c else 0
  by_cases hc : p c
  · rw [if_pos hc]
    unfold condMean
    rw [← sub_div, abs_div, abs_of_pos hQ, div_le_iff₀ hQ, ← sum_sub_distrib]
    calc |∑ ω₂ : Ω₂ (a := a) p, (X (merge (part₁ (Function.update ω c (swap x y * ω c))) ω₂) -
          X (merge (part₁ ω) ω₂))|
        ≤ ∑ ω₂ : Ω₂ (a := a) p, |X (merge (part₁ (Function.update ω c (swap x y * ω c))) ω₂) -
          X (merge (part₁ ω) ω₂)| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ _ω₂ : Ω₂ (a := a) p, b c := by
          refine sum_le_sum fun ω₂ _ => ?_
          rw [update_merge₁ ω ω₂ c hc]
          have h1 : merge (part₁ ω) ω₂ c = ω c := merge_part ω ω₂ c hc
          have h := hX (merge (part₁ ω) ω₂) c x y
          rwa [h1] at h
      _ = b c * ∏ c : {c // ¬ p c}, ((a c).factorial : ℝ) := by
          rw [sum_const, card_univ, nsmul_eq_mul, Fintype.card_pi]
          push_cast
          simp only [Fintype.card_perm, Fintype.card_fin]
          ring
  · rw [if_neg hc]
    have : part₁ (p := p) (Function.update ω c (swap x y * ω c)) = part₁ ω := by
      funext c'
      have : (c' : ι) ≠ c := fun h => hc (h ▸ c'.2)
      simp [part₁, Function.update_of_ne this]
    simp [condMean, this]

/-- The conditional mean only depends on the first-stage coordinates. -/
theorem depends_condMean {X : (∀ c, Perm (Fin (a c))) → ℝ} {a' : ι → ℕ}
    (hX : DependsFirstG X a') :
    DependsFirstG (condMean (p := p) X) (fun c => if p c then a' c else 0) := by
  intro ω ω' h
  unfold condMean
  congr 1
  refine sum_congr rfl fun ω₂ _ => hX _ _ fun c j hj => ?_
  by_cases hc : p c
  · rw [merge_part ω ω₂ c hc, merge_part ω' ω₂ c hc]
    exact h c j (by simpa [hc] using hj)
  · simp [merge, hc]

omit [Fintype ι] [DecidableEq ι] in
/-- The second-stage restriction only depends on the first `a'` positions. -/
theorem depends_stage₂ {X : (∀ c, Perm (Fin (a c))) → ℝ} {a' : ι → ℕ}
    (hX : DependsFirstG X a') (ω₁ : Ω₁ (a := a) p) :
    DependsFirstG (a := fun c : {c // ¬ p c} => a c) (fun ω₂ => X (merge ω₁ ω₂))
      (fun c => a' c.1) := by
  intro ω₂ ω₂' h
  refine hX _ _ fun c j hj => ?_
  by_cases hc : p c
  · simp [merge, hc]
  · simp only [merge, hc, dif_neg, not_false_eq_true]
    exact h ⟨c, hc⟩ j hj


section TailLe

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {a : ι → ℕ}

/-- **Lemma `lip3` with an upper bound for the variance proxy.** -/
theorem lipschitz_tail_le (a' : ι → ℕ) (f : (∀ i, Perm (Fin (a i))) → ℝ) (b : ι → ℝ)
    (hb : ∀ i, 0 ≤ b i) (hf : IsLipschitzG f b) (hd : DependsFirstG f a') {B t : ℝ}
    (hB : ∑ i, (a' i : ℝ) * b i ^ 2 ≤ B) (hB0 : 0 < B) (ht : 0 < t) :
    probG (a := a) (fun σ => t < |f σ - meanG f|) ≤ 2 * Real.exp (-(t ^ 2 / (2 * B))) := by
  classical
  set B' := ∑ i, (a' i : ℝ) * b i ^ 2
  by_cases hB' : 0 < B'
  · -- scale the constants up so that the proxy is exactly `B`
    set s := Real.sqrt (B / B')
    have hs1 : 1 ≤ s := Real.one_le_sqrt.2 ((one_le_div hB').2 hB)
    have hss : s ^ 2 = B / B' := Real.sq_sqrt (by positivity)
    refine lipschitz_tail_general a' f (fun i => s * b i)
      (fun i => mul_nonneg (Real.sqrt_nonneg _) (hb i))
      (fun σ i x y => (hf σ i x y).trans (le_mul_of_one_le_left (hb i) hs1)) hd ?_ hB0 ht
    have : ∑ i, (a' i : ℝ) * (s * b i) ^ 2 = B / B' * B' := by
      rw [mul_sum]
      refine sum_congr rfl fun i _ => ?_
      rw [mul_pow, hss]; ring
    rw [this]; field_simp
  · have hnn : ∀ i ∈ univ, 0 ≤ (a' i : ℝ) * b i ^ 2 := fun i _ => by
      have := hb i; positivity
    have hzero : ∀ i, (a' i : ℝ) * b i ^ 2 = 0 := fun i =>
      (sum_eq_zero_iff_of_nonneg hnn).1 (le_antisymm (not_lt.1 hB') (sum_nonneg hnn)) i
        (mem_univ i)
    by_cases hex : ∃ i, a' i ≠ 0
    · obtain ⟨i₀, hi₀⟩ := hex
      have ha : (0 : ℝ) < a' i₀ := by exact_mod_cast Nat.pos_of_ne_zero hi₀
      have hb0 : b i₀ = 0 := by
        have := hzero i₀
        exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1
          ((mul_eq_zero.1 this).resolve_left ha.ne')
      set b' : ι → ℝ := fun i => if i = i₀ then Real.sqrt (B / a' i₀) else b i
      refine lipschitz_tail_general a' f b' (fun i => by
          by_cases h : i = i₀
          · simp only [b', if_pos h]; exact Real.sqrt_nonneg _
          · simp only [b', if_neg h]; exact hb i)
        (fun σ i x y => (hf σ i x y).trans (by
          by_cases h : i = i₀
          · subst h; simp only [b', if_true, hb0]; exact Real.sqrt_nonneg _
          · simp only [b', if_neg h]; exact le_rfl)) hd ?_ hB0 ht
      rw [← add_sum_erase univ _ (mem_univ i₀), sum_eq_zero fun i hi => by
        simp only [b', if_neg (ne_of_mem_erase hi)]; exact hzero i]
      simp only [b', if_true]
      rw [Real.sq_sqrt (by positivity)]
      field_simp
      ring
    · push Not at hex
      have hP : (0 : ℝ) < ∏ i, ((a i).factorial : ℝ) :=
        prod_pos fun i _ => by exact_mod_cast Nat.factorial_pos _
      -- `f` is constant
      have hconst : ∀ σ, f σ = meanG f := by
        intro σ
        have : ∀ τ, f τ = f σ := fun τ => hd τ σ fun i j hj => by
          rw [hex i] at hj; exact absurd hj (Nat.not_lt_zero _)
        unfold meanG
        rw [sum_congr rfl fun τ _ => this τ, sum_const, card_univ, nsmul_eq_mul]
        have hc : (Fintype.card (∀ i, Perm (Fin (a i))) : ℝ) = ∏ i, ((a i).factorial : ℝ) := by
          rw [Fintype.card_pi]; push_cast; simp [Fintype.card_perm]
        rw [hc]; field_simp
      have : probG (a := a) (fun σ => t < |f σ - meanG f|) = 0 := by
        unfold probG
        rw [filter_false_of_mem fun σ _ h => by
          rw [← hconst σ, sub_self, abs_zero] at h; linarith]
        simp
      rw [this]; positivity

end TailLe


section TwoStageLip

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {a : ι → ℕ} {p : ι → Prop} [DecidablePred p]

/-- **Two-stage concentration via `lip3`.** The first stage uses Lipschitz data of the conditional
mean on all of `Ω`; the second stage may use Lipschitz data depending on the first-stage outcome
(e.g. only the copies compatible with `(f, T, π)` matter). -/
theorem two_stage_lip_tail (X : (∀ c, Perm (Fin (a c))) → ℝ) (b₁ : ι → ℝ) (hb₁ : ∀ c, 0 ≤ b₁ c)
    (a₁ : ι → ℕ) (h₁L : IsLipschitzG (condMean (p := p) X) b₁)
    (h₁D : DependsFirstG (condMean (p := p) X) a₁) {B₁ B₂ t₁ t₂ : ℝ}
    (hB₁ : ∑ c, (a₁ c : ℝ) * b₁ c ^ 2 ≤ B₁) (hB₁0 : 0 < B₁)
    (h₂ : ∀ ω₁ : Ω₁ (a := a) p, ∃ (b₂ : {c // ¬ p c} → ℝ) (a₂ : {c // ¬ p c} → ℕ),
      (∀ c, 0 ≤ b₂ c) ∧
      IsLipschitzG (a := fun c : {c // ¬ p c} => a c) (fun ω₂ => X (merge ω₁ ω₂)) b₂ ∧
      DependsFirstG (a := fun c : {c // ¬ p c} => a c) (fun ω₂ => X (merge ω₁ ω₂)) a₂ ∧
      ∑ c, (a₂ c : ℝ) * b₂ c ^ 2 ≤ B₂)
    (hB₂0 : 0 < B₂) (ht₁ : 0 < t₁) (ht₂ : 0 < t₂) :
    probG (a := a) (fun ω => t₁ + t₂ < |X ω - meanG X|) ≤
      2 * Real.exp (-(t₁ ^ 2 / (2 * B₁))) + 2 * Real.exp (-(t₂ ^ 2 / (2 * B₂))) := by
  refine (two_stage_tail (p := p) (ε₂ := 2 * Real.exp (-(t₂ ^ 2 / (2 * B₂)))) X
    fun ω₁ => ?_).trans ?_
  · obtain ⟨b₂, a₂, hb₂, hL, hD, hB⟩ := h₂ ω₁
    have hmean : ∀ ω₂, condMean (p := p) X (merge ω₁ ω₂) =
        meanG (a := fun c : {c // ¬ p c} => a c) (fun ω₂' => X (merge ω₁ ω₂')) := by
      intro ω₂; rw [condMean_merge]; rfl
    simp_rw [hmean]
    exact lipschitz_tail_le a₂ _ b₂ hb₂ hL hD hB hB₂0 ht₂
  · have h1 := lipschitz_tail_le a₁ (condMean (p := p) X) b₁ hb₁ h₁L h₁D hB₁ hB₁0 ht₁
    rw [meanG_condMean] at h1
    linarith

end TwoStageLip

end DesignsII
