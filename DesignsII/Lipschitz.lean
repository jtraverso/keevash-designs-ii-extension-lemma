/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import DesignsII.ExtDefs
public import KeevashRAC.PL.Permutation

/-!
# Lipschitz functions of independent random injections (Keevash, *Existence of designs II*,
§3.1, Lemma `lip3`; *Designs I*, Lemma 2.11)

Let `a, a' : Fin m → ℕ`. A uniformly random injection `πᵢ : [a'ᵢ] → [aᵢ]` is the restriction of a
uniformly random permutation `σᵢ ∈ S_{aᵢ}` to its first `a'ᵢ` positions, so a function of
`π = (πᵢ)` is a function `f` of `σ = (σᵢ)` that only depends on the first `a'ᵢ` positions of each
`σᵢ` (`DependsFirstPi`). `f` is `b`-Lipschitz (`IsLipschitzPi`) if composing one `σᵢ` on the left
with a transposition changes `f` by at most `bᵢ`; it is then `B`-varying with
`B = ∑ a'ᵢ bᵢ²`.

* `perm_mgf_first`: for one permutation depending on its first `k` positions,
  `∑_σ exp(λ (f σ - 𝔼 f)) ≤ n! exp(k λ² b² / 2)` (refines `perm_mgf_le` of the registered
  *Counting designs* package, PALOMAR-2026-11-14-000022, whose helper lemmas are reused);
* `pi_mgf`: the product version, `∏ aᵢ! · exp(λ² B / 2)`;
* `lipschitz_tail` (**Lemma `lip3`**): `P(|f - 𝔼 f| > t) ≤ 2 exp(-t² / 2B)`.
-/

@[expose] public section

namespace DesignsII

open Finset Equiv Pseudorandom.Keevash

/-! ### One permutation, depending on its first `k` positions -/

/-- `g` only depends on the first `k` values `σ 0, …, σ (k-1)`. -/
def DependsFirst {n : ℕ} (g : Perm (Fin n) → ℝ) (k : ℕ) : Prop :=
  ∀ σ τ : Perm (Fin n), (∀ j : Fin n, (j : ℕ) < k → σ j = τ j) → g σ = g τ

theorem DependsFirst.comp_lift {n k : ℕ} {g : Perm (Fin (n + 1)) → ℝ}
    (hg : DependsFirst g (k + 1)) (p : Fin (n + 1)) :
    DependsFirst (fun σ => g (swap 0 p * liftPerm σ)) k := by
  intro σ τ h
  refine hg _ _ fun x hx => ?_
  simp only [Perm.coe_mul, Function.comp_apply]
  congr 1
  refine Fin.cases ?_ (fun j hj => ?_) x hx
  · intro _; rw [liftPerm_zero, liftPerm_zero]
  · rw [liftPerm_succ, liftPerm_succ, h j (by simp at hj; omega)]

theorem DependsFirst.const {n : ℕ} {g : Perm (Fin n) → ℝ} (hg : DependsFirst g 0)
    (σ : Perm (Fin n)) : g σ = g 1 :=
  hg σ 1 fun _ h => absurd h (Nat.not_lt_zero _)

/-- `sum_exp_le_of_sum_eq_zero` allowing `b = 0`. -/
theorem sum_exp_le_of_sum_eq_zero' {ι : Type*} [Fintype ι] (d : ι → ℝ) (hd : ∑ i, d i = 0)
    {b : ℝ} (hb : 0 ≤ b) (hdb : ∀ i, |d i| ≤ b) (l : ℝ) :
    ∑ i, Real.exp (l * d i) ≤ Fintype.card ι * Real.exp (l ^ 2 * b ^ 2 / 2) := by
  rcases hb.lt_or_eq with hb | rfl
  · exact sum_exp_le_of_sum_eq_zero d hd hb hdb l
  · have h0 : ∀ i, d i = 0 := fun i => abs_nonpos_iff.1 (hdb i)
    simp [h0]

/-- The exponential moment bound for a Lipschitz function of a uniform permutation that depends
only on its first `k` positions. -/
theorem perm_mgf_first : ∀ (n k : ℕ) (g : Perm (Fin n) → ℝ) {b : ℝ} (_hb : 0 ≤ b)
    (_hg : IsLipschitzPerm g b) (_hd : DependsFirst g k) (l : ℝ),
    ∑ σ, Real.exp (l * (g σ - permMean g)) ≤
      n.factorial * Real.exp (k * (l ^ 2 * b ^ 2) / 2)
  | n, 0, g, b, _, _, hd, l => by
    have hM : permMean g = g 1 := by
      simp only [permMean]
      rw [sum_congr rfl fun σ _ => hd.const σ, sum_const, card_univ, Fintype.card_perm,
        Fintype.card_fin, nsmul_eq_mul]
      have : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
      field_simp
    simp only [hM, hd.const, sub_self, mul_zero, Real.exp_zero, sum_const, card_univ,
      Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul, mul_one, Nat.cast_zero, zero_mul,
      zero_div]
    rfl
  | 0, k + 1, g, b, _, _, _, l => by
    have h1 : ∀ σ : Perm (Fin 0), σ = 1 := fun σ => Subsingleton.elim _ _
    have hM : permMean g = g 1 := by simp [permMean, h1]
    simp only [hM, h1, sub_self, mul_zero, Real.exp_zero, sum_const, card_univ, Fintype.card_perm,
      Fintype.card_fin, Nat.factorial_zero, Nat.cast_one, one_mul]
    simp only [one_smul]
    exact Real.one_le_exp (by positivity)
  | n + 1, k + 1, g, b, hb, hg, hd, l => by
    set F : Fin (n + 1) → Perm (Fin n) → ℝ := fun p σ => g (swap 0 p * liftPerm σ) with hF
    set m : Fin (n + 1) → ℝ := fun p => permMean (F p) with hm
    set M := permMean g with hMdef
    have hfac : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
    have hM : M = (∑ p, m p) / (n + 1) := by
      rw [hMdef, hm, permMean, sum_perm_succ]
      simp only [permMean, Nat.factorial_succ, Nat.cast_mul, ← sum_div, hF]
      push_cast
      field_simp
    have hd0 : ∑ p, (m p - M) = 0 := by
      rw [sum_sub_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, hM]
      push_cast
      field_simp
      ring
    have hmm : ∀ p q, |m q - m p| ≤ b := by
      intro p q
      have h := sum_lift_sub_le hg p q
      have : m q - m p = (∑ σ, F q σ - ∑ σ, F p σ) / n.factorial := by
        simp only [hm, permMean]; ring
      rw [this, abs_div, abs_of_pos hfac, div_le_iff₀ hfac]
      linarith
    have hdb : ∀ p, |m p - M| ≤ b := by
      intro p
      have : m p - M = (∑ q, (m p - m q)) / (n + 1) := by
        rw [sum_sub_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, hM]
        push_cast
        field_simp
      rw [this, abs_div, abs_of_pos (by positivity : (0 : ℝ) < n + 1),
        div_le_iff₀ (by positivity)]
      calc |∑ q, (m p - m q)| ≤ ∑ q, |m p - m q| := abs_sum_le_sum_abs _ _
        _ ≤ ∑ _q : Fin (n + 1), b := sum_le_sum fun q _ => by rw [abs_sub_comm]; exact hmm p q
        _ = b * (n + 1) := by simp; ring
    have hIH : ∀ p, ∑ σ, Real.exp (l * (F p σ - m p)) ≤
        n.factorial * Real.exp (k * (l ^ 2 * b ^ 2) / 2) :=
      fun p => perm_mgf_first n k (F p) hb (hg.comp_lift p) (hd.comp_lift p) l
    have hH := sum_exp_le_of_sum_eq_zero' (fun p => m p - M) hd0 hb hdb l
    rw [Fintype.card_fin] at hH
    calc ∑ σ, Real.exp (l * (g σ - M))
        = ∑ p, Real.exp (l * (m p - M)) * ∑ σ, Real.exp (l * (F p σ - m p)) := by
          rw [sum_perm_succ]
          refine sum_congr rfl fun p _ => ?_
          rw [mul_sum]
          refine sum_congr rfl fun σ _ => ?_
          rw [← Real.exp_add]
          congr 1
          simp only [hF]
          ring
      _ ≤ ∑ p, Real.exp (l * (m p - M)) * (n.factorial * Real.exp (k * (l ^ 2 * b ^ 2) / 2)) :=
          sum_le_sum fun p _ => mul_le_mul_of_nonneg_left (hIH p) (Real.exp_pos _).le
      _ = (∑ p, Real.exp (l * (m p - M))) * (n.factorial * Real.exp (k * (l ^ 2 * b ^ 2) / 2)) :=
          by rw [sum_mul]
      _ ≤ ((n + 1 : ℕ) * Real.exp (l ^ 2 * b ^ 2 / 2)) *
            (n.factorial * Real.exp (k * (l ^ 2 * b ^ 2) / 2)) := by
          gcongr
      _ = (n + 1).factorial * Real.exp ((k + 1 : ℕ) * (l ^ 2 * b ^ 2) / 2) := by
          rw [Nat.factorial_succ]
          push_cast
          rw [show ((k : ℝ) + 1) * (l ^ 2 * b ^ 2) / 2 =
            l ^ 2 * b ^ 2 / 2 + k * (l ^ 2 * b ^ 2) / 2 by ring, Real.exp_add]
          ring

/-! ### Several independent permutations -/

variable {m : ℕ} {a : Fin m → ℕ}

/-- `f` only depends on the first `a' i` positions of each `σ i`. -/
def DependsFirstPi (f : (∀ i, Perm (Fin (a i))) → ℝ) (a' : Fin m → ℕ) : Prop :=
  ∀ σ τ : ∀ i, Perm (Fin (a i)), (∀ i (j : Fin (a i)), (j : ℕ) < a' i → σ i j = τ i j) →
    f σ = f τ

/-- `f` is `b`-Lipschitz: composing `σ i` on the left with a transposition changes `f` by at
most `b i`. -/
def IsLipschitzPi (f : (∀ i, Perm (Fin (a i))) → ℝ) (b : Fin m → ℝ) : Prop :=
  ∀ (σ : ∀ i, Perm (Fin (a i))) (i : Fin m) (x y : Fin (a i)),
    |f (Function.update σ i (swap x y * σ i)) - f σ| ≤ b i

/-- The mean of `f` under independent uniform permutations. -/
noncomputable def piMean (f : (∀ i, Perm (Fin (a i))) → ℝ) : ℝ :=
  (∑ σ, f σ) / ∏ i, ((a i).factorial : ℝ)

theorem card_pi_perm_real (a : Fin m → ℕ) :
    ((univ : Finset (∀ i, Perm (Fin (a i)))).card : ℝ) = ∏ i, ((a i).factorial : ℝ) := by
  rw [card_univ, Fintype.card_pi]
  push_cast
  simp [Fintype.card_perm]

theorem prod_factorial_pos (a : Fin m → ℕ) : (0 : ℝ) < ∏ i, ((a i).factorial : ℝ) :=
  prod_pos fun i _ => by exact_mod_cast Nat.factorial_pos _

/-- Summing over `∀ i : Fin (m+1), Perm (Fin (a i))` is summing over the first coordinate and
the rest. -/
theorem sum_pi_cons {a : Fin (m + 1) → ℕ} (h : (∀ i, Perm (Fin (a i))) → ℝ) :
    ∑ σ, h σ = ∑ σ₀ : Perm (Fin (a 0)), ∑ ρ : (∀ i : Fin m, Perm (Fin (a i.succ))),
      h (Fin.cons σ₀ ρ) := by
  rw [← (Fin.consEquiv fun i => Perm (Fin (a i))).sum_comp, Fintype.sum_prod_type]
  rfl

/-- **The product exponential moment bound.** -/
theorem pi_mgf : ∀ (m : ℕ) (a a' : Fin m → ℕ) (f : (∀ i, Perm (Fin (a i))) → ℝ) (b : Fin m → ℝ)
    (_hb : ∀ i, 0 ≤ b i) (_hf : IsLipschitzPi f b) (_hd : DependsFirstPi f a') (l : ℝ),
    ∑ σ, Real.exp (l * (f σ - piMean f)) ≤
      (∏ i, ((a i).factorial : ℝ)) * Real.exp (l ^ 2 * ∑ i, (a' i : ℝ) * b i ^ 2 / 2)
  | 0, a, a', f, b, _, _, _, l => by
    have h1 : ∀ σ : ∀ i : Fin 0, Perm (Fin (a i)), σ = fun i => i.elim0 := fun σ =>
      funext fun i => i.elim0
    simp [piMean, h1]
  | m + 1, a, a', f, b, hb, hf, hd, l => by
    set F : Perm (Fin (a 0)) → (∀ i : Fin m, Perm (Fin (a i.succ))) → ℝ :=
      fun σ₀ ρ => f (Fin.cons σ₀ ρ) with hF
    set h : Perm (Fin (a 0)) → ℝ := fun σ₀ => piMean (F σ₀) with hh
    have hP := prod_factorial_pos (fun i : Fin m => a i.succ)
    have hP0 : (0 : ℝ) < (a 0).factorial := by exact_mod_cast Nat.factorial_pos _
    have hprod : ∏ i, ((a i).factorial : ℝ) =
        (a 0).factorial * ∏ i : Fin m, ((a i.succ).factorial : ℝ) := Fin.prod_univ_succ _
    have hM : piMean f = permMean h := by
      simp only [piMean, permMean, hh, hF]
      rw [sum_pi_cons, hprod, ← sum_div, div_div]; ring
    -- the first coordinate
    have hLip : IsLipschitzPerm h (b 0) := by
      intro σ₀ x y
      simp only [hh, piMean, hF]
      rw [← sub_div, ← sum_sub_distrib, abs_div, abs_of_pos hP, div_le_iff₀ hP]
      calc |∑ ρ, (f (Fin.cons (swap x y * σ₀) ρ) - f (Fin.cons σ₀ ρ))|
          ≤ ∑ ρ : (∀ i : Fin m, Perm (Fin (a i.succ))),
              |f (Fin.cons (swap x y * σ₀) ρ) - f (Fin.cons σ₀ ρ)| := abs_sum_le_sum_abs _ _
        _ ≤ ∑ _ρ : (∀ i : Fin m, Perm (Fin (a i.succ))), b 0 := by
            refine sum_le_sum fun ρ _ => ?_
            have := hf (Fin.cons σ₀ ρ) 0 x y
            rwa [Fin.cons_zero, Fin.update_cons_zero] at this
        _ = b 0 * ∏ i : Fin m, ((a i.succ).factorial : ℝ) := by
            rw [sum_const, nsmul_eq_mul, card_pi_perm_real]; ring
    have hDep : DependsFirst h (a' 0) := by
      intro σ τ hστ
      simp only [hh, piMean, hF]
      congr 1
      refine sum_congr rfl fun ρ _ => hd _ _ fun i j hj => ?_
      refine Fin.cases (fun j hj => ?_) (fun i j _ => rfl) i j hj
      simpa using hστ j hj
    -- the remaining coordinates
    have hIH : ∀ σ₀, ∑ ρ, Real.exp (l * (F σ₀ ρ - h σ₀)) ≤
        (∏ i : Fin m, ((a i.succ).factorial : ℝ)) *
          Real.exp (l ^ 2 * ∑ i : Fin m, (a' i.succ : ℝ) * b i.succ ^ 2 / 2) := by
      intro σ₀
      refine pi_mgf m (fun i => a i.succ) (fun i => a' i.succ) (F σ₀) (fun i => b i.succ)
        (fun i => hb _) (fun ρ i x y => ?_) (fun ρ ρ' hρ => ?_) l
      · have := hf (Fin.cons σ₀ ρ) i.succ x y
        simp only [Fin.cons_succ] at this
        rwa [← Fin.cons_update] at this
      · exact hd _ _ fun i => Fin.cases (fun _ _ => rfl) (fun i j hj => hρ i j hj) i
    have h1 := perm_mgf_first (a 0) (a' 0) h (hb 0) hLip hDep l
    calc ∑ σ, Real.exp (l * (f σ - piMean f))
        = ∑ σ₀, Real.exp (l * (h σ₀ - permMean h)) *
            ∑ ρ, Real.exp (l * (F σ₀ ρ - h σ₀)) := by
          rw [sum_pi_cons, hM]
          refine sum_congr rfl fun σ₀ _ => ?_
          rw [mul_sum]
          refine sum_congr rfl fun ρ _ => ?_
          rw [← Real.exp_add]
          congr 1
          simp only [hF]
          ring
      _ ≤ ∑ σ₀, Real.exp (l * (h σ₀ - permMean h)) *
            ((∏ i : Fin m, ((a i.succ).factorial : ℝ)) *
              Real.exp (l ^ 2 * ∑ i : Fin m, (a' i.succ : ℝ) * b i.succ ^ 2 / 2)) :=
          sum_le_sum fun σ₀ _ => mul_le_mul_of_nonneg_left (hIH σ₀) (Real.exp_pos _).le
      _ = (∑ σ₀, Real.exp (l * (h σ₀ - permMean h))) *
            ((∏ i : Fin m, ((a i.succ).factorial : ℝ)) *
              Real.exp (l ^ 2 * ∑ i : Fin m, (a' i.succ : ℝ) * b i.succ ^ 2 / 2)) := by
          rw [sum_mul]
      _ ≤ ((a 0).factorial * Real.exp (a' 0 * (l ^ 2 * b 0 ^ 2) / 2)) *
            ((∏ i : Fin m, ((a i.succ).factorial : ℝ)) *
              Real.exp (l ^ 2 * ∑ i : Fin m, (a' i.succ : ℝ) * b i.succ ^ 2 / 2)) := by
          gcongr
      _ = (∏ i, ((a i).factorial : ℝ)) *
            Real.exp (l ^ 2 * ∑ i, (a' i : ℝ) * b i ^ 2 / 2) := by
          rw [hprod, Fin.sum_univ_succ, mul_add, Real.exp_add]
          rw [show (a' 0 : ℝ) * (l ^ 2 * b 0 ^ 2) / 2 = l ^ 2 * ((a' 0 : ℝ) * b 0 ^ 2 / 2) by
            ring]
          ring

/-! ### The tail bound -/

open Classical in
/-- Probability under independent uniform permutations. -/
noncomputable def piProb (A : (∀ i, Perm (Fin (a i))) → Prop) : ℝ :=
  ((univ.filter A).card : ℝ) / ∏ i, ((a i).factorial : ℝ)

open Classical in
theorem card_upper_tail_pi (a' : Fin m → ℕ) (f : (∀ i, Perm (Fin (a i))) → ℝ) (b : Fin m → ℝ)
    (hb : ∀ i, 0 ≤ b i) (hf : IsLipschitzPi f b) (hd : DependsFirstPi f a')
    {B t : ℝ} (hB : B = ∑ i, (a' i : ℝ) * b i ^ 2) (hB0 : 0 < B) (ht : 0 < t) :
    ((univ.filter (fun σ => t < f σ - piMean f)).card : ℝ) ≤
      (∏ i, ((a i).factorial : ℝ)) * Real.exp (-(t ^ 2 / (2 * B))) := by
  set M := piMean f
  set l := t / B with hl
  have hl0 : 0 < l := by positivity
  have hmarkov : ((univ.filter (fun σ => t < f σ - M)).card : ℝ) * Real.exp (l * t) ≤
      ∑ σ, Real.exp (l * (f σ - M)) := by
    rw [← nsmul_eq_mul, ← sum_const]
    calc ∑ _σ ∈ univ.filter (fun σ => t < f σ - M), Real.exp (l * t)
        ≤ ∑ σ ∈ univ.filter (fun σ => t < f σ - M), Real.exp (l * (f σ - M)) := by
          refine sum_le_sum fun σ hσ => ?_
          rw [mem_filter] at hσ
          exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hσ.2.le hl0.le)
      _ ≤ ∑ σ, Real.exp (l * (f σ - M)) :=
          sum_le_sum_of_subset_of_nonneg (subset_univ _) fun _ _ _ => (Real.exp_pos _).le
  have hmgf := pi_mgf m a a' f b hb hf hd l
  have hexp : Real.exp (l ^ 2 * ∑ i, (a' i : ℝ) * b i ^ 2 / 2) =
      Real.exp (-(t ^ 2 / (2 * B))) * Real.exp (l * t) := by
    rw [← Real.exp_add]
    congr 1
    rw [← sum_div, ← hB, hl]
    field_simp
    ring
  rw [hexp, ← mul_assoc] at hmgf
  exact le_of_mul_le_mul_right (hmarkov.trans hmgf) (Real.exp_pos _)

theorem IsLipschitzPi.neg {f : (∀ i, Perm (Fin (a i))) → ℝ} {b : Fin m → ℝ}
    (hf : IsLipschitzPi f b) : IsLipschitzPi (fun σ => -f σ) b := by
  intro σ i x y
  rw [show -f (Function.update σ i (swap x y * σ i)) - -f σ =
    -(f (Function.update σ i (swap x y * σ i)) - f σ) by ring, abs_neg]
  exact hf σ i x y

/-- **Designs II, Lemma `lip3`** (*Designs I*, Lemma 2.11). If `f` is a `b`-Lipschitz function of
independent uniform permutations `σᵢ ∈ S_{aᵢ}` that only depends on their first `a'ᵢ` positions
(i.e. of independent uniform injections `[a'ᵢ] → [aᵢ]`) and `B = ∑ a'ᵢ bᵢ²`, then
`P(|f - 𝔼 f| > t) ≤ 2 exp(-t² / 2B)`. -/
theorem lipschitz_tail (a' : Fin m → ℕ) (f : (∀ i, Perm (Fin (a i))) → ℝ) (b : Fin m → ℝ)
    (hb : ∀ i, 0 ≤ b i) (hf : IsLipschitzPi f b) (hd : DependsFirstPi f a')
    {B t : ℝ} (hB : B = ∑ i, (a' i : ℝ) * b i ^ 2) (hB0 : 0 < B) (ht : 0 < t) :
    piProb (fun σ => t < |f σ - piMean f|) ≤ 2 * Real.exp (-(t ^ 2 / (2 * B))) := by
  classical
  have hP := prod_factorial_pos a
  have h1 := card_upper_tail_pi a' f b hb hf hd hB hB0 ht
  have h2 := card_upper_tail_pi a' (fun σ => -f σ) b hb hf.neg
    (fun σ τ h => by simp only [hd σ τ h]) hB hB0 ht
  have hmean : piMean (fun σ => -f σ) = -piMean f := by
    simp [piMean, sum_neg_distrib, neg_div]
  simp only [hmean] at h2
  have hsub : univ.filter (fun σ => t < |f σ - piMean f|) ⊆
      univ.filter (fun σ => t < f σ - piMean f) ∪
        univ.filter (fun σ => t < -f σ - -piMean f) := by
    intro σ hσ
    simp only [mem_filter, mem_univ, true_and, mem_union] at hσ ⊢
    rcases lt_abs.1 hσ with h | h
    · left; exact h
    · right; linarith
  unfold piProb
  rw [div_le_iff₀ hP]
  calc ((univ.filter (fun σ => t < |f σ - piMean f|)).card : ℝ)
      ≤ ((univ.filter (fun σ => t < f σ - piMean f) ∪
          univ.filter (fun σ => t < -f σ - -piMean f)).card : ℝ) := by
        exact_mod_cast card_le_card hsub
    _ ≤ ((univ.filter (fun σ => t < f σ - piMean f)).card : ℝ) +
          (univ.filter (fun σ => t < -f σ - -piMean f)).card := by
        exact_mod_cast card_union_le _ _
    _ ≤ _ := by linarith


/-! ### Arbitrary finite index types -/

section General

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {a : ι → ℕ}

/-- `f` only depends on the first `a' i` positions of each `σ i` (general index type). -/
def DependsFirstG (f : (∀ i, Perm (Fin (a i))) → ℝ) (a' : ι → ℕ) : Prop :=
  ∀ σ τ : ∀ i, Perm (Fin (a i)), (∀ i (j : Fin (a i)), (j : ℕ) < a' i → σ i j = τ i j) →
    f σ = f τ

/-- `b`-Lipschitz (general index type). -/
def IsLipschitzG (f : (∀ i, Perm (Fin (a i))) → ℝ) (b : ι → ℝ) : Prop :=
  ∀ (σ : ∀ i, Perm (Fin (a i))) (i : ι) (x y : Fin (a i)),
    |f (Function.update σ i (swap x y * σ i)) - f σ| ≤ b i

/-- Mean under independent uniform permutations (general index type). -/
noncomputable def meanG (f : (∀ i, Perm (Fin (a i))) → ℝ) : ℝ :=
  (∑ σ, f σ) / ∏ i, ((a i).factorial : ℝ)

/-- **Lemma `lip3`** for an arbitrary finite index type of independent uniform permutations. -/
theorem lipschitz_tail_general (a' : ι → ℕ) (f : (∀ i, Perm (Fin (a i))) → ℝ) (b : ι → ℝ)
    (hb : ∀ i, 0 ≤ b i) (hf : IsLipschitzG f b) (hd : DependsFirstG f a')
    {B t : ℝ} (hB : B = ∑ i, (a' i : ℝ) * b i ^ 2) (hB0 : 0 < B) (ht : 0 < t) :
    probG (fun σ => t < |f σ - meanG f|) ≤ 2 * Real.exp (-(t ^ 2 / (2 * B))) := by
  classical
  set e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  set P : ι → Type := fun i => Perm (Fin (a i))
  set E := Equiv.piCongrLeft' P e
  set g : (∀ j : Fin (Fintype.card ι), Perm (Fin (a (e.symm j)))) → ℝ := fun τ => f (E.symm τ)
  have hS : ∀ τ j, E.symm τ (e.symm j) = τ j := fun τ j =>
    Equiv.piCongrLeft'_symm_apply_apply P e τ j
  have hprod : ∏ j, ((a (e.symm j)).factorial : ℝ) = ∏ i, ((a i).factorial : ℝ) :=
    Equiv.prod_comp e.symm (fun i => ((a i).factorial : ℝ))
  have hmean : piMean g = meanG f := by
    unfold piMean meanG
    rw [hprod]
    congr 1
    exact Equiv.sum_comp E.symm f
  have hg : IsLipschitzPi g (fun j => b (e.symm j)) := by
    intro τ j x y
    have := hf (E.symm τ) (e.symm j) x y
    simp only [g]
    rw [Function.piCongrLeft'_symm_update]
    rwa [hS] at this
  have hgd : DependsFirstPi g (fun j => a' (e.symm j)) := by
    intro τ τ' h
    refine hd _ _ fun i => ?_
    obtain ⟨j, rfl⟩ := e.symm.surjective i
    rw [hS, hS]
    exact h j
  have hB' : B = ∑ j, (a' (e.symm j) : ℝ) * b (e.symm j) ^ 2 := by
    rw [hB]; exact (Equiv.sum_comp e.symm (fun i => (a' i : ℝ) * b i ^ 2)).symm
  have h := lipschitz_tail (fun j => a' (e.symm j)) g (fun j => b (e.symm j)) (fun j => hb _) hg
    hgd hB' hB0 ht
  unfold piProb at h
  unfold probG
  rw [hprod, hmean] at h
  have hcard : (univ.filter fun τ => t < |g τ - meanG f|).card =
      (univ.filter fun σ => t < |f σ - meanG f|).card := by
    refine card_bij (fun τ _ => E.symm τ) (fun τ hτ => by simpa [g] using hτ)
      (fun τ _ τ' _ h => E.symm.injective h) fun σ hσ => ⟨E σ, by simpa [g] using hσ, by simp⟩
  rw [hcard] at h
  exact h

end General

end DesignsII
