/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Asymptotics of the variance proxies of Lemma `ext*`

For an extension with `v ≥ 1` new vertices, configurations `|C| ≤ Δ N^v` and
`D_i ≤ Δ N^{v-(r-f_i)}` configurations through a given `i`-th edge (`f_i ≤ r - 1` fixed vertices
in it), the proxies of `ext_star` satisfy

* `proxy₁_le`: `z N (2 L_f)² ≤ 4 z (m q^r C Δ)² N^{2v-1}`, `L_f = ∑_i q^{f_i+1} N^{r-f_i-1} C D_i`;
* `proxy₂_le`: `4 S (z q^r + z) (∑_i C D_i) (2C+2) m |C| z q^r ≤ c₂ N^{2v-1}`;
* `exp_tail_le`: for `t = ε N^v` and `B ≤ c N^{2v-1}`, `exp(-t²/2B) ≤ exp(-ε² N/(2c))`.

Here `C = C(q,r)` is any natural number (`CC`).
-/

@[expose] public section

namespace DesignsII

open Finset

theorem Lf_sum_le {m : ℕ} (N v r q CC Δ : ℕ) (f D : Fin m → ℕ) (hq : 1 ≤ q)
    (hf : ∀ i, f i + 1 ≤ r) (hrv : ∀ i, r ≤ v + f i) (hD : ∀ i, D i ≤ Δ * N ^ (v - (r - f i))) :
    ∑ i, q ^ (f i + 1) * N ^ (r - (f i + 1)) * (CC * D i) ≤ m * (q ^ r * CC * Δ) * N ^ (v - 1) := by
  calc ∑ i, q ^ (f i + 1) * N ^ (r - (f i + 1)) * (CC * D i)
      ≤ ∑ _i : Fin m, q ^ r * CC * Δ * N ^ (v - 1) := by
        refine sum_le_sum fun i _ => ?_
        have hexp : r - (f i + 1) + (v - (r - f i)) = v - 1 := by
          have := hf i; have := hrv i; omega
        calc q ^ (f i + 1) * N ^ (r - (f i + 1)) * (CC * D i)
            ≤ q ^ r * N ^ (r - (f i + 1)) * (CC * (Δ * N ^ (v - (r - f i)))) := by
              gcongr
              all_goals first | exact hq | exact hf i | exact hD i
          _ = q ^ r * CC * Δ * N ^ (v - 1) := by rw [← hexp, pow_add]; ring
    _ = m * (q ^ r * CC * Δ) * N ^ (v - 1) := by
        rw [sum_const, card_univ, Fintype.card_fin, smul_eq_mul]; ring

theorem D_sum_le {m : ℕ} (N v r CC Δ : ℕ) (f D : Fin m → ℕ) (hN : 1 ≤ N)
    (hf : ∀ i, f i + 1 ≤ r) (hD : ∀ i, D i ≤ Δ * N ^ (v - (r - f i))) :
    ∑ i, CC * D i ≤ m * (CC * Δ) * N ^ (v - 1) := by
  calc ∑ i, CC * D i ≤ ∑ _i : Fin m, CC * Δ * N ^ (v - 1) := by
        refine sum_le_sum fun i _ => ?_
        calc CC * D i ≤ CC * (Δ * N ^ (v - (r - f i))) := Nat.mul_le_mul_left _ (hD i)
          _ ≤ CC * (Δ * N ^ (v - 1)) := by
              gcongr
              all_goals first | exact hN | (have := hf i; omega)
          _ = CC * Δ * N ^ (v - 1) := by ring
    _ = m * (CC * Δ) * N ^ (v - 1) := by
        rw [sum_const, card_univ, Fintype.card_fin, smul_eq_mul]; ring

theorem pow_two_sub_one {N : ℝ} {v : ℕ} (hv : 1 ≤ v) :
    N * (N ^ (v - 1)) ^ 2 = N ^ (2 * v - 1) := by
  rw [← pow_mul, ← pow_succ']; congr 1; omega

/-- **First-stage proxy.** -/
theorem proxy₁_le {m : ℕ} (z N v r q CC Δ : ℕ) (f D : Fin m → ℕ) (hq : 1 ≤ q) (hv : 1 ≤ v)
    (hf : ∀ i, f i + 1 ≤ r) (hrv : ∀ i, r ≤ v + f i) (hD : ∀ i, D i ≤ Δ * N ^ (v - (r - f i))) :
    (z : ℝ) * N * (2 * ((∑ i, q ^ (f i + 1) * N ^ (r - (f i + 1)) * (CC * D i) : ℕ) : ℝ)) ^ 2 ≤
      4 * z * ((m * (q ^ r * CC * Δ) : ℕ) : ℝ) ^ 2 * (N : ℝ) ^ (2 * v - 1) := by
  have h := Lf_sum_le N v r q CC Δ f D hq hf hrv hD
  have h' : ((∑ i, q ^ (f i + 1) * N ^ (r - (f i + 1)) * (CC * D i) : ℕ) : ℝ) ≤
      ((m * (q ^ r * CC * Δ) : ℕ) : ℝ) * (N : ℝ) ^ (v - 1) := by exact_mod_cast h
  have h0 : (0 : ℝ) ≤ ((∑ i, q ^ (f i + 1) * N ^ (r - (f i + 1)) * (CC * D i) : ℕ) : ℝ) := by
    positivity
  calc (z : ℝ) * N * (2 * ((∑ i, q ^ (f i + 1) * N ^ (r - (f i + 1)) * (CC * D i) : ℕ) : ℝ)) ^ 2
      ≤ (z : ℝ) * N * (2 * (((m * (q ^ r * CC * Δ) : ℕ) : ℝ) * (N : ℝ) ^ (v - 1))) ^ 2 := by
        gcongr
    _ = 4 * z * ((m * (q ^ r * CC * Δ) : ℕ) : ℝ) ^ 2 * ((N : ℝ) * ((N : ℝ) ^ (v - 1)) ^ 2) := by
        ring
    _ = _ := by rw [pow_two_sub_one hv]

/-- **Second-stage proxy.** -/
theorem proxy₂_le {m : ℕ} {β : Type*} (C : Finset β) (S z N v r q CC Δ : ℕ) (f D : Fin m → ℕ)
    (hN : 1 ≤ N) (hv : 1 ≤ v) (hf : ∀ i, f i + 1 ≤ r) (hD : ∀ i, D i ≤ Δ * N ^ (v - (r - f i)))
    (hC : C.card ≤ Δ * N ^ v) :
    4 * (S : ℝ) * (((z * q ^ r + z) * ∑ i, CC * D i : ℕ) : ℝ) *
        (((2 * CC + 2) * (m * C.card * (z * q ^ r)) : ℕ) : ℝ) ≤
      4 * S * ((z * q ^ r + z) * (m * (CC * Δ)) : ℕ) * (((2 * CC + 2) * (m * Δ * (z * q ^ r)) : ℕ) : ℝ) *
        (N : ℝ) ^ (2 * v - 1) := by
  have h1 : ((z * q ^ r + z) * ∑ i, CC * D i : ℕ) ≤ (z * q ^ r + z) * (m * (CC * Δ)) * N ^ (v - 1) := by
    rw [mul_assoc]; exact Nat.mul_le_mul_left _ (D_sum_le N v r CC Δ f D hN hf hD)
  have h2 : ((2 * CC + 2) * (m * C.card * (z * q ^ r)) : ℕ) ≤
      (2 * CC + 2) * (m * Δ * (z * q ^ r)) * N ^ v := by
    calc (2 * CC + 2) * (m * C.card * (z * q ^ r)) ≤ (2 * CC + 2) * (m * (Δ * N ^ v) * (z * q ^ r)) := by
          gcongr
      _ = (2 * CC + 2) * (m * Δ * (z * q ^ r)) * N ^ v := by ring
  have h1' : ((((z * q ^ r + z) * ∑ i, CC * D i : ℕ)) : ℝ) ≤
      (((z * q ^ r + z) * (m * (CC * Δ)) : ℕ) : ℝ) * (N : ℝ) ^ (v - 1) := by exact_mod_cast h1
  have h2' : ((((2 * CC + 2) * (m * C.card * (z * q ^ r)) : ℕ)) : ℝ) ≤
      (((2 * CC + 2) * (m * Δ * (z * q ^ r)) : ℕ) : ℝ) * (N : ℝ) ^ v := by exact_mod_cast h2
  have hpow : (N : ℝ) ^ (v - 1) * (N : ℝ) ^ v = (N : ℝ) ^ (2 * v - 1) := by
    rw [← pow_add]; congr 1; omega
  calc 4 * (S : ℝ) * (((z * q ^ r + z) * ∑ i, CC * D i : ℕ) : ℝ) *
        (((2 * CC + 2) * (m * C.card * (z * q ^ r)) : ℕ) : ℝ)
      ≤ 4 * (S : ℝ) * ((((z * q ^ r + z) * (m * (CC * Δ)) : ℕ) : ℝ) * (N : ℝ) ^ (v - 1)) *
          ((((2 * CC + 2) * (m * Δ * (z * q ^ r)) : ℕ) : ℝ) * (N : ℝ) ^ v) := by
        gcongr
    _ = _ := by rw [← hpow]; ring

/-- **The exponential tail at scale `t = ε N^v`.** -/
theorem exp_tail_le {N ε c B : ℝ} {v : ℕ} (hv : 1 ≤ v) (hN : 0 < N) (hc : 0 < c) (hB0 : 0 < B)
    (hB : B ≤ c * N ^ (2 * v - 1)) :
    Real.exp (-((ε * N ^ v) ^ 2 / (2 * B))) ≤ Real.exp (-(ε ^ 2 * N / (2 * c))) := by
  rw [Real.exp_le_exp, neg_le_neg_iff]
  have hpow : (N ^ v) ^ 2 = N * N ^ (2 * v - 1) := by
    rw [← pow_mul, ← pow_succ']; congr 1; omega
  have hNp : 0 < N ^ (2 * v - 1) := by positivity
  rw [mul_pow, hpow, div_le_div_iff₀ (by positivity) (by positivity)]
  have : ε ^ 2 * N * (2 * B) ≤ ε ^ 2 * N * (2 * (c * N ^ (2 * v - 1))) := by
    gcongr
  nlinarith [sq_nonneg ε]

end DesignsII
