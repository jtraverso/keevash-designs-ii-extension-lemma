/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import DesignsII.ExtStar

/-!
# Size of the conditional passing probability

`passLB_ge`: if a copy meets the fixed set `U` in `s ≤ r - 1` vertices and
`N = |K| ≥ 2(q² + q|U|)`, `|U| + q ≤ N`, then

  `passLB ≥ 1/(2 N^{q-r}) · z^{-Q} ((q-r)!/q!)^Q |𝒜|^{-1} k/N_act`,  `Q = C(q,r)`,

the order `ρ`-type bound of Lemma `e|E` (with `k/N_act ≈ y_φ ω n^{q-r}` this is `≈ z^{-Q} ρ`).
-/

@[expose] public section

namespace DesignsII

open Finset

variable {F K : Type*} [Field F] [Field K] [Algebra F K] [Fintype K] [DecidableEq K]

namespace TParams

variable {P : TParams}

omit [Field F] [Field K] [Algebra F K] [Fintype K] [DecidableEq K] in
/-- An injective copy has `C(q,r)` edges. -/
theorem card_edges {φ : Fin P.q → Fin P.n} (hφ : Function.Injective φ) :
    (edges φ).card = P.q.choose P.r := by
  rw [edges, card_powersetCard, card_image_of_injective _ hφ, card_univ, Fintype.card_fin]

/-- Real arithmetic core: `(N^a - c N^{a-1}) (N-u-w)!/(N-u)! ≥ 1/(2 N^{w-a})`. -/
theorem core_ge (N u w a c : ℕ) (ha : 1 ≤ a) (haw : a ≤ w) (hc : 2 * c ≤ N)
    (huw : u + w ≤ N) :
    1 / (2 * (N : ℝ) ^ (w - a)) ≤
      (((N ^ a : ℕ) : ℝ) - ((c * N ^ (a - 1) : ℕ) : ℝ)) *
        (((N - u - w).factorial : ℕ) : ℝ) / ((N - u).factorial : ℝ) := by
  have hN : 0 < N := by omega
  have hX : (0 : ℝ) < N := by exact_mod_cast hN
  -- the first factor
  have h1 : (N : ℝ) ^ a / 2 ≤ ((N ^ a : ℕ) : ℝ) - ((c * N ^ (a - 1) : ℕ) : ℝ) := by
    push_cast
    have hpow : (N : ℝ) ^ a = N * (N : ℝ) ^ (a - 1) := by
      rw [← pow_succ']; congr 1; omega
    have hc' : (c : ℝ) ≤ N / 2 := by
      rw [le_div_iff₀ (by norm_num)]; exact_mod_cast (by omega : c * 2 ≤ N)
    rw [hpow]
    nlinarith [pow_pos hX (a - 1)]
  -- the factorial ratio
  have hfac : ((N - u).factorial : ℝ) =
      ((N - u - w).factorial : ℝ) * ((N - u).descFactorial w : ℝ) := by
    exact_mod_cast (Nat.factorial_mul_descFactorial (by omega : w ≤ N - u)).symm
  have hdesc : ((N - u).descFactorial w : ℝ) ≤ (N : ℝ) ^ w := by
    exact_mod_cast (Nat.descFactorial_le_pow _ _).trans (Nat.pow_le_pow_left (Nat.sub_le _ _) _)
  have hdpos : (0 : ℝ) < ((N - u).descFactorial w : ℝ) := by
    exact_mod_cast Nat.descFactorial_pos.2 (by omega)
  have hfpos : (0 : ℝ) < ((N - u - w).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
  have h2 : ((((N - u - w).factorial : ℕ) : ℝ)) / ((N - u).factorial : ℝ) =
      1 / ((N - u).descFactorial w : ℝ) := by
    rw [hfac]; field_simp
  rw [mul_div_assoc, h2]
  have hsplit : (N : ℝ) ^ w = (N : ℝ) ^ (w - a) * (N : ℝ) ^ a := by
    rw [← pow_add]; congr 1; omega
  calc 1 / (2 * (N : ℝ) ^ (w - a)) = (N : ℝ) ^ a / 2 * (1 / (N : ℝ) ^ w) := by
        rw [hsplit]; field_simp
    _ ≤ (((N ^ a : ℕ) : ℝ) - ((c * N ^ (a - 1) : ℕ) : ℝ)) * (1 / ((N - u).descFactorial w : ℝ)) := by
        refine mul_le_mul h1 ?_ (by positivity) ((div_nonneg (by positivity) (by norm_num)).trans h1)
        exact one_div_le_one_div_of_le hdpos hdesc

open Classical in
/-- **The conditional passing probability is of order `N^{r-q}`.** -/
theorem passLB_ge (hK : Fintype.card K = P.N) (U : Finset (Fin P.n)) (j : Fin P.z)
    {φ : Fin P.q → Fin P.n} (hφ : Function.Injective φ) (k : ℕ)
    (hs : (univ.filter fun i => φ i ∈ U).card + 1 ≤ P.r)
    (hN : 2 * (P.q ^ 2 + P.q * U.card) ≤ P.N) (hUq : U.card + P.q ≤ P.N) :
    1 / (2 * (P.N : ℝ) ^ (P.q - P.r)) * (1 / (P.z : ℝ)) ^ P.q.choose P.r *
        (((P.q - P.r).factorial : ℝ) / (P.q.factorial : ℝ)) ^ P.q.choose P.r *
        (1 / (P.NA : ℝ)) * ((k : ℝ) / P.Nact) ≤
      passLB (K := K) U j hφ k := by
  have hI := I₀_fixedPos (P := P) U j hφ
  set s := (I₀ (fixedPos U (.inl j)) (wEmb hφ)).card with hsdef
  have hs' : s + 1 ≤ P.r := by rw [hsdef, hI]; exact hs
  have hS : (fixedPos U (.inl j)).card = U.card := card_map _
  have hnew : Fintype.card {i // wEmb hφ i ∉ fixedPos U (.inl j)} = P.q - s := by
    rw [Fintype.card_subtype]
    have h := card_filter_add_card_filter_not (s := (univ : Finset (Fin P.q)))
      (fun i => wEmb hφ i ∈ fixedPos U (.inl j))
    rw [card_univ, Fintype.card_fin] at h
    have h' : (univ.filter fun i => wEmb hφ i ∈ fixedPos U (.inl j)).card = s := by
      rw [hsdef]; unfold I₀; congr 1; ext; simp only [mem_filter, mem_univ, true_and]; exact Iff.rfl
    have h'' : (univ.filter fun i => wEmb hφ i ∉ fixedPos U (.inl j)).card =
        (univ.filter fun i => ¬ wEmb hφ i ∈ fixedPos U (.inl j)).card := by congr 1
    omega
  have hrq := P.hrq
  have hcore := core_ge P.N U.card (P.q - s) (P.r - s) (P.q ^ 2 + P.q * U.card)
    (by omega) (by omega) hN (by omega)
  rw [show P.q - s - (P.r - s) = P.q - P.r by omega] at hcore
  have hrest : (0 : ℝ) ≤ (1 / (P.z : ℝ)) ^ P.q.choose P.r *
      (((P.q - P.r).factorial : ℝ) / (P.q.factorial : ℝ)) ^ P.q.choose P.r *
      (1 / (P.NA : ℝ)) * ((k : ℝ) / P.Nact) := by positivity
  have := mul_le_mul_of_nonneg_right hcore hrest
  unfold passLB
  rw [hK, hS, hnew, card_edges hφ, ← hsdef]
  convert this using 1 <;> ring

end TParams

end DesignsII
