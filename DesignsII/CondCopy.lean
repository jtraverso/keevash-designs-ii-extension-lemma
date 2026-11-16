/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import DesignsII.CondCompat
public import DesignsII.ManyDeg

/-!
# The conditional probability that a copy passes the template tests (Lemma `e|E`)

Condition the colour coordinates `f_j` on their values at the positions of a set `U` of fixed
vertices (`fixedPos U`), leaving all other coordinates unconditioned. In the conditioned space the
copy `φ` (colour `j`) passes all tests with probability

  `#Y' (N - |U| - |I₁|)! / (N - |U|)! · z^{-|φ(Q)|} · ((q-r)!/q!)^{|φ(Q)|} · |𝒜|^{-1} · k/N_act`

(`probG_copyOK_cond`): the `f_j` factor is `card_cond_compat`, the others are unchanged
(`ratio_liftC_empty`). Together with `card_Yc_le`/`card_Yc_ge` this is Lemma `e|E`.
-/

@[expose] public section

namespace DesignsII

open Finset Equiv

variable {F K : Type*} [Field F] [Field K] [Algebra F K] [Fintype K] [DecidableEq K]

namespace TParams

variable {P : TParams}

/-- The conditioned positions: `U` (as positions of `[N]`) in every colour coordinate. -/
def fixedPos (U : Finset (Fin P.n)) : ∀ c : P.Coord, Finset (Fin (P.size c))
  | .inl _ => U.map (Fin.castLEEmb P.hnN)
  | .inr _ => ∅

/-! ### The unconditioned factors, as ratios -/

omit [Fintype K] [DecidableEq K] in
open Classical in
theorem ratio_T (M : Matrix (Fin P.q) (Fin P.r) F) (κ : Fin P.N ≃ K) (j : Fin P.z)
    (a₀ : Fin P.NA) (k : ℕ) (φ : Fin P.q → Fin P.n) (e : Finset (Fin P.n)) :
    ratio (copyEv M κ j a₀ k φ (.inr (.inl e))) = if e ∈ edges φ then 1 / (P.z : ℝ) else 1 := by
  unfold ratio
  by_cases he : e ∈ edges φ
  · rw [if_pos he]
    have h1 := (card_filter_congr' (copyEv M κ j a₀ k φ (.inr (.inl e)))
      (fun σ : Perm (Fin P.z) => σ ⟨0, P.hz⟩ = j) fun σ => ⟨fun h => h he, fun h _ => h⟩).trans
      (card_perm_val0 P.hz j)
    rw [h1]; exact factorial_ratio_pred P.hz
  · rw [if_neg he]
    exact @ratio_true P.z (copyEv M κ j a₀ k φ (.inr (.inl e))) (Classical.decPred _)
      fun σ hh => absurd hh he

omit [Fintype K] [DecidableEq K] in
open Classical in
theorem ratio_pi {M : Matrix (Fin P.q) (Fin P.r) F} (κ : Fin P.N ≃ K) (j : Fin P.z)
    (a₀ : Fin P.NA) (k : ℕ) {φ : Fin P.q → Fin P.n} (hφ : Function.Injective φ)
    (e : Finset (Fin P.n)) :
    ratio (copyEv M κ j a₀ k φ (.inr (.inr (.inl e)))) =
      if e ∈ edges φ then ((P.q - P.r).factorial : ℝ) / (P.q.factorial : ℝ) else 1 := by
  unfold ratio
  by_cases he : e ∈ edges φ
  · rw [if_pos he]
    have hc : e.card = P.r := (mem_powersetCard.1 he).2
    have hsub : e ⊆ univ.image φ := (mem_powersetCard.1 he).1
    have h1 := (card_filter_congr' (copyEv M κ j a₀ k φ (.inr (.inr (.inl e))))
      (fun σ : Perm (Fin P.q) => ∀ (hc : e.card = P.r) i (hi : φ i ∈ e),
        σ (Fin.castLE P.hrq ((e.orderIsoOfFin hc).symm ⟨φ i, hi⟩)) = i)
      fun σ => ⟨fun h => h he, fun h _ => h⟩).trans (card_pi_event hφ hc hsub)
    rw [h1]; rfl
  · rw [if_neg he]
    exact @ratio_true P.q (copyEv M κ j a₀ k φ (.inr (.inr (.inl e)))) (Classical.decPred _)
      fun σ hh => absurd hh he

omit [Fintype K] [DecidableEq K] in
open Classical in
theorem ratio_A (M : Matrix (Fin P.q) (Fin P.r) F) (κ : Fin P.N ≃ K) (j : Fin P.z)
    (a₀ : Fin P.NA) (k : ℕ) (φ φ' : Fin P.q → Fin P.n) :
    ratio (copyEv M κ j a₀ k φ (.inr (.inr (.inr (.inl φ'))))) =
      if φ' = φ then 1 / (P.NA : ℝ) else 1 := by
  unfold ratio
  by_cases h : φ' = φ
  · rw [if_pos h]
    subst h
    have h1 := (card_filter_congr' (copyEv M κ j a₀ k φ' (.inr (.inr (.inr (.inl φ')))))
      (fun σ : Perm (Fin P.NA) => σ ⟨0, P.hNA⟩ = a₀)
      fun σ => ⟨fun h => h rfl, fun h _ => h⟩).trans (card_perm_val0 P.hNA a₀)
    rw [h1]; exact factorial_ratio_pred P.hNA
  · rw [if_neg h]
    exact @ratio_true P.NA (copyEv M κ j a₀ k φ (.inr (.inr (.inr (.inl φ')))))
      (Classical.decPred _) fun σ hh => absurd hh h

omit [Fintype K] [DecidableEq K] in
open Classical in
theorem ratio_act (M : Matrix (Fin P.q) (Fin P.r) F) (κ : Fin P.N ≃ K) (j : Fin P.z)
    (a₀ : Fin P.NA) {k : ℕ} (hk : k ≤ P.Nact) (φ φ' : Fin P.q → Fin P.n) :
    ratio (copyEv M κ j a₀ k φ (.inr (.inr (.inr (.inr φ'))))) =
      if φ' = φ then (k : ℝ) / P.Nact else 1 := by
  unfold ratio
  by_cases h : φ' = φ
  · rw [if_pos h]
    subst h
    have h1 := (card_filter_congr' (copyEv M κ j a₀ k φ' (.inr (.inr (.inr (.inr φ')))))
      (fun σ : Perm (Fin P.Nact) => ((σ ⟨0, P.hNact⟩ : Fin P.Nact) : ℕ) < k)
      fun σ => ⟨fun h => h rfl, fun h _ => h⟩).trans (card_perm_val0_lt P.hNact k)
    rw [h1, min_eq_left hk]
    change (((k * (P.Nact - 1).factorial : ℕ) : ℝ)) / (P.Nact.factorial : ℝ) = _
    push_cast
    rw [mul_div_assoc, factorial_ratio_pred P.hNact]
    ring
  · rw [if_neg h]
    exact @ratio_true P.Nact (copyEv M κ j a₀ k φ (.inr (.inr (.inr (.inr φ')))))
      (Classical.decPred _) fun σ hh => absurd hh h

/-- Unconditioned coordinates keep their ratios (`ratio` form of `ratio_liftC_empty`). -/
theorem ratio_liftC_of_empty {m : ℕ} (S : Finset (Fin m)) (hS : S = ∅) (v : S ↪ Fin m)
    (E : Perm (Fin m) → Prop) :
    ratio (fun σ : Perm (Fin (m - S.card)) => E (liftC S v σ)) = ratio E := by
  subst hS
  unfold ratio
  exact ratio_liftC_empty v E

open Classical in
/-- **Lemma `e|E` (conditional probability of passing the tests).** In the space conditioned on the
values `v` of the colour coordinates at the fixed vertices `U`, the copy `φ` passes all tests of
colour `j` with probability `P_f^cond · z^{-|φ(Q)|} ((q-r)!/q!)^{|φ(Q)|} |𝒜|^{-1} k/N_act`, where
`P_f^cond` is the conditional probability of `f_j`-compatibility (`card_cond_compat`). -/
theorem probG_copyOK_cond (M : Matrix (Fin P.q) (Fin P.r) F) (κ : Fin P.N ≃ K) (j : Fin P.z)
    (a₀ : Fin P.NA) {k : ℕ} (hk : k ≤ P.Nact) {φ : Fin P.q → Fin P.n}
    (hφ : Function.Injective φ) (U : Finset (Fin P.n))
    (v : ∀ c, fixedPos U c ↪ Fin (P.size c)) :
    probG (a := fun c => P.size c - (fixedPos U c).card)
        (fun τ => CopyOK M κ j a₀ k φ (liftPi (fixedPos U) v τ)) =
      ratio (fun σ : Perm (Fin (P.size (.inl j) - (fixedPos U (.inl j)).card)) =>
          ∃ y, ∀ i, κ (liftC (fixedPos U (.inl j)) (v (.inl j)) σ (Fin.castLE P.hnN (φ i))) =
            mvec M y i) *
        (1 / (P.z : ℝ)) ^ (edges φ).card *
        (((P.q - P.r).factorial : ℝ) / (P.q.factorial : ℝ)) ^ (edges φ).card *
        (1 / (P.NA : ℝ)) * ((k : ℝ) / P.Nact) := by
  have hiff : (fun τ => CopyOK M κ j a₀ k φ (liftPi (fixedPos U) v τ)) =
      fun τ => ∀ c, copyEv M κ j a₀ k φ c (liftC (fixedPos U c) (v c) (τ c)) := by
    funext τ
    exact propext (copyOK_iff M κ j a₀ k φ _)
  rw [hiff, probG_pi (fun c σ => copyEv M κ j a₀ k φ c (liftC (fixedPos U c) (v c) σ)),
    Fintype.prod_sum_type, Fintype.prod_sum_type, Fintype.prod_sum_type,
    Fintype.prod_sum_type]
  have hf : ∀ j' : Fin P.z, ratio (fun σ : Perm (Fin (P.size (.inl j') - (fixedPos U (.inl j')).card)) =>
      copyEv M κ j a₀ k φ (.inl j') (liftC (fixedPos U (.inl j')) (v (.inl j')) σ)) =
      if j' = j then ratio (fun σ : Perm (Fin (P.size (.inl j) - (fixedPos U (.inl j)).card)) =>
          ∃ y, ∀ i, κ (liftC (fixedPos U (.inl j)) (v (.inl j)) σ (Fin.castLE P.hnN (φ i))) =
            mvec M y i) else 1 := by
    intro j'
    by_cases h : j' = j
    · rw [if_pos h]; subst h
      exact ratio_congr fun σ => ⟨fun h => h rfl, fun h _ => h⟩
    · rw [if_neg h]; exact ratio_true' _ fun σ hh => absurd hh h
  have hT : ∀ e : Finset (Fin P.n), ratio (fun σ => copyEv M κ j a₀ k φ (.inr (.inl e))
      (liftC (fixedPos U (.inr (.inl e))) (v (.inr (.inl e))) σ)) =
      if e ∈ edges φ then 1 / (P.z : ℝ) else 1 := fun e => by
    rw [ratio_liftC_of_empty (fixedPos U (.inr (.inl e))) rfl, ratio_T]
  have hpi : ∀ e : Finset (Fin P.n), ratio (fun σ => copyEv M κ j a₀ k φ (.inr (.inr (.inl e)))
      (liftC (fixedPos U (.inr (.inr (.inl e)))) (v (.inr (.inr (.inl e)))) σ)) =
      if e ∈ edges φ then ((P.q - P.r).factorial : ℝ) / (P.q.factorial : ℝ) else 1 := fun e => by
    rw [ratio_liftC_of_empty (fixedPos U (.inr (.inr (.inl e)))) rfl, ratio_pi κ j a₀ k hφ]
  have hA : ∀ φ' : Fin P.q → Fin P.n,
      ratio (fun σ => copyEv M κ j a₀ k φ (.inr (.inr (.inr (.inl φ'))))
        (liftC (fixedPos U (.inr (.inr (.inr (.inl φ'))))) (v (.inr (.inr (.inr (.inl φ'))))) σ)) =
      if φ' = φ then 1 / (P.NA : ℝ) else 1 := fun φ' => by
    rw [ratio_liftC_of_empty (fixedPos U (.inr (.inr (.inr (.inl φ'))))) rfl, ratio_A]
  have hact : ∀ φ' : Fin P.q → Fin P.n,
      ratio (fun σ => copyEv M κ j a₀ k φ (.inr (.inr (.inr (.inr φ'))))
        (liftC (fixedPos U (.inr (.inr (.inr (.inr φ'))))) (v (.inr (.inr (.inr (.inr φ'))))) σ)) =
      if φ' = φ then (k : ℝ) / P.Nact else 1 := fun φ' => by
    rw [ratio_liftC_of_empty (fixedPos U (.inr (.inr (.inr (.inr φ'))))) rfl,
      ratio_act M κ j a₀ hk]
  rw [Fintype.prod_congr _ _ hf, Fintype.prod_congr _ _ hT, Fintype.prod_congr _ _ hpi,
    Fintype.prod_congr _ _ hA, Fintype.prod_congr _ _ hact]
  rw [prod_ite_eq' univ j, prod_ite_eq' univ φ, prod_ite_eq' univ φ, prod_ite_mem, prod_ite_mem,
    univ_inter, prod_const, prod_const]
  simp only [mem_univ, if_true]
  ring

open Classical in
/-- The colour factor in closed form: `#Y' · (N - |U| - |I₁|)! / (N - |U|)!`. -/
theorem ratio_compat_cond {M : Matrix (Fin P.q) (Fin P.r) F} (hM : IsGeneric M) (κ : Fin P.N ≃ K)
    (j : Fin P.z) {φ : Fin P.q → Fin P.n} (hφ : Function.Injective φ) (U : Finset (Fin P.n))
    (v : fixedPos U (.inl j) ↪ Fin (P.size (.inl j))) :
    ratio (fun σ : Perm (Fin (P.size (.inl j) - (fixedPos U (.inl j)).card)) =>
        ∃ y, ∀ i, κ (liftC (fixedPos U (.inl j)) v σ (Fin.castLE P.hnN (φ i))) = mvec M y i) =
      (((Yc (fixedPos U (.inl j)) v κ M ⟨fun i => Fin.castLE P.hnN (φ i), fun i i' h =>
          hφ (Fin.castLE_injective P.hnN h)⟩).card *
        (P.N - (fixedPos U (.inl j)).card -
          Fintype.card {i // Fin.castLE P.hnN (φ i) ∉ fixedPos U (.inl j)}).factorial : ℕ) : ℝ) /
        ((P.N - (fixedPos U (.inl j)).card).factorial : ℝ) := by
  classical
  unfold ratio
  congr 1
  have h := card_cond_compat (fixedPos U (.inl j)) v κ
    ⟨fun i => Fin.castLE P.hnN (φ i), fun i i' h => hφ (Fin.castLE_injective P.hnN h)⟩ hM P.hrq
  norm_cast
  convert h using 4
  · rfl
  · exact Fintype.card_congr (Equiv.refl _)

end TParams

end DesignsII
