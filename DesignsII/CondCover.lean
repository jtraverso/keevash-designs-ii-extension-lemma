/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import DesignsII.CondCopy

/-!
# Covering prescribed edges in the conditioned template space (expectation of `ext*`)

In the space conditioned on the values `v` at the positions `S` (any conditioning, e.g.
`fixedPos U`), the results of `Joint.lean` hold verbatim for the events pulled back by `liftPi`:

* `probG_copyOK_joint_cond`: copies with distinct colours, distinct maps and disjoint edge sets
  pass their tests independently;
* `probG_cover_colors_ge_cond`: the probability that every edge `e_i` is covered by a passing copy
  is at least `∑_{j injective} ∑_{(φ_i) ∈ T} ∏_i P(φ_i passes with colour j_i | v)`; the colourings
  `j` may be restricted to any set (e.g. injections into the non-degenerate colours).
-/

@[expose] public section

namespace DesignsII

open Finset Equiv

variable {F K : Type*} [Field F] [Field K] [Algebra F K] [Fintype K] [DecidableEq K]

namespace TParams

variable {P : TParams} (S : ∀ c : P.Coord, Finset (Fin (P.size c)))
  (v : ∀ c, S c ↪ Fin (P.size c))

omit [Fintype K] [DecidableEq K] in
/-- **Joint probability in the conditioned space.** -/
theorem probG_copyOK_joint_cond {m : ℕ} (M : Matrix (Fin P.q) (Fin P.r) F) (κ : Fin P.N ≃ K)
    (j : Fin m → Fin P.z) (a₀ : Fin m → Fin P.NA) (k : Fin m → ℕ)
    (φ : Fin m → Fin P.q → Fin P.n) (hj : Function.Injective j) (hφ : Function.Injective φ)
    (hdisj : ∀ i i', i ≠ i' → Disjoint (edges (φ i)) (edges (φ i'))) :
    probG (a := fun c => P.size c - (S c).card)
        (fun τ => ∀ i, CopyOK M κ (j i) (a₀ i) (k i) (φ i) (liftPi S v τ)) =
      ∏ i, probG (a := fun c => P.size c - (S c).card)
        (fun τ => CopyOK M κ (j i) (a₀ i) (k i) (φ i) (liftPi S v τ)) := by
  have hiff : ∀ i, (fun τ => CopyOK M κ (j i) (a₀ i) (k i) (φ i) (liftPi S v τ)) =
      fun τ => ∀ c, copyEv M κ (j i) (a₀ i) (k i) (φ i) c (liftC (S c) (v c) (τ c)) :=
    fun i => funext fun τ => propext (copyOK_iff _ _ _ _ _ _ _)
  have hall : (fun τ => ∀ i, CopyOK M κ (j i) (a₀ i) (k i) (φ i) (liftPi S v τ)) =
      fun τ => ∀ i c, copyEv M κ (j i) (a₀ i) (k i) (φ i) c (liftC (S c) (v c) (τ c)) :=
    funext fun τ => propext (forall_congr' fun i => copyOK_iff _ _ _ _ _ _ _)
  rw [hall]
  simp_rw [hiff]
  refine probG_forall_indep
    (fun i c σ => copyEv M κ (j i) (a₀ i) (k i) (φ i) c (liftC (S c) (v c) σ))
    fun c i i' hii => ?_
  rcases c with j' | e | e | φ' | φ'
  · by_cases h : j i = j'
    · right; intro σ hh; exact absurd (hj (h.trans hh)) hii
    · left; intro σ hh; exact absurd hh.symm h
  · by_cases h : e ∈ edges (φ i)
    · right; intro σ hh; exact absurd hh (disjoint_left.1 (hdisj i i' hii) h)
    · left; intro σ hh; exact absurd hh h
  · by_cases h : e ∈ edges (φ i)
    · right; intro σ hh; exact absurd hh (disjoint_left.1 (hdisj i i' hii) h)
    · left; intro σ hh; exact absurd hh h
  · by_cases h : φ i = φ'
    · right; intro σ hh; exact absurd (hφ (h.trans hh)) hii
    · left; intro σ hh; exact absurd hh.symm h
  · by_cases h : φ i = φ'
    · right; intro σ hh; exact absurd (hφ (h.trans hh)) hii
    · left; intro σ hh; exact absurd hh.symm h

omit [Fintype K] [DecidableEq K] in
/-- **Cover lower bound in the conditioned space**, over any set `Jset` of injective colourings. -/
theorem probG_cover_colors_ge_cond {m : ℕ} {M : Matrix (Fin P.q) (Fin P.r) F} (hM : IsGeneric M)
    (κ : Fin P.N ≃ K) (a₀ : (Fin P.q → Fin P.n) → Fin P.NA) (k : (Fin P.q → Fin P.n) → ℕ)
    (e : Fin m → Finset (Fin P.n)) (Q : Fin m → (Fin P.q → Fin P.n) → Prop)
    (T : Finset (Fin m → Fin P.q → Fin P.n))
    (hT : ∀ φ ∈ T, (∀ i, Function.Injective (φ i)) ∧ (∀ i, e i ∈ edges (φ i) ∧ Q i (φ i)) ∧
      Function.Injective φ ∧ ∀ i i', i ≠ i' → Disjoint (edges (φ i)) (edges (φ i')))
    (Jset : Finset (Fin m → Fin P.z)) (hJ : ∀ j ∈ Jset, Function.Injective j) :
    ∑ j ∈ Jset, ∑ φ ∈ T, ∏ i, probG (a := fun c => P.size c - (S c).card)
        (fun τ => CopyOK M κ (j i) (a₀ (φ i)) (k (φ i)) (φ i) (liftPi S v τ)) ≤
      probG (a := fun c => P.size c - (S c).card) (fun τ => ∀ i, ∃ ψ : Fin P.q → Fin P.n,
        Function.Injective ψ ∧ (e i ∈ edges ψ ∧ Q i ψ) ∧ ∃ j, CopyOK M κ j (a₀ ψ) (k ψ) ψ (liftPi S v τ)) := by
  classical
  calc _ = ∑ j ∈ Jset, probG (a := fun c => P.size c - (S c).card)
        (fun τ => ∃ φ ∈ T, ∀ i, CopyOK M κ (j i) (a₀ (φ i)) (k (φ i)) (φ i) (liftPi S v τ)) := by
        refine sum_congr rfl fun j hj => ?_
        rw [probG_exists_disjoint T _ fun φ hφ φ' hφ' hne τ h1 h2 => hne ?_]
        · refine sum_congr rfl fun φ hφ => ?_
          obtain ⟨-, -, hinj, hdisj⟩ := hT φ hφ
          exact (probG_copyOK_joint_cond S v M κ j (fun i => a₀ (φ i)) (fun i => k (φ i)) φ
            (hJ j hj) hinj hdisj).symm
        · funext i
          exact copyOK_unique hM κ ((hT φ hφ).1 i) (h1 i) (h2 i) ((hT φ hφ).2.1 i).1
            ((hT φ' hφ').2.1 i).1
    _ = probG (a := fun c => P.size c - (S c).card) (fun τ => ∃ j ∈ Jset, ∃ φ ∈ T,
          ∀ i, CopyOK M κ (j i) (a₀ (φ i)) (k (φ i)) (φ i) (liftPi S v τ)) := by
        refine (probG_exists_disjoint Jset _ fun j _ j' _ hne τ h1 h2 => hne ?_).symm
        obtain ⟨φ, hφ, h1⟩ := h1
        obtain ⟨φ', hφ', h2⟩ := h2
        funext i
        exact (copyOK_T (h1 i) ((hT φ hφ).2.1 i).1).symm.trans (copyOK_T (h2 i) ((hT φ' hφ').2.1 i).1)
    _ ≤ _ := probG_mono fun τ ⟨j, _, φ, hφ, h⟩ i =>
        ⟨φ i, (hT φ hφ).1 i, (hT φ hφ).2.1 i, j i, h i⟩

end TParams


namespace TParams

variable {P : TParams} (S : ∀ c : P.Coord, Finset (Fin (P.size c)))
  (v : ∀ c, S c ↪ Fin (P.size c))

omit [Fintype K] [DecidableEq K] in
open Classical in
/-- **Expectation of the covering count (`ext*`, first moment).** If every candidate copy passes
with conditional probability at least `p`, the conditional mean of
`X = #{b ∈ C : every edge of b is covered by a passing copy}` is at least
`∑_b #J_b · #T_b · p^m`. -/
theorem meanG_cover_ge {β : Type*} {m : ℕ} {M : Matrix (Fin P.q) (Fin P.r) F} (hM : IsGeneric M)
    (κ : Fin P.N ≃ K) (a₀ : (Fin P.q → Fin P.n) → Fin P.NA) (k : (Fin P.q → Fin P.n) → ℕ)
    (C : Finset β) (e : β → Fin m → Finset (Fin P.n))
    (Q : β → Fin m → (Fin P.q → Fin P.n) → Prop)
    (T : β → Finset (Fin m → Fin P.q → Fin P.n))
    (hT : ∀ b ∈ C, ∀ φ ∈ T b, (∀ i, Function.Injective (φ i)) ∧ (∀ i, e b i ∈ edges (φ i) ∧ Q b i (φ i)) ∧
      Function.Injective φ ∧ ∀ i i', i ≠ i' → Disjoint (edges (φ i)) (edges (φ i')))
    (Jset : β → Finset (Fin m → Fin P.z)) (hJ : ∀ b ∈ C, ∀ j ∈ Jset b, Function.Injective j)
    {p : ℝ} (hp0 : 0 ≤ p)
    (hp : ∀ b ∈ C, ∀ j ∈ Jset b, ∀ φ ∈ T b, ∀ i, p ≤ probG (a := fun c => P.size c - (S c).card)
      (fun τ => CopyOK M κ (j i) (a₀ (φ i)) (k (φ i)) (φ i) (liftPi S v τ))) :
    ∑ b ∈ C, ((Jset b).card : ℝ) * (T b).card * p ^ m ≤
      meanG (a := fun c => P.size c - (S c).card) (countVar C fun b τ => ∀ i,
        ∃ ψ : Fin P.q → Fin P.n, Function.Injective ψ ∧ (e b i ∈ edges ψ ∧ Q b i ψ) ∧
          ∃ j, CopyOK M κ j (a₀ ψ) (k ψ) ψ (liftPi S v τ)) := by
  rw [meanG_count]
  refine sum_le_sum fun b hb => ?_
  refine le_trans ?_ (probG_cover_colors_ge_cond S v hM κ a₀ k (e b) (Q b) (T b) (hT b hb) (Jset b)
    (hJ b hb))
  calc ((Jset b).card : ℝ) * (T b).card * p ^ m
      = ∑ _j ∈ Jset b, ∑ _φ ∈ T b, ∏ _i : Fin m, p := by
        rw [sum_const, sum_const, prod_const, card_univ, Fintype.card_fin, nsmul_eq_mul,
          nsmul_eq_mul]
        ring
    _ ≤ _ := sum_le_sum fun j hj => sum_le_sum fun φ hφ =>
        Finset.prod_le_prod₀ (fun _ _ => hp0) fun i _ => hp b hb j hj φ hφ i

end TParams

end DesignsII
