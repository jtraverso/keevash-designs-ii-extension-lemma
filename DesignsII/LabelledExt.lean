/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import DesignsII.ExtDefs
public import DesignsII.ExtStar
public import DesignsII.AtomEq

/-!
# Lemma `ext*` in the labelled framework

The template `M*(ω)` is the set of pairs `(a₀ φ, φ)` of copies passing the template tests (for
some colour). Copies that are not `Φ`-embeddings of `A_{a₀ φ}` are never activated (`k φ = 0`),
so `M*(ω)` consists of embeddings and `leGamma_onOrbit_boundary` applies.

For a configuration `b` with labelled maps `ψ b i ∈ Φ_r` (the maps `φ⁺ψ'`, `ψ' ∈ H'`), the
witness predicate `atomQ` says that the covering copy `φ` has, at the orbit of `ψ b i`, the atom
`γ(ψ b i)` (`moleculeP S A (ψ b i)`). Then

* `leGamma_of_coverEv`: covering with `atomQ` gives `γ(ψ b i) ≤_γ ∂^γ M*(ω)` for every `i`, i.e.
  `φ⁺ ∈ X_{E,H'}(Φ, γ[∂^γ M*]^A)` (`gammaG`);
* `ext_star_labelled`: the lower tail of `ext_star` for the labelled count
  `#{b ∈ C : ∀ i, γ(ψ b i) ≤_γ ∂^γ M*(ω)}`.
-/

@[expose] public section

namespace DesignsII

open Finset

variable {F K : Type*} [Field F] [Field K] [Algebra F K] [Fintype K] [DecidableEq K]

namespace TParams

variable {P : TParams} {D r : ℕ}

/-- The witness predicate: the covering copy has the atom `γ(ψ)` at the orbit of `ψ`. -/
noncomputable def atomQ (S : VSystem (Fin P.q) (Fin P.NA) (Fin D → ℤ) r)
    (Sg : Subgroup (Equiv.Perm (Fin P.q))) (A : Fin P.NA) (a₀ : (Fin P.q → Fin P.n) → Fin P.NA)
    {β : Type*} {m : ℕ} (ψ : β → Fin m → (Fin P.q → Option (Fin P.n))) :
    β → Fin m → (Fin P.q → Fin P.n) → Prop :=
  fun b i φ => moleculeP S A (ψ b i) = onOrbit Sg (S.molecule (a₀ φ) φ) (ψ b i) (domF (ψ b i))

omit [Fintype K] [DecidableEq K] in
open Classical in
theorem mem_templateSet_embedding (M : Matrix (Fin P.q) (Fin P.r) F) (κ : Fin P.N ≃ K)
    (a₀ : (Fin P.q → Fin P.n) → Fin P.NA) (k : (Fin P.q → Fin P.n) → ℕ)
    (S : VSystem (Fin P.q) (Fin P.NA) (Fin D → ℤ) r) (Φ : RSystem (Fin P.q) (Fin P.n))
    (hk0 : ∀ φ, ¬ IsEmbedding (S.A (a₀ φ)) Φ φ → k φ = 0) (ω : P.Ω) :
    ∀ p ∈ templateSet M κ a₀ k ω, IsEmbedding (S.A p.1) Φ p.2 := by
  intro p hp
  obtain ⟨h1, j, hok⟩ := (mem_filter.1 hp).2
  by_contra hn
  rw [h1] at hn
  have := hok.2.1
  unfold Active at this
  rw [hk0 _ hn] at this
  exact Nat.not_lt_zero _ this

omit [Fintype K] [DecidableEq K] in
/-- **Covering with the atom predicate gives the labelled condition.** -/
theorem leGamma_of_coverEv (M : Matrix (Fin P.q) (Fin P.r) F) (κ : Fin P.N ≃ K)
    (a₀ : (Fin P.q → Fin P.n) → Fin P.NA) (k : (Fin P.q → Fin P.n) → ℕ)
    (S : VSystem (Fin P.q) (Fin P.NA) (Fin D → ℤ) r) (Sg : Subgroup (Equiv.Perm (Fin P.q)))
    (Φ : RSystem (Fin P.q) (Fin P.n)) (hΦ : IsAdapted Φ Sg)
    (hk0 : ∀ φ, ¬ IsEmbedding (S.A (a₀ φ)) Φ φ → k φ = 0) (A : Fin P.NA) {β : Type*} {m : ℕ}
    (e : β → Fin m → Finset (Fin P.n)) (ψ : β → Fin m → (Fin P.q → Option (Fin P.n)))
    (ω : P.Ω) (b : β) (h : CoverEv M κ a₀ k (e b) (atomQ S Sg A a₀ ψ b) ω) (i : Fin m) :
    LeGamma S Sg Φ (moleculeP S A (ψ b i)) (S.boundary (templateSet M κ a₀ k ω)) := by
  classical
  obtain ⟨φ, -, ⟨-, hQ⟩, j, hok⟩ := h i
  have hmem : (a₀ φ, φ) ∈ templateSet M κ a₀ k ω :=
    mem_filter.2 ⟨mem_univ _, rfl, j, hok⟩
  have := leGamma_onOrbit_boundary Sg S Φ hΦ _
    (mem_templateSet_embedding M κ a₀ k S Φ hk0 ω) hmem (ψ b i)
  simp only [atomQ] at hQ
  rw [hQ]
  exact this

open Classical in
/-- The plain covering count is at most the labelled count. -/
theorem countVar_le_labelled (M : Matrix (Fin P.q) (Fin P.r) F) (κ : Fin P.N ≃ K)
    (a₀ : (Fin P.q → Fin P.n) → Fin P.NA) (k : (Fin P.q → Fin P.n) → ℕ)
    (S : VSystem (Fin P.q) (Fin P.NA) (Fin D → ℤ) r) (Sg : Subgroup (Equiv.Perm (Fin P.q)))
    (Φ : RSystem (Fin P.q) (Fin P.n)) (hΦ : IsAdapted Φ Sg)
    (hk0 : ∀ φ, ¬ IsEmbedding (S.A (a₀ φ)) Φ φ → k φ = 0) (A : Fin P.NA) {β : Type*} {m : ℕ}
    (C : Finset β) (e : β → Fin m → Finset (Fin P.n))
    (ψ : β → Fin m → (Fin P.q → Option (Fin P.n))) (ω : P.Ω) :
    countVar C (fun b ω => CoverEv M κ a₀ k (e b) (atomQ S Sg A a₀ ψ b) ω) ω ≤
      ((C.filter fun b => ∀ i, LeGamma S Sg Φ (moleculeP S A (ψ b i))
        (S.boundary (templateSet M κ a₀ k ω))).card : ℝ) := by
  unfold countVar
  exact_mod_cast card_le_card fun b hb => mem_filter.2 ⟨(mem_filter.1 hb).1,
    leGamma_of_coverEv M κ a₀ k S Sg Φ hΦ hk0 A e ψ ω b (mem_filter.1 hb).2⟩

open Classical in
/-- **Lemma `ext*` (labelled form).** With the hypotheses of `ext_star` for the atom predicate,
the number of configurations `b ∈ C` with `γ(ψ b i) ≤_γ ∂^γ M*` for all `i` (i.e. the
`φ⁺ ∈ X_{E,H'}(Φ, γ[∂^γ M*]^A)`) is at least `∑_b (z+1-kd)_m #T_b p^m - t₁ - t₂` except with
probability `C(z,kd) p_deg^kd + 2e^{-t₁²/2B₁} + 2e^{-t₂²/2B₂}`. -/
theorem ext_star_labelled {M : Matrix (Fin P.q) (Fin P.r) F} (hM : IsGeneric M)
    (hrows : DistinctRows M) (κ : Fin P.N ≃ K) (a₀ : (Fin P.q → Fin P.n) → Fin P.NA)
    (k : (Fin P.q → Fin P.n) → ℕ) (hk : ∀ ψ, k ψ ≤ P.Nact)
    (S : VSystem (Fin P.q) (Fin P.NA) (Fin D → ℤ) r) (Sg : Subgroup (Equiv.Perm (Fin P.q)))
    (Φ : RSystem (Fin P.q) (Fin P.n)) (hΦ : IsAdapted Φ Sg)
    (hk0 : ∀ φ, ¬ IsEmbedding (S.A (a₀ φ)) Φ φ → k φ = 0) (A : Fin P.NA)
    {s : ℕ} (u : Fin s ↪ Fin P.n)
    (kd : ℕ) {β : Type*} {m : ℕ} (C : Finset β) (e : β → Fin m → Finset (Fin P.n))
    (ψ : β → Fin m → (Fin P.q → Option (Fin P.n)))
    (Fx : Fin m → Finset (Fin P.n)) (hFU : ∀ i, Fx i ⊆ univ.map u)
    (hF : ∀ b ∈ C, ∀ i, Fx i ⊆ e b i) (hFr : ∀ i, (Fx i).card + 1 ≤ P.r) (D : Fin m → ℕ)
    (hD : ∀ i (e' : Finset (Fin P.n)), (C.filter fun b => e b i = e').card ≤ D i)
    (T : β → Finset (Fin m → Fin P.q → Fin P.n))
    (hT : ∀ b ∈ C, ∀ φ ∈ T b, (∀ i, Function.Injective (φ i)) ∧
      (∀ i, e b i ∈ edges (φ i) ∧ atomQ S Sg A a₀ ψ b i (φ i)) ∧
      Function.Injective φ ∧ ∀ i i', i ≠ i' → Disjoint (edges (φ i)) (edges (φ i')))
    (hTU : ∀ b ∈ C, ∀ φ ∈ T b, ∀ i,
      (univ.filter fun l => φ i l ∈ univ.map u).card + 1 ≤ P.r)
    {p : ℝ} (hp0 : 0 ≤ p)
    (hp : ∀ b ∈ C, ∀ φ ∈ T b, ∀ i (j : Fin P.z) (hφ : Function.Injective (φ i)),
      p ≤ passLB (K := K) (univ.map u) j hφ (k (φ i)))
    {Smax : ℕ} (hSmax : ∀ c : P.Coord, c.isLeft = false → P.size c ≤ Smax)
    {B₁ B₂ t₁ t₂ : ℝ}
    (hB₁ : (P.z : ℝ) * P.N * (2 * ((∑ i, P.q ^ ((Fx i).card + 1) *
      Fintype.card K ^ (P.r - ((Fx i).card + 1)) * (P.q.choose P.r * D i) : ℕ) : ℝ)) ^ 2 ≤ B₁)
    (hB₂ : 4 * (Smax : ℝ) * (((P.z * P.q ^ P.r + P.z) * ∑ i, P.q.choose P.r * D i : ℕ) : ℝ) *
      (((2 * P.q.choose P.r + 2) * (m * C.card * (P.z * P.q ^ P.r)) : ℕ) : ℝ) ≤ B₂)
    (hB₁0 : 0 < B₁) (hB₂0 : 0 < B₂) (ht₁ : 0 < t₁) (ht₂ : 0 < t₂) :
    probG (a := P.size) (fun ω =>
        ((C.filter fun b => ∀ i, LeGamma S Sg Φ (moleculeP S A (ψ b i))
          (S.boundary (templateSet M κ a₀ k ω))).card : ℝ) <
          ∑ b ∈ C, ((P.z + 1 - kd).descFactorial m : ℝ) * (T b).card * p ^ m - (t₁ + t₂)) ≤
      (P.z.choose kd : ℝ) * ratio (DegPerm (F := F) κ u) ^ kd +
        (2 * Real.exp (-(t₁ ^ 2 / (2 * B₁))) + 2 * Real.exp (-(t₂ ^ 2 / (2 * B₂)))) :=
  (probG_mono fun ω h => lt_of_le_of_lt
    (countVar_le_labelled M κ a₀ k S Sg Φ hΦ hk0 A C e ψ ω) h).trans
    (ext_star hM hrows κ a₀ k hk u kd C e (atomQ S Sg A a₀ ψ) Fx hFU hF hFr D hD T hT hTU hp0
      hp hSmax hB₁ hB₂ hB₁0 hB₂0 ht₁ ht₂)

omit [Field F] [Field K] [Algebra F K] [Fintype K] [DecidableEq K] in
theorem dom_restrictT {R V : Type*} [DecidableEq R] (φ : R → V) (B : Finset R) :
    dom (restrictT φ B) = B := by
  ext x; by_cases hx : x ∈ B <;> simp [dom, restrictT, restrict, hx]

/-- **Copies extending `ψ_{b,i}` satisfy the atom predicate** (Lemma 2.21 (ii)). -/
theorem atomQ_of_extends (S : VSystem (Fin P.q) (Fin P.NA) (Fin D → ℤ) r)
    (Sg : Subgroup (Equiv.Perm (Fin P.q))) {A : Fin P.NA} (hA : S.A A = sigmaLe Sg)
    (a₀ : (Fin P.q → Fin P.n) → Fin P.NA) {β : Type*} {m : ℕ}
    (ψ : β → Fin m → (Fin P.q → Option (Fin P.n))) {b : β} {i : Fin m}
    {φ : Fin P.q → Fin P.n} (hφ : Function.Injective φ) (ha : a₀ φ = A) {B : Finset (Fin P.q)}
    (hB : B.card = r) (hψ : ψ b i = restrictT φ B) : atomQ S Sg A a₀ ψ b i φ := by
  unfold atomQ
  rw [hψ, ha, domF_eq (dom_restrictT φ B)]
  exact (onOrbit_molecule_restrict S Sg hA hφ hB).symm

end TParams

end DesignsII
