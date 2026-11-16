/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import DesignsII.ExtDefs
public import DesignsII.LabelledExt
public import DesignsII.PassAsymp
public import DesignsII.ExtAsymp

/-!
# Lemma `ext*` with explicit rates

`ext_star_rates`: in the template space, for configurations `b ∈ C` (labelled `r`-maps `ψ b i`,
edges `e b i`, `|C| ≤ Δ N^v`, at most `Δ N^{v-(r-f_i)}` configurations through a given `i`-th
edge, `f_i = |F_i| ≤ r - 1` fixed vertices in it) and candidate tuples `T b` of copies extending
the edges with activation thresholds `≥ k_min`,

  `P(X < ∑_b (z+1-kd)_m #T_b p^m - 2ε N^v) ≤ C(z,kd) p_deg^kd + 2e^{-ε²N/(2c₁)} + 2e^{-ε²N/(2c₂)}`

where `X = #{b ∈ C : ∀ i, γ(ψ b i) ≤_γ ∂^γ M*}`, `p = (2N^{q-r})^{-1} z^{-Q} ((q-r)!/q!)^Q
|𝒜|^{-1} k_min/N_act` (`Q = C(q,r)`), `p_deg = |F|^s N^{s-1} (N-s)!/N!` and `c₁, c₂` are explicit
constants independent of `N`.
-/

@[expose] public section

namespace DesignsII

open Finset

variable {F K : Type*} [Field F] [Fintype F] [DecidableEq F] [Field K] [Algebra F K] [Fintype K]
  [DecidableEq K]

namespace TParams

variable {P : TParams} {D r : ℕ}

open Classical in
/-- **Lemma `ext*` with explicit rates.** -/
theorem ext_star_rates {M : Matrix (Fin P.q) (Fin P.r) F} (hM : IsGeneric M)
    (hrows : DistinctRows M) (κ : Fin P.N ≃ K) (hK : Fintype.card K = P.N)
    (a₀ : (Fin P.q → Fin P.n) → Fin P.NA)
    (k : (Fin P.q → Fin P.n) → ℕ) (hk : ∀ ψ, k ψ ≤ P.Nact)
    (S : VSystem (Fin P.q) (Fin P.NA) (Fin D → ℤ) r) (Sg : Subgroup (Equiv.Perm (Fin P.q)))
    (Φ : RSystem (Fin P.q) (Fin P.n)) (hΦ : IsAdapted Φ Sg)
    (hk0 : ∀ φ, ¬ IsEmbedding (S.A (a₀ φ)) Φ φ → k φ = 0) (A : Fin P.NA)
    {s : ℕ} (u : Fin s ↪ Fin P.n) (kd : ℕ) {β : Type*} {m : ℕ} (C : Finset β)
    (e : β → Fin m → Finset (Fin P.n)) (ψ : β → Fin m → (Fin P.q → Option (Fin P.n)))
    (Fx : Fin m → Finset (Fin P.n)) (hFU : ∀ i, Fx i ⊆ univ.map u)
    (hF : ∀ b ∈ C, ∀ i, Fx i ⊆ e b i) (hFr : ∀ i, (Fx i).card + 1 ≤ P.r)
    {v Δ : ℕ} (hv : 1 ≤ v) (hrv : ∀ i, P.r ≤ v + (Fx i).card) (Dc : Fin m → ℕ)
    (hD : ∀ i (e' : Finset (Fin P.n)), (C.filter fun b => e b i = e').card ≤ Dc i)
    (hDΔ : ∀ i, Dc i ≤ Δ * P.N ^ (v - (P.r - (Fx i).card))) (hCΔ : C.card ≤ Δ * P.N ^ v)
    (T : β → Finset (Fin m → Fin P.q → Fin P.n))
    (hT : ∀ b ∈ C, ∀ φ ∈ T b, (∀ i, Function.Injective (φ i)) ∧
      (∀ i, e b i ∈ edges (φ i) ∧ atomQ S Sg A a₀ ψ b i (φ i)) ∧
      Function.Injective φ ∧ ∀ i i', i ≠ i' → Disjoint (edges (φ i)) (edges (φ i')))
    (hTU : ∀ b ∈ C, ∀ φ ∈ T b, ∀ i,
      (univ.filter fun l => φ i l ∈ univ.map u).card + 1 ≤ P.r)
    {kmin : ℕ} (hkmin : ∀ b ∈ C, ∀ φ ∈ T b, ∀ i, kmin ≤ k (φ i))
    (hNpos : 0 < P.N) (hq1 : 1 ≤ P.q)
    (hN : 2 * (P.q ^ 2 + P.q * s) ≤ P.N) (hsq : s + P.q ≤ P.N)
    {Smax : ℕ} (hSmax : ∀ c : P.Coord, c.isLeft = false → P.size c ≤ Smax)
    {ε : ℝ} (hε : 0 < ε) :
    probG (a := P.size) (fun ω =>
        ((C.filter fun b => ∀ i, LeGamma S Sg Φ (moleculeP S A (ψ b i))
          (S.boundary (templateSet M κ a₀ k ω))).card : ℝ) <
          ∑ b ∈ C, ((P.z + 1 - kd).descFactorial m : ℝ) * (T b).card * pRate P kmin ^ m -
            2 * (ε * (P.N : ℝ) ^ v)) ≤
      (P.z.choose kd : ℝ) * ((Fintype.card F ^ s * Fintype.card K ^ (s - 1) : ℕ) *
          ((P.N - s).factorial : ℝ) / (P.N.factorial : ℝ)) ^ kd +
        (2 * Real.exp (-(ε ^ 2 * P.N / (2 * c₁ P m Δ))) +
          2 * Real.exp (-(ε ^ 2 * P.N / (2 * c₂ P m Δ Smax)))) := by
  have hN0 : (0 : ℝ) < P.N := by exact_mod_cast hNpos
  have hc₁ : 0 < c₁ P m Δ := by unfold c₁; positivity
  have hc₂ : 0 < c₂ P m Δ Smax := by unfold c₂; positivity
  set B₁ := c₁ P m Δ * (P.N : ℝ) ^ (2 * v - 1)
  set B₂ := c₂ P m Δ Smax * (P.N : ℝ) ^ (2 * v - 1)
  have hB₁0 : 0 < B₁ := by positivity
  have hB₂0 : 0 < B₂ := by positivity
  set t := ε * (P.N : ℝ) ^ v
  have ht : 0 < t := by positivity
  -- the proxies
  have hB₁ : (P.z : ℝ) * P.N * (2 * ((∑ i, P.q ^ ((Fx i).card + 1) *
      Fintype.card K ^ (P.r - ((Fx i).card + 1)) * (P.q.choose P.r * Dc i) : ℕ) : ℝ)) ^ 2 ≤ B₁ := by
    rw [hK]
    refine (proxy₁_le P.z P.N v P.r P.q (P.q.choose P.r) Δ (fun i => (Fx i).card) Dc
      hq1 hv hFr hrv hDΔ).trans ?_
    exact mul_le_mul_of_nonneg_right (by unfold c₁; linarith) (pow_pos hN0 _).le
  have hB₂ : 4 * (Smax : ℝ) * (((P.z * P.q ^ P.r + P.z) * ∑ i, P.q.choose P.r * Dc i : ℕ) : ℝ) *
      (((2 * P.q.choose P.r + 2) * (m * C.card * (P.z * P.q ^ P.r)) : ℕ) : ℝ) ≤ B₂ := by
    refine (proxy₂_le C Smax P.z P.N v P.r P.q (P.q.choose P.r) Δ (fun i => (Fx i).card) Dc
      hNpos hv hFr hDΔ hCΔ).trans ?_
    exact mul_le_mul_of_nonneg_right (by unfold c₂; linarith) (pow_pos hN0 _).le
  -- the passing probability
  have hp0 : 0 ≤ pRate P kmin := by unfold pRate; positivity
  have hp : ∀ b ∈ C, ∀ φ ∈ T b, ∀ i (j : Fin P.z) (hφ : Function.Injective (φ i)),
      pRate P kmin ≤ passLB (K := K) (univ.map u) j hφ (k (φ i)) := by
    intro b hb φ hφT i j hφ
    have := passLB_ge hK (univ.map u) j hφ (k (φ i)) (hTU b hb φ hφT i)
      (by rw [card_map, card_univ, Fintype.card_fin]; exact hN)
      (by rw [card_map, card_univ, Fintype.card_fin]; exact hsq)
    refine le_trans ?_ this
    unfold pRate
    gcongr
    exact_mod_cast hkmin b hb φ hφT i
  have hmain := ext_star_labelled hM hrows κ a₀ k hk S Sg Φ hΦ hk0 A u kd C e ψ Fx hFU hF hFr Dc
    hD T hT hTU hp0 hp hSmax hB₁ hB₂ hB₁0 hB₂0 ht ht
  rw [show 2 * t = t + t by ring]
  refine hmain.trans ?_
  have hr0 : 0 ≤ ratio (DegPerm (F := F) κ u) := by unfold ratio; positivity
  refine add_le_add (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ hr0 (ratio_deg_le κ u) kd) (by positivity))
    (add_le_add (mul_le_mul_of_nonneg_left ?_ (by norm_num))
      (mul_le_mul_of_nonneg_left ?_ (by norm_num)))
  · exact exp_tail_le (ε := ε) hv hN0 hc₁ hB₁0 le_rfl
  · exact exp_tail_le (ε := ε) hv hN0 hc₂ hB₂0 le_rfl

end TParams

end DesignsII
