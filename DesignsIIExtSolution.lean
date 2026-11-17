/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib
public import DesignsII.ExtPaper

/-!
# Proof of the statement in `DesignsIIExtChallenge.lean`

The definitions of the challenge are those of `DesignsII.ExtDefs` (the same text); the statement
is `DesignsII.TParams.ext_star_paper`.
-/

@[expose] public section

namespace DesignsII

open Finset

section Statement

variable {F K : Type*} [Field F] [Fintype F] [DecidableEq F] [Field K] [Algebra F K] [Fintype K]
  [DecidableEq K]

namespace TParams

variable {P : TParams} {D : ℕ}

open Classical in
/-- **Keevash, *The existence of designs II*, Lemma 3.8 (`ext*`), in the random template space.**

The template space consists of independent uniform permutations: `f_j` (`j < z`, values in a
field `K` with `N ≥ n` elements via `κ`), `T_e ∈ [z]` and `π_e` for `r`-sets `e`, and `A_φ`, the
activation of each map `φ : [q] → [n]`. A copy `φ` of colour `j` is in the template (`CopyOK`) if
`A_φ = A`, `φ` is activated (threshold `k φ`), `T_e = j` and `π_e φ = id` on its edges and
`f_j ∘ φ = M y` for some `y` (`M` a generic `q × r` matrix over a finite field `F ⊆ K` with
distinct rows); `M* = templateSet`. Let `Φ` be a `Σ`-adapted `[q]`-complex on `[n]`, `γ` a vector
system with `A = Σ^≤`, `G` such that `(Φ, γ[G])` is `(ω, h)`-extendable, and let only copies that
are `Φ`-embeddings be activated, those with `γ(φ) ≤_γ G` with threshold at least `k_min`.
For configurations `b ∈ C` (labelled `r`-maps `ψ b i ∈ Φ_{B_i}` with `γ(ψ b i) ≤_γ G`, distinct
edges `e b i = Im(ψ b i)`, fixed vertices `u` meeting each edge in `F_i`, `|F_i| ≤ r - 1`,
`|C| ≤ Δ N^v`, at most `Δ N^{v-(r-|F_i|)}` configurations through a given `i`-th edge), the number
of configurations all of whose atoms `γ(ψ b i)` lie below `∂^γ M*` is at least
`|C| (z+1-kd)_m (a^m - m² · K_c · (n^{q-r})^{m-2}) p^m - 2ε N^v` (in Lean
`m * m * (Kc * (n ^ (q - r)) ^ (m - 2))`, i.e. `K_c` appears exactly once, also for `m = 2`), with
`a = ω |V(Φ)|^{q-r} - (q-r) s n^{q-r-1}`, `p = pRate` and
`K_c = q^{r+1} n^{q-r-1} · q^r n^{q-r} · (1 + C(q,r))` (so the correction is
`O(n^{(q-r)m-1})`, of lower order than `a^m`), except with probability at most
`C(z,kd) p_deg^kd + 2e^{-ε²N/(2c₁)} + 2e^{-ε²N/(2c₂)}`.

This is an explicit finite-`N` bound. The constants `c₁` (depending on `z, q, r, m, Δ`) and `c₂`
(depending on `z, q, r, m, Δ` and on `Smax`, a bound for the sizes `NA`, `N_act`, … of the
non-colour coordinates) do not involve `N` directly; the failure probability tends to `0` as
`N → ∞` only when these parameters (and `|F|, s, kd, ε`) are kept fixed, or more generally when
`c₁, c₂ = o(N)` and `|F|^s / N → 0`. -/
theorem lemma_3_8 {M : Matrix (Fin P.q) (Fin P.r) F} (hM : IsGeneric M)
    (hrows : DistinctRows M) (κ : Fin P.N ≃ K) (hK : Fintype.card K = P.N)
    (S : VSystem (Fin P.q) (Fin P.NA) (Fin D → ℤ) P.r) (Sg : Subgroup (Equiv.Perm (Fin P.q)))
    (Φ : RSystem (Fin P.q) (Fin P.n)) (hΦc : Φ.IsComplex) (hΦ : IsAdapted Φ Sg)
    (A : Fin P.NA) (hA : S.A A = sigmaLe Sg) (G : (Fin P.q → Option (Fin P.n)) → (Fin D → ℤ))
    {ω : ℝ} {hh : ℕ} (hh0 : 0 < hh) (hext : IsExtendableRel (r := P.r) Φ (gammaG S Sg Φ G) ω hh)
    (k : (Fin P.q → Fin P.n) → ℕ) (hk : ∀ ψ, k ψ ≤ P.Nact)
    (hk0 : ∀ φ, ¬ IsEmbedding (S.A A) Φ φ → k φ = 0) {kmin : ℕ}
    (hkG : ∀ φ, Function.Injective φ → IsEmbedding (S.A A) Φ φ →
      LeGamma S Sg Φ (S.molecule A φ) G → kmin ≤ k φ)
    {s : ℕ} (u : Fin s ↪ Fin P.n) (kd : ℕ) {β : Type*} {m : ℕ} (C : Finset β)
    (Bl : Fin m → Finset (Fin P.q)) (hBl : ∀ i, (Bl i).card = P.r)
    (ψ : β → Fin m → (Fin P.q → Option (Fin P.n))) (hψΦ : ∀ b ∈ C, ∀ i, ψ b i ∈ Φ.maps (Bl i))
    (hψG : ∀ b ∈ C, ∀ i, LeGamma S Sg Φ (moleculeP S A (ψ b i)) G)
    (e : β → Fin m → Finset (Fin P.n)) (he : ∀ b ∈ C, ∀ i, (e b i).card = P.r)
    (heψ : ∀ b ∈ C, ∀ i, ∀ x ∈ Bl i, ∃ w ∈ e b i, ψ b i x = some w)
    (heinj : ∀ b ∈ C, Function.Injective (e b))
    (Fx : Fin m → Finset (Fin P.n)) (hFU : ∀ i, Fx i ⊆ univ.map u)
    (hF : ∀ b ∈ C, ∀ i, Fx i ⊆ e b i) (hFeq : ∀ b ∈ C, ∀ i, e b i ∩ univ.map u ⊆ Fx i)
    (hFr : ∀ i, (Fx i).card + 1 ≤ P.r)
    {v Δ : ℕ} (hv : 1 ≤ v) (hrv : ∀ i, P.r ≤ v + (Fx i).card) (Dc : Fin m → ℕ)
    (hD : ∀ i (e' : Finset (Fin P.n)), (C.filter fun b => e b i = e').card ≤ Dc i)
    (hDΔ : ∀ i, Dc i ≤ Δ * P.N ^ (v - (P.r - (Fx i).card))) (hCΔ : C.card ≤ Δ * P.N ^ v)
    (hNpos : 0 < P.N) (hq1 : 1 ≤ P.q) (hn : 0 < P.n)
    (hN : 2 * (P.q ^ 2 + P.q * s) ≤ P.N) (hsq : s + P.q ≤ P.N)
    {Smax : ℕ} (hSmax : ∀ c : P.Coord, c.isLeft = false → P.size c ≤ Smax)
    (ha : 0 ≤ ω * ((vertices Φ).toFinset.card : ℝ) ^ (P.q - P.r) -
      ((P.q - P.r) * (s * P.n ^ (P.q - P.r - 1)) : ℕ))
    {ε : ℝ} (hε : 0 < ε) :
    probG (a := P.size) (fun ω' =>
        ((C.filter fun b => ∀ i, LeGamma S Sg Φ (moleculeP S A (ψ b i))
          (S.boundary (templateSet M κ (fun _ => A) k ω'))).card : ℝ) <
          C.card * (((P.z + 1 - kd).descFactorial m : ℝ) *
            ((ω * ((vertices Φ).toFinset.card : ℝ) ^ (P.q - P.r) -
              ((P.q - P.r) * (s * P.n ^ (P.q - P.r - 1)) : ℕ)) ^ m -
              (m * m * (P.Kc * (P.n ^ (P.q - P.r)) ^ (m - 2)) : ℕ)) * pRate P kmin ^ m) -
            2 * (ε * (P.N : ℝ) ^ v)) ≤
      (P.z.choose kd : ℝ) * ((Fintype.card F ^ s * Fintype.card K ^ (s - 1) : ℕ) *
          ((P.N - s).factorial : ℝ) / (P.N.factorial : ℝ)) ^ kd +
        (2 * Real.exp (-(ε ^ 2 * P.N / (2 * c₁ P m Δ))) +
          2 * Real.exp (-(ε ^ 2 * P.N / (2 * c₂ P m Δ Smax)))) :=
  ext_star_paper hM hrows κ hK S Sg Φ hΦc hΦ A hA G hh0 hext k hk hk0 hkG u kd C Bl hBl ψ hψΦ hψG e he heψ heinj Fx hFU hF hFeq hFr hv hrv Dc hD hDΔ hCΔ hNpos hq1 hn hN hsq hSmax ha hε

end TParams

end Statement

end DesignsII
