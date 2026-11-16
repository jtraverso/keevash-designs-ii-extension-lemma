/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import DesignsII.ExtDefs
public import DesignsII.ExtFinal
public import DesignsII.ExtCand

/-!
# Lemma `ext*` (Keevash, *The existence of designs II*, Lemma 3.8), template-space form

`ext_star_paper`: the candidate tuples are built from `(ω, h)`-extendability of `(Φ, γ[G])`
(`candSet`, `goodTuples`). For configurations `b ∈ C` whose edges are labelled maps
`ψ b i ∈ Φ_{B_i} ∩ γ[G]^A`, with probability at least
`1 - C(z,kd) p_deg^kd - 2e^{-ε²N/(2c₁)} - 2e^{-ε²N/(2c₂)}`,

  `#{b ∈ C : ∀ i, γ(ψ b i) ≤_γ ∂^γ M*} ≥ |C| (z+1-kd)_m (a^m - m² K n^{(q-r)(m-2)}) p^m - 2ε N^v`

with `a = ω |V(Φ)|^{q-r} - (q-r) s n^{q-r-1}`, `K = q^{r+1} n^{q-r-1} q^r n^{q-r} (1 + C(q,r))`.
-/

@[expose] public section

namespace DesignsII

open Finset

variable {F K : Type*} [Field F] [Fintype F] [DecidableEq F] [Field K] [Algebra F K] [Fintype K]
  [DecidableEq K]

namespace TParams

variable {P : TParams} {D : ℕ}

/-- Real lower bound for good tuples. -/
theorem card_goodTuples_ge_real {m : ℕ} (e : Fin m → Finset (Fin P.n))
    (he : ∀ i, (e i).card = P.r) (heinj : Function.Injective e)
    (A : Fin m → Finset (Fin P.q → Fin P.n)) (hAe : ∀ i, ∀ φ ∈ A i, e i ∈ edges φ)
    {a : ℝ} (ha : 0 ≤ a) (hA : ∀ i, a ≤ (A i).card) {Nmax : ℕ} (hAN : ∀ i, (A i).card ≤ Nmax) :
    a ^ m - (m * m * (P.Kc * Nmax ^ (m - 2)) : ℕ) ≤ ((goodTuples A).card : ℝ) := by
  classical
  have h := card_goodTuples_ge e he heinj A hAe
  have hsum : ∑ p ∈ univ.filter (fun p : Fin m × Fin m => p.1 ≠ p.2),
      P.q ^ (P.r + 1) * P.n ^ (P.q - (P.r + 1)) * (P.q ^ P.r * P.n ^ (P.q - P.r)) *
        (1 + P.q.choose P.r) * ∏ l ∈ (univ.erase p.1).erase p.2, (A l).card ≤
      m * m * (P.Kc * Nmax ^ (m - 2)) := by
    calc _ ≤ ∑ _p ∈ univ.filter (fun p : Fin m × Fin m => p.1 ≠ p.2), P.Kc * Nmax ^ (m - 2) := by
          refine sum_le_sum fun p hp => Nat.mul_le_mul_left _ ?_
          have hne : p.1 ≠ p.2 := (mem_filter.1 hp).2
          have hcard : ((univ.erase p.1).erase p.2).card = m - 2 := by
            rw [card_erase_of_mem (mem_erase.2 ⟨fun h => hne h.symm, mem_univ _⟩),
              card_erase_of_mem (mem_univ _), card_univ, Fintype.card_fin]; omega
          rw [← hcard]
          exact prod_le_pow_card _ _ _ fun l _ => hAN l
      _ ≤ m * m * (P.Kc * Nmax ^ (m - 2)) := by
          rw [sum_const, smul_eq_mul]
          refine Nat.mul_le_mul_right _ ((card_le_univ _).trans ?_)
          simp
  have hprod : a ^ m ≤ ((∏ i, (A i).card : ℕ) : ℝ) := by
    push_cast
    calc a ^ m = ∏ _i : Fin m, a := by simp
      _ ≤ _ := Finset.prod_le_prod₀ (fun _ _ => ha) fun i _ => hA i
  have h' : ((∏ i, (A i).card : ℕ) : ℝ) ≤ ((goodTuples A).card : ℝ) +
      ((m * m * (P.Kc * Nmax ^ (m - 2)) : ℕ) : ℝ) := by
    exact_mod_cast h.trans (Nat.add_le_add_left hsum _)
  linarith

open Classical in
/-- **Lemma `ext*` (Keevash, *Designs II*, Lemma 3.8) in the template space.** -/
theorem ext_star_paper {M : Matrix (Fin P.q) (Fin P.r) F} (hM : IsGeneric M)
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
          2 * Real.exp (-(ε ^ 2 * P.N / (2 * c₂ P m Δ Smax)))) := by
  set U := univ.map u
  set Ab : β → Fin m → Finset (Fin P.q → Fin P.n) := fun b i =>
    candSet S Sg Φ G A U (Bl i) (ψ b i)
  set T : β → Finset (Fin m → Fin P.q → Fin P.n) := fun b => goodTuples (Ab b)
  -- properties of candidates
  have hmemAb : ∀ b ∈ C, ∀ i, ∀ φ ∈ Ab b i,
      Function.Injective φ ∧ ψ b i = restrictT φ (Bl i) ∧ e b i ∈ edges φ ∧
        (univ.filter fun l => φ l ∈ U).card + 1 ≤ P.r ∧ kmin ≤ k φ := by
    intro b hb i φ hφ
    obtain ⟨⟨hΦu, hagree, hrest⟩, hnoU⟩ := (mem_filter.1 hφ).2
    have hinj := injective_of_maps_univ hΦu
    have hψeq := eq_restrictT (Φ.dom_eq _ _ (hψΦ b hb i)) hagree
    have himg : (Bl i).image φ = e b i := by
      refine eq_of_subset_of_card_le (fun w hw => ?_) ?_
      · obtain ⟨x, hx, rfl⟩ := mem_image.1 hw
        obtain ⟨w', hw', hψw⟩ := heψ b hb i x hx
        rw [hagree x hx] at hψw
        rw [Option.some.inj hψw]; exact hw'
      · rw [card_image_of_injective _ hinj, hBl, he b hb i]
    refine ⟨hinj, hψeq, ?_, ?_, ?_⟩
    · refine mem_powersetCard.2 ⟨?_, he b hb i⟩
      rw [← himg]; exact image_subset_image (subset_univ _)
    · have hsub : (univ.filter fun l => φ l ∈ U).image φ ⊆ Fx i := by
        intro w hw
        obtain ⟨l, hl, rfl⟩ := mem_image.1 hw
        have hlU := (mem_filter.1 hl).2
        have hlB : l ∈ Bl i := by by_contra h; exact hnoU l h hlU
        exact hFeq b hb i (mem_inter.2 ⟨himg ▸ mem_image_of_mem _ hlB, hlU⟩)
      have := card_le_card hsub
      rw [card_image_of_injective _ hinj] at this
      exact (Nat.add_le_add_right this 1).trans (hFr i)
    · have hemb : IsEmbedding (S.A A) Φ φ := by rw [hA]; exact isEmbedding_sigmaLe hΦc hΦ hΦu
      refine hkG φ hinj hemb (leGamma_molecule_of_restrict Sg S Φ hΦ hA hinj hemb G
        (hBl i) fun B hB => ?_)
      by_cases hBs : B ⊆ Bl i
      · have : B = Bl i := eq_of_subset_of_card_le hBs (by rw [hB, hBl])
        rw [this, ← hψeq]; exact hψG b hb i
      · exact (hrest B hB hBs).2
  have hTprops : ∀ b ∈ C, ∀ φ ∈ T b, (∀ i, Function.Injective (φ i)) ∧
      (∀ i, e b i ∈ edges (φ i) ∧ atomQ S Sg A (fun _ => A) ψ b i (φ i)) ∧
      Function.Injective φ ∧ ∀ i i', i ≠ i' → Disjoint (edges (φ i)) (edges (φ i')) := by
    intro b hb φ hφ
    obtain ⟨hpi, hinj, hdisj⟩ := mem_filter.1 hφ
    have hmem : ∀ i, φ i ∈ Ab b i := fun i => Fintype.mem_piFinset.1 hpi i
    refine ⟨fun i => (hmemAb b hb i _ (hmem i)).1, fun i => ⟨(hmemAb b hb i _ (hmem i)).2.2.1,
      atomQ_of_extends S Sg hA (fun _ => A) ψ (hmemAb b hb i _ (hmem i)).1 rfl (hBl i)
        (hmemAb b hb i _ (hmem i)).2.1⟩, hinj, hdisj⟩
  have hmain := ext_star_rates hM hrows κ hK (fun _ => A) k hk S Sg Φ hΦ hk0 A u kd C e ψ Fx hFU
    hF hFr hv hrv Dc hD hDΔ hCΔ T hTprops
    (fun b hb φ hφ i => (hmemAb b hb i _
      (Fintype.mem_piFinset.1 (mem_filter.1 hφ).1 i)).2.2.2.1)
    (fun b hb φ hφ i => (hmemAb b hb i _
      (Fintype.mem_piFinset.1 (mem_filter.1 hφ).1 i)).2.2.2.2)
    hNpos hq1 hN hsq hSmax hε
  refine le_trans (probG_mono fun ω' h => lt_of_lt_of_le h ?_) hmain
  -- the explicit lower bound for the mean
  refine sub_le_sub_right ?_ _
  have hconst : ∀ X : ℝ, (C.card : ℝ) * X = ∑ _b ∈ C, X := fun X => by
    rw [sum_const, nsmul_eq_mul]
  rw [hconst]
  refine sum_le_sum fun b hb => ?_
  refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ (by positivity))
    (by unfold pRate; positivity)
  have hcard := card_goodTuples_ge_real (e b) (he b hb) (heinj b hb) (Ab b)
    (fun i φ hφ => (hmemAb b hb i φ hφ).2.2.1) ha
    (fun i => by
      have := card_candSet_ge S Sg Φ hΦc G hh0 hext A U (hψΦ b hb i) hn
      rw [hBl, card_map, card_univ, Fintype.card_fin] at this
      exact this)
    (fun i => by
      have := card_candSet_le S Sg Φ G A U (Bl i) (ψ b i) hn
      rwa [hBl] at this)
  exact hcard

end TParams

end DesignsII
