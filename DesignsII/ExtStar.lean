/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import DesignsII.ExtConc
public import DesignsII.ManyDeg

/-!
# Assembly of Lemma `ext*` on the template space

* `cover_lower_tail`: the law of total probability over the values at the fixed vertices `U`
  (with an exceptional set `Bad` of values), the conditional concentration `cover_tail_fixed` and
  a lower bound `μ` for the conditional means outside `Bad` give
  `P(X < μ - t₁ - t₂) ≤ P(Bad) + 2e^{-t₁²/2B₁} + 2e^{-t₂²/2B₂}`;
* `probG_degBad_le`: with `Bad` = "at least `k` colours are degenerate at `U`",
  `P(Bad) ≤ C(z, k) p_deg^k` (`probG_many_deg_le`).
-/

@[expose] public section

namespace DesignsII

open Finset Equiv

variable {F K : Type*} [Field F] [Field K] [Algebra F K] [Fintype K] [DecidableEq K]

namespace TParams

variable {P : TParams}

open Classical in
/-- **Lower tail of the covering count** (assembly of `ext*`). -/
theorem cover_lower_tail {M : Matrix (Fin P.q) (Fin P.r) F} (hM : IsGeneric M)
    (κ : Fin P.N ≃ K) (a₀ : (Fin P.q → Fin P.n) → Fin P.NA) (k : (Fin P.q → Fin P.n) → ℕ)
    {β : Type*} {m : ℕ} (C : Finset β) (e : β → Fin m → Finset (Fin P.n))
    (Q : β → Fin m → (Fin P.q → Fin P.n) → Prop)
    (U : Finset (Fin P.n))
    (Fx : Fin m → Finset (Fin P.n)) (hFU : ∀ i, Fx i ⊆ U) (hF : ∀ b ∈ C, ∀ i, Fx i ⊆ e b i)
    (hFr : ∀ i, (Fx i).card + 1 ≤ P.r) (D : Fin m → ℕ)
    (hD : ∀ i (e' : Finset (Fin P.n)), (C.filter fun b => e b i = e').card ≤ D i)
    {Smax : ℕ} (hSmax : ∀ c : P.Coord, c.isLeft = false → P.size c ≤ Smax)
    (Bad : (∀ c, fixedPos U c ↪ Fin (P.size c)) → Prop) {μ : ℝ}
    (hμ : ∀ v, ¬ Bad v → μ ≤ meanG (a := fun c => P.size c - (fixedPos U c).card)
      (fun τ => countVar C (fun b ω => CoverEv M κ a₀ k (e b) (Q b) ω) (liftPi (fixedPos U) v τ)))
    {B₁ B₂ t₁ t₂ : ℝ}
    (hB₁ : (P.z : ℝ) * P.N * (2 * ((∑ i, P.q ^ ((Fx i).card + 1) *
      Fintype.card K ^ (P.r - ((Fx i).card + 1)) * (P.q.choose P.r * D i) : ℕ) : ℝ)) ^ 2 ≤ B₁)
    (hB₂ : 4 * (Smax : ℝ) * (((P.z * P.q ^ P.r + P.z) * ∑ i, P.q.choose P.r * D i : ℕ) : ℝ) *
      (((2 * P.q.choose P.r + 2) * (m * C.card * (P.z * P.q ^ P.r)) : ℕ) : ℝ) ≤ B₂)
    (hB₁0 : 0 < B₁) (hB₂0 : 0 < B₂) (ht₁ : 0 < t₁) (ht₂ : 0 < t₂) :
    probG (a := P.size) (fun ω =>
        countVar C (fun b ω => CoverEv M κ a₀ k (e b) (Q b) ω) ω < μ - (t₁ + t₂)) ≤
      probG (a := P.size) (fun ω => Bad (restrS (fixedPos U) ω)) +
        (2 * Real.exp (-(t₁ ^ 2 / (2 * B₁))) + 2 * Real.exp (-(t₂ ^ 2 / (2 * B₂)))) := by
  refine probG_le_of_cond_except (fixedPos U) _ Bad (by positivity) fun v hv => ?_
  refine le_trans (probG_mono fun τ hτ => ?_) (cover_tail_fixed hM κ a₀ k C e Q U v Fx hFU hF hFr
    D hD hSmax hB₁ hB₂ hB₁0 hB₂0 ht₁ ht₂)
  have := hμ v hv
  exact lt_abs.2 (Or.inr (by linarith))

open Classical in
/-- `v` has at least `k` colours whose values at the fixed vertices `u` are `F`-dependent. -/
def DegBad (κ : Fin P.N ≃ K) {s : ℕ} (u : Fin s ↪ Fin P.n) (k : ℕ)
    (v : ∀ c, fixedPos (univ.map u) c ↪ Fin (P.size c)) : Prop :=
  k ≤ (univ.filter fun j : Fin P.z => ¬ LinearIndependent F fun t =>
    κ (v (.inl j) ⟨Fin.castLE P.hnN (u t),
      mem_map_of_mem (Fin.castLEEmb P.hnN) (mem_map_of_mem u (mem_univ t))⟩)).card

omit [Fintype K] [DecidableEq K] in
open Classical in
/-- **Few degenerate colours**: `P(DegBad) ≤ C(z, k) p_deg^k`. -/
theorem probG_degBad_le (κ : Fin P.N ≃ K) {s : ℕ} (u : Fin s ↪ Fin P.n) (k : ℕ) :
    probG (a := P.size) (fun ω => DegBad (F := F) κ u k (restrS (fixedPos (univ.map u)) ω)) ≤
      (P.z.choose k : ℝ) * ratio (DegPerm (F := F) κ u) ^ k := by
  refine le_trans (le_of_eq ?_) (probG_many_deg_le κ u k)
  congr 1
  funext ω
  unfold DegBad DegPerm
  congr! 3

end TParams


/-! ### The conditional probability that a copy passes (Lemma `e|E`, lower bound) -/

namespace TParams

variable {P : TParams}

/-- The positions `f_j(φ(·))` read by a copy, as an embedding into `[N]`. -/
abbrev wEmb {φ : Fin P.q → Fin P.n} (hφ : Function.Injective φ) : Fin P.q ↪ Fin P.N :=
  ⟨fun i => Fin.castLE P.hnN (φ i), fun _ _ h => hφ (Fin.castLE_injective P.hnN h)⟩

open Classical in
/-- **Lower bound for the conditional probability that a copy passes** (Lemma `e|E`): if the
copy has `s = |I₀| ≤ r - 1` fixed vertices and the revealed values there are `F`-independent,
it passes with conditional probability at least
`(N^{r-s} - (q² + q|U|) N^{r-s-1}) (N-|U|-#new)!/(N-|U|)! · z^{-Q} ((q-r)!/q!)^Q |𝒜|^{-1} k/N_act`. -/
theorem probG_copyOK_cond_ge {M : Matrix (Fin P.q) (Fin P.r) F} (hM : IsGeneric M)
    (hrows : DistinctRows M) (κ : Fin P.N ≃ K) (j : Fin P.z) (a₀ : Fin P.NA) {k : ℕ}
    (hk : k ≤ P.Nact) {φ : Fin P.q → Fin P.n} (hφ : Function.Injective φ) (U : Finset (Fin P.n))
    (v : ∀ c, fixedPos U c ↪ Fin (P.size c))
    (hI : (I₀ (fixedPos U (.inl j)) (wEmb hφ)).card + 1 ≤ P.r)
    (hc : LinearIndependent F fun t : Fin (I₀ (fixedPos U (.inl j)) (wEmb hφ)).card =>
      cval (fixedPos U (.inl j)) (v (.inl j)) κ (wEmb hφ)
        ((I₀ (fixedPos U (.inl j)) (wEmb hφ)).orderEmbOfFin rfl t)) :
    (((Fintype.card K ^ (P.r - (I₀ (fixedPos U (.inl j)) (wEmb hφ)).card) : ℕ) : ℝ) -
        (((P.q ^ 2 + P.q * (fixedPos U (.inl j)).card) *
          Fintype.card K ^ (P.r - (I₀ (fixedPos U (.inl j)) (wEmb hφ)).card - 1) : ℕ) : ℝ)) *
        (((P.N - (fixedPos U (.inl j)).card -
          Fintype.card {i // wEmb hφ i ∉ fixedPos U (.inl j)}).factorial : ℕ) : ℝ) /
          ((P.N - (fixedPos U (.inl j)).card).factorial : ℝ) *
        (1 / (P.z : ℝ)) ^ (edges φ).card *
        (((P.q - P.r).factorial : ℝ) / (P.q.factorial : ℝ)) ^ (edges φ).card *
        (1 / (P.NA : ℝ)) * ((k : ℝ) / P.Nact) ≤
      probG (a := fun c => P.size c - (fixedPos U c).card)
        (fun τ => CopyOK M κ j a₀ k φ (liftPi (fixedPos U) v τ)) := by
  have hr : ratio (fun σ : Perm (Fin (P.size (.inl j) - (fixedPos U (.inl j)).card)) =>
      ∃ y, ∀ i, κ (liftC (fixedPos U (.inl j)) (v (.inl j)) σ (Fin.castLE P.hnN (φ i))) =
        mvec M y i) =
      (((Yc (fixedPos U (.inl j)) (v (.inl j)) κ M (wEmb hφ)).card *
        (P.N - (fixedPos U (.inl j)).card -
          Fintype.card {i // wEmb hφ i ∉ fixedPos U (.inl j)}).factorial : ℕ) : ℝ) /
        ((P.N - (fixedPos U (.inl j)).card).factorial : ℝ) :=
    ratio_compat_cond hM κ j hφ U (v (.inl j))
  rw [probG_copyOK_cond M κ j a₀ hk hφ U v, hr]
  have hY := card_Yc_ge (fixedPos U (.inl j)) (v (.inl j)) κ (wEmb hφ) hM P.hrq hrows hI hc
  have hY' : (((Fintype.card K ^ (P.r - (I₀ (fixedPos U (.inl j)) (wEmb hφ)).card) : ℕ) : ℝ) -
      (((P.q ^ 2 + P.q * (fixedPos U (.inl j)).card) *
        Fintype.card K ^ (P.r - (I₀ (fixedPos U (.inl j)) (wEmb hφ)).card - 1) : ℕ) : ℝ)) ≤
      ((Yc (fixedPos U (.inl j)) (v (.inl j)) κ M (wEmb hφ)).card : ℝ) := by
    have : ((Fintype.card K ^ (P.r - (I₀ (fixedPos U (.inl j)) (wEmb hφ)).card) : ℕ) : ℝ) ≤
        ((Yc (fixedPos U (.inl j)) (v (.inl j)) κ M (wEmb hφ)).card : ℝ) +
        (((P.q ^ 2 + P.q * (fixedPos U (.inl j)).card) *
          Fintype.card K ^ (P.r - (I₀ (fixedPos U (.inl j)) (wEmb hφ)).card - 1) : ℕ) : ℝ) := by
      exact_mod_cast hY
    linarith
  have hpos : (0 : ℝ) ≤ (1 / (P.z : ℝ)) ^ (edges φ).card *
      (((P.q - P.r).factorial : ℝ) / (P.q.factorial : ℝ)) ^ (edges φ).card *
      (1 / (P.NA : ℝ)) * ((k : ℝ) / P.Nact) := by positivity
  have hfac : (0 : ℝ) ≤ (((P.N - (fixedPos U (.inl j)).card -
      Fintype.card {i // wEmb hφ i ∉ fixedPos U (.inl j)}).factorial : ℕ) : ℝ) /
      ((P.N - (fixedPos U (.inl j)).card).factorial : ℝ) := by positivity
  have key : ((Fintype.card K ^ (P.r - (I₀ (fixedPos U (.inl j)) (wEmb hφ)).card) : ℕ) -
      (((P.q ^ 2 + P.q * (fixedPos U (.inl j)).card) *
        Fintype.card K ^ (P.r - (I₀ (fixedPos U (.inl j)) (wEmb hφ)).card - 1) : ℕ) : ℝ)) *
      ((((P.N - (fixedPos U (.inl j)).card -
        Fintype.card {i // wEmb hφ i ∉ fixedPos U (.inl j)}).factorial : ℕ) : ℝ) /
        ((P.N - (fixedPos U (.inl j)).card).factorial : ℝ)) ≤
      (((Yc (fixedPos U (.inl j)) (v (.inl j)) κ M (wEmb hφ)).card *
        (P.N - (fixedPos U (.inl j)).card -
          Fintype.card {i // wEmb hφ i ∉ fixedPos U (.inl j)}).factorial : ℕ) : ℝ) /
        ((P.N - (fixedPos U (.inl j)).card).factorial : ℝ) := by
    refine (mul_le_mul_of_nonneg_right hY' hfac).trans (le_of_eq ?_)
    push_cast
    ring
  calc _ = ((Fintype.card K ^ (P.r - (I₀ (fixedPos U (.inl j)) (wEmb hφ)).card) : ℕ) -
        (((P.q ^ 2 + P.q * (fixedPos U (.inl j)).card) *
          Fintype.card K ^ (P.r - (I₀ (fixedPos U (.inl j)) (wEmb hφ)).card - 1) : ℕ) : ℝ)) *
        ((((P.N - (fixedPos U (.inl j)).card -
          Fintype.card {i // wEmb hφ i ∉ fixedPos U (.inl j)}).factorial : ℕ) : ℝ) /
          ((P.N - (fixedPos U (.inl j)).card).factorial : ℝ)) *
        ((1 / (P.z : ℝ)) ^ (edges φ).card *
        (((P.q - P.r).factorial : ℝ) / (P.q.factorial : ℝ)) ^ (edges φ).card *
        (1 / (P.NA : ℝ)) * ((k : ℝ) / P.Nact)) := by ring
    _ ≤ _ := by
        have := mul_le_mul_of_nonneg_right key hpos
        convert this using 1
        ring

end TParams


/-! ### The conditional mean outside the degenerate event -/

namespace TParams

variable {P : TParams}

open Classical in
/-- The lower bound of `probG_copyOK_cond_ge`. -/
noncomputable def passLB (U : Finset (Fin P.n)) (j : Fin P.z) {φ : Fin P.q → Fin P.n}
    (hφ : Function.Injective φ) (k : ℕ) : ℝ :=
  (((Fintype.card K ^ (P.r - (I₀ (fixedPos U (.inl j)) (wEmb hφ)).card) : ℕ) : ℝ) -
      (((P.q ^ 2 + P.q * (fixedPos U (.inl j)).card) *
        Fintype.card K ^ (P.r - (I₀ (fixedPos U (.inl j)) (wEmb hφ)).card - 1) : ℕ) : ℝ)) *
      (((P.N - (fixedPos U (.inl j)).card -
        Fintype.card {i // wEmb hφ i ∉ fixedPos U (.inl j)}).factorial : ℕ) : ℝ) /
        ((P.N - (fixedPos U (.inl j)).card).factorial : ℝ) *
      (1 / (P.z : ℝ)) ^ (edges φ).card *
      (((P.q - P.r).factorial : ℝ) / (P.q.factorial : ℝ)) ^ (edges φ).card *
      (1 / (P.NA : ℝ)) * ((k : ℝ) / P.Nact)

omit [Field F] [Field K] [Algebra F K] [Fintype K] [DecidableEq K] in
open Classical in
theorem I₀_fixedPos (U : Finset (Fin P.n)) (j : Fin P.z) {φ : Fin P.q → Fin P.n}
    (hφ : Function.Injective φ) :
    I₀ (fixedPos U (.inl j)) (wEmb hφ) = univ.filter fun i => φ i ∈ U := by
  ext i
  unfold I₀
  rw [mem_filter, mem_filter]
  simp only [mem_univ, true_and]
  exact mem_map' (Fin.castLEEmb P.hnN)

/-- Colour `j` is non-degenerate for `v` at the fixed vertices `u`. -/
def GoodCol (κ : Fin P.N ≃ K) {s : ℕ} (u : Fin s ↪ Fin P.n)
    (v : ∀ c, fixedPos (univ.map u) c ↪ Fin (P.size c)) (j : Fin P.z) : Prop :=
  LinearIndependent F fun t => κ (v (.inl j) ⟨Fin.castLE P.hnN (u t),
    mem_map_of_mem (Fin.castLEEmb P.hnN) (mem_map_of_mem u (mem_univ t))⟩)

omit [Fintype K] [DecidableEq K] in
open Classical in
/-- **The revealed values at the fixed vertices of a copy are independent** for a
non-degenerate colour. -/
theorem cval_indep_of_good (κ : Fin P.N ≃ K) {s : ℕ} (u : Fin s ↪ Fin P.n)
    (v : ∀ c, fixedPos (univ.map u) c ↪ Fin (P.size c)) {j : Fin P.z}
    (hj : GoodCol (F := F) κ u v j) {φ : Fin P.q → Fin P.n} (hφ : Function.Injective φ) :
    LinearIndependent F fun t : Fin (I₀ (fixedPos (univ.map u) (.inl j)) (wEmb hφ)).card =>
      cval (fixedPos (univ.map u) (.inl j)) (v (.inl j)) κ (wEmb hφ)
        ((I₀ (fixedPos (univ.map u) (.inl j)) (wEmb hφ)).orderEmbOfFin rfl t) := by
  set S := fixedPos (univ.map u) (.inl j)
  set I := I₀ S (wEmb hφ)
  set e := I.orderEmbOfFin rfl
  have hmem : ∀ t, wEmb hφ (e t) ∈ S := fun t => by
    have := I.orderEmbOfFin_mem rfl t
    simp only [I, I₀, mem_filter] at this
    exact this.2
  have hex : ∀ t, ∃ t', u t' = φ (e t) := fun t => by
    have h := mem_map.1 (hmem t)
    obtain ⟨x, hx, hxe⟩ := h
    obtain ⟨t', -, ht'⟩ := mem_map.1 hx
    exact ⟨t', ht'.trans (Fin.castLE_injective P.hnN hxe)⟩
  choose g hg using hex
  have hginj : Function.Injective g := fun t t' h =>
    e.injective (hφ (by rw [← hg t, ← hg t', h]))
  convert hj.comp g hginj using 1
  funext t
  simp only [Function.comp, cval]
  split_ifs with h
  · congr 2
    exact Subtype.ext (show Fin.castLE P.hnN (φ (e t)) = Fin.castLE P.hnN (u (g t)) by rw [hg t])
  · exact absurd (hmem t) h

omit [Fintype K] [DecidableEq K] in
open Classical in
/-- Injective colourings by non-degenerate colours. -/
theorem card_good_inj_ge (κ : Fin P.N ≃ K) {s : ℕ} (u : Fin s ↪ Fin P.n) (kd m : ℕ)
    (v : ∀ c, fixedPos (univ.map u) c ↪ Fin (P.size c))
    (hv : ¬ DegBad (F := F) κ u kd v) :
    (P.z + 1 - kd).descFactorial m ≤
      (univ.filter fun j : Fin m → Fin P.z =>
        Function.Injective j ∧ ∀ i, GoodCol (F := F) κ u v (j i)).card := by
  have h1 := card_filter_add_card_filter_not (s := (univ : Finset (Fin P.z)))
    (fun j => GoodCol (F := F) κ u v j)
  rw [card_univ, Fintype.card_fin] at h1
  have h2 : (univ.filter fun j : Fin P.z => ¬ GoodCol (F := F) κ u v j).card < kd := by
    have h := hv
    unfold DegBad at h
    push Not at h
    convert h using 3
    exact Iff.rfl
  set G := univ.filter fun j : Fin P.z => GoodCol (F := F) κ u v j
  have hG : P.z + 1 - kd ≤ G.card := by omega
  calc (P.z + 1 - kd).descFactorial m ≤ G.card.descFactorial m := Nat.descFactorial_le _ hG
    _ = Fintype.card (Fin m ↪ G) := by simp
    _ ≤ _ := by
        refine card_le_card_of_injOn (fun e i => (e i : Fin P.z)) (fun e _ => ?_) ?_
        · refine mem_filter.2 ⟨mem_univ _, fun i i' h => e.injective (Subtype.ext h), fun i => ?_⟩
          exact (mem_filter.1 (e i).2).2
        · intro e _ e' _ h
          ext i
          exact congrArg Fin.val (congrFun h i)

open Classical in
/-- **The conditional mean of the covering count outside the degenerate event**: at least
`∑_b (z+1-kd)_m · #T_b · p^m`, if every candidate copy passes with conditional probability
`≥ passLB ≥ p` and meets the fixed set in at most `r - 1` vertices. -/
theorem meanG_ext_ge {M : Matrix (Fin P.q) (Fin P.r) F} (hM : IsGeneric M)
    (hrows : DistinctRows M) (κ : Fin P.N ≃ K) (a₀ : (Fin P.q → Fin P.n) → Fin P.NA)
    (k : (Fin P.q → Fin P.n) → ℕ) (hk : ∀ ψ, k ψ ≤ P.Nact) {s : ℕ} (u : Fin s ↪ Fin P.n)
    (kd : ℕ) (v : ∀ c, fixedPos (univ.map u) c ↪ Fin (P.size c))
    (hv : ¬ DegBad (F := F) κ u kd v)
    {β : Type*} {m : ℕ} (C : Finset β) (e : β → Fin m → Finset (Fin P.n))
    (Q : β → Fin m → (Fin P.q → Fin P.n) → Prop)
    (T : β → Finset (Fin m → Fin P.q → Fin P.n))
    (hT : ∀ b ∈ C, ∀ φ ∈ T b, (∀ i, Function.Injective (φ i)) ∧ (∀ i, e b i ∈ edges (φ i) ∧ Q b i (φ i)) ∧
      Function.Injective φ ∧ ∀ i i', i ≠ i' → Disjoint (edges (φ i)) (edges (φ i')))
    (hTU : ∀ b ∈ C, ∀ φ ∈ T b, ∀ i,
      (univ.filter fun l => φ i l ∈ univ.map u).card + 1 ≤ P.r)
    {p : ℝ} (hp0 : 0 ≤ p)
    (hp : ∀ b ∈ C, ∀ φ ∈ T b, ∀ i (j : Fin P.z) (hφ : Function.Injective (φ i)),
      p ≤ passLB (K := K) (univ.map u) j hφ (k (φ i))) :
    ∑ b ∈ C, ((P.z + 1 - kd).descFactorial m : ℝ) * (T b).card * p ^ m ≤
      meanG (a := fun c => P.size c - (fixedPos (univ.map u) c).card)
        (fun τ => countVar C (fun b ω => CoverEv M κ a₀ k (e b) (Q b) ω)
          (liftPi (fixedPos (univ.map u)) v τ)) := by
  set J := univ.filter fun j : Fin m → Fin P.z =>
    Function.Injective j ∧ ∀ i, GoodCol (F := F) κ u v (j i)
  have hmean := meanG_cover_ge (fixedPos (univ.map u)) v hM κ a₀ k C e Q T hT (fun _ => J)
    (fun b _ j hj => (mem_filter.1 hj).2.1) hp0 fun b hb j hj φ hφ i => by
      obtain ⟨hinj, -, -, -⟩ := hT b hb φ hφ
      refine (hp b hb φ hφ i (j i) (hinj i)).trans ?_
      refine probG_copyOK_cond_ge hM hrows κ (j i) (a₀ (φ i)) (hk (φ i)) (hinj i) _ v ?_ ?_
      · rw [I₀_fixedPos]; exact hTU b hb φ hφ i
      · exact cval_indep_of_good κ u v ((mem_filter.1 hj).2.2 i) (hinj i)
  refine le_trans (sum_le_sum fun b _ => ?_) hmean
  refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ (by positivity))
    (by positivity)
  exact_mod_cast card_good_inj_ge κ u kd m v hv

end TParams


/-! ### Lemma `ext*` on the template space -/

namespace TParams

variable {P : TParams}

open Classical in
/-- **Lemma `ext*` (template space).** For fixed vertices `u`, configurations `b ∈ C` with edges
`e b i ⊇ F i` (`F i ⊆ u`, `|F i| ≤ r - 1`) and edge-disjoint candidate tuples `T b` of copies
meeting `u` in at most `r - 1` vertices, each passing with conditional probability `≥ p`, the
number `X` of configurations all of whose edges are covered by passing copies satisfies
`P(X < ∑_b (z+1-kd)_m #T_b p^m - t₁ - t₂) ≤ C(z,kd) p_deg^kd + 2e^{-t₁²/2B₁} + 2e^{-t₂²/2B₂}`. -/
theorem ext_star {M : Matrix (Fin P.q) (Fin P.r) F} (hM : IsGeneric M)
    (hrows : DistinctRows M) (κ : Fin P.N ≃ K) (a₀ : (Fin P.q → Fin P.n) → Fin P.NA)
    (k : (Fin P.q → Fin P.n) → ℕ) (hk : ∀ ψ, k ψ ≤ P.Nact) {s : ℕ} (u : Fin s ↪ Fin P.n)
    (kd : ℕ) {β : Type*} {m : ℕ} (C : Finset β) (e : β → Fin m → Finset (Fin P.n))
    (Q : β → Fin m → (Fin P.q → Fin P.n) → Prop)
    (Fx : Fin m → Finset (Fin P.n)) (hFU : ∀ i, Fx i ⊆ univ.map u)
    (hF : ∀ b ∈ C, ∀ i, Fx i ⊆ e b i) (hFr : ∀ i, (Fx i).card + 1 ≤ P.r) (D : Fin m → ℕ)
    (hD : ∀ i (e' : Finset (Fin P.n)), (C.filter fun b => e b i = e').card ≤ D i)
    (T : β → Finset (Fin m → Fin P.q → Fin P.n))
    (hT : ∀ b ∈ C, ∀ φ ∈ T b, (∀ i, Function.Injective (φ i)) ∧ (∀ i, e b i ∈ edges (φ i) ∧ Q b i (φ i)) ∧
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
        countVar C (fun b ω => CoverEv M κ a₀ k (e b) (Q b) ω) ω <
          ∑ b ∈ C, ((P.z + 1 - kd).descFactorial m : ℝ) * (T b).card * p ^ m - (t₁ + t₂)) ≤
      (P.z.choose kd : ℝ) * ratio (DegPerm (F := F) κ u) ^ kd +
        (2 * Real.exp (-(t₁ ^ 2 / (2 * B₁))) + 2 * Real.exp (-(t₂ ^ 2 / (2 * B₂)))) := by
  refine (cover_lower_tail hM κ a₀ k C e Q (univ.map u) Fx hFU hF hFr D hD hSmax
    (DegBad (F := F) κ u kd)
    (fun v hv => meanG_ext_ge hM hrows κ a₀ k hk u kd v hv C e Q T hT hTU hp0 hp)
    hB₁ hB₂ hB₁0 hB₂0 ht₁ ht₂).trans ?_
  gcongr
  exact probG_degBad_le κ u kd

end TParams

end DesignsII
