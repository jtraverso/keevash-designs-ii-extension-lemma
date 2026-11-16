/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import DesignsII.ExtCert
public import DesignsII.TwoStage
public import DesignsII.Stage2Cert

/-!
# Concentration of the covering count of Lemma `ext*` (two stages)

Stage 1 reveals the colour coordinates `f_j`; stage 2 the coordinates `T`, `π`, `A` and the
activations. Given the colours, only the *relevant* coordinates matter: those read by a copy
`ψ` that is `f_j`-compatible for some colour `j` (`Relevant`). Every passing copy is compatible,
so the covering events only depend on the colours and the relevant coordinates
(`coverEv_iff_of_agree_rel`); in the second stage the count therefore depends on at most
`z · |K|^r · (2 C(q,r) + 2)` coordinates (`card_relSet_le`).
-/

@[expose] public section

namespace DesignsII

open Finset Equiv

variable {F K : Type*} [Field F] [Field K] [Algebra F K] [Fintype K] [DecidableEq K]

namespace TParams

variable {P : TParams} (M : Matrix (Fin P.q) (Fin P.r) F) (κ : Fin P.N ≃ K)
  (a₀ : (Fin P.q → Fin P.n) → Fin P.NA) (k : (Fin P.q → Fin P.n) → ℕ)

/-- A coordinate read by the tests of a copy compatible with some colour. -/
def Relevant (ω : P.Ω) (c : P.Coord) : Prop :=
  ∃ ψ : Fin P.q → Fin P.n, Function.Injective ψ ∧ ∃ j,
    (∃ y, ∀ i, κ (fval ω j (ψ i)) = mvec M y i) ∧
      ∃ p, (⟨c, p⟩ : Σ c : P.Coord, Fin (P.size c)) ∈ copyDeps j ψ

omit [Fintype K] [DecidableEq K] in
/-- Relevance only depends on the colours. -/
theorem relevant_congr {ω ω' : P.Ω} (hcol : ∀ j, ω (.inl j) = ω' (.inl j)) (c : P.Coord) :
    Relevant M κ ω c ↔ Relevant M κ ω' c := by
  have : ∀ j x, fval ω j x = fval ω' j x := fun j x => by unfold fval; rw [hcol j]
  simp only [Relevant, this]

omit [Fintype K] [DecidableEq K] in
theorem coverEv_of_agree_rel {m : ℕ} (e : Fin m → Finset (Fin P.n)) (Q : Fin m → (Fin P.q → Fin P.n) → Prop) {ω ω' : P.Ω}
    (hcol : ∀ j, ω (.inl j) = ω' (.inl j)) (hrel : ∀ c, Relevant M κ ω c → ω c = ω' c)
    (h : CoverEv M κ a₀ k e Q ω) : CoverEv M κ a₀ k e Q ω' := by
  intro i
  obtain ⟨ψ, hinj, he, j, hok⟩ := h i
  refine ⟨ψ, hinj, he, j, copyOK_of_agree M κ j (a₀ ψ) (k ψ) ψ (fun cp hcp => ?_) hok⟩
  obtain ⟨c, pp⟩ := cp
  rcases c with j' | c'
  · simp [hcol j']
  · exact congrFun (congrArg DFunLike.coe (hrel _ ⟨ψ, hinj, j, hok.2.2.2.2, pp, hcp⟩)) pp

omit [Fintype K] [DecidableEq K] in
/-- **The covering events only depend on the colours and the relevant coordinates.** -/
theorem coverEv_iff_of_agree_rel {m : ℕ} (e : Fin m → Finset (Fin P.n)) (Q : Fin m → (Fin P.q → Fin P.n) → Prop) {ω ω' : P.Ω}
    (hcol : ∀ j, ω (.inl j) = ω' (.inl j)) (hrel : ∀ c, Relevant M κ ω c → ω c = ω' c) :
    CoverEv M κ a₀ k e Q ω ↔ CoverEv M κ a₀ k e Q ω' :=
  ⟨coverEv_of_agree_rel M κ a₀ k e Q hcol hrel,
    coverEv_of_agree_rel M κ a₀ k e Q (fun j => (hcol j).symm)
      fun c hc => (hrel c ((relevant_congr M κ hcol c).2 hc)).symm⟩

end TParams

namespace TParams

variable {P : TParams}

open Classical in
/-- **Few relevant coordinates**: at most `z · |K|^r · (2 C(q,r) + 2)` non-colour coordinates are
read by colour-compatible copies. -/
theorem card_relSet_le {M : Matrix (Fin P.q) (Fin P.r) F} (hM : IsGeneric M) (κ : Fin P.N ≃ K)
    (ω : P.Ω) :
    (univ.filter fun c : P.Coord => c.isLeft = false ∧ Relevant M κ ω c).card ≤
      P.z * (Fintype.card K ^ P.r * (2 * P.q.choose P.r + 2)) := by
  set Cand : Fin P.z → Finset (Fin P.q → Fin P.n) := fun j => univ.filter fun ψ =>
    (∃ y, ∀ i, κ (fval ω j (ψ i)) = mvec M y i) ∧ (∅ : Finset (Fin P.n)) ⊆ univ.image ψ
  set NC : (Fin P.q → Fin P.n) → Finset P.Coord := fun ψ =>
    ((edges ψ).image fun e => (.inr (.inl e) : P.Coord)) ∪
      ((edges ψ).image fun e => (.inr (.inr (.inl e)) : P.Coord)) ∪
        {.inr (.inr (.inr (.inl ψ))), .inr (.inr (.inr (.inr ψ)))}
  have hsub : (univ.filter fun c : P.Coord => c.isLeft = false ∧ Relevant M κ ω c) ⊆
      univ.biUnion fun j => (Cand j).biUnion NC := by
    intro c hc
    obtain ⟨hl, ψ, -, j, hcomp, pp, hcp⟩ := (mem_filter.1 hc).2
    refine mem_biUnion.2 ⟨j, mem_univ _, mem_biUnion.2 ⟨ψ,
      mem_filter.2 ⟨mem_univ _, hcomp, empty_subset _⟩, ?_⟩⟩
    rcases mem_copyDeps_fst hcp with ⟨jj, hj⟩ | ⟨e, he, hce | hce⟩ | hA | hA
    · simp only at hj; subst hj; simp at hl
    · simp only at hce; subst hce
      exact mem_union_left _ (mem_union_left _ (mem_image_of_mem _ he))
    · simp only at hce; subst hce
      exact mem_union_left _ (mem_union_right _ (mem_image_of_mem _ he))
    · simp only at hA; subst hA; simp [NC]
    · simp only at hA; subst hA; simp [NC]
  have hedges : ∀ ψ : Fin P.q → Fin P.n, (edges ψ).card ≤ P.q.choose P.r := fun ψ => by
    rw [edges, card_powersetCard]
    exact Nat.choose_le_choose _ (card_image_le.trans (by simp))
  have hNC : ∀ ψ, (NC ψ).card ≤ 2 * P.q.choose P.r + 2 := fun ψ => by
    refine (card_union_le _ _).trans ?_
    refine (add_le_add (card_union_le _ _) card_le_two).trans ?_
    have := hedges ψ
    linarith [card_image_le (s := edges ψ) (f := fun e => (.inr (.inl e) : P.Coord)),
      card_image_le (s := edges ψ) (f := fun e => (.inr (.inr (.inl e)) : P.Coord))]
  have hCand : ∀ j, (Cand j).card ≤ Fintype.card K ^ P.r := fun j => by
    have h := card_cand_supset_le hM P.hrq (fval_injective ω κ j) ∅ (by simp)
    simpa [Cand] using h
  refine (card_le_card hsub).trans (card_biUnion_le.trans ?_)
  calc ∑ j, ((Cand j).biUnion NC).card
      ≤ ∑ _j : Fin P.z, Fintype.card K ^ P.r * (2 * P.q.choose P.r + 2) := by
        refine sum_le_sum fun j _ => card_biUnion_le.trans ?_
        calc ∑ ψ ∈ Cand j, (NC ψ).card ≤ ∑ _ψ ∈ Cand j, (2 * P.q.choose P.r + 2) :=
              sum_le_sum fun ψ _ => hNC ψ
          _ = (Cand j).card * (2 * P.q.choose P.r + 2) := by rw [sum_const, smul_eq_mul]
          _ ≤ _ := Nat.mul_le_mul_right _ (hCand j)
    _ = _ := by rw [sum_const, card_univ, Fintype.card_fin, smul_eq_mul]

end TParams


/-! ### The second stage in the conditioned space -/

namespace TParams

variable {P : TParams} (M : Matrix (Fin P.q) (Fin P.r) F) (κ : Fin P.N ≃ K)
  (a₀ : (Fin P.q → Fin P.n) → Fin P.NA) (k : (Fin P.q → Fin P.n) → ℕ)
  (S : ∀ c : P.Coord, Finset (Fin (P.size c))) (v : ∀ c, S c ↪ Fin (P.size c))

/-- The colour coordinates (first stage). -/
abbrev IsCol (c : P.Coord) : Prop := c.isLeft = true

omit [Field F] [Field K] [Algebra F K] [Fintype K] [DecidableEq K] in
theorem liftPi_merge_col
    (ω₁ : Ω₁ (a := fun c : P.Coord => P.size c - (S c).card) IsCol)
    (σ σ' : Ω₂ (a := fun c : P.Coord => P.size c - (S c).card) IsCol) (j : Fin P.z) :
    liftPi S v (merge ω₁ σ) (.inl j) = liftPi S v (merge ω₁ σ') (.inl j) := by
  simp only [liftPi, merge, dif_pos (show IsCol (Sum.inl j : P.Coord) from rfl)]

omit [Fintype K] [DecidableEq K] in
open Classical in
/-- **The second stage only depends on the relevant coordinates.** -/
theorem depends_cover_stage₂ {β : Type*} {m : ℕ} (C : Finset β) (e : β → Fin m → Finset (Fin P.n))
    (Q : β → Fin m → (Fin P.q → Fin P.n) → Prop)
    (ω₁ : Ω₁ (a := fun c : P.Coord => P.size c - (S c).card) IsCol) :
    DependsFirstG (a := fun c : {c // ¬ IsCol c} => P.size c.1 - (S c.1).card)
      (fun ω₂ => countVar C (fun b ω => CoverEv M κ a₀ k (e b) (Q b) ω) (liftPi S v (merge ω₁ ω₂)))
      (fun c => if Relevant M κ (liftPi S v (merge ω₁ 1)) c.1 then P.size c.1 - (S c.1).card
        else 0) := by
  intro σ τ h
  have hcol := liftPi_merge_col S v ω₁ σ τ
  have hrel : ∀ c, Relevant M κ (liftPi S v (merge ω₁ σ)) c →
      liftPi S v (merge ω₁ σ) c = liftPi S v (merge ω₁ τ) c := by
    intro c hc
    by_cases hp : IsCol c
    · rcases c with j | c
      · exact hcol j
      · cases hp
    · have hc' : Relevant M κ (liftPi S v (merge ω₁ 1)) c :=
        (relevant_congr M κ (liftPi_merge_col S v ω₁ σ 1) c).1 hc
      have hστ : σ ⟨c, hp⟩ = τ ⟨c, hp⟩ :=
        Equiv.ext fun x => h ⟨c, hp⟩ x (by simp only [hc', ↓reduceIte]; exact x.2)
      simp [liftPi, merge, hp, hστ]
  have key : ∀ b, CoverEv M κ a₀ k (e b) (Q b) (liftPi S v (merge ω₁ σ)) ↔
      CoverEv M κ a₀ k (e b) (Q b) (liftPi S v (merge ω₁ τ)) := fun b =>
    coverEv_iff_of_agree_rel M κ a₀ k (e b) (Q b) hcol hrel
  simp only [countVar, key]

end TParams


/-! ### The two-stage tail bound for the covering count -/

namespace TParams

variable {P : TParams} (S : ∀ c : P.Coord, Finset (Fin (P.size c))) (v : ∀ c, S c ↪ Fin (P.size c))

open Classical in
/-- **Concentration of the covering count of `ext*`** in the space conditioned on the values `v`
at the positions `S`. The hypotheses are uniform witness bounds: `Lf` at colour positions outside
`S`, `Lo` at all other positions (`card_wit_f_le`, `card_wit_other_le`). The first stage (colours)
has variance proxy `z N (2 Lf)²`; the second stage uses constants `Lc ω c` depending only on the
colours (`stage₂_lipschitz_cert`), with proxy `Smax ∑_c (2 Lc ω c)²` (bounded by
`stage₂_proxy_le` for `Lc = LcC`). -/
theorem cover_two_stage_tail {M : Matrix (Fin P.q) (Fin P.r) F} (hM : IsGeneric M)
    (κ : Fin P.N ≃ K) (a₀ : (Fin P.q → Fin P.n) → Fin P.NA) (k : (Fin P.q → Fin P.n) → ℕ)
    {β : Type*} {m : ℕ} (C : Finset β) (e : β → Fin m → Finset (Fin P.n))
    (Q : β → Fin m → (Fin P.q → Fin P.n) → Prop) {Lf Lo : ℝ}
    (hLf0 : 0 ≤ Lf) (hLo0 : 0 ≤ Lo)
    (hLf : ∀ (ω : P.Ω) (j : Fin P.z) (p : Fin (P.size (.inl j))), p ∉ S (.inl j) →
      ((C.filter fun b => CoverEv M κ a₀ k (e b) (Q b) ω ∧
        (⟨.inl j, p⟩ : Σ c : P.Coord, Fin (P.size c)) ∈ coverCert M κ a₀ k (e b) (Q b) ω).card : ℝ) ≤ Lf)
    (hLo : ∀ (ω : P.Ω) (c : P.Coord) (p : Fin (P.size c)), c.isLeft = false →
      ((C.filter fun b => CoverEv M κ a₀ k (e b) (Q b) ω ∧
        (⟨c, p⟩ : Σ c : P.Coord, Fin (P.size c)) ∈ coverCert M κ a₀ k (e b) (Q b) ω).card : ℝ) ≤ Lo)
    {Lc : P.Ω → P.Coord → ℝ} (hLc0 : ∀ ω c, 0 ≤ Lc ω c)
    (hLc : ∀ (ω : P.Ω) (c : P.Coord) (p : Fin (P.size c)), c.isLeft = false →
      ((C.filter fun b => CoverEv M κ a₀ k (e b) (Q b) ω ∧
        (⟨c, p⟩ : Σ c : P.Coord, Fin (P.size c)) ∈ coverCert M κ a₀ k (e b) (Q b) ω).card : ℝ) ≤
          Lc ω c)
    (hLcol : ∀ ω ω' : P.Ω, (∀ j, ω (.inl j) = ω' (.inl j)) → Lc ω = Lc ω')
    {Smax : ℕ} (hSmax : ∀ c : P.Coord, c.isLeft = false → P.size c ≤ Smax)
    {B₁ B₂ t₁ t₂ : ℝ} (hB₁ : (P.z : ℝ) * P.N * (2 * Lf) ^ 2 ≤ B₁)
    (hB₂ : ∀ ω : P.Ω, (Smax : ℝ) *
      ∑ c : P.Coord, (if c.isLeft = false then (2 * Lc ω c) ^ 2 else 0) ≤ B₂)
    (hB₁0 : 0 < B₁) (hB₂0 : 0 < B₂) (ht₁ : 0 < t₁) (ht₂ : 0 < t₂) :
    probG (a := fun c => P.size c - (S c).card) (fun τ => t₁ + t₂ <
        |countVar C (fun b ω => CoverEv M κ a₀ k (e b) (Q b) ω) (liftPi S v τ) -
          meanG (a := fun c => P.size c - (S c).card)
            (fun τ => countVar C (fun b ω => CoverEv M κ a₀ k (e b) (Q b) ω) (liftPi S v τ))|) ≤
      2 * Real.exp (-(t₁ ^ 2 / (2 * B₁))) + 2 * Real.exp (-(t₂ ^ 2 / (2 * B₂))) := by
  set a' : P.Coord → ℕ := fun c => P.size c - (S c).card
  set X : (∀ c, Perm (Fin (a' c))) → ℝ :=
    fun τ => countVar C (fun b ω => CoverEv M κ a₀ k (e b) (Q b) ω) (liftPi S v τ)
  set L : P.Coord → ℝ := fun c => if IsCol c then Lf else Lo
  have hL0 : ∀ c, 0 ≤ L c := fun c => by
    simp only [L]; split_ifs <;> assumption
  have hX : IsLipschitzG (a := a') X (fun c => 2 * L c) := by
    refine cond_countVar_lipschitz_cert S v C _ (fun b ω => coverCert M κ a₀ k (e b) (Q b) ω)
      (fun b _ ω ω' h hag => coverEv_of_agree M κ a₀ k (e b) (Q b) h hag) L fun ω c p hp => ?_
    rcases c with j | c
    · simp only [L, IsCol, Sum.isLeft_inl, if_true]; convert hLf ω j p hp
    · simp only [L, IsCol, Sum.isLeft_inr, Bool.false_eq_true, if_false]; convert hLo ω (.inr c) p rfl
  have hXD : DependsFirstG (a := a') X a' := fun σ τ h => by
    have : σ = τ := funext fun c => Equiv.ext fun x => h c x x.2
    rw [this]
  refine two_stage_lip_tail (p := IsCol) X (fun c => if IsCol c then 2 * L c else 0)
    (fun c => by split_ifs <;> [linarith [hL0 c]; exact le_rfl])
    (fun c => if IsCol c then a' c else 0) (lipschitz_condMean hX) (depends_condMean hXD)
    ?_ hB₁0 (fun ω₁ => ?_) hB₂0 ht₁ ht₂
  · -- first stage
    refine le_trans ?_ hB₁
    rw [Fintype.sum_sum_type]
    simp only [IsCol, Sum.isLeft_inl, Sum.isLeft_inr, if_true, L, Bool.false_eq_true,
      if_false, CharP.cast_eq_zero, zero_mul, sum_const_zero, add_zero]
    calc ∑ j : Fin P.z, ((a' (.inl j) : ℕ) : ℝ) * (2 * Lf) ^ 2
        ≤ ∑ _j : Fin P.z, (P.N : ℝ) * (2 * Lf) ^ 2 := by
          refine sum_le_sum fun j _ => mul_le_mul_of_nonneg_right ?_ (by positivity)
          exact_mod_cast Nat.sub_le _ _
      _ = _ := by rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
  · -- second stage: constants depending on the colours
    obtain ⟨ωs, hωs⟩ : ∃ ωs, ωs = liftPi S v (merge ω₁ 1) := ⟨_, rfl⟩
    have hLs : ∀ ω₂ (c : {c : P.Coord // ¬ IsCol c}), Lc (liftPi S v (merge ω₁ ω₂)) c.1 = Lc ωs c.1 :=
      fun ω₂ c => congrFun (hLcol _ _ (by rw [hωs]; exact liftPi_merge_col S v ω₁ ω₂ 1)) c.1
    refine ⟨fun c => 2 * Lc ωs c.1, fun c => P.size c.1 - (S c.1).card,
      fun c => by linarith [hLc0 ωs c.1], ?_, ?_, ?_⟩
    · refine stage₂_lipschitz_cert S v C _ (fun b ω => coverCert M κ a₀ k (e b) (Q b) ω)
        (fun b _ ω ω' h hag => coverEv_of_agree M κ a₀ k (e b) (Q b) h hag) ω₁
        (fun c => Lc ωs c.1) fun ω₂ c pp hp => ?_
      have hc : c.1.isLeft = false := by simpa [IsCol] using c.2
      rw [← hLs ω₂ c]
      convert hLc (liftPi S v (merge ω₁ ω₂)) c.1 pp hc
    · intro σ τ h
      have : σ = τ := funext fun c => Equiv.ext fun x => h c x x.2
      rw [this]
    · refine le_trans ?_ (hB₂ ωs)
      calc ∑ c : {c : P.Coord // ¬ IsCol c},
            ((P.size c.1 - (S c.1).card : ℕ) : ℝ) * (2 * Lc ωs c.1) ^ 2
          ≤ ∑ c : {c : P.Coord // ¬ IsCol c}, (Smax : ℝ) * (2 * Lc ωs c.1) ^ 2 := by
            refine sum_le_sum fun c _ => mul_le_mul_of_nonneg_right ?_ (by positivity)
            have hc : c.1.isLeft = false := by simpa [IsCol] using c.2
            exact_mod_cast (Nat.sub_le _ _).trans (hSmax c.1 hc)
        _ = (Smax : ℝ) * ∑ c ∈ univ.filter (fun c : P.Coord => ¬ IsCol c), (2 * Lc ωs c) ^ 2 := by
            rw [mul_sum]
            exact (Finset.sum_subtype (univ.filter fun c : P.Coord => ¬ IsCol c)
              (fun c => by simp) (fun c => (Smax : ℝ) * (2 * Lc ωs c) ^ 2)).symm
        _ = _ := by
            rw [sum_filter]
            congr 1
            refine sum_congr rfl fun c _ => ?_
            simp [IsCol]

end TParams


/-! ### Colour-dependent second-stage constants -/

namespace TParams

variable {P : TParams} (M : Matrix (Fin P.q) (Fin P.r) F) (κ : Fin P.N ≃ K)

/-- `ψ` is injective and compatible with colour `j`. -/
def CompatC (ω : P.Ω) (j : Fin P.z) (ψ : Fin P.q → Fin P.n) : Prop :=
  Function.Injective ψ ∧ ∃ y, ∀ i, κ (fval ω j (ψ i)) = mvec M y i

open Classical in
/-- The compatible copies reading coordinate `c`. -/
noncomputable def Wc (ω : P.Ω) (c : P.Coord) : Finset (Fin P.z × (Fin P.q → Fin P.n)) :=
  univ.filter fun x => CompatC M κ ω x.1 x.2 ∧
    ∃ pp, (⟨c, pp⟩ : Σ c : P.Coord, Fin (P.size c)) ∈ copyDeps x.1 x.2

open Classical in
/-- The configurations having an edge in `ψ`, counted with multiplicity over `i`. -/
noncomputable def gC {β : Type*} {m : ℕ} (C : Finset β) (e : β → Fin m → Finset (Fin P.n))
    (ψ : Fin P.q → Fin P.n) : ℕ :=
  ∑ i, (C.filter fun b => e b i ∈ edges ψ).card

/-- The second-stage constant at `c`. -/
noncomputable def LcC {β : Type*} {m : ℕ} (C : Finset β) (e : β → Fin m → Finset (Fin P.n))
    (ω : P.Ω) (c : P.Coord) : ℝ :=
  ∑ x ∈ Wc M κ ω c, (gC C e x.2 : ℝ)

omit [Fintype K] [DecidableEq K] in
open Classical in
theorem Wc_congr {ω ω' : P.Ω} (hcol : ∀ j, ω (.inl j) = ω' (.inl j)) :
    Wc M κ ω = Wc M κ ω' := by
  have : ∀ j x, fval ω j x = fval ω' j x := fun j x => by unfold fval; rw [hcol j]
  funext c
  unfold Wc
  exact Finset.filter_congr fun x _ => by simp only [CompatC, this]

omit [Fintype K] [DecidableEq K] in
open Classical in
/-- **Witness count at any position ≤ `LcC`.** -/
theorem card_wit_le_LcC (a₀ : (Fin P.q → Fin P.n) → Fin P.NA) (k : (Fin P.q → Fin P.n) → ℕ)
    {β : Type*} {m : ℕ} (C : Finset β) (e : β → Fin m → Finset (Fin P.n))
    (Q : β → Fin m → (Fin P.q → Fin P.n) → Prop) (ω : P.Ω) (c : P.Coord) (pp : Fin (P.size c)) :
    ((C.filter fun b => CoverEv M κ a₀ k (e b) (Q b) ω ∧
      (⟨c, pp⟩ : Σ c : P.Coord, Fin (P.size c)) ∈ coverCert M κ a₀ k (e b) (Q b) ω).card : ℝ) ≤
      LcC M κ C e ω c := by
  have hsub : (C.filter fun b => CoverEv M κ a₀ k (e b) (Q b) ω ∧
      (⟨c, pp⟩ : Σ c : P.Coord, Fin (P.size c)) ∈ coverCert M κ a₀ k (e b) (Q b) ω) ⊆
      (Wc M κ ω c).biUnion fun x => univ.biUnion fun i => C.filter fun b => e b i ∈ edges x.2 := by
    intro b hb
    obtain ⟨hbC, hcov, hmem⟩ := mem_filter.1 hb
    unfold coverCert at hmem
    rw [dif_pos hcov] at hmem
    obtain ⟨i, -, hi⟩ := mem_biUnion.1 hmem
    obtain ⟨hinj, he, hj⟩ := Classical.choose_spec (hcov i)
    have hok := Classical.choose_spec hj
    refine mem_biUnion.2 ⟨(Classical.choose hj, Classical.choose (hcov i)),
      mem_filter.2 ⟨mem_univ _, ⟨hinj, hok.2.2.2.2⟩, pp, hi⟩,
      mem_biUnion.2 ⟨i, mem_univ _, mem_filter.2 ⟨hbC, he.1⟩⟩⟩
  unfold LcC gC
  refine (Nat.cast_le.2 ((card_le_card hsub).trans card_biUnion_le)).trans ?_
  push_cast
  exact sum_le_sum fun x _ => by exact_mod_cast card_biUnion_le

open Classical in
/-- Compatible copies (any colour) having a given `r`-set as an edge: at most `z q^r`. -/
theorem card_compat_edge_le {M : Matrix (Fin P.q) (Fin P.r) F} (hM : IsGeneric M)
    (κ : Fin P.N ≃ K) (ω : P.Ω) (e₀ : Finset (Fin P.n)) :
    (univ.filter fun x : Fin P.z × (Fin P.q → Fin P.n) =>
      CompatC M κ ω x.1 x.2 ∧ e₀ ∈ edges x.2).card ≤ P.z * P.q ^ P.r := by
  rw [card_filter, Fintype.sum_prod_type]
  calc ∑ j : Fin P.z, ∑ ψ : Fin P.q → Fin P.n,
        (if CompatC M κ ω j ψ ∧ e₀ ∈ edges ψ then 1 else 0)
      ≤ ∑ _j : Fin P.z, P.q ^ P.r := by
        refine sum_le_sum fun j _ => ?_
        rw [← card_filter]
        by_cases he : e₀.card = P.r
        · have h := card_cand_supset_le hM P.hrq (fval_injective ω κ j) e₀ he.le
          rw [he, Nat.sub_self, pow_zero, mul_one] at h
          refine le_trans (card_le_card fun ψ hψ => ?_) h
          obtain ⟨⟨-, hc⟩, hed⟩ := (mem_filter.1 hψ).2
          exact mem_filter.2 ⟨mem_univ _, hc, (mem_powersetCard.1 hed).1⟩
        · rw [filter_false_of_mem fun ψ _ h => he (mem_powersetCard.1 h.2).2, card_empty]
          exact Nat.zero_le _
    _ = P.z * P.q ^ P.r := by rw [sum_const, card_univ, Fintype.card_fin, smul_eq_mul]

end TParams


namespace TParams

variable {P : TParams} {M : Matrix (Fin P.q) (Fin P.r) F} (κ : Fin P.N ≃ K)

omit [Field F] [Field K] [Algebra F K] [Fintype K] [DecidableEq K] in
theorem reads_cases {c : P.Coord} {j : Fin P.z} {ψ : Fin P.q → Fin P.n} {pp : Fin (P.size c)}
    (h : (⟨c, pp⟩ : Σ c : P.Coord, Fin (P.size c)) ∈ copyDeps j ψ) :
    (∃ jj, c = .inl jj) ∨ (∃ e ∈ edges ψ, c = .inr (.inl e) ∨ c = .inr (.inr (.inl e))) ∨
      c = .inr (.inr (.inr (.inl ψ))) ∨ c = .inr (.inr (.inr (.inr ψ))) :=
  mem_copyDeps_fst h

open Classical in
/-- **Few compatible copies read a non-colour coordinate.** -/
theorem card_Wc_le (hM : IsGeneric M) (ω : P.Ω) (c : P.Coord) (hc : c.isLeft = false) :
    (Wc M κ ω c).card ≤ P.z * P.q ^ P.r + P.z := by
  rcases c with j | e₀ | e₀ | ψ₀ | ψ₀
  · simp at hc
  · refine (card_le_card fun x hx => ?_).trans ((card_compat_edge_le hM κ ω e₀).trans
      (Nat.le_add_right _ _))
    obtain ⟨hcomp, pp, h⟩ := (mem_filter.1 hx).2
    refine mem_filter.2 ⟨mem_univ _, hcomp, ?_⟩
    rcases reads_cases h with ⟨jj, hj⟩ | ⟨e, he, hce | hce⟩ | hA | hA
    · simp at hj
    · simp only [Sum.inr.injEq, Sum.inl.injEq] at hce; rw [hce]; exact he
    · simp at hce
    · simp at hA
    · simp at hA
  · refine (card_le_card fun x hx => ?_).trans ((card_compat_edge_le hM κ ω e₀).trans
      (Nat.le_add_right _ _))
    obtain ⟨hcomp, pp, h⟩ := (mem_filter.1 hx).2
    refine mem_filter.2 ⟨mem_univ _, hcomp, ?_⟩
    rcases reads_cases h with ⟨jj, hj⟩ | ⟨e, he, hce | hce⟩ | hA | hA
    · simp at hj
    · simp at hce
    · simp only [Sum.inr.injEq, Sum.inl.injEq] at hce; rw [hce]; exact he
    · simp at hA
    · simp at hA
  all_goals
    refine (card_le_card (t := univ.image fun j : Fin P.z => (j, ψ₀)) fun x hx => ?_).trans
      (card_image_le.trans (by simp))
    obtain ⟨-, pp, h⟩ := (mem_filter.1 hx).2
    refine mem_image.2 ⟨x.1, mem_univ _, ?_⟩
    rcases reads_cases h with ⟨jj, hj⟩ | ⟨e, he, hce | hce⟩ | hA | hA
    all_goals first
      | (simp at hj) | (simp at hce)
      | (simp only [Sum.inr.injEq, Sum.inl.injEq, reduceCtorEq] at hA; rw [hA])
      | (simp at hA)

end TParams


namespace TParams

variable {P : TParams} {M : Matrix (Fin P.q) (Fin P.r) F} (κ : Fin P.N ≃ K)

omit [Field F] [Field K] [Algebra F K] [Fintype K] [DecidableEq K] in
open Classical in
/-- A copy reads at most `2 C(q,r) + 2` non-colour coordinates. -/
theorem card_reads_le (j : Fin P.z) (ψ : Fin P.q → Fin P.n) :
    (univ.filter fun c : P.Coord => c.isLeft = false ∧
      ∃ pp, (⟨c, pp⟩ : Σ c : P.Coord, Fin (P.size c)) ∈ copyDeps j ψ).card ≤
      2 * P.q.choose P.r + 2 := by
  set NC : Finset P.Coord :=
    ((edges ψ).image fun e => (.inr (.inl e) : P.Coord)) ∪
      ((edges ψ).image fun e => (.inr (.inr (.inl e)) : P.Coord)) ∪
        {.inr (.inr (.inr (.inl ψ))), .inr (.inr (.inr (.inr ψ)))}
  have hsub : (univ.filter fun c : P.Coord => c.isLeft = false ∧
      ∃ pp, (⟨c, pp⟩ : Σ c : P.Coord, Fin (P.size c)) ∈ copyDeps j ψ) ⊆ NC := by
    intro c hc
    obtain ⟨hl, pp, h⟩ := (mem_filter.1 hc).2
    rcases reads_cases h with ⟨jj, hj⟩ | ⟨e, he, hce | hce⟩ | hA | hA
    · subst hj; simp at hl
    · subst hce; exact mem_union_left _ (mem_union_left _ (mem_image_of_mem _ he))
    · subst hce; exact mem_union_left _ (mem_union_right _ (mem_image_of_mem _ he))
    · subst hA; simp [NC]
    · subst hA; simp [NC]
  have hedges : (edges ψ).card ≤ P.q.choose P.r := by
    rw [edges, card_powersetCard]
    exact Nat.choose_le_choose _ (card_image_le.trans (by simp))
  refine (card_le_card hsub).trans ((card_union_le _ _).trans ?_)
  refine (add_le_add (card_union_le _ _) card_le_two).trans ?_
  linarith [card_image_le (s := edges ψ) (f := fun e => (.inr (.inl e) : P.Coord)),
    card_image_le (s := edges ψ) (f := fun e => (.inr (.inr (.inl e)) : P.Coord))]

omit [Fintype K] [DecidableEq K] in
theorem gC_le {β : Type*} {m : ℕ} (C : Finset β) (e : β → Fin m → Finset (Fin P.n))
    (D : Fin m → ℕ) (hD : ∀ i (e' : Finset (Fin P.n)), (C.filter fun b => e b i = e').card ≤ D i)
    (ψ : Fin P.q → Fin P.n) : gC C e ψ ≤ ∑ i, P.q.choose P.r * D i :=
  sum_le_sum fun i _ => card_edge_in_copy_le C e D hD i ψ

/-- **The maximal second-stage constant.** -/
theorem LcC_le (hM : IsGeneric M) {β : Type*} {m : ℕ} (C : Finset β)
    (e : β → Fin m → Finset (Fin P.n)) (D : Fin m → ℕ)
    (hD : ∀ i (e' : Finset (Fin P.n)), (C.filter fun b => e b i = e').card ≤ D i)
    (ω : P.Ω) (c : P.Coord) (hc : c.isLeft = false) :
    LcC M κ C e ω c ≤ (((P.z * P.q ^ P.r + P.z) * ∑ i, P.q.choose P.r * D i : ℕ) : ℝ) := by
  unfold LcC
  calc ∑ x ∈ Wc M κ ω c, (gC C e x.2 : ℝ)
      ≤ ∑ _x ∈ Wc M κ ω c, ((∑ i, P.q.choose P.r * D i : ℕ) : ℝ) :=
        sum_le_sum fun x _ => by exact_mod_cast gC_le C e D hD x.2
    _ = (Wc M κ ω c).card * ((∑ i, P.q.choose P.r * D i : ℕ) : ℝ) := by
        rw [sum_const, nsmul_eq_mul]
    _ ≤ _ := by
        push_cast
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast card_Wc_le κ hM ω c hc)
          (by positivity)

open Classical in
/-- **The total second-stage constant**: `∑_c L_c ≤ (2C(q,r)+2) · m · |C| · z q^r`. -/
theorem sum_LcC_le (hM : IsGeneric M) {β : Type*} {m : ℕ} (C : Finset β)
    (e : β → Fin m → Finset (Fin P.n)) (ω : P.Ω) :
    ∑ c : P.Coord, (if c.isLeft = false then LcC M κ C e ω c else 0) ≤
      (((2 * P.q.choose P.r + 2) * (m * C.card * (P.z * P.q ^ P.r)) : ℕ) : ℝ) := by
  set g : Fin P.z × (Fin P.q → Fin P.n) → ℕ := fun x => gC C e x.2
  set Pc : P.Coord → Fin P.z × (Fin P.q → Fin P.n) → Prop := fun c x =>
    CompatC M κ ω x.1 x.2 ∧ ∃ pp, (⟨c, pp⟩ : Σ c : P.Coord, Fin (P.size c)) ∈ copyDeps x.1 x.2
  have h1 : ∀ c, (if c.isLeft = false then LcC M κ C e ω c else 0) =
      ((∑ x, if c.isLeft = false ∧ Pc c x then g x else 0 : ℕ) : ℝ) := by
    intro c
    unfold LcC Wc
    rw [← Nat.cast_sum, sum_filter]
    split_ifs with hc
    · push_cast
      refine sum_congr rfl fun x _ => ?_
      simp only [Pc, hc, true_and]
      split_ifs <;> simp [g]
    · simp [hc]
  rw [sum_congr rfl fun c _ => h1 c, ← Nat.cast_sum]
  norm_cast
  rw [sum_comm]
  have h2 : ∀ x, (∑ c, if c.isLeft = false ∧ Pc c x then g x else 0) ≤
      if CompatC M κ ω x.1 x.2 then (2 * P.q.choose P.r + 2) * g x else 0 := by
    intro x
    split_ifs with hx
    · rw [← sum_filter, sum_const, smul_eq_mul]
      refine Nat.mul_le_mul_right _ ((card_le_card fun c hc => ?_).trans (card_reads_le x.1 x.2))
      obtain ⟨hl, -, hr⟩ := (mem_filter.1 hc).2
      exact mem_filter.2 ⟨mem_univ _, hl, hr⟩
    · exact (sum_eq_zero fun c _ => by simp [Pc, hx]).le
  refine (sum_le_sum fun x _ => h2 x).trans ?_
  have h3 : (∑ x : Fin P.z × (Fin P.q → Fin P.n),
      if CompatC M κ ω x.1 x.2 then (2 * P.q.choose P.r + 2) * g x else 0) =
      (2 * P.q.choose P.r + 2) * ∑ x : Fin P.z × (Fin P.q → Fin P.n),
        if CompatC M κ ω x.1 x.2 then g x else 0 := by
    rw [mul_sum]; refine sum_congr rfl fun x _ => ?_; split_ifs <;> simp
  rw [h3]
  refine Nat.mul_le_mul_left _ ?_
  have h4 : (∑ x : Fin P.z × (Fin P.q → Fin P.n), if CompatC M κ ω x.1 x.2 then g x else 0) =
      ∑ i : Fin m, ∑ b ∈ C, (univ.filter fun x : Fin P.z × (Fin P.q → Fin P.n) =>
        CompatC M κ ω x.1 x.2 ∧ e b i ∈ edges x.2).card := by
    simp only [g, gC, card_filter]
    calc (∑ x : Fin P.z × (Fin P.q → Fin P.n), if CompatC M κ ω x.1 x.2 then
          ∑ i : Fin m, ∑ b ∈ C, (if e b i ∈ edges x.2 then 1 else 0) else 0)
        = ∑ x : Fin P.z × (Fin P.q → Fin P.n), ∑ i : Fin m, ∑ b ∈ C,
            (if CompatC M κ ω x.1 x.2 ∧ e b i ∈ edges x.2 then 1 else 0) :=
          sum_congr rfl fun x _ => by
            by_cases h : CompatC M κ ω x.1 x.2 <;> simp [h]
      _ = ∑ i : Fin m, ∑ x : Fin P.z × (Fin P.q → Fin P.n), ∑ b ∈ C,
            (if CompatC M κ ω x.1 x.2 ∧ e b i ∈ edges x.2 then 1 else 0) := sum_comm
      _ = _ := sum_congr rfl fun i _ => sum_comm
  rw [h4]
  calc ∑ i : Fin m, ∑ b ∈ C, (univ.filter fun x : Fin P.z × (Fin P.q → Fin P.n) =>
        CompatC M κ ω x.1 x.2 ∧ e b i ∈ edges x.2).card
      ≤ ∑ _i : Fin m, ∑ _b ∈ C, P.z * P.q ^ P.r :=
        sum_le_sum fun i _ => sum_le_sum fun b _ => card_compat_edge_le hM κ ω (e b i)
    _ = m * C.card * (P.z * P.q ^ P.r) := by
        rw [sum_const, sum_const, card_univ, Fintype.card_fin, smul_eq_mul, smul_eq_mul]; ring

/-- **The second-stage variance proxy**: `Smax ∑_c (2L_c)² ≤ 4 Smax · max L · ∑ L`. -/
theorem stage₂_proxy_le (hM : IsGeneric M) {β : Type*} {m : ℕ} (C : Finset β)
    (e : β → Fin m → Finset (Fin P.n)) (D : Fin m → ℕ)
    (hD : ∀ i (e' : Finset (Fin P.n)), (C.filter fun b => e b i = e').card ≤ D i)
    (Smax : ℕ) (ω : P.Ω) :
    (Smax : ℝ) * ∑ c : P.Coord, (if c.isLeft = false then (2 * LcC M κ C e ω c) ^ 2 else 0) ≤
      4 * Smax * (((P.z * P.q ^ P.r + P.z) * ∑ i, P.q.choose P.r * D i : ℕ) : ℝ) *
        (((2 * P.q.choose P.r + 2) * (m * C.card * (P.z * P.q ^ P.r)) : ℕ) : ℝ) := by
  set Lmax := (((P.z * P.q ^ P.r + P.z) * ∑ i, P.q.choose P.r * D i : ℕ) : ℝ)
  have h0 : ∀ c, 0 ≤ LcC M κ C e ω c := fun c => sum_nonneg fun _ _ => by positivity
  have hterm : ∀ c : P.Coord, (if c.isLeft = false then (2 * LcC M κ C e ω c) ^ 2 else 0) ≤
      4 * Lmax * (if c.isLeft = false then LcC M κ C e ω c else 0) := by
    intro c
    split_ifs with hc
    · have := LcC_le κ hM C e D hD ω c hc
      nlinarith [h0 c]
    · simp
  calc (Smax : ℝ) * ∑ c : P.Coord, (if c.isLeft = false then (2 * LcC M κ C e ω c) ^ 2 else 0)
      ≤ Smax * ∑ c : P.Coord, 4 * Lmax * (if c.isLeft = false then LcC M κ C e ω c else 0) :=
        mul_le_mul_of_nonneg_left (sum_le_sum fun c _ => hterm c) (by positivity)
    _ = 4 * Smax * Lmax * ∑ c : P.Coord, (if c.isLeft = false then LcC M κ C e ω c else 0) := by
        rw [← mul_sum]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (sum_LcC_le κ hM C e ω) (by positivity)

end TParams


/-! ### Instantiation at the fixed vertices -/

namespace TParams

variable {P : TParams}

omit [Field F] [Field K] [Algebra F K] [Fintype K] [DecidableEq K] in
/-- Colour positions read by the tests are values `castLE x`, so they lie below `n`. -/
theorem copyDeps_inl_lt {j j' : Fin P.z} {ψ : Fin P.q → Fin P.n} {p : Fin (P.size (.inl j))}
    (h : (⟨.inl j, p⟩ : Σ c : P.Coord, Fin (P.size c)) ∈ copyDeps j' ψ) : (p : ℕ) < P.n := by
  simp only [copyDeps, mem_union, mem_image, mem_univ, true_and, mem_insert, mem_singleton,
    mem_product] at h
  rcases h with (⟨i, hi⟩ | ⟨e, -, he⟩) | (⟨ex, -, hex⟩ | h | h)
  · rw [Sigma.mk.inj_iff] at hi
    obtain ⟨h1, h2⟩ := hi
    cases h1
    have := eq_of_heq h2
    rw [← this]
    exact (ψ i).isLt
  · exact absurd (congrArg Sigma.fst he) (by simp)
  · exact absurd (congrArg Sigma.fst hex) (by simp)
  · exact absurd (congrArg Sigma.fst h) (by simp)
  · exact absurd (congrArg Sigma.fst h) (by simp)

open Classical in
/-- **Concentration of the covering count of `ext*` given the colours at the fixed vertices
`U`.** Here `Fx i ⊆ U` are the fixed vertices of the `i`-th edge of every configuration and `D i`
bounds the number of configurations with a given `i`-th edge. -/
theorem cover_tail_fixed {M : Matrix (Fin P.q) (Fin P.r) F} (hM : IsGeneric M)
    (κ : Fin P.N ≃ K) (a₀ : (Fin P.q → Fin P.n) → Fin P.NA) (k : (Fin P.q → Fin P.n) → ℕ)
    {β : Type*} {m : ℕ} (C : Finset β) (e : β → Fin m → Finset (Fin P.n))
    (Q : β → Fin m → (Fin P.q → Fin P.n) → Prop)
    (U : Finset (Fin P.n)) (v : ∀ c, fixedPos U c ↪ Fin (P.size c))
    (Fx : Fin m → Finset (Fin P.n)) (hFU : ∀ i, Fx i ⊆ U) (hF : ∀ b ∈ C, ∀ i, Fx i ⊆ e b i)
    (hFr : ∀ i, (Fx i).card + 1 ≤ P.r) (D : Fin m → ℕ)
    (hD : ∀ i (e' : Finset (Fin P.n)), (C.filter fun b => e b i = e').card ≤ D i)
    {Smax : ℕ} (hSmax : ∀ c : P.Coord, c.isLeft = false → P.size c ≤ Smax)
    {B₁ B₂ t₁ t₂ : ℝ}
    (hB₁ : (P.z : ℝ) * P.N * (2 * ((∑ i, P.q ^ ((Fx i).card + 1) *
      Fintype.card K ^ (P.r - ((Fx i).card + 1)) * (P.q.choose P.r * D i) : ℕ) : ℝ)) ^ 2 ≤ B₁)
    (hB₂ : 4 * (Smax : ℝ) * (((P.z * P.q ^ P.r + P.z) * ∑ i, P.q.choose P.r * D i : ℕ) : ℝ) *
      (((2 * P.q.choose P.r + 2) * (m * C.card * (P.z * P.q ^ P.r)) : ℕ) : ℝ) ≤ B₂)
    (hB₁0 : 0 < B₁) (hB₂0 : 0 < B₂) (ht₁ : 0 < t₁) (ht₂ : 0 < t₂) :
    probG (a := fun c => P.size c - (fixedPos U c).card) (fun τ => t₁ + t₂ <
        |countVar C (fun b ω => CoverEv M κ a₀ k (e b) (Q b) ω) (liftPi (fixedPos U) v τ) -
          meanG (a := fun c => P.size c - (fixedPos U c).card)
            (fun τ => countVar C (fun b ω => CoverEv M κ a₀ k (e b) (Q b) ω)
              (liftPi (fixedPos U) v τ))|) ≤
      2 * Real.exp (-(t₁ ^ 2 / (2 * B₁))) + 2 * Real.exp (-(t₂ ^ 2 / (2 * B₂))) := by
  refine cover_two_stage_tail (fixedPos U) v hM κ a₀ k C e Q (by positivity) (by positivity)
    (fun ω j p hp => ?_) (fun ω c p hc => ?_) (Lc := LcC M κ C e)
    (Lo := ((∑ i, P.q.choose P.r * D i : ℕ) : ℝ))
    (fun ω c => sum_nonneg fun _ _ => by positivity)
    (fun ω c p _ => card_wit_le_LcC M κ a₀ k C e Q ω c p)
    (fun ω ω' h => by unfold LcC; rw [Wc_congr M κ h]) hSmax hB₁
    (fun ω => (stage₂_proxy_le κ hM C e D hD Smax ω).trans hB₂) hB₁0 hB₂0 ht₁ ht₂
  · by_cases hpn : (p : ℕ) < P.n
    · set x : Fin P.n := ⟨p, hpn⟩
      have hpx : p = Fin.castLE P.hnN x := Fin.ext rfl
      have hx : x ∉ U := fun hxU => hp (by
        rw [hpx]
        exact mem_map_of_mem (Fin.castLEEmb P.hnN) hxU)
      rw [hpx]
      exact_mod_cast card_wit_f_le hM κ a₀ k C e Q Fx hF hFr D hD ω j x
        fun i hxi => hx (hFU i hxi)
    · have : (C.filter fun b => CoverEv M κ a₀ k (e b) (Q b) ω ∧
          (⟨.inl j, p⟩ : Σ c : P.Coord, Fin (P.size c)) ∈ coverCert M κ a₀ k (e b) (Q b) ω) = ∅ := by
        refine filter_false_of_mem fun b _ ⟨hcov, hmem⟩ => hpn ?_
        unfold coverCert at hmem
        rw [dif_pos hcov] at hmem
        obtain ⟨i, -, hi⟩ := mem_biUnion.1 hmem
        exact copyDeps_inl_lt hi
      rw [this, card_empty, Nat.cast_zero]
      positivity
  · rcases c with j | c
    · simp at hc
    · exact_mod_cast card_wit_other_le hM κ a₀ k C e Q D hD ω ⟨.inr c, p⟩
        fun jj h => Sum.inr_ne_inl h

end TParams

end DesignsII
