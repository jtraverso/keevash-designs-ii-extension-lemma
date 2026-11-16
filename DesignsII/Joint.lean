/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import DesignsII.TemplateSpace

/-!
# Independence of template events on disjoint coordinates

* `probG_pi`: an event that is a conjunction of events on the individual coordinates has
  probability `∏_c P(E_c)`;
* `probG_forall_indep`: if every coordinate is constrained by at most one of the events
  `E_1, …, E_m`, then `P(E_1 ∧ … ∧ E_m) = ∏ P(E_i)`;
* `probG_copyOK_joint`: copies `φ_1, …, φ_m` with pairwise distinct colours `j_i`, pairwise
  distinct maps and pairwise disjoint edge sets pass their template tests independently.

This replaces the conditioning on local events in the proof of Lemma `ext*` (Designs II, §3.3):
for a lower bound on the probability that prescribed edges are covered by the template with
prescribed atoms, it suffices to sum, over distinct colours and edge-disjoint covering copies,
the exact product probabilities (the corresponding events are disjoint by
`template_edge_unique`).
-/

@[expose] public section

namespace DesignsII

open Finset Equiv

section General

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {a : ι → ℕ}

/-- The probability of a coordinate event `E` on `Perm (Fin m)`. -/
noncomputable def ratio {m : ℕ} (E : Perm (Fin m) → Prop) : ℝ := by
  classical
  exact ((univ.filter E).card : ℝ) / (m.factorial : ℝ)

theorem probG_pi (E : ∀ c, Perm (Fin (a c)) → Prop) :
    probG (a := a) (fun ω => ∀ c, E c (ω c)) = ∏ c, ratio (E c) := by
  classical
  unfold probG ratio
  rw [prod_div_distrib]
  congr 1
  rw [← Nat.cast_prod]
  congr 1
  convert card_pi_filter E using 2
  ext ω; simp

theorem ratio_true' {m : ℕ} (E : Perm (Fin m) → Prop) (h : ∀ σ, E σ) : ratio E = 1 := by
  classical
  unfold ratio
  rw [filter_true_of_mem fun σ _ => h σ, card_univ, Fintype.card_perm, Fintype.card_fin]
  exact div_self (by exact_mod_cast (Nat.factorial_pos m).ne')

theorem ratio_congr {m : ℕ} {E E' : Perm (Fin m) → Prop} (h : ∀ σ, E σ ↔ E' σ) :
    ratio E = ratio E' := by
  have : E = E' := funext fun σ => propext (h σ)
  rw [this]

theorem ratio_forall_single {m k : ℕ} (E : Fin k → Perm (Fin m) → Prop)
    (h : ∀ i i', i ≠ i' → (∀ σ, E i σ) ∨ ∀ σ, E i' σ) :
    ratio (fun σ => ∀ i, E i σ) = ∏ i, ratio (E i) := by
  by_cases hex : ∃ i₀, ¬ ∀ σ, E i₀ σ
  · obtain ⟨i₀, hi₀⟩ := hex
    have htriv : ∀ i ≠ i₀, ∀ σ, E i σ := fun i hi => (h i i₀ hi).resolve_right hi₀
    rw [← mul_prod_erase univ _ (mem_univ i₀),
      prod_eq_one fun i hi => ratio_true' _ (htriv i (ne_of_mem_erase hi)), mul_one]
    refine ratio_congr fun σ => ⟨fun hσ => hσ i₀, fun hσ i => ?_⟩
    by_cases hi : i = i₀
    · exact hi ▸ hσ
    · exact htriv i hi σ
  · push Not at hex
    rw [ratio_true' _ fun σ i => hex i σ, prod_eq_one fun i _ => ratio_true' _ (hex i)]

/-- **Independence**: if each coordinate is constrained by at most one of the events, the
probability of the conjunction is the product of the probabilities. -/
theorem probG_forall_indep {k : ℕ} (E : Fin k → ∀ c, Perm (Fin (a c)) → Prop)
    (h : ∀ c i i', i ≠ i' → (∀ σ, E i c σ) ∨ ∀ σ, E i' c σ) :
    probG (a := a) (fun ω => ∀ i c, E i c (ω c)) =
      ∏ i, probG (a := a) (fun ω => ∀ c, E i c (ω c)) := by
  have h1 : probG (a := a) (fun ω => ∀ i c, E i c (ω c)) =
      probG (a := a) (fun ω => ∀ c, ∀ i, E i c (ω c)) := by
    congr 1
    funext ω
    exact propext ⟨fun hω c i => hω i c, fun hω i c => hω c i⟩
  rw [h1, probG_pi (fun c σ => ∀ i, E i c σ)]
  simp_rw [probG_pi]
  rw [prod_comm]
  exact prod_congr rfl fun c _ => ratio_forall_single (fun i => E i c) (h c)

end General

namespace TParams

variable {P : TParams} {F K : Type*} [Field F] [Field K] [Algebra F K] [Fintype K]
  [DecidableEq K]

omit [Fintype K] [DecidableEq K] in
/-- **Joint probability for edge-disjoint copies with distinct colours.** -/
theorem probG_copyOK_joint {m : ℕ} (M : Matrix (Fin P.q) (Fin P.r) F) (κ : Fin P.N ≃ K)
    (j : Fin m → Fin P.z) (a₀ : Fin m → Fin P.NA) (k : Fin m → ℕ)
    (φ : Fin m → Fin P.q → Fin P.n) (hj : Function.Injective j) (hφ : Function.Injective φ)
    (hdisj : ∀ i i', i ≠ i' → Disjoint (edges (φ i)) (edges (φ i'))) :
    probG (a := P.size) (fun ω => ∀ i, CopyOK M κ (j i) (a₀ i) (k i) (φ i) ω) =
      ∏ i, probG (a := P.size) (CopyOK M κ (j i) (a₀ i) (k i) (φ i)) := by
  have hiff : ∀ i, CopyOK M κ (j i) (a₀ i) (k i) (φ i) =
      fun ω => ∀ c, copyEv M κ (j i) (a₀ i) (k i) (φ i) c (ω c) :=
    fun i => funext fun ω => propext (copyOK_iff _ _ _ _ _ _ ω)
  simp_rw [hiff]
  refine probG_forall_indep (fun i c => copyEv M κ (j i) (a₀ i) (k i) (φ i) c)
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

end TParams


section Disjoint

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {a : ι → ℕ}

/-- The probability of a union of pairwise disjoint events is the sum of the probabilities. -/
theorem probG_exists_disjoint {β : Type*} (S : Finset β) (A : β → (∀ c, Perm (Fin (a c))) → Prop)
    (hdisj : ∀ b ∈ S, ∀ b' ∈ S, b ≠ b' → ∀ ω, A b ω → A b' ω → False) :
    probG (a := a) (fun ω => ∃ b ∈ S, A b ω) = ∑ b ∈ S, probG (a := a) (A b) := by
  classical
  unfold probG
  rw [← sum_div]
  congr 1
  rw [← Nat.cast_sum]
  congr 1
  rw [← card_biUnion]
  · congr 1
    ext ω
    simp
  · intro b hb b' hb' hbb
    rw [Function.onFun, disjoint_left]
    intro ω h1 h2
    simp only [mem_filter, mem_univ, true_and] at h1 h2
    exact hdisj b hb b' hb' hbb ω h1 h2

end Disjoint

namespace TParams

variable {P : TParams} {F K : Type*} [Field F] [Field K] [Algebra F K] [Fintype K]
  [DecidableEq K]

omit [Fintype K] [DecidableEq K] in
/-- **Two copies passing the template tests and sharing an edge coincide** (Lemma 3.3 of Designs I
applied to the template space). -/
theorem copyOK_unique {M : Matrix (Fin P.q) (Fin P.r) F} (hM : IsGeneric M) (κ : Fin P.N ≃ K)
    {j j' : Fin P.z} {a₀ a₀' : Fin P.NA} {k k' : ℕ} {φ φ' : Fin P.q → Fin P.n}
    (hφ : Function.Injective φ) {ω : P.Ω} (h : CopyOK M κ j a₀ k φ ω)
    (h' : CopyOK M κ j' a₀' k' φ' ω) {e : Finset (Fin P.n)} (he : e ∈ edges φ)
    (he' : e ∈ edges φ') : φ = φ' := by
  classical
  rcases Nat.eq_zero_or_pos P.q with hq | hq
  · funext i; exact absurd i.2 (by omega)
  set f : Fin P.z → Fin P.n → K := fun j x => κ (fval ω j x)
  have hf : ∀ j, Function.Injective (f j) := fun j x y hxy =>
    Fin.castLE_injective P.hnN ((ω (.inl j)).injective (κ.injective hxy))
  set π : Finset (Fin P.n) → Fin P.n → Fin P.q := fun e x => (pival ω e x).getD ⟨0, hq⟩
  have hJ : ∀ {j a k φ}, CopyOK M κ j a k φ ω → CompatJ M f (fun e => Tval ω e) j φ := by
    intro j a k φ hc
    refine ⟨fun e hcard hsub => hc.2.2.1 e (mem_powersetCard.2 ⟨hsub, hcard⟩), ?_⟩
    obtain ⟨y, hy⟩ := hc.2.2.2.2
    exact ⟨y, fun i => hy i⟩
  have hP : ∀ {j a k φ}, CopyOK M κ j a k φ ω → CompatPi (r := P.r) π φ := by
    intro j a k φ hc e hcard hsub i hi
    simp only [π, hc.2.2.2.1 e (mem_powersetCard.2 ⟨hsub, hcard⟩) i hi, Option.getD_some]
  exact template_disjoint hM hf hφ (hJ h) (hJ h') (hP h) (hP h')
    (mem_powersetCard.1 he).2 (mem_powersetCard.1 he).1 (mem_powersetCard.1 he').1

end TParams


section Mono

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {a : ι → ℕ}

theorem probG_mono {A B : (∀ c, Perm (Fin (a c))) → Prop} (h : ∀ ω, A ω → B ω) :
    probG (a := a) A ≤ probG (a := a) B := by
  classical
  unfold probG
  refine div_le_div_of_nonneg_right ?_ (prod_nonneg fun i _ => by positivity)
  exact_mod_cast card_le_card (monotone_filter_right _ fun ω _ hω => h ω hω)

end Mono

namespace TParams

variable {P : TParams} {F K : Type*} [Field F] [Field K] [Algebra F K] [Fintype K]
  [DecidableEq K]

omit [Fintype K] [DecidableEq K] in
/-- **Lower bound for covering prescribed edges by the template.** Let `e_1, …, e_m` be edges with
pairwise distinct colours `j_i`, and let `T` be a set of tuples `(φ_1, …, φ_m)` of injective maps
with `e_i ⊆ φ_i(Q)` (`e_i ∈ edges φ_i`), pairwise distinct and with pairwise disjoint edge sets.
Then the probability that every `e_i` is covered by a copy of colour `j_i` passing the template
tests is at least `∑_{(φ_i) ∈ T} ∏_i P(φ_i passes)`. -/
theorem probG_cover_ge {m : ℕ} {M : Matrix (Fin P.q) (Fin P.r) F} (hM : IsGeneric M)
    (κ : Fin P.N ≃ K) (j : Fin m → Fin P.z) (hj : Function.Injective j)
    (a₀ : (Fin P.q → Fin P.n) → Fin P.NA) (k : (Fin P.q → Fin P.n) → ℕ)
    (e : Fin m → Finset (Fin P.n)) (T : Finset (Fin m → Fin P.q → Fin P.n))
    (hT : ∀ φ ∈ T, (∀ i, Function.Injective (φ i)) ∧ (∀ i, e i ∈ edges (φ i)) ∧
      Function.Injective φ ∧ ∀ i i', i ≠ i' → Disjoint (edges (φ i)) (edges (φ i'))) :
    ∑ φ ∈ T, ∏ i, probG (a := P.size) (CopyOK M κ (j i) (a₀ (φ i)) (k (φ i)) (φ i)) ≤
      probG (a := P.size) (fun ω => ∀ i, ∃ ψ : Fin P.q → Fin P.n, Function.Injective ψ ∧
        e i ∈ edges ψ ∧ CopyOK M κ (j i) (a₀ ψ) (k ψ) ψ ω) := by
  calc ∑ φ ∈ T, ∏ i, probG (a := P.size) (CopyOK M κ (j i) (a₀ (φ i)) (k (φ i)) (φ i))
      = ∑ φ ∈ T, probG (a := P.size)
          (fun ω => ∀ i, CopyOK M κ (j i) (a₀ (φ i)) (k (φ i)) (φ i) ω) := by
        refine sum_congr rfl fun φ hφ => ?_
        obtain ⟨-, -, hinj, hdisj⟩ := hT φ hφ
        exact (probG_copyOK_joint M κ j (fun i => a₀ (φ i)) (fun i => k (φ i)) φ hj hinj
          hdisj).symm
    _ = probG (a := P.size)
          (fun ω => ∃ φ ∈ T, ∀ i, CopyOK M κ (j i) (a₀ (φ i)) (k (φ i)) (φ i) ω) := by
        refine (probG_exists_disjoint T _ fun φ hφ φ' hφ' hne ω h1 h2 => hne ?_).symm
        funext i
        exact copyOK_unique hM κ ((hT φ hφ).1 i) (h1 i) (h2 i) ((hT φ hφ).2.1 i)
          ((hT φ' hφ').2.1 i)
    _ ≤ _ := probG_mono fun ω ⟨φ, hφ, h⟩ i =>
        ⟨φ i, (hT φ hφ).1 i, (hT φ hφ).2.1 i, h i⟩

end TParams


namespace TParams

variable {P : TParams} {F K : Type*} [Field F] [Field K] [Algebra F K] [Fintype K]
  [DecidableEq K]

omit [Fintype K] [DecidableEq K] in
theorem copyOK_T {M : Matrix (Fin P.q) (Fin P.r) F} {κ : Fin P.N ≃ K} {j : Fin P.z}
    {a₀ : Fin P.NA} {k : ℕ} {φ : Fin P.q → Fin P.n} {ω : P.Ω}
    (h : CopyOK M κ j a₀ k φ ω) {e : Finset (Fin P.n)} (he : e ∈ edges φ) : Tval ω e = j :=
  h.2.2.1 e he

omit [Fintype K] [DecidableEq K] in
/-- **Lower bound for covering prescribed edges, any colours.** Summing `probG_cover_ge` over
injective colourings `j : [m] → [z]` (the events for different colourings are disjoint, as
`T_{e_i} = j_i`). -/
theorem probG_cover_colors_ge {m : ℕ} {M : Matrix (Fin P.q) (Fin P.r) F} (hM : IsGeneric M)
    (κ : Fin P.N ≃ K) (a₀ : (Fin P.q → Fin P.n) → Fin P.NA) (k : (Fin P.q → Fin P.n) → ℕ)
    (e : Fin m → Finset (Fin P.n)) (T : Finset (Fin m → Fin P.q → Fin P.n))
    (hT : ∀ φ ∈ T, (∀ i, Function.Injective (φ i)) ∧ (∀ i, e i ∈ edges (φ i)) ∧
      Function.Injective φ ∧ ∀ i i', i ≠ i' → Disjoint (edges (φ i)) (edges (φ i'))) :
    ∑ j ∈ univ.filter (fun j : Fin m → Fin P.z => Function.Injective j),
        ∑ φ ∈ T, ∏ i, probG (a := P.size) (CopyOK M κ (j i) (a₀ (φ i)) (k (φ i)) (φ i)) ≤
      probG (a := P.size) (fun ω => ∀ i, ∃ ψ : Fin P.q → Fin P.n, Function.Injective ψ ∧
        e i ∈ edges ψ ∧ ∃ j, CopyOK M κ j (a₀ ψ) (k ψ) ψ ω) := by
  classical
  calc _ ≤ ∑ j ∈ univ.filter (fun j : Fin m → Fin P.z => Function.Injective j),
        probG (a := P.size) (fun ω => ∀ i, ∃ ψ : Fin P.q → Fin P.n, Function.Injective ψ ∧
          e i ∈ edges ψ ∧ CopyOK M κ (j i) (a₀ ψ) (k ψ) ψ ω) :=
        sum_le_sum fun j hj => probG_cover_ge hM κ j (mem_filter.1 hj).2 a₀ k e T hT
    _ = probG (a := P.size) (fun ω => ∃ j ∈ univ.filter (fun j : Fin m → Fin P.z =>
          Function.Injective j), ∀ i, ∃ ψ : Fin P.q → Fin P.n, Function.Injective ψ ∧
          e i ∈ edges ψ ∧ CopyOK M κ (j i) (a₀ ψ) (k ψ) ψ ω) := by
        refine (probG_exists_disjoint _ _ fun j _ j' _ hne ω h1 h2 => hne ?_).symm
        funext i
        obtain ⟨ψ, -, he, hc⟩ := h1 i
        obtain ⟨ψ', -, he', hc'⟩ := h2 i
        exact (copyOK_T hc he).symm.trans (copyOK_T hc' he')
    _ ≤ _ := probG_mono fun ω ⟨j, _, h⟩ i => by
        obtain ⟨ψ, h1, h2, h3⟩ := h i
        exact ⟨ψ, h1, h2, j i, h3⟩

end TParams

end DesignsII
