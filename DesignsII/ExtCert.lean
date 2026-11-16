/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import DesignsII.CondCert
public import DesignsII.CandSet
public import DesignsII.CondCover

/-!
# Certificates for the covering events of Lemma `ext*`

For edges `e_1, …, e_m` the covering event `CoverEv e ω` says that every `e_i` lies in some copy
passing the template tests (any colour). Its certificate `coverCert e ω` is the set of positions
read by chosen witness copies (`copyDeps`); it certifies the event (`coverEv_of_agree`).

`card_wit_f_le`: at a position of `f_j` at a non-fixed vertex `x`, the number of configurations
`b` (with edges `e b i ⊇ F i`) whose certificate contains that position is at most
`∑_i q^{|F_i|+1} N^{r-|F_i|-1} · C(q,r) · D_i`, where `D_i` bounds the number of configurations
with a given `i`-th edge: a witness through `x` of colour `j` is an `f_j`-compatible copy whose
image contains `F_i ∪ {x}` (`card_cand_supset_le`).
-/

@[expose] public section

namespace DesignsII

open Finset Equiv

variable {F K : Type*} [Field F] [Field K] [Algebra F K] [Fintype K] [DecidableEq K]

namespace TParams

variable {P : TParams} (M : Matrix (Fin P.q) (Fin P.r) F) (κ : Fin P.N ≃ K)
  (a₀ : (Fin P.q → Fin P.n) → Fin P.NA) (k : (Fin P.q → Fin P.n) → ℕ)

/-- Every edge `e_i` is covered by a passing copy. -/
def CoverEv {m : ℕ} (e : Fin m → Finset (Fin P.n)) (Q : Fin m → (Fin P.q → Fin P.n) → Prop) (ω : P.Ω) : Prop :=
  ∀ i, ∃ ψ : Fin P.q → Fin P.n, Function.Injective ψ ∧ (e i ∈ edges ψ ∧ Q i ψ) ∧
    ∃ j, CopyOK M κ j (a₀ ψ) (k ψ) ψ ω

open Classical in
/-- The certificate: the positions read by chosen witnesses. -/
noncomputable def coverCert {m : ℕ} (e : Fin m → Finset (Fin P.n)) (Q : Fin m → (Fin P.q → Fin P.n) → Prop) (ω : P.Ω) :
    Finset (Σ c : P.Coord, Fin (P.size c)) :=
  if h : CoverEv M κ a₀ k e Q ω then
    univ.biUnion fun i => copyDeps (Classical.choose (Classical.choose_spec (h i)).2.2)
      (Classical.choose (h i))
  else ∅

omit [Fintype K] [DecidableEq K] in
/-- **The certificate certifies.** -/
theorem coverEv_of_agree {m : ℕ} (e : Fin m → Finset (Fin P.n)) (Q : Fin m → (Fin P.q → Fin P.n) → Prop) {ω ω' : P.Ω}
    (h : CoverEv M κ a₀ k e Q ω) (hag : AgreeAt (coverCert M κ a₀ k e Q ω) ω ω') :
    CoverEv M κ a₀ k e Q ω' := by
  classical
  intro i
  set ψ := Classical.choose (h i)
  obtain ⟨hinj, he, hj⟩ := Classical.choose_spec (h i)
  set j := Classical.choose hj
  have hok : CopyOK M κ j (a₀ ψ) (k ψ) ψ ω := Classical.choose_spec hj
  refine ⟨ψ, hinj, he, j, ?_⟩
  refine (copyOK_iff_of_agree M κ j (a₀ ψ) (k ψ) ψ fun cp hcp => hag cp ?_).1 hok
  unfold coverCert
  rw [dif_pos h]
  exact mem_biUnion.2 ⟨i, mem_univ _, hcp⟩

omit [Fintype K] [DecidableEq K] in
/-- An `f_j`-position in `copyDeps j' ψ` comes from a vertex of `ψ` and `j' = j`. -/
theorem mem_copyDeps_inl {j j' : Fin P.z} {ψ : Fin P.q → Fin P.n} {x : Fin P.n}
    (h : (⟨.inl j, Fin.castLE P.hnN x⟩ : Σ c : P.Coord, Fin (P.size c)) ∈ copyDeps j' ψ) :
    j = j' ∧ x ∈ univ.image ψ := by
  simp only [copyDeps, mem_union, mem_image, mem_univ, true_and, mem_insert, mem_singleton,
    mem_product] at h
  rcases h with (⟨i, hi⟩ | ⟨e, -, he⟩) | (⟨ex, -, hex⟩ | h | h)
  · rw [Sigma.mk.inj_iff] at hi
    obtain ⟨h1, h2⟩ := hi
    cases h1
    refine ⟨rfl, mem_image.2 ⟨i, mem_univ _, ?_⟩⟩
    exact Fin.castLE_injective P.hnN (eq_of_heq h2)
  · exact absurd (congrArg Sigma.fst he) (by simp)
  · exact absurd (congrArg Sigma.fst hex) (by simp)
  · exact absurd (congrArg Sigma.fst h) (by simp)
  · exact absurd (congrArg Sigma.fst h) (by simp)

end TParams


namespace TParams

variable {P : TParams}

theorem fval_injective (ω : P.Ω) (κ : Fin P.N ≃ K) (j : Fin P.z) :
    Function.Injective fun x => κ (fval ω j x) := fun x y h =>
  Fin.castLE_injective P.hnN ((ω (.inl j)).injective (κ.injective h))

omit [Fintype K] [DecidableEq K] in
/-- Configurations whose `i`-th edge lies in a given copy. -/
theorem card_edge_in_copy_le {β : Type*} {m : ℕ} (C : Finset β)
    (e : β → Fin m → Finset (Fin P.n)) (D : Fin m → ℕ)
    (hD : ∀ i (e' : Finset (Fin P.n)), (C.filter fun b => e b i = e').card ≤ D i)
    (i : Fin m) (ψ : Fin P.q → Fin P.n) :
    (C.filter fun b => e b i ∈ edges ψ).card ≤ P.q.choose P.r * D i := by
  classical
  calc _ ≤ ∑ e' ∈ edges ψ, (C.filter fun b => e b i = e').card := by
        rw [← card_biUnion]
        · exact card_le_card fun b hb => mem_biUnion.2 ⟨e b i, (mem_filter.1 hb).2,
            mem_filter.2 ⟨(mem_filter.1 hb).1, rfl⟩⟩
        · intro x _ y _ hxy
          rw [Function.onFun, disjoint_left]
          intro b h1 h2
          exact hxy ((mem_filter.1 h1).2.symm.trans (mem_filter.1 h2).2)
    _ ≤ ∑ _e' ∈ edges ψ, D i := sum_le_sum fun e' _ => hD i e'
    _ ≤ P.q.choose P.r * D i := by
        rw [sum_const, smul_eq_mul]
        gcongr
        rw [edges, card_powersetCard]
        exact Nat.choose_le_choose _ (card_image_le.trans (by simp))

open Classical in
/-- **Witness count at an `f_j`-position of a non-fixed vertex.** -/
theorem card_wit_f_le {β : Type*} {m : ℕ} {M : Matrix (Fin P.q) (Fin P.r) F}
    (hM : IsGeneric M) (κ : Fin P.N ≃ K) (a₀ : (Fin P.q → Fin P.n) → Fin P.NA)
    (k : (Fin P.q → Fin P.n) → ℕ) (C : Finset β) (e : β → Fin m → Finset (Fin P.n))
    (Q : β → Fin m → (Fin P.q → Fin P.n) → Prop)
    (Fx : Fin m → Finset (Fin P.n)) (hF : ∀ b ∈ C, ∀ i, Fx i ⊆ e b i)
    (hFr : ∀ i, (Fx i).card + 1 ≤ P.r) (D : Fin m → ℕ)
    (hD : ∀ i (e' : Finset (Fin P.n)), (C.filter fun b => e b i = e').card ≤ D i)
    (ω : P.Ω) (j : Fin P.z) (x : Fin P.n) (hx : ∀ i, x ∉ Fx i) :
    (C.filter fun b => CoverEv M κ a₀ k (e b) (Q b) ω ∧
        (⟨.inl j, Fin.castLE P.hnN x⟩ : Σ c : P.Coord, Fin (P.size c)) ∈
          coverCert M κ a₀ k (e b) (Q b) ω).card ≤
      ∑ i, P.q ^ ((Fx i).card + 1) * Fintype.card K ^ (P.r - ((Fx i).card + 1)) *
        (P.q.choose P.r * D i) := by
  set Cand : Fin m → Finset (Fin P.q → Fin P.n) := fun i => univ.filter fun ψ =>
    (∃ y, ∀ i', κ (fval ω j (ψ i')) = mvec M y i') ∧ insert x (Fx i) ⊆ univ.image ψ
  have hsub : (C.filter fun b => CoverEv M κ a₀ k (e b) (Q b) ω ∧
      (⟨.inl j, Fin.castLE P.hnN x⟩ : Σ c : P.Coord, Fin (P.size c)) ∈
        coverCert M κ a₀ k (e b) (Q b) ω) ⊆
      univ.biUnion fun i => (Cand i).biUnion fun ψ => C.filter fun b => e b i ∈ edges ψ := by
    intro b hb
    obtain ⟨hbC, hcov, hmem⟩ := mem_filter.1 hb
    unfold coverCert at hmem
    rw [dif_pos hcov] at hmem
    obtain ⟨i, -, hi⟩ := mem_biUnion.1 hmem
    set ψ := Classical.choose (hcov i)
    obtain ⟨-, he, hj⟩ := Classical.choose_spec (hcov i)
    have hok := Classical.choose_spec hj
    obtain ⟨hjj, hxψ⟩ := mem_copyDeps_inl hi
    refine mem_biUnion.2 ⟨i, mem_univ _, mem_biUnion.2 ⟨ψ, mem_filter.2 ⟨mem_univ _, ?_, ?_⟩,
      mem_filter.2 ⟨hbC, he.1⟩⟩⟩
    · rw [hjj]; exact hok.2.2.2.2
    · exact insert_subset hxψ ((hF b hbC i).trans (mem_powersetCard.1 he.1).1)
  refine (card_le_card hsub).trans (card_biUnion_le.trans (sum_le_sum fun i _ => ?_))
  refine card_biUnion_le.trans ?_
  calc _ ≤ ∑ _ψ ∈ Cand i, P.q.choose P.r * D i :=
        sum_le_sum fun ψ _ => card_edge_in_copy_le C e D hD i ψ
    _ = (Cand i).card * (P.q.choose P.r * D i) := by rw [sum_const, smul_eq_mul]
    _ ≤ _ := by
        gcongr
        have h := card_cand_supset_le hM P.hrq (fval_injective ω κ j) (insert x (Fx i))
          (by rw [card_insert_of_notMem (hx i)]; exact hFr i)
        rwa [card_insert_of_notMem (hx i)] at h

end TParams


namespace TParams

variable {P : TParams}

omit [Fintype K] [DecidableEq K] in
/-- The coordinate of a position read by the tests of `ψ`. -/
theorem mem_copyDeps_fst {j : Fin P.z} {ψ : Fin P.q → Fin P.n}
    {cp : Σ c : P.Coord, Fin (P.size c)} (h : cp ∈ copyDeps j ψ) :
    (∃ jj, cp.1 = .inl jj) ∨
      (∃ e ∈ edges ψ, cp.1 = .inr (.inl e) ∨ cp.1 = .inr (.inr (.inl e))) ∨
      cp.1 = .inr (.inr (.inr (.inl ψ))) ∨ cp.1 = .inr (.inr (.inr (.inr ψ))) := by
  simp only [copyDeps, mem_union, mem_image, mem_univ, true_and, mem_insert, mem_singleton,
    mem_product] at h
  rcases h with (⟨i, hi⟩ | ⟨e, he, hcp⟩) | (⟨ex, hex, hcp⟩ | hcp | hcp)
  · exact Or.inl ⟨j, by rw [← hi]⟩
  · exact Or.inr (Or.inl ⟨e, he, Or.inl (by rw [← hcp])⟩)
  · exact Or.inr (Or.inl ⟨ex.1, hex.1, Or.inr (by rw [← hcp])⟩)
  · exact Or.inr (Or.inr (Or.inl (by rw [hcp])))
  · exact Or.inr (Or.inr (Or.inr (by rw [hcp])))

omit [Fintype K] [DecidableEq K] in
/-- **At a non-colour position, all passing witnesses reading it coincide.** -/
theorem witness_unique {M : Matrix (Fin P.q) (Fin P.r) F} (hM : IsGeneric M) (κ : Fin P.N ≃ K)
    (a₀ : (Fin P.q → Fin P.n) → Fin P.NA) (k : (Fin P.q → Fin P.n) → ℕ) (ω : P.Ω)
    {cp : Σ c : P.Coord, Fin (P.size c)} (hcp : ∀ jj, cp.1 ≠ .inl jj)
    {ψ ψ' : Fin P.q → Fin P.n} {j j' : Fin P.z} (hψ : Function.Injective ψ)
    (h : CopyOK M κ j (a₀ ψ) (k ψ) ψ ω) (h' : CopyOK M κ j' (a₀ ψ') (k ψ') ψ' ω)
    (hm : cp ∈ copyDeps j ψ) (hm' : cp ∈ copyDeps j' ψ') : ψ = ψ' := by
  rcases mem_copyDeps_fst hm with ⟨jj, hj⟩ | ⟨e, he, hce⟩ | hA | hA
  · exact absurd hj (hcp jj)
  · rcases mem_copyDeps_fst hm' with ⟨jj, hj⟩ | ⟨e', he', hce'⟩ | hA' | hA'
    · exact absurd hj (hcp jj)
    · have hee : e = e' := by
        rcases hce with h1 | h1 <;> rcases hce' with h2 | h2 <;> rw [h1] at h2 <;>
          simp_all
      subst hee
      exact copyOK_unique hM κ hψ h h' he he'
    · rcases hce with h1 | h1 <;> rw [h1] at hA' <;> simp at hA'
    · rcases hce with h1 | h1 <;> rw [h1] at hA' <;> simp at hA'
  · rcases mem_copyDeps_fst hm' with ⟨jj, hj⟩ | ⟨e', he', hce'⟩ | hA' | hA'
    · exact absurd hj (hcp jj)
    · rcases hce' with h2 | h2 <;> rw [hA] at h2 <;> simp at h2
    · rw [hA] at hA'; simpa using hA'
    · rw [hA] at hA'; simp at hA'
  · rcases mem_copyDeps_fst hm' with ⟨jj, hj⟩ | ⟨e', he', hce'⟩ | hA' | hA'
    · exact absurd hj (hcp jj)
    · rcases hce' with h2 | h2 <;> rw [hA] at h2 <;> simp at h2
    · rw [hA] at hA'; simp at hA'
    · rw [hA] at hA'; simpa using hA'

open Classical in
/-- **Witness count at a non-colour position** (`T`, `π`, `A`, activation): at most
`∑_i C(q,r) D_i`. -/
theorem card_wit_other_le {β : Type*} {m : ℕ} {M : Matrix (Fin P.q) (Fin P.r) F}
    (hM : IsGeneric M) (κ : Fin P.N ≃ K) (a₀ : (Fin P.q → Fin P.n) → Fin P.NA)
    (k : (Fin P.q → Fin P.n) → ℕ) (C : Finset β) (e : β → Fin m → Finset (Fin P.n))
    (Q : β → Fin m → (Fin P.q → Fin P.n) → Prop)
    (D : Fin m → ℕ)
    (hD : ∀ i (e' : Finset (Fin P.n)), (C.filter fun b => e b i = e').card ≤ D i)
    (ω : P.Ω) (cp : Σ c : P.Coord, Fin (P.size c)) (hcp : ∀ jj, cp.1 ≠ .inl jj) :
    (C.filter fun b => CoverEv M κ a₀ k (e b) (Q b) ω ∧ cp ∈ coverCert M κ a₀ k (e b) (Q b) ω).card ≤
      ∑ i, P.q.choose P.r * D i := by
  by_cases hex : ∃ ψ : Fin P.q → Fin P.n, Function.Injective ψ ∧
      ∃ j, CopyOK M κ j (a₀ ψ) (k ψ) ψ ω ∧ cp ∈ copyDeps j ψ
  · obtain ⟨ψs, hψs, js, hoks, hms⟩ := hex
    have hsub : (C.filter fun b => CoverEv M κ a₀ k (e b) (Q b) ω ∧ cp ∈ coverCert M κ a₀ k (e b) (Q b) ω) ⊆
        univ.biUnion fun i => C.filter fun b => e b i ∈ edges ψs := by
      intro b hb
      obtain ⟨hbC, hcov, hmem⟩ := mem_filter.1 hb
      unfold coverCert at hmem
      rw [dif_pos hcov] at hmem
      obtain ⟨i, -, hi⟩ := mem_biUnion.1 hmem
      obtain ⟨hinj, he, hj⟩ := Classical.choose_spec (hcov i)
      have hok := Classical.choose_spec hj
      have := witness_unique hM κ a₀ k ω hcp hinj hok hoks hi hms
      exact mem_biUnion.2 ⟨i, mem_univ _, mem_filter.2 ⟨hbC, this ▸ he.1⟩⟩
    exact (card_le_card hsub).trans (card_biUnion_le.trans
      (sum_le_sum fun i _ => card_edge_in_copy_le C e D hD i ψs))
  · have : (C.filter fun b => CoverEv M κ a₀ k (e b) (Q b) ω ∧ cp ∈ coverCert M κ a₀ k (e b) (Q b) ω) = ∅ := by
      refine filter_false_of_mem fun b _ ⟨hcov, hmem⟩ => hex ?_
      unfold coverCert at hmem
      rw [dif_pos hcov] at hmem
      obtain ⟨i, -, hi⟩ := mem_biUnion.1 hmem
      obtain ⟨hinj, -, hj⟩ := Classical.choose_spec (hcov i)
      exact ⟨_, hinj, _, Classical.choose_spec hj, hi⟩
    rw [this, card_empty]; exact Nat.zero_le _

end TParams

end DesignsII
