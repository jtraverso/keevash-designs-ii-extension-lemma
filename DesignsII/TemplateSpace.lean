/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import DesignsII.ExtDefs
public import DesignsII.TemplateProb
public import DesignsII.Lipschitz

/-!
# The probability space of the random template (Keevash, *Designs II*, §3.2)

All the randomness of the template is encoded by independent uniform permutations (so that
Lemma `lip3`, `lipschitz_tail_general`, applies directly):

* `f j` (`j ∈ [z]`): a permutation `σ` of `[N]`, `N = |𝔽_{p^a}|`; the injection
  `f_j : [n] → 𝔽_{p^a}` is `x ↦ κ (σ x)` (first `n` positions);
* `T e` (`e ⊆ [n]`): a permutation of `[z]`; `T_e = σ 0`;
* `π e`: a permutation of `[q]`; for `|e| = r` the injection `π_e : e → [q]` sends the `k`-th
  element of `e` to `σ k` (first `r` positions);
* `A φ` (`φ : [q] → [n]`): a permutation of `[|𝒜|]`; `A_φ = σ 0`;
* `act φ`: a permutation of `[Nact]`; `φ` is activated iff `σ 0 < k_φ`. (The paper activates
  with probability `y_φ ω n^{q-r}`; any rational approximation `k_φ / Nact` can be used.)

`prob_template_copy` computes, for a fixed injective `φ`, the probability that `φ` passes all
the random tests defining `M*_j` (Definition 3.2): it is the product
`(1/|𝒜|) (k_φ/Nact) z^{-Q} ((q)_r)^{-Q} P_f`, with `P_f` given by `card_compat`.
-/

@[expose] public section

namespace DesignsII

open Finset Equiv

namespace TParams

variable (P : TParams)

variable {P}

end TParams


namespace TParams

variable {P : TParams}

variable {F K : Type*} [Field F] [Field K] [Algebra F K] [Fintype K] [DecidableEq K]

/-- The coordinate events of `CopyOK`. -/
def copyEv (M : Matrix (Fin P.q) (Fin P.r) F) (κ : Fin P.N ≃ K) (j : Fin P.z) (a₀ : Fin P.NA)
    (k : ℕ) (φ : Fin P.q → Fin P.n) : ∀ c : P.Coord, Perm (Fin (P.size c)) → Prop
  | .inl j' => fun σ => j' = j →
      ∃ y, ∀ i, κ ((σ : Perm (Fin P.N)) (Fin.castLE P.hnN (φ i))) = mvec M y i
  | .inr (.inl e) => fun σ => e ∈ edges φ → (σ : Perm (Fin P.z)) ⟨0, P.hz⟩ = j
  | .inr (.inr (.inl e)) => fun σ => e ∈ edges φ → ∀ (hc : e.card = P.r) i (hi : φ i ∈ e),
      (σ : Perm (Fin P.q)) (Fin.castLE P.hrq ((e.orderIsoOfFin hc).symm ⟨φ i, hi⟩)) = i
  | .inr (.inr (.inr (.inl φ'))) => fun σ => φ' = φ → (σ : Perm (Fin P.NA)) ⟨0, P.hNA⟩ = a₀
  | .inr (.inr (.inr (.inr φ'))) => fun σ => φ' = φ →
      (((σ : Perm (Fin P.Nact)) ⟨0, P.hNact⟩ : Fin P.Nact) : ℕ) < k

omit [Fintype K] [DecidableEq K] in
theorem copyOK_iff (M : Matrix (Fin P.q) (Fin P.r) F) (κ : Fin P.N ≃ K) (j : Fin P.z)
    (a₀ : Fin P.NA) (k : ℕ) (φ : Fin P.q → Fin P.n) (ω : P.Ω) :
    CopyOK M κ j a₀ k φ ω ↔ ∀ c, copyEv M κ j a₀ k φ c (ω c) := by
  constructor
  · rintro ⟨hA, hact, hT, hpi, hf⟩ c
    rcases c with j' | e | e | φ' | φ'
    · rintro rfl; exact hf
    · intro he; exact hT e he
    · intro he hc i hi
      have := hpi e he i hi
      unfold pival at this
      rw [dif_pos ⟨hc, hi⟩] at this
      exact Option.some.inj this
    · rintro rfl; exact hA
    · rintro rfl; exact hact
  · intro h
    refine ⟨h (.inr (.inr (.inr (.inl φ)))) rfl, h (.inr (.inr (.inr (.inr φ)))) rfl,
      fun e he => h (.inr (.inl e)) he, fun e he i hi => ?_, h (.inl j) rfl⟩
    have hc : e.card = P.r := (mem_powersetCard.1 he).2
    unfold pival
    rw [dif_pos ⟨hc, hi⟩]
    exact congrArg some (h (.inr (.inr (.inl e))) he hc i hi)

end TParams

/-! ### Counting the coordinate events -/

theorem card_fin_lt (m k : ℕ) : (univ.filter fun v : Fin m => (v : ℕ) < k).card = min k m := by
  rw [← card_range (min k m), ← card_map Fin.valEmbedding]
  congr 1
  ext x
  simp only [mem_map, mem_filter, mem_univ, true_and, Fin.valEmbedding_apply, mem_range]
  constructor
  · rintro ⟨v, hv, rfl⟩; omega
  · intro hx; exact ⟨⟨x, by omega⟩, by simp; omega, rfl⟩

theorem card_perm_val0 {m : ℕ} (hm : 0 < m) (v : Fin m) :
    (univ.filter fun σ : Perm (Fin m) => σ ⟨0, hm⟩ = v).card = (m - 1).factorial := by
  rw [← card_perm_fix (⟨fun _ : Fin 1 => ⟨0, hm⟩, fun a b _ => Subsingleton.elim a b⟩ :
    Fin 1 ↪ Fin m) ⟨fun _ : Fin 1 => v, fun a b _ => Subsingleton.elim a b⟩]
  congr 1
  ext σ
  simp only [mem_filter, mem_univ, true_and]
  exact ⟨fun h _ => h, fun h => h 0⟩

theorem card_perm_val0_lt {m : ℕ} (hm : 0 < m) (k : ℕ) :
    (univ.filter fun σ : Perm (Fin m) => ((σ ⟨0, hm⟩ : Fin m) : ℕ) < k).card =
      min k m * (m - 1).factorial := by
  classical
  rw [card_eq_sum_card_fiberwise (f := fun σ : Perm (Fin m) => σ ⟨0, hm⟩)
    (t := univ.filter fun v : Fin m => (v : ℕ) < k)
    (fun σ hσ => by simpa using (mem_filter.1 hσ).2)]
  rw [← card_fin_lt m k, ← smul_eq_mul, ← sum_const]
  refine sum_congr rfl fun v hv => ?_
  rw [← card_perm_val0 hm v]
  congr 1
  ext σ
  simp only [mem_filter, mem_univ, true_and]
  constructor
  · rintro ⟨-, h⟩; exact h
  · intro h; exact ⟨h ▸ (mem_filter.1 hv).2, h⟩


namespace TParams

variable {P : TParams}

/-- The index `i` with `φ i` equal to the `x`-th element of an edge `e ⊆ φ([q])`. -/
noncomputable def edgeIdx (φ : Fin P.q → Fin P.n) (e : Finset (Fin P.n)) (hc : e.card = P.r)
    (he : e ⊆ univ.image φ) (x : Fin P.r) : Fin P.q :=
  Classical.choose (mem_image.1 (he (e.orderIsoOfFin hc x).2))

theorem edgeIdx_spec (φ : Fin P.q → Fin P.n) (e : Finset (Fin P.n)) (hc : e.card = P.r)
    (he : e ⊆ univ.image φ) (x : Fin P.r) :
    φ (edgeIdx φ e hc he x) = (e.orderIsoOfFin hc x : Fin P.n) :=
  (Classical.choose_spec (mem_image.1 (he (e.orderIsoOfFin hc x).2))).2

/-- The number of orderings `σ` of `[q]` with `π_e φ = id` on an edge `e ⊆ φ([q])`. -/
theorem card_pi_event {φ : Fin P.q → Fin P.n} (hφ : Function.Injective φ)
    {e : Finset (Fin P.n)} (hc : e.card = P.r) (he : e ⊆ univ.image φ) :
    (univ.filter fun σ : Perm (Fin P.q) => ∀ (hc : e.card = P.r) i (hi : φ i ∈ e),
      σ (Fin.castLE P.hrq ((e.orderIsoOfFin hc).symm ⟨φ i, hi⟩)) = i).card =
      (P.q - P.r).factorial := by
  have hidx : Function.Injective (edgeIdx φ e hc he) := by
    intro x x' h
    have := congrArg φ h
    rw [edgeIdx_spec φ e hc he, edgeIdx_spec φ e hc he] at this
    exact (e.orderIsoOfFin hc).injective (Subtype.ext this)
  rw [← card_perm_fix (Fin.castLEEmb P.hrq) ⟨edgeIdx φ e hc he, hidx⟩]
  congr 1
  ext σ
  simp only [mem_filter, mem_univ, true_and, Fin.castLEEmb_apply]
  constructor
  · intro h x
    have hx : φ (edgeIdx φ e hc he x) ∈ e := by rw [edgeIdx_spec φ e hc he]; exact (e.orderIsoOfFin hc x).2
    have := h hc _ hx
    have hsymm : (e.orderIsoOfFin hc).symm ⟨φ (edgeIdx φ e hc he x), hx⟩ = x := by
      rw [OrderIso.symm_apply_eq]; exact Subtype.ext (edgeIdx_spec φ e hc he x)
    rwa [hsymm] at this
  · intro h hc' i hi
    set x := (e.orderIsoOfFin hc').symm ⟨φ i, hi⟩
    have h1 := h x
    have h2 : edgeIdx φ e hc he x = i := by
      apply hφ
      rw [edgeIdx_spec φ e hc he]
      have : (e.orderIsoOfFin hc x : Fin P.n) = (e.orderIsoOfFin hc' x : Fin P.n) := rfl
      rw [this, OrderIso.apply_symm_apply]
    rw [h1]; exact h2

end TParams


namespace TParams

variable {P : TParams} {F K : Type*} [Field F] [Field K] [Algebra F K] [Fintype K]
  [DecidableEq K]

theorem card_filter_congr' {α : Type*} [Fintype α] (p q : α → Prop) [DecidablePred p]
    [DecidablePred q] (h : ∀ x, p x ↔ q x) : (univ.filter p).card = (univ.filter q).card := by
  rw [filter_congr fun x _ => h x]

theorem factorial_ratio_pred {m : ℕ} (hm : 0 < m) :
    ((m - 1).factorial : ℝ) / (m.factorial : ℝ) = 1 / m := by
  have h := Nat.mul_factorial_pred (n := m) (by omega)
  have hpos : (0 : ℝ) < (m - 1).factorial := by exact_mod_cast Nat.factorial_pos _
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  rw [← h]; push_cast; field_simp

theorem ratio_true {m : ℕ} (E : Perm (Fin m) → Prop) [DecidablePred E] (h : ∀ σ, E σ) :
    ((univ.filter E).card : ℝ) / (m.factorial : ℝ) = 1 := by
  rw [filter_true_of_mem fun σ _ => h σ, card_univ, Fintype.card_perm, Fintype.card_fin]
  exact div_self (by exact_mod_cast (Nat.factorial_pos m).ne')

open Classical in
/-- **The probability that a fixed injective `φ` passes all the random tests of `M*_j`** is
`P_f · z^{-|φ(Q)|} · ((q-r)!/q!)^{|φ(Q)|} · |𝒜|^{-1} · k/N_act`, where
`P_f = #{y : My injective} (N-q)!/N!` (Designs II, proof of Lemma `e|E`, without conditioning). -/
theorem probG_copyOK {M : Matrix (Fin P.q) (Fin P.r) F} (hM : IsGeneric M) (κ : Fin P.N ≃ K)
    (j : Fin P.z) (a₀ : Fin P.NA) {k : ℕ} (hk : k ≤ P.Nact) {φ : Fin P.q → Fin P.n}
    (hφ : Function.Injective φ) :
    probG (a := P.size) (CopyOK M κ j a₀ k φ) =
      (((univ.filter fun y : Fin P.r → K => Function.Injective (mvec M y)).card *
          (P.N - P.q).factorial : ℕ) / (P.N.factorial : ℝ)) *
        (1 / (P.z : ℝ)) ^ (edges φ).card *
        (((P.q - P.r).factorial : ℝ) / (P.q.factorial : ℝ)) ^ (edges φ).card *
        (1 / (P.NA : ℝ)) * ((k : ℝ) / P.Nact) := by
  classical
  have hcard : (univ.filter (CopyOK M κ j a₀ k φ)).card =
      ∏ c, (univ.filter (copyEv M κ j a₀ k φ c)).card := by
    rw [← card_pi_filter]
    congr 1
    ext ω
    simp only [mem_filter, mem_univ, true_and, copyOK_iff]
  unfold probG
  rw [hcard]
  push_cast
  rw [← prod_div_distrib]
  simp only [Fintype.prod_sum_type]
  -- the `f` coordinates
  have hf : ∀ j' : Fin P.z,
      ((univ.filter (copyEv M κ j a₀ k φ (.inl j'))).card : ℝ) /
          ((P.size (.inl j')).factorial : ℝ) =
        if j' = j then
          (((univ.filter fun y : Fin P.r → K => Function.Injective (mvec M y)).card *
            (P.N - P.q).factorial : ℕ) / (P.N.factorial : ℝ)) else 1 := by
    intro j'
    by_cases h : j' = j
    · rw [if_pos h]
      subst h
      have h1 := (card_filter_congr' (copyEv M κ j' a₀ k φ (.inl j'))
        (fun σ : Perm (Fin P.N) => ∃ y, ∀ i, κ (σ (Fin.castLE P.hnN (φ i))) = mvec M y i)
        fun σ => ⟨fun h => h rfl, fun h _ => h⟩).trans
        (card_compat hM P.hrq κ ⟨fun i => Fin.castLE P.hnN (φ i), fun i i' h =>
          hφ (Fin.castLE_injective P.hnN h)⟩)
      rw [h1]; rfl
    · rw [if_neg h]
      exact @ratio_true P.N (copyEv M κ j a₀ k φ (.inl j')) (Classical.decPred _) fun σ hh => absurd hh h
  have hT : ∀ e : Finset (Fin P.n),
      ((univ.filter (copyEv M κ j a₀ k φ (.inr (.inl e)))).card : ℝ) /
          ((P.size (.inr (.inl e))).factorial : ℝ) =
        if e ∈ edges φ then 1 / (P.z : ℝ) else 1 := by
    intro e
    by_cases he : e ∈ edges φ
    · rw [if_pos he]
      have h1 := (card_filter_congr' (copyEv M κ j a₀ k φ (.inr (.inl e)))
        (fun σ : Perm (Fin P.z) => σ ⟨0, P.hz⟩ = j) fun σ => ⟨fun h => h he, fun h _ => h⟩).trans
        (card_perm_val0 P.hz j)
      rw [h1]; exact factorial_ratio_pred P.hz
    · rw [if_neg he]
      exact @ratio_true P.z (copyEv M κ j a₀ k φ (.inr (.inl e))) (Classical.decPred _) fun σ hh => absurd hh he
  have hpi : ∀ e : Finset (Fin P.n),
      ((univ.filter (copyEv M κ j a₀ k φ (.inr (.inr (.inl e))))).card : ℝ) /
          ((P.size (.inr (.inr (.inl e)))).factorial : ℝ) =
        if e ∈ edges φ then ((P.q - P.r).factorial : ℝ) / (P.q.factorial : ℝ) else 1 := by
    intro e
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
      exact @ratio_true P.q (copyEv M κ j a₀ k φ (.inr (.inr (.inl e)))) (Classical.decPred _) fun σ hh => absurd hh he
  have hA : ∀ φ' : Fin P.q → Fin P.n,
      ((univ.filter (copyEv M κ j a₀ k φ (.inr (.inr (.inr (.inl φ')))))).card : ℝ) /
          ((P.size (.inr (.inr (.inr (.inl φ'))))).factorial : ℝ) =
        if φ' = φ then 1 / (P.NA : ℝ) else 1 := by
    intro φ'
    by_cases h : φ' = φ
    · rw [if_pos h]
      subst h
      have h1 := (card_filter_congr' (copyEv M κ j a₀ k φ' (.inr (.inr (.inr (.inl φ')))))
        (fun σ : Perm (Fin P.NA) => σ ⟨0, P.hNA⟩ = a₀)
        fun σ => ⟨fun h => h rfl, fun h _ => h⟩).trans (card_perm_val0 P.hNA a₀)
      rw [h1]; exact factorial_ratio_pred P.hNA
    · rw [if_neg h]
      exact @ratio_true P.NA (copyEv M κ j a₀ k φ (.inr (.inr (.inr (.inl φ'))))) (Classical.decPred _) fun σ hh => absurd hh h
  have hact : ∀ φ' : Fin P.q → Fin P.n,
      ((univ.filter (copyEv M κ j a₀ k φ (.inr (.inr (.inr (.inr φ')))))).card : ℝ) /
          ((P.size (.inr (.inr (.inr (.inr φ'))))).factorial : ℝ) =
        if φ' = φ then (k : ℝ) / P.Nact else 1 := by
    intro φ'
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
      exact @ratio_true P.Nact (copyEv M κ j a₀ k φ (.inr (.inr (.inr (.inr φ'))))) (Classical.decPred _) fun σ hh => absurd hh h
  rw [Fintype.prod_congr _ _ hf, Fintype.prod_congr _ _ hT, Fintype.prod_congr _ _ hpi,
    Fintype.prod_congr _ _ hA, Fintype.prod_congr _ _ hact]
  rw [prod_ite_eq' univ j, prod_ite_eq' univ φ, prod_ite_eq' univ φ, prod_ite_mem, prod_ite_mem, univ_inter,
    prod_const, prod_const]
  simp only [mem_univ, if_true]
  push_cast
  ring

end TParams

end DesignsII
