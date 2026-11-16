/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import DesignsII.Degenerate
public import DesignsII.Joint

/-!
# Few colours are degenerate at the fixed vertices

For fixed vertices `u : [s] ↪ [n]`, colour `j` is *degenerate* if the values `f_j(u_1), …, f_j(u_s)`
are `F`-linearly dependent (`DegColour`). The colours are independent coordinates of the template
space, so

* `ratio_deg_le`: a single colour is degenerate with probability at most
  `p_deg = |F|^s N^{s-1} (N-s)!/N!` (`≈ |F|^s / N`);
* `probG_many_deg_le`: at least `k` colours are degenerate with probability at most
  `C(z, k) p_deg^k`.
-/

@[expose] public section

namespace DesignsII

open Finset Equiv

section Union

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {a : ι → ℕ}

/-- Union bound over a finite family of events. -/
theorem probG_exists_le {β : Type*} (T : Finset β) (A : β → (∀ c, Perm (Fin (a c))) → Prop) :
    probG (a := a) (fun ω => ∃ b ∈ T, A b ω) ≤ ∑ b ∈ T, probG (a := a) (A b) := by
  classical
  induction T using Finset.induction_on with
  | empty =>
    unfold probG; simp
  | insert b T hb ih =>
    rw [sum_insert hb]
    refine (probG_mono (B := fun ω => A b ω ∨ ∃ b' ∈ T, A b' ω) fun ω ⟨b', hb', h⟩ => ?_).trans
      ((probG_or_le _ _).trans (by linarith))
    rcases mem_insert.1 hb' with rfl | h'
    · exact Or.inl h
    · exact Or.inr ⟨b', h', h⟩

end Union

variable {F K : Type*} [Field F] [Fintype F] [DecidableEq F] [Field K] [Algebra F K] [Fintype K]
  [DecidableEq K]

namespace TParams

variable {P : TParams}

/-- Colour-coordinate degeneracy at the positions `u` (as a predicate on the permutation). -/
def DegPerm (κ : Fin P.N ≃ K) {s : ℕ} (u : Fin s ↪ Fin P.n) (σ : Perm (Fin P.N)) : Prop :=
  ¬ LinearIndependent F fun k => κ (σ (Fin.castLE P.hnN (u k)))

open Classical in
/-- **A single colour is rarely degenerate.** -/
theorem ratio_deg_le (κ : Fin P.N ≃ K) {s : ℕ} (u : Fin s ↪ Fin P.n) :
    ratio (DegPerm (F := F) κ u) ≤
      (Fintype.card F ^ s * Fintype.card K ^ (s - 1) : ℕ) * ((P.N - s).factorial : ℝ) /
        (P.N.factorial : ℝ) := by
  unfold ratio
  refine div_le_div_of_nonneg_right ?_ (by positivity)
  set w : Fin s ↪ Fin P.N := u.trans (Fin.castLEEmb P.hnN)
  set D : Finset (Fin s ↪ Fin P.N) :=
    univ.filter fun e => ¬ LinearIndependent F fun k => κ (e k)
  have h1 : (univ.filter (DegPerm (F := F) κ u)).card = D.card * (P.N - s).factorial := by
    rw [← card_perm_restrict_mem w D]
    congr 1
    ext σ
    simp [DegPerm, D, w]
  have h2 : D.card ≤ Fintype.card F ^ s * Fintype.card K ^ (s - 1) := by
    refine le_trans ?_ (card_dependent_le (F := F) (K := K) s)
    refine card_le_card_of_injOn (fun e k => κ (e k)) (fun e he => ?_) ?_
    · simpa [D] using he
    · intro e _ e' _ h
      ext k
      exact congrArg Fin.val (κ.injective (congrFun h k))
  rw [h1]
  push_cast
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast h2) (by positivity)

omit [Fintype F] [DecidableEq F] [Fintype K] [DecidableEq K] in
open Classical in
/-- The probability that all colours in `J` are degenerate is the product. -/
theorem probG_all_deg_eq (κ : Fin P.N ≃ K) {s : ℕ} (u : Fin s ↪ Fin P.n)
    (J : Finset (Fin P.z)) :
    probG (a := P.size) (fun ω => ∀ j ∈ J, DegPerm (F := F) κ u (ω (.inl j))) =
      ratio (DegPerm (F := F) κ u) ^ J.card := by
  set X : ∀ c : P.Coord, Perm (Fin (P.size c)) → Prop := fun c => match c with
    | .inl j => fun σ => j ∈ J → DegPerm (F := F) κ u σ
    | .inr _ => fun _ => True
  have h : probG (a := P.size) (fun ω => ∀ j ∈ J, DegPerm (F := F) κ u (ω (.inl j))) =
      probG (a := P.size) (fun ω => ∀ c, X c (ω c)) := by
    congr 1
    funext ω
    refine propext ⟨fun hω c => ?_, fun hω j hj => hω (.inl j) hj⟩
    rcases c with j | c
    · exact fun hj => hω j hj
    · trivial
  rw [h, probG_pi, Fintype.prod_sum_type]
  have h1 : ∀ j : Fin P.z, ratio (X (.inl j)) =
      if j ∈ J then ratio (DegPerm (F := F) κ u) else 1 := by
    intro j
    split_ifs with hj
    · exact ratio_congr fun σ => ⟨fun h => h hj, fun h _ => h⟩
    · exact ratio_true' _ fun σ hh => absurd hh hj
  have h2 : ∀ c, ratio (X (.inr c)) = 1 := fun c => ratio_true' _ fun _ => trivial
  rw [Fintype.prod_congr _ _ h1, Fintype.prod_congr _ _ h2, prod_const_one, mul_one,
    prod_ite_mem, univ_inter, prod_const]

omit [Fintype F] [DecidableEq F] [Fintype K] [DecidableEq K] in
open Classical in
/-- **At least `k` degenerate colours** has probability at most `C(z, k) p^k`. -/
theorem probG_many_deg_le (κ : Fin P.N ≃ K) {s : ℕ} (u : Fin s ↪ Fin P.n) (k : ℕ) :
    probG (a := P.size)
        (fun ω => k ≤ (univ.filter fun j => DegPerm (F := F) κ u (ω (.inl j))).card) ≤
      (P.z.choose k : ℝ) * ratio (DegPerm (F := F) κ u) ^ k := by
  calc _ ≤ probG (a := P.size) (fun ω => ∃ J ∈ (univ : Finset (Fin P.z)).powersetCard k,
        ∀ j ∈ J, DegPerm (F := F) κ u (ω (.inl j))) := by
        refine probG_mono fun ω hω => ?_
        obtain ⟨J, hJ, hJk⟩ := exists_subset_card_eq hω
        exact ⟨J, mem_powersetCard.2 ⟨subset_univ _, hJk⟩, fun j hj => (mem_filter.1 (hJ hj)).2⟩
    _ ≤ ∑ J ∈ (univ : Finset (Fin P.z)).powersetCard k,
          probG (a := P.size) (fun ω => ∀ j ∈ J, DegPerm (F := F) κ u (ω (.inl j))) :=
        probG_exists_le _ _
    _ = _ := by
        rw [sum_congr rfl fun J hJ => by
          rw [probG_all_deg_eq, (mem_powersetCard.1 hJ).2], sum_const, card_powersetCard,
          card_univ, Fintype.card_fin, nsmul_eq_mul]

end TParams

end DesignsII
