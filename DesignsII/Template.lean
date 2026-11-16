/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import DesignsII.ExtDefs
public import Mathlib

/-!
# The algebraic template (Keevash, *Existence of designs II*, §3.2; *Designs I*, Lemma 3.3)

Fix a field `F` (in the paper `F = 𝔽_p`), an extension `K` of `F` (`K = 𝔽_{p^a}`) and a matrix
`M ∈ F^{q × r}` that is **generic**: every `r × r` submatrix is nonsingular (`IsGeneric`).

For `j ∈ [z]` let `f j : [n] → K` be an injection, let `T` assign to every `r`-set `e` a colour
`T e ∈ [z]` and let `π` assign to every `r`-set `e` a map `π e : [n] → [q]`. A map `φ : [q] → [n]`
is

* **compatible with `j`** (`CompatJ`) if every `r`-set `e ⊆ φ([q])` has `T e = j` and
  `f j ∘ φ = M y` for some `y ∈ K^r`;
* **compatible with `π`** (`CompatPi`) if `π e (φ i) = i` whenever `φ i ∈ e ⊆ φ([q])`, `|e| = r`.

`template_disjoint`: two injective maps compatible with `π` and with some `j, j'` whose images
share an `r`-set are equal. Hence the copies `φ(Q)` of the template are pairwise
`r`-edge-disjoint, i.e. `{φ(Q) : φ ∈ M*}` is a `K_q^r`-decomposition of `G* = ⋃ φ(Q)`
(`template_edge_unique`).
-/

@[expose] public section

namespace DesignsII

open Finset Matrix

variable {F K : Type*} [Field F] [Field K] [Algebra F K] {q r n z : ℕ}


/-- A Vandermonde matrix `M i k = x_i^k` with distinct `x_i` is generic. -/
theorem isGeneric_vandermonde (x : Fin q ↪ F) :
    IsGeneric (r := r) (Matrix.of fun (i : Fin q) (k : Fin r) => x i ^ (k : ℕ)) := by
  intro b
  have : (Matrix.of fun (i : Fin q) (k : Fin r) => x i ^ (k : ℕ)).submatrix b id =
      Matrix.vandermonde (x ∘ b) := by
    ext i k; simp [Matrix.vandermonde]
  rw [this, Matrix.det_vandermonde_ne_zero_iff]
  exact x.injective.comp b.injective

/-- Generic matrices exist over any field with at least `q` elements. -/
theorem exists_isGeneric [Fintype F] (hq : q ≤ Fintype.card F) :
    ∃ M : Matrix (Fin q) (Fin r) F, IsGeneric M := by
  obtain ⟨x⟩ : Nonempty (Fin q ↪ F) := Function.Embedding.nonempty_of_card_le (by simpa using hq)
  exact ⟨_, isGeneric_vandermonde x⟩

/-- `φ` is compatible with colour `j`. -/
def CompatJ (M : Matrix (Fin q) (Fin r) F) (f : Fin z → Fin n → K) (T : Finset (Fin n) → Fin z)
    (j : Fin z) (φ : Fin q → Fin n) : Prop :=
  (∀ e : Finset (Fin n), e.card = r → e ⊆ univ.image φ → T e = j) ∧
    ∃ y : Fin r → K, ∀ i, f j (φ i) = (M.map (algebraMap F K) *ᵥ y) i

/-- `φ` is compatible with `π` (`π_e φ = id` on every `r`-set `e ⊆ φ([q])`). -/
def CompatPi (π : Finset (Fin n) → Fin n → Fin q) (φ : Fin q → Fin n) : Prop :=
  ∀ e : Finset (Fin n), e.card = r → e ⊆ univ.image φ → ∀ i, φ i ∈ e → π e (φ i) = i

/-- A generic `M` is injective on `K^r` along any `r` rows. -/
theorem generic_rows_inj {M : Matrix (Fin q) (Fin r) F} (hM : IsGeneric M) {B : Finset (Fin q)}
    (hB : B.card = r) {y y' : Fin r → K}
    (h : ∀ i ∈ B, (M.map (algebraMap F K) *ᵥ y) i = (M.map (algebraMap F K) *ᵥ y') i) :
    y = y' := by
  set b : Fin r ↪ Fin q := (B.orderEmbOfFin hB).toEmbedding
  set N : Matrix (Fin r) (Fin r) K := (M.submatrix b id).map (algebraMap F K)
  have hN : N.det ≠ 0 := by
    have : N.det = algebraMap F K (M.submatrix b id).det := by
      simp only [N]
      exact ((algebraMap F K).map_det (M.submatrix b id)).symm
    rw [this]
    exact (map_ne_zero _).2 (hM b)
  have h0 : N *ᵥ (y - y') = 0 := by
    funext k
    have hk : b k ∈ B := B.orderEmbOfFin_mem hB k
    have := h _ hk
    simp only [mulVec, dotProduct, map_apply] at this
    simp only [N, mulVec, dotProduct, map_apply, submatrix_apply, id, Pi.sub_apply, mul_sub,
      sum_sub_distrib, Pi.zero_apply]
    rw [this, sub_self]
  exact sub_eq_zero.1 (eq_zero_of_mulVec_eq_zero hN h0)

/-- **Designs I, Lemma 3.3 / Designs II, §3.2.** Two maps (the first injective) that are compatible with `π`
and with colours `j, j'`, and whose images share an `r`-set, are equal. -/
theorem template_disjoint {M : Matrix (Fin q) (Fin r) F} (hM : IsGeneric M)
    {f : Fin z → Fin n → K} (hf : ∀ j, Function.Injective (f j)) {T : Finset (Fin n) → Fin z}
    {π : Finset (Fin n) → Fin n → Fin q} {j j' : Fin z} {φ φ' : Fin q → Fin n}
    (hφ : Function.Injective φ)
    (hJ : CompatJ M f T j φ) (hJ' : CompatJ M f T j' φ')
    (hP : CompatPi (r := r) π φ) (hP' : CompatPi (r := r) π φ')
    {e : Finset (Fin n)} (he : e.card = r) (h1 : e ⊆ univ.image φ) (h2 : e ⊆ univ.image φ') :
    φ = φ' := by
  classical
  have hjj : j = j' := (hJ.1 e he h1).symm.trans (hJ'.1 e he h2)
  subst hjj
  obtain ⟨y, hy⟩ := hJ.2
  obtain ⟨y', hy'⟩ := hJ'.2
  -- the positions of `e` in `φ`
  set B : Finset (Fin q) := univ.filter fun i => φ i ∈ e
  have hBimg : B.image φ = e := by
    ext x
    simp only [B, mem_image, mem_filter, mem_univ, true_and]
    constructor
    · rintro ⟨i, hi, rfl⟩; exact hi
    · intro hx
      obtain ⟨i, -, hi⟩ := mem_image.1 (h1 hx)
      exact ⟨i, hi ▸ hx, hi⟩
  have hB : B.card = r := by
    rw [← he, ← hBimg, card_image_of_injective _ hφ]
  -- `φ` and `φ'` agree on `B`
  have hagree : ∀ i ∈ B, φ' i = φ i := by
    intro i hi
    have hi' : φ i ∈ e := (mem_filter.1 hi).2
    obtain ⟨i', -, hi'eq⟩ := mem_image.1 (h2 hi')
    have a1 := hP e he h1 i hi'
    have a2 := hP' e he h2 i' (hi'eq ▸ hi')
    rw [hi'eq] at a2
    have hii : i' = i := a2.symm.trans a1
    rw [hii] at hi'eq; exact hi'eq
  have hyy : y = y' := by
    refine generic_rows_inj hM hB fun i hi => ?_
    rw [← hy, ← hy', hagree i hi]
  subst hyy
  funext i
  exact hf j ((hy i).trans (hy' i).symm)

/-- Every `r`-set lies in the image of at most one injective map compatible with `π` and some
colour: the template copies form a `K_q^r`-decomposition of their union. -/
theorem template_edge_unique {M : Matrix (Fin q) (Fin r) F} (hM : IsGeneric M)
    {f : Fin z → Fin n → K} (hf : ∀ j, Function.Injective (f j)) {T : Finset (Fin n) → Fin z}
    {π : Finset (Fin n) → Fin n → Fin q} (e : Finset (Fin n)) (he : e.card = r) :
    {φ : Fin q → Fin n | Function.Injective φ ∧ (∃ j, CompatJ M f T j φ) ∧
      CompatPi (r := r) π φ ∧ e ⊆ univ.image φ}.Subsingleton := by
  rintro φ ⟨hφ, ⟨j, hJ⟩, hP, h1⟩ φ' ⟨-, ⟨j', hJ'⟩, hP', h2⟩
  exact template_disjoint hM hf hφ hJ hJ' hP hP' he h1 h2

end DesignsII
