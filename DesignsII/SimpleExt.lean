/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import DesignsII.MainStatement
public import DesignsII.AtomEq

/-!
# Copies extending a map, from extendability

`simpleH`: the complex of all restrictions of the labelled map `x ↦ (x, 0)` (one copy of the
labels). Applying `(Φ, Φ')`-extendability to it with `F` = the labels of `B` gives
(`card_extensions_ge`): for `ψ ∈ Φ_B` there are at least `ω |V(Φ)|^{|R| - |B|}` maps `φ : R → V`
with `φ ∈ Φ_R` (as a labelled map), `φ|_B = ψ`, and `φ|_{B'} ∈ Φ'` for every `r`-set `B' ⊄ B`.
-/

@[expose] public section

namespace DesignsII

open Finset

variable {R V ι : Type*} [DecidableEq R] [Fintype R] [Fintype V] [DecidableEq V] {r : ℕ}

/-- The labelled map `x ↦ (x, 0)`. -/
def iota0 {s : ℕ} (hs : 0 < s) : R → Option (R × Fin s) := fun x => some (x, ⟨0, hs⟩)

omit [Fintype R] in
theorem dom_restrict_iota0 {s : ℕ} (hs : 0 < s) (B : Finset R) :
    dom (restrict (iota0 hs) B) = B := by
  ext x; by_cases hx : x ∈ B <;> simp [dom, restrict, iota0, hx]

/-- The complex of all restrictions of `iota0`. -/
def simpleH {s : ℕ} (hs : 0 < s) : RSystem R (R × Fin s) where
  maps B := {restrict (iota0 hs) B}
  dom_eq B ψ h := by rw [Set.mem_singleton_iff.1 h]; exact dom_restrict_iota0 hs B
  inj B ψ h := by
    rw [Set.mem_singleton_iff.1 h]
    intro x y hx hxy
    by_cases h1 : x ∈ B <;> by_cases h2 : y ∈ B <;>
      simp_all [restrict, iota0]

omit [Fintype R] in
theorem simpleH_isComplex {s : ℕ} (hs : 0 < s) : (simpleH (R := R) hs).IsComplex := by
  intro B B' hB ψ hψ
  rw [Set.mem_singleton_iff.1 hψ]
  show restrict (restrict (iota0 hs) B) B' = restrict (iota0 hs) B'
  rw [restrict_restrict, inter_eq_right.2 hB]

omit [Fintype R] in
theorem simpleH_partite {s : ℕ} (hs : 0 < s) (B : Finset R) :
    (simpleH hs).maps B ⊆ (partiteMaps R (Fin s)).maps B := by
  intro ψ hψ
  rw [Set.mem_singleton_iff.1 hψ]
  refine ⟨dom_restrict_iota0 hs B, fun i p hp => ?_⟩
  by_cases hi : i ∈ B <;> simp_all [restrict, iota0]
  rw [← hp]

theorem vertices_simpleH {s : ℕ} (hs : 0 < s) :
    vertices (simpleH (R := R) hs) = ↑(univ.image fun x : R => (x, (⟨0, hs⟩ : Fin s))) := by
  ext v
  simp only [vertices, simpleH, Set.mem_singleton_iff, coe_image, coe_univ, Set.image_univ,
    Set.mem_range, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨B, ψ, rfl, x, hx⟩
    by_cases hxB : x ∈ B
    · simp only [restrict, iota0, hxB, ite_true, Option.some.injEq] at hx
      exact ⟨x, hx⟩
    · simp [restrict, hxB] at hx
  · rintro ⟨x, rfl⟩
    exact ⟨univ, _, rfl, x, by simp [restrict, iota0]⟩

omit [Fintype R] in
theorem mem_induce_simpleH {s : ℕ} (hs : 0 < s) (B B' : Finset R) (ψ : R → Option (R × Fin s)) :
    ψ ∈ ((simpleH hs).induce ↑(B.image fun x : R => (x, (⟨0, hs⟩ : Fin s)))).maps B' ↔
      ψ = restrict (iota0 hs) B' ∧ B' ⊆ B := by
  simp only [RSystem.induce, simpleH, Set.mem_ofPred_eq, Set.mem_singleton_iff, coe_image]
  constructor
  · rintro ⟨rfl, h⟩
    refine ⟨rfl, fun x hx => ?_⟩
    have := h x (x, ⟨0, hs⟩) (by simp [restrict, iota0, hx])
    obtain ⟨y, hy, hyx⟩ := this
    simp only [Prod.mk.injEq] at hyx
    exact hyx.1 ▸ hy
  · rintro ⟨rfl, hB⟩
    refine ⟨rfl, fun x w hw => ?_⟩
    by_cases hx : x ∈ B'
    · simp only [restrict, iota0, hx, ite_true, Option.some.injEq] at hw
      exact ⟨x, hB hx, hw⟩
    · simp [restrict, hx] at hw
/-- `ψ` is defined on its domain. -/
theorem some_of_mem_dom {ψ : R → Option V} {B : Finset R} (h : dom ψ = B) {x : R} (hx : x ∈ B) :
    ∃ w, ψ x = some w := by
  have : x ∈ dom ψ := by rw [h]; exact hx
  exact Option.ne_none_iff_exists'.1 this

open Classical in
/-- **Copies extending `ψ` from extendability.** -/
theorem card_extensions_ge (Φ : RSystem R V) (hΦc : Φ.IsComplex) (Φ' : ι → Set (R → Option V))
    {ω : ℝ} {s : ℕ} (hs : 0 < s) (hext : IsExtendableRel (r := r) Φ Φ' ω s) (A : ι)
    {B : Finset R} {ψ : R → Option V} (hψ : ψ ∈ Φ.maps B) (v₀ : V) :
    ω * ((vertices Φ).toFinset.card : ℝ) ^ (Fintype.card R - B.card) ≤
      ((univ.filter fun φ : R → V => restrictT φ univ ∈ Φ.maps univ ∧
        (∀ x ∈ B, ψ x = some (φ x)) ∧
        ∀ B' : Finset R, B'.card = r → ¬ B' ⊆ B → restrictT φ B' ∈ Φ' A).card : ℝ) := by
  set ι0 : R → R × Fin s := fun x => (x, ⟨0, hs⟩)
  have hι0 : Function.Injective ι0 := fun x y h => (Prod.mk.inj h).1
  set VH := univ.image ι0
  set F := B.image ι0
  set φF : R × Fin s → V := fun p => (ψ p.1).getD v₀
  have hdψ : dom ψ = B := Φ.dom_eq B ψ hψ
  have hφF : ∀ x ∈ B, ψ x = some (φF (ι0 x)) := by
    intro x hx
    obtain ⟨w, hw⟩ := some_of_mem_dom hdψ hx
    simp [φF, ι0, hw]
  -- `φF` embeds `H[F]`
  have hemb : IsEmbedding ((simpleH hs).induce ↑F) Φ φF := by
    have hvert : ∀ v ∈ vertices ((simpleH hs).induce ↑F), ∃ x ∈ B, v = ι0 x := by
      rintro v ⟨B'', θ, hθ, x, hx⟩
      obtain ⟨rfl, hB''⟩ := (mem_induce_simpleH hs B B'' θ).1 hθ
      by_cases hxB : x ∈ B''
      · simp only [restrict, iota0, hxB, ite_true, Option.some.injEq] at hx
        exact ⟨x, hB'' hxB, hx.symm⟩
      · simp [restrict, hxB] at hx
    refine ⟨fun v hv v' hv' hvv => ?_, fun B'' θ hθ => ?_⟩
    · obtain ⟨x, hx, rfl⟩ := hvert v hv
      obtain ⟨y, hy, rfl⟩ := hvert v' hv'
      have h1 := hφF x hx
      have h2 := hφF y hy
      have : ψ x = ψ y := by rw [h1, h2, hvv]
      rw [Φ.inj B ψ hψ x y (by rw [h1]; simp) this]
    · obtain ⟨rfl, hB''⟩ := (mem_induce_simpleH hs B B'' θ).1 hθ
      have : comp φF (restrict (iota0 hs) B'') = restrict ψ B'' := by
        funext x
        by_cases hx : x ∈ B''
        · simp only [comp, restrict, iota0, hx, ite_true, Option.map_some]
          exact (hφF x (hB'' hx)).symm
        · simp [comp, restrict, hx]
      rw [this]
      exact hΦc B B'' hB'' ψ hψ
  have hVF : (VH \ F).card = Fintype.card R - B.card := by
    have : VH \ F = (univ \ B).image ι0 := by
      rw [image_sdiff_of_injOn (hι0.injOn) (subset_univ _)]
    rw [this, card_image_of_injective _ hι0, card_sdiff_of_subset (subset_univ _), card_univ]
  have key := hext (simpleH hs) VH F φF (fun _ => some A) (simpleH_isComplex hs)
    (simpleH_partite hs) (vertices_simpleH hs) (image_subset_image (subset_univ _)) hemb
  rw [hVF] at key
  refine key.trans ?_
  norm_cast
  set Ψ : (VH → V) → (R → V) := fun g x => g ⟨ι0 x, mem_image_of_mem _ (mem_univ x)⟩
  refine card_le_card_of_injOn Ψ (fun g hg => ?_) (fun g hg g' hg' h => ?_)
  · obtain ⟨f, hf, rfl⟩ := mem_image.1 hg
    obtain ⟨⟨-, hfmaps⟩, hfF, hfΦ'⟩ := (mem_filter.1 hf).2
    have hcomp : ∀ B' : Finset R, comp f (restrict (iota0 hs) B') = restrictT (fun x => f (ι0 x)) B' := by
      intro B'; funext x
      by_cases hx : x ∈ B' <;> simp [comp, restrict, iota0, restrictT, hx, ι0]
    refine mem_filter.2 ⟨mem_univ _, ?_, fun x hx => ?_, fun B' hB' hnot => ?_⟩
    · rw [show Ψ (fun w : VH => f w) = fun x => f (ι0 x) from rfl, ← hcomp]
      exact hfmaps univ _ rfl
    · rw [show Ψ (fun w : VH => f w) x = f (ι0 x) from rfl, hfF _ (mem_image_of_mem _ hx)]
      exact hφF x hx
    · rw [show Ψ (fun w : VH => f w) = fun x => f (ι0 x) from rfl, ← hcomp]
      refine hfΦ' B' hB' _ rfl ?_ A rfl
      rw [mem_induce_simpleH]
      exact fun h => hnot h.2
  · funext w
    obtain ⟨x, -, hx⟩ := mem_image.1 w.2
    have : w = ⟨ι0 x, mem_image_of_mem _ (mem_univ x)⟩ := Subtype.ext hx.symm
    rw [this]
    exact congrFun h x

end DesignsII
