/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib

/-!
# Definitions of the statement of Lemma `ext*` (Keevash, *The existence of designs II*)

All definitions used in the statement of `DesignsII.TParams.lemma_3_8` (labelled complexes,
adapted complexes, extensions and extendability, vector systems, molecules and atoms, the
template probability space and the template `M*`). The Palomar challenge repeats this file
verbatim, followed by the statement.
-/

@[expose] public section

namespace DesignsII

open Finset

section Complex

variable {R V : Type*} [DecidableEq R]

/-- The domain of a labelled map. -/
def dom (φ : R → Option V) : Set R := {x | φ x ≠ none}

/-- A labelled map is injective on its domain. -/
def InjOnDom (φ : R → Option V) : Prop :=
  ∀ x y, φ x ≠ none → φ x = φ y → x = y

/-- The restriction of a labelled map to `B`. -/
def restrict (φ : R → Option V) (B : Finset R) : R → Option V :=
  fun x => if x ∈ B then φ x else none

theorem injOnDom_restrict {φ : R → Option V} (hφ : InjOnDom φ) (B : Finset R) :
    InjOnDom (restrict φ B) := by
  intro x y hx hxy
  unfold restrict at hx hxy
  by_cases h1 : x ∈ B
  · by_cases h2 : y ∈ B
    · simp only [h1, h2, ite_true] at hx hxy
      exact hφ x y hx hxy
    · simp only [h1, h2, ite_true, ite_false] at hx hxy
      exact absurd hxy hx
  · simp [h1] at hx

/-- An `R`-system on `V`: for each finite `B ⊆ R`, a set of injective labelled maps with domain
`B`. -/
structure RSystem (R V : Type*) [DecidableEq R] where
  maps : Finset R → Set (R → Option V)
  dom_eq : ∀ B, ∀ φ ∈ maps B, dom φ = B
  inj : ∀ B, ∀ φ ∈ maps B, InjOnDom φ

namespace RSystem

/-- An `R`-system is an `R`-complex if it is closed under restriction. -/
def IsComplex (Φ : RSystem R V) : Prop :=
  ∀ B B', B' ⊆ B → ∀ φ ∈ Φ.maps B, restrict φ B' ∈ Φ.maps B'

end RSystem

end Complex

section Adapted

variable {R V : Type*} [DecidableEq R]

/-- `φσ`: the relabelling of `φ` by `σ`, restricted to `B`. -/
def relabel (φ : R → Option V) (σ : Equiv.Perm R) (B : Finset R) : R → Option V :=
  fun x => if x ∈ B then φ (σ x) else none

/-- `Φ` is `Σ`-adapted: `φσ ∈ Φ_B` whenever `φ ∈ Φ_{σ(B)}` and `σ ∈ Σ`. -/
def IsAdapted (Φ : RSystem R V) (Sg : Subgroup (Equiv.Perm R)) : Prop :=
  ∀ σ ∈ Sg, ∀ B, ∀ φ ∈ Φ.maps (B.map σ.toEmbedding), relabel φ σ B ∈ Φ.maps B

/-- The orbit of `ψ ∈ Φ_B`: the relabellings `ψσ` with `σ ∈ Σ` and `σ(B') = B`. -/
def orbit (Sg : Subgroup (Equiv.Perm R)) (ψ : R → Option V) (B : Finset R) :
    Set (R → Option V) :=
  {χ | ∃ σ ∈ Sg, ∃ B', B'.map σ.toEmbedding = B ∧ χ = relabel ψ σ B'}

end Adapted

section Extension

variable {R V W : Type*} [DecidableEq R]

/-- `V(Φ)`: the vertices used by the maps of `Φ`. -/
def vertices (Φ : RSystem R V) : Set V := {v | ∃ B, ∃ φ ∈ Φ.maps B, ∃ x, φ x = some v}

/-- Composition of a labelled map with a map of values. -/
def comp (f : W → V) (ψ : R → Option W) : R → Option V := fun x => (ψ x).map f

/-- `f` is a `Φ`-embedding of `H`. -/
def IsEmbedding (H : RSystem R W) (Φ : RSystem R V) (f : W → V) : Prop :=
  Set.InjOn f (vertices H) ∧ ∀ B, ∀ ψ ∈ H.maps B, comp f ψ ∈ Φ.maps B

/-- The labelled maps `ψ : R → Option (R × S)` that are partite: `ψ i = some (i, x)`. -/
def IsPartite {S : Type*} (ψ : R → Option (R × S)) : Prop :=
  ∀ i p, ψ i = some p → p.1 = i

omit [DecidableEq R] in
theorem injOnDom_of_partite {S : Type*} {ψ : R → Option (R × S)} (h : IsPartite ψ) :
    InjOnDom ψ := by
  intro x y hx hxy
  obtain ⟨p, hp⟩ := Option.ne_none_iff_exists'.1 hx
  rw [← h x p hp, h y p (hxy ▸ hp)]

/-- The complex `R(S)` of all partite maps. -/
def partiteMaps (R S : Type*) [DecidableEq R] : RSystem R (R × S) where
  maps B := {ψ | dom ψ = B ∧ IsPartite ψ}
  dom_eq _ _ h := h.1
  inj _ _ h := injOnDom_of_partite h.2

/-- `H[F]`: the maps of `H` with image in `F`. -/
def RSystem.induce (H : RSystem R W) (F : Set W) : RSystem R W where
  maps B := {ψ | ψ ∈ H.maps B ∧ ∀ x w, ψ x = some w → w ∈ F}
  dom_eq B ψ h := H.dom_eq B ψ h.1
  inj B ψ h := H.inj B ψ h.1

end Extension

section VDecomp

variable {R V ι Γ : Type*} [DecidableEq R]

/-- A vector system for a family of `R`-complexes on `R`, with values in `Γ` on `r`-sets. -/
structure VSystem (R ι Γ : Type*) [DecidableEq R] (r : ℕ) where
  A : ι → RSystem R R
  γ : ι → (R → Option R) → Γ

namespace VSystem

variable {r : ℕ} (S : VSystem R ι Γ r)

/-- `(A i)_r`: the maps of `A i` with an `r`-element domain. -/
def mapsR (i : ι) : Set (R → Option R) := {θ | ∃ B : Finset R, B.card = r ∧ θ ∈ (S.A i).maps B}

variable [AddCommMonoid Γ]

/-- The molecule `γ(φ)` of a `Φ`-embedding `φ` of `A i`: `γ(φ)_ψ = γ i θ` if `ψ = φ ∘ θ` with
`θ ∈ (A i)_r` (zero otherwise). -/
noncomputable def molecule (i : ι) (φ : R → V) (ψ : R → Option V) : Γ :=
  ∑ᶠ θ ∈ {θ | θ ∈ S.mapsR i ∧ comp φ θ = ψ}, S.γ i θ

/-- `∂Ψ = ∑_{(i, φ) ∈ Ψ} γ(φ)` for a finite set `Ψ` of embeddings. -/
noncomputable def boundary (Ψ : Finset (ι × (R → V))) (ψ : R → Option V) : Γ :=
  ∑ p ∈ Ψ, S.molecule p.1 p.2 ψ

end VSystem

end VDecomp

section MainStatement

variable {R V ι : Type*} [DecidableEq R] {D r : ℕ}

/-- `Σ^≤`: all restrictions `σ|_B` (as labelled maps `R → Option R`). -/
def sigmaLe (Sg : Subgroup (Equiv.Perm R)) : RSystem R R where
  maps B := {θ | ∃ σ ∈ Sg, θ = restrict (fun x => some (σ x)) B}
  dom_eq B θ h := by
    obtain ⟨σ, -, rfl⟩ := h
    ext x; simp [dom, restrict]
  inj B θ h := by
    obtain ⟨σ, -, rfl⟩ := h
    exact injOnDom_restrict (fun x y _ hxy => σ.injective (Option.some.inj hxy)) B

/-- The restriction of a vector to the orbit of `ψ ∈ Φ_B`. -/
noncomputable def onOrbit {M : Type*} [Zero M] (Sg : Subgroup (Equiv.Perm R))
    (J : (R → Option V) → M) (ψ : R → Option V) (B : Finset R) : (R → Option V) → M := by
  classical
  exact fun χ => if χ ∈ orbit Sg ψ B then J χ else 0

/-- The `γ`-atoms: nonzero restrictions `γ(φ)^O` of molecules of embeddings to orbits of `Φ_r`. -/
def atoms (S : VSystem R ι (Fin D → ℤ) r) (Sg : Subgroup (Equiv.Perm R)) (Φ : RSystem R V) :
    Set ((R → Option V) → (Fin D → ℤ)) :=
  {a | a ≠ 0 ∧ ∃ i φ, IsEmbedding (S.A i) Φ φ ∧ ∃ B : Finset R, B.card = r ∧
    ∃ ψ ∈ Φ.maps B, a = onOrbit Sg (S.molecule i φ) ψ B}

/-- `H ≤_γ G`: `G - H` is the sum of a multiset of `γ`-atoms. -/
def LeGamma (S : VSystem R ι (Fin D → ℤ) r) (Sg : Subgroup (Equiv.Perm R)) (Φ : RSystem R V)
    (H G : (R → Option V) → (Fin D → ℤ)) : Prop :=
  ∃ l : List ((R → Option V) → (Fin D → ℤ)), (∀ a ∈ l, a ∈ atoms S Sg Φ) ∧ G - H = l.sum

/-- Composition of a partial map `ψ : R → Option V` with a labelled map `θ : R → Option R`. -/
def compP (ψ : R → Option V) (θ : R → Option R) : R → Option V := fun x => (θ x).bind ψ

/-- `γ(ψ)` for a partial map `ψ` (Definition 2.22): `γ(ψ)_{ψθ} = γ_θ` for `θ ∈ (A i)_r` with
image in the domain of `ψ`. -/
noncomputable def moleculeP (S : VSystem R ι (Fin D → ℤ) r) (i : ι) (ψ : R → Option V)
    (χ : R → Option V) : Fin D → ℤ :=
  ∑ᶠ θ ∈ {θ | θ ∈ S.mapsR i ∧ (∀ x a, θ x = some a → ψ a ≠ none) ∧ compP ψ θ = χ}, S.γ i θ

/-- `γ[G]^{A_i}`: the maps `ψ ∈ Φ_r` with `γ(ψ) ≤_γ G` (Definition 2.23). -/
def gammaG (S : VSystem R ι (Fin D → ℤ) r) (Sg : Subgroup (Equiv.Perm R)) (Φ : RSystem R V)
    (G : (R → Option V) → (Fin D → ℤ)) (i : ι) : Set (R → Option V) :=
  {ψ | (∃ B : Finset R, B.card = r ∧ ψ ∈ Φ.maps B) ∧ LeGamma S Sg Φ (moleculeP S i ψ) G}

variable [Fintype V] [DecidableEq V]

open Classical in
/-- `(Φ, Φ')`-extendability (Definition 2.9) for restrictions `Φ' i ⊆ Φ_r`: for every complex
`H ⊆ R(Fin s)`, `F ⊆ V(H)`, `Φ`-embedding `φ` of `H[F]` and labelling `t` of the maps of `H` by restrictions
(`t ψ = some i`), the number of `Φ`-embeddings of `H` extending `φ` that map every `ψ ∉ H[F]` with
`t ψ = some i` and `r`-element domain into `Φ' i` is at least
`ω |V(Φ)|^{|V(H) ∖ F|}`. -/
def IsExtendableRel [Fintype R] (Φ : RSystem R V) (Φ' : ι → Set (R → Option V)) (ω : ℝ)
    (s : ℕ) : Prop :=
  ∀ (H : RSystem R (R × Fin s)) (VH F : Finset (R × Fin s)) (φ : R × Fin s → V)
    (t : (R → Option (R × Fin s)) → Option ι),
    H.IsComplex → (∀ B, H.maps B ⊆ (partiteMaps R (Fin s)).maps B) →
    vertices H = VH → F ⊆ VH → IsEmbedding (H.induce F) Φ φ →
    ω * ((vertices Φ).toFinset.card : ℝ) ^ (VH \ F).card ≤
      ((univ.filter fun f : R × Fin s → V => IsEmbedding H Φ f ∧ (∀ w ∈ F, f w = φ w) ∧
          ∀ B : Finset R, B.card = r → ∀ ψ ∈ H.maps B, ψ ∉ (H.induce ↑F).maps B → ∀ i,
            t ψ = some i → comp f ψ ∈ Φ' i).image fun f (w : VH) => f w).card

end MainStatement

section Template

open Matrix

variable {F K : Type*} [Field F] [Field K] [Algebra F K] {q r n z : ℕ}

/-- `M` is generic: every `r × r` submatrix (rows chosen by an injection) is nonsingular. -/
def IsGeneric (M : Matrix (Fin q) (Fin r) F) : Prop :=
  ∀ b : Fin r ↪ Fin q, (M.submatrix b id).det ≠ 0

end Template

section TemplateProb

open Matrix Equiv

variable {F K : Type*} [Field F] [Field K] [Algebra F K] [Fintype K] [DecidableEq K] {q r N : ℕ}

/-- `M y ∈ K^q`. -/
def mvec (M : Matrix (Fin q) (Fin r) F) (y : Fin r → K) : Fin q → K :=
  M.map (algebraMap F K) *ᵥ y

/-- Rows of `M` are pairwise distinct. -/
def DistinctRows (M : Matrix (Fin q) (Fin r) F) : Prop := Function.Injective M

end TemplateProb

section TemplateSpace

open Equiv

/-- Parameters of the template space. -/
structure TParams where
  (n q r z N NA Nact : ℕ)
  (hz : 0 < z) (hrq : r ≤ q) (hnN : n ≤ N) (hNA : 0 < NA) (hNact : 0 < Nact)

namespace TParams

variable (P : TParams)

/-- The coordinates. -/
abbrev Coord : Type :=
  Fin P.z ⊕ Finset (Fin P.n) ⊕ Finset (Fin P.n) ⊕ (Fin P.q → Fin P.n) ⊕ (Fin P.q → Fin P.n)

/-- The size of the permuted set at each coordinate. -/
def size : P.Coord → ℕ
  | .inl _ => P.N
  | .inr (.inl _) => P.z
  | .inr (.inr (.inl _)) => P.q
  | .inr (.inr (.inr (.inl _))) => P.NA
  | .inr (.inr (.inr (.inr _))) => P.Nact

/-- The sample space. -/
abbrev Ω : Type := ∀ c : P.Coord, Perm (Fin (P.size c))

variable {P}

/-- `f_j(x)` as an element of `[N]`. -/
def fval (ω : P.Ω) (j : Fin P.z) (x : Fin P.n) : Fin P.N :=
  ω (.inl j) (Fin.castLE P.hnN x)

/-- `T_e`. -/
def Tval (ω : P.Ω) (e : Finset (Fin P.n)) : Fin P.z :=
  ω (.inr (.inl e)) ⟨0, P.hz⟩

open Classical in
/-- `π_e(x)` (junk outside `|e| = r`, `x ∈ e`). -/
noncomputable def pival (ω : P.Ω) (e : Finset (Fin P.n)) (x : Fin P.n) : Option (Fin P.q) :=
  if h : e.card = P.r ∧ x ∈ e then
    some (ω (.inr (.inr (.inl e))) (Fin.castLE P.hrq ((e.orderIsoOfFin h.1).symm ⟨x, h.2⟩)))
  else none

/-- `A_φ` (an index in `[|𝒜|]`). -/
def Aval (ω : P.Ω) (φ : Fin P.q → Fin P.n) : Fin P.NA :=
  ω (.inr (.inr (.inr (.inl φ)))) ⟨0, P.hNA⟩

/-- `φ` is activated (threshold `k`). -/
def Active (ω : P.Ω) (φ : Fin P.q → Fin P.n) (k : ℕ) : Prop :=
  (ω (.inr (.inr (.inr (.inr φ)))) ⟨0, P.hNact⟩ : ℕ) < k

end TParams

namespace TParams

variable {P : TParams}

/-- The edges `φ(Q)`: the `r`-subsets of the image of `φ`. -/
def edges (φ : Fin P.q → Fin P.n) : Finset (Finset (Fin P.n)) :=
  (univ.image φ).powersetCard P.r

variable {F K : Type*} [Field F] [Field K] [Algebra F K] [Fintype K] [DecidableEq K]

/-- `φ` passes all the random tests in the definition of `M*_j` (Definition 3.2): `A_φ = a₀`,
`φ` is activated, `T_e = j` and `π_e φ = id` on every edge `e ⊆ φ(Q)`, and `f_j ∘ φ = M y`. -/
def CopyOK (M : Matrix (Fin P.q) (Fin P.r) F) (κ : Fin P.N ≃ K) (j : Fin P.z) (a₀ : Fin P.NA)
    (k : ℕ) (φ : Fin P.q → Fin P.n) (ω : P.Ω) : Prop :=
  Aval ω φ = a₀ ∧ Active ω φ k ∧ (∀ e ∈ edges φ, Tval ω e = j) ∧
    (∀ e ∈ edges φ, ∀ i, φ i ∈ e → pival ω e (φ i) = some i) ∧
    ∃ y, ∀ i, κ (fval ω j (φ i)) = mvec M y i

end TParams

end TemplateSpace

section General

open Equiv

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {a : ι → ℕ}

open Classical in
/-- Probability under independent uniform permutations (general index type). -/
noncomputable def probG (A : (∀ i, Perm (Fin (a i))) → Prop) : ℝ :=
  ((univ.filter A).card : ℝ) / ∏ i, ((a i).factorial : ℝ)

end General

section Labelled

variable {F K : Type*} [Field F] [Field K] [Algebra F K] [Fintype K] [DecidableEq K]

namespace TParams

variable {P : TParams} {D r : ℕ}

open Classical in
/-- The template `M*(ω)` as a set of embeddings `(A, φ)`. -/
noncomputable def templateSet (M : Matrix (Fin P.q) (Fin P.r) F) (κ : Fin P.N ≃ K)
    (a₀ : (Fin P.q → Fin P.n) → Fin P.NA) (k : (Fin P.q → Fin P.n) → ℕ) (ω : P.Ω) :
    Finset (Fin P.NA × (Fin P.q → Fin P.n)) :=
  univ.filter fun p => p.1 = a₀ p.2 ∧ ∃ j, CopyOK M κ j (a₀ p.2) (k p.2) p.2 ω

end TParams

end Labelled

section Rates

variable {F K : Type*} [Field F] [Fintype F] [DecidableEq F] [Field K] [Algebra F K] [Fintype K]
  [DecidableEq K]

namespace TParams

variable {P : TParams} {D r : ℕ}

/-- The passing-probability lower bound `p`. -/
noncomputable def pRate (P : TParams) (kmin : ℕ) : ℝ :=
  1 / (2 * (P.N : ℝ) ^ (P.q - P.r)) * (1 / (P.z : ℝ)) ^ P.q.choose P.r *
    (((P.q - P.r).factorial : ℝ) / (P.q.factorial : ℝ)) ^ P.q.choose P.r *
    (1 / (P.NA : ℝ)) * ((kmin : ℝ) / P.Nact)

/-- The first-stage constant. -/
noncomputable def c₁ (P : TParams) (m Δ : ℕ) : ℝ :=
  4 * P.z * ((m * (P.q ^ P.r * P.q.choose P.r * Δ) : ℕ) : ℝ) ^ 2 + 1

/-- The second-stage constant. -/
noncomputable def c₂ (P : TParams) (m Δ Smax : ℕ) : ℝ :=
  4 * Smax * ((P.z * P.q ^ P.r + P.z) * (m * (P.q.choose P.r * Δ)) : ℕ) *
    (((2 * P.q.choose P.r + 2) * (m * Δ * (P.z * P.q ^ P.r)) : ℕ) : ℝ) + 1

/-- The conflict constant. -/
def Kc (P : TParams) : ℕ :=
  P.q ^ (P.r + 1) * P.n ^ (P.q - (P.r + 1)) * (P.q ^ P.r * P.n ^ (P.q - P.r)) * (1 + P.q.choose P.r)

end TParams

end Rates

end DesignsII
