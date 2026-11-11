/-
Machine-generated (Claude, Aristotle), no line written by a person. Copyleft: GPL-3.0-or-later.

# Week 7: covering maps, lifting, fibrations, the mapping cylinder, `πₙ` abelian

This file proves the second half of week 7 of the book. A continuous `p : E → B` is a
covering map if every point of `B` has an evenly covered open neighbourhood (`def:covering-map`,
`def:evenly-covered`); its fibres are discrete. Two lifts of one map from a connected space that
agree at one point agree everywhere (`lem:unique-lift`), by the book's open-and-closed proof.
Path lifting and homotopy lifting hold for every covering map (`thm:lifting-general`), by week
6's proofs, and so a loop with a lift that is not a loop is not trivial in `π₁`
(`cor:nonclosed-lift`). Then what the lecture added: locally trivial fibrations
(`def:fibration`), their pullbacks and those of coverings (`lem:pullback-fibration`), coverings
as fibrations with discrete fibre, sections of a trivial fibration with discrete fibre and the
coverings of `[0, 1]` (`lem:covering-interval`), and the universal cover
(`def:universal-cover`). Last, the mapping cylinder (`def:mapping-cylinder`,
`prop:mapping-cylinder`) and Eckmann–Hilton: `πₙ(X, x)` is abelian for `n ≥ 2`
(`thm-3n-eh`).

Departures from the book:
* "`p` maps the sheet `S` homeomorphically onto `U`" is stated as: `p` is one to one on `S`,
  `p(S) = U`, and a subset `W ⊆ U` is open iff `S ∩ p⁻¹(W)` is open. As `S` and `U` are open,
  their open subsets are the open sets of `E` and `B` inside them, so this says exactly that
  `p : S → U` is a continuous bijection whose inverse is continuous.
* `thm:lifting-general` is proved by week 6's grid proofs with "the sheet over `U` containing" in
  place of "the interval over `U` containing", as the book says. One change in homotopy lifting:
  week 6 lifted the left edge of each row through the point already lifted, a lift of a path
  from any `s₀` that `ℝ → S¹` gives by a shift and a general covering does not; here the whole
  left edge is lifted once, at the start. Path lifting starts at `s = 0`, as in the book.
* "Every covering of `[0, 1]` is trivial" (`lem:covering-interval` (2)) is stated with the fibre
  `F = p⁻¹(0)`, and its trivialisation over `[0, j/N]` is a pair of inverse maps rather than a
  homeomorphism of subspaces (see its docstring). Not formalised: the second proof of
  `lem:unique-lift`, and the converse half of "coverings are the locally trivial fibrations with
  discrete fibre" (a covering of a connected base is a fibration).
* `def:universal-cover`'s standing hypothesis, `B` path-connected, is the third condition of
  `IsUniversalCover`.
* `πₙ` is Mathlib's `HomotopyGroup`; the course does not define it.
* From Analysis I and Munkres, through the bridges: the connectedness of `I` and of `I × I`; the
  Lebesgue number lemma on `I` and on `I × I`; in
  `prop:mapping-cylinder`, that `M_f × I` is a quotient of `((X × I) ⊔ Y) × I` (Munkres,
  Exercise 29.11, `continuous_quotient_prod_I` of `Week03Hot.lean`, in the book's "not proved"
  list) and that `(A ⊔ Y) × I` is the disjoint union of `A × I` and `Y × I`.

New to Lean? Read `Course/README.md` first.
-/
import Course.Week03Hot
import Course.Week02Glue
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Topology.Homotopy.HomotopyGroup

-- Bookkeeping. `E`, `B`, `Y` below are spaces (types; `u v w` are their "universe levels",
-- which you may ignore): `E` the total space, `B` the base (the letters of the lecture, from the
-- French *espace* and *base*). `open Set` lets us write `range`, `univ` without prefixes.
universe u v w

set_option warn.classDefReducibility false

namespace Course

open Set

noncomputable section

variable {E : Type u} {B : Type v} {Y : Type w}

/-! ## Covering maps (`def:evenly-covered`, `def:covering-map`) -/

section Covering
variable [TopSpace E] [TopSpace B] [TopSpace Y]

/-- `p` maps `S` homeomorphically onto `U`, for open `S ⊆ E` and `U ⊆ B`: `p` is one to one on
`S`, `p(S) = U`, and a subset `W ⊆ U` is open iff `S ∩ p⁻¹(W)` is open. (The last condition says
that `p : S → U` and its inverse are both continuous; see the departures above.) Mathlib: the
hypotheses of `IsOpen.trivializationDiscrete`.

Lean: `InjOn p S` is "`p` is one to one on `S`"; `p '' S` is the image `p(S)`. -/
def MapsHomeomorphically (p : E → B) (S : Set E) (U : Set B) : Prop :=
  InjOn p S ∧ p '' S = U ∧ ∀ W ⊆ U, IsOpen W ↔ IsOpen (S ∩ p ⁻¹' W)

/-- **`def:evenly-covered`**: an open `U ⊆ B` is evenly covered by `p : E → B` if `p⁻¹(U)` is a
disjoint union of open subsets of `E`, the sheets over `U`, each mapped homeomorphically onto `U`
by `p`. Mathlib: `IsEvenlyCovered` (in the product form `p⁻¹(U) ≅ U × F`).

In Lean the sheets are a family `𝒮` of subsets of `E` (a `Set (Set E)`): each is open, two
different ones are disjoint, their union `⋃₀ 𝒮` is `p⁻¹(U)`, and each is mapped
homeomorphically onto `U`. -/
def EvenlyCovered (p : E → B) (U : Set B) : Prop :=
  IsOpen U ∧ ∃ 𝒮 : Set (Set E), (∀ S ∈ 𝒮, IsOpen S) ∧
    (∀ S ∈ 𝒮, ∀ S' ∈ 𝒮, S ≠ S' → Disjoint S S') ∧ p ⁻¹' U = ⋃₀ 𝒮 ∧
    ∀ S ∈ 𝒮, MapsHomeomorphically p S U

/-- **`def:covering-map`**: a continuous `p : E → B` is a covering map if every point of `B` has an
evenly covered open neighbourhood. (The preimage may be empty: `p` need not be onto.)
Mathlib: `IsCoveringMap` (see `isCovering_iff_mathlib`). -/
def IsCovering (p : E → B) : Prop :=
  Continuous p ∧ ∀ b : B, ∃ U : Set B, b ∈ U ∧ EvenlyCovered p U

variable {p : E → B}

/-- A set is open if each of its points has an open neighbourhood inside it: it is the union of
these neighbourhoods. Mathlib: `isOpen_iff_forall_mem_open`. -/
theorem isOpen_of_forall_nhd {A : Set Y} (h : ∀ y ∈ A, ∃ W : Set Y, IsOpen W ∧ y ∈ W ∧ W ⊆ A) :
    IsOpen A := by
  -- `A` is the union of all open `W ⊆ A`: each point of `A` lies in one (`h`).
  have : A = ⋃₀ {W | IsOpen W ∧ W ⊆ A} := by
    ext y
    constructor
    · intro hy
      obtain ⟨W, hW, hyW, hWA⟩ := h y hy
      exact ⟨W, ⟨hW, hWA⟩, hyW⟩
    · rintro ⟨W, ⟨-, hWA⟩, hyW⟩
      exact hWA hyW
  rw [this]
  exact isOpen_sUnion fun W hW => hW.1

/-- Every point `e` of `E` lies in a sheet over an evenly covered neighbourhood of `p(e)`: an
open `S ∋ e` on which `p` is one to one. (Lean: `⟨S, hS, …⟩` packs `S` with its properties.) -/
theorem IsCovering.exists_sheet (hp : IsCovering p) (e : E) :
    ∃ S : Set E, IsOpen S ∧ e ∈ S ∧ InjOn p S := by
  -- Take an evenly covered `U ∋ p(e)`; then `e ∈ p⁻¹(U)`, the union of the sheets.
  obtain ⟨U, hU, -, 𝒮, hopen, -, hpre, hhom⟩ := hp.2 (p e)
  have he : e ∈ ⋃₀ 𝒮 := hpre ▸ hU
  obtain ⟨S, hS, heS⟩ := he
  exact ⟨S, hopen S hS, heS, (hhom S hS).1⟩

/-- The inverse of `p` on a sheet: if `p` maps the open `S` homeomorphically onto `U`, every
continuous `h : Y → B` with values in `U` lifts to a continuous `σ : Y → S`, `σ(y)` being the
point of `S` over `h(y)`. Mathlib: `IsEvenlyCovered.toTrivialization`, `Trivialization.invFun`.

The proof: for open `V ⊆ E`, `σ⁻¹(V) = h⁻¹(p(S ∩ V))`, and `p(S ∩ V)` is open because
`S ∩ p⁻¹(p(S ∩ V)) = S ∩ V` is (`p` is one to one on `S`). -/
theorem MapsHomeomorphically.exists_lift {S : Set E} {U : Set B}
    (hS : MapsHomeomorphically p S U) (hSo : IsOpen S) {h : Y → B} (hh : Continuous h)
    (hU : ∀ y, h y ∈ U) : ∃ σ : Y → E, Continuous σ ∧ (∀ y, σ y ∈ S) ∧ ∀ y, p (σ y) = h y := by
  obtain ⟨hinj, him, hopen⟩ := hS
  -- Step 1. For each `y`, `h(y) ∈ U = p(S)`: choose `σ(y) ∈ S` over `h(y)`.
  have hex : ∀ y, ∃ x, x ∈ S ∧ p x = h y := fun y => by
    have := hU y
    rw [← him] at this
    exact this
  choose σ hσS hσp using hex
  refine ⟨σ, fun V hV => ?_, hσS, hσp⟩
  -- Step 2. `W = p(S ∩ V)` lies in `U`, and `S ∩ p⁻¹(W) = S ∩ V` is open; so `W` is open.
  have hW : IsOpen (p '' (S ∩ V)) := by
    have hWU : p '' (S ∩ V) ⊆ U := him ▸ image_mono inter_subset_left
    rw [hopen _ hWU]
    convert hSo.inter hV using 1
    ext x
    constructor
    · rintro ⟨hxS, x', ⟨hx'S, hx'V⟩, hpx⟩
      exact ⟨hxS, hinj hx'S hxS hpx ▸ hx'V⟩
    · rintro ⟨hxS, hxV⟩
      exact ⟨hxS, x, ⟨hxS, hxV⟩, rfl⟩
  -- Step 3. `σ(y) ∈ V` iff `h(y) ∈ W`: if `h(y) = p(x)` with `x ∈ S ∩ V`, then `σ(y) = x`, both
  -- being points of `S` over `h(y)`. So `σ⁻¹(V) = h⁻¹(W)`, open.
  convert hh _ hW using 1
  ext y
  constructor
  · intro hy
    exact ⟨σ y, ⟨hσS y, hy⟩, hσp y⟩
  · rintro ⟨x, ⟨hxS, hxV⟩, hpx⟩
    show σ y ∈ V
    rwa [hinj (hσS y) hxS ((hσp y).trans hpx.symm)]

/-- `def:covering-map`, the last claim: the fibres of a covering map are discrete. Every subset
`A` of the fibre `p⁻¹(b)` is open in it. Mathlib: `IsEvenlyCovered.discreteTopology_fiber`.

The book's proof: each sheet is open and meets the fibre once. (Lean: the fibre `p⁻¹(b)` is
`p ⁻¹' {b}`, a subspace of `E`; a point `a` of it is a point `a.1 : E` with `p(a.1) = b`.) -/
theorem IsCovering.discrete_fibre (hp : IsCovering p) (b : B) (A : Set (p ⁻¹' {b})) :
    IsOpen A := by
  -- For each point `a` of the fibre choose an open `S(a) ∋ a` on which `p` is one to one.
  -- (Lean: `choose` turns "for each `e` there is `S`" into a map `e ↦ S(e)`.)
  choose S hSo haS hinj using hp.exists_sheet
  -- Then `A` is the trace on the fibre of the open `⋃_{a ∈ A} S(a)`, so it is open in the
  -- fibre (`def-1-14`).
  refine ⟨⋃ a ∈ A, S a.1, isOpen_iUnion fun a => isOpen_iUnion fun _ => hSo a.1, ?_⟩
  ext x
  simp only [mem_preimage, mem_iUnion]
  constructor
  · intro hx
    exact ⟨x, hx, haS x.1⟩
  -- If `x ∈ S(a)` with `a ∈ A`: both `x` and `a` lie in `S(a)` over `b`, and `p` is one to one
  -- on `S(a)`, so `x = a ∈ A`. A sheet meets the fibre once.
  · rintro ⟨a, ha, hxa⟩
    have : x.1 = a.1 := hinj a.1 hxa (haS a.1) (by rw [x.2, a.2])
    rwa [Subtype.ext this]

/-! ## Uniqueness of lifts (`lem:unique-lift`) -/

/-- **`lem:unique-lift`**: let `p : E → B` be a covering and `Y` connected. Two continuous
`f̃₁, f̃₂ : Y → E` with `p f̃₁ = p f̃₂` (`hpf`) that agree at one point `y₀` (`h0`) agree
everywhere. Mathlib: `IsCoveringMap.eq_of_comp_eq`.

The book's proof: the set where they agree is open and closed. -/
theorem IsCovering.eq_of_lift (hp : IsCovering p) (hY : Connected Y) {f₁ f₂ : Y → E}
    (h₁ : Continuous f₁) (h₂ : Continuous f₂) (hpf : ∀ y, p (f₁ y) = p (f₂ y)) {y₀ : Y}
    (h0 : f₁ y₀ = f₂ y₀) (y : Y) : f₁ y = f₂ y := by
  -- Step 1. Every `y` has an open neighbourhood `W` on which "`f̃₁ = f̃₂`" holds at every point
  -- if it holds at `y`, and fails at every point if it fails at `y`.
  have key : ∀ y, ∃ W : Set Y, IsOpen W ∧ y ∈ W ∧ ∀ z ∈ W, (f₁ z = f₂ z ↔ f₁ y = f₂ y) := by
    intro y
    -- Let `U` be an evenly covered neighbourhood of `p f̃₁(y) = p f̃₂(y)`, `S` the sheet over
    -- `U` containing `f̃₁(y)` and `S'` the one containing `f̃₂(y)`.
    obtain ⟨U, hU, -, 𝒮, hopen, hdisj, hpre, hhom⟩ := hp.2 (p (f₁ y))
    obtain ⟨S, hS, h1S⟩ : f₁ y ∈ ⋃₀ 𝒮 := hpre ▸ hU
    obtain ⟨S', hS', h2S'⟩ : f₂ y ∈ ⋃₀ 𝒮 := hpre ▸ (show p (f₂ y) ∈ U from hpf y ▸ hU)
    -- `W = f̃₁⁻¹(S) ∩ f̃₂⁻¹(S')` is an open neighbourhood of `y`.
    refine ⟨f₁ ⁻¹' S ∩ f₂ ⁻¹' S', (h₁ S (hopen S hS)).inter (h₂ S' (hopen S' hS')),
      ⟨h1S, h2S'⟩, fun z ⟨hz1, hz2⟩ => ?_⟩
    by_cases hSS : S = S'
    -- If `S = S'`: `p` is one to one on `S`, and `p f̃₁ = p f̃₂`; so `f̃₁ = f̃₂` at `z` and at
    -- `y` alike.
    · subst hSS
      have hinj := (hhom S hS).1
      exact iff_of_true (hinj hz1 hz2 (hpf z)) (hinj h1S h2S' (hpf y))
    -- If `S ≠ S'`: the sheets are disjoint, so `f̃₁ ≠ f̃₂` at `z` and at `y` alike.
    · have hd := hdisj S hS S' hS' hSS
      have hne : ∀ a, a ∈ S → a ∈ S' → False := fun a ha ha' =>
        Set.disjoint_left.mp hd ha ha'
      exact iff_of_false (fun h => hne _ hz1 (h ▸ hz2)) (fun h => hne _ h1S (h ▸ h2S'))
  -- Step 2. So the set `A` where they agree is open, and so is its complement.
  set A : Set Y := {z | f₁ z = f₂ z} with hA
  have hAo : IsOpen A := isOpen_of_forall_nhd fun z hz => by
    obtain ⟨W, hW, hzW, hiff⟩ := key z
    exact ⟨W, hW, hzW, fun z' hz' => (hiff z' hz').mpr hz⟩
  have hAc : IsOpen Aᶜ := isOpen_of_forall_nhd fun z hz => by
    obtain ⟨W, hW, hzW, hiff⟩ := key z
    exact ⟨W, hW, hzW, fun z' hz' h => hz ((hiff z' hz').mp h)⟩
  -- Step 3. `Y` is connected and `y₀ ∈ A`, so `Aᶜ` is empty and `y ∈ A`.
  rcases hY A Aᶜ hAo hAc (union_compl_self A) disjoint_compl_right with h | h
  · exact absurd (h ▸ (h0 : y₀ ∈ A)) (notMem_empty y₀)
  · by_contra hy
    exact notMem_empty y (h ▸ (hy : y ∈ Aᶜ))

/-- A lift of a constant map from a connected space is constant: `lem:unique-lift` applied to
`f̃` and the constant map at `f̃(y₀)`. (`hc` says that `p(f̃(y)) = p(f̃(y₀))` for every `y`.)
Mathlib: `IsCoveringMap.const_of_comp`. -/
theorem IsCovering.const_of_lift (hp : IsCovering p) (hY : Connected Y) {f : Y → E}
    (hf : Continuous f) {y₀ : Y} (hc : ∀ y, p (f y) = p (f y₀)) (y : Y) : f y = f y₀ :=
  hp.eq_of_lift hY (f₂ := fun _ => f y₀) hf continuous_const hc rfl y

end Covering

/-! ## The bridge to Mathlib's covering maps -/

section Bridge
variable [tE : TopSpace E] [tB : TopSpace B]

/-- **Bridge.** A covering map of the course is one of Mathlib's (`IsCoveringMap`), for the same
topologies (`toMathlib`), and conversely. Mathlib's definition asks, for each `b ∈ B`, for an open
`U ∋ b` and a homeomorphism `p⁻¹(U) ≅ U × p⁻¹(b)` over `U`, with `p⁻¹(b)` discrete: the product
form of the sheets (the remark after `def:covering-map`). Going there, the sheets become the points
of a discrete space (Mathlib's `IsOpen.trivializationDiscrete`); coming back, the sheets are the
sets `U × {a}` carried back to `E`. -/
theorem isCovering_iff_mathlib (p : E → B) :
    IsCovering p ↔ @IsCoveringMap E B tE.toMathlib tB.toMathlib p := by
  -- Work with Mathlib's versions of the two topologies, which have the same open sets.
  let _ := tE.toMathlib
  let _ := tB.toMathlib
  constructor
  -- (→) Let `b ∈ B`, and `U ∋ b` evenly covered, with sheets `𝒮`.
  · rintro ⟨hpc, hcov⟩ b
    obtain ⟨U, hbU, hUo, 𝒮, hopen, hdisj, hpre, hhom⟩ := hcov b
    by_cases h𝒮 : 𝒮.Nonempty
    -- If there are sheets, make `𝒮` a discrete space; `E` is not empty (a sheet maps onto
    -- `U ∋ b`), and Mathlib builds the homeomorphism `p⁻¹(U) ≅ U × 𝒮` from the sheets.
    · let _ : TopologicalSpace 𝒮 := ⊥
      have : DiscreteTopology 𝒮 := ⟨rfl⟩
      have : Nonempty 𝒮 := h𝒮.to_subtype
      obtain ⟨S, hS⟩ := h𝒮
      obtain ⟨e, -, -⟩ := (hhom S hS).2.1.symm ▸ hbU
      have : Nonempty (B → E) := ⟨fun _ => e⟩
      have hUo' : _root_.IsOpen U := hUo
      let t := hUo'.trivializationDiscrete (f := p) (fun S : 𝒮 => (S : Set E)) U
        (fun S W hW => by rw [inter_comm]; exact (hhom S.1 S.2).2.2 W hW)
        (fun S => (hhom S.1 S.2).1)
        (fun S => by rw [SurjOn, (hhom S.1 S.2).2.1])
        (fun S S' h => hdisj S.1 S.2 S'.1 S'.2 (fun h' => h (Subtype.ext h')))
        (by rw [hpre, sUnion_eq_iUnion])
      exact (IsEvenlyCovered.of_trivialization (t := t) hbU).to_isEvenlyCovered_preimage
    -- If there are none, `p⁻¹(U) = ∅`, and `U` is evenly covered with the empty fibre.
    · have hempty : p ⁻¹' U = ∅ := by
        rw [hpre, sUnion_eq_empty]
        intro S hS
        exact absurd ⟨S, hS⟩ h𝒮
      have hUo' : _root_.IsOpen U := hUo
      exact (IsEvenlyCovered.of_preimage_eq_empty Empty (hUo'.mem_nhds hbU)
        hempty).to_isEvenlyCovered_preimage
  -- (←) `p` is continuous (Mathlib: `IsCoveringMap.continuous`). Let `b ∈ B`, with `U ∋ b` and
  -- `H : p⁻¹(U) ≅ U × F` over `U`, `F = p⁻¹(b)` discrete.
  · intro hcov
    refine ⟨(continuous_iff_mathlib p).mpr hcov.continuous, fun b => ?_⟩
    obtain ⟨hdisc, U, hbU, hU, hpU, H, hH⟩ := hcov b
    -- The sheet `T(a)` over `U`, for `a ∈ F`: the points `e` of `p⁻¹(U)` with `H(e) ∈ U × {a}`.
    -- (Lean: `∃ he : P, Q he` is "`P` holds, and `Q` holds for that proof of `P`".)
    let T : p ⁻¹' {b} → Set E := fun a => {e | ∃ he : p e ∈ U, (H ⟨e, he⟩).2 = a}
    -- `T(a)` is open: it is the preimage of the open `{a}` (`F` is discrete) under the
    -- continuous `e ↦ (H e)₂`, inside the open `p⁻¹(U)`.
    have hTo : ∀ a, _root_.IsOpen (T a) := fun a => by
      have h1 : _root_.IsOpen ((fun z => (H z).2) ⁻¹' {a}) :=
        (_root_.continuous_snd.comp H.continuous).isOpen_preimage _ (isOpen_discrete _)
      convert hpU.isOpenMap_subtype_val _ h1 using 1
      ext e
      constructor
      · rintro ⟨he, rfl⟩
        exact ⟨⟨e, he⟩, rfl, rfl⟩
      · rintro ⟨⟨e', he⟩, h, rfl⟩
        exact ⟨he, h⟩
    -- Two points of `T(a)` over the same point of `U` are equal, `H` being one to one.
    have hTinj : ∀ a, InjOn p (T a) := fun a e he e' he' hpe => by
      obtain ⟨h1, h1'⟩ := he
      obtain ⟨h2, h2'⟩ := he'
      have : H ⟨e, h1⟩ = H ⟨e', h2⟩ :=
        Prod.ext (Subtype.ext (by rw [hH, hH]; exact hpe)) (h1'.trans h2'.symm)
      exact congrArg Subtype.val (H.injective this)
    -- `p(T(a)) = U`: the point `H⁻¹(u, a)` lies in `T(a)` over `u`.
    have hTim : ∀ a, p '' T a = U := fun a => by
      ext u
      constructor
      · rintro ⟨e, ⟨he, -⟩, rfl⟩
        exact he
      · intro hu
        refine ⟨(H.symm (⟨u, hu⟩, a)).1, ⟨(H.symm (⟨u, hu⟩, a)).2, ?_⟩, ?_⟩
        · simp
        · have := hH (H.symm (⟨u, hu⟩, a))
          simp only [Homeomorph.apply_symm_apply] at this
          exact this.symm
    refine ⟨U, hbU, hU, range T, ?_, ?_, ?_, ?_⟩
    · rintro _ ⟨a, rfl⟩
      exact hTo a
    -- Different sheets are disjoint: a point of `T(a) ∩ T(a')` has `a = (H e)₂ = a'`.
    · rintro _ ⟨a, rfl⟩ _ ⟨a', rfl⟩ hne
      refine Set.disjoint_left.mpr fun e ⟨h1, h1'⟩ ⟨h2, h2'⟩ => hne ?_
      rw [← h1', ← h2']
    -- Every point of `p⁻¹(U)` lies in the sheet `T((H e)₂)`.
    · ext e
      constructor
      · intro he
        exact ⟨T (H ⟨e, he⟩).2, ⟨_, rfl⟩, he, rfl⟩
      · rintro ⟨_, ⟨a, rfl⟩, he, -⟩
        exact he
    -- Each sheet is mapped homeomorphically onto `U`: `W ⊆ U` is open iff `T(a) ∩ p⁻¹(W)` is,
    -- since `p` is continuous and open (Mathlib: `IsCoveringMap.isOpenMap`) and
    -- `p(T(a) ∩ p⁻¹(W)) = W`.
    · rintro _ ⟨a, rfl⟩
      refine ⟨hTinj a, hTim a, fun W hWU => ⟨fun hW => (hTo a).inter
        (hcov.continuous.isOpen_preimage W hW), fun hW => ?_⟩⟩
      have : p '' (T a ∩ p ⁻¹' W) = W := by
        rw [image_inter_preimage, hTim a, inter_eq_right.mpr hWU]
      rw [← this]
      exact hcov.isOpenMap _ hW

end Bridge

/-! ## Lifting for any covering map (`thm:lifting-general`, `cor:nonclosed-lift`)

The book proves existence by week 6's proofs (`Week06.lean`: `exists_grid_I`, `strip_lift`,
`exists_lift_path`, `exists_grid_II`, `exists_lift_homotopy`) with "the sheet over `U`
containing" in place of "the interval over `U` containing", and so do the proofs below: the two
arcs become the evenly covered open sets, and the inverse of `p` on an arc, moved by an integer,
becomes the inverse of `p` on a sheet (`MapsHomeomorphically.exists_lift`). Uniqueness is
`lem:unique-lift`, which replaces week 6's `lem:integer-difference`. -/

section Lifting
variable [tE : TopSpace E] [tB : TopSpace B] {p : E → B}

/-- The Lebesgue number lemma on `I` (Analysis I: `I` is compact, Mathlib's
`lebesgue_number_lemma_of_metric`, through `isOpen_I_iff`), for the cover of `I` by the
preimages under `f` of evenly covered open sets: for some `N ≥ 1`, `f` carries each
`[j/N, (j+1)/N]`, `j < N`, into an evenly covered `U`. As week 6's `exists_grid_I`, with
evenly covered sets in place of the two arcs. -/
theorem IsCovering.exists_grid_I (hp : IsCovering p) {f : I → B} (hf : Continuous f) :
    ∃ N : ℕ, 0 < N ∧ ∀ j : ℕ, j < N → ∃ U, EvenlyCovered p U ∧ ∀ s : I, (j : ℝ) / N ≤ s →
      (s : ℝ) ≤ ((j : ℝ) + 1) / N → f s ∈ U := by
  -- For each `b ∈ B` choose an evenly covered `U(b) ∋ b`. The sets `f⁻¹(U(b))` are open in `I`
  -- and cover it; so there is `δ > 0` such that every ball `B(s, δ)` of `I` lies in one of them.
  choose U hbU hU using hp.2
  obtain ⟨δ, hδ, hball⟩ := lebesgue_number_lemma_of_metric (isCompact_univ (X := unitInterval))
    (c := fun b => f ⁻¹' U b) (fun b => (isOpen_I_iff _).mp (hf _ (hU b).1))
    (fun s _ => mem_iUnion.mpr ⟨f s, hbU (f s)⟩)
  -- Take `N = n + 1` with `1/(n + 1) < δ` (Analysis I: the Archimedean property).
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hδ
  refine ⟨n + 1, n.succ_pos, fun j hj => ?_⟩
  obtain ⟨h0, h01, h1⟩ := grid_facts n.succ_pos hj
  -- The ball of radius `δ` about `j/N` lies in some `f⁻¹(U(b))`; and every `s` in
  -- `[j/N, (j + 1)/N]` is within `1/N < δ` of `j/N`.
  obtain ⟨b, hb⟩ := hball (I.pt ((j : ℝ) / (n + 1 : ℕ))) (mem_univ _)
  refine ⟨U b, hU b, fun s hs1 hs2 => hb ?_⟩
  have e : ((j : ℝ) + 1) / (n + 1 : ℕ) = (j : ℝ) / (n + 1 : ℕ) + 1 / ((n : ℝ) + 1) := by
    push_cast; ring
  rw [Metric.mem_ball, Subtype.dist_eq, Real.dist_eq, I.coe_pt h0 (h01.trans h1), abs_lt]
  constructor <;> linarith

/-- The heart of both lifting theorems: a continuous `G : I × I → B` that carries each column
`[j/N, (j+1)/N] × I` into an evenly covered set (`hcol`), and has a lift `ℓ` along its left edge
(`hpℓ`: `p(ℓ(t)) = G(0, t)`), has a lift `L` with `L(0, t) = ℓ(t)`. As week 6's `strip_lift`.

The proof is the book's "lifting piece by piece", a column at a time from the left: over column
`j`, carried into the evenly covered `U`, take the inverse of `p` on the sheet over `U`
containing the point `L(j/N, 0)` already lifted; the new lift and the old then agree along the
whole edge `{j/N} × I` by `lem:unique-lift`, and the gluing lemma (`prop-1-20`) assembles
them. -/
theorem IsCovering.strip_lift (hp : IsCovering p) {G : I × I → B} (hG : Continuous G) {N : ℕ}
    (hN : 0 < N) (hcol : ∀ j : ℕ, j < N → ∃ U, EvenlyCovered p U ∧ ∀ q : I × I,
      (j : ℝ) / N ≤ q.1 → (q.1 : ℝ) ≤ ((j : ℝ) + 1) / N → G q ∈ U)
    {ℓ : I → E} (hℓ : Continuous ℓ) (hpℓ : ∀ t, p (ℓ t) = G (0, t)) :
    ∃ L : I × I → E, Continuous L ∧ (∀ q, p (L q) = G q) ∧ ∀ t, L (0, t) = ℓ t := by
  -- The claim, by induction on `j ≤ N`: `G` restricted to the first `j` columns,
  -- `[0, j/N] × I`, written `(s, t) ↦ G(clamp(s), t)` with the clamp of `I` onto `[0, j/N]`,
  -- has a lift `L` with `L(0, t) = ℓ(t)`.
  have key : ∀ j : ℕ, j ≤ N → ∃ L : I × I → E, Continuous L ∧
      (∀ q : I × I, p (L q) = G (I.clamp 0 ((j : ℝ) / N) q.1, q.2)) ∧ ∀ t, L (0, t) = ℓ t := by
    intro j
    induction j with
    | zero =>
      -- `j = 0`: the map is `(s, t) ↦ G(0, t)`, and `(s, t) ↦ ℓ(t)` lifts it.
      intro _
      refine ⟨fun q => ℓ q.2, hℓ.comp continuous_snd, fun q => ?_, fun t => rfl⟩
      simp only [Nat.cast_zero, zero_div, I.clamp_zero_zero]
      exact hpℓ q.2
    | succ j ih =>
      -- `j → j + 1`. By induction `L` lifts `G` on `[0, a] × I`, `a = j/N`, and column `j`,
      -- `[a, a'] × I` with `a' = (j + 1)/N`, is carried by `G` into the evenly covered `U`,
      -- with sheets `𝒮`.
      intro hj
      obtain ⟨L, hL, hpL, hL0⟩ := ih (by omega)
      obtain ⟨U, ⟨-, 𝒮, hopen, -, hpre, hhom⟩, hb⟩ := hcol j (by omega)
      obtain ⟨ha0, haa', ha'1⟩ := grid_facts hN hj
      set a : ℝ := (j : ℝ) / N with ha
      set a' : ℝ := ((j : ℝ) + 1) / N with ha'
      have hj' : ((j + 1 : ℕ) : ℝ) / N = a' := by rw [ha']; push_cast; ring
      rw [hj']
      -- `c` is the point `a` of `I`. Both clamps fix it.
      set c : I := I.pt a with hc
      have hcc : (c : ℝ) = a := I.coe_pt ha0 (haa'.trans ha'1)
      have hcl0 : I.clamp 0 a c = c :=
        I.clamp_of_mem le_rfl ha0 (haa'.trans ha'1) (hcc ▸ ha0) hcc.le
      have hcl : I.clamp a a' c = c := I.clamp_of_mem ha0 haa' ha'1 hcc.ge (hcc ▸ haa')
      -- `G` on the column, as the map `(s, t) ↦ G(clamp(s), t)`, lands in `U`.
      have hmem : ∀ q : I × I, G (I.clamp a a' q.1, q.2) ∈ U := fun q =>
        hb _ (I.mem_clamp ha0 haa' ha'1 q.1).1 (I.mem_clamp ha0 haa' ha'1 q.1).2
      -- The sheet `S` over `U` containing `L(a, 0)`, which lies over `G(a, 0) ∈ U`.
      obtain ⟨S, hS, hLS⟩ : L (c, 0) ∈ ⋃₀ 𝒮 := by
        rw [← hpre]
        show p (L (c, 0)) ∈ U
        have := hmem (c, 0)
        rw [hcl] at this
        rwa [hpL, hcl0]
      -- The lift of the column: `P(s, t) = σ(G(s, t))`, `σ` the inverse of `p` on `S`.
      obtain ⟨P, hPc, hPS, hpP⟩ := (hhom S hS).exists_lift (hopen S hS)
        (h := fun q : I × I => G (I.clamp a a' q.1, q.2))
        (hG.comp (((I.continuous_clamp a a').comp continuous_fst).prodMk continuous_snd)) hmem
      -- `P(a, 0) = L(a, 0)`: both lie in `S` over `G(a, 0)`, and `p` is one to one on `S`.
      have hP0 : L (c, 0) = P (c, 0) :=
        (hhom S hS).1 hLS (hPS _) (by rw [hpP, hpL, hcl0, hcl])
      -- The old lift `L` and the new `P` agree along the edge `{a} × I`: `t ↦ L(a, t)` and
      -- `t ↦ P(a, t)` both lift `t ↦ G(a, t)` and agree at `t = 0`; so they are equal by
      -- `lem:unique-lift`, `I` being connected.
      have hagree : ∀ q : I × I, (q.1 : ℝ) = a → L q = P q := by
        rintro ⟨s, t⟩ hs
        have hs' : s = c := Subtype.ext (hs.trans hcc.symm)
        subst hs'
        exact hp.eq_of_lift connected_I (f₁ := fun t => L (c, t)) (f₂ := fun t => P (c, t))
          (hL.comp (continuous_const.prodMk continuous_id))
          (hPc.comp (continuous_const.prodMk continuous_id))
          (fun t => by simp only [hpL, hpP, hcl0, hcl]) (y₀ := 0) hP0 t
      -- Glue: the new lift is `L` where `s ≤ a` and `P` where `s ≥ a`, continuous by the gluing
      -- lemma (`continuous_glue_le`, `prop-1-20`), since `L = P` where `s = a`.
      refine ⟨fun q => if (q.1 : ℝ) ≤ a then L q else P q,
        continuous_glue_le (continuous_subtype_val.comp continuous_fst) a hL hPc hagree,
        fun q => ?_, fun t => ?_⟩
      -- It lifts `G` on `[0, a'] × I`: for `s ≤ a` both clamps fix `s` and `L` lifts `G`
      -- there; for `s > a`, clamping onto `[a, a']` or onto `[0, a']` is the same.
      · by_cases h : (q.1 : ℝ) ≤ a
        · simp only [h, ite_true, hpL]
          rw [I.clamp_of_mem le_rfl ha0 (haa'.trans ha'1) q.1.2.1 h,
            I.clamp_of_mem le_rfl (ha0.trans haa') ha'1 q.1.2.1 (h.trans haa')]
        · simp only [h, ite_false, hpP]
          rw [I.clamp_eq_clamp ha0 haa' ha'1 (le_of_lt (not_le.mp h))]
      -- On the left edge `s = 0 ≤ a` it is `L(0, t) = ℓ(t)`.
      · have h : ((0 : I) : ℝ) ≤ a := by simpa using ha0
        simp only [h, ite_true, hL0]
  -- For `j = N` the clamp is onto `[0, N/N] = I`, the identity: `L` lifts `G`.
  obtain ⟨L, hL, hpL, hL0⟩ := key N le_rfl
  have hNN : (N : ℝ) / N = 1 := div_self (by exact_mod_cast hN.ne')
  refine ⟨L, hL, fun q => ?_, hL0⟩
  rw [hpL, hNN, I.clamp_zero_one]

/-- **`thm:lifting-general`**, path lifting, existence: for a covering `p : E → B`, every path
`f : I → B` has a lift `f̃ : I → E` (continuous, `p f̃ = f`) with `f̃(0) = e`, for any `e` over
`f(0)` (`he : p(e) = f(0)`). As `thm:path-lifting` for `ℝ → S¹`.
Mathlib: `IsCoveringMap.exists_path_lifts`.

The book's proof, that of `thm:path-lifting` with sheets in place of intervals: a grid of mesh
`1/N` below a Lebesgue number (Analysis I), and the lift along `[0, 1/N]`, `[1/N, 2/N]`, … by
the inverses of `p` on sheets (`strip_lift`, for the map `(s, t) ↦ f(s)`). -/
theorem IsCovering.exists_lift_path (hp : IsCovering p) {f : I → B} (hf : Continuous f) (e : E)
    (he : p e = f 0) : ∃ g : I → E, Continuous g ∧ (∀ s, p (g s) = f s) ∧ g 0 = e := by
  -- Step 1. A grid: `f` carries each `[j/N, (j + 1)/N]` into an evenly covered set.
  obtain ⟨N, hN, hgrid⟩ := hp.exists_grid_I hf
  -- Step 2. Lift piece by piece from `e`: apply `strip_lift` to the map `(s, t) ↦ f(s)` of the
  -- square, with the constant `e` as the lift of its left edge.
  obtain ⟨L, hL, hpL, hL0⟩ := hp.strip_lift (G := fun q => f q.1) (hf.comp continuous_fst) hN
    (fun j hj => (hgrid j hj).imp fun U hU => ⟨hU.1, fun q h1 h2 => hU.2 q.1 h1 h2⟩)
    (ℓ := fun _ => e) continuous_const (fun _ => he)
  -- Step 3. `f̃(s) = L(s, 0)` lifts `f`, and `f̃(0) = L(0, 0) = e`.
  exact ⟨fun s => L (s, 0), hL.comp (continuous_id.prodMk continuous_const), fun s => hpL (s, 0),
    hL0 0⟩

/-- **`thm:lifting-general`**, path lifting, uniqueness: two lifts `g₁, g₂ : I → E` of the same
path (`hpg : p g₁ = p g₂`) that agree at `0` are equal: `lem:unique-lift`, `I` being connected
(Analysis I, `connected_I`). Mathlib: `IsCoveringMap.eq_of_comp_eq`. -/
theorem IsCovering.lift_path_unique (hp : IsCovering p) {g₁ g₂ : I → E} (h₁ : Continuous g₁)
    (h₂ : Continuous g₂) (hpg : ∀ s, p (g₁ s) = p (g₂ s)) (h0 : g₁ 0 = g₂ 0) : g₁ = g₂ :=
  funext (hp.eq_of_lift connected_I h₁ h₂ hpg h0)

/-- The Lebesgue number lemma on `I × I` (Analysis I, through `II_toMathlib`): for some `N`, `F`
carries each square `[j/N, (j+1)/N] × [k/N, (k+1)/N]` of the grid into an evenly covered set.
As week 6's `exists_grid_II`, and with the proof of `exists_grid_I` in two coordinates. -/
theorem IsCovering.exists_grid_II (hp : IsCovering p) {F : I × I → B} (hF : Continuous F) :
    ∃ N : ℕ, 0 < N ∧ ∀ j k : ℕ, j < N → k < N → ∃ U, EvenlyCovered p U ∧ ∀ q : I × I,
      (j : ℝ) / N ≤ q.1 → (q.1 : ℝ) ≤ ((j : ℝ) + 1) / N →
      (k : ℝ) / N ≤ q.2 → (q.2 : ℝ) ≤ ((k : ℝ) + 1) / N → F q ∈ U := by
  -- The sets `F⁻¹(U(b))` are open (in Mathlib's terms, through the bridge) and cover `I × I`;
  -- take a Lebesgue number `δ` (Analysis I) and `N` with `1/N < δ`.
  choose U hbU hU using hp.2
  have hopen : ∀ b, _root_.IsOpen (F ⁻¹' U b) := fun b => by
    have := (isOpen_iff_mathlib _).mp (hF _ (hU b).1)
    rwa [II_toMathlib] at this
  obtain ⟨δ, hδ, hball⟩ := lebesgue_number_lemma_of_metric
    (isCompact_univ (X := unitInterval × unitInterval)) (c := fun b => F ⁻¹' U b) hopen
    (fun q _ => mem_iUnion.mpr ⟨F q, hbU (F q)⟩)
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hδ
  refine ⟨n + 1, n.succ_pos, fun j k hj hk => ?_⟩
  obtain ⟨h0, h01, h1⟩ := grid_facts n.succ_pos hj
  obtain ⟨k0, k01, k1⟩ := grid_facts n.succ_pos hk
  -- A point of the square with corner `(j/N, k/N)` is within `1/N` of that corner in each
  -- coordinate.
  obtain ⟨b, hb⟩ := hball (I.pt ((j : ℝ) / (n + 1 : ℕ)), I.pt ((k : ℝ) / (n + 1 : ℕ))) (mem_univ _)
  refine ⟨U b, hU b, fun q hs1 hs2 ht1 ht2 => hb ?_⟩
  have e : ((j : ℝ) + 1) / (n + 1 : ℕ) = (j : ℝ) / (n + 1 : ℕ) + 1 / ((n : ℝ) + 1) := by
    push_cast; ring
  have e' : ((k : ℝ) + 1) / (n + 1 : ℕ) = (k : ℝ) / (n + 1 : ℕ) + 1 / ((n : ℝ) + 1) := by
    push_cast; ring
  rw [Metric.mem_ball, Prod.dist_eq, max_lt_iff, Subtype.dist_eq, Subtype.dist_eq, Real.dist_eq,
    Real.dist_eq, I.coe_pt h0 (h01.trans h1), I.coe_pt k0 (k01.trans k1), abs_lt, abs_lt]
  refine ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩

/-- **`thm:lifting-general`**, homotopy lifting, existence: for a covering `p : E → B`, every
continuous `F : I × I → B` has a lift `F̃ : I × I → E` with `F̃(0, 0) = e`, for any `e` over
`F(0, 0)`. As `thm:homotopy-lifting` for `ℝ → S¹`. Mathlib: `IsCoveringMap.liftHomotopy`.

The book's proof, that of `thm:homotopy-lifting` with sheets in place of intervals: a grid of
squares, each carried by `F` into an evenly covered set (Lebesgue number, Analysis I), lifted
row by row from the bottom, each row square by square from the left (`strip_lift`); a new row
agrees with the rows below along their common edge by `lem:unique-lift`, and the gluing lemma
assembles the rows. One change from week 6, where the left edge of each row was lifted through
the point already lifted (a lift of a path from any `s₀`, which a general covering does not
give by a shift): here the whole left edge `t ↦ F(0, t)` is lifted once, at the start, and each
row starts from its piece of that lift. -/
theorem IsCovering.exists_lift_homotopy (hp : IsCovering p) {F : I × I → B} (hF : Continuous F)
    (e : E) (he : p e = F (0, 0)) :
    ∃ G : I × I → E, Continuous G ∧ (∀ q, p (G q) = F q) ∧ G (0, 0) = e := by
  -- Step 1. A grid: `F` carries each square of side `1/N` into an evenly covered set.
  obtain ⟨N, hN, hgrid⟩ := hp.exists_grid_II hF
  -- Step 2. Lift the left edge `t ↦ F(0, t)` from `e` to `λ` (path lifting).
  obtain ⟨lam, hlam, hplam, hlam0⟩ := hp.exists_lift_path (f := fun t => F (0, t))
    (hF.comp (continuous_const.prodMk continuous_id)) e he
  -- Step 3, the claim, by induction on `k ≤ N`: `F` on the first `k` rows, `I × [0, k/N]`,
  -- written `(s, t) ↦ F(s, clamp(t))` with the clamp of `I` onto `[0, k/N]`, has a lift `L`
  -- whose left edge is that of `λ`: `L(0, t) = λ(clamp(t))`.
  have key : ∀ k : ℕ, k ≤ N → ∃ L : I × I → E, Continuous L ∧
      (∀ q : I × I, p (L q) = F (q.1, I.clamp 0 ((k : ℝ) / N) q.2)) ∧
      ∀ t, L (0, t) = lam (I.clamp 0 ((k : ℝ) / N) t) := by
    intro k
    induction k with
    | zero =>
      -- `k = 0`: the map is `(s, t) ↦ F(s, 0)`. Lift the bottom edge `s ↦ F(s, 0)` from `e`
      -- (path lifting) to `g`; then `(s, t) ↦ g(s)` is the lift, and `g(0) = e = λ(0)`.
      intro _
      obtain ⟨g, hg, hpg, hg0⟩ := hp.exists_lift_path (f := fun s => F (s, 0))
        (hF.comp (continuous_id.prodMk continuous_const)) e he
      refine ⟨fun q => g q.1, hg.comp continuous_fst, fun q => ?_, fun t => ?_⟩
      · simp only [Nat.cast_zero, zero_div, I.clamp_zero_zero]
        exact hpg q.1
      · simp only [Nat.cast_zero, zero_div, I.clamp_zero_zero]
        rw [hg0, hlam0]
    | succ k ih =>
      -- `k → k + 1`. By induction `L` lifts `F` on `I × [0, r]`, `r = k/N`; row `k` is
      -- `I × [r, r']`, `r' = (k + 1)/N`, and `c` is the point `r` of `I`.
      intro hk
      obtain ⟨L, hL, hpL, hL0⟩ := ih (by omega)
      obtain ⟨ha0, haa', ha'1⟩ := grid_facts hN hk
      set r : ℝ := (k : ℝ) / N with hr
      set r' : ℝ := ((k : ℝ) + 1) / N with hr'
      have hk' : ((k + 1 : ℕ) : ℝ) / N = r' := by rw [hr']; push_cast; ring
      rw [hk']
      set c : I := I.pt r with hc
      have hcc : (c : ℝ) = r := I.coe_pt ha0 (haa'.trans ha'1)
      have hcl0 : I.clamp 0 r c = c :=
        I.clamp_of_mem le_rfl ha0 (haa'.trans ha'1) (hcc ▸ ha0) hcc.le
      have hcl : I.clamp r r' c = c := I.clamp_of_mem ha0 haa' ha'1 hcc.ge (hcc ▸ haa')
      -- Row `k`, as the map `G_k(s, t) = F(s, clamp(t))` with the clamp onto `[r, r']`.
      set Gk : I × I → B := fun q => F (q.1, I.clamp r r' q.2) with hGk
      have hGkc : Continuous Gk :=
        hF.comp (continuous_fst.prodMk ((I.continuous_clamp r r').comp continuous_snd))
      -- Its left edge `t ↦ G_k(0, t)` is lifted by `t ↦ λ(clamp(t))`.
      have hℓ : Continuous (fun t => lam (I.clamp r r' t)) := hlam.comp (I.continuous_clamp r r')
      -- Lift the row square by square from the left (`strip_lift`), starting from that lift:
      -- the squares of row `k` are carried into evenly covered sets (Step 1).
      obtain ⟨M, hM, hpM, hM0⟩ := hp.strip_lift hGkc hN (fun j hj =>
        (hgrid j k hj (by omega)).imp fun U hU => ⟨hU.1, fun q h1 h2 => hU.2 _ h1 h2
          (I.mem_clamp ha0 haa' ha'1 q.2).1 (I.mem_clamp ha0 haa' ha'1 q.2).2⟩)
        hℓ (fun t => hplam _)
      -- The old lift `L` and the new `M` agree along the edge `I × {r}`: `s ↦ L(s, r)` and
      -- `s ↦ M(s, r)` both lift `s ↦ F(s, r)` and agree at `s = 0`, both being `λ(r)` there;
      -- so they are equal by `lem:unique-lift`, `I` being connected.
      have hagree : ∀ q : I × I, (q.2 : ℝ) = r → L q = M q := by
        rintro ⟨s, t⟩ ht
        have ht' : t = c := Subtype.ext (ht.trans hcc.symm)
        subst ht'
        exact hp.eq_of_lift connected_I (f₁ := fun s => L (s, c)) (f₂ := fun s => M (s, c))
          (hL.comp (continuous_id.prodMk continuous_const))
          (hM.comp (continuous_id.prodMk continuous_const))
          (fun s => by simp only [hpL, hpM, hGk, hcl0, hcl]) (y₀ := 0)
          (by simp only [hM0, hL0, hcl0, hcl]) s
      -- Glue: `L` where `t ≤ r`, `M` where `t ≥ r` (`continuous_glue_le`, `prop-1-20`). It lifts
      -- `F` on `I × [0, r']`, the clamps agreeing as in `strip_lift`, and so does its left edge.
      refine ⟨fun q => if (q.2 : ℝ) ≤ r then L q else M q,
        continuous_glue_le (continuous_subtype_val.comp continuous_snd) r hL hM hagree,
        fun q => ?_, fun t => ?_⟩
      · by_cases h : (q.2 : ℝ) ≤ r
        · simp only [h, ite_true, hpL]
          rw [I.clamp_of_mem le_rfl ha0 (haa'.trans ha'1) q.2.2.1 h,
            I.clamp_of_mem le_rfl (ha0.trans haa') ha'1 q.2.2.1 (h.trans haa')]
        · simp only [h, ite_false, hpM, hGk]
          rw [I.clamp_eq_clamp ha0 haa' ha'1 (le_of_lt (not_le.mp h))]
      · by_cases h : (t : ℝ) ≤ r
        · simp only [h, ite_true, hL0]
          rw [I.clamp_of_mem le_rfl ha0 (haa'.trans ha'1) t.2.1 h,
            I.clamp_of_mem le_rfl (ha0.trans haa') ha'1 t.2.1 (h.trans haa')]
        · simp only [h, ite_false, hM0]
          rw [I.clamp_eq_clamp ha0 haa' ha'1 (le_of_lt (not_le.mp h))]
  -- Step 4. For `k = N` the clamp is the identity of `I`: `L` lifts `F`, and
  -- `L(0, 0) = λ(0) = e`.
  obtain ⟨L, hL, hpL, hL0⟩ := key N le_rfl
  have hNN : (N : ℝ) / N = 1 := div_self (by exact_mod_cast hN.ne')
  refine ⟨L, hL, fun q => ?_, ?_⟩
  · rw [hpL, hNN, I.clamp_zero_one]
  · rw [hL0, hNN, I.clamp_zero_one, hlam0]

/-- **`thm:lifting-general`**, homotopy lifting, uniqueness: two lifts of the same map
`I × I → B` that agree at one point are equal: `lem:unique-lift`, `I × I` being connected
(Analysis I, `preconnected_II`). -/
theorem IsCovering.lift_homotopy_unique (hp : IsCovering p) {G₁ G₂ : I × I → E}
    (h₁ : Continuous G₁) (h₂ : Continuous G₂) (hpG : ∀ q, p (G₁ q) = p (G₂ q)) {q₀ : I × I}
    (h0 : G₁ q₀ = G₂ q₀) : G₁ = G₂ :=
  funext (hp.eq_of_lift (connected_iff_preconnectedSpace.mpr preconnected_II) h₁ h₂ hpG h0)

/-- `thm:lifting-general`, the last part of `thm:homotopy-lifting`: if `F(s, t)` does not depend
on `t` for one `s` (`hs`), then neither does its lift `G`: `G(s, t) = G(s, 0)`. The proof:
`t ↦ G(s, t)` lifts a constant path, so it is constant (`lem:unique-lift`). Applied at `s = 0`
and `s = 1`, the lift of a path homotopy is a path homotopy. Mathlib:
`IsCoveringMap.liftHomotopyRel`. -/
theorem IsCovering.lift_edge_const (hp : IsCovering p) {F : I × I → B} {G : I × I → E}
    (hG : Continuous G) (hpG : ∀ q, p (G q) = F q) (s : I) (hs : ∀ t, F (s, t) = F (s, 0))
    (t : I) : G (s, t) = G (s, 0) :=
  hp.const_of_lift connected_I (f := fun t => G (s, t))
    (hG.comp (continuous_const.prodMk continuous_id)) (y₀ := 0)
    (fun t => by simp only [hpG, hs]) t

/-- **`cor:nonclosed-lift`**: if a loop `f` at `x` has a lift `g` (continuous, `p g = f`) that is
not a loop, `g(1) ≠ g(0)`, then `[f] ≠ 1` in `π₁(B, x)`. Mathlib:
`IsCoveringMap.liftPath_apply_one_eq_of_homotopicRel`, `IsCoveringMap.monodromy`.

The book's proof: a path homotopy from `f` to the constant loop lifts to a path homotopy with
fixed ends, from the lift of `f` to the lift of the constant loop, which is constant. -/
theorem IsCovering.mk_ne_one_of_lift (hp : IsCovering p) {x : B} (f : Path x x) {g : I → E}
    (hg : Continuous g) (hpg : ∀ s, p (g s) = f s) (hne : g 1 ≠ g 0) : (⟦f⟧ : pi1 x) ≠ 1 := by
  -- Suppose `[f] = 1`: there is a path homotopy `H` from `f` to the constant loop `c_x`
  -- (`Quotient.exact`: equal classes come from related loops).
  intro h
  obtain ⟨H⟩ : f.Homotopic (Path.refl x) := Quotient.exact h
  -- Step 1. Lift `H` to `G` with `G(0, 0) = g(0)`, which lies over `f(0) = H(0, 0)`
  -- (`thm:lifting-general`).
  obtain ⟨G, hG, hpG, hG0⟩ := hp.exists_lift_homotopy H.continuous_toFun (g 0)
    (by rw [hpg, H.zero'])
  -- Step 2. The bottom edge of `G` lifts `f` from `g(0)`, so it is `g` (uniqueness).
  have hbot : ∀ s, G (s, 0) = g s := hp.eq_of_lift connected_I (f₁ := fun s => G (s, 0))
    (hG.comp (continuous_id.prodMk continuous_const)) hg (fun s => by rw [hpG, H.zero', hpg])
    (y₀ := 0) hG0
  -- Step 3. The other three edges of `H` stay at `x`, so their lifts are constant: the left
  -- and right edges by `lift_edge_const`, the top edge in the same way.
  have hleft : ∀ t, G (0, t) = G (0, 0) := hp.lift_edge_const hG hpG 0
    (fun t => by rw [H.source', H.source'])
  have hright : ∀ t, G (1, t) = G (1, 0) := hp.lift_edge_const hG hpG 1
    (fun t => by rw [H.target', H.target'])
  have htop : ∀ s, G (s, 1) = G (0, 1) := hp.const_of_lift connected_I
    (f := fun s => G (s, 1)) (hG.comp (continuous_id.prodMk continuous_const))
    (fun s => by rw [hpG, hpG, H.one', H.one']; rfl)
  -- Step 4. Going round the boundary of the square: `g(1) = G(1, 0) = G(1, 1) = G(0, 1) =
  -- G(0, 0) = g(0)`, against the hypothesis.
  apply hne
  calc g 1 = G (1, 0) := (hbot 1).symm
    _ = G (1, 1) := (hright 1).symm
    _ = G (0, 1) := htop 1
    _ = G (0, 0) := hleft 1
    _ = g 0 := hbot 0

end Lifting

/-! ## Locally trivial fibrations (`def:fibration`, `lem:pullback-fibration`,
`lem:covering-interval`, `def:universal-cover`) -/

section Fibration
variable [TopSpace E] [TopSpace B] {B' : Type*} [TopSpace B'] {F : Type*} [TopSpace F]

/-- **`def:fibration`**: a continuous `p : E → B` is a locally trivial fibration with fibre `F`
if every point of `B` has an open neighbourhood `U` with a homeomorphism `φ : p⁻¹(U) → U × F`
over `U`, that is, with `pr_U ∘ φ = p` on `p⁻¹(U)`. Mathlib: `Trivialization`,
`FiberBundle`.

Lean: `φ.toFun` is the map of the homeomorphism `φ` (`Homeomorph`, week 1), `φ.invFun` its
inverse; `(φ.toFun e).1` is the first coordinate, a point of `U`, and `((φ.toFun e).1 : B)` the
same point seen in `B`. -/
def IsLocallyTrivial (p : E → B) (F : Type*) [TopSpace F] : Prop :=
  Continuous p ∧ ∀ b : B, ∃ U : Set B, IsOpen U ∧ b ∈ U ∧
    ∃ φ : Homeomorph (p ⁻¹' U) (U × F), ∀ e, ((φ.toFun e).1 : B) = p e

/-- **`lem:pullback-fibration`** (1): the pullback of a locally trivial fibration with fibre `F`
along any continuous `g : B' → B` is a locally trivial fibration with fibre `F`. The pullback
is `p' : B' ×_B E → B'`, `p'(b', e) = b'` (`prop:pullback-top`, `Week02Glue.lean`'s
`fibreProduct g p`). Mathlib: `Trivialization.pullback`.

The book's proof: over `U' = g⁻¹(U)` the map `ψ(b', e) = (b', pr_F φ(e))` is a homeomorphism
`p'⁻¹(U') → U' × F` over `U'`, with inverse `χ(b', x) = (b', φ⁻¹(g(b'), x))`. -/
theorem IsLocallyTrivial.pullback {p : E → B} (hp : IsLocallyTrivial p F) {g : B' → B}
    (hg : Continuous g) : IsLocallyTrivial (fibreProduct.fst : fibreProduct g p → B') F := by
  refine ⟨continuous_fibreProduct_fst, fun b' => ?_⟩
  -- Take `U ∋ g(b')` and `φ : p⁻¹(U) → U × F` over `U`; then `U' = g⁻¹(U)` is open.
  obtain ⟨U, hU, hbU, φ, hφ⟩ := hp.2 (g b')
  refine ⟨g ⁻¹' U, hg U hU, hbU, ?_⟩
  -- A point `z` of `p'⁻¹(U')` is a pair `(b', e)` (Lean: `z.1.1.1` and `z.1.1.2`) with
  -- `g(b') = p(e)` (`z.1.2`) and `g(b') ∈ U` (`z.2`); so `e ∈ p⁻¹(U)`.
  have hmem : ∀ z : (fibreProduct.fst : fibreProduct g p → B') ⁻¹' (g ⁻¹' U),
      p z.1.1.2 ∈ U := fun z => by
    rw [← z.1.2]
    exact z.2
  -- For `w = φ⁻¹(g(b'), x)`: `p(w) = g(b')`, as `φ` is over `U`.
  have hinv : ∀ q : (g ⁻¹' U) × F,
      p (φ.invFun (⟨g q.1.1, q.1.2⟩, q.2)).1 = g q.1.1 := fun q => by
    rw [← hφ, φ.right_inv]
  refine ⟨{
    toFun := fun z => (⟨z.1.1.1, z.2⟩, (φ.toFun ⟨z.1.1.2, hmem z⟩).2)
    invFun := fun q => ⟨⟨(q.1.1, (φ.invFun (⟨g q.1.1, q.1.2⟩, q.2)).1), (hinv q).symm⟩, q.1.2⟩
    left_inv := fun z => ?_
    right_inv := fun q => ?_
    continuous_toFun := ?_
    continuous_invFun := ?_ }, fun z => rfl⟩
  -- `χ(ψ(b', e)) = (b', e)`: `(g(b'), pr_F φ(e)) = φ(e)`, because `φ` is over `U` and
  -- `g(b') = p(e)`; and `φ⁻¹(φ(e)) = e`.
  · have hw : ((⟨g z.1.1.1, z.2⟩ : U), (φ.toFun ⟨z.1.1.2, hmem z⟩).2) =
        φ.toFun ⟨z.1.1.2, hmem z⟩ :=
      Prod.ext (Subtype.ext (z.1.2.trans (hφ ⟨z.1.1.2, hmem z⟩).symm)) rfl
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · rfl
    show (φ.invFun ((⟨g z.1.1.1, z.2⟩ : U), (φ.toFun ⟨z.1.1.2, hmem z⟩).2)).1 = z.1.1.2
    rw [hw, φ.left_inv]
  -- `ψ(χ(b', x)) = (b', x)`: `pr_F φ(φ⁻¹(g(b'), x)) = x`.
  · apply Prod.ext
    · rfl
    show (φ.toFun (φ.invFun (⟨g q.1.1, q.1.2⟩, q.2))).2 = q.2
    rw [φ.right_inv]
  -- `ψ` is continuous: its coordinates are composites of continuous maps (`thm:product-top`,
  -- `prop-1-15`).
  · refine Continuous.prodMk (continuous_subtype_mk'
      (g := fun z : (fibreProduct.fst : fibreProduct g p → B') ⁻¹' (g ⁻¹' U) => z.1.1.1)
      (continuous_fst.comp (continuous_subtype_val.comp continuous_subtype_val)) _) ?_
    exact continuous_snd.comp (φ.continuous_toFun.comp (continuous_subtype_mk'
      (g := fun z : (fibreProduct.fst : fibreProduct g p → B') ⁻¹' (g ⁻¹' U) => z.1.1.2)
      (continuous_snd.comp (continuous_subtype_val.comp continuous_subtype_val)) _))
  -- `χ` is continuous, for the same reasons.
  · have hb : Continuous (fun q : (g ⁻¹' U) × F => (q.1 : B')) :=
      continuous_subtype_val.comp continuous_fst
    have hw : Continuous (fun q : (g ⁻¹' U) × F => φ.invFun (⟨g q.1.1, q.1.2⟩, q.2)) :=
      φ.continuous_invFun.comp ((continuous_subtype_mk' (g := fun q : (g ⁻¹' U) × F => g q.1.1)
        (hg.comp hb) _).prodMk continuous_snd)
    exact continuous_subtype_mk' (continuous_subtype_mk' (hb.prodMk
      (continuous_subtype_val.comp hw)) _) _

/-- **`lem:pullback-fibration`** (2): the pullback `p' : B' ×_B E → B'` of a covering `p` along
any continuous `g : B' → B` is a covering. Mathlib: `IsCoveringMap.pullback`.

The book's proof: over `U' = g⁻¹(U)`, `U` evenly covered, the homeomorphism of (1) carries the
sheets over `U` to sheets over `U'`. In Lean, with the sheets themselves: the sheet over `U'`
coming from a sheet `S` over `U` is `S' = {(b', e) | e ∈ S}`, which `p'` maps homeomorphically
onto `U'`, with inverse `χ(b') = (b', σ(g(b')))`, `σ` the inverse of `p` on `S`. -/
theorem IsCovering.pullback {p : E → B} (hp : IsCovering p) {g : B' → B} (hg : Continuous g) :
    IsCovering (fibreProduct.fst : fibreProduct g p → B') := by
  refine ⟨continuous_fibreProduct_fst, fun b' => ?_⟩
  -- Take an evenly covered `U ∋ g(b')`, with sheets `𝒮`; then `U' = g⁻¹(U)` is open.
  obtain ⟨U, hbU, hUo, 𝒮, hopen, hdisj, hpre, hhom⟩ := hp.2 (g b')
  -- The sheet `T(S) = {(b', e) | e ∈ S}`, the preimage of `S` under `(b', e) ↦ e`. A point
  -- `z` of the pullback is a pair `(b', e)` (Lean: `z.1.1`, `z.1.2`) with `g(b') = p(e)`
  -- (`z.2`).
  let T : Set E → Set (fibreProduct g p) := fun S => {z | z.1.2 ∈ S}
  have hTo : ∀ S ∈ 𝒮, IsOpen (T S) := fun S hS => continuous_fibreProduct_snd S (hopen S hS)
  refine ⟨g ⁻¹' U, hbU, hg U hUo, T '' 𝒮, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨S, hS, rfl⟩
    exact hTo S hS
  -- Different sheets come from different `S`, which are disjoint; so are the `T(S)`.
  · rintro _ ⟨S, hS, rfl⟩ _ ⟨S', hS', rfl⟩ hne
    have hd := hdisj S hS S' hS' (fun h => hne (h ▸ rfl))
    exact Set.disjoint_left.mpr fun z hz hz' => Set.disjoint_left.mp hd hz hz'
  -- `p'⁻¹(U')` is the union of the `T(S)`: `g(b') ∈ U` iff `p(e) ∈ U` iff `e` lies in a sheet.
  · ext z
    constructor
    · intro hz
      have : z.1.2 ∈ p ⁻¹' U := by
        show p z.1.2 ∈ U
        rw [← z.2]
        exact hz
      rw [hpre] at this
      obtain ⟨S, hS, hzS⟩ := this
      exact ⟨T S, ⟨S, hS, rfl⟩, hzS⟩
    · rintro ⟨_, ⟨S, hS, rfl⟩, hzS⟩
      have : z.1.2 ∈ p ⁻¹' U := hpre ▸ ⟨S, hS, hzS⟩
      show g z.1.1 ∈ U
      rw [z.2]
      exact this
  -- Each `T(S)` is mapped homeomorphically onto `U'` by `p'`.
  · rintro _ ⟨S, hS, rfl⟩
    obtain ⟨hinj, him, -⟩ := hhom S hS
    -- The inverse `σ` of `p` on `S`, applied to `g(b')` for `b' ∈ U'`.
    obtain ⟨σ, hσc, hσS, hσp⟩ := (hhom S hS).exists_lift (hopen S hS)
      (h := fun u : g ⁻¹' U => g u) (hg.comp continuous_subtype_val) (fun u => u.2)
    -- `χ(b') = (b', σ(g(b')))`, a continuous map `U' → B' ×_B E` into `T(S)`.
    let χ : g ⁻¹' U → fibreProduct g p := fun u => ⟨(u.1, σ u), (hσp u).symm⟩
    have hχ : Continuous χ :=
      continuous_subtype_mk' (continuous_subtype_val.prodMk hσc) _
    refine ⟨?_, ?_, fun W hWU => ⟨fun hW => (hTo S hS).inter
      (continuous_fibreProduct_fst W hW), fun hW => ?_⟩⟩
    -- One to one: two points `(b', e)`, `(b', e')` of `T(S)` have `p(e) = g(b') = p(e')`,
    -- so `e = e'`.
    · intro z hz z' hz' h
      have h' : z.1.1 = z'.1.1 := h
      have he : z.1.2 = z'.1.2 := hinj hz hz' (by rw [← z.2, ← z'.2, h'])
      exact Subtype.ext (Prod.ext h' he)
    -- Onto `U'`: `g(p'(z)) = p(e) ∈ p(S) = U`; and `b' ∈ U'` is `p'(χ(b'))`.
    · ext u
      constructor
      · rintro ⟨z, hz, rfl⟩
        show g z.1.1 ∈ U
        rw [z.2, ← him]
        exact ⟨z.1.2, hz, rfl⟩
      · intro hu
        exact ⟨χ ⟨u, hu⟩, hσS _, rfl⟩
    -- If `T(S) ∩ p'⁻¹(W)` is open, so is `W`: it is the image in `B'` of
    -- `χ⁻¹(T(S) ∩ p'⁻¹(W))`, open in the open `U'`.
    · have : W = Subtype.val '' (χ ⁻¹' (T S ∩ fibreProduct.fst ⁻¹' W)) := by
        ext u
        constructor
        · intro hu
          exact ⟨⟨u, hWU hu⟩, ⟨hσS _, hu⟩, rfl⟩
        · rintro ⟨u', ⟨-, hu'⟩, rfl⟩
          exact hu'
      rw [this]
      exact (hg U hUo).image_val (hχ _ hW)

omit [TopSpace B] in
/-- **`lem:pullback-fibration`** (3): the fibre of the pullback `p'` over `b'` is homeomorphic
to the fibre of `p` over `g(b')`, by `(b', e) ↦ e`. Mathlib: none (`Function.Pullback`).

The book's proof, directly: `(b', e) ↦ e` is continuous with inverse `e ↦ (b', e)` on the fibre
`p⁻¹(g(b'))`, both coordinates of which are continuous (`thm:product-top`, `prop-1-15`). (Lean:
a point `z` of the fibre of `p'` is a point `z.1 = ((b'', e), _)` of the pullback with
`b'' = b'`, which is `z.2`.) -/
theorem pullback_fibre {p : E → B} {g : B' → B} (b' : B') :
    ∃ φ : Homeomorph ((fibreProduct.fst : fibreProduct g p → B') ⁻¹' {b'}) (p ⁻¹' {g b'}),
      ∀ z, (φ.toFun z : E) = z.1.1.2 := by
  -- `(b', e) ↦ e` lands in `p⁻¹(g(b'))`: `p(e) = g(b'')` and `b'' = b'`.
  have hmem : ∀ z : (fibreProduct.fst : fibreProduct g p → B') ⁻¹' {b'},
      p z.1.1.2 = g b' := fun z => by
    have h : z.1.1.1 = b' := z.2
    rw [← z.1.2, h]
  refine ⟨{
    toFun := fun z => ⟨z.1.1.2, hmem z⟩
    invFun := fun e => ⟨⟨(b', e.1), e.2.symm⟩, rfl⟩
    left_inv := fun z => ?_
    right_inv := fun e => rfl
    continuous_toFun := continuous_subtype_mk' (g := fun z :
        (fibreProduct.fst : fibreProduct g p → B') ⁻¹' {b'} => z.1.1.2)
      (continuous_snd.comp (continuous_subtype_val.comp continuous_subtype_val)) _
    continuous_invFun := continuous_subtype_mk' (continuous_subtype_mk'
      (continuous_const.prodMk continuous_subtype_val) _) _ }, fun z => rfl⟩
  -- `e ↦ (b', e)` undoes it, as `b'' = b'`.
  have h : z.1.1.1 = b' := z.2
  exact Subtype.ext (Subtype.ext (Prod.ext h.symm rfl))

/-- **`lem:covering-interval`** (1): the sections of the trivial fibration `B × F → B` are the
maps `b ↦ (b, σ(b))` with `σ : B → F` continuous; if `F` is discrete (`hF`: every subset is open)
and `B` is connected, `σ` is constant. Here: a continuous section `s` (`hsec`: `pr_B ∘ s = id`)
has `s(b') = (b', σ(b))` for all `b, b'`. Mathlib: `IsPreconnected.constant`.

The book's proof: `σ = pr_F ∘ s` is continuous (`thm:product-top`); the image of a connected
space is connected, and the only non-empty connected subsets of a discrete space are points. In
Lean, directly: `σ⁻¹(σ(b))` and its complement are open, so the first is all of `B`. -/
theorem section_eq_const (hF : ∀ A : Set F, IsOpen A) (hB : Connected B) {s : B → B × F}
    (hs : Continuous s) (hsec : ∀ b, (s b).1 = b) (b b' : B) : s b' = (b', (s b).2) := by
  have hσ : Continuous (fun b => (s b).2) := continuous_snd.comp hs
  -- The set `C = {b'' | σ(b'') = σ(b)}` and its complement are preimages of subsets of the
  -- discrete `F`, so both are open; `b ∈ C`, so the complement is empty.
  rcases hB {b'' | (s b'').2 = (s b).2} {b'' | (s b'').2 = (s b).2}ᶜ
    (hσ _ (hF {(s b).2})) (hσ _ (hF {(s b).2}ᶜ)) (union_compl_self _) disjoint_compl_right
    with h | h
  · exact absurd (h ▸ (rfl : (s b).2 = (s b).2)) (notMem_empty b)
  · have hb' : (s b').2 = (s b).2 := by
      by_contra hne
      exact notMem_empty b' (h ▸ hne)
    exact Prod.ext (hsec b') hb'

/-- A map `P : X × F → Z`, `F` discrete (`hF`), is continuous if each `x ↦ P(x, a)` is: the
preimage of an open `V` contains, about each of its points `(x, a)`, the open rectangle
`{x' | P(x', a) ∈ V} × {a}` (`isOpen_prod_iff`). Mathlib: `continuous_prod_of_discrete_right`. -/
theorem continuous_of_discrete_right {X Z : Type*} [TopSpace X] [TopSpace Z]
    (hF : ∀ A : Set F, IsOpen A) {P : X × F → Z} (h : ∀ a, Continuous (fun x => P (x, a))) :
    Continuous P := by
  intro V hV
  rw [isOpen_prod_iff]
  rintro ⟨x, a⟩ hz
  refine ⟨(fun x => P (x, a)) ⁻¹' V, {a}, h a V hV, hF {a}, ⟨hz, rfl⟩, fun q hq => ?_⟩
  obtain ⟨hq1, hq2⟩ := hq
  have : q = (q.1, a) := Prod.ext rfl hq2
  rw [this]
  exact hq1

/-- A locally constant map is continuous, whatever the topology of its target: the preimage of
any set is the union of open sets on which the map is constant. -/
theorem continuous_of_locallyConst {Φ : E → F}
    (h : ∀ e, ∃ V : Set E, IsOpen V ∧ e ∈ V ∧ ∀ e' ∈ V, Φ e' = Φ e) : Continuous Φ :=
  fun A _ => isOpen_of_forall_nhd fun e he => by
    obtain ⟨V, hV, heV, hc⟩ := h e
    exact ⟨V, hV, heV, fun e' he' => show Φ e' ∈ A by rw [hc e' he']; exact he⟩

/-- The sets `{t ∈ I | t < r}` and `{t ∈ I | t > r}` are open in `I` (Analysis I). -/
theorem isOpen_I_lt (r : ℝ) : IsOpen {t : I | (t : ℝ) < r} :=
  (isOpen_I_iff _).mpr (isOpen_lt _root_.continuous_subtype_val _root_.continuous_const)

/-- See `isOpen_I_lt`. -/
theorem isOpen_I_gt (r : ℝ) : IsOpen {t : I | r < (t : ℝ)} :=
  (isOpen_I_iff _).mpr (isOpen_lt _root_.continuous_const _root_.continuous_subtype_val)

/-- A covering `p : E → I` has a point over `0` above each point of `E`: lift the path from
`p(e)` to `0`, `t ↦ (1 - t) p(e)`, from `e` (`thm:lifting-general`). -/
theorem IsCovering.nonempty_fibre_zero {p : E → I} (hp : IsCovering p) (e : E) :
    Nonempty (p ⁻¹' ({0} : Set I)) := by
  have hf : Continuous (fun t : I => I.pt ((p e : ℝ) * (1 - t))) :=
    continuous_of_mathlib_eq I_toMathlib I_toMathlib (continuous_projIcc.comp (by fun_prop))
  obtain ⟨g, -, hpg, -⟩ := hp.exists_lift_path hf e
    (Subtype.ext (by rw [I.coe_pt (by simp [(p e).2.1]) (by simp [(p e).2.2])]; simp))
  refine ⟨⟨g 1, ?_⟩⟩
  show p (g 1) = 0
  rw [hpg]
  exact Subtype.ext (by rw [I.coe_pt (by simp) (by simp)]; simp)

/-- **`lem:covering-interval`** (2): every covering `p : E → [0, 1]` is trivial: there is a
homeomorphism `φ : E → [0, 1] × F` over `[0, 1]` (`(φ e)₁ = p(e)`), `F = p⁻¹(0)` (discrete,
`def:covering-map`). Mathlib: none (`IsCoveringMap`, `Trivialization`).

The book's proof: a grid `0 < 1/N < … < 1` with each `[j/N, (j+1)/N]` inside an evenly covered
`U` (Lebesgue number), and a trivialisation over `[0, j/N]` extended step by step across the
next interval through the sheets over `U`, the two pieces pasted by the gluing lemma. In Lean the
trivialisation over `[0, r]`, `r = j/N`, is a pair of maps: `Ψ : I × F → E`, continuous, with
`p(Ψ(t, a)) = clamp(t)` (the clamp of `I` onto `[0, r]`, as in `strip_lift`), and `Φ : E → F`,
locally constant on `p⁻¹[0, r]` (that is, continuous there, `F` being discrete), inverse to
each other over `[0, r]`: `Φ(Ψ(t, a)) = a`, `Ψ(p(e), Φ(e)) = e`. Over the next interval,
`Ψ(t, a)` is the point over `t` of the sheet containing `Ψ(r, a)` (the book's
`(id × αβ⁻¹) ∘ ψ_j`, inverted), and `Φ(e)` is `Φ` of the point over `r` of the sheet containing
`e`. -/
theorem IsCovering.trivial_over_I {p : E → I} (hp : IsCovering p) :
    ∃ φ : Homeomorph E (I × (p ⁻¹' ({0} : Set I))), ∀ e, (φ.toFun e).1 = p e := by
  classical
  -- `F = p⁻¹(0)` is discrete (`def:covering-map`), and not empty if `E` is not.
  have hdisc : ∀ A : Set (p ⁻¹' ({0} : Set I)), IsOpen A := hp.discrete_fibre 0
  have hne := hp.nonempty_fibre_zero
  -- Step 1. A grid: each `[j/N, (j + 1)/N]` lies in an evenly covered set (Lebesgue number).
  obtain ⟨N, hN, hgrid⟩ := hp.exists_grid_I (f := id) continuous_id
  -- Step 2, the claim, by induction on `j ≤ N`: `p` is trivial over `[0, j/N]`, as above.
  have key : ∀ j : ℕ, j ≤ N → ∃ Ψ : I × (p ⁻¹' ({0} : Set I)) → E,
      ∃ Φ : E → p ⁻¹' ({0} : Set I), Continuous Ψ ∧
      (∀ q, p (Ψ q) = I.clamp 0 ((j : ℝ) / N) q.1) ∧
      (∀ e, (p e : ℝ) ≤ (j : ℝ) / N → ∃ V : Set E, IsOpen V ∧ e ∈ V ∧
        ∀ e' ∈ V, (p e' : ℝ) ≤ (j : ℝ) / N → Φ e' = Φ e) ∧
      (∀ q : I × (p ⁻¹' ({0} : Set I)), (q.1 : ℝ) ≤ (j : ℝ) / N → Φ (Ψ q) = q.2) ∧
      (∀ e, (p e : ℝ) ≤ (j : ℝ) / N → Ψ (p e, Φ e) = e) := by
    intro j
    induction j with
    | zero =>
      -- `j = 0`: over `[0, 0] = {0}`, `Ψ(t, a) = a` and `Φ(e) = e` on `F`. (Off `F`, `Φ` takes
      -- any value: it is not used there.)
      intro _
      simp only [Nat.cast_zero, zero_div]
      have h0 : ∀ e, (p e : ℝ) ≤ 0 → p e = 0 := fun e h => Subtype.ext (le_antisymm h (p e).2.1)
      refine ⟨fun q => q.2.1, fun e => if h : p e = 0 then ⟨e, h⟩ else Classical.choice (hne e),
        continuous_subtype_val.comp continuous_snd, fun q => ?_, fun e he => ?_, fun q _ => ?_,
        fun e he => ?_⟩
      · rw [I.clamp_zero_zero]
        exact q.2.2
      -- `Φ` is locally constant on `F`: a sheet about `e` meets `F` only at `e`.
      · obtain ⟨S, hSo, heS, hinj⟩ := hp.exists_sheet e
        refine ⟨S, hSo, heS, fun e' he' hpe' => ?_⟩
        rw [hinj he' heS (by rw [h0 e' hpe', h0 e he])]
      · have h : p q.2.1 = 0 := q.2.2
        simp only [h, dite_true]
      · have h := h0 e he
        simp only [h, dite_true]
    | succ j ih =>
      -- `j → j + 1`. By induction `p` is trivial over `[0, a]`, `a = j/N`, by `Ψ`, `Φ`; and
      -- `[a, a']`, `a' = (j + 1)/N`, lies in the evenly covered `U`, with sheets `𝒮`.
      intro hj
      obtain ⟨Ψ, Φ, hΨc, hpΨ, hΦloc, hΦΨ, hΨΦ⟩ := ih (by omega)
      obtain ⟨U, ⟨-, 𝒮, hopen, hdisj, hpre, hhom⟩, hb⟩ := hgrid j (by omega)
      obtain ⟨ha0, haa', ha'1⟩ := grid_facts hN hj
      set a : ℝ := (j : ℝ) / N with ha
      set a' : ℝ := ((j : ℝ) + 1) / N with ha'
      have hj' : ((j + 1 : ℕ) : ℝ) / N = a' := by rw [ha']; push_cast; ring
      rw [hj']
      -- `c` is the point `a` of `I`. Both clamps fix it.
      set c : I := I.pt a with hc
      have hcc : (c : ℝ) = a := I.coe_pt ha0 (haa'.trans ha'1)
      have hcl0 : I.clamp 0 a c = c :=
        I.clamp_of_mem le_rfl ha0 (haa'.trans ha'1) (hcc ▸ ha0) hcc.le
      have hcl : I.clamp a a' c = c := I.clamp_of_mem ha0 haa' ha'1 hcc.ge (hcc ▸ haa')
      have hcU : c ∈ U := hb c hcc.ge (hcc ▸ haa')
      have hclU : ∀ t, I.clamp a a' t ∈ U := fun t =>
        hb _ (I.mem_clamp ha0 haa' ha'1 t).1 (I.mem_clamp ha0 haa' ha'1 t).2
      -- A point over `U` lies in a sheet; two sheets with a common point are the same.
      have hsheet : ∀ e, p e ∈ U → ∃ S ∈ 𝒮, e ∈ S := fun e he => by
        have : e ∈ p ⁻¹' U := he
        rw [hpre] at this
        exact this
      have hsame : ∀ S ∈ 𝒮, ∀ S' ∈ 𝒮, ∀ x, x ∈ S → x ∈ S' → S = S' :=
        fun S hS S' hS' x hx hx' => by
          by_contra hne
          exact Set.disjoint_left.mp (hdisj S hS S' hS' hne) hx hx'
      -- For `x ∈ F`: the sheet `S(x)` containing `Ψ(a, x)`, which lies over `a`, and the inverse
      -- `σ_x` of `p` on it, along `[a, a']`: `σ_x(t) ∈ S(x)` lies over `clamp(t)`.
      have hΨa : ∀ x, p (Ψ (c, x)) = c := fun x => by rw [hpΨ, hcl0]
      choose Sa hSa hΨSa using fun x => hsheet (Ψ (c, x)) (by rw [hΨa x]; exact hcU)
      choose σ hσc hσS hσp using fun x =>
        (hhom (Sa x) (hSa x)).exists_lift (hopen _ (hSa x)) (I.continuous_clamp a a') hclU
      -- `ρ(e)`: the point over `a` of the sheet containing `e` (any point, if there is none).
      have hρex : ∀ e, ∃ y, ∀ S ∈ 𝒮, e ∈ S → y ∈ S ∧ p y = c := fun e => by
        by_cases h : ∃ S ∈ 𝒮, e ∈ S
        · obtain ⟨S, hS, heS⟩ := h
          have : c ∈ p '' S := (hhom S hS).2.1.symm ▸ hcU
          obtain ⟨y, hyS, hpy⟩ := this
          refine ⟨y, fun S' hS' heS' => ?_⟩
          rw [← hsame S hS S' hS' e heS heS']
          exact ⟨hyS, hpy⟩
        · exact ⟨e, fun S hS heS => absurd ⟨S, hS, heS⟩ h⟩
      choose ρ hρ using hρex
      -- Two points of a sheet `S` over `a` are equal (`p` is one to one on `S`).
      have hover : ∀ S ∈ 𝒮, ∀ y y', y ∈ S → y' ∈ S → p y = c → p y' = c → y = y' :=
        fun S hS y y' hy hy' hpy hpy' => (hhom S hS).1 hy hy' (hpy.trans hpy'.symm)
      -- `σ_x(a) = Ψ(a, x)`: both are points of `S(x)` over `a`.
      have hσa : ∀ x, σ x c = Ψ (c, x) := fun x =>
        hover _ (hSa x) _ _ (hσS x c) (hΨSa x) (by rw [hσp, hcl]) (hΨa x)
      -- `Φ(ρ(y)) = x` for `y ∈ S(x)`: `ρ(y)` is the point of `S(x)` over `a`, `Ψ(a, x)`.
      have hΦρ : ∀ x y, y ∈ Sa x → Φ (ρ y) = x := fun x y hy => by
        have := hover _ (hSa x) _ _ ((hρ y _ (hSa x) hy).1) (hΨSa x) (hρ y _ (hSa x) hy).2 (hΨa x)
        rw [this, hΦΨ (c, x) hcc.le]
      -- The new pair: `Ψ` over `[0, a]` and `σ` over `[a, a']`; `Φ` over `[0, a]` and `Φ ∘ ρ`
      -- over `[a, a']`.
      refine ⟨fun q => if (q.1 : ℝ) ≤ a then Ψ q else σ q.2 q.1,
        fun e => if (p e : ℝ) ≤ a then Φ e else Φ (ρ e), ?_, fun q => ?_, fun e he => ?_,
        fun q hq => ?_, fun e he => ?_⟩
      -- The new `Ψ` is continuous by the gluing lemma (`prop-1-20`), as the two pieces agree at
      -- `t = a` (`hσa`); the piece `(t, x) ↦ σ_x(t)` is continuous, `F` being discrete.
      · refine continuous_glue_le (continuous_subtype_val.comp continuous_fst) a hΨc
          (continuous_of_discrete_right hdisc (P := fun q => σ q.2 q.1) hσc) ?_
        rintro ⟨t, x⟩ ht
        have ht' : t = c := Subtype.ext (ht.trans hcc.symm)
        subst ht'
        exact (hσa x).symm
      -- It lies over `clamp(t)`, the clamps agreeing as in `strip_lift`.
      · by_cases h : (q.1 : ℝ) ≤ a
        · simp only [h, ite_true, hpΨ]
          rw [I.clamp_of_mem le_rfl ha0 (haa'.trans ha'1) q.1.2.1 h,
            I.clamp_of_mem le_rfl (ha0.trans haa') ha'1 q.1.2.1 (h.trans haa')]
        · simp only [h, ite_false, hσp]
          rw [I.clamp_eq_clamp ha0 haa' ha'1 (le_of_lt (not_le.mp h))]
      -- The new `Φ` is locally constant on `p⁻¹[0, a']`. Three cases, `p(e) < a`, `= a`, `> a`.
      · rcases lt_trichotomy (p e : ℝ) a with hlt | heq | hgt
        -- `p(e) < a`: where `p < a` the new `Φ` is the old one, locally constant.
        · obtain ⟨V, hV, heV, hc⟩ := hΦloc e hlt.le
          refine ⟨V ∩ p ⁻¹' {t | (t : ℝ) < a}, hV.inter (hp.1 _ (isOpen_I_lt a)), ⟨heV, hlt⟩,
            fun e' he' _ => ?_⟩
          have h' : (p e' : ℝ) ≤ a := le_of_lt he'.2
          simp only [h', hlt.le, ite_true]
          exact hc e' he'.1 h'
        -- `p(e) = a`: `e` lies in a sheet `S`; on `V ∩ S` both pieces give `Φ(e)`, since `e` is
        -- the point of `S` over `a`.
        · have hpe : p e = c := Subtype.ext (heq.trans hcc.symm)
          obtain ⟨S, hS, heS⟩ := hsheet e (hpe ▸ hcU)
          obtain ⟨V, hV, heV, hc⟩ := hΦloc e heq.le
          refine ⟨V ∩ S, hV.inter (hopen S hS), ⟨heV, heS⟩, fun e' he' _ => ?_⟩
          simp only [heq.le, ite_true]
          by_cases h' : (p e' : ℝ) ≤ a
          · simp only [h', ite_true]
            exact hc e' he'.1 h'
          · simp only [h', ite_false]
            rw [hover S hS _ _ (hρ e' S hS he'.2).1 heS (hρ e' S hS he'.2).2 hpe]
        -- `p(e) > a`: `e` lies in a sheet `S`; on `S ∩ {p > a}` the new `Φ` is `Φ(ρ(e))`.
        · obtain ⟨S, hS, heS⟩ := hsheet e (hb _ hgt.le he)
          refine ⟨S ∩ p ⁻¹' {t | a < (t : ℝ)}, (hopen S hS).inter (hp.1 _ (isOpen_I_gt a)),
            ⟨heS, hgt⟩, fun e' he' _ => ?_⟩
          have h' : ¬ (p e' : ℝ) ≤ a := not_le.mpr he'.2
          simp only [h', not_le.mpr hgt, ite_false]
          rw [hover S hS _ _ (hρ e' S hS he'.1).1 (hρ e S hS heS).1 (hρ e' S hS he'.1).2
            (hρ e S hS heS).2]
      -- `Φ(Ψ(t, x)) = x` for `t ≤ a'`.
      · by_cases h : (q.1 : ℝ) ≤ a
        · have hp' : (p (Ψ q) : ℝ) ≤ a := by
            rw [hpΨ, I.clamp_of_mem le_rfl ha0 (haa'.trans ha'1) q.1.2.1 h]
            exact h
          simp only [h, hp', ite_true]
          exact hΦΨ q h
        · have hq' : I.clamp a a' q.1 = q.1 :=
            I.clamp_of_mem ha0 haa' ha'1 (le_of_lt (not_le.mp h)) hq
          have hp' : ¬ (p (σ q.2 q.1) : ℝ) ≤ a := by
            rw [hσp, hq']
            exact h
          simp only [h, hp', ite_false]
          exact hΦρ q.2 _ (hσS q.2 q.1)
      -- `Ψ(p(e), Φ(e)) = e` for `p(e) ≤ a'`.
      · by_cases h : (p e : ℝ) ≤ a
        · simp only [h, ite_true]
          exact hΨΦ e h
        · simp only [h, ite_false]
          -- `e` lies in a sheet `S`, and `x = Φ(ρ(e))` has `Ψ(a, x) = ρ(e) ∈ S`; so `S(x) = S`,
          -- and `σ_x(p(e))` is the point of `S` over `p(e)`, which is `e`.
          obtain ⟨S, hS, heS⟩ := hsheet e (hb _ (le_of_lt (not_le.mp h)) he)
          obtain ⟨hρS, hpρ⟩ := hρ e S hS heS
          have hΨρ : Ψ (c, Φ (ρ e)) = ρ e := by
            have := hΨΦ (ρ e) (by rw [hpρ, hcc])
            rwa [hpρ] at this
          have hSS : Sa (Φ (ρ e)) = S :=
            hsame _ (hSa _) S hS _ (hΨSa _) (show Ψ (c, Φ (ρ e)) ∈ S by rw [hΨρ]; exact hρS)
          have hq' : I.clamp a a' (p e) = p e :=
            I.clamp_of_mem ha0 haa' ha'1 (le_of_lt (not_le.mp h)) he
          refine (hhom S hS).1 (hSS ▸ hσS _ (p e)) heS ?_
          rw [hσp, hq']
  -- Step 3. For `j = N`, `[0, N/N] = I`: `e ↦ (p(e), Φ(e))` and `Ψ` are inverse homeomorphisms
  -- over `I`; `Φ` is continuous, being locally constant everywhere.
  have hNN : (N : ℝ) / N = 1 := div_self (by exact_mod_cast hN.ne')
  obtain ⟨Ψ, Φ, hΨc, hpΨ, hΦloc, hΦΨ, hΨΦ⟩ := key N le_rfl
  rw [hNN] at hpΨ hΦloc hΦΨ hΨΦ
  have hΦc : Continuous Φ := continuous_of_locallyConst fun e => by
    obtain ⟨V, hV, heV, hc⟩ := hΦloc e (p e).2.2
    exact ⟨V, hV, heV, fun e' he' => hc e' he' (p e').2.2⟩
  refine ⟨{
    toFun := fun e => (p e, Φ e)
    invFun := Ψ
    left_inv := fun e => hΨΦ e (p e).2.2
    right_inv := fun q => Prod.ext (show p (Ψ q) = q.1 by rw [hpΨ, I.clamp_zero_one])
      (hΦΨ q q.1.2.2)
    continuous_toFun := hp.1.prodMk hΦc
    continuous_invFun := hΨc }, fun e => rfl⟩

/-- A locally trivial fibration with a discrete fibre `F` (`hF`: every subset of `F` is open)
is a covering map: the sheets over `U` are the sets `φ⁻¹(U × {a})`, `a ∈ F`. The remark after
`def:covering-map`, and the sentence after `def:fibration`. Mathlib: `IsFiberBundle.isCoveringMap`.

(The converse, for a covering whose fibres are all in bijection with `F`, is the other half of
that remark; it is not formalised here.) -/
theorem IsLocallyTrivial.isCovering {p : E → B} (hp : IsLocallyTrivial p F)
    (hF : ∀ A : Set F, IsOpen A) : IsCovering p := by
  refine ⟨hp.1, fun b => ?_⟩
  obtain ⟨U, hU, hbU, φ, hφ⟩ := hp.2 b
  -- `p⁻¹(U)` is open, `p` being continuous.
  have hpU : IsOpen (p ⁻¹' U) := hp.1 U hU
  -- The sheet `T(a)`, `a ∈ F`: the points `e` of `p⁻¹(U)` with `φ(e) ∈ U × {a}`.
  let T : F → Set E := fun a => {e | ∃ he : p e ∈ U, (φ.toFun ⟨e, he⟩).2 = a}
  -- `T(a)` is the image in `E` of the preimage of the open `{a}` under the continuous
  -- `e ↦ pr_F φ(e)` on the open `p⁻¹(U)`; so it is open (`IsOpen.image_val`).
  have hT : ∀ a, T a = Subtype.val '' ((fun z => (φ.toFun z).2) ⁻¹' {a}) := fun a => by
    ext e
    constructor
    · rintro ⟨he, h⟩
      exact ⟨⟨e, he⟩, h, rfl⟩
    · rintro ⟨⟨e', he⟩, h, rfl⟩
      exact ⟨he, h⟩
  have hTo : ∀ a, IsOpen (T a) := fun a => by
    rw [hT]
    exact hpU.image_val ((continuous_snd.comp φ.continuous_toFun) _ (hF {a}))
  -- `σ_a : U → E`, `u ↦ φ⁻¹(u, a)`, is continuous, lands in `T(a)` and lies over `u`.
  let σ : F → U → E := fun a u => (φ.invFun (u, a)).1
  have hσc : ∀ a, Continuous (σ a) := fun a =>
    continuous_subtype_val.comp (φ.continuous_invFun.comp (continuous_id.prodMk continuous_const))
  have hσp : ∀ a u, p (σ a u) = u := fun a u => by
    rw [← hφ, φ.right_inv]
  have hσT : ∀ a u, σ a u ∈ T a := fun a u =>
    ⟨(φ.invFun (u, a)).2, by show (φ.toFun (φ.invFun (u, a))).2 = a; rw [φ.right_inv]⟩
  -- Two points of `T(a)` over the same point are equal, as `φ` is one to one.
  have hTinj : ∀ a, InjOn p (T a) := fun a e he e' he' hpe => by
    obtain ⟨h1, h1'⟩ := he
    obtain ⟨h2, h2'⟩ := he'
    have : φ.toFun ⟨e, h1⟩ = φ.toFun ⟨e', h2⟩ :=
      Prod.ext (Subtype.ext (by rw [hφ, hφ]; exact hpe)) (h1'.trans h2'.symm)
    exact congrArg Subtype.val (φ.injective this)
  -- `p(T(a)) = U`.
  have hTim : ∀ a, p '' T a = U := fun a => by
    ext u
    constructor
    · rintro ⟨e, ⟨he, -⟩, rfl⟩
      exact he
    · intro hu
      exact ⟨σ a ⟨u, hu⟩, hσT a ⟨u, hu⟩, hσp a ⟨u, hu⟩⟩
  refine ⟨U, hbU, hU, range T, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨a, rfl⟩
    exact hTo a
  -- Different sheets are disjoint: a point of `T(a) ∩ T(a')` has `a = pr_F φ(e) = a'`.
  · rintro _ ⟨a, rfl⟩ _ ⟨a', rfl⟩ hne
    refine Set.disjoint_left.mpr fun e ⟨h1, h1'⟩ ⟨h2, h2'⟩ => hne ?_
    rw [← h1', ← h2']
  -- `p⁻¹(U)` is the union of the sheets: `e ∈ T(pr_F φ(e))`.
  · ext e
    constructor
    · intro he
      exact ⟨T (φ.toFun ⟨e, he⟩).2, ⟨_, rfl⟩, he, rfl⟩
    · rintro ⟨_, ⟨a, rfl⟩, he, -⟩
      exact he
  -- Each sheet maps homeomorphically onto `U`. If `W ⊆ U` is open, `T(a) ∩ p⁻¹(W)` is open (`p`
  -- is continuous). Conversely, `W` is the image in `B` of `σ_a⁻¹(T(a) ∩ p⁻¹(W))`, open in the
  -- open `U` because `σ_a` is continuous.
  · rintro _ ⟨a, rfl⟩
    refine ⟨hTinj a, hTim a, fun W hWU => ⟨fun hW => (hTo a).inter (hp.1 W hW), fun hW => ?_⟩⟩
    have : W = Subtype.val '' (σ a ⁻¹' (T a ∩ p ⁻¹' W)) := by
      ext u
      constructor
      · intro hu
        refine ⟨⟨u, hWU hu⟩, ⟨hσT a _, ?_⟩, rfl⟩
        show p (σ a ⟨u, hWU hu⟩) ∈ W
        rw [hσp]
        exact hu
      · rintro ⟨u', ⟨-, hu'⟩, rfl⟩
        have : p (σ a u') ∈ W := hu'
        rwa [hσp] at this
    rw [this]
    exact hU.image_val (hσc a _ hW)

/-- **`def:universal-cover`**: let `B` be path-connected. A universal cover of `B` is a covering
`p : E → B` with `E` simply connected (`def:simply-connected`: non-empty, path-connected, with
trivial `π₁`). Here the hypothesis on `B` is the third condition. Mathlib: none
(`IsCoveringMap` with `SimplyConnectedSpace`). -/
def IsUniversalCover (p : E → B) : Prop :=
  IsCovering p ∧ SimplyConnected E ∧ PathConnected B

end Fibration

/-! ## The mapping cylinder (`def:mapping-cylinder`, `prop:mapping-cylinder`) -/

section MappingCylinder
variable {X : Type u} {Z : Type v} {A : Type*} [TopSpace X] [TopSpace Y] [TopSpace Z]
  [TopSpace A]

/-- A map on `(A ⊔ Y) × I` is continuous if it is continuous on `A × I` and on `Y × I`: the space
`(A ⊔ Y) × I` is the disjoint union of `A × I` and `Y × I` (Mathlib:
`Homeomorph.sumProdDistrib`, `Continuous.sumElim`), taken through the bridges `prod_toMathlib`,
`sum_toMathlib`, `I_toMathlib`. -/
theorem continuous_sum_prod_I {g : (A ⊕ Y) × I → Z}
    (h₁ : Continuous (fun p : A × I => g (Sum.inl p.1, p.2)))
    (h₂ : Continuous (fun p : Y × I => g (Sum.inr p.1, p.2))) : Continuous g := by
  let _ := (‹TopSpace A›).toMathlib
  let _ := (‹TopSpace Y›).toMathlib
  let _ := (‹TopSpace Z›).toMathlib
  -- The two pieces, in Mathlib's language.
  have h₁' : _root_.Continuous (fun p : A × unitInterval => g (Sum.inl p.1, p.2)) :=
    mathlib_continuous_of_eq (by rw [prod_toMathlib, I_toMathlib]) rfl h₁
  have h₂' : _root_.Continuous (fun p : Y × unitInterval => g (Sum.inr p.1, p.2)) :=
    mathlib_continuous_of_eq (by rw [prod_toMathlib, I_toMathlib]) rfl h₂
  -- `g` is the map defined by cases on `A × I ⊔ Y × I`, composed with `(A ⊔ Y) × I ≅
  -- A × I ⊔ Y × I`.
  have hg : _root_.Continuous g := by
    have : g = Sum.elim (fun p : A × unitInterval => g (Sum.inl p.1, p.2))
        (fun p : Y × unitInterval => g (Sum.inr p.1, p.2)) ∘
          Homeomorph.sumProdDistrib (X := A) (Y := Y) (Z := unitInterval) := by
      funext q
      rcases q with ⟨a | y, t⟩ <;> rfl
    rw [this]
    exact (h₁'.sumElim h₂').comp (Homeomorph.continuous _)
  exact continuous_of_mathlib_eq (by rw [prod_toMathlib, sum_toMathlib, I_toMathlib]) rfl hg

/-- **`def:mapping-cylinder`**: for `f : X → Y`, the mapping cylinder `M_f` is the pushout of
`X × I ← X → Y`, `(x, 1) ↤ x ↦ f(x)` (`def:pushout`, `Week02Glue.lean`): the cylinder `X × I`
with its top `X × {1}` glued to `Y` by `f`, `(x, 1) ∼ f(x)`. Mathlib: none. -/
abbrev MappingCylinder (f : X → Y) : Type _ := Pushout (fun x : X => ((x, 1) : X × I)) f

/-- The inclusion `i : X → M_f`, `x ↦ [x, 0]`, of the bottom of the cylinder. -/
def MappingCylinder.incl (f : X → Y) (x : X) : MappingCylinder f := Pushout.inl (x, 0)

/-- The retraction `r : M_f → Y`: `r[x, s] = f(x)` on the cylinder, `r(y) = y` on `Y`; well
defined because at `s = 1` both say `f(x)`. -/
def MappingCylinder.retr (f : X → Y) : MappingCylinder f → Y :=
  Pushout.desc (fun q : X × I => f q.1) (fun y => y) fun _ => rfl

/-- The deformation `H([x, s], t) = [x, s + t(1 - s)]` on the cylinder, `H(y, t) = y` on `Y`
(`prop:mapping-cylinder`). It is well defined: at `s = 1` it is `[x, 1] = f(x)` for every `t`.
`Cone.up (s, t) = s + t(1 - s)` is the same slide as for the cone (`prop:cone-contractible`). -/
def MappingCylinder.slide (f : X → Y) (q : MappingCylinder f × I) : MappingCylinder f :=
  Pushout.desc (fun p : X × I => (Pushout.inl (p.1, Cone.up (p.2, q.2)) : MappingCylinder f))
    Pushout.inr (fun x => by
      show Pushout.inl (x, Cone.up (1, q.2)) = Pushout.inr (f x)
      rw [Cone.one_up]
      exact congrFun pushout_comm x) q.1

/-- **`prop:mapping-cylinder`**: `Y` is a deformation retract of `M_f`, and `f` is the composite
`r ∘ i` of the inclusion `i : X → M_f` with the retraction `r : M_f → Y`, which is the identity
on `Y`. So up to homotopy equivalence every map is an inclusion. Mathlib: none.

The book's proof: `H([x, s], t) = [x, s + t(1 - s)]`, `H(y, t) = y` is well defined
(`MappingCylinder.slide`) and continuous, because `M_f × I` is a quotient of
`((X × I) ⊔ Y) × I` (Munkres, Exercise 29.11, `continuous_quotient_prod_I`, cited in the book's
"not proved" list). At `t = 1` it lands in `Y`, at `[x, 1] = f(x)` or at `y`. -/
theorem mappingCylinder_deformationRetract (f : X → Y) :
    IsDeformationRetract (range (Pushout.inr : Y → MappingCylinder f)) ∧
      MappingCylinder.retr f ∘ MappingCylinder.incl f = f ∧
      MappingCylinder.retr f ∘ Pushout.inr = id := by
  refine ⟨⟨MappingCylinder.slide f, ?_, ?_, ?_, ?_⟩, rfl, rfl⟩
  -- `H` is continuous: by Munkres 29.11 it suffices that `(u, t) ↦ H([u], t)` is continuous on
  -- `((X × I) ⊔ Y) × I`, which is checked on the two pieces: `((x, s), t) ↦ [x, up(s, t)]`
  -- and `(y, t) ↦ [y]`.
  · apply continuous_quotient_prod_I
    apply continuous_sum_prod_I
    · exact continuous_pushout_inl.comp ((continuous_fst.comp continuous_fst).prodMk
        (Cone.continuous_up.comp ((continuous_snd.comp continuous_fst).prodMk continuous_snd)))
    · exact continuous_pushout_inr.comp continuous_fst
  -- `H(-, 0) = id`: `up(s, 0) = s`. (Lean: `Quotient.ind` reduces to a class `[u]`, and
  -- `rcases` splits `u` into a point of the cylinder or of `Y`.)
  · intro c
    induction c using Quotient.ind with
    | _ u =>
      rcases u with ⟨x, s⟩ | y
      · show Pushout.inl (x, Cone.up (s, 0)) = Pushout.inl (x, s)
        rw [Cone.up_zero]
      · rfl
  -- `H(-, 1)` lands in `Y`: `[x, up(s, 1)] = [x, 1] = f(x)`.
  · intro c
    induction c using Quotient.ind with
    | _ u =>
      rcases u with ⟨x, s⟩ | y
      · refine ⟨f x, ?_⟩
        show Pushout.inr (f x) = Pushout.inl (x, Cone.up (s, 1))
        rw [Cone.up_one]
        exact (congrFun pushout_comm x).symm
      · exact ⟨y, rfl⟩
  -- `H` fixes `Y` at all times, by definition.
  · rintro _ ⟨y, rfl⟩ t
    rfl

end MappingCylinder

/-! ## Higher homotopy groups are abelian (`thm-3n-eh`)

Here `πₙ(X, x)` is Mathlib's `HomotopyGroup.Pi n X x` (written `π_ n X x` in Mathlib), for the
course's topology on `X` read as Mathlib's (`toMathlib`): the classes of maps
`(Iⁿ, ∂Iⁿ) → (X, x)` up to homotopy rel `∂Iⁿ`. The course does not define `πₙ` itself. -/

/-- **`thm-3n-eh`**: for `n ≥ 2`, written `n + 2` with `n ≥ 0`, the group
`πₙ(X, x)` is abelian. Mathlib: `HomotopyGroup.commGroup`, `EckmannHilton.mul_comm`.

The book's proof, which is the one below. Concatenating in the first coordinate gives a law
`·₁`, in the second a law `·₂` (Mathlib: `HomotopyGroup.auxGroup 0` and `auxGroup 1`); both have
the constant map as unit (`isUnital_auxGroup`), and they satisfy the interchange law
`(f ·₂ g) ·₁ (h ·₂ k) = (f ·₁ h) ·₂ (g ·₁ k)`, both sides being the map that is `f, g, h, k` on
the four quarter-cubes (Mathlib: `GenLoop.transAt_distrib`). Putting units in the right places
shows that `·₁ = ·₂` and that the law is commutative (Mathlib: `EckmannHilton.mul_comm`). The
group law of `πₙ` is `·₂` (all the laws agree, Mathlib's `auxGroup_indep`). -/
theorem eckmann_hilton {X : Type u} [t : TopSpace X] (n : ℕ) (x : X)
    (a b : @HomotopyGroup.Pi (n + 2) X t.toMathlib x) : a * b = b * a := by
  let _ := t.toMathlib
  open HomotopyGroup GenLoop in
  -- Step 1. The two coordinates `i = 0` and `j = 1` differ (here `n + 2 ≥ 2` is used).
  have hij : (0 : Fin (n + 2)) ≠ 1 := by simp
  -- Step 2. The two laws `·₁`, `·₂`, each with the constant map as unit.
  have h₁ := isUnital_auxGroup (X := X) (x := x) (0 : Fin (n + 2))
  have h₂ := isUnital_auxGroup (X := X) (x := x) (1 : Fin (n + 2))
  -- Step 3. The interchange law, checked on representatives `f, g, h, k` (`transAt_distrib`).
  -- (Lean: `rintro ⟨f⟩` takes a class and names a loop representing it.)
  have hdist : ∀ a b c d : HomotopyGroup (Fin (n + 2)) X x,
      (auxGroup 0).mul ((auxGroup 1).mul a b) ((auxGroup 1).mul c d) =
        (auxGroup 1).mul ((auxGroup 0).mul a c) ((auxGroup 0).mul b d) := by
    rintro ⟨f⟩ ⟨g⟩ ⟨h⟩ ⟨k⟩
    change Quotient.mk' _ = _
    apply congr_arg Quotient.mk'
    simp only [fromLoop_trans_toLoop, transAt_distrib hij, Homeomorph.coe_toEquiv,
      loopHomeo_apply, Homeomorph.coe_symm_toEquiv, loopHomeo_symm_apply]
  -- Step 4. Eckmann–Hilton: so `·₂` is commutative.
  have hcomm := EckmannHilton.mul_comm h₁ h₂ hdist
  -- Step 5. The product of `πₙ` is `·₂`.
  have hgrp : (HomotopyGroup.group (Fin (n + 2)) : Group (HomotopyGroup (Fin (n + 2)) X x)) =
      auxGroup 1 := auxGroup_indep _ 1
  have key : ∀ a b : HomotopyGroup (Fin (n + 2)) X x, a * b = (auxGroup 1).mul a b := by
    intro a b
    rw [← hgrp]
    rfl
  rw [key, key]
  exact hcomm.comm a b

end

end Course
