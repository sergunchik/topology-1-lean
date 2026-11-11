/-
Machine-generated (Claude, Aristotle), no line written by a person. Copyleft: GPL-3.0-or-later.

# Week 2: the reals, products, quotients, coproducts

This file builds the spaces of week 2 of the book on top of
week 1's definitions. First `ℝ`, with the topology of the metric `|x - y|`, and the interval
`I = [0, 1]` as a subspace. Then the three constructions that every later week uses, each with
its universal property: the product `∏ᵢ Xᵢ`, whose base is the boxes `∏ᵢ Uᵢ` with `Uᵢ = Xᵢ` for
all but finitely many `i`, and in which a map into the product is continuous iff its components
are (`thm:product-top`); the disjoint union `∐ᵢ Xᵢ`, in which a map out of it is continuous iff
its restrictions are (`prop:coproduct-top`); and the quotient `X/∼`, with the final topology for
`q : X → X/∼` (`def:initial-final`, `def:quotient`), out of which a map `f` is continuous iff
`f ∘ q` is (`prop:quotient-univ`). Finally the continuity of `+`, `·`, `-`, `min`, `max` on `ℝ`,
which the course takes from Analysis I.

Departures from the book:
* The topology of `ℝ` is that of a pseudo-metric (week 1's `PseudoMetric.toTopSpace`), and
  `I = [0, 1]` carries the subspace topology (`def-1-14`).
* Products and coproducts are done twice: for two spaces (`X × Y`, `X ⊕ Y`), which is what most
  of the course uses, and for a family (`∀ i, A i` is `∏ᵢ Aᵢ`, `Σ i, A i` is `∐ᵢ Aᵢ`). The
  universal property is stated as "a map is continuous iff its components (restrictions) are";
  that the map with given components is unique is a fact about sets, recalled in a docstring.
* The final topology is defined for a single map `q : X → Y` (`TopSpace.coinduced`), not
  necessarily onto; for a family of maps the book's definition is not formalised here. The
  initial topology is not formalised, except in its two cases: the subspace (week 1) and the
  product.
* From Analysis I, through the bridges `real_toMathlib` and `prod_toMathlib` (week 1 says what
  a bridge is): the continuity of `+`, `·`, `-`, `x ↦ -x`, `min`, `max` on `ℝ`. No other proof
  uses a bridge. Mathlib's names below were checked against Lean and Mathlib v4.34.1.

New to Lean? Read `Course/README.md` first.
-/
import Course.Week01
import Mathlib.Topology.Constructions.SumProd
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.Order.Real
import Mathlib.Topology.UnitInterval

-- Bookkeeping, as in week 1: universe levels (ignore them), the namespace `Course`, `open Set`.
universe u v w

set_option warn.classDefReducibility false

namespace Course

open Set

variable {X : Type u} {Y : Type v} {Z : Type w}

/-! ## The real line and the unit interval -/

/-- The metric `d(x, y) = |x - y|` on `ℝ` (Analysis I 1.2). Mathlib: `Real.pseudoMetricSpace`
(`Real.dist_eq`).

Lean: `noncomputable` says that the definition uses real numbers, which Lean cannot compute
with; it changes nothing for proofs. -/
noncomputable def realMetric : PseudoMetric ℝ where
  d x y := |x - y|
  -- `|x - y| ≥ 0`, `|x - x| = 0`, `|x - y| = |y - x|`, `|x - z| ≤ |x - y| + |y - z|`:
  -- facts about the absolute value (Analysis I).
  nonneg _ _ := abs_nonneg _
  self x := by simp
  symm x y := abs_sub_comm x y
  triangle x y z := abs_sub_le x y z

/-- The topology of `ℝ`: that of the metric `|x - y|`. Mathlib: the topology of
`Real.pseudoMetricSpace` (see `isOpen_real_iff`).

Lean: an `instance`, so that Lean uses this topology whenever `ℝ` appears as a space. -/
noncomputable instance real : TopSpace ℝ := realMetric.toTopSpace

/-- `U ⊆ ℝ` is open iff it contains an interval `(x - ε, x + ε)`, written as a ball, about each
of its points: week 1's `PseudoMetric.isOpen_iff` for this metric. Mathlib: `Metric.isOpen_iff`. -/
theorem isOpen_real_iff_ball (U : Set ℝ) :
    IsOpen U ↔ ∀ x ∈ U, ∃ ε > 0, realMetric.ball x ε ⊆ U :=
  realMetric.isOpen_iff U

/-- **Bridge.** The open sets of `ℝ` are Mathlib's. Mathlib: `Metric.isOpen_iff`. -/
theorem isOpen_real_iff (U : Set ℝ) : IsOpen U ↔ _root_.IsOpen U := by
  -- Both say "`U` contains a ball about each of its points"; Mathlib's ball `{y | |y - x| < ε}`
  -- is ours, `{y | |x - y| < ε}`, since `|y - x| = |x - y|`.
  rw [isOpen_real_iff_ball, Metric.isOpen_iff]
  have hball : ∀ x ε, Metric.ball x ε = realMetric.ball x ε := by
    intro x ε; ext y
    change |y - x| < ε ↔ |x - y| < ε
    rw [abs_sub_comm]
  simp only [hball]

/-- **Bridge.** The topology of `ℝ` is Mathlib's: two topologies with the same open sets are
equal (`TopologicalSpace.ext`).

Lean: `(inferInstance : TopologicalSpace ℝ)` is the topology on `ℝ` that Mathlib provides. -/
theorem real_toMathlib : real.toMathlib = (inferInstance : TopologicalSpace ℝ) := by
  apply TopologicalSpace.ext
  funext U
  exact propext (isOpen_real_iff U)

/-- The unit interval `[0, 1]`, with the subspace topology of `ℝ` (`def-1-14`).
Mathlib: `unitInterval`.

Lean: `Icc 0 1` is the closed interval `{x | 0 ≤ x ≤ 1}`. `abbrev` is a `def` that Lean unfolds
freely, so that `I` is seen as a subset of `ℝ` and gets week 1's subspace topology; a point
`s : I` is a real number `(s : ℝ)` with a proof that `0 ≤ s ≤ 1`. -/
abbrev I : Set ℝ := Icc 0 1

/-- **Bridge.** The topology of `I` is Mathlib's topology of `unitInterval`.
Mathlib: `instTopologicalSpaceSubtype`. -/
theorem I_toMathlib : (subspace I).toMathlib = (inferInstance : TopologicalSpace unitInterval) := by
  -- A subspace of `ℝ` (`subspace_toMathlib`), with `ℝ`'s topology Mathlib's (`real_toMathlib`).
  rw [subspace_toMathlib, real_toMathlib]

/-- **Bridge.** The open sets of `I` are those of Mathlib's `unitInterval`. -/
theorem isOpen_I_iff (V : Set I) : IsOpen V ↔ @_root_.IsOpen unitInterval _ V := by
  rw [isOpen_iff_mathlib, I_toMathlib]

/-! ## Products (`def:product`, `thm:product-top`) -/

section Product
variable [TopSpace X] [TopSpace Y] [TopSpace Z]

variable (X Y) in
/-- The open rectangles `U × V`, `U` open in `X` and `V` open in `Y`: the base of
`thm:product-top` for two factors. Mathlib: no name (see `isOpen_prod_iff`).

Lean: `U ×ˢ V` is the product `U × V` of two sets, a subset of `X × Y`; `X × Y` itself is the
product of the sets, whose points are pairs `(x, y)`. -/
def rectangles : Set (Set (X × Y)) := {W | ∃ U V, IsOpen U ∧ IsOpen V ∧ W = U ×ˢ V}

/-- `thm:product-top`: the product topology on `X × Y`, generated by the open rectangles, which
are a base by the base criterion `prop-1-10`: they cover, since `X × Y` is one, and the
intersection of two is a third. Mathlib: `instTopologicalSpaceProd` (see `prod_toMathlib`). -/
instance prod : TopSpace (X × Y) :=
  TopSpace.ofBase (rectangles X Y)
    -- They cover: `X × Y` is itself an open rectangle.
    (eq_univ_of_forall fun _ =>
      ⟨univ ×ˢ univ, ⟨univ, univ, isOpen_univ, isOpen_univ, rfl⟩, by simp⟩)
    -- The intersection of two is a third: `(U × V) ∩ (U' × V') = (U ∩ U') × (V ∩ V')`.
    (by
      rintro _ ⟨U, V, hU, hV, rfl⟩ _ ⟨U', V', hU', hV', rfl⟩ z hz
      exact ⟨(U ∩ U') ×ˢ (V ∩ V'), ⟨_, _, hU.inter hU', hV.inter hV', rfl⟩,
        by rwa [← prod_inter_prod], by rw [prod_inter_prod]⟩)

/-- `thm:product-top`: the open rectangles are a base of the product (`prop-1-10`).
Mathlib: `TopologicalSpace.isTopologicalBasis_opens` with
`TopologicalSpace.IsTopologicalBasis.prod`. -/
theorem isBase_rectangles : IsBase (rectangles X Y) := TopSpace.isBase_ofBase _ _ _

/-- A product `U × V` of open sets is open: it is a member of the base. Mathlib: `IsOpen.prod`. -/
theorem IsOpen.prod {U : Set X} {V : Set Y} (hU : IsOpen U) (hV : IsOpen V) :
    IsOpen (U ×ˢ V) :=
  isBase_rectangles.1 _ ⟨U, V, hU, hV, rfl⟩

/-- `W ⊆ X × Y` is open iff it contains an open rectangle about each of its points.
Mathlib: `isOpen_prod_iff`. -/
theorem isOpen_prod_iff {W : Set (X × Y)} :
    IsOpen W ↔ ∀ z ∈ W, ∃ U V, IsOpen U ∧ IsOpen V ∧ z ∈ U ×ˢ V ∧ U ×ˢ V ⊆ W := by
  constructor
  · -- An open `W` contains a member of the base about each of its points (`IsBase.exists_subset`).
    intro hW z hz
    obtain ⟨_, ⟨U, V, hU, hV, rfl⟩, hzB, hBW⟩ := isBase_rectangles.exists_subset hW hz
    exact ⟨U, V, hU, hV, hzB, hBW⟩
  · -- Conversely, `W` is the union of the open rectangles inside it.
    intro h
    refine ⟨{B | B ∈ rectangles X Y ∧ B ⊆ W}, fun B hB => hB.1, ?_⟩
    ext z
    constructor
    · intro hz
      obtain ⟨U, V, hU, hV, hzUV, hUVW⟩ := h z hz
      exact ⟨U ×ˢ V, ⟨⟨U, V, hU, hV, rfl⟩, hUVW⟩, hzUV⟩
    · rintro ⟨B, ⟨_, hBW⟩, hzB⟩
      exact hBW hzB

/-- `thm:product-top`: the first projection `π₁(x, y) = x` is continuous, `π₁⁻¹(U) = U × Y`
being a basic set. Mathlib: `continuous_fst`.

Lean: `Prod.fst` is `π₁`, and `q.1` is the first coordinate of a pair `q`. -/
theorem continuous_fst : Continuous (Prod.fst : X × Y → X) := fun U hU => by
  rw [← prod_univ]; exact hU.prod isOpen_univ

/-- `thm:product-top`: the second projection `π₂(x, y) = y` is continuous, `π₂⁻¹(V) = X × V`
being a basic set. Mathlib: `continuous_snd`. -/
theorem continuous_snd : Continuous (Prod.snd : X × Y → Y) := fun V hV => by
  rw [← univ_prod]; exact isOpen_univ.prod hV

/-- `thm:product-top`, the universal property: `z ↦ (f z, g z)` is continuous iff `f` and `g`
are, since its preimage of `U × V` is `f⁻¹(U) ∩ g⁻¹(V)` and continuity may be checked on a
base (`prop-1-19`). The map is the only one with these components (`Prod.ext`).
Mathlib: `continuous_prodMk`. -/
theorem continuous_prodMk {f : Z → X} {g : Z → Y} :
    Continuous (fun z => (f z, g z)) ↔ Continuous f ∧ Continuous g := by
  constructor
  · -- `f = π₁ ∘ (f, g)` and `g = π₂ ∘ (f, g)` are composites of continuous maps
    -- (`prop-1n-composite`).
    intro h
    exact ⟨continuous_fst.comp h, continuous_snd.comp h⟩
  · -- Conversely, it suffices to check preimages of basic sets (`prop-1-19`), and the preimage
    -- of `U × V` is `f⁻¹(U) ∩ g⁻¹(V)`, an intersection of two open sets.
    rintro ⟨hf, hg⟩
    rw [continuous_iff_base isBase_rectangles]
    rintro _ ⟨U, V, hU, hV, rfl⟩
    rw [mk_preimage_prod]
    exact (hf U hU).inter (hg V hV)

/-- A map `h : Z → X × Y` is continuous iff its two components `π₁ ∘ h`, `π₂ ∘ h` are: the
universal property again, for `h = (π₁ ∘ h, π₂ ∘ h)`. Mathlib: `continuous_prodMk`. -/
theorem continuous_prod_iff {h : Z → X × Y} :
    Continuous h ↔ Continuous (Prod.fst ∘ h) ∧ Continuous (Prod.snd ∘ h) :=
  continuous_prodMk (f := fun z => (h z).1) (g := fun z => (h z).2)

/-- **Bridge.** The product topology is Mathlib's. Mathlib: `isOpen_prod_iff`. -/
theorem prod_toMathlib :
    (prod : TopSpace (X × Y)).toMathlib =
      @instTopologicalSpaceProd X Y (‹TopSpace X›).toMathlib (‹TopSpace Y›).toMathlib := by
  -- Both say: `W` is open iff it contains an open rectangle about each of its points
  -- (`isOpen_prod_iff` here, `_root_.isOpen_prod_iff` in Mathlib).
  let _ := (‹TopSpace X›).toMathlib
  let _ := (‹TopSpace Y›).toMathlib
  apply TopologicalSpace.ext
  funext W
  apply propext
  change IsOpen W ↔ _
  rw [isOpen_prod_iff, _root_.isOpen_prod_iff]
  constructor
  · intro h a b hab
    obtain ⟨U, V, hU, hV, ⟨ha, hb⟩, hUV⟩ := h (a, b) hab
    exact ⟨U, V, hU, hV, ha, hb, hUV⟩
  · rintro h ⟨a, b⟩ hab
    obtain ⟨U, V, hU, hV, ha, hb, hUV⟩ := h a b hab
    exact ⟨U, V, hU, hV, ⟨ha, hb⟩, hUV⟩

end Product

/-! ## The arithmetic of `ℝ` is continuous (the Analysis I input)

The book takes the continuity of `+`, `·`, `-`, `min`, `max` on `ℝ × ℝ` from Analysis I; here it
comes from Mathlib through the bridges `prod_toMathlib` and `real_toMathlib`. Constant maps are
continuous by `continuous_const` (week 1). -/

section Arithmetic

/-- A map `ℝ × ℝ → ℝ` continuous in Mathlib's sense is continuous in the course's: the bridge
through which the Analysis I facts below enter. -/
theorem continuous_real_of_mathlib {f : ℝ × ℝ → ℝ} (hf : _root_.Continuous f) : Continuous f := by
  -- The course's continuity is Mathlib's (`continuous_iff_mathlib`) for the topologies of
  -- `ℝ × ℝ` and `ℝ`, which are Mathlib's (`prod_toMathlib`, `real_toMathlib`).
  rw [continuous_iff_mathlib, prod_toMathlib, real_toMathlib]
  exact hf

/-- The same for maps `ℝ → ℝ`. -/
theorem continuous_real_of_mathlib₁ {f : ℝ → ℝ} (hf : _root_.Continuous f) : Continuous f := by
  rw [continuous_iff_mathlib, real_toMathlib]
  exact hf

/-- Addition `ℝ × ℝ → ℝ` is continuous (Analysis I). Mathlib: `continuous_add`. -/
theorem continuous_add_real : Continuous (fun p : ℝ × ℝ => p.1 + p.2) :=
  continuous_real_of_mathlib _root_.continuous_add

/-- Multiplication `ℝ × ℝ → ℝ` is continuous (Analysis I). Mathlib: `continuous_mul`. -/
theorem continuous_mul_real : Continuous (fun p : ℝ × ℝ => p.1 * p.2) :=
  continuous_real_of_mathlib _root_.continuous_mul

/-- Subtraction `ℝ × ℝ → ℝ` is continuous (Analysis I). Mathlib: `continuous_sub`. -/
theorem continuous_sub_real : Continuous (fun p : ℝ × ℝ => p.1 - p.2) :=
  continuous_real_of_mathlib ContinuousSub.continuous_sub

/-- Negation `ℝ → ℝ` is continuous (Analysis I). Mathlib: `continuous_neg`. -/
theorem continuous_neg_real : Continuous (fun x : ℝ => -x) :=
  continuous_real_of_mathlib₁ ContinuousNeg.continuous_neg

/-- `min : ℝ × ℝ → ℝ` is continuous (Analysis I). Mathlib: `continuous_min`. -/
theorem continuous_min_real : Continuous (fun p : ℝ × ℝ => min p.1 p.2) :=
  continuous_real_of_mathlib _root_.continuous_min

/-- `max : ℝ × ℝ → ℝ` is continuous (Analysis I). Mathlib: `continuous_max`. -/
theorem continuous_max_real : Continuous (fun p : ℝ × ℝ => max p.1 p.2) :=
  continuous_real_of_mathlib _root_.continuous_max

/-- Constant maps `X → ℝ` are continuous: week 1's `continuous_const`, for any target.
Mathlib: `continuous_const`. -/
theorem continuous_const_real [TopSpace X] (c : ℝ) : Continuous (fun _ : X => c) :=
  continuous_const

end Arithmetic

/-! ## Final topologies and quotients (`def:initial-final`, `def:quotient`, `prop:quotient-univ`) -/

/-- `def:initial-final`, `def:quotient`: the final topology for a map `q : X → Y` from a space
to a set, in which `V` is open iff `q⁻¹(V)` is open; preimage commutes with intersections and
unions, so it is a topology. For `q` surjective it is the quotient topology.
Mathlib: `TopologicalSpace.coinduced` (see `coinduced_toMathlib`). -/
def TopSpace.coinduced [TopSpace X] (q : X → Y) : TopSpace Y where
  IsOpen V := IsOpen (q ⁻¹' V)
  -- `q⁻¹(Y) = X`, `q⁻¹(U ∩ V) = q⁻¹(U) ∩ q⁻¹(V)`, `q⁻¹(⋃₀ 𝒰) = ⋃_{U ∈ 𝒰} q⁻¹(U)`.
  isOpen_univ := by rw [preimage_univ]; exact isOpen_univ
  isOpen_inter U V hU hV := by rw [preimage_inter]; exact IsOpen.inter hU hV
  isOpen_sUnion 𝒰 h := by
    rw [preimage_sUnion]; exact isOpen_iUnion fun U => isOpen_iUnion fun hU => h U hU

section Final
variable [TopSpace X] [TopSpace Z]

/-- `V` is open in the final topology iff `q⁻¹(V)` is open: the definition.
Mathlib: `isOpen_coinduced`.

Lean: `@IsOpen Y (TopSpace.coinduced q) V` names the topology of `Y` by hand, since `Y` is only a
set. -/
theorem isOpen_coinduced_iff (q : X → Y) {V : Set Y} :
    @IsOpen Y (TopSpace.coinduced q) V ↔ IsOpen (q ⁻¹' V) := Iff.rfl

/-- `prop:quotient-univ`: `q` is continuous for the final topology: `q⁻¹(V)` is open for open
`V` by definition.
Mathlib: `continuous_coinduced_rng`. -/
theorem continuous_coinduced (q : X → Y) : @Continuous X Y _ (TopSpace.coinduced q) q :=
  fun _ hV => hV

/-- `def:initial-final`: the final topology is the finest making `q` continuous: every topology
`τ` on `Y` for which `q` is continuous has only open sets of the final topology.
Mathlib: `continuous_iff_coinduced_le`. -/
theorem coinduced_finest (q : X → Y) (τ : TopSpace Y) (hτ : @Continuous X Y _ τ q) (V : Set Y)
    (hV : τ.IsOpen V) : @IsOpen Y (TopSpace.coinduced q) V :=
  -- `q` is continuous for `τ`, so `q⁻¹(V)` is open: that is what open in the final topology means.
  hτ V hV

/-- `prop:quotient-univ`: a map `f` out of `Y`, with the final topology for `q`, is continuous
iff `f ∘ q` is: `q⁻¹(f⁻¹(W)) = (f ∘ q)⁻¹(W)`. Mathlib: `continuous_coinduced_dom`. -/
theorem continuous_coinduced_iff (q : X → Y) {f : Y → Z} :
    @Continuous Y Z (TopSpace.coinduced q) _ f ↔ Continuous (f ∘ q) :=
  -- For open `W ⊆ Z`, "`f⁻¹(W)` is open in `Y`" means "`q⁻¹(f⁻¹(W))` is open in `X`", and
  -- `q⁻¹(f⁻¹(W)) = (f ∘ q)⁻¹(W)`: the two sides say the same thing, for each `W`.
  ⟨fun hf W hW => hf W hW, fun h W hW => h W hW⟩

/-- **Bridge.** The final topology is Mathlib's `TopologicalSpace.coinduced`.
Mathlib: `isOpen_coinduced`. -/
theorem coinduced_toMathlib (q : X → Y) :
    (TopSpace.coinduced q).toMathlib = @TopologicalSpace.coinduced X Y q (‹TopSpace X›).toMathlib :=
  TopologicalSpace.ext rfl

end Final

/-- `def:quotient`: the quotient space `X/∼` of a space by an equivalence relation, the set of
classes with the final topology for `x ↦ [x]`. Mathlib: `instTopologicalSpaceQuotient`
(see `quotient_toMathlib`).

Lean: an equivalence relation `∼` on `X` is a `Setoid X` (we call it `s`, and write `a ≈ b` for
`a ∼ b`); `Quotient s` is the set `X/∼` of classes, and `Quotient.mk s : X → X/∼` is the
projection `q(x) = [x]`. -/
instance quotient [TopSpace X] (s : Setoid X) : TopSpace (Quotient s) :=
  TopSpace.coinduced (Quotient.mk s)

section Quotient
variable [TopSpace X] [TopSpace Z] {s : Setoid X}

/-- `def:quotient`: `V ⊆ X/∼` is open iff `q⁻¹(V)` is open in `X`: the definition.
Mathlib: `isOpen_coinduced` (Mathlib's quotient topology is also the final one). -/
theorem isOpen_quotient_iff {V : Set (Quotient s)} : IsOpen V ↔ IsOpen (Quotient.mk s ⁻¹' V) :=
  Iff.rfl

/-- `prop:quotient-univ`: the projection `X → X/∼` is continuous.
Mathlib: `continuous_quotient_mk'`. -/
theorem continuous_quotient_mk : Continuous (Quotient.mk s) :=
  continuous_coinduced _

/-- `prop:quotient-univ`: a map `f : X/∼ → Z` is continuous iff `f ∘ q` is.
Mathlib: `Topology.IsQuotientMap.continuous_iff` (for `isQuotientMap_quotient_mk'`). -/
theorem continuous_quotient_iff {f : Quotient s → Z} :
    Continuous f ↔ Continuous (f ∘ Quotient.mk s) :=
  continuous_coinduced_iff _

/-- `prop:quotient-univ`: a continuous `g : X → Z` constant on the classes induces a continuous
`ḡ : X/∼ → Z` with `ḡ ∘ q = g`. Mathlib: `continuous_quotient_lift`.

Lean: `h` says that `g` is constant on classes (`a ∼ b` implies `g a = g b`), and
`Quotient.lift g h` is the map `ḡ([x]) = g(x)`, well defined because of `h`. -/
theorem continuous_quotient_lift {g : X → Z} (hg : Continuous g) (h : ∀ a b, a ≈ b → g a = g b) :
    Continuous (Quotient.lift g h : Quotient s → Z) :=
  -- `ḡ ∘ q = g` is continuous, so `ḡ` is (`continuous_quotient_iff`).
  continuous_quotient_iff.mpr hg

-- (Lean: `omit … in` drops the topologies, which the next statement, about sets, does not use.)
omit [TopSpace X] [TopSpace Z] in
/-- `prop:quotient-univ`: `ḡ` is the only map with `ḡ ∘ q = g`, since `q` is onto: if
`f ∘ q = g` (`hf`), then `f = ḡ`. Mathlib: `Quotient.lift_comp_mk`, `Quotient.ind`. -/
theorem quotient_lift_unique {g : X → Z} (h : ∀ a b, a ≈ b → g a = g b) (f : Quotient s → Z)
    (hf : f ∘ Quotient.mk s = g) : f = Quotient.lift g h := by
  -- Two maps are equal if they agree at every class `y` (`funext`); every class is some `[x]`
  -- (`Quotient.ind`), and `f([x]) = g(x) = ḡ([x])`.
  funext y
  induction y using Quotient.ind with
  | _ x => exact congrFun hf x

/-- **Bridge.** The quotient topology is Mathlib's: both are the final topology for `q`. -/
theorem quotient_toMathlib :
    (quotient s).toMathlib = @instTopologicalSpaceQuotient X s (‹TopSpace X›).toMathlib :=
  TopologicalSpace.ext rfl

end Quotient

/-! ## Coproducts (`def:coproduct`, `prop:coproduct-top`) -/

/-- `prop:coproduct-top`: the disjoint union `X ⊔ Y`, in which `U` is open iff `U ∩ X` and
`U ∩ Y` are open, i.e. its preimages under the two inclusions are. Mathlib:
`instTopologicalSpaceSum` (see `sum_toMathlib`).

Lean: `X ⊕ Y` is the disjoint union of the sets, with inclusions `Sum.inl : X → X ⊕ Y` and
`Sum.inr : Y → X ⊕ Y` (the book's `ι₁`, `ι₂`); so `Sum.inl ⁻¹' U` is the book's `U ∩ X`. -/
instance sum [TopSpace X] [TopSpace Y] : TopSpace (X ⊕ Y) where
  IsOpen U := IsOpen (Sum.inl ⁻¹' U) ∧ IsOpen (Sum.inr ⁻¹' U)
  -- The axioms hold in `X` and in `Y` separately, since preimage commutes with `∩` and `⋃`.
  isOpen_univ := by simp only [preimage_univ]; exact ⟨isOpen_univ, isOpen_univ⟩
  isOpen_inter U V hU hV := by
    simp only [preimage_inter]; exact ⟨hU.1.inter hV.1, hU.2.inter hV.2⟩
  isOpen_sUnion 𝒰 h := by
    simp only [preimage_sUnion]
    exact ⟨isOpen_iUnion fun U => isOpen_iUnion fun hU => (h U hU).1,
      isOpen_iUnion fun U => isOpen_iUnion fun hU => (h U hU).2⟩

section Coproduct
variable [TopSpace X] [TopSpace Y] [TopSpace Z]

/-- `prop:coproduct-top`: `U ⊆ X ⊔ Y` is open iff `U ∩ X` and `U ∩ Y` are: the definition.
Mathlib: `isOpen_sum_iff`. -/
theorem isOpen_sum_iff {U : Set (X ⊕ Y)} :
    IsOpen U ↔ IsOpen (Sum.inl ⁻¹' U) ∧ IsOpen (Sum.inr ⁻¹' U) := Iff.rfl

/-- `prop:coproduct-top`: the first inclusion is continuous, by definition of the topology.
Mathlib: `continuous_inl`. -/
theorem continuous_inl : Continuous (Sum.inl : X → X ⊕ Y) := fun _ hU => hU.1

/-- `prop:coproduct-top`: the second inclusion is continuous. Mathlib: `continuous_inr`. -/
theorem continuous_inr : Continuous (Sum.inr : Y → X ⊕ Y) := fun _ hU => hU.2

/-- `prop:coproduct-top`, the universal property: a map out of `X ⊔ Y` is continuous iff its
restrictions to `X` and to `Y` are, since `h⁻¹(V) ∩ X = (h ∘ ι₁)⁻¹(V)`.
Mathlib: `continuous_sum_dom`. -/
theorem continuous_sum_iff {h : X ⊕ Y → Z} :
    Continuous h ↔ Continuous (h ∘ Sum.inl) ∧ Continuous (h ∘ Sum.inr) :=
  -- `⇒`: composites with the continuous inclusions. `⇐`: for open `V`, `h⁻¹(V)` is open iff
  -- `h⁻¹(V) ∩ X = (h ∘ ι₁)⁻¹(V)` and `h⁻¹(V) ∩ Y = (h ∘ ι₂)⁻¹(V)` are, which they are.
  ⟨fun hh => ⟨hh.comp continuous_inl, hh.comp continuous_inr⟩,
    fun ⟨h₁, h₂⟩ V hV => ⟨h₁ V hV, h₂ V hV⟩⟩

/-- `prop:coproduct-top`: maps `f : X → Z` and `g : Y → Z` glue to `X ⊔ Y → Z`, continuous iff
both are; it is the only map restricting to `f` and `g` (`Sum.elim`).
Mathlib: `continuous_sum_elim`.

Lean: `Sum.elim f g` is the map equal to `f` on `X` and to `g` on `Y`. -/
theorem continuous_sum_elim {f : X → Z} {g : Y → Z} :
    Continuous (Sum.elim f g) ↔ Continuous f ∧ Continuous g :=
  continuous_sum_iff

/-- **Bridge.** The disjoint union topology is Mathlib's. Mathlib: `isOpen_sum_iff`. -/
theorem sum_toMathlib :
    (sum : TopSpace (X ⊕ Y)).toMathlib =
      @instTopologicalSpaceSum X Y (‹TopSpace X›).toMathlib (‹TopSpace Y›).toMathlib := by
  -- Mathlib's open sets of `X ⊕ Y` are also those with both preimages open
  -- (`_root_.isOpen_sum_iff`).
  let _ := (‹TopSpace X›).toMathlib
  let _ := (‹TopSpace Y›).toMathlib
  apply TopologicalSpace.ext
  funext U
  apply propext
  change IsOpen (Sum.inl ⁻¹' U) ∧ IsOpen (Sum.inr ⁻¹' U) ↔ _
  rw [_root_.isOpen_sum_iff]
  exact Iff.rfl

end Coproduct

/-! ## Products of families (`thm:product-top` in full) -/

/-- With a base, `U` is open iff it contains a basic set about each of its points, as it is then
the union of the basic sets inside it. Mathlib:
`TopologicalSpace.IsTopologicalBasis.isOpen_iff`. -/
theorem IsBase.isOpen_iff [TopSpace X] {𝓑 : Set (Set X)} (h𝓑 : IsBase 𝓑) {U : Set X} :
    IsOpen U ↔ ∀ x ∈ U, ∃ B ∈ 𝓑, x ∈ B ∧ B ⊆ U := by
  -- `⇒` is `IsBase.exists_subset`. `⇐`: `U` is the union of the members of `𝓑` inside it, a
  -- union of open sets.
  refine ⟨fun hU x hx => h𝓑.exists_subset hU hx, fun h => ?_⟩
  have : U = ⋃₀ {B | B ∈ 𝓑 ∧ B ⊆ U} := by
    ext x
    constructor
    · intro hx
      obtain ⟨B, hB, hxB, hBU⟩ := h x hx
      exact ⟨B, ⟨hB, hBU⟩, hxB⟩
    · rintro ⟨B, ⟨_, hBU⟩, hxB⟩
      exact hBU hxB
  rw [this]
  exact isOpen_sUnion fun B hB => h𝓑.1 B hB.1

-- In the next sections `(Aᵢ)_{i ∈ ι}` is a family of spaces. (Lean: `A : ι → Type*` gives a
-- set `A i` for each index `i`, and `[∀ i, TopSpace (A i)]` a topology on each. A point of the
-- product `∏ᵢ Aᵢ`, written `∀ i, A i`, is a function `f` choosing a point `f i ∈ Aᵢ` for each `i`.)
section PiProduct
variable {ι : Type*} {A : ι → Type*} [∀ i, TopSpace (A i)]

variable (A) in
/-- The base of `thm:product-top`: the boxes `∏ᵢ Uᵢ` with every `Uᵢ` open and `Uᵢ = Aᵢ` for
all but finitely many `i`. Mathlib: no name (see `isOpen_pi_iff`).

Lean: `univ.pi U` is the box `∏ᵢ Uᵢ = {f | f i ∈ U i for every i}`, and
`{i | U i ≠ univ}.Finite` says that `Uᵢ ≠ Aᵢ` for only finitely many `i`. -/
def boxes : Set (Set (∀ i, A i)) :=
  {B | ∃ U : ∀ i, Set (A i), (∀ i, IsOpen (U i)) ∧ {i | U i ≠ univ}.Finite ∧ B = univ.pi U}

/-- `thm:product-top`: the product topology on `∏ᵢ Aᵢ`, generated by the boxes, a base by
`prop-1-10`: the whole product is a box, and the intersection of two boxes is the box of the
intersections, which constrains only the finitely many coordinates either one constrains.
Mathlib: `Pi.topologicalSpace` (see `pi_toMathlib`). -/
instance pi : TopSpace (∀ i, A i) :=
  TopSpace.ofBase (boxes A)
    -- They cover: `∏ᵢ Aᵢ` is itself a box, with no coordinate constrained.
    (eq_univ_of_forall fun _ =>
      ⟨univ.pi fun _ => univ, ⟨fun _ => univ, fun _ => isOpen_univ, by simp, rfl⟩, by simp⟩)
    -- The intersection of two boxes is the box `∏ᵢ (Uᵢ ∩ Vᵢ)`, whose factors are open.
    (by
      rintro _ ⟨U, hU, hUf, rfl⟩ _ ⟨V, hV, hVf, rfl⟩ f hf
      refine ⟨univ.pi fun i => U i ∩ V i, ⟨_, fun i => (hU i).inter (hV i), ?_, rfl⟩,
        by rwa [pi_inter_distrib], by rw [pi_inter_distrib]⟩
      -- It constrains only finitely many coordinates: if `Uᵢ ∩ Vᵢ ≠ Aᵢ`, then `Uᵢ ≠ Aᵢ` or
      -- `Vᵢ ≠ Aᵢ`, so `i` lies in the union of two finite sets.
      refine (hUf.union hVf).subset fun i hi => ?_
      by_contra h
      simp only [mem_union, mem_ofPred_eq, not_or, not_not] at h
      exact hi (by rw [h.1, h.2, univ_inter]))

/-- `thm:product-top`: the boxes are a base of the product (`prop-1-10`).
Mathlib: `isTopologicalBasis_pi`. -/
theorem isBase_boxes : IsBase (boxes A) := TopSpace.isBase_ofBase _ _ _

/-- `thm:product-top`: each projection is continuous, `πᵢ⁻¹(W)` being the box with `W` in
place `i` and `Aⱼ` elsewhere. Mathlib: `continuous_apply`.

Lean: `Function.update (fun _ => univ) i W` is the family equal to `W` at `i` and to `Aⱼ` at
every `j ≠ i`. -/
theorem continuous_apply (i : ι) : Continuous (fun f : ∀ j, A j => f i) := by
  -- (Lean: `classical` lets us split into the cases `j = i` and `j ≠ i`.)
  classical
  intro W hW
  refine isBase_boxes.1 _ ⟨Function.update (fun _ => univ) i W, fun j => ?_, ?_, ?_⟩
  · -- Each factor is open: `W` at `i`, `Aⱼ` elsewhere.
    by_cases hj : j = i
    · subst hj; rw [Function.update_self]; exact hW
    · rw [Function.update_of_ne hj]; exact isOpen_univ
  · -- Only the coordinate `i` is constrained.
    refine (finite_singleton i).subset fun j hj => ?_
    by_contra hji
    exact hj (Function.update_of_ne hji _ _)
  · -- And `πᵢ⁻¹(W)` is that box.
    exact eval_preimage

/-- `thm:product-top`, the universal property: `z ↦ (fᵢ(z))ᵢ` is continuous iff every `fᵢ` is.
The preimage of a box `∏ᵢ Uᵢ` is `⋂_{i ∈ F} fᵢ⁻¹(Uᵢ)`, `F` the finite set of `i` with
`Uᵢ ≠ Aᵢ`: a *finite* intersection of open sets. The map with components `fᵢ` is the only
one: a point of the product is determined by its coordinates (`funext`).
Mathlib: `continuous_pi_iff`. -/
theorem continuous_pi_iff {f : ∀ i, Z → A i} [TopSpace Z] :
    Continuous (fun z i => f i z) ↔ ∀ i, Continuous (f i) := by
  constructor
  · -- `fᵢ = πᵢ ∘ f` is a composite of continuous maps.
    intro h i
    exact (continuous_apply i).comp h
  · -- Conversely, it suffices to check preimages of boxes (`prop-1-19`).
    intro hf
    rw [continuous_iff_base isBase_boxes]
    rintro _ ⟨U, hU, hUf, rfl⟩
    -- Step 1. `f⁻¹(∏ᵢ Uᵢ) = ⋂_{i ∈ F} fᵢ⁻¹(Uᵢ)`, `F = {i | Uᵢ ≠ Aᵢ}`: for `i ∉ F` the condition
    -- `fᵢ(z) ∈ Aᵢ` is empty.
    have : (fun z i => f i z) ⁻¹' univ.pi U =
        ⋂₀ ((fun i => f i ⁻¹' U i) '' {i | U i ≠ univ}) := by
      ext z
      simp only [mem_preimage, mem_univ_pi, mem_sInter, mem_image, forall_exists_index, and_imp,
        forall_apply_eq_imp_iff₂]
      constructor
      · intro h i _; exact h i
      · intro h i
        by_cases hi : U i = univ
        · rw [hi]; trivial
        · exact h i hi
    -- Step 2. `F` is finite, so this is a finite intersection of open sets (week 1's
    -- `isOpen_sInter_of_finite`): exactly why all but finitely many `Uᵢ` must be `Aᵢ`.
    rw [this]
    exact isOpen_sInter_of_finite (hUf.image _) (by
      rintro _ ⟨i, -, rfl⟩
      exact hf i _ (hU i))

/-- **Bridge.** The product topology of a family is Mathlib's. Mathlib: `isOpen_pi_iff`. -/
theorem pi_toMathlib :
    (pi : TopSpace (∀ i, A i)).toMathlib =
      @Pi.topologicalSpace ι A (fun i => (‹∀ i, TopSpace (A i)› i).toMathlib) := by
  -- Both say: `W` is open iff it contains a box about each of its points. Mathlib's boxes are
  -- written `(F : Finset ι).pi u`, constraining the coordinates in a finite set `F`; the proof
  -- translates between the two ways of writing a box.
  classical
  let _ : ∀ i, TopologicalSpace (A i) := fun i => (‹∀ i, TopSpace (A i)› i).toMathlib
  apply TopologicalSpace.ext
  funext W
  apply propext
  change IsOpen W ↔ _
  rw [isBase_boxes.isOpen_iff, _root_.isOpen_pi_iff]
  constructor
  · rintro h f hf
    obtain ⟨_, ⟨U, hU, hUf, rfl⟩, hfB, hBW⟩ := h f hf
    refine ⟨hUf.toFinset, U, fun i _ => ⟨hU i, hfB i (mem_univ i)⟩, fun g hg => hBW ?_⟩
    intro i _
    by_cases hi : U i = univ
    · rw [hi]; trivial
    · exact hg i (by simpa using hi)
  · rintro h f hf
    obtain ⟨F, u, hu, hFW⟩ := h f hf
    refine ⟨univ.pi fun i => if i ∈ F then u i else univ,
      ⟨_, fun i => ?_, (F.finite_toSet).subset fun i hi => ?_, rfl⟩, fun i _ => ?_, ?_⟩
    · split_ifs with hi
      · exact (hu i hi).1
      · exact isOpen_univ
    · by_contra hiF
      exact hi (by simp [Finset.mem_coe.not.mp hiF])
    · dsimp only
      split_ifs with hi
      · exact (hu i hi).2
      · trivial
    · intro g hg
      apply hFW
      intro i hi
      have := hg i (mem_univ i)
      simpa [Finset.mem_coe.mp hi] using this

end PiProduct

/-! ## Coproducts of families (`prop:coproduct-top` in full) -/

/-- `prop:coproduct-top`: the disjoint union `∐ᵢ Aᵢ` of a family, in which `U` is open iff
`U ∩ Aᵢ` is open in each `Aᵢ`. Mathlib: `instTopologicalSpaceSigma` (see `sigma_toMathlib`).

Lean: a point of `Σ i, A i` is a pair `⟨i, a⟩` of an index `i` and a point `a ∈ Aᵢ`;
`Sigma.mk i : A i → Σ i, A i` is the inclusion `ιᵢ`, so `Sigma.mk i ⁻¹' U` is `U ∩ Aᵢ`. -/
instance sigma {ι : Type*} {A : ι → Type*} [∀ i, TopSpace (A i)] : TopSpace (Σ i, A i) where
  IsOpen U := ∀ i, IsOpen (Sigma.mk i ⁻¹' U)
  isOpen_univ i := by rw [preimage_univ]; exact isOpen_univ
  isOpen_inter U V hU hV i := by rw [preimage_inter]; exact IsOpen.inter (hU i) (hV i)
  isOpen_sUnion 𝒰 h i := by
    rw [preimage_sUnion]; exact isOpen_iUnion fun U => isOpen_iUnion fun hU => h U hU i

section SigmaCoproduct
variable {ι : Type*} {A : ι → Type*} [∀ i, TopSpace (A i)] [TopSpace Z]

/-- `prop:coproduct-top`: `U ⊆ ∐ᵢ Aᵢ` is open iff every `U ∩ Aᵢ` is: the definition.
Mathlib: `isOpen_sigma_iff`. -/
theorem isOpen_sigma_iff {U : Set (Σ i, A i)} : IsOpen U ↔ ∀ i, IsOpen (Sigma.mk i ⁻¹' U) :=
  Iff.rfl

/-- `prop:coproduct-top`: each inclusion `ιᵢ` is continuous. Mathlib: `continuous_sigmaMk`. -/
theorem continuous_sigmaMk (i : ι) : Continuous (Sigma.mk i : A i → Σ i, A i) :=
  fun _ hU => hU i

/-- `prop:coproduct-top`, the universal property: a map out of `∐ᵢ Aᵢ` is continuous iff each
of its restrictions `h ∘ ιᵢ` is. A family `fᵢ : Aᵢ → Z` determines one map `h` on the union,
`h⟨i, a⟩ = fᵢ(a)`, and it is the only one. Mathlib: `continuous_sigma_iff`. -/
theorem continuous_sigma_iff {h : (Σ i, A i) → Z} :
    Continuous h ↔ ∀ i, Continuous (fun a => h ⟨i, a⟩) :=
  -- `⇒`: composites with the continuous inclusions. `⇐`: for open `V ⊆ Z`,
  -- `h⁻¹(V) ∩ Aᵢ = (h ∘ ιᵢ)⁻¹(V)` is open for each `i`, which is what open in `∐ᵢ Aᵢ` means.
  ⟨fun hh i => hh.comp (continuous_sigmaMk i), fun hi V hV i => hi i V hV⟩

/-- **Bridge.** The disjoint union topology of a family is Mathlib's.
Mathlib: `isOpen_sigma_iff`. -/
theorem sigma_toMathlib :
    (sigma : TopSpace (Σ i, A i)).toMathlib =
      @instTopologicalSpaceSigma ι A (fun i => (‹∀ i, TopSpace (A i)› i).toMathlib) := by
  -- Mathlib's open sets of `∐ᵢ Aᵢ` are also those meeting every `Aᵢ` in an open set.
  let _ : ∀ i, TopologicalSpace (A i) := fun i => (‹∀ i, TopSpace (A i)› i).toMathlib
  apply TopologicalSpace.ext
  funext U
  apply propext
  change (∀ i, IsOpen (Sigma.mk i ⁻¹' U)) ↔ _
  rw [_root_.isOpen_sigma_iff]
  exact Iff.rfl

end SigmaCoproduct

end Course
