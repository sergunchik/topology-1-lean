/-
Machine-generated (Claude, Aristotle), no line written by a person. Copyleft: GPL-3.0-or-later.

# Week 4, continued: equalizers, limits, loops on the circle, simplices, the Hopf map

This file proves four groups of results of week 4 of the book.
(1) In `Top` the equalizer of `f, g : X → Y` is the subspace `E = {x | f(x) = g(x)}`, and the
coequalizer is the quotient of `Y` by the smallest equivalence relation with `f(x) ∼ g(x)`
(`def:equalizer`, `prop:equalizer-top`); from these and products, every diagram of spaces has a
limit, the subspace of the compatible families in `∏ᵢ Xᵢ`, and dually a colimit, a quotient of
`∐ᵢ Xᵢ` (`thm:limits-from-products`, `cor:top-complete`).
(2) A loop at `x` is the same as a pointed map `(S¹, 1) → (X, x)`, and path homotopy of loops is
pointed homotopy of maps, so `π₁(X, x) = [S¹, X]_*` (`prop:loops-circle`).
(3) The standard simplex `Δⁿ` is homeomorphic to the ball `Dⁿ`, by a homeomorphism carrying
`∂Δⁿ` onto the sphere `Sⁿ⁻¹`, for `n = 1, 2` (`def:simplex`, `prop:simplex-ball`).
(4) The Hopf map `η : S³ → S²` (`def:quaternions`, `def:hopf-map`, `prop:hopf-fibres`). A unit
quaternion `q` acts on the imaginary quaternions `ℝi + ℝj + ℝk = ℝ³` by the rotation
`x ↦ q x q̄`, which moves the unit sphere `S²` in itself; `η` follows the point `i`, sending `q`
to its image `η(q) = q i q̄`. `η` is onto, and `η(q) = η(q')` exactly when `q' = q λ` for a unit
complex number `λ = e^{iθ}`: the fibre through `q` is the circle `{q e^{iθ}}`, homeomorphic to
`S¹`, and `S²` is `S³` with each of these circles collapsed to a point.

Departures from the book:
* A diagram is given by its objects `X i`, `i : ι`, and its arrows `u a : X (s a) → X (t a)`,
  `a : α`, not as a functor; and the limits and colimits are built in `Top` only, by the proof
  of `thm:limits-from-products` (that theorem for an arbitrary category is not formalised).
* `prop:loops-circle`: the part on the pinch map `S¹ → S¹ ∨ S¹` is not done.
* `prop:simplex-ball` is done for `n = 1, 2` only, in coordinates; for `n = 2` the continuity of
  the inverse comes from an explicit bound instead of from compactness.
* A quaternion `q = z + jw`, `z = a + bi`, `w = c + di`, is the point `((a, b), (c, d))` of
  `ℝ⁴ = (ℝ × ℝ) × (ℝ × ℝ)`; Mathlib's quaternions `ℍ[ℝ]` are used only to check that the book's
  formula for `η` is `q i q̄` (`conj_i_eq`). `prop:s3-su2` and `prop:quaternion-rotations` are
  not formalised, so `η` is shown onto by an explicit preimage of each point.
* From Analysis I, through the bridges: a continuous map from a compact space to a Hausdorff one
  is closed; the continuity of real formulas and of `√`; the squeeze lemma. Each use says so.
  Mathlib's names below were checked against Lean and Mathlib v4.34.1.

New to Lean? Read `Course/README.md` first.
-/
import Course.Week06Circle
import Mathlib.Algebra.Quaternion
import Mathlib.Tactic.LinearCombination

-- Bookkeeping. `X`, `Y`, `W` below are spaces (types; `u v w …` are their "universe levels",
-- which you may ignore).
universe u v w u' v'

set_option warn.classDefReducibility false
set_option linter.unusedSectionVars false

namespace Course

open Set

/-! ## Equalizers and coequalizers (`def:equalizer`, `prop:equalizer-top`)

The equalizer of `f, g : X → Y` is the course's subspace (week 1), the coequalizer the course's
quotient (week 2). -/

section Equalizer
variable {X : Type u} {Y : Type v} [TopSpace X] [TopSpace Y] {W : Type w} [TopSpace W]

/-- The equalizer of `f, g : X → Y` in `Top`: the subset `E = {x ∈ X | f(x) = g(x)}`, a space
with the subspace topology, together with its inclusion `e : E → X`. `prop:equalizer-top`.
Mathlib: `CategoryTheory.Limits.equalizer` (abstract; no explicit construction in `TopCat` in
v4.34.1). -/
def equalizer (f g : X → Y) : Set X := {x | f x = g x}

variable {f g : X → Y}

/-- `f ∘ e = g ∘ e` for the inclusion `e : E → X`. `def:equalizer`.
Mathlib: `CategoryTheory.Limits.equalizer.condition`.

Lean: the inclusion `e` is `Subtype.val`, which forgets that a point lies in `E`. A point
`x : equalizer f g` is a pair of a point `x.1` of `X` and a proof `x.2` of `f(x.1) = g(x.1)`. -/
theorem equalizer_condition :
    f ∘ (Subtype.val : equalizer f g → X) = g ∘ (Subtype.val : equalizer f g → X) :=
  -- Two maps are equal if they agree at every `x` (`funext`), and at `x ∈ E` the equation
  -- `f(x) = g(x)` is the very condition `x.2` for `x` to lie in `E`.
  funext fun x => x.2

/-- If `f(h(w)) = g(h(w))` for every `w` (`hfg`), then `h : W → X` takes its values in `E`, so it
is a map `W → E`, `w ↦ h(w)`. `prop:equalizer-top`. Mathlib:
`CategoryTheory.Limits.equalizer.lift`. -/
def equalizer.lift (h : W → X) (hfg : ∀ w, f (h w) = g (h w)) : W → equalizer f g :=
  fun w => ⟨h w, hfg w⟩

/-- If `h : W → X` is continuous and `f ∘ h = g ∘ h`, then `h`, as a map `W → E`, is
continuous: a map into a subspace is continuous when it is continuous into the whole space
(`ex:initial-final`). `prop:equalizer-top`, existence. Mathlib: `Continuous.subtype_mk`. -/
theorem continuous_equalizer_lift {h : W → X} (hh : Continuous h)
    (hfg : ∀ w, f (h w) = g (h w)) : Continuous (equalizer.lift h hfg) :=
  continuous_into_subspace hh hfg

/-- **`prop:equalizer-top`**, the equalizer: every continuous `h : W → X` with `f ∘ h = g ∘ h`
factors through the inclusion `e : E → X` by exactly one continuous map `k : W → E`,
`e ∘ k = h`. Mathlib: `CategoryTheory.Limits.equalizer.lift`,
`CategoryTheory.Limits.equalizer.hom_ext`.

Lean: `∃! k, P k` says "there is exactly one `k` with `P k`". -/
theorem equalizer_universal {h : W → X} (hh : Continuous h) (hfg : f ∘ h = g ∘ h) :
    ∃! k : W → equalizer f g, Continuous k ∧ Subtype.val ∘ k = h := by
  -- Existence: `h` lands in `E`, so `k = h`, seen as a map into `E` (`equalizer.lift`), is
  -- continuous (`continuous_equalizer_lift`), and `e ∘ k = h` by definition (`rfl`).
  -- (Lean: `congrFun hfg w` evaluates `f ∘ h = g ∘ h` at `w`; `?_` is left for later.)
  refine ⟨equalizer.lift h (congrFun hfg), ⟨continuous_equalizer_lift hh _, rfl⟩, ?_⟩
  -- Uniqueness: let `k'` be another continuous map with `e ∘ k' = h` (`hk`; its continuity,
  -- the `-`, is not needed). At every `w`, `k'(w)` and `k(w) = h(w)` are the same point of `X`,
  -- hence the same point of `E`, because `e` is injective (`Subtype.ext`).
  rintro k ⟨-, hk⟩
  funext w
  exact Subtype.ext (congrFun hk w)

/-- The relation `a R b` on `Y`: `a = f(x)` and `b = g(x)` for some `x ∈ X`. It is not yet an
equivalence relation. `prop:equalizer-top`. -/
def coequalizerRel (f g : X → Y) (a b : Y) : Prop := ∃ x, a = f x ∧ b = g x

/-- `∼`, the smallest equivalence relation on `Y` with `f(x) ∼ g(x)` for all `x ∈ X`: `a ∼ b`
when a finite chain `a = y₀, y₁, …, yₙ = b` links them, each step `yₖ R yₖ₊₁` or
`yₖ₊₁ R yₖ`. `prop:equalizer-top`. Mathlib: `Relation.EqvGen.setoid`.

Lean: a `Setoid Y` is an equivalence relation on `Y`, and `Relation.EqvGen R` is the
equivalence relation generated by `R`. -/
def coequalizerSetoid (f g : X → Y) : Setoid Y := Relation.EqvGen.setoid (coequalizerRel f g)

/-- The coequalizer of `f, g` in `Top`: the quotient space `Y/∼` (`def:quotient`).
`prop:equalizer-top`. Mathlib: `CategoryTheory.Limits.coequalizer`, with
`TopCat.coequalizer_isOpen_iff` (its topology is the quotient topology).

Lean: `abbrev` is a `def` that Lean unfolds freely; `Quotient s` is the set of classes of the
equivalence relation `s`, with the quotient topology of week 2. -/
abbrev Coequalizer (f g : X → Y) : Type v := Quotient (coequalizerSetoid f g)

/-- `q ∘ f = q ∘ g` for the quotient map `q : Y → Y/∼`, `q(y) = [y]`: `[f(x)] = [g(x)]` because
`f(x) ∼ g(x)`. `def:equalizer`. Mathlib: `CategoryTheory.Limits.coequalizer.condition`.

Lean: `Quotient.mk s y` is the class `[y]`. -/
theorem coequalizer_condition :
    Quotient.mk (coequalizerSetoid f g) ∘ f = Quotient.mk (coequalizerSetoid f g) ∘ g :=
  -- At each `x`: `f(x) R g(x)` with the witness `x` (`⟨x, rfl, rfl⟩`), so `f(x) ∼ g(x)`
  -- (`EqvGen.rel`), and related points have equal classes (`Quotient.sound`).
  funext fun x => Quotient.sound (Relation.EqvGen.rel _ _ ⟨x, rfl, rfl⟩)

/-- If `k ∘ f = k ∘ g` (`hk`), then `k` is constant on the classes of `∼`: `a ∼ b` implies
`k(a) = k(b)`. `prop:equalizer-top` (in its proof: "constant on the classes of the relation").
Mathlib: `Relation.EqvGen.rec`. -/
theorem coequalizer_const {Z : Type w} {k : Y → Z} (hk : k ∘ f = k ∘ g) :
    ∀ a b, (coequalizerSetoid f g).r a b → k a = k b := by
  -- By induction on how `a ∼ b` was obtained. There are four ways (Lean: `induction … with`
  -- takes them one by one, `ih` being the statement for the smaller steps).
  intro a b hab
  induction hab with
  -- A generating step `a = f(x)`, `b = g(x)`: then `k(f(x)) = k(g(x))` is `hk` at `x`.
  | rel a b h => obtain ⟨x, rfl, rfl⟩ := h; exact congrFun hk x
  -- Reflexivity `a ∼ a`: `k(a) = k(a)`.
  | refl => rfl
  -- Symmetry: from `k(a) = k(b)`, `k(b) = k(a)`.
  | symm _ _ _ ih => exact ih.symm
  -- Transitivity: from `k(a) = k(b)` and `k(b) = k(c)`, `k(a) = k(c)`.
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- **`prop:equalizer-top`**, the coequalizer: every continuous `k : Y → Z` with
`k ∘ f = k ∘ g` factors through `q : Y → Y/∼` by exactly one continuous map `k̄`, `k̄ ∘ q = k`.
Mathlib: `CategoryTheory.Limits.coequalizer.desc`, `CategoryTheory.Limits.coequalizer.hom_ext`.
-/
theorem coequalizer_universal {Z : Type w} [TopSpace Z] {k : Y → Z} (hk : Continuous k)
    (hfg : k ∘ f = k ∘ g) :
    ∃! k' : Coequalizer f g → Z, Continuous k' ∧ k' ∘ Quotient.mk _ = k := by
  -- Existence: `k` is constant on the classes (`coequalizer_const`), so it induces
  -- `k̄ : Y/∼ → Z`, `k̄[y] = k(y)` (Lean: `Quotient.lift k _`), continuous by
  -- `prop:quotient-univ` (`continuous_quotient_lift`); and `k̄ ∘ q = k` by definition.
  refine ⟨Quotient.lift k (coequalizer_const hfg),
    ⟨continuous_quotient_lift hk _, rfl⟩, ?_⟩
  -- Uniqueness: a map `k'` with `k' ∘ q = k` is `k̄`, because `q` is onto
  -- (`prop:quotient-univ`, `quotient_lift_unique`).
  rintro k' ⟨-, hk'⟩
  exact quotient_lift_unique _ k' hk'

end Equalizer

/-! ## Limits from products and equalizers (`thm:limits-from-products`, `cor:top-complete`)

A diagram has objects `X i`, `i : ι`, and arrows `u a : X (s a) → X (t a)`, `a : α`
(`s` for source, `t` for target), each continuous. The book's proof of
`thm:limits-from-products`, in `Top`: put `P = ∏ᵢ Xᵢ`, `Q = ∏_a X_{t(a)}`, two maps `a, b : P → Q`,
and the limit `L` is their equalizer.

Lean: `∀ i, X i` is the product `∏ᵢ Xᵢ`: an element `x` is a family, with one `x i ∈ X i` for
each `i`. `Σ i, X i` is the disjoint union `∐ᵢ Xᵢ`: an element is a pair `⟨i, x⟩` of an index
`i` and a point `x ∈ X i`. -/

section Limits
variable {ι : Type u} {α : Type v} (X : ι → Type u') [∀ i, TopSpace (X i)]
  (s t : α → ι) (u : ∀ a, X (s a) → X (t a))

/-- The map `a : P → Q` with `π_a ∘ a = π_{t(a)}`: it reads off the target of each arrow,
`a(x)_a = x_{t(a)}`. `thm:limits-from-products`. -/
def limA (x : ∀ i, X i) : ∀ a, X (t a) := fun a => x (t a)

/-- The map `b : P → Q` with `π_a ∘ b = u_a ∘ π_{s(a)}`: it reads off the source of each arrow
and applies the arrow, `b(x)_a = u_a(x_{s(a)})`. `thm:limits-from-products`. -/
def limB (x : ∀ i, X i) : ∀ a, X (t a) := fun a => u a (x (s a))

/-- `a : P → Q` is continuous: its components are projections, and a map into a product is
continuous when its components are (`thm:product-top`). `thm:limits-from-products`. -/
theorem continuous_limA : Continuous (limA X t) :=
  continuous_pi_iff.mpr fun a => continuous_apply (t a)

variable {X s t u}

/-- If every arrow `u_a` is continuous (`hu`), then `b : P → Q` is continuous: its components
`u_a ∘ π_{s(a)}` are (`thm:product-top`). `thm:limits-from-products`. -/
theorem continuous_limB (hu : ∀ a, Continuous (u a)) : Continuous (limB X s t u) :=
  continuous_pi_iff.mpr fun a => (hu a).comp (continuous_apply (s a))

variable (X s t u)

/-- The limit `L` of the diagram: the equalizer of `a, b : P → Q` (`prop:equalizer-top`), a
subspace of the course's product `∏ᵢ Xᵢ`. `thm:limits-from-products`, `cor:top-complete`.
Mathlib: `TopCat.limitCone` (on `{u : ∀ j, F.obj j // ∀ {i j} f, F.map f (u i) = u j}`),
`CategoryTheory.Limits.limitConeOfEqualizerAndProduct`. -/
def limit : Set (∀ i, X i) := equalizer (limA X t) (limB X s t u)

/-- The limit is the set of compatible families: `x ∈ L` if and only if `u_a(x_{s(a)}) = x_{t(a)}`
for every arrow `a`. `cor:top-complete`. Mathlib: `TopCat.limitCone`'s carrier. -/
theorem mem_limit_iff {x : ∀ i, X i} : x ∈ limit X s t u ↔ ∀ a, u a (x (s a)) = x (t a) := by
  -- `x ∈ L` means `a(x) = b(x)` in `Q`, and two families are equal when they agree in every
  -- component `a`: `x_{t(a)} = u_a(x_{s(a)})`.
  change (fun a => x (t a)) = (fun a => u a (x (s a))) ↔ _
  exact ⟨fun h a => (congrFun h a).symm, fun h => funext fun a => (h a).symm⟩

variable {X s t u}

/-- The cone's maps `p_i = π_i ∘ e : L → X_i`, `p_i(x) = x_i`. `thm:limits-from-products`.
Mathlib: `CategoryTheory.Limits.limit.π`. -/
def limit.proj (i : ι) (x : limit X s t u) : X i := x.1 i

/-- Each `p_i` is continuous: a projection (`thm:product-top`) after the inclusion.
`thm:limits-from-products`. -/
theorem continuous_limit_proj (i : ι) : Continuous (limit.proj (u := u) i) :=
  (continuous_apply i).comp continuous_subtype_val

/-- The maps `p_i` form a cone: `u_a ∘ p_{s(a)} = p_{t(a)}` for every arrow `a`.
`thm:limits-from-products` ("A cone"). Mathlib: `CategoryTheory.Limits.limit.w`. -/
theorem limit_cone (a : α) : u a ∘ limit.proj (s a) = limit.proj (u := u) (t a) :=
  -- At a point `x ∈ L`, this is the compatibility `u_a(x_{s(a)}) = x_{t(a)}` (`mem_limit_iff`).
  funext fun x => ((mem_limit_iff X s t u).mp x.2) a

/-- **`thm:limits-from-products`**, **`cor:top-complete`**: every cone factors uniquely through
the limit. A cone `(W, (q_i))` is a family of continuous `q_i : W → X_i` (`hq`) with
`u_a ∘ q_{s(a)} = q_{t(a)}` for every arrow (`hcone`); there is exactly one continuous
`w : W → L` with `p_i ∘ w = q_i` for every `i`. (The continuity of the arrows makes `b` a
morphism, `continuous_limB`; the factorisation itself does not use it.)
Mathlib: `CategoryTheory.Limits.limit.lift`, `CategoryTheory.Limits.limit.hom_ext`. -/
theorem limit_universal {W : Type w} [TopSpace W]
    {q : ∀ i, W → X i} (hq : ∀ i, Continuous (q i)) (hcone : ∀ a, u a ∘ q (s a) = q (t a)) :
    ∃! w : W → limit X s t u, Continuous w ∧ ∀ i, limit.proj i ∘ w = q i := by
  -- Step 1. Let `q : W → P` be the map with `π_i ∘ q = q_i`, `q(x) = (q_i(x))ᵢ`; it is
  -- continuous because its components are (`thm:product-top`).
  have hQ : Continuous (fun x i => q i x) := continuous_pi_iff.mpr hq
  -- Step 2. `a ∘ q = b ∘ q`, by uniqueness in `Q`: for each arrow `a`, the components are
  -- `q_{t(a)}(x)` and `u_a(q_{s(a)}(x))`, equal because the `q_i` form a cone.
  have hab : limA X t ∘ (fun x i => q i x) = limB X s t u ∘ (fun x i => q i x) :=
    funext fun x => funext fun a => (congrFun (hcone a) x).symm
  -- Step 3. So `q` factors through the equalizer `e : L → P`: `q = e ∘ w` for exactly one
  -- continuous `w` (`equalizer_universal`), and `p_i ∘ w = π_i ∘ e ∘ w = π_i ∘ q = q_i`.
  obtain ⟨w, ⟨hw, hwq⟩, huniq⟩ := equalizer_universal hQ hab
  refine ⟨w, ⟨hw, fun i => funext fun x => congrFun (congrFun hwq x) i⟩, ?_⟩
  -- Step 4. Uniqueness. If also `p_i ∘ w' = q_i` for every `i`, then `π_i ∘ e ∘ w' = q_i` for
  -- every `i`, so `e ∘ w' = q` by uniqueness in `P`; and `q` factors through the equalizer only
  -- once, so `w' = w`.
  rintro w' ⟨hw', hw'q⟩
  refine huniq w' ⟨hw', funext fun x => funext fun i => ?_⟩
  exact congrFun (hw'q i) x

/-! The colimit, dually: the quotient of the coproduct `∐ᵢ Xᵢ` by the smallest equivalence
relation with `(s(a), x) ∼ (t(a), u_a(x))`. -/

variable (X s t u)

/-- The relation `(s(a), x) R (t(a), u_a(x))` on `∐ᵢ Xᵢ`: a point `x ∈ X_{s(a)}` is related to its
image under the arrow `a`. `cor:top-complete`. -/
def colimitRel (y z : Σ i, X i) : Prop := ∃ a x, y = ⟨s a, x⟩ ∧ z = ⟨t a, u a x⟩

/-- The colimit: the quotient of `∐ᵢ Xᵢ` (`prop:coproduct-top`) by the smallest equivalence
relation `∼` containing `colimitRel`. `cor:top-complete`.
Mathlib: `CategoryTheory.Limits.colimit`, with `TopCat.colimit_isOpen_iff`. -/
abbrev Colimit : Type (max u u') := Quotient (Relation.EqvGen.setoid (colimitRel X s t u))

variable {X s t u}

/-- The cocone's maps `ι_i : X_i → colim`, `x ↦ [(i, x)]`. `cor:top-complete`.
Mathlib: `CategoryTheory.Limits.colimit.ι`. -/
def colimit.inj (i : ι) (x : X i) : Colimit X s t u := Quotient.mk _ ⟨i, x⟩

/-- Each `ι_i : X_i → colim` is continuous: the inclusion `X_i → ∐ᵢ Xᵢ` (`prop:coproduct-top`)
followed by the quotient map (`prop:quotient-univ`). `cor:top-complete`. -/
theorem continuous_colimit_inj (i : ι) : Continuous (colimit.inj (u := u) i) :=
  continuous_quotient_mk.comp (continuous_sigmaMk i)

/-- The maps `ι_i` form a cocone: `ι_{t(a)} ∘ u_a = ι_{s(a)}` for every arrow `a`.
`cor:top-complete`. Mathlib: `CategoryTheory.Limits.colimit.w`. -/
theorem colimit_cocone (a : α) : colimit.inj (t a) ∘ u a = colimit.inj (u := u) (s a) :=
  -- At `x ∈ X_{s(a)}`: `(s(a), x) R (t(a), u_a(x))`, so the two points have the same class.
  funext fun x => Quotient.sound
    (Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ ⟨a, x, rfl, rfl⟩))

/-- **`cor:top-complete`**, the colimit (the dual half of `thm:limits-from-products`): every
cocone factors uniquely through the colimit. A cocone `(W, (q_i))` is a family of continuous
`q_i : X_i → W` (`hq`) with `q_{t(a)} ∘ u_a = q_{s(a)}` for every arrow (`hcocone`); there is
exactly one continuous `w : colim → W` with `w ∘ ι_i = q_i` for every `i`.
Mathlib: `CategoryTheory.Limits.colimit.desc`, `CategoryTheory.Limits.colimit.hom_ext`. -/
theorem colimit_universal {W : Type w} [TopSpace W] {q : ∀ i, X i → W}
    (hq : ∀ i, Continuous (q i)) (hcocone : ∀ a, q (t a) ∘ u a = q (s a)) :
    ∃! w : Colimit X s t u → W, Continuous w ∧ ∀ i, w ∘ colimit.inj i = q i := by
  -- Step 1. The `q_i` are one map `Q : ∐ᵢ Xᵢ → W`, `Q(i, x) = q_i(x)`, continuous because each
  -- of its restrictions is (`prop:coproduct-top`).
  let Q : (Σ i, X i) → W := fun y => q y.1 y.2
  have hQ : Continuous Q := continuous_sigma_iff.mpr hq
  -- Step 2. `Q` is constant on the classes of `∼`: by induction on how `y ∼ z` was obtained,
  -- as in `coequalizer_const`. For a generating step `y = (s(a), x)`, `z = (t(a), u_a(x))`,
  -- `Q(y) = q_{s(a)}(x) = q_{t(a)}(u_a(x)) = Q(z)` because the `q_i` form a cocone.
  have hconst : ∀ y z, (Relation.EqvGen.setoid (colimitRel X s t u)).r y z → Q y = Q z := by
    intro y z h
    induction h with
    | rel y z h =>
      obtain ⟨a, x, rfl, rfl⟩ := h
      exact (congrFun (hcocone a) x).symm
    | refl => rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  -- Step 3. So `Q` induces a continuous `w : colim → W`, `w[y] = Q(y)` (`prop:quotient-univ`),
  -- and `w ∘ ι_i = q_i` by definition.
  refine ⟨Quotient.lift Q hconst, ⟨continuous_quotient_lift hQ _, fun i => rfl⟩, ?_⟩
  -- Step 4. Uniqueness: a map `w'` with `w' ∘ ι_i = q_i` for all `i` has `w'[y] = Q(y)` for
  -- every `y = (i, x)`, so it is the map induced by `Q`, unique because the quotient map is
  -- onto (`quotient_lift_unique`).
  rintro w ⟨-, hw⟩
  refine quotient_lift_unique _ w (funext fun y => ?_)
  exact congrFun (hw y.1) y.2

end Limits


/-! ## Loops are maps from the circle (`prop:loops-circle`)

The book's proof: `q : I → S¹`, `q(s) = e^{2πis}`, is a quotient map identifying `0` with `1`,
so a loop factors uniquely through it; and `q × id : I × I → S¹ × I` is a quotient map too,
being a continuous surjection from a compact space to a Hausdorff one, hence closed. So
homotopies of loops descend to the circle as well.

What comes from Analysis I, through the bridges `I_toMathlib`, `S1_toMathlib`,
`prod_toMathlib`: a continuous map from a compact space (`I`, `I × I`) to a Hausdorff one
(`S¹`, `S¹ × I`) is closed (Analysis I 5.3; Mathlib: `Continuous.isClosedMap`); and the
properties of `p(t) = e^{2πit}` and of the integer part `⌊a⌋` from week 6. -/

noncomputable section Loops
open Real
variable {X : Type u} [TopSpace X] {x : X}

/-- **Bridge.** A map that is closed for Mathlib's topologies is closed for the course's. -/
theorem isClosedMap_of_mathlib_eq {A : Type v} {B : Type w} [tA : TopSpace A] [tB : TopSpace B]
    {mA : TopologicalSpace A} {mB : TopologicalSpace B} (hA : tA.toMathlib = mA)
    (hB : tB.toMathlib = mB) {f : A → B} (hf : @_root_.IsClosedMap A B mA mB f) :
    IsClosedMap f := by
  -- Replace Mathlib's topologies by the course's, seen in Mathlib (Lean: `subst`).
  subst hA hB
  -- A course-closed `C` is Mathlib-closed (the bridge `isClosed_iff_mathlib`), so `f(C)` is
  -- Mathlib-closed by `hf`, hence course-closed.
  intro C hC
  exact (isClosed_iff_mathlib _).mpr (hf C ((isClosed_iff_mathlib C).mp hC))

/-- A continuous closed surjection `q : A → B` is a quotient map: a map `φ : B → X` is continuous
as soon as `φ ∘ q` is. `prop:loops-circle` (in its proof: "hence closed, hence a quotient map").
Mathlib: `IsClosedMap.isQuotientMap`. -/
theorem continuous_of_closedMap_comp {A : Type v} {B : Type w} [TopSpace A] [TopSpace B]
    {q : A → B} (hq : IsClosedMap q) (hs : Function.Surjective q) {φ : B → X}
    (hφ : Continuous (φ ∘ q)) : Continuous φ := by
  -- We check continuity by closed sets (Analysis I 4.21, `continuous_iff_isClosed`): let
  -- `C ⊆ X` be closed.
  rw [continuous_iff_isClosed] at hφ ⊢
  intro C hC
  -- Since `q` is onto, `φ⁻¹(C) = q(q⁻¹(φ⁻¹(C))) = q((φ ∘ q)⁻¹(C))`.
  have e : φ ⁻¹' C = q '' ((φ ∘ q) ⁻¹' C) := by
    rw [preimage_comp, image_preimage_eq _ hs]
  -- And `(φ ∘ q)⁻¹(C)` is closed because `φ ∘ q` is continuous, so its image under the closed
  -- map `q` is closed.
  rw [e]
  exact hq _ (hφ C hC)

/-- `q : I → S¹`, `q(s) = e^{2πis} = p(s)`: the map of `prop:loops-circle`, which wraps `I`
once round the circle. Mathlib: `Circle.exp` restricted to `[0, 2π]`.

Lean: `s : I` is a real number with a proof that it lies in `[0, 1]`; `p s` uses it as a real
number. -/
def qI (s : I) : S1 := p s

/-- `q` is continuous: `p` is (week 6), and so is the inclusion `I → ℝ`. -/
theorem continuous_qI : Continuous qI := continuous_p.comp continuous_subtype_val

/-- `q(0) = e⁰ = 1`. -/
@[simp] theorem qI_zero : qI 0 = 1 := by simp [qI]

/-- `q(1) = e^{2πi} = 1` (week 6's `p_int`: `p(n) = 1` for an integer `n`). -/
@[simp] theorem qI_one : qI 1 = 1 := by
  have := p_int 1
  simpa [qI] using this

/-- `q` is onto. -/
theorem qI_surjective : Function.Surjective qI := by
  -- Every `z ∈ S¹` is `p(a)` for some real `a` (`p_surjective`, week 6).
  intro z
  obtain ⟨a, rfl⟩ := p_surjective z
  -- Take `s = a - ⌊a⌋`, which lies in `[0, 1)` because `⌊a⌋ ≤ a < ⌊a⌋ + 1` (Analysis I) …
  refine ⟨⟨a - ⌊a⌋, by linarith [Int.floor_le a], by linarith [Int.lt_floor_add_one a]⟩, ?_⟩
  -- … and `p(a - ⌊a⌋) = p(a)` because `p` has period `1` (`p_add_int`, week 6).
  change p (a - ⌊a⌋) = p a
  rw [sub_eq_add_neg, ← Int.cast_neg]
  exact p_add_int a _

/-- `q` identifies `0` with `1` and nothing else: if `q(s) = q(s')`, then `s = s'`, or
`s = 0, s' = 1`, or `s = 1, s' = 0`. -/
theorem qI_eq {s s' : I} (h : qI s = qI s') :
    s = s' ∨ (s = 0 ∧ s' = 1) ∨ (s = 1 ∧ s' = 0) := by
  -- `p(s) = p(s')` means `s' - s = n` for an integer `n` (`p_eq_iff`, week 6).
  obtain ⟨n, hn⟩ := p_eq_iff.mp h
  -- Since `s, s' ∈ [0, 1]`, `-1 ≤ n ≤ 1` (first as real numbers, then as integers).
  have h1 : (n : ℝ) ≤ 1 := by linarith [s.2.1, s'.2.2]
  have h2 : (-1 : ℝ) ≤ n := by linarith [s.2.2, s'.2.1]
  have h1' : n ≤ 1 := by exact_mod_cast h1
  have h2' : -1 ≤ n := by exact_mod_cast h2
  have hs := s.2
  have hs' := s'.2
  simp only [mem_Icc] at hs hs'
  -- Three cases (Lean: `interval_cases n` tries `n = -1, 0, 1`). Two points of `I` are equal
  -- when they are equal as real numbers (`Subtype.ext`).
  interval_cases n
  -- `n = -1`: `s' = s - 1`, and with `s ≤ 1`, `s' ≥ 0` this forces `s = 1`, `s' = 0`.
  · right; right
    push_cast at hn
    exact ⟨Subtype.ext (by rw [Set.Icc.coe_one]; linarith),
      Subtype.ext (by rw [Set.Icc.coe_zero]; linarith)⟩
  -- `n = 0`: `s' = s`.
  · left; apply Subtype.ext; push_cast at hn; linarith
  -- `n = 1`: `s' = s + 1`, which forces `s = 0`, `s' = 1`.
  · right; left
    push_cast at hn
    exact ⟨Subtype.ext (by rw [Set.Icc.coe_zero]; linarith),
      Subtype.ext (by rw [Set.Icc.coe_one]; linarith)⟩

/-- `q` is closed: a continuous map from the compact `I` to the Hausdorff `S¹` (Analysis I 5.3,
through the bridges `I_toMathlib`, `S1_toMathlib`). `prop:loops-circle`.
Mathlib: `Continuous.isClosedMap`. -/
theorem isClosedMap_qI : IsClosedMap qI :=
  isClosedMap_of_mathlib_eq I_toMathlib S1_toMathlib
    (mathlib_continuous_of_eq I_toMathlib S1_toMathlib continuous_qI).isClosedMap

/-- **Bridge.** The course topology of the cylinder `S¹ × I` is Mathlib's. -/
theorem S1I_toMathlib :
    (prod : TopSpace (S1 × I)).toMathlib = (inferInstance : TopologicalSpace (S1 × I)) := by
  rw [prod_toMathlib, S1_toMathlib, I_toMathlib]

/-- `q × id : I × I → S¹ × I`, `(s, t) ↦ (q(s), t)`. `prop:loops-circle`. -/
def qII (w : I × I) : S1 × I := (qI w.1, w.2)

/-- `q × id` is continuous: both components are (`thm:product-top`). -/
theorem continuous_qII : Continuous qII :=
  continuous_prodMk.mpr ⟨continuous_qI.comp continuous_fst, continuous_snd⟩

/-- `q × id` is onto, because `q` is: `(z, t) = (q(s), t)` for `s` with `q(s) = z`. -/
theorem qII_surjective : Function.Surjective qII := by
  rintro ⟨z, t⟩
  obtain ⟨s, rfl⟩ := qI_surjective z
  exact ⟨(s, t), rfl⟩

/-- `q × id` is closed: a continuous map from the compact `I × I` to the Hausdorff `S¹ × I`
(Analysis I 5.3, through the bridges). `prop:loops-circle`. Mathlib: `Continuous.isClosedMap`.
-/
theorem isClosedMap_qII : IsClosedMap qII :=
  isClosedMap_of_mathlib_eq II_toMathlib S1I_toMathlib
    (mathlib_continuous_of_eq II_toMathlib S1I_toMathlib continuous_qII).isClosedMap

/-- A map `g : I → X` with `g(0) = g(1)` descends to `ḡ : S¹ → X`, `ḡ(q(s)) = g(s)`.
`prop:loops-circle`.

Lean: `Classical.choose h` picks, by the axiom of choice, some witness of an existence statement
`h`; here some `s ∈ I` with `q(s) = z`, and `ḡ(z) = g(s)`. -/
def descend (g : I → X) (z : S1) : X := g (Classical.choose (qI_surjective z))

/-- If `g(0) = g(1)` (`hg`), then `ḡ(q(s)) = g(s)`. -/
theorem descend_qI {g : I → X} (hg : g 0 = g 1) (s : I) : descend g (qI s) = g s := by
  -- `ḡ(q(s)) = g(s')` for the chosen `s'` with `q(s') = q(s)`. By `qI_eq`, either `s' = s`, or
  -- `{s', s} = {0, 1}` and then `g(s') = g(s)` because `g(0) = g(1)`.
  have h := Classical.choose_spec (qI_surjective (qI s))
  rcases qI_eq h with h | ⟨h0, h1⟩ | ⟨h1, h0⟩
  · rw [descend, h]
  · rw [descend, h0, h1, hg]
  · rw [descend, h1, h0, hg]

/-- If `g : I → X` is continuous and `g(0) = g(1)`, then `ḡ : S¹ → X` is continuous, because `q`
is a quotient map (`continuous_of_closedMap_comp`) and `ḡ ∘ q = g` is continuous.
`prop:loops-circle`. -/
theorem continuous_descend {g : I → X} (hg : Continuous g) (h01 : g 0 = g 1) :
    Continuous (descend g) :=
  continuous_of_closedMap_comp isClosedMap_qI qI_surjective
    (by rw [show descend g ∘ qI = g from funext (descend_qI h01)]; exact hg)

/-- A map `G : I × I → X` with `G(0, t) = G(1, t)` for all `t` descends to
`Ḡ : S¹ × I → X`, `Ḡ(q(s), t) = G(s, t)`. `prop:loops-circle`. -/
def descend₂ (G : I × I → X) (w : S1 × I) : X := G (Classical.choose (qI_surjective w.1), w.2)

/-- If `G(0, t) = G(1, t)` for all `t` (`hG`), then `Ḡ(q(s), t) = G(s, t)`. -/
theorem descend₂_qII {G : I × I → X} (hG : ∀ t, G (0, t) = G (1, t)) (w : I × I) :
    descend₂ G (qII w) = G w := by
  -- As in `descend_qI`: `Ḡ(q(s), t) = G(s', t)` for the chosen `s'` with `q(s') = q(s)`, and
  -- either `s' = s` or `{s', s} = {0, 1}`.
  obtain ⟨s, t⟩ := w
  have h := Classical.choose_spec (qI_surjective (qI s))
  change G (Classical.choose (qI_surjective (qI s)), t) = G (s, t)
  rcases qI_eq h with h | ⟨h0, h1⟩ | ⟨h1, h0⟩
  · rw [h]
  · rw [h0, h1, hG]
  · rw [h1, h0, hG]

/-- If `G` is continuous and `G(0, t) = G(1, t)`, then `Ḡ : S¹ × I → X` is continuous, because
`q × id` is a quotient map (closed and onto). `prop:loops-circle`. -/
theorem continuous_descend₂ {G : I × I → X} (hG : Continuous G) (h01 : ∀ t, G (0, t) = G (1, t)) :
    Continuous (descend₂ G) :=
  continuous_of_closedMap_comp isClosedMap_qII qII_surjective
    (by rw [show descend₂ G ∘ qII = G from funext (descend₂_qII h01)]; exact hG)

variable (x) in
/-- The pointed maps `(S¹, 1) → (X, x)`: the continuous `φ : S¹ → X` with `φ(1) = x`.
`prop:loops-circle`. Mathlib: none named (a `ContinuousMap` with a base point condition).

Lean: `variable (x) in` makes the base point `x` an explicit argument here, `PointedMap x`. A
pointed map `φ` is a pair: the map `φ.1` and the proof `φ.2` of the two conditions, so `φ.2.1`
says `φ.1` is continuous and `φ.2.2` that `φ.1 1 = x`. -/
def PointedMap : Type u := {φ : S1 → X // Continuous φ ∧ φ 1 = x}

/-- The loop `φ ∘ q` at `x` of a pointed map `φ`. `prop:loops-circle`. -/
def PointedMap.loop (φ : PointedMap x) : Path x x where
  -- `φ ∘ q` is continuous as a composite, and starts and ends at `φ(q(0)) = φ(q(1)) = φ(1) = x`.
  toFun := φ.1 ∘ qI
  continuous_toFun := φ.2.1.comp continuous_qI
  source' := by simp [φ.2.2]
  target' := by simp [φ.2.2]

/-- The pointed map `γ̄ : (S¹, 1) → (X, x)` of a loop `γ`, through which `γ` factors:
`γ̄ ∘ q = γ`. `prop:loops-circle`. -/
def Path.toPointedMap (γ : Path x x) : PointedMap x :=
  -- `γ̄` is continuous because `γ(0) = γ(1) = x` (`continuous_descend`), and
  -- `γ̄(1) = γ̄(q(0)) = γ(0) = x`.
  ⟨descend γ, continuous_descend γ.continuous (by simp),
    by rw [← qI_zero, descend_qI (by simp)]; exact γ.source⟩

/-- **`prop:loops-circle`**, first part: loops at `x` correspond to pointed maps
`(S¹, 1) → (X, x)`, by `φ ↦ φ ∘ q`; a loop factors uniquely through the quotient map
`q : I → S¹` identifying `0` with `1`. Mathlib: none (in v4.34.1 `FundamentalGroup` is built
from `Path`, with no comparison to maps out of the circle).

Lean: `A ≃ B` is a bijection, given by a map `toFun`, a map `invFun` back, and proofs
`left_inv`, `right_inv` that the two composites are the identity. -/
def loopEquiv : PointedMap x ≃ Path x x where
  toFun := PointedMap.loop
  invFun := Path.toPointedMap
  -- The descent of `φ ∘ q` is `φ`: at a point `z = q(s)` of the circle (`q` is onto), both
  -- are `φ(q(s))` (`descend_qI`).
  left_inv φ := by
    apply Subtype.ext
    funext z
    obtain ⟨s, rfl⟩ := qI_surjective z
    exact descend_qI (g := φ.1 ∘ qI) (by simp [φ.2.2]) s
  -- `γ̄ ∘ q = γ`: at every `s`, `γ̄(q(s)) = γ(s)` (`descend_qI`).
  right_inv γ := Path.ext fun s => descend_qI (g := γ) (by simp) s

/-- A pointed homotopy `φ ≃ ψ` of pointed maps `(S¹, 1) → (X, x)`: a homotopy `H : S¹ × I → X`
from `φ` to `ψ` (`def:homotopy`) that keeps the base point at `x`, `H(1, t) = x` for all `t`.
`prop:loops-circle`. Mathlib: `ContinuousMap.HomotopyRel` with `{1}`. -/
def PointedHomotopic (φ ψ : PointedMap x) : Prop :=
  ∃ H : Homotopy φ.1 ψ.1, ∀ t, H.toFun (1, t) = x

/-- **`prop:loops-circle`**, second part: the loops `φ ∘ q` and `ψ ∘ q` are path homotopic if
and only if `φ` and `ψ` are pointed homotopic. Mathlib: none. -/
theorem homotopic_iff_pointedHomotopic (φ ψ : PointedMap x) :
    Path.Homotopic φ.loop ψ.loop ↔ PointedHomotopic φ ψ := by
  constructor
  -- (⇒) Let `F : I × I → X` be a path homotopy from `φ ∘ q` to `ψ ∘ q`.
  · rintro ⟨F⟩
    -- Its two sides go to `x`, so `F(0, t) = F(1, t)` for every `t` …
    have h01 : ∀ t, F.toFun (0, t) = F.toFun (1, t) := fun t => by
      rw [F.source', F.target']
    -- … and `F` descends along the quotient map `q × id` to a continuous `H : S¹ × I → X`,
    -- `H(q(s), t) = F(s, t)` (`continuous_descend₂`). It remains to check that `H` is a pointed
    -- homotopy from `φ` to `ψ`.
    refine ⟨⟨descend₂ F.toFun, continuous_descend₂ F.continuous_toFun h01, ?_, ?_⟩, ?_⟩
    -- Bottom: at `z = q(s)`, `H(q(s), 0) = F(s, 0) = φ(q(s))`.
    · intro z
      obtain ⟨s, rfl⟩ := qI_surjective z
      exact (descend₂_qII h01 (s, 0)).trans (F.zero' s)
    -- Top: `H(q(s), 1) = F(s, 1) = ψ(q(s))`.
    · intro z
      obtain ⟨s, rfl⟩ := qI_surjective z
      exact (descend₂_qII h01 (s, 1)).trans (F.one' s)
    -- Base point: `H(1, t) = H(q(0), t) = F(0, t) = x`.
    · intro t
      change descend₂ F.toFun (1, t) = x
      rw [← qI_zero]
      change descend₂ F.toFun (qII (0, t)) = x
      rw [descend₂_qII h01]
      exact F.source' t
  -- (⇐) Let `H` be a pointed homotopy from `φ` to `ψ`. Then `H ∘ (q × id)`,
  -- `(s, t) ↦ H(q(s), t)`, is a path homotopy from `φ ∘ q` to `ψ ∘ q`: continuous as a
  -- composite, its bottom and top are `φ(q(s))` and `ψ(q(s))`, and its sides are
  -- `H(q(0), t) = H(q(1), t) = H(1, t) = x`.
  · rintro ⟨H, hH⟩
    refine ⟨⟨⟨H.toFun ∘ qII, H.continuous_toFun.comp continuous_qII, fun s => H.zero' _,
      fun s => H.one' _⟩, fun t => ?_, fun t => ?_⟩⟩
    · change H.toFun (qI 0, t) = x; rw [qI_zero]; exact hH t
    · change H.toFun (qI 1, t) = x; rw [qI_one]; exact hH t

variable (x) in
/-- Pointed homotopy is an equivalence relation on the pointed maps `(S¹, 1) → (X, x)`: by
`homotopic_iff_pointedHomotopic` it is path homotopy of the loops, which is one (week 4,
`pathSetoid`). `prop:loops-circle`.

Lean: an `instance` is a definition that Lean finds by itself when it is needed; a `Setoid` is
given by the relation `r` and the proof `iseqv` that it is reflexive, symmetric and transitive. -/
instance pointedSetoid : Setoid (PointedMap x) where
  r := PointedHomotopic
  iseqv := by
    -- `e`: `φ ≃ ψ` (pointed) if and only if `φ ∘ q ≃ₚ ψ ∘ q`. Each of the three properties is
    -- carried over from path homotopy through `e`.
    have e : ∀ φ ψ : PointedMap x, PointedHomotopic φ ψ ↔ (pathSetoid x x).r φ.loop ψ.loop :=
      fun φ ψ => (homotopic_iff_pointedHomotopic φ ψ).symm
    exact ⟨fun φ => (e φ φ).mpr ((pathSetoid x x).iseqv.refl _),
      fun h => (e _ _).mpr ((pathSetoid x x).iseqv.symm ((e _ _).mp h)),
      fun h h' => (e _ _).mpr ((pathSetoid x x).iseqv.trans ((e _ _).mp h) ((e _ _).mp h'))⟩

variable (x) in
/-- **`prop:loops-circle`**: `π₁(X, x) = [S¹, X]_*`, the pointed homotopy classes of pointed
maps `(S¹, 1) → (X, x)`: a bijection `[γ] ↦ [γ̄]`. Mathlib: none.

Lean: `Quotient.congr e h` turns a bijection `e : A ≃ B` that respects the two relations (`h`)
into a bijection of the sets of classes. -/
def pi1EquivPointed : pi1 x ≃ Quotient (pointedSetoid x) :=
  -- The bijection is `γ ↦ γ̄` (`loopEquiv.symm`). It respects the relations: `γ ≃ₚ γ'` if and
  -- only if `γ̄ ≃ γ̄'` (pointed), because the latter means `γ̄ ∘ q ≃ₚ γ̄' ∘ q`
  -- (`homotopic_iff_pointedHomotopic`), and `γ̄ ∘ q = γ` (`Equiv.apply_symm_apply`).
  Quotient.congr loopEquiv.symm fun γ γ' => by
    change Path.Homotopic γ γ' ↔ PointedHomotopic (loopEquiv.symm γ) (loopEquiv.symm γ')
    rw [← homotopic_iff_pointedHomotopic]
    change Path.Homotopic γ γ' ↔
      Path.Homotopic (loopEquiv (loopEquiv.symm γ)) (loopEquiv (loopEquiv.symm γ'))
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]

end Loops


/-! ## The standard simplex is a ball (`def:simplex`, `prop:simplex-ball`)

The book proves `Δⁿ ≅ Dⁿ` by the radial map from the barycentre `b`. Here it is done in
coordinates for `n = 1` (a segment, where the map is affine) and `n = 2` (a triangle).
What comes from Analysis I, through the bridges `subspace_toMathlib`, `pi_toMathlib`,
`prod_toMathlib`, `real_toMathlib`: the continuity of real formulas.

Lean: a point of `ℝⁿ⁺¹` is a function `x : Fin (n + 1) → ℝ`, `i ↦ xᵢ`, where `Fin (n + 1)` is
the set `{0, 1, …, n}`; `![a, b]` is the point `(a, b)`. `∑ i, x i` is `x₀ + ⋯ + xₙ`. -/

noncomputable section Simplex

/-- The standard `n`-simplex `Δⁿ = {x ∈ ℝⁿ⁺¹ | xᵢ ≥ 0, x₀ + ⋯ + xₙ = 1}`, a subspace of the
course's product `ℝⁿ⁺¹ = ∏_{i ≤ n} ℝ` (`thm:product-top`). `def:simplex`.
Mathlib: `stdSimplex ℝ (Fin (n + 1))`. -/
def simplex (n : ℕ) : Set (Fin (n + 1) → ℝ) := {x | (∀ i, 0 ≤ x i) ∧ ∑ i, x i = 1}

/-- The boundary `∂Δⁿ`, the union of the proper faces: the points of `Δⁿ` with some coordinate
`xᵢ = 0`. `prop:simplex-ball`. Mathlib: none (`stdSimplex` has no boundary in v4.34.1). -/
def simplexBoundary (n : ℕ) : Set (simplex n) := {x | ∃ i, x.1 i = 0}

/-- **Bridge.** The course topology of `Δⁿ` is Mathlib's subspace topology of
`Fin (n + 1) → ℝ`. -/
theorem simplex_toMathlib (n : ℕ) :
    (subspace (simplex n)).toMathlib = (inferInstance : TopologicalSpace (simplex n)) := by
  have h : (fun _ : Fin (n + 1) => (real : TopSpace ℝ).toMathlib) =
      fun _ => (inferInstance : TopologicalSpace ℝ) :=
    funext fun _ => real_toMathlib
  rw [subspace_toMathlib, pi_toMathlib, h]

/-- The closed ball `D¹ = [-1, 1]`. Mathlib: `Metric.closedBall (0 : ℝ) 1`. -/
abbrev D1 : Set ℝ := Icc (-1) 1

/-- **Bridge.** The course topology of `D¹` is Mathlib's. -/
theorem D1_toMathlib : (subspace D1).toMathlib = (inferInstance : TopologicalSpace D1) := by
  rw [subspace_toMathlib, real_toMathlib]

/-- `Δ¹ → D¹`, `x ↦ x₁ - x₀`: the coordinate along the segment `[e₀, e₁]`, measured from its
barycentre `(1/2, 1/2)`. `prop:simplex-ball`, `n = 1`. -/
def simplexToD1 (x : simplex 1) : D1 :=
  -- `x₁ - x₀ ∈ [-1, 1]`, because `x₀, x₁ ≥ 0` and `x₀ + x₁ = 1`.
  ⟨x.1 1 - x.1 0, by
    obtain ⟨h0, hs⟩ := x.2
    have h01 := h0 0
    have h11 := h0 1
    rw [Fin.sum_univ_two] at hs
    constructor <;> linarith⟩

/-- `D¹ → Δ¹`, `v ↦ b + (v/2)(e₁ - e₀) = ((1 - v)/2, (1 + v)/2)`: the book's map
`v ↦ b + |v| (r(v/|v|) - b)`, where `r(±1)` are the two vertices. `prop:simplex-ball`, `n = 1`. -/
def D1ToSimplex (v : D1) : simplex 1 :=
  -- Both coordinates are `≥ 0` because `-1 ≤ v ≤ 1`, and they sum to `1`.
  ⟨![(1 - v.1) / 2, (1 + v.1) / 2], by
    refine ⟨fun i => ?_, ?_⟩
    · fin_cases i <;> simp <;> linarith [v.2.1, v.2.2]
    · rw [Fin.sum_univ_two]; simp; ring⟩

/-- **`prop:simplex-ball`**, `n = 1`: `Δ¹ ≅ D¹`. Both maps are given by real formulas, hence
continuous (Analysis I, through `simplex_toMathlib`, `D1_toMathlib`).
Mathlib: none (no homeomorphism of `stdSimplex` with a ball in v4.34.1).

Lean: a `Homeomorph A B` (week 1) is a bijection `toFun` with inverse `invFun`, the proofs
`left_inv`, `right_inv` that they are inverse, and the proofs that both are continuous. -/
def simplexHomeoD1 : Homeomorph (simplex 1) D1 where
  toFun := simplexToD1
  invFun := D1ToSimplex
  -- `x ↦ x₁ - x₀ ↦ ((1 - x₁ + x₀)/2, (1 + x₁ - x₀)/2) = (x₀, x₁)`, since `x₀ + x₁ = 1`. Checked
  -- coordinate by coordinate (Lean: `fin_cases i` takes `i = 0` and `i = 1`).
  left_inv x := by
    obtain ⟨x, h0, hs⟩ := x
    apply Subtype.ext
    funext i
    rw [Fin.sum_univ_two] at hs
    fin_cases i <;> simp [simplexToD1, D1ToSimplex] <;> linarith
  -- `v ↦ ((1 - v)/2, (1 + v)/2) ↦ (1 + v)/2 - (1 - v)/2 = v`.
  right_inv v := by
    apply Subtype.ext
    simp [simplexToD1, D1ToSimplex]
    ring
  -- `x ↦ x₁ - x₀` is a difference of two coordinates, continuous (Analysis I), and lands in
  -- `D¹`; the bridges bring this back to the course's continuity.
  continuous_toFun :=
    continuous_of_mathlib_eq (simplex_toMathlib 1) D1_toMathlib (Continuous.subtype_mk
      (((_root_.continuous_apply 1).comp _root_.continuous_subtype_val).sub
        ((_root_.continuous_apply 0).comp _root_.continuous_subtype_val)) _)
  -- `v ↦ ((1 - v)/2, (1 + v)/2)`: each coordinate is an affine function of `v`.
  continuous_invFun :=
    continuous_of_mathlib_eq D1_toMathlib (simplex_toMathlib 1) (Continuous.subtype_mk (by
      refine continuous_pi fun i => ?_
      fin_cases i <;> simp <;> fun_prop) _)

/-- **`prop:simplex-ball`**, `n = 1`, the boundary: the homeomorphism carries
`∂Δ¹ = {e₀, e₁}` onto the sphere `S⁰ = {-1, 1}`: `x ∈ ∂Δ¹` if and only if `x₁ - x₀ = ±1`.
(Lean: `simplexHomeoD1.toEquiv x` is the image of `x`.) -/
theorem simplexHomeoD1_boundary (x : simplex 1) :
    x ∈ simplexBoundary 1 ↔ (simplexHomeoD1.toEquiv x).1 = -1 ∨ (simplexHomeoD1.toEquiv x).1 = 1 := by
  obtain ⟨x, h0, hs⟩ := x
  rw [Fin.sum_univ_two] at hs
  change (∃ i, x i = 0) ↔ x 1 - x 0 = -1 ∨ x 1 - x 0 = 1
  constructor
  -- (⇒) If `x₀ = 0`, then `x₁ = 1` and `x₁ - x₀ = 1`; if `x₁ = 0`, then `x₁ - x₀ = -1`.
  · rintro ⟨i, hi⟩
    fin_cases i
    · right; simp at hi; linarith
    · left; simp at hi; linarith
  -- (⇐) If `x₁ - x₀ = -1`, then with `x₀ + x₁ = 1`, `x₁ = 0`; if `x₁ - x₀ = 1`, then `x₀ = 0`.
  · rintro (h | h)
    · exact ⟨1, by linarith [h0 0, h0 1]⟩
    · exact ⟨0, by linarith [h0 0, h0 1]⟩

end Simplex


/-! ### `n = 2`: the triangle and the disc

The book's radial map, in coordinates. Put the barycentre `b = (1/3, 1/3, 1/3)` at the origin
and use `(w₀, w₁)` as coordinates on the directions of the plane `x₀ + x₁ + x₂ = 1`, so that
`w = (a, c, -a - c)`. The ray from `b` in the direction `w` leaves `Δ²` at `b + τ w` with
`1/τ = 3 g(a, c)`, `g(a, c) = max(-a, -c, a + c)`: the coordinate of `b + t w` that vanishes
first is a `wᵢ < 0` with `-wᵢ` largest. So the book's `v ↦ b + |v| (r(v/|v|) - b)` is
`v ↦ b + k(v) v` with `k(v) = |v| / (3 g(v))` (and `0 ↦ b`), and its inverse is
`w ↦ k(w)⁻¹ w`. Both are continuous at the origin because `|w| ≤ 2 g(w)` and `g(w) ≤ 2 |w|`
(the book: "`|r(u) - b|` is bounded"); elsewhere they are real formulas (Analysis I).

In short: `x ∈ Δ²` exactly when `3 g(x - b) ≤ 1`, and `∂Δ²` is where `3 g(x - b) = 1`; the
radial map stretches each ray from the origin so that the circle `|v| = 1` goes to `3 g = 1`.

Lean: `m • v` is the multiple `m v` of a vector `v` by a number `m`. `Tendsto f (𝓝 0) (𝓝 0)`
says `f(v) → 0` as `v → 0`, and `ContinuousAt f v` that `f` is continuous at the point `v`
(Analysis I, in Mathlib's words). -/

noncomputable section Simplex2
open Real Filter Topology

/-- `g(a, c) = max(-a, -c, a + c)`: the gauge of `Δ² - b` up to the factor `3`, so that
`b + (a, c, -a - c) ∈ Δ²` exactly when `3 g(a, c) ≤ 1`. -/
def sgauge (v : ℝ × ℝ) : ℝ := max (-v.1) (max (-v.2) (v.1 + v.2))

/-- `|v| = √(a² + c²)` for `v = (a, c)`. -/
def snorm (v : ℝ × ℝ) : ℝ := √(v.1 ^ 2 + v.2 ^ 2)

/-- `k(v) = |v| / (3 g(v))`, so that `b + k(v) v` is the book's radial map. (At `v = 0`, Lean's
convention `x / 0 = 0` gives `k(0) = 0`.) -/
def sk (v : ℝ × ℝ) : ℝ := snorm v / (3 * sgauge v)

/-- `g(a, c)` is at least each of `-a`, `-c`, `a + c`. -/
theorem sgauge_ge (v : ℝ × ℝ) :
    -v.1 ≤ sgauge v ∧ -v.2 ≤ sgauge v ∧ v.1 + v.2 ≤ sgauge v :=
  ⟨le_max_left _ _, (le_max_left _ _).trans (le_max_right _ _),
    (le_max_right _ _).trans (le_max_right _ _)⟩

/-- `g(v) ≥ 0`: the three numbers `-a`, `-c`, `a + c` sum to `0`, so one of them is `≥ 0`. -/
theorem sgauge_nonneg (v : ℝ × ℝ) : 0 ≤ sgauge v := by
  obtain ⟨h1, h2, h3⟩ := sgauge_ge v; linarith

/-- `|a| ≤ 2 g(a, c)`: `-a ≤ g` and `a = (a + c) + (-c) ≤ 2 g`. -/
theorem abs_fst_le (v : ℝ × ℝ) : |v.1| ≤ 2 * sgauge v := by
  obtain ⟨h1, h2, h3⟩ := sgauge_ge v; rw [abs_le]; constructor <;> linarith

/-- `|c| ≤ 2 g(a, c)`, in the same way. -/
theorem abs_snd_le (v : ℝ × ℝ) : |v.2| ≤ 2 * sgauge v := by
  obtain ⟨h1, h2, h3⟩ := sgauge_ge v; rw [abs_le]; constructor <;> linarith

/-- `g(a, c) ≤ 2(|a| + |c|)`: each of `-a`, `-c`, `a + c` is. -/
theorem sgauge_le (v : ℝ × ℝ) : sgauge v ≤ 2 * (|v.1| + |v.2|) := by
  unfold sgauge
  refine max_le (by linarith [neg_le_abs v.1, abs_nonneg v.1, abs_nonneg v.2])
    (max_le (by linarith [neg_le_abs v.2, abs_nonneg v.2, abs_nonneg v.1]) ?_)
  linarith [le_abs_self v.1, le_abs_self v.2, abs_nonneg v.1, abs_nonneg v.2]

/-- If `g(v) = 0`, then `v = 0`: from `-a ≤ 0`, `-c ≤ 0`, `a + c ≤ 0`. -/
theorem eq_zero_of_sgauge {v : ℝ × ℝ} (h : sgauge v = 0) : v = 0 := by
  obtain ⟨h1, h2, h3⟩ := sgauge_ge v
  exact Prod.ext (by simp; linarith) (by simp; linarith)

/-- `|v| ≥ 0`. -/
theorem snorm_nonneg (v : ℝ × ℝ) : 0 ≤ snorm v := Real.sqrt_nonneg _

/-- `|v|² = a² + c²`, because `(√s)² = s` for `s ≥ 0` (Analysis I, `Real.sq_sqrt`). -/
theorem snorm_sq (v : ℝ × ℝ) : snorm v ^ 2 = v.1 ^ 2 + v.2 ^ 2 :=
  Real.sq_sqrt (by positivity)

/-- `|a| ≤ |v|`, since `a² ≤ a² + c²`. -/
theorem abs_fst_le_snorm (v : ℝ × ℝ) : |v.1| ≤ snorm v :=
  Real.abs_le_sqrt (by nlinarith [sq_nonneg v.2])

/-- `|c| ≤ |v|`, since `c² ≤ a² + c²`. -/
theorem abs_snd_le_snorm (v : ℝ × ℝ) : |v.2| ≤ snorm v :=
  Real.abs_le_sqrt (by nlinarith [sq_nonneg v.1])

/-- `|0| = 0`. -/
theorem snorm_zero : snorm 0 = 0 := by simp [snorm]

/-- `k(v) ≥ 0`, a quotient of two numbers `≥ 0`. -/
theorem sk_nonneg (v : ℝ × ℝ) : 0 ≤ sk v :=
  div_nonneg (snorm_nonneg v) (by linarith [sgauge_nonneg v])

/-- `k(v) g(v) = |v| / 3`, also at `v = 0`. -/
theorem sk_mul_sgauge (v : ℝ × ℝ) : sk v * sgauge v = snorm v / 3 := by
  -- If `g(v) = 0`, then `v = 0` (`eq_zero_of_sgauge`) and both sides are `0`; otherwise cancel
  -- `g(v)` in `|v| g(v) / (3 g(v))`.
  by_cases h : sgauge v = 0
  · rw [eq_zero_of_sgauge h, snorm_zero]; simp [sk, sgauge]
  · unfold sk; field_simp

/-- If `v ≠ 0`, then `k(v) > 0`. -/
theorem sk_pos {v : ℝ × ℝ} (hv : v ≠ 0) : 0 < sk v := by
  -- `g(v) ≠ 0` (`eq_zero_of_sgauge`), and `|v| ≠ 0`, since `|v| = 0` would give `|a| ≤ 0` and
  -- `|c| ≤ 0`, so `v = 0`. Both are `≥ 0`, hence `> 0`, and so is their quotient.
  have hg : sgauge v ≠ 0 := fun h => hv (eq_zero_of_sgauge h)
  have hn : snorm v ≠ 0 := by
    intro h
    have h1 := abs_fst_le_snorm v
    have h2 := abs_snd_le_snorm v
    rw [h] at h1 h2
    exact hv (Prod.ext (abs_nonpos_iff.mp h1) (abs_nonpos_iff.mp h2))
  exact div_pos (lt_of_le_of_ne (snorm_nonneg v) (Ne.symm hn))
    (by linarith [lt_of_le_of_ne (sgauge_nonneg v) (Ne.symm hg)])

/-- `k` is constant on each ray, `k(m v) = k(v)` for `m > 0`, because `|m v| = m |v|` and
`g(m v) = m g(v)`. -/
theorem sk_smul {m : ℝ} (hm : 0 < m) (v : ℝ × ℝ) : sk (m • v) = sk v := by
  -- `|m v| = √(m²(a² + c²)) = m |v|`, since `√(m²) = m` for `m > 0` (Analysis I).
  have hN : snorm (m • v) = m * snorm v := by
    unfold snorm
    simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    rw [show (m * v.1) ^ 2 + (m * v.2) ^ 2 = m ^ 2 * (v.1 ^ 2 + v.2 ^ 2) by ring,
      Real.sqrt_mul (by positivity), Real.sqrt_sq hm.le]
  -- `g(m v) = max(-m a, -m c, m a + m c) = m g(v)`, since `m > 0` (`mul_max_of_nonneg`).
  have hG : sgauge (m • v) = m * sgauge v := by
    unfold sgauge
    simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    rw [mul_max_of_nonneg _ _ hm.le, mul_max_of_nonneg _ _ hm.le]
    congr 1 <;> [ring; congr 1 <;> ring]
  -- So `k(m v) = m |v| / (3 m g(v)) = k(v)`.
  unfold sk
  rw [hN, hG]
  rw [show 3 * (m * sgauge v) = m * (3 * sgauge v) by ring, mul_div_mul_left _ _ hm.ne']

/-- If `|f(v)| ≤ h(v)` for all `v` and `h(v) → 0` as `v → 0`, then `f(v) → 0` as `v → 0`
(Analysis I: the squeeze). Mathlib: `squeeze_zero_norm`. -/
theorem tendsto_zero_of_abs_le {f h : ℝ × ℝ → ℝ} (hb : ∀ v, |f v| ≤ h v)
    (hh : Tendsto h (𝓝 0) (𝓝 0)) : Tendsto f (𝓝 0) (𝓝 0) :=
  squeeze_zero_norm (fun v => by rw [Real.norm_eq_abs]; exact hb v) hh

/-- `v ↦ |v|` is continuous (Analysis I: arithmetic and `√`). -/
theorem continuous_snorm : _root_.Continuous snorm := by unfold snorm; fun_prop

/-- `v ↦ g(v)` is continuous (Analysis I: arithmetic and `max`). -/
theorem continuous_sgauge : _root_.Continuous sgauge := by unfold sgauge; fun_prop

/-- `k` is continuous at every `v ≠ 0`: a quotient of continuous functions whose denominator
`3 g(v)` does not vanish there (Analysis I). -/
theorem continuousAt_sk {v : ℝ × ℝ} (hv : v ≠ 0) : ContinuousAt sk v := by
  have hg : sgauge v ≠ 0 := fun h => hv (eq_zero_of_sgauge h)
  exact continuous_snorm.continuousAt.div
    (_root_.continuous_const.mul continuous_sgauge).continuousAt (by simpa using hg)

/-- The radial map `v ↦ k(v) v` is continuous (Analysis I). -/
theorem continuous_radial : _root_.Continuous (fun v : ℝ × ℝ => sk v • v) := by
  -- It is enough to check continuity at each point `v`.
  rw [continuous_iff_continuousAt]
  intro v
  by_cases hv : v = 0
  -- At `v = 0`, where the formula breaks down. Each coordinate `x` of `w` has `|x| ≤ 2 g(w)`, so
  -- `|k(w) x| ≤ 2 k(w) g(w) = (2/3)|w|` (`sk_mul_sgauge`), which tends to `0`; by the squeeze,
  -- `k(w) w → 0 = k(0) 0`.
  · subst hv
    have bound : ∀ w : ℝ × ℝ, ∀ x, |x| ≤ 2 * sgauge w → |sk w * x| ≤ 2 / 3 * snorm w := by
      intro w x hx
      rw [abs_mul, abs_of_nonneg (sk_nonneg w)]
      have := mul_le_mul_of_nonneg_left hx (sk_nonneg w)
      nlinarith [sk_mul_sgauge w]
    have hN : Tendsto (fun w => 2 / 3 * snorm w) (𝓝 0) (𝓝 0) := by
      have hc : _root_.Continuous (fun w : ℝ × ℝ => 2 / 3 * snorm w) :=
        _root_.continuous_const.mul continuous_snorm
      exact hc.tendsto' 0 0 (by simp [snorm_zero])
    change Tendsto _ (𝓝 0) (𝓝 (sk 0 • (0 : ℝ × ℝ)))
    rw [smul_zero]
    rw [show (0 : ℝ × ℝ) = (0, 0) from rfl]
    -- A map into the plane tends to `(0, 0)` when both coordinates tend to `0`.
    refine Tendsto.prodMk_nhds ?_ ?_
    · exact tendsto_zero_of_abs_le (fun w => bound w w.1 (abs_fst_le w)) hN
    · exact tendsto_zero_of_abs_le (fun w => bound w w.2 (abs_snd_le w)) hN
  -- At `v ≠ 0`: `k` is continuous there (`continuousAt_sk`), and so is `v ↦ k(v) v`.
  · exact (continuousAt_sk hv).smul continuousAt_id

/-- The inverse radial map `w ↦ k(w)⁻¹ w` is continuous (Analysis I). -/
theorem continuous_radialInv : _root_.Continuous (fun v : ℝ × ℝ => (sk v)⁻¹ • v) := by
  rw [continuous_iff_continuousAt]
  intro v
  by_cases hv : v = 0
  -- At `0`. Each coordinate `x` of `w` has `|x| ≤ |w|`, so
  -- `|k(w)⁻¹ x| = 3 g(w) |x| / |w| ≤ 3 g(w)`, which tends to `0` (`g` is continuous and
  -- `g(0) = 0`); by the squeeze, `k(w)⁻¹ w → 0`.
  · subst hv
    have bound : ∀ w : ℝ × ℝ, ∀ x, |x| ≤ snorm w → |(sk w)⁻¹ * x| ≤ 3 * sgauge w := by
      intro w x hx
      rw [abs_mul, sk, inv_div, abs_of_nonneg (by
        exact div_nonneg (by linarith [sgauge_nonneg w]) (snorm_nonneg w))]
      by_cases hn : snorm w = 0
      · rw [hn, div_zero, zero_mul]; linarith [sgauge_nonneg w]
      · rw [div_mul_eq_mul_div, div_le_iff₀ (lt_of_le_of_ne (snorm_nonneg w) (Ne.symm hn))]
        exact mul_le_mul_of_nonneg_left hx (by linarith [sgauge_nonneg w])
    have hG : Tendsto (fun w => 3 * sgauge w) (𝓝 0) (𝓝 0) := by
      have hc : _root_.Continuous (fun w : ℝ × ℝ => 3 * sgauge w) :=
        _root_.continuous_const.mul continuous_sgauge
      exact hc.tendsto' 0 0 (by simp [sgauge])
    change Tendsto _ (𝓝 0) (𝓝 ((sk 0)⁻¹ • (0 : ℝ × ℝ)))
    rw [smul_zero]
    rw [show (0 : ℝ × ℝ) = (0, 0) from rfl]
    refine Tendsto.prodMk_nhds ?_ ?_
    · exact tendsto_zero_of_abs_le (fun w => bound w w.1 (abs_fst_le_snorm w)) hG
    · exact tendsto_zero_of_abs_le (fun w => bound w w.2 (abs_snd_le_snorm w)) hG
  -- At `v ≠ 0`: `k` is continuous and positive there, so `1/k` is continuous there too.
  · exact ((continuousAt_sk hv).inv₀ (sk_pos hv).ne').smul continuousAt_id

/-- The two radial maps are inverse, one way: `k(k(v) v)⁻¹ k(v) v = v`, because
`k(k(v) v) = k(v)` (`sk_smul`: `k` is constant on rays). -/
theorem radialInv_radial (v : ℝ × ℝ) : (sk (sk v • v))⁻¹ • (sk v • v) = v := by
  by_cases hv : v = 0
  · subst hv; simp
  · rw [sk_smul (sk_pos hv), smul_smul, inv_mul_cancel₀ (sk_pos hv).ne', one_smul]

/-- … and the other way: `k(k(w)⁻¹ w) k(w)⁻¹ w = w`, because `k(k(w)⁻¹ w) = k(w)`. -/
theorem radial_radialInv (w : ℝ × ℝ) : sk ((sk w)⁻¹ • w) • ((sk w)⁻¹ • w) = w := by
  by_cases hw : w = 0
  · subst hw; simp
  · rw [sk_smul (inv_pos.mpr (sk_pos hw)), smul_smul, mul_inv_cancel₀ (sk_pos hw).ne', one_smul]

/-- `|k(w)⁻¹ w|² = 9 g(w)²`, unless `w = 0`. -/
theorem radialInv_sq (w : ℝ × ℝ) :
    ((sk w)⁻¹ * w.1) ^ 2 + ((sk w)⁻¹ * w.2) ^ 2 = 9 * sgauge w ^ 2 ∨ w = 0 := by
  by_cases hw : w = 0
  · exact Or.inr hw
  left
  -- For `w ≠ 0`, `|w| ≠ 0`, and `|k(w)⁻¹ w|² = (3 g(w) / |w|)² |w|² = 9 g(w)²`.
  have hn : snorm w ≠ 0 := by
    have := sk_pos hw
    intro h; rw [sk, h, zero_div] at this; exact lt_irrefl _ this
  rw [sk, inv_div, mul_pow, mul_pow, ← mul_add, ← snorm_sq, div_pow]
  field_simp
  ring

/-- `D² → Δ²`, `v = (a, c) ↦ b + k(v) (a, c, -a - c)`. `prop:simplex-ball`, `n = 2`. -/
def D2ToSimplex (v : D2) : simplex 2 :=
  -- It lands in `Δ²`: the coordinates sum to `1`, and each is at least
  -- `1/3 - k(v) g(v) = (1 - |v|)/3 ≥ 0`, because `|v| ≤ 1` on the disc.
  ⟨![1 / 3 + (sk v.1 • v.1).1, 1 / 3 + (sk v.1 • v.1).2,
      1 / 3 - ((sk v.1 • v.1).1 + (sk v.1 • v.1).2)], by
    obtain ⟨h1, h2, h3⟩ := sgauge_ge v.1
    have hk := sk_nonneg v.1
    have hkg := sk_mul_sgauge v.1
    have hN : snorm v.1 ≤ 1 := Real.sqrt_le_one.mpr v.2
    refine ⟨fun i => ?_, ?_⟩
    · fin_cases i <;> simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul] <;> simp
      · nlinarith [mul_nonneg hk (by linarith : 0 ≤ v.1.1 + sgauge v.1)]
      · nlinarith [mul_nonneg hk (by linarith : 0 ≤ v.1.2 + sgauge v.1)]
      · nlinarith [mul_nonneg hk (by linarith : 0 ≤ sgauge v.1 - (v.1.1 + v.1.2))]
    · rw [Fin.sum_univ_three]; simp; ring⟩

/-- `Δ² → D²`, `x ↦ k(w)⁻¹ w` for `w = (x₀ - 1/3, x₁ - 1/3)`. `prop:simplex-ball`, `n = 2`. -/
def simplexToD2 (x : simplex 2) : D2 :=
  -- It lands in `D²`: `|k(w)⁻¹ w| = 3 g(w) = max(1 - 3x₀, 1 - 3x₁, 1 - 3x₂) ≤ 1`, because the
  -- `xᵢ` are `≥ 0` and `x₂ = 1 - x₀ - x₁`.
  ⟨(sk (x.1 0 - 1 / 3, x.1 1 - 1 / 3))⁻¹ • (x.1 0 - 1 / 3, x.1 1 - 1 / 3), by
    obtain ⟨h0, hs⟩ := x.2
    rw [Fin.sum_univ_three] at hs
    have hg : sgauge (x.1 0 - 1 / 3, x.1 1 - 1 / 3) ≤ 1 / 3 := by
      unfold sgauge
      refine max_le (by simp; linarith [h0 0]) (max_le (by simp; linarith [h0 1]) ?_)
      simp; linarith [h0 2]
    have hg0 := sgauge_nonneg (x.1 0 - 1 / 3, x.1 1 - 1 / 3)
    change (_ : ℝ) ^ 2 + _ ^ 2 ≤ 1
    simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    rcases radialInv_sq (x.1 0 - 1 / 3, x.1 1 - 1 / 3) with h | h
    · rw [h]; nlinarith
    · rw [Prod.ext_iff] at h
      simp only [Prod.fst_zero, Prod.snd_zero] at h
      rw [h.1, h.2]; simp⟩

/-- **`prop:simplex-ball`**, `n = 2`: `D² ≅ Δ²`, by the book's radial map
`v ↦ b + |v| (r(v/|v|) - b)` (here `b + k(v) v` in the coordinates above), whose inverse is
`x ↦ k(w)⁻¹ w`; both are continuous (`continuous_radial`, `continuous_radialInv`; Analysis I,
through the bridges `D2_toMathlib`, `simplex_toMathlib`). The book gets the continuity of the
inverse from compactness; here it is the explicit bound `g(w) ≤ 2 |w|`.
Mathlib: none (no homeomorphism of `stdSimplex` with a ball in v4.34.1). -/
def D2HomeoSimplex : Homeomorph D2 (simplex 2) where
  toFun := D2ToSimplex
  invFun := simplexToD2
  -- `v ↦ x ↦ v`: the first two coordinates of `x`, minus `1/3`, are `w = k(v) v`, and
  -- `k(w)⁻¹ w = v` (`radialInv_radial`).
  left_inv v := by
    apply Subtype.ext
    have e : ((1 / 3 + (sk v.1 • v.1).1 - 1 / 3, 1 / 3 + (sk v.1 • v.1).2 - 1 / 3) : ℝ × ℝ) =
        sk v.1 • v.1 := by ext <;> simp
    change (sk (_ - 1 / 3, _ - 1 / 3))⁻¹ • ((_ : ℝ) - 1 / 3, (_ : ℝ) - 1 / 3) = v.1
    simp only [D2ToSimplex, Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [e]
    exact radialInv_radial v.1
  -- `x ↦ v ↦ x`: with `w = (x₀ - 1/3, x₁ - 1/3)` and `v = k(w)⁻¹ w`, `k(v) v = w`
  -- (`radial_radialInv`, `e1`, `e2` its two coordinates). So the coordinates come back as
  -- `1/3 + w₀ = x₀`, `1/3 + w₁ = x₁`, and `1/3 - w₀ - w₁ = 1 - x₀ - x₁ = x₂`.
  right_inv x := by
    have hs := x.2.2
    rw [Fin.sum_univ_three] at hs
    apply Subtype.ext
    have hG : (simplexToD2 x).1 = (sk (x.1 0 - 1 / 3, x.1 1 - 1 / 3))⁻¹ •
        (x.1 0 - 1 / 3, x.1 1 - 1 / 3) := rfl
    have e := radial_radialInv (x.1 0 - 1 / 3, x.1 1 - 1 / 3)
    rw [← hG] at e
    have e1 := congrArg Prod.fst e
    have e2 := congrArg Prod.snd e
    simp only at e1 e2
    funext i
    fin_cases i
    · change 1 / 3 + (sk (simplexToD2 x).1 • (simplexToD2 x).1).1 = x.1 0; rw [e1]; ring
    · change 1 / 3 + (sk (simplexToD2 x).1 • (simplexToD2 x).1).2 = x.1 1; rw [e2]; ring
    · change 1 / 3 - ((sk (simplexToD2 x).1 • (simplexToD2 x).1).1 +
        (sk (simplexToD2 x).1 • (simplexToD2 x).1).2) = x.1 2
      rw [e1, e2]; linarith
  -- Continuity of `v ↦ x`: each coordinate is `1/3` plus or minus a coordinate of the
  -- continuous `k(v) v` (`continuous_radial`); the bridges turn this into the course's.
  continuous_toFun := by
    refine continuous_of_mathlib_eq D2_toMathlib (simplex_toMathlib 2)
      (Continuous.subtype_mk ?_ _)
    have hR := continuous_radial.comp (_root_.continuous_subtype_val (p := (· ∈ D2)))
    refine continuous_pi fun i => ?_
    fin_cases i
    · exact _root_.continuous_const.add (_root_.continuous_fst.comp hR)
    · exact _root_.continuous_const.add (_root_.continuous_snd.comp hR)
    · exact _root_.continuous_const.sub
        ((_root_.continuous_fst.comp hR).add (_root_.continuous_snd.comp hR))
  -- Continuity of `x ↦ v`: `w = (x₀ - 1/3, x₁ - 1/3)` is continuous in `x`, and `w ↦ k(w)⁻¹ w`
  -- is continuous (`continuous_radialInv`).
  continuous_invFun := by
    refine continuous_of_mathlib_eq (simplex_toMathlib 2) D2_toMathlib
      (Continuous.subtype_mk ?_ _)
    refine continuous_radialInv.comp ?_
    have h0 := (_root_.continuous_apply (0 : Fin 3)).comp
      (_root_.continuous_subtype_val (p := (· ∈ simplex 2)))
    have h1 := (_root_.continuous_apply (1 : Fin 3)).comp
      (_root_.continuous_subtype_val (p := (· ∈ simplex 2)))
    exact (h0.sub _root_.continuous_const).prodMk (h1.sub _root_.continuous_const)

/-- **`prop:simplex-ball`**, `n = 2`, the boundary: the homeomorphism carries the circle
`S¹ ⊆ D²` onto `∂Δ²`: the image of `v ∈ D²` has a coordinate `0` if and only if `|v| = 1`. -/
theorem D2HomeoSimplex_boundary (v : D2) :
    D2HomeoSimplex.toEquiv v ∈ simplexBoundary 2 ↔ v.1 ∈ S1 := by
  -- The facts used: `-a, -c, a + c ≤ g(v)`, `k(v) ≥ 0`, `k(v) g(v) = |v|/3`, and `|v| ≤ 1`.
  obtain ⟨h1, h2, h3⟩ := sgauge_ge v.1
  have hk := sk_nonneg v.1
  have hkg := sk_mul_sgauge v.1
  have hN : snorm v.1 ≤ 1 := Real.sqrt_le_one.mpr v.2
  -- `v ∈ S¹` means `|v| = 1` (`√s = 1` exactly when `s = 1`).
  have hN1 : snorm v.1 = 1 ↔ v.1 ∈ S1 := by
    change _ ↔ v.1.1 ^ 2 + v.1.2 ^ 2 = 1
    rw [snorm, Real.sqrt_eq_one]
  rw [← hN1]
  change (∃ i, (![1 / 3 + (sk v.1 • v.1).1, 1 / 3 + (sk v.1 • v.1).2,
      1 / 3 - ((sk v.1 • v.1).1 + (sk v.1 • v.1).2)] : Fin 3 → ℝ) i = 0) ↔ _
  simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  constructor
  -- (⇒) Each coordinate of `b + k(v) w` is at least `1/3 - k(v) g(v) = (1 - |v|)/3 ≥ 0`; if one
  -- of them is `0`, then `(1 - |v|)/3 ≤ 0`, so `|v| = 1`. One case for each coordinate.
  · rintro ⟨i, hi⟩
    fin_cases i <;> simp at hi
    · nlinarith [mul_le_mul_of_nonneg_left h1 hk]
    · nlinarith [mul_le_mul_of_nonneg_left h2 hk]
    · nlinarith [mul_le_mul_of_nonneg_left h3 hk]
  -- (⇐) If `|v| = 1`, then `k(v) g(v) = 1/3`. The maximum `g(v)` is attained by one of `-a`,
  -- `-c`, `a + c` (Lean: `max_choice` says `max(s, t)` is `s` or `t`), and the matching
  -- coordinate `1/3 - k(v) g(v)` is `0`.
  · intro h
    rw [h] at hkg
    rcases max_choice (-v.1.1) (max (-v.1.2) (v.1.1 + v.1.2)) with hg | hg
    · refine ⟨0, ?_⟩; simp; rw [sgauge, hg] at hkg; linarith
    · rcases max_choice (-v.1.2) (v.1.1 + v.1.2) with hg' | hg'
      · refine ⟨1, ?_⟩; simp; rw [sgauge, hg, hg'] at hkg; linarith
      · refine ⟨2, ?_⟩; simp; rw [sgauge, hg, hg'] at hkg; linarith

end Simplex2


/-! ## The Hopf map (`def:quaternions`, `def:hopf-map`, `prop:hopf-fibres`)

A unit quaternion `q` rotates the space `ℝi + ℝj + ℝk` of imaginary quaternions by
`x ↦ q x q̄`, and so moves the unit sphere `S²` there in itself; the Hopf map follows the point
`i`, `η(q) = q i q̄`. Two unit quaternions `q`, `q'` send `i` to the same point exactly when
`q' = q λ` for a unit complex number `λ`; so each fibre of `η` is a circle `{q λ : |λ| = 1}`.

Coordinates. A quaternion `q = z + jw` with `z = a + bi`, `w = c + di` (so `q = a + bi + cj - dk`,
since `j(di) = d ji = -dk`) is the point `((a, b), (c, d))` of the course's
`ℝ⁴ = (ℝ × ℝ) × (ℝ × ℝ)`, and `S³` is the unit sphere there, `|z|² + |w|² = 1`; `S²` is the unit
sphere of the imaginary quaternions `ℝi + ℝj + ℝk = ℝ × ℝ × ℝ`. A complex number `λ = l₁ + l₂ i`
is the pair `(l₁, l₂)`, and `S¹` the unit circle. What comes from outside: the product of
Mathlib's `ℍ[ℝ]` (`def:quaternions`, algebra), only to check that the book's formula is
`q i q̄`; `√` and the continuity of real formulas (Analysis I, through the bridges).

Lean: for `q : (ℝ × ℝ) × (ℝ × ℝ)`, `q.1 = z = (q.1.1, q.1.2) = (a, b)` and
`q.2 = w = (q.2.1, q.2.2) = (c, d)`. A point `q : S3` is a pair of such a point `q.1` and a proof
`q.2` that it lies on `S³`; so `q.1.1.1` is `a`. `ℝ × ℝ × ℝ` means `ℝ × (ℝ × ℝ)`, so the
coordinates of `y` are `y.1`, `y.2.1`, `y.2.2`. -/

noncomputable section Hopf
open Real

/-- `S³`, the unit quaternions: `a² + b² + c² + d² = 1`. `def:quaternions`.
Mathlib: `Quaternion.normSq`, `Metric.sphere (0 : ℍ) 1`. -/
def S3 : Set ((ℝ × ℝ) × (ℝ × ℝ)) := {q | q.1.1 ^ 2 + q.1.2 ^ 2 + q.2.1 ^ 2 + q.2.2 ^ 2 = 1}

/-- `S²`, the unit imaginary quaternions `y₁ i + y₂ j + y₃ k`, `y₁² + y₂² + y₃² = 1`, in the
coordinates `(i, j, k)`. Mathlib: `Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1`. -/
def S2 : Set (ℝ × ℝ × ℝ) := {y | y.1 ^ 2 + y.2.1 ^ 2 + y.2.2 ^ 2 = 1}

/-- The quaternion `z + jw = a + bi + cj - dk` of `((a, b), (c, d))`, in Mathlib's `ℍ[ℝ]`, whose
element `⟨a₀, a₁, a₂, a₃⟩` is `a₀ + a₁ i + a₂ j + a₃ k`. -/
def toQuat (q : (ℝ × ℝ) × (ℝ × ℝ)) : Quaternion ℝ := ⟨q.1.1, q.1.2, q.2.1, -q.2.2⟩

/-- The book's formula `η(z + jw) = (|z|² - |w|²) i - 2 z w̄ k`. Since
`z w̄ = (ac + bd) + (bc - ad) i` and `ik = -j`, it is
`(|z|² - |w|², 2 Im(z w̄), -2 Re(z w̄)) = (a² + b² - c² - d², 2(bc - ad), -2(ac + bd))` in the
coordinates `(i, j, k)`. `prop:hopf-fibres`. -/
def hopfFormula (q : (ℝ × ℝ) × (ℝ × ℝ)) : ℝ × ℝ × ℝ :=
  (q.1.1 ^ 2 + q.1.2 ^ 2 - q.2.1 ^ 2 - q.2.2 ^ 2,
    2 * (q.1.2 * q.2.1 - q.1.1 * q.2.2), -2 * (q.1.1 * q.2.1 + q.1.2 * q.2.2))

/-- `q i q̄` is the imaginary quaternion with coordinates `hopfFormula q`: the book's formula for
`η` is right (`exr-4-hopf`, a computation). `prop:hopf-fibres`. Mathlib: none.

Lean: `star q` is the conjugate `q̄`, and `⟨0, 1, 0, 0⟩` is `i`. -/
theorem conj_i_eq (q : (ℝ × ℝ) × (ℝ × ℝ)) :
    toQuat q * ⟨0, 1, 0, 0⟩ * star (toQuat q) =
      ⟨0, (hopfFormula q).1, (hopfFormula q).2.1, (hopfFormula q).2.2⟩ := by
  -- Compare the four components `1, i, j, k` (`ext`): multiply out with `i² = j² = k² = ijk = -1`
  -- (Mathlib's product, `simp`), and the two sides are the same polynomials (`ring`).
  ext <;> simp [toQuat, hopfFormula] <;> ring

/-- **`def:hopf-map`**: the Hopf map `η : S³ → S²`, `η(q) = q i q̄` (`conj_i_eq`), the image of
the point `i` under the rotation `x ↦ q x q̄`. Mathlib: none (no Hopf fibration in v4.34.1). -/
def hopf (q : S3) : S2 :=
  -- It lands in `S²`: `|η(q)| = |q|² = 1`. In coordinates,
  -- `(|z|² - |w|²)² + 4|z w̄|² = (|z|² + |w|²)²`, so `|η(q)|² - 1 = (|q|² + 1)(|q|² - 1) = 0`
  -- (Lean: `linear_combination` checks this identity of polynomials, using `h : |q|² = 1`).
  ⟨hopfFormula q.1, by
    have h := q.2
    change q.1.1.1 ^ 2 + q.1.1.2 ^ 2 + q.1.2.1 ^ 2 + q.1.2.2 ^ 2 = 1 at h
    change (_ : ℝ) ^ 2 + _ ^ 2 + _ ^ 2 = 1
    simp only [hopfFormula]
    linear_combination (q.1.1.1 ^ 2 + q.1.1.2 ^ 2 + q.1.2.1 ^ 2 + q.1.2.2 ^ 2 + 1) * h⟩

/-- **Bridge.** The course topology of `S³` is Mathlib's subspace topology of
`(ℝ × ℝ) × (ℝ × ℝ)`. -/
theorem S3_toMathlib : (subspace S3).toMathlib = (inferInstance : TopologicalSpace S3) := by
  rw [subspace_toMathlib, prod_toMathlib, prod_toMathlib, real_toMathlib]

/-- **Bridge.** The course topology of `S²` is Mathlib's. -/
theorem S2_toMathlib : (subspace S2).toMathlib = (inferInstance : TopologicalSpace S2) := by
  rw [subspace_toMathlib, prod_toMathlib, prod_toMathlib, real_toMathlib]

/-- `η` is continuous: its coordinates are polynomials (Analysis I, through the bridges).
`def:hopf-map`. -/
theorem continuous_hopf : Continuous hopf :=
  continuous_of_mathlib_eq S3_toMathlib S2_toMathlib
    (Continuous.subtype_mk (by unfold hopfFormula; fun_prop) _)

/-- Right multiplication by a complex number `λ = (l₁, l₂)`: `(z + jw) λ = zλ + j wλ`, with
`zλ = (a l₁ - b l₂) + (a l₂ + b l₁) i`. `prop:hopf-fibres`. -/
def rmul (q : (ℝ × ℝ) × (ℝ × ℝ)) (l : ℝ × ℝ) : (ℝ × ℝ) × (ℝ × ℝ) :=
  ((q.1.1 * l.1 - q.1.2 * l.2, q.1.1 * l.2 + q.1.2 * l.1),
    (q.2.1 * l.1 - q.2.2 * l.2, q.2.1 * l.2 + q.2.2 * l.1))

/-- The complex number `λ = z̄ z' + w̄ w'`, for which `q' = q λ` when `η(q) = η(q')`
(`rmul_lam`). `prop:hopf-fibres`. -/
def lam (q q' : (ℝ × ℝ) × (ℝ × ℝ)) : ℝ × ℝ :=
  (q.1.1 * q'.1.1 + q.1.2 * q'.1.2 + q.2.1 * q'.2.1 + q.2.2 * q'.2.2,
    q.1.1 * q'.1.2 - q.1.2 * q'.1.1 + q.2.1 * q'.2.2 - q.2.2 * q'.2.1)

/-- If `q ∈ S³` and `|λ| = 1`, then `q λ ∈ S³`: `|q λ|² = |zλ|² + |wλ|² = |q|² |λ|² = 1`. -/
theorem rmul_mem {q : (ℝ × ℝ) × (ℝ × ℝ)} (hq : q ∈ S3) {l : ℝ × ℝ} (hl : l ∈ S1) :
    rmul q l ∈ S3 := by
  change q.1.1 ^ 2 + q.1.2 ^ 2 + q.2.1 ^ 2 + q.2.2 ^ 2 = 1 at hq
  change l.1 ^ 2 + l.2 ^ 2 = 1 at hl
  change (_ : ℝ) ^ 2 + _ ^ 2 + _ ^ 2 + _ ^ 2 = 1
  simp only [rmul]
  linear_combination (q.1.1 ^ 2 + q.1.2 ^ 2 + q.2.1 ^ 2 + q.2.2 ^ 2) * hl + hq

/-- If `|λ| = 1`, then `η(q λ) = η(q)`: `|zλ|² - |wλ|² = (|z|² - |w|²)|λ|²` and
`(zλ)(wλ)‾ = z w̄ |λ|²`, so every coordinate of `η(qλ)` is `|λ|² = 1` times that of `η(q)`.
The easy half of `prop:hopf-fibres`. -/
theorem hopfFormula_rmul (q : (ℝ × ℝ) × (ℝ × ℝ)) {l : ℝ × ℝ} (hl : l ∈ S1) :
    hopfFormula (rmul q l) = hopfFormula q := by
  change l.1 ^ 2 + l.2 ^ 2 = 1 at hl
  simp only [hopfFormula, rmul, Prod.mk.injEq]
  refine ⟨?_, ?_, ?_⟩
  · linear_combination (q.1.1 ^ 2 + q.1.2 ^ 2 - q.2.1 ^ 2 - q.2.2 ^ 2) * hl
  · linear_combination (2 * (q.1.2 * q.2.1 - q.1.1 * q.2.2)) * hl
  · linear_combination (-2 * (q.1.1 * q.2.1 + q.1.2 * q.2.2)) * hl

/-- The heart of `prop:hopf-fibres`: if `q, q' ∈ S³` and `η(q) = η(q')`, then `q' = q λ` with
`λ = z̄ z' + w̄ w'`. The book's proof: `q⁻¹ q'` commutes with `i`, so it is complex. In
coordinates: `z λ - z'` is `z' (|z|² - |z'|²) + (z w̄ - z' w̄') w'`, and both brackets vanish
when `η(q) = η(q')` and `|q| = |q'| = 1`; likewise `w λ - w'`. -/
theorem rmul_lam {q q' : (ℝ × ℝ) × (ℝ × ℝ)} (hq : q ∈ S3) (hq' : q' ∈ S3)
    (h : hopfFormula q = hopfFormula q') : rmul q (lam q q') = q' := by
  -- The hypotheses in coordinates: `|q|² = 1`, `|q'|² = 1`, and the three coordinates of
  -- `η(q) = η(q')`: `H1` (`|z|² - |w|² = |z'|² - |w'|²`), and `H2`, `H3` (`z w̄ = z' w̄'`).
  -- With `|z|² + |w|² = |z'|² + |w'|² = 1`, `H1` gives `|z|² = |z'|²` and `|w|² = |w'|²`.
  change q.1.1 ^ 2 + q.1.2 ^ 2 + q.2.1 ^ 2 + q.2.2 ^ 2 = 1 at hq
  change q'.1.1 ^ 2 + q'.1.2 ^ 2 + q'.2.1 ^ 2 + q'.2.2 ^ 2 = 1 at hq'
  simp only [hopfFormula, Prod.mk.injEq] at h
  obtain ⟨H1, H2, H3⟩ := h
  obtain ⟨⟨a, b⟩, ⟨c, d⟩⟩ := q
  obtain ⟨⟨a', b'⟩, ⟨c', d'⟩⟩ := q'
  simp only [rmul, lam, Prod.mk.injEq] at *
  -- The four real coordinates of `q λ = q'`. In each, the difference of the two sides is the
  -- combination of `H1`, `H2`, `H3`, `hq`, `hq'` written after `linear_combination`, which is
  -- the identity in the docstring, written out.
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · linear_combination (a' / 2) * H1 + (a' / 2) * hq + (a' / 2) * hq' - (c' / 2) * H3
      - (d' / 2) * H2
  · linear_combination (b' / 2) * H1 + (b' / 2) * hq + (b' / 2) * hq' - (d' / 2) * H3
      + (c' / 2) * H2
  · linear_combination (c' / 2) * hq + (c' / 2) * hq' - (c' / 2) * H1 - (a' / 2) * H3
      + (b' / 2) * H2
  · linear_combination (d' / 2) * hq + (d' / 2) * hq' - (d' / 2) * H1 - (b' / 2) * H3
      - (a' / 2) * H2

/-- In the same situation, `λ = z̄ z' + w̄ w'` is a unit complex number. -/
theorem lam_mem {q q' : (ℝ × ℝ) × (ℝ × ℝ)} (hq : q ∈ S3) (hq' : q' ∈ S3)
    (h : hopfFormula q = hopfFormula q') : lam q q' ∈ S1 := by
  -- `q' = q λ` (`rmul_lam`), so `1 = |q'|² = |q λ|² = |λ|² |q|² = |λ|²`.
  have e := rmul_lam hq hq' h
  change q.1.1 ^ 2 + q.1.2 ^ 2 + q.2.1 ^ 2 + q.2.2 ^ 2 = 1 at hq
  change q'.1.1 ^ 2 + q'.1.2 ^ 2 + q'.2.1 ^ 2 + q'.2.2 ^ 2 = 1 at hq'
  change (lam q q').1 ^ 2 + (lam q q').2 ^ 2 = 1
  rw [← e] at hq'
  simp only [rmul] at hq'
  linear_combination hq' - ((lam q q').1 ^ 2 + (lam q q').2 ^ 2) * hq

/-- **`prop:hopf-fibres`**: `η(q) = η(q')` if and only if `q' = q λ` for a unit complex number
`λ`. Mathlib: none. -/
theorem hopf_eq_iff (q q' : S3) : hopf q = hopf q' ↔ ∃ l ∈ S1, q'.1 = rmul q.1 l := by
  constructor
  -- (⇒) Take `λ = z̄ z' + w̄ w'`: it is a unit complex number (`lam_mem`), and `q' = q λ`
  -- (`rmul_lam`). (Two points of `S²` are equal when they are equal in `ℝ³`: `congrArg`.)
  · intro h
    have h' : hopfFormula q.1 = hopfFormula q'.1 := congrArg Subtype.val h
    exact ⟨lam q.1 q'.1, lam_mem q.2 q'.2 h', (rmul_lam q.2 q'.2 h').symm⟩
  -- (⇐) If `q' = q λ` with `|λ| = 1`, then `η(q') = η(q λ) = η(q)` (`hopfFormula_rmul`).
  · rintro ⟨l, hl, e⟩
    apply Subtype.ext
    change hopfFormula q.1 = hopfFormula q'.1
    rw [e, hopfFormula_rmul _ hl]

/-- **`prop:hopf-fibres`**: `η` is onto. Departure from the book, whose proof uses
`prop:quaternion-rotations` (not formalised): an explicit preimage of `(y₁, y₂, y₃)`, namely
`z = √((1 + y₁)/2)`, `w = -(y₃ + i y₂)/(2z)` when `y₁ ≠ -1`, and `(z, w) = (0, 1)`, the
quaternion `j`, when `y₁ = -1`. -/
theorem hopf_surjective : Function.Surjective hopf := by
  -- Let `y = (y₁, y₂, y₃) ∈ S²`.
  rintro ⟨⟨y1, y2, y3⟩, hy⟩
  change y1 ^ 2 + y2 ^ 2 + y3 ^ 2 = 1 at hy
  by_cases h1 : y1 = -1
  -- The south pole `y = -i`: then `y₂² + y₃² = 0`, so `y₂ = y₃ = 0`, and `η(j) = j i j̄ = -i`
  -- (`z = 0`, `w = 1`: the formula gives `(0 - 1, 0, 0)`).
  · have h23 : y2 ^ 2 + y3 ^ 2 = 0 := by rw [h1] at hy; linarith
    have h2 : y2 = 0 := by nlinarith [sq_nonneg y2, sq_nonneg y3]
    have h3 : y3 = 0 := by nlinarith [sq_nonneg y2, sq_nonneg y3]
    refine ⟨⟨((0, 0), (1, 0)), by simp [S3]⟩, ?_⟩
    apply Subtype.ext
    simp [hopf, hopfFormula, h1, h2, h3]
  -- Otherwise `y₁ > -1` (since `y₁² ≤ 1`), so `(1 + y₁)/2 > 0`, and `z = √((1 + y₁)/2) > 0`
  -- with `z² = (1 + y₁)/2` (Analysis I). Write `w = (c, d) = (-y₃/(2z), -y₂/(2z))`.
  · have hpos : 0 < (1 + y1) / 2 := by
      have : -1 ≤ y1 := by nlinarith [sq_nonneg y2, sq_nonneg y3, sq_nonneg (y1 + 1)]
      have : -1 < y1 := lt_of_le_of_ne this (Ne.symm h1)
      linarith
    set a := √((1 + y1) / 2) with ha
    have ha2 : a ^ 2 = (1 + y1) / 2 := Real.sq_sqrt hpos.le
    have ha0 : a ≠ 0 := (Real.sqrt_pos.mpr hpos).ne'
    refine ⟨⟨((a, 0), (-y3 / (2 * a), -y2 / (2 * a))), ?_⟩, ?_⟩
    -- `q = z + jw` is on `S³`: `|z|² + |w|² = (1 + y₁)/2 + (y₂² + y₃²)/(2(1 + y₁))
    -- = (1 + y₁)/2 + (1 - y₁)/2 = 1`, using `y₂² + y₃² = 1 - y₁²`.
    · change a ^ 2 + 0 ^ 2 + (-y3 / (2 * a)) ^ 2 + (-y2 / (2 * a)) ^ 2 = 1
      field_simp
      rw [ha2]
      linear_combination hy
    -- `η(q) = y`, coordinate by coordinate: `|z|² - |w|² = (1 + y₁)/2 - (1 - y₁)/2 = y₁`;
    -- `2(bc - ad) = -2z · (-y₂/(2z)) = y₂`; `-2(ac + bd) = -2z · (-y₃/(2z)) = y₃`.
    · apply Subtype.ext
      change hopfFormula ((a, 0), (-y3 / (2 * a), -y2 / (2 * a))) = (y1, y2, y3)
      simp only [hopfFormula, Prod.mk.injEq]
      refine ⟨?_, ?_, ?_⟩
      · field_simp
        rw [ha2]
        linear_combination -hy
      · field_simp; ring
      · field_simp; ring

/-- The fibre `η⁻¹(η(q))` through `q`, a subspace of `S³`. `prop:hopf-fibres`. -/
def hopfFibre (q : S3) : Set S3 := {q' | hopf q' = hopf q}

/-- **Bridge.** The course topology of a fibre is Mathlib's. -/
theorem hopfFibre_toMathlib (q : S3) :
    (subspace (hopfFibre q)).toMathlib = (inferInstance : TopologicalSpace (hopfFibre q)) := by
  rw [subspace_toMathlib, S3_toMathlib]

/-- **`prop:hopf-fibres`**: every fibre of `η` is a circle: `λ ↦ q λ` is a homeomorphism from
`S¹` onto the fibre through `q`, with inverse `q' ↦ z̄ z' + w̄ w'` (`hopf_eq_iff`). Both are
polynomial, hence continuous (Analysis I, through the bridges).
Mathlib: none.

Lean: a point of the fibre is a point of `S³` (itself a point of `ℝ⁴` with a proof) with a
proof that it lies in the fibre; so `q'.1.1` is the point of `ℝ⁴`, and `Subtype.ext` is used
twice. -/
def hopfFibreHomeo (q : S3) : Homeomorph S1 (hopfFibre q) where
  -- `λ ↦ q λ`: it lies on `S³` (`rmul_mem`) and in the fibre, `η(qλ) = η(q)`
  -- (`hopfFormula_rmul`).
  toFun l := ⟨⟨rmul q.1 l.1, rmul_mem q.2 l.2⟩, by
    apply Subtype.ext
    change hopfFormula (rmul q.1 l.1) = hopfFormula q.1
    exact hopfFormula_rmul _ l.2⟩
  -- `q' ↦ λ = z̄ z' + w̄ w'`, a unit complex number (`lam_mem`).
  invFun q' := ⟨lam q.1 q'.1.1, lam_mem q.2 q'.1.2 (congrArg Subtype.val q'.2).symm⟩
  -- `λ ↦ q λ ↦ z̄ zλ + w̄ wλ = (|z|² + |w|²) λ = λ`, since `|q| = 1`.
  left_inv l := by
    apply Subtype.ext
    have hq := q.2
    change q.1.1.1 ^ 2 + q.1.1.2 ^ 2 + q.1.2.1 ^ 2 + q.1.2.2 ^ 2 = 1 at hq
    change lam q.1 (rmul q.1 l.1) = l.1
    apply Prod.ext
    · simp only [lam, rmul]; linear_combination l.1.1 * hq
    · simp only [lam, rmul]; linear_combination l.1.2 * hq
  -- `q' ↦ λ ↦ q λ = q'`, because `η(q') = η(q)` (`rmul_lam`).
  right_inv q' := by
    apply Subtype.ext; apply Subtype.ext
    exact rmul_lam q.2 q'.1.2 (congrArg Subtype.val q'.2).symm
  -- Both maps are given by polynomials in the coordinates (Analysis I), brought back to the
  -- course's continuity through the bridges.
  continuous_toFun := by
    refine continuous_of_mathlib_eq S1_toMathlib (hopfFibre_toMathlib q)
      (Continuous.subtype_mk (Continuous.subtype_mk ?_ _) _)
    unfold rmul; fun_prop
  continuous_invFun := by
    refine continuous_of_mathlib_eq (hopfFibre_toMathlib q) S1_toMathlib
      (Continuous.subtype_mk ?_ _)
    unfold lam; fun_prop

end Hopf

end Course
