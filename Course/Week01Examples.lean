/-
Machine-generated (Claude, Aristotle), no line written by a person. Copyleft: GPL-3.0-or-later.

# Week 1: the examples

This file checks the examples of week 1 of the book
that make a claim one can prove. The Sierpiński space `S = {a, b}`, with open sets `∅, {a}, S`,
is a topology in which `b ∈ cl{a}` but `a ∉ cl{b}`, so no metric gives it (`ex-1-2`,
`ex-1n-2`). The discrete, trivial and cofinite topologies are recalled from Analysis I 4.2. The
base criterion (`prop-1-10`) holds trivially for the cylinders, the `p`-adic classes and the
half-open intervals (`ex-1-11`). "Open" depends on the space: `[0, 1/2)` is open in `[0, 1]` and
not in `ℝ` (`ex-1-16`, `def-1n-6`), and the interior of `[0, 1]` is `(0, 1)` in `ℝ` but
`[0, 1)` in `[0, 2]` (`ex-1-18`). The sphere `S⁰ = {-R, R}` is discrete (`ex-1n-sphere`).
Then homeomorphisms: `(-1, 1) ≅ ℝ` by `x ↦ x/(1 - |x|)` (`ex-1-23`, `ex-1n-9`), the open square
is homeomorphic to the open disc by radial rescaling (`ex-1-25`), and two continuous bijections
that are not homeomorphisms: the identity `(ℝ, discrete) → (ℝ, usual)`, and
`e : [0, 1) → S¹`, `e(t) = (cos 2πt, sin 2πt)`, since `S¹` is compact and `[0, 1)` is not
(`ex-1-26`, `ex-1n-10`). Each declaration names the book's label and Mathlib's counterpart,
checked against Lean and Mathlib v4.34.1.

Departures from the book:
* The two points of the Sierpiński space are the two propositions, `a = True` and `b = False`,
  as in Mathlib (Lean's `Prop` is the type of statements, which has exactly these two values up
  to equality).
* The plane is `ℝ × ℝ`, and the two norms of `ex-1-25` are written out in coordinates:
  `‖x‖_∞ = max(|x₁|, |x₂|)` and `‖x‖₂ = √(x₁² + x₂²)`.
* "Not a homeomorphism" is stated as "there is no homeomorphism whose underlying map is this
  one".
* From Analysis I, through the bridges `real_toMathlib`, `prod_toMathlib`, `subspace_toMathlib`:
  the continuity of the concrete real functions (quotients, `|·|`, `cos`, `sin`, `√`), the
  inverse cosine, and the compactness of the circle (Heine–Borel). Each use says so. Everything
  else is proved here in the course's terms.

New to Lean? Read `Course/README.md` first.
-/
import Course.Week02
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Topology.MetricSpace.Bounded

-- Bookkeeping. `X`, `Y` below are spaces (types; `u v` are their "universe levels", which you
-- may ignore). `open Set` lets us write `Ioo a b` for the interval `(a, b)`, `Icc a b` for
-- `[a, b]`, `Ico a b` for `[a, b)` and `Iio c` for `(-∞, c)`, without the prefix `Set.`.
universe u v

set_option warn.classDefReducibility false

namespace Course

open Set

variable {X : Type u} {Y : Type v}

/-! ## The real line: open intervals and small balls -/

/-- An open interval `(a, b)` is open in `ℝ`: it is the ball about its midpoint `(a + b)/2` of
radius half its length, `(b - a)/2`. Mathlib: `isOpen_Ioo`. -/
theorem isOpen_Ioo_real (a b : ℝ) : IsOpen (Ioo a b) := by
  -- Step 1. `(a, b) = {y : |(a + b)/2 - y| < (b - a)/2}`. (Lean: `change` restates the goal in
  -- a form that is equal to it by definition; here it unfolds "`y ∈ (a, b)`" and "`y` is in the
  -- ball".) `|t| < r` means `-r < t < r` (`abs_lt`), and each direction is linear arithmetic.
  have h : Ioo a b = realMetric.ball ((a + b) / 2) ((b - a) / 2) := by
    ext y
    change a < y ∧ y < b ↔ |(a + b) / 2 - y| < (b - a) / 2
    rw [abs_lt]
    constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith
  -- Step 2. A ball is open (`def-1n-1`).
  rw [h]
  exact realMetric.isOpen_ball _ _

/-- If `U` is open in `ℝ` and `x ∈ U`, then there is `ε > 0` such that every `y` with
`|x - y| < ε` is in `U` (the definition of the metric topology, `def-1n-1`).
Mathlib: `Metric.isOpen_iff`. -/
theorem exists_abs_lt_of_isOpen_real {U : Set ℝ} (hU : IsOpen U) {x : ℝ} (hx : x ∈ U) :
    ∃ ε > 0, ∀ y, |x - y| < ε → y ∈ U := by
  -- `U` contains a ball `{y : |x - y| < ε}` about `x` (`isOpen_real_iff_ball`, `Week02.lean`).
  obtain ⟨ε, hε, h⟩ := (isOpen_real_iff_ball U).mp hU x hx
  exact ⟨ε, hε, fun y hy => h hy⟩

/-! ## The Sierpiński space (`ex-1-2`, `ex-1n-2`) -/

/-- `ex-1-2`, `ex-1n-2`: the Sierpiński space `S = {a, b}` with open sets `∅, {a}, S`. Its
points are taken to be the two propositions, `a = True` (the generic point) and `b = False`
(the special point), as in Mathlib; the open sets are written as the sets that contain `a`
as soon as they contain `b`, which are exactly `∅, {a}, S` (`isOpen_sierpinski_iff`).
Mathlib: `sierpinskiSpace` (see `sierpinski_toMathlib`).

Lean: an `instance` is a definition that Lean then uses automatically: from here on, `Prop`
carries this topology whenever a topology on it is needed. The four lines after `where` give
the open sets and prove the three axioms of a topology (`TopSpace`, `Week01.lean`). -/
instance sierpinski : TopSpace Prop where
  -- `U` is open when `b ∈ U` implies `a ∈ U`.
  IsOpen U := False ∈ U → True ∈ U
  -- `S` is open: it contains `a`.
  isOpen_univ := fun _ => mem_univ _
  -- If `U` and `V` are open and `b ∈ U ∩ V`, then `a ∈ U` and `a ∈ V`.
  -- (Lean: `h.1`, `h.2` are the two halves of `h : b ∈ U ∧ b ∈ V`.)
  isOpen_inter := fun _ _ hU hV h => ⟨hU h.1, hV h.2⟩
  -- If `b` is in the union of the open sets of `𝒰`, it is in some `U ∈ 𝒰`; then `a ∈ U`, so
  -- `a` is in the union. (Lean: `rintro 𝒰 h ⟨U, hU, hF⟩` is `intro` followed by `obtain`: "let
  -- `𝒰` be such that `h`, and let `U ∈ 𝒰` (`hU`) contain `b` (`hF`)".)
  isOpen_sUnion := by
    rintro 𝒰 h ⟨U, hU, hF⟩
    exact ⟨U, hU, h U hU hF⟩

/-- `ex-1-2`: the open sets of `S` are exactly `∅`, `{a}` and `S`. (That these three sets form
a topology is "by inspection" in the book; here it is the three axioms checked in
`sierpinski`.) -/
theorem isOpen_sierpinski_iff (U : Set Prop) : IsOpen U ↔ U = ∅ ∨ U = {True} ∨ U = univ := by
  change (False ∈ U → True ∈ U) ↔ _
  constructor
  -- (⇒) Let `U` be open (`h`: if `b ∈ U` then `a ∈ U`). Sort by which of `a`, `b` lie in `U`.
  -- Each time, to show `U` equals the set we name, we check each point `q`: `q` is `a` or `b`
  -- (Lean: `Classical.propComplete q` says `q = True ∨ q = False`; the pattern `rfl` then puts
  -- `True`, resp. `False`, in place of `q`), and `simp` reads off the answer from `hT`, `hF`.
  · intro h
    by_cases hT : True ∈ U
    · by_cases hF : False ∈ U
      -- `a, b ∈ U`: `U = S`.
      · right; right
        ext q; rcases Classical.propComplete q with rfl | rfl <;> simp [hT, hF]
      -- `a ∈ U`, `b ∉ U`: `U = {a}`.
      · right; left
        ext q; rcases Classical.propComplete q with rfl | rfl <;> simp [hT, hF]
    -- `a ∉ U`: then `b ∉ U` too, since `b ∈ U` would force `a ∈ U`; so `U = ∅`.
    · left
      have hF : False ∉ U := fun hF => hT (h hF)
      ext q; rcases Classical.propComplete q with rfl | rfl <;> simp [hT, hF]
  -- (⇐) Each of `∅`, `{a}`, `S` is open: for `∅` there is no `b` in it, and `{a}`, `S` contain
  -- `a`.
  · rintro (rfl | rfl | rfl) <;> simp

/-- `ex-1-2`: `{a}` is open. (Lean: `Or.inr (Or.inl rfl)` picks the second of the three
alternatives `U = ∅ ∨ U = {a} ∨ U = S`.) -/
theorem isOpen_sierpinski_generic : IsOpen ({True} : Set Prop) :=
  (isOpen_sierpinski_iff _).mpr (Or.inr (Or.inl rfl))

/-- `ex-1-2`: `{b}` is not open. -/
theorem not_isOpen_sierpinski_special : ¬ IsOpen ({False} : Set Prop) := by
  -- If `{b}` were open, then `b ∈ {b}` would give `a ∈ {b}`, that is `a = b`, which is false.
  -- (Lean: `absurd p np` concludes anything from `p` and `¬p`.)
  intro h
  have : True ∈ ({False} : Set Prop) := h rfl
  exact absurd (this : True = False) (by simp)

/-- `ex-1-2`: `b ∈ cl{a}`: the only open set containing `b` is `S`, which contains `a`. -/
theorem special_mem_closure_generic : False ∈ closure ({True} : Set Prop) := by
  -- The closure `cl{a}` is the intersection of the closed sets `C ⊇ {a}` (`closure`,
  -- `Week01.lean`); take such a `C` and show `b ∈ C`.
  rw [closure, mem_sInter]
  rintro C ⟨hC, hTC⟩
  -- Suppose `b ∉ C`. `C` is closed, so its complement is open (`hC`); it contains `b`, hence
  -- contains `a`. But `a ∈ C` (`hTC`, as `{a} ⊆ C`): a contradiction.
  -- (Lean: `by_contra hF` supposes the negation of the goal, calls it `hF`, and asks for a
  -- contradiction.)
  by_contra hF
  exact hC hF (hTC rfl)

/-- `ex-1-2`: `a ∉ cl{b}`: `a` has the open neighbourhood `{a}`, which misses `b`; that is,
`{b}` is closed. -/
theorem generic_not_mem_closure_special : True ∉ closure ({False} : Set Prop) := by
  -- Step 1. `{b}` is closed: its complement `{a}` is open, since it does not contain `b`.
  have hC : IsClosed ({False} : Set Prop) := by
    change False ∈ ({False} : Set Prop)ᶜ → True ∈ ({False} : Set Prop)ᶜ
    intro h; exact absurd rfl h
  -- Step 2. The closure of `{b}` is the smallest closed set containing it (Analysis I 4.11(v),
  -- `closure_minimal`), so it is `{b}` itself; and `a ∉ {b}`.
  intro h
  have : True ∈ ({False} : Set Prop) := closure_minimal subset_rfl hC h
  exact absurd (this : True = False) (by simp)

/-- `ex-1-2`, `ex-1n-2`: the Sierpiński space is not (pseudo-)metrizable: "nearness here is a
one-way relation, which no metric allows". If a pseudo-metric `d` gave this topology, the ball
about `a` inside the open set `{a}` would have some radius `ε`; then the ball of radius `ε`
about `b` would lie in `{b}`, since `d(b, a) = d(a, b) < ε` would put `b` in `{a}`; so `{b}`
would be open, which it is not.
Mathlib: no `PseudoMetrizableSpace Prop` instance; `Prop` is not `T₁`.

Lean: `m.toTopSpace` is the topology of the pseudo-metric `m` (`def-1n-1`), and
`@IsOpen Prop m.toTopSpace U` says "`U` is open for that topology"; the `@` lets us name the
topology by hand instead of letting Lean use the instance `sierpinski`. -/
theorem sierpinski_not_pseudoMetrizable : ¬ ∃ m : PseudoMetric Prop, m.toTopSpace = sierpinski := by
  -- Suppose the pseudo-metric `m` (with distance `m.d`) gives the Sierpiński topology (`hm`).
  rintro ⟨m, hm⟩
  -- Then `{a}` is open for `m`, and `{b}` is not.
  have h₁ : @IsOpen Prop m.toTopSpace {True} := by rw [hm]; exact isOpen_sierpinski_generic
  have h₂ : ¬ @IsOpen Prop m.toTopSpace {False} := by rw [hm]; exact not_isOpen_sierpinski_special
  -- Step 1. As `{a}` is open and `a ∈ {a}`, some ball `B(a, ε)` lies in `{a}` (`hball`).
  obtain ⟨ε, hε, hball⟩ := (m.isOpen_iff _).mp h₁ True rfl
  -- Step 2. We show `{b}` is open for `m`, against `h₂`: about its one point `b` we take the
  -- ball `B(b, ε)`, and check that every `y` in it is `b`.
  apply h₂
  rw [m.isOpen_iff]
  rintro x rfl
  refine ⟨ε, hε, fun y hy => ?_⟩
  rcases Classical.propComplete y with rfl | rfl
  · -- The case `y = a`: then `d(b, a) < ε`, so `d(a, b) < ε` by symmetry, and `b ∈ B(a, ε)`,
    -- which lies in `{a}`: so `b = a`, which is false.
    have hy' : m.d True False < ε := by rw [m.symm]; exact hy
    have : False ∈ ({True} : Set Prop) := hball hy'
    exact absurd (this : False = True) (by simp)
  · -- The case `y = b`: then `y ∈ {b}`.
    rfl

/-- **Bridge.** The Sierpiński space is Mathlib's `sierpinskiSpace`, the topology on `Prop`
generated by `{True}`. Mathlib: `sierpinskiSpace`, `isOpen_singleton_true`. -/
theorem sierpinski_toMathlib : sierpinski.toMathlib = sierpinskiSpace := by
  -- Two topologies are equal if each is finer than the other (`le_antisymm`; Mathlib writes
  -- `t ≤ t'` for "`t` is finer than `t'`").
  apply le_antisymm
  -- Ours is finer than the topology generated by `{a}`, because `{a}` is open in ours.
  · change _ ≤ TopologicalSpace.generateFrom {{True}}
    rw [TopologicalSpace.le_generateFrom_iff_subset_isOpen]
    rintro _ rfl
    exact isOpen_sierpinski_generic
  -- Conversely, each of our open sets `∅`, `{a}`, `S` is open in Mathlib's.
  · intro U hU
    rcases (isOpen_sierpinski_iff U).mp hU with rfl | rfl | rfl
    · exact _root_.isOpen_empty
    · exact isOpen_singleton_true
    · exact _root_.isOpen_univ

/-! ## Discrete, trivial and cofinite topologies (Analysis I 4.2, recalled in week 1) -/

-- (Lean: `variable (X) in` makes `X` an explicit argument of the next definition, so that we
-- write `discrete X` for "the discrete topology on `X`".)
variable (X) in
/-- The discrete topology on `X`: every subset is open (Analysis I 4.2). Mathlib: `⊥`, with
`DiscreteTopology` (see `discrete_toMathlib`).

Lean: this is a `def`, not an `instance`: a set carries many topologies, so we name this one
and say each time that we mean it. "Every `U` is open" is written `IsOpen U := True`, and each
axiom then holds by `trivial` (the proof of `True`). -/
def discrete : TopSpace X where
  IsOpen _ := True
  isOpen_univ := trivial
  isOpen_inter _ _ _ _ := trivial
  isOpen_sUnion _ _ := trivial

variable (X) in
/-- The trivial (indiscrete) topology on `X`: only `∅` and `X` are open (Analysis I 4.2).
Mathlib: `⊤` (see `indiscrete_toMathlib`). -/
def indiscrete : TopSpace X where
  IsOpen U := U = ∅ ∨ U = univ
  isOpen_univ := Or.inr rfl
  -- `∅ ∩ V = ∅`, `U ∩ ∅ = ∅` and `X ∩ X = X`: four cases, each by `simp`.
  isOpen_inter := by
    rintro U V (rfl | rfl) (rfl | rfl) <;> simp
  -- A union of sets each `∅` or `X`: if `X` is among them the union is `X`; otherwise all of
  -- them are `∅`, and so is the union.
  isOpen_sUnion := by
    intro 𝒰 h
    by_cases hu : univ ∈ 𝒰
    · right; exact eq_univ_of_univ_subset (subset_sUnion_of_mem hu)
    · left
      apply sUnion_eq_empty.mpr
      intro U hU
      rcases h U hU with h' | rfl
      · exact h'
      · exact absurd hU hu

variable (X) in
/-- The cofinite topology on `X`: the open sets are `∅` and the sets with finite complement
(Analysis I 4.2). Mathlib: `TopologicalSpace.cofinite` (see `cofinite_toMathlib`).

Lean: `Uᶜ.Finite` says "the complement `X ∖ U` is finite". -/
def cofinite : TopSpace X where
  IsOpen U := U = ∅ ∨ Uᶜ.Finite
  -- `X` is open: its complement `∅` is finite.
  isOpen_univ := Or.inr (by simp)
  -- `U ∩ V`: if `U` or `V` is `∅`, so is `U ∩ V`; otherwise `(U ∩ V)ᶜ = Uᶜ ∪ Vᶜ` is a union of
  -- two finite sets, hence finite.
  isOpen_inter := by
    rintro U V (rfl | hU) (rfl | hV)
    · simp
    · simp
    · simp
    · right; rw [compl_inter]; exact hU.union hV
  -- A union `⋃ 𝒰`: if some `U ∈ 𝒰` has finite complement, then `(⋃ 𝒰)ᶜ ⊆ Uᶜ` is finite;
  -- otherwise every member of `𝒰` is `∅`, and so is the union.
  isOpen_sUnion := by
    intro 𝒰 h
    by_cases hc : ∃ U ∈ 𝒰, Uᶜ.Finite
    · obtain ⟨U, hU, hfin⟩ := hc
      right
      exact hfin.subset (compl_subset_compl.mpr (subset_sUnion_of_mem hU))
    · left
      apply sUnion_eq_empty.mpr
      intro U hU
      rcases h U hU with h' | h'
      · exact h'
      · exact absurd ⟨U, hU, h'⟩ hc

/-- If `X` is discrete, every map `f : X → Y` is continuous: every preimage `f⁻¹(V)` is open,
since every subset of `X` is. Mathlib: `continuous_of_discreteTopology`.

Lean: `@Continuous X Y (discrete X) _ f` is "`f` is continuous when `X` has the discrete
topology"; the `@` lets us name the topology of `X` by hand, and `_` leaves that of `Y` to the
instance `[TopSpace Y]`. -/
theorem continuous_of_discrete [TopSpace Y] (f : X → Y) :
    @Continuous X Y (discrete X) _ f := fun _ _ => trivial

/-- **Bridge.** The discrete topology is Mathlib's `⊥`, the finest topology.
Mathlib: `DiscreteTopology`. -/
theorem discrete_toMathlib : (discrete X).toMathlib = ⊥ :=
  -- It is finer than every topology, since every set is open in it; and `⊥` is finer than it.
  le_antisymm (fun _ _ => trivial) bot_le

/-- **Bridge.** The trivial topology is Mathlib's `⊤`, the coarsest topology.
Mathlib: `TopologicalSpace.isOpen_top_iff`. -/
theorem indiscrete_toMathlib : (indiscrete X).toMathlib = ⊤ :=
  -- Both have the same open sets, `∅` and `X` (`isOpen_top_iff`). (Lean: `funext` and
  -- `propext` turn "the same sets are open" into an equality of topologies.)
  TopologicalSpace.ext (funext fun U => propext (TopologicalSpace.isOpen_top_iff U).symm)

/-- **Bridge.** The cofinite topology is Mathlib's `TopologicalSpace.cofinite` (the topology
of the type synonym `CofiniteTopology X`), whose open sets are the `U` with `U ≠ ∅ → Uᶜ`
finite. Mathlib: `TopologicalSpace.cofinite`, `CofiniteTopology.isOpen_iff'`. -/
theorem cofinite_toMathlib : (cofinite X).toMathlib = TopologicalSpace.cofinite := by
  -- It is enough that the open sets agree: "`U = ∅` or `Uᶜ` finite" is the same as
  -- "if `U` is nonempty then `Uᶜ` is finite", by pure logic (`tauto`).
  apply TopologicalSpace.ext
  funext U
  apply propext
  change (U = ∅ ∨ Uᶜ.Finite) ↔ (U.Nonempty → Uᶜ.Finite)
  rw [← not_nonempty_iff_eq_empty]
  tauto

/-! ## The base criterion in use (`ex-1-11`) -/

/-- `ex-1-11`: if any two members of `𝓑` are nested or disjoint, the intersection condition of
the base criterion (`prop-1-10`, `prop-1n-5`) holds "in the strongest possible way": `B₃` may be
taken to be the smaller of `B₁`, `B₂`.

The hypothesis `h` says that any two members of `𝓑` are nested or disjoint; the conclusion is
the intersection condition of `prop-1-10`, word for word. -/
theorem inter_condition_of_nested {𝓑 : Set (Set X)}
    (h : ∀ B₁ ∈ 𝓑, ∀ B₂ ∈ 𝓑, B₁ ⊆ B₂ ∨ B₂ ⊆ B₁ ∨ Disjoint B₁ B₂) :
    ∀ B₁ ∈ 𝓑, ∀ B₂ ∈ 𝓑, ∀ x ∈ B₁ ∩ B₂, ∃ B₃ ∈ 𝓑, x ∈ B₃ ∧ B₃ ⊆ B₁ ∩ B₂ := by
  -- Let `B₁, B₂ ∈ 𝓑` and `x ∈ B₁ ∩ B₂` (`hx.1 : x ∈ B₁`, `hx.2 : x ∈ B₂`).
  intro B₁ h₁ B₂ h₂ x hx
  rcases h B₁ h₁ B₂ h₂ with h' | h' | h'
  -- If `B₁ ⊆ B₂`, then `B₁ ∩ B₂ = B₁`: take `B₃ = B₁`.
  · exact ⟨B₁, h₁, hx.1, subset_inter subset_rfl h'⟩
  -- If `B₂ ⊆ B₁`, take `B₃ = B₂`.
  · exact ⟨B₂, h₂, hx.2, subset_inter h' subset_rfl⟩
  -- If they are disjoint, there is no `x ∈ B₁ ∩ B₂` at all.
  · exact absurd hx.2 (disjoint_left.mp h' hx.1)

namespace Words

variable {A : Type u}

/-- `ex-1-11`: two cylinders `C_u`, `C_v` (the infinite words beginning with the finite word
`u`, resp. `v`; `cylinder`, `Week01.lean`) are nested or disjoint: if `u` and `v` agree where
both are defined, the cylinder of the longer word lies in that of the shorter; otherwise no
word begins with both.

Lean: a word `u` of length `n` is a map `u : Fin n → A` (`Fin n = {0, …, n - 1}`); a letter
`u ⟨i, h⟩` is the `i`-th, with the proof `h` that `i < n`. -/
theorem cylinder_nested {n m : ℕ} (u : Fin n → A) (v : Fin m → A) :
    cylinder u ⊆ cylinder v ∨ cylinder v ⊆ cylinder u ∨ Disjoint (cylinder u) (cylinder v) := by
  -- Case 1: `u` and `v` agree at every `i` less than both lengths.
  by_cases h : ∀ (i : ℕ) (h₁ : i < n) (h₂ : i < m), u ⟨i, h₁⟩ = v ⟨i, h₂⟩
  · rcases le_total n m with hnm | hmn
    -- If `n ≤ m`, a word `w` beginning with `v` begins with `u`: for `i < n`,
    -- `w(i) = v(i) = u(i)`. So `C_v ⊆ C_u`.
    · right; left
      intro w hw i
      exact (hw ⟨i, lt_of_lt_of_le i.2 hnm⟩).trans (h i i.2 _).symm
    -- If `m ≤ n`, in the same way `C_u ⊆ C_v`.
    · left
      intro w hw i
      exact (hw ⟨i, lt_of_lt_of_le i.2 hmn⟩).trans (h i _ i.2)
  -- Case 2: `u(i) ≠ v(i)` for some `i` less than both lengths. A word `w` in both cylinders
  -- would have `u(i) = w(i) = v(i)`: so the cylinders are disjoint.
  · simp only [not_forall] at h
    obtain ⟨i, h₁, h₂, hne⟩ := h
    right; right
    exact disjoint_left.mpr fun w hu hv => hne ((hu ⟨i, h₁⟩).symm.trans (hv ⟨i, h₂⟩))

/-- `ex-1-11`: the cylinders satisfy the intersection condition of the base criterion with
`B₃` the smaller of the two. -/
theorem cylinders_inter_condition :
    ∀ B₁ ∈ {C : Set (ℕ → A) | ∃ n, ∃ u : Fin n → A, C = cylinder u},
    ∀ B₂ ∈ {C : Set (ℕ → A) | ∃ n, ∃ u : Fin n → A, C = cylinder u}, ∀ x ∈ B₁ ∩ B₂,
    ∃ B₃ ∈ {C : Set (ℕ → A) | ∃ n, ∃ u : Fin n → A, C = cylinder u}, x ∈ B₃ ∧ B₃ ⊆ B₁ ∩ B₂ := by
  -- By `inter_condition_of_nested`, it is enough that two cylinders `C_u`, `C_v` are nested or
  -- disjoint, which is `cylinder_nested`.
  apply inter_condition_of_nested
  rintro _ ⟨n, u, rfl⟩ _ ⟨m, v, rfl⟩
  exact cylinder_nested u v

end Words

namespace PAdic

variable {p : ℕ}

/-- `ex-1-11`: for `k ≤ l`, the class `b + p^{l+1}ℤ` lies in `a + p^{k+1}ℤ` or misses it,
according as `p^{k+1}` divides `b - a` or not.

Lean: the class `a + p^{k+1}ℤ` is written `{n : ℤ | p^(k+1) ∣ n - a}`, and `(p : ℤ)` is the
natural number `p` seen as an integer. -/
theorem class_subset_or_disjoint (a b : ℤ) {k l : ℕ} (hkl : k ≤ l) :
    {n : ℤ | (p : ℤ) ^ (l + 1) ∣ n - b} ⊆ {n | (p : ℤ) ^ (k + 1) ∣ n - a} ∨
      Disjoint {n : ℤ | (p : ℤ) ^ (k + 1) ∣ n - a} {n | (p : ℤ) ^ (l + 1) ∣ n - b} := by
  -- As `k ≤ l`, `p^{k+1}` divides `p^{l+1}`.
  have hpow : (p : ℤ) ^ (k + 1) ∣ (p : ℤ) ^ (l + 1) := pow_dvd_pow _ (by omega)
  by_cases h : (p : ℤ) ^ (k + 1) ∣ b - a
  -- If `p^{k+1} ∣ b - a`: for `n` in `b + p^{l+1}ℤ`, `n - a = (n - b) + (b - a)` is a sum of
  -- two multiples of `p^{k+1}`, so `n ∈ a + p^{k+1}ℤ`.
  · left
    intro n hn
    have : n - a = (n - b) + (b - a) := by ring
    change (p : ℤ) ^ (k + 1) ∣ n - a
    rw [this]
    exact dvd_add (hpow.trans hn) h
  -- If not: an `n` in both classes would give `p^{k+1} ∣ (n - b) - (n - a) = -(b - a)`, so
  -- `p^{k+1} ∣ b - a` after all. (Lean: `rwa` is `rw` followed by `exact this`.)
  · right
    refine disjoint_left.mpr fun n ha hb => h ?_
    have := dvd_sub (hpow.trans (hb : (p : ℤ) ^ (l + 1) ∣ n - b)) (ha : (p : ℤ) ^ (k + 1) ∣ n - a)
    rwa [show n - b - (n - a) = -(b - a) by ring, dvd_neg] at this

/-- `ex-1-11`: two residue classes `a + p^{k+1}ℤ`, `b + p^{l+1}ℤ` are nested or disjoint.
(Lean: `classes (p := p)` is the set of all classes `a + p^{k+1}ℤ`, `Week01.lean`, with `p`
given by name.) -/
theorem classes_nested :
    ∀ B₁ ∈ classes (p := p), ∀ B₂ ∈ classes (p := p), B₁ ⊆ B₂ ∨ B₂ ⊆ B₁ ∨ Disjoint B₁ B₂ := by
  -- The class with the larger exponent lies in the other or misses it
  -- (`class_subset_or_disjoint`), whichever of `k`, `l` is larger.
  rintro _ ⟨a, k, rfl⟩ _ ⟨b, l, rfl⟩
  rcases le_total k l with hkl | hlk
  · rcases class_subset_or_disjoint (p := p) a b hkl with h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  · rcases class_subset_or_disjoint (p := p) b a hlk with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr h.symm)

/-- `ex-1-11`: the residue classes satisfy the intersection condition with `B₃` the smaller. -/
theorem classes_inter_condition :
    ∀ B₁ ∈ classes (p := p), ∀ B₂ ∈ classes (p := p), ∀ x ∈ B₁ ∩ B₂,
    ∃ B₃ ∈ classes (p := p), x ∈ B₃ ∧ B₃ ⊆ B₁ ∩ B₂ :=
  inter_condition_of_nested classes_nested

end PAdic

/-- `ex-1-11`: the half-open intervals `[a, b)` of `ℝ`. -/
def halfOpenIntervals : Set (Set ℝ) := {B | ∃ a b : ℝ, B = Ico a b}

/-- `ex-1-11`: the intersection of two half-open intervals is again one,
`[a, b) ∩ [c, d) = [max a c, min b d)`, possibly empty. Mathlib: `Set.Ico_inter_Ico`.
(Lean: `a ⊔ c` is `max a c` and `b ⊓ d` is `min b d`.) -/
theorem Ico_inter_Ico_mem (a b c d : ℝ) : Ico a b ∩ Ico c d ∈ halfOpenIntervals :=
  ⟨a ⊔ c, b ⊓ d, Set.Ico_inter_Ico⟩

/-- `ex-1-11`: the half-open intervals pass the base criterion, so they are a base of a
topology on `ℝ` (the lower limit topology). Mathlib: none in the library proper (the
Sorgenfrey line is in `Counterexamples`). -/
def lowerLimit : TopSpace ℝ :=
  -- The topology whose open sets are the unions of half-open intervals (`TopSpace.ofBase`,
  -- `prop-1-10`). Its two hypotheses:
  TopSpace.ofBase halfOpenIntervals
    -- (1) they cover `ℝ`: `x ∈ [x, x + 1)`;
    (eq_univ_of_forall fun x => ⟨Ico x (x + 1), ⟨x, x + 1, rfl⟩, le_rfl, by linarith⟩)
    -- (2) the intersection condition: `[a, b) ∩ [c, d)` is itself a half-open interval
    -- (`Ico_inter_Ico_mem`), so it may be taken as `B₃`.
    (by
      rintro _ ⟨a, b, rfl⟩ _ ⟨c, d, rfl⟩ x hx
      exact ⟨_, Ico_inter_Ico_mem a b c d, hx, subset_rfl⟩)

/-- `ex-1-11`: the half-open intervals are a base of `lowerLimit` (`prop-1-10`). -/
theorem isBase_halfOpenIntervals : @IsBase ℝ lowerLimit halfOpenIntervals :=
  TopSpace.isBase_ofBase _ _ _

/-! ## Openness depends on the space (`ex-1-16`, `def-1n-6`) -/

/-- `ex-1-16`: `[0, 1/2)` as a subset of `I = [0, 1]`.

Lean: a point `x : I` is a pair of a real number `x.1` and a proof `x.2` that `0 ≤ x.1 ≤ 1`
(so `x.2.1 : 0 ≤ x.1`); `{x | x.1 < 1/2}` is the set of points of `I` below `1/2`. -/
def halfI : Set I := {x | x.1 < 1 / 2}

/-- `ex-1-16`: `[0, 1/2)` is open in `[0, 1]`: it equals `(-1/2, 1/2) ∩ [0, 1]`, and
`(-1/2, 1/2)` is open in `ℝ`, being a ball. -/
theorem isOpen_halfI : IsOpen halfI := by
  -- By the definition of the subspace topology (`def-1-14`, `def-1n-6`) we must give an open
  -- `U ⊆ ℝ` with `[0, 1/2) = U ∩ [0, 1]`. Take the ball `U = {y : |0 - y| < 1/2}`, open by
  -- `def-1n-1`.
  refine ⟨realMetric.ball 0 (1 / 2), realMetric.isOpen_ball 0 (1 / 2), ?_⟩
  -- For `x ∈ [0, 1]`: `x < 1/2 ⟺ |0 - x| < 1/2`, since `|0 - x| = |x| = x` as `x ≥ 0`.
  ext x
  change x.1 < 1 / 2 ↔ |0 - x.1| < 1 / 2
  rw [zero_sub, abs_neg, abs_of_nonneg x.2.1]

/-- `ex-1-16`: `[0, 1/2)` is not open in `ℝ`: every interval about `0` contains negative
numbers. Mathlib: no lemma by this name; `Ico_mem_nhds_iff` is the nearest. -/
theorem not_isOpen_Ico_real : ¬ IsOpen (Ico (0 : ℝ) (1 / 2)) := by
  -- Suppose it is open. As `0 ∈ [0, 1/2)`, it contains every `y` with `|0 - y| < ε`, for some
  -- `ε > 0` (`exists_abs_lt_of_isOpen_real`).
  intro h
  obtain ⟨ε, hε, hball⟩ := exists_abs_lt_of_isOpen_real h (show (0 : ℝ) ∈ Ico 0 (1 / 2) by
    constructor <;> norm_num)
  -- Then it contains `y = -ε/2`, which is negative: a contradiction with `y ≥ 0`.
  have := hball (-(ε / 2)) (abs_lt.mpr ⟨by linarith, by linarith⟩)
  linarith [this.1]

/-- `ex-1-16`, Analysis I 4.9: every subset of `A` open in `A` is open in `X` exactly when `A`
itself is open in `X`. Mathlib: `IsOpen.isOpenMap_subtype_val`,
`Topology.IsOpenEmbedding.isOpenMap`.

Lean: `Subtype.val : A → X` is the inclusion of `A` in `X`, and `Subtype.val '' V` is `V`
seen as a subset of `X`. -/
theorem forall_isOpen_image_val_iff [TopSpace X] {A : Set X} :
    (∀ V : Set A, IsOpen V → IsOpen (Subtype.val '' V)) ↔ IsOpen A := by
  constructor
  -- (⇒) `A` is open in itself, so `A` is open in `X`. (`univ` is `A` seen as a subset of `A`.)
  · intro h
    simpa using h univ isOpen_univ
  -- (⇐) If `A` is open and `V = U ∩ A` with `U` open in `X`, then `V` is an intersection of
  -- two open sets of `X` (`IsOpen.image_val`, `Week01.lean`).
  · intro hA V hV
    exact hA.image_val hV

/-! ## Interiors do not restrict (`ex-1-18`) -/

/-- The interior of `S`: the union of the open sets inside it (Analysis I 4.11).
Mathlib: `interior`. -/
def interior [TopSpace X] (S : Set X) : Set X := ⋃₀ {U | IsOpen U ∧ U ⊆ S}

/-- **Bridge.** Mathlib: `interior` (its definition, `interior s = ⋃₀ {t | IsOpen t ∧ t ⊆ s}`). -/
theorem interior_eq_mathlib [t : TopSpace X] (S : Set X) :
    interior S = @_root_.interior X t.toMathlib S := rfl

/-- `ex-1-18`: in `ℝ` the interior of `[0, 1]` is `(0, 1)`: an open set inside `[0, 1]`
contains neither `0` nor `1`, since it would contain points just outside. -/
theorem interior_Icc_real : interior (Icc (0 : ℝ) 1) = Ioo 0 1 := by
  ext x
  constructor
  -- (⊆) Let `x ∈ U` with `U` open and `U ⊆ [0, 1]`. Some `ε`-interval about `x` lies in `U`
  -- (`h`), and `0 ≤ x ≤ 1` (`hx`).
  · rintro ⟨U, ⟨hU, hUS⟩, hxU⟩
    obtain ⟨ε, hε, h⟩ := exists_abs_lt_of_isOpen_real hU hxU
    have hx := hUS hxU
    constructor
    -- `x ≠ 0`: if `x = 0`, then `-ε/2 ∈ U ⊆ [0, 1]`, but `-ε/2 < 0`.
    · rcases eq_or_lt_of_le hx.1 with rfl | h0
      · have := hUS (h (-(ε / 2)) (abs_lt.mpr ⟨by linarith, by linarith⟩))
        linarith [this.1]
      · exact h0
    -- `x ≠ 1`: if `x = 1`, then `1 + ε/2 ∈ U ⊆ [0, 1]`, but `1 + ε/2 > 1`.
    · rcases eq_or_lt_of_le hx.2 with rfl | h1
      · have := hUS (h (1 + ε / 2) (abs_lt.mpr ⟨by linarith, by linarith⟩))
        linarith [this.2]
      · exact h1
  -- (⊇) `(0, 1)` is itself open (`isOpen_Ioo_real`) and lies in `[0, 1]`.
  · intro hx
    exact ⟨Ioo 0 1, ⟨isOpen_Ioo_real 0 1, Ioo_subset_Icc_self⟩, hx⟩

/-- `ex-1-18`: in `A = [0, 2]` the interior of `S = [0, 1]` is `[0, 1)`: it is open in `A`,
being `(-1, 1) ∩ A`; and an open set of `A` containing `1` contains points of `A` just above
`1`. (Here `S` and `[0, 1)` are written as subsets of `A`: the `x ∈ A` with `x ≤ 1`, resp.
`x < 1`.) -/
theorem interior_Icc_subspace :
    interior {x : Icc (0 : ℝ) 2 | x.1 ≤ 1} = {x | x.1 < 1} := by
  ext x
  constructor
  -- (⊆) Let `x ∈ V`, where `V ⊆ S` is open in `A`, so `V = U ∩ A` with `U` open in `ℝ`. Then
  -- `x ≤ 1`, and we show `x ≠ 1`.
  · rintro ⟨V, ⟨⟨U, hU, rfl⟩, hVS⟩, hxV⟩
    have hx1 : x.1 ≤ 1 := hVS hxV
    rcases eq_or_lt_of_le hx1 with h1 | h1
    -- Suppose `x = 1`. (Lean: `exfalso` turns the goal into `False`: we aim for a
    -- contradiction.) Some `ε`-interval about `1` lies in `U` (`h`). Let `δ = min(ε, 1)`; the
    -- point `y = 1 + δ/2` lies in `A = [0, 2]` (as `δ ≤ 1`) and within `ε` of `1`, so
    -- `y ∈ U ∩ A = V ⊆ S`, that is `y ≤ 1`; but `y > 1`.
    · exfalso
      obtain ⟨ε, hε, h⟩ := exists_abs_lt_of_isOpen_real hU hxV
      have hm : 0 < min ε 1 := lt_min hε one_pos
      have hm₁ : min ε 1 ≤ ε := min_le_left _ _
      have hm₂ : min ε 1 ≤ 1 := min_le_right _ _
      have hy : (1 + min ε 1 / 2 : ℝ) ∈ Icc (0 : ℝ) 2 := ⟨by linarith, by linarith⟩
      -- (Lean: `⟨1 + δ/2, hy⟩` is the number `1 + δ/2` as a point of `A`, with the proof `hy`
      -- that it lies in `A`.)
      have hyU : (⟨1 + min ε 1 / 2, hy⟩ : Icc (0 : ℝ) 2) ∈ Subtype.val ⁻¹' U :=
        h _ (abs_lt.mpr ⟨by rw [h1]; linarith, by rw [h1]; linarith⟩)
      have : 1 + min ε 1 / 2 ≤ 1 := hVS hyU
      linarith
    · exact h1
  -- (⊇) `[0, 1) = (-1, 1) ∩ A` is open in `A`, lies in `S`, and contains `x`.
  · intro hx
    refine ⟨{x : Icc (0 : ℝ) 2 | x.1 < 1},
      ⟨⟨Ioo (-1) 1, isOpen_Ioo_real _ _, ?_⟩, fun y (hy : y.1 < 1) => (le_of_lt hy : y.1 ≤ 1)⟩, hx⟩
    -- It remains to check `[0, 1) = (-1, 1) ∩ A`: for `y ∈ A`, `y ≥ 0 > -1`, so
    -- `y < 1 ⟺ -1 < y < 1`.
    ext y
    have := y.2.1
    change y.1 < 1 ↔ -1 < y.1 ∧ y.1 < 1
    exact ⟨fun h => ⟨by linarith, h⟩, And.right⟩

/-! ## The sphere `S⁰` (`ex-1n-sphere`) -/

/-- `ex-1n-sphere`: the sphere `S⁰_R = {-R, R} ⊆ ℝ`, with the subspace topology.
Mathlib: `Metric.sphere (0 : ℝ) R`. -/
def S0 (R : ℝ) : Set ℝ := {-R, R}

/-- `ex-1n-sphere`: for `R > 0` the two points of `S⁰_R` are open in it,
`{-R} = (-2R, 0) ∩ S⁰_R` and `{R} = (0, 2R) ∩ S⁰_R`. -/
theorem isOpen_singleton_S0 {R : ℝ} (hR : 0 < R) (x : S0 R) : IsOpen ({x} : Set (S0 R)) := by
  -- The point `x` is `-R` or `R` (`hx`).
  have hx := x.2
  simp only [S0, mem_insert_iff, mem_singleton_iff] at hx
  rcases hx with hx | hx
  -- The case `x = -R`: `{-R} = (-2R, 0) ∩ S⁰_R`. We check it at each `y ∈ S⁰_R`, that is at
  -- `y = -R` (where both sides hold: `-2R < -R < 0`) and at `y = R` (where both fail:
  -- `R ≠ -R` and `R > 0`). The four goals below are these two directions at the two points.
  · refine ⟨Ioo (-2 * R) 0, isOpen_Ioo_real _ _, ?_⟩
    ext y
    have hy := y.2
    simp only [S0, mem_insert_iff, mem_singleton_iff] at hy
    simp only [mem_singleton_iff, mem_preimage, mem_Ioo, Subtype.ext_iff, hx]
    rcases hy with hy | hy <;> rw [hy] <;> constructor <;> intro h
    · constructor <;> linarith
    · rfl
    · linarith
    · linarith [h.2]
  -- The case `x = R`: `{R} = (0, 2R) ∩ S⁰_R`, in the same way.
  · refine ⟨Ioo 0 (2 * R), isOpen_Ioo_real _ _, ?_⟩
    ext y
    have hy := y.2
    simp only [S0, mem_insert_iff, mem_singleton_iff] at hy
    simp only [mem_singleton_iff, mem_preimage, mem_Ioo, Subtype.ext_iff, hx]
    rcases hy with hy | hy <;> rw [hy] <;> constructor <;> intro h
    · linarith
    · linarith [h.1]
    · constructor <;> linarith
    · rfl

/-- `ex-1n-sphere`: `S⁰` is discrete: every subset is the union of its points, each open.
Mathlib: `DiscreteTopology` of a finite `T₁` space. -/
theorem S0_discrete {R : ℝ} (hR : 0 < R) : subspace (S0 R) = discrete (S0 R) := by
  -- Two topologies are equal when they have the same open sets (`TopSpace.ext`). Every set is
  -- open in the discrete one; so let `V ⊆ S⁰_R` and show it is open in the subspace topology.
  apply TopSpace.ext
  intro V
  refine ⟨fun _ => trivial, fun _ => ?_⟩
  -- `V = ⋃_{x ∈ V} {x}`, a union of open points (`isOpen_singleton_S0`), hence open.
  have : V = ⋃ x ∈ V, {x} := by simp
  change IsOpen V
  rw [this]
  exact isOpen_iUnion fun x => isOpen_iUnion fun _ => isOpen_singleton_S0 hR x

/-! ## Continuity of concrete maps: the Analysis I input -/

/-- **Bridge.** If the topologies of `X` and `Y` are, through the bridges, the Mathlib
topologies `mX` and `mY` (`hX`, `hY`), then a map continuous in Mathlib's sense is continuous
in the course's. This is the door through which the Analysis I facts about concrete real
functions (`x ↦ x/(1 - |x|)`, `cos`, `√`, …) enter.

Lean: `private` means the lemma is used only in this file. -/
private theorem continuous_of_mathlib' [tX : TopSpace X] [tY : TopSpace Y]
    {mX : TopologicalSpace X} {mY : TopologicalSpace Y} (hX : tX.toMathlib = mX)
    (hY : tY.toMathlib = mY) {f : X → Y} (hf : @_root_.Continuous X Y mX mY f) :
    Continuous f := by
  -- Put `tX.toMathlib` for `mX` and `tY.toMathlib` for `mY` (Lean: `subst`), and use the
  -- bridge `continuous_iff_mathlib` of `Week01.lean`.
  subst hX hY; exact (continuous_iff_mathlib f).mpr hf

/-- **Bridge.** A subspace `A ⊆ ℝ` carries Mathlib's subspace topology: the course's subspace
topology of the course's `ℝ` is Mathlib's subspace topology of Mathlib's `ℝ`.
(Lean: `inferInstance` is "the topology Mathlib puts on `A` by default".) -/
theorem subspace_real_toMathlib (A : Set ℝ) :
    (subspace A).toMathlib = (inferInstance : TopologicalSpace A) := by
  rw [subspace_toMathlib, real_toMathlib]

/-! ## `(-1, 1) ≅ ℝ` (`ex-1-23`, `ex-1n-9`) -/

/-- If `x ∈ (-1, 1)`, then `|x| < 1`. -/
theorem abs_lt_one_of_mem_Ioo {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) : |x| < 1 :=
  abs_lt.mpr ⟨hx.1, hx.2⟩

/-- For every `y ∈ ℝ`, `y/(1 + |y|) ∈ (-1, 1)`: the map `y ↦ y/(1 + |y|)` lands in `(-1, 1)`. -/
theorem div_one_add_abs_mem_Ioo (y : ℝ) : y / (1 + |y|) ∈ Ioo (-1 : ℝ) 1 := by
  -- Multiply out the positive denominator: `-(1 + |y|) < y < 1 + |y|`, true since
  -- `-|y| ≤ y ≤ |y|`.
  have h : 0 < 1 + |y| := by positivity
  rw [mem_Ioo, lt_div_iff₀ h, div_lt_iff₀ h]
  constructor <;> linarith [neg_abs_le y, le_abs_self y]

/-- `ex-1-23`, `ex-1n-9`: `(-1, 1) ≅ ℝ` by `x ↦ x / (1 - |x|)`, with inverse
`y ↦ y / (1 + |y|)`; both are continuous, being quotients of continuous functions with
non-vanishing denominator (Analysis I, through `subspace_real_toMathlib`, `real_toMathlib`).
So a bounded space can be homeomorphic to an unbounded one. Mathlib: `Homeomorph` (e.g.
`OrderIso.toHomeomorph` of an order isomorphism `Ioo (-1) 1 ≃o ℝ`).

Lean: a homeomorphism (`Homeomorph`, `Week01.lean`) is given by two maps and four proofs:
the map `toFun` (`f`), the map `invFun` (`g`), the proofs `left_inv` that `g(f(x)) = x` and
`right_inv` that `f(g(y)) = y`, and the proofs that `f` and `g` are continuous. A point
`x : Ioo (-1) 1` is a real number `x.1` with the proof `x.2` that `-1 < x.1 < 1`.
`noncomputable` says that the definition uses real division, which Lean cannot compute. -/
noncomputable def homeoIooReal : Homeomorph (Ioo (-1 : ℝ) 1) ℝ where
  toFun x := x.1 / (1 - |x.1|)
  -- `g(y)` is the number `y/(1 + |y|)` with the proof that it lies in `(-1, 1)`.
  invFun y := ⟨y / (1 + |y|), div_one_add_abs_mem_Ioo y⟩
  -- `g(f(x)) = x`. With `t = x/(1 - |x|)` we have `|t| = |x|/(1 - |x|)` (as `1 - |x| > 0`), so
  -- `1 + |t| = 1/(1 - |x|)` and `t/(1 + |t|) = x`: clear denominators (`field_simp`) and
  -- expand (`ring`). (Lean: `Subtype.ext` reduces this to an equality of real numbers.)
  left_inv x := by
    apply Subtype.ext
    have h : 0 < 1 - |x.1| := sub_pos.mpr (abs_lt_one_of_mem_Ioo x.2)
    change x.1 / (1 - |x.1|) / (1 + |x.1 / (1 - |x.1|)|) = x.1
    rw [abs_div, abs_of_pos h]
    field_simp
    ring
  -- `f(g(y)) = y`. With `s = y/(1 + |y|)`, `|s| = |y|/(1 + |y|)`, so `1 - |s| = 1/(1 + |y|)`
  -- and `s/(1 - |s|) = y`.
  right_inv y := by
    have h : 0 < 1 + |y| := by positivity
    change y / (1 + |y|) / (1 - |y / (1 + |y|)|) = y
    rw [abs_div, abs_of_pos h]
    field_simp
    ring
  -- `f` is continuous: a quotient of continuous functions whose denominator `1 - |x|` does not
  -- vanish on `(-1, 1)` (Analysis I, through the bridges).
  continuous_toFun := continuous_of_mathlib' (subspace_real_toMathlib _) real_toMathlib
    (Continuous.div (by fun_prop) (by fun_prop)
      fun x => (sub_pos.mpr (abs_lt_one_of_mem_Ioo x.2)).ne')
  -- `g` is continuous: `y/(1 + |y|)` is a quotient with denominator `1 + |y| > 0`
  -- (Analysis I); and a continuous map into `ℝ` with values in `(-1, 1)` is continuous as a map
  -- into the subspace `(-1, 1)` (`Continuous.subtype_mk`).
  continuous_invFun := continuous_of_mathlib' real_toMathlib (subspace_real_toMathlib _)
    (Continuous.subtype_mk (Continuous.div _root_.continuous_id (by fun_prop)
      fun y => (by positivity : (0 : ℝ) < 1 + |y|).ne') _)

/-! ## The open square and the open disc (`ex-1-25`, `ex-1n-9`) -/

/-- The sup norm `‖x‖_∞ = max(|x₁|, |x₂|)` on `ℝ²`. Mathlib: the norm of `ℝ × ℝ`
(`Prod.norm_def`). -/
def normInf (q : ℝ × ℝ) : ℝ := max |q.1| |q.2|

/-- The euclidean norm `‖x‖₂ = √(x₁² + x₂²)` on `ℝ²`. Mathlib: `EuclideanSpace.norm_eq`. -/
noncomputable def norm2 (q : ℝ × ℝ) : ℝ := √(q.1 ^ 2 + q.2 ^ 2)

/-- `ex-1-25`: the open square `(-1, 1)²`, the points with `‖x‖_∞ < 1`. -/
def openSquare : Set (ℝ × ℝ) := {q | normInf q < 1}

/-- `ex-1-25`: the open disc, the points with `‖x‖₂ < 1`. Mathlib: `Metric.ball 0 1` in
`EuclideanSpace ℝ (Fin 2)`. -/
def openDisc : Set (ℝ × ℝ) := {q | norm2 q < 1}

/-- `‖x‖_∞ ≥ 0`. -/
theorem normInf_nonneg (q : ℝ × ℝ) : 0 ≤ normInf q := le_max_of_le_left (abs_nonneg _)

/-- `‖x‖₂ ≥ 0`. -/
theorem norm2_nonneg (q : ℝ × ℝ) : 0 ≤ norm2 q := Real.sqrt_nonneg _

/-- `‖c x‖_∞ = c ‖x‖_∞` for `c ≥ 0`. (Lean: `c • q` is the vector `q` multiplied by the number
`c`, coordinate by coordinate.) -/
theorem normInf_smul {c : ℝ} (hc : 0 ≤ c) (q : ℝ × ℝ) : normInf (c • q) = c * normInf q := by
  -- `max(|c x₁|, |c x₂|) = max(c|x₁|, c|x₂|) = c max(|x₁|, |x₂|)`.
  simp only [normInf, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, abs_mul, abs_of_nonneg hc]
  exact (mul_max_of_nonneg _ _ hc).symm

/-- `‖c x‖₂ = c ‖x‖₂` for `c ≥ 0`. -/
theorem norm2_smul {c : ℝ} (hc : 0 ≤ c) (q : ℝ × ℝ) : norm2 (c • q) = c * norm2 q := by
  -- `√((c x₁)² + (c x₂)²) = √(c²(x₁² + x₂²)) = √(c²) √(x₁² + x₂²) = c √(x₁² + x₂²)`.
  simp only [norm2, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  rw [show (c * q.1) ^ 2 + (c * q.2) ^ 2 = c ^ 2 * (q.1 ^ 2 + q.2 ^ 2) by ring,
    Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq hc]

/-- The two norms are comparable: `‖x‖_∞ ≤ ‖x‖₂`. -/
theorem normInf_le_norm2 (q : ℝ × ℝ) : normInf q ≤ norm2 q :=
  -- `|x₁| = √(x₁²) ≤ √(x₁² + x₂²)`, and the same for `|x₂|` (`Real.abs_le_sqrt`).
  max_le (Real.abs_le_sqrt (by nlinarith [sq_nonneg q.2]))
    (Real.abs_le_sqrt (by nlinarith [sq_nonneg q.1]))

/-- The two norms are comparable: `‖x‖₂ ≤ 2‖x‖_∞`. -/
theorem norm2_le_two_normInf (q : ℝ × ℝ) : norm2 q ≤ 2 * normInf q := by
  -- Write `m = ‖x‖_∞`. Then `|xᵢ| ≤ m`, so `xᵢ² ≤ m²` for `i = 1, 2`.
  have h₁ : |q.1| ≤ normInf q := le_max_left _ _
  have h₂ : |q.2| ≤ normInf q := le_max_right _ _
  have hm := normInf_nonneg q
  have e₁ : q.1 ^ 2 ≤ normInf q ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h₁ 2
  have e₂ : q.2 ^ 2 ≤ normInf q ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h₂ 2
  -- So `√(x₁² + x₂²) ≤ √(2m²) ≤ √((2m)²) = 2m`.
  calc norm2 q ≤ √((2 * normInf q) ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
    _ = 2 * normInf q := Real.sqrt_sq (by linarith)

/-- `‖x‖_∞ > 0` for `x ≠ 0`. -/
theorem normInf_pos {q : ℝ × ℝ} (hq : q ≠ 0) : 0 < normInf q := by
  -- If `‖x‖_∞ = 0`, then `|x₁| ≤ 0` and `|x₂| ≤ 0`, so `x = (0, 0)`, against `hq`.
  -- (Lean: `h ▸ e` rewrites the fact `e` with the equation `h`.)
  rcases (normInf_nonneg q).lt_or_eq with h | h
  · exact h
  · exfalso
    apply hq
    have h₁ : |q.1| ≤ 0 := h ▸ le_max_left _ _
    have h₂ : |q.2| ≤ 0 := h ▸ le_max_right _ _
    exact Prod.ext (abs_nonpos_iff.mp h₁) (abs_nonpos_iff.mp h₂)

/-- `‖x‖₂ > 0` for `x ≠ 0`: `‖x‖₂ ≥ ‖x‖_∞ > 0`. -/
theorem norm2_pos {q : ℝ × ℝ} (hq : q ≠ 0) : 0 < norm2 q :=
  (normInf_pos hq).trans_le (normInf_le_norm2 q)

/-- `ex-1-25`: the radial rescaling `x ↦ x · ‖x‖_∞ / ‖x‖₂` (and `0 ↦ 0`, which is what the
formula gives in Lean, where `0 / 0 = 0`). -/
noncomputable def squareToDisc (q : ℝ × ℝ) : ℝ × ℝ := (normInf q / norm2 q) • q

/-- `ex-1-25`: its inverse, `y ↦ y · ‖y‖₂ / ‖y‖_∞` (and `0 ↦ 0`). -/
noncomputable def discToSquare (q : ℝ × ℝ) : ℝ × ℝ := (norm2 q / normInf q) • q

/-- `‖f(x)‖₂ = ‖x‖_∞` for `f = squareToDisc`. -/
theorem norm2_squareToDisc (q : ℝ × ℝ) : norm2 (squareToDisc q) = normInf q := by
  -- At `x = 0` both sides are `0`. Otherwise
  -- `‖(‖x‖_∞/‖x‖₂) x‖₂ = (‖x‖_∞/‖x‖₂) ‖x‖₂ = ‖x‖_∞` (`norm2_smul`, the factor being `≥ 0`).
  -- (Lean: `subst hq` puts `0` for `q` everywhere.)
  by_cases hq : q = 0
  · subst hq; simp [squareToDisc, norm2, normInf]
  · rw [squareToDisc, norm2_smul (div_nonneg (normInf_nonneg q) (norm2_pos hq).le),
      div_mul_cancel₀ _ (norm2_pos hq).ne']

/-- `‖g(y)‖_∞ = ‖y‖₂` for `g = discToSquare`. -/
theorem normInf_discToSquare (q : ℝ × ℝ) : normInf (discToSquare q) = norm2 q := by
  -- As for `norm2_squareToDisc`, with the two norms exchanged.
  by_cases hq : q = 0
  · subst hq; simp [discToSquare, norm2, normInf]
  · rw [discToSquare, normInf_smul (div_nonneg (norm2_pos hq).le (normInf_nonneg q)),
      div_mul_cancel₀ _ (normInf_pos hq).ne']

/-- `g(f(x)) = x`. -/
theorem discToSquare_squareToDisc (q : ℝ × ℝ) : discToSquare (squareToDisc q) = q := by
  by_cases hq : q = 0
  · subst hq; simp [squareToDisc, discToSquare]
  -- For `x ≠ 0` write `λ = ‖x‖_∞/‖x‖₂ > 0`, so `f(x) = λx`. Then `‖λx‖₂ = ‖x‖_∞`
  -- (`norm2_squareToDisc`) and `‖λx‖_∞ = λ‖x‖_∞`, so
  -- `g(λx) = (‖x‖_∞ / (λ‖x‖_∞)) λx = x`: the factor is `1`, as `field_simp` checks.
  · have hI := normInf_pos hq
    have h₂ := norm2_pos hq
    have hc : 0 ≤ normInf q / norm2 q := div_nonneg hI.le h₂.le
    rw [discToSquare, norm2_squareToDisc, squareToDisc, normInf_smul hc, smul_smul]
    rw [show normInf q / (normInf q / norm2 q * normInf q) * (normInf q / norm2 q) = 1 by
      field_simp, one_smul]

/-- `f(g(y)) = y`. -/
theorem squareToDisc_discToSquare (q : ℝ × ℝ) : squareToDisc (discToSquare q) = q := by
  -- As for `discToSquare_squareToDisc`, with the two norms exchanged.
  by_cases hq : q = 0
  · subst hq; simp [squareToDisc, discToSquare]
  · have hI := normInf_pos hq
    have h₂ := norm2_pos hq
    have hc : 0 ≤ norm2 q / normInf q := div_nonneg h₂.le hI.le
    rw [squareToDisc, normInf_discToSquare, discToSquare, norm2_smul hc, smul_smul]
    rw [show norm2 q / (norm2 q / normInf q * norm2 q) * (norm2 q / normInf q) = 1 by
      field_simp, one_smul]

/-- `ex-1-25`: a radial rescaling `x ↦ (a(x)/b(x)) x` of the plane is continuous when `a`, `b`
are, `b` vanishes only at `0`, and the factor `a/b` is bounded: away from `0` it is a quotient
with non-vanishing denominator, and at `0` it is squeezed, `‖(a/b) x‖ ≤ C‖x‖` (Analysis I,
here in Mathlib's terms: `squeeze_zero_norm`; the norm of `ℝ × ℝ` is the sup norm).

The hypothesis `hb0` says that `b(x) ≠ 0` for `x ≠ 0`, and `hC` that `|a(x)/b(x)| ≤ C` for
every `x`. -/
theorem continuous_rescale {a b : ℝ × ℝ → ℝ} (ha : _root_.Continuous a)
    (hb : _root_.Continuous b) (hb0 : ∀ q, q ≠ 0 → b q ≠ 0) {C : ℝ}
    (hC : ∀ q, |a q / b q| ≤ C) : _root_.Continuous fun q => (a q / b q) • q := by
  -- A map is continuous when it is continuous at every point `x` (Analysis I).
  rw [_root_.continuous_iff_continuousAt]
  intro q
  by_cases hq : q = 0
  -- At `x = 0`, where the map is `0`: we show `(a(x)/b(x)) x → 0` as `x → 0`. Its norm is at
  -- most `C‖x‖` (first goal), and `C‖x‖ → C‖0‖ = 0` (second goal); so it tends to `0` by the
  -- squeeze rule (`squeeze_zero_norm`).
  · subst hq
    simp only [ContinuousAt, smul_zero]
    refine squeeze_zero_norm (a := fun q => C * ‖q‖) (fun q => ?_) ?_
    · rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (hC q) (norm_nonneg q)
    · have hc : _root_.Continuous fun q : ℝ × ℝ => C * ‖q‖ := by fun_prop
      simpa using hc.tendsto (0 : ℝ × ℝ)
  -- At `x ≠ 0`: `a/b` is continuous at `x` as `b(x) ≠ 0`, and so is its product with `x ↦ x`.
  · exact ((ha.continuousAt.div hb.continuousAt (hb0 q hq)).smul continuousAt_id)

/-- `x ↦ ‖x‖_∞ = max(|x₁|, |x₂|)` is continuous (Analysis I: `max`, `|·|` and the coordinates
are). -/
theorem continuous_normInf : _root_.Continuous normInf := by
  unfold normInf; fun_prop

/-- `x ↦ ‖x‖₂ = √(x₁² + x₂²)` is continuous (Analysis I: `√` and polynomials are). -/
theorem continuous_norm2 : _root_.Continuous norm2 := by
  unfold norm2; fun_prop

/-- `ex-1-25`: `x ↦ x · ‖x‖_∞/‖x‖₂` is continuous, "because the two norms are comparable":
the factor lies in `[0, 1]`. -/
theorem continuous_squareToDisc : _root_.Continuous squareToDisc :=
  -- `continuous_rescale` with `a = ‖·‖_∞`, `b = ‖·‖₂` (positive off `0`, `norm2_pos`), `C = 1`:
  -- `0 ≤ ‖x‖_∞/‖x‖₂ ≤ 1` since `‖x‖_∞ ≤ ‖x‖₂` (`normInf_le_norm2`).
  continuous_rescale continuous_normInf continuous_norm2 (fun _ hq => (norm2_pos hq).ne')
    (C := 1) fun q => by
      rw [abs_of_nonneg (div_nonneg (normInf_nonneg q) (norm2_nonneg q))]
      exact div_le_one_of_le₀ (normInf_le_norm2 q) (norm2_nonneg q)

/-- `ex-1-25`: `y ↦ y · ‖y‖₂/‖y‖_∞` is continuous: the factor lies in `[0, 2]`. -/
theorem continuous_discToSquare : _root_.Continuous discToSquare :=
  -- `continuous_rescale` with `a = ‖·‖₂`, `b = ‖·‖_∞`, `C = 2`: `0 ≤ ‖y‖₂/‖y‖_∞ ≤ 2` since
  -- `‖y‖₂ ≤ 2‖y‖_∞` (`norm2_le_two_normInf`); at `y = 0` the factor is `0/0 = 0`.
  continuous_rescale continuous_norm2 continuous_normInf (fun _ hq => (normInf_pos hq).ne')
    (C := 2) fun q => by
      rw [abs_of_nonneg (div_nonneg (norm2_nonneg q) (normInf_nonneg q))]
      by_cases hq : q = 0
      · subst hq; simp [normInf]
      · rw [div_le_iff₀ (normInf_pos hq)]
        exact norm2_le_two_normInf q

/-- **Bridge.** A subspace of the plane carries Mathlib's subspace topology. -/
theorem subspace_plane_toMathlib (A : Set (ℝ × ℝ)) :
    (subspace A).toMathlib = (inferInstance : TopologicalSpace A) := by
  rw [subspace_toMathlib, prod_toMathlib, real_toMathlib]

/-- `ex-1-25`: the rescaling maps the square into the disc, as `‖f(x)‖₂ = ‖x‖_∞ < 1`. -/
theorem squareToDisc_mem (q : openSquare) : squareToDisc q.1 ∈ openDisc := by
  change norm2 (squareToDisc q.1) < 1
  rw [norm2_squareToDisc]; exact q.2

/-- `ex-1-25`: the inverse maps the disc into the square, as `‖g(y)‖_∞ = ‖y‖₂ < 1`. -/
theorem discToSquare_mem (q : openDisc) : discToSquare q.1 ∈ openSquare := by
  change normInf (discToSquare q.1) < 1
  rw [normInf_discToSquare]; exact q.2

/-- `ex-1-25`, `ex-1n-9`: the open square `(-1, 1)²` is homeomorphic to the open disc, by the
radial rescaling `x ↦ x · ‖x‖_∞/‖x‖₂`, `0 ↦ 0`, with inverse `y ↦ y · ‖y‖₂/‖y‖_∞`; it maps the
square `‖x‖_∞ < 1` onto the disc `‖x‖₂ < 1` since `‖f(x)‖₂ = ‖x‖_∞`. Continuity is Analysis I,
through `subspace_plane_toMathlib`. Mathlib: `Homeomorph`. -/
noncomputable def homeoSquareDisc : Homeomorph openSquare openDisc where
  -- `f(x)`, with the proof that it lies in the disc; `g(y)`, with the proof that it lies in the
  -- square.
  toFun q := ⟨squareToDisc q.1, squareToDisc_mem q⟩
  invFun q := ⟨discToSquare q.1, discToSquare_mem q⟩
  -- `g(f(x)) = x` and `f(g(y)) = y`, computed in the plane.
  left_inv q := Subtype.ext (discToSquare_squareToDisc q.1)
  right_inv q := Subtype.ext (squareToDisc_discToSquare q.1)
  -- `f` is continuous: it is the inclusion of the square in the plane (continuous), followed
  -- by the rescaling (continuous, `continuous_squareToDisc`), with values in the disc. Mathlib's
  -- continuity, carried over by the bridges.
  continuous_toFun := continuous_of_mathlib' (subspace_plane_toMathlib _)
    (subspace_plane_toMathlib _)
    ((continuous_squareToDisc.comp _root_.continuous_subtype_val).subtype_mk squareToDisc_mem)
  -- `g` is continuous, in the same way.
  continuous_invFun := continuous_of_mathlib' (subspace_plane_toMathlib _)
    (subspace_plane_toMathlib _)
    ((continuous_discToSquare.comp _root_.continuous_subtype_val).subtype_mk discToSquare_mem)

/-! ## Continuous and bijective is not enough (`ex-1-26`, `ex-1n-10`) -/

/-- `ex-1-26`: the identity `(ℝ, discrete) → (ℝ, usual)` is continuous: every map out of a
discrete space is. -/
theorem continuous_id_discrete_real : @Continuous ℝ ℝ (discrete ℝ) real id :=
  continuous_of_discrete id

/-- `ex-1-26`: its inverse, the identity `(ℝ, usual) → (ℝ, discrete)`, is not continuous:
`{0}` is open in the discrete topology and not in the usual one. -/
theorem not_continuous_id_real_discrete : ¬ @Continuous ℝ ℝ real (discrete ℝ) id := by
  -- If it were continuous, the preimage of the open set `{0}` of `(ℝ, discrete)`, which is
  -- `{0}`, would be open in the usual topology. Then some `ε`-interval about `0` lies in `{0}`,
  -- and in particular `ε/2 = 0`, against `ε > 0`.
  intro h
  have h0 : IsOpen ({0} : Set ℝ) := h {0} trivial
  obtain ⟨ε, hε, hball⟩ := exists_abs_lt_of_isOpen_real h0 (mem_singleton 0)
  have : ε / 2 = 0 := hball (ε / 2) (abs_lt.mpr ⟨by linarith, by linarith⟩)
  linarith

/-- `ex-1-26`, `ex-1n-10`: the identity `(ℝ, discrete) → (ℝ, usual)` is a continuous bijection
and not a homeomorphism.

Lean: "not a homeomorphism" is "there is no homeomorphism `h` whose underlying map is `id`";
`@Homeomorph ℝ ℝ (discrete ℝ) real` names the two topologies by hand, `h.toEquiv` is the
bijection underlying `h`, and `⇑` turns it into a plain map `ℝ → ℝ`. -/
theorem id_discrete_real_not_homeomorph :
    @Continuous ℝ ℝ (discrete ℝ) real id ∧ Function.Bijective (id : ℝ → ℝ) ∧
      ¬ ∃ h : @Homeomorph ℝ ℝ (discrete ℝ) real, ⇑(@Homeomorph.toEquiv ℝ ℝ (discrete ℝ) real h) = id := by
  -- Continuous: `continuous_id_discrete_real`; bijective: the identity is.
  refine ⟨continuous_id_discrete_real, Function.bijective_id, ?_⟩
  -- Suppose `h` is a homeomorphism with underlying map `id` (`hh`); call its bijection `e`.
  -- (Lean: `set e := …` gives a name to an expression.)
  rintro ⟨h, hh⟩
  set e := @Homeomorph.toEquiv ℝ ℝ (discrete ℝ) real h
  -- Its inverse is also the identity: `y = e(e⁻¹(y)) = e⁻¹(y)`, since `e = id`.
  have hinv : e.invFun = id :=
    funext fun y => by have := e.apply_symm_apply y; rw [hh] at this; exact this
  -- And the inverse of a homeomorphism is continuous: so the identity `(ℝ, usual) →
  -- (ℝ, discrete)` would be continuous, against `not_continuous_id_real_discrete`.
  have := @Homeomorph.continuous_invFun ℝ ℝ (discrete ℝ) real h
  rw [hinv] at this
  exact not_continuous_id_real_discrete this

/-! ### Compactness, as far as `ex-1-26` needs it (Analysis I §5) -/

/-- A compact space: every open covering `{U_i}_{i ∈ ι}` has a finite subcovering
(Analysis I 5.1, on the board in week 1). Mathlib: `CompactSpace`
(see `isCompactSpace_iff_mathlib`).

Lean: the covering is a family `U : ι → Set X` indexed by a set `ι`; "covering" is
`∀ x, ∃ i, x ∈ U i`; and a `Finset ι` is a finite subset `J ⊆ ι`. -/
def IsCompactSpace (X : Type u) [TopSpace X] : Prop :=
  ∀ (ι : Type u) (U : ι → Set X), (∀ i, IsOpen (U i)) → (∀ x, ∃ i, x ∈ U i) →
    ∃ J : Finset ι, ∀ x, ∃ i ∈ J, x ∈ U i

/-- **Bridge.** Compactness is Mathlib's `CompactSpace`.
Mathlib: `isCompact_univ_iff`, `isCompact_iff_finite_subcover`. -/
theorem isCompactSpace_iff_mathlib [t : TopSpace X] :
    IsCompactSpace X ↔ @CompactSpace X t.toMathlib := by
  -- Give `X` Mathlib's version of its topology (Lean: `let _ := …`), and unfold Mathlib's
  -- definition: `X` is compact iff every open covering of `X` has a finite subcovering. The
  -- two definitions say the same thing, up to writing "`x ∈ X`" and "`x ∈ ⋃ U_i`".
  let _ := t.toMathlib
  rw [← isCompact_univ_iff, isCompact_iff_finite_subcover]
  constructor
  · intro h ι U hU hcover
    obtain ⟨J, hJ⟩ := h ι U hU fun x => by simpa using hcover (mem_univ x)
    exact ⟨J, fun x _ => by simpa using hJ x⟩
  · intro h ι U hU hcover
    obtain ⟨J, hJ⟩ := h U hU fun x _ => mem_iUnion.mpr (hcover x)
    exact ⟨J, fun x => by simpa using hJ (mem_univ x)⟩

/-- A continuous image of a compact space is compact (Analysis I 5.3(iii)): pull an open
covering of `Y` back along `f`. Mathlib: `IsCompact.image`, `Function.Surjective.compactSpace`.
(`hs`: `f` is surjective.) -/
theorem IsCompactSpace.of_surjective {X Y : Type u} [TopSpace X] [TopSpace Y]
    (hX : IsCompactSpace X) {f : X → Y} (hf : Continuous f) (hs : Function.Surjective f) :
    IsCompactSpace Y := by
  -- Let `{U_i}` be an open covering of `Y`. Then `{f⁻¹(U_i)}` is an open covering of `X`, so
  -- finitely many, `i ∈ J`, cover `X`.
  intro ι U hU hcover
  obtain ⟨J, hJ⟩ := hX ι (fun i => f ⁻¹' U i) (fun i => hf _ (hU i)) fun x => hcover (f x)
  -- The same `U_i`, `i ∈ J`, cover `Y`: each `y` is `f(x)` for some `x`, and `x ∈ f⁻¹(U_i)`
  -- for some `i ∈ J`.
  refine ⟨J, fun y => ?_⟩
  obtain ⟨x, rfl⟩ := hs y
  exact hJ x

/-- A ray `(-∞, c)` is open in `ℝ`: it contains the ball of radius `c - x` about each of its
points `x`. Mathlib: `isOpen_Iio`. -/
theorem isOpen_Iio_real (c : ℝ) : IsOpen (Iio c) := by
  -- Let `x < c`, and `|x - y| < c - x`. Then `y - x < c - x`, so `y < c`.
  rw [isOpen_real_iff_ball]
  intro x hx
  refine ⟨c - x, sub_pos.mpr hx, fun y hy => ?_⟩
  change |x - y| < c - x at hy
  have := (abs_lt.mp hy).1
  change y < c
  linarith

/-- `ex-1-26`: `[0, 1)` is not compact: the open sets `[0, 1 - 1/(n+1))` cover it, and no
finitely many of them do. Mathlib: no lemma by this name; a compact subset of `ℝ` is closed
(`IsCompact.isClosed`) and `[0, 1)` is not. -/
theorem not_isCompactSpace_Ico : ¬ IsCompactSpace (Ico (0 : ℝ) 1) := by
  -- Step 1. The sets `U_n = [0, 1) ∩ (-∞, 1 - 1/(n+1))`, `n ∈ ℕ`, are open in `[0, 1)`
  -- (`isOpen_Iio_real`, `def-1-14`), and they cover it: for `x < 1` there is `n` with
  -- `1/(n+1) < 1 - x` (Archimedes, Analysis I: `exists_nat_one_div_lt`), so `x ∈ U_n`. By
  -- compactness, finitely many, the `U_n` with `n ∈ J`, cover `[0, 1)`.
  -- (Lean: `(n : ℝ)` is the natural number `n` seen as a real number.)
  intro h
  obtain ⟨J, hJ⟩ := h ℕ (fun n => Subtype.val ⁻¹' Iio (1 - 1 / ((n : ℝ) + 1)))
    (fun n => ⟨_, isOpen_Iio_real _, rfl⟩)
    (fun x => by
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.mpr x.2.2)
      exact ⟨n, show x.1 < 1 - 1 / ((n : ℝ) + 1) by linarith⟩)
  -- Step 2. Let `N = max J`, and `t = 1 - 1/(N+2)`, a point of `[0, 1)`.
  set N := J.sup id
  have hN : (0 : ℝ) < (N : ℝ) + 2 := by positivity
  have ht : 1 - 1 / ((N : ℝ) + 2) ∈ Ico (0 : ℝ) 1 := by
    constructor
    · rw [sub_nonneg, div_le_one hN]; linarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
    · have : 0 < 1 / ((N : ℝ) + 2) := by positivity
      linarith
  -- Step 3. `t` lies in some `U_n` with `n ∈ J`, so `n ≤ N` and `t < 1 - 1/(n+1)`, that is
  -- `1/(n+1) < 1/(N+2)`. But `n + 1 < N + 2` gives `1/(N+2) < 1/(n+1)`: a contradiction.
  obtain ⟨n, hnJ, hn⟩ := hJ ⟨_, ht⟩
  have hnN : (n : ℝ) ≤ N := by exact_mod_cast (Finset.le_sup (f := id) hnJ)
  change 1 - 1 / ((N : ℝ) + 2) < 1 - 1 / ((n : ℝ) + 1) at hn
  have : 1 / ((N : ℝ) + 2) < 1 / ((n : ℝ) + 1) :=
    one_div_lt_one_div_of_lt (by positivity) (by linarith)
  linarith

/-- The circle `S¹ = {(x, y) | x² + y² = 1}`, with the subspace topology of the plane `ℝ × ℝ`
(`def-1-14`, `thm:product-top`). Mathlib: `Circle` (in `ℂ`). -/
def circle : Set (ℝ × ℝ) := {q | q.1 ^ 2 + q.2 ^ 2 = 1}

/-- **Bridge.** The course topology of `S¹` is Mathlib's subspace topology of `ℝ × ℝ`. -/
theorem circle_toMathlib : (subspace circle).toMathlib = (inferInstance : TopologicalSpace circle) := by
  rw [subspace_toMathlib, prod_toMathlib, real_toMathlib]

/-- `ex-1-26`: `S¹` is compact: it is closed and bounded in `ℝ²` (Analysis I, Heine–Borel,
through `circle_toMathlib`). Mathlib: `Metric.isCompact_of_isClosed_isBounded`. -/
theorem isCompactSpace_circle : IsCompactSpace circle := by
  -- Translate to Mathlib's compactness of the subset `S¹ ⊆ ℝ²` (the bridges), and apply
  -- Heine–Borel (Analysis I): a closed and bounded subset of `ℝ²` is compact.
  rw [isCompactSpace_iff_mathlib, circle_toMathlib, ← isCompact_iff_compactSpace]
  apply Metric.isCompact_of_isClosed_isBounded
  -- Closed: `S¹ = {q : x² + y² = 1}` is where a continuous function equals a constant.
  · exact isClosed_eq (by fun_prop) _root_.continuous_const
  -- Bounded: `S¹` lies in the closed ball of radius `1` about `0`. Mathlib's distance on
  -- `ℝ × ℝ` is the sup distance, so we must show `|x| ≤ 1` and `|y| ≤ 1`, that is
  -- `-1 ≤ x ≤ 1` and `-1 ≤ y ≤ 1`: four inequalities, each from `x² + y² = 1` (`nlinarith`).
  · rw [Metric.isBounded_iff_subset_closedBall 0]
    refine ⟨1, fun q (hq : q.1 ^ 2 + q.2 ^ 2 = 1) => ?_⟩
    rw [Metric.mem_closedBall, Prod.dist_eq, Real.dist_eq, Real.dist_eq, max_le_iff]
    simp only [Prod.fst_zero, Prod.snd_zero, sub_zero]
    constructor <;> rw [abs_le] <;> constructor <;>
      nlinarith [sq_nonneg q.1, sq_nonneg q.2, sq_nonneg (q.1 - 1), sq_nonneg (q.1 + 1),
        sq_nonneg (q.2 - 1), sq_nonneg (q.2 + 1)]

-- (Lean: `open Real in` lets the next declaration write `cos`, `sin`, `π` for `Real.cos`, …)
open Real in
/-- `ex-1-26`, `ex-1n-10`: `e : [0, 1) → S¹`, `e(t) = (cos 2πt, sin 2πt)`.
Mathlib: `Circle.exp` (up to the factor `2π`), `AddCircle.equivIco`.

The point `e(t)` is given with the proof that it lies on `S¹`: `cos² + sin² = 1` (`simp`). -/
noncomputable def expIco (t : Ico (0 : ℝ) 1) : circle :=
  ⟨(cos (2 * π * t), sin (2 * π * t)), by simp [circle]⟩

/-- `ex-1-26`: `e` is continuous: `cos` and `sin` are (Analysis I, through the bridges).
Mathlib: `Real.continuous_cos`, `Real.continuous_sin`. -/
theorem continuous_expIco : Continuous expIco :=
  -- `t ↦ (cos 2πt, sin 2πt)` is continuous into `ℝ²` (`fun_prop`), with values in `S¹`.
  continuous_of_mathlib' (subspace_real_toMathlib _) circle_toMathlib
    (Continuous.subtype_mk (by fun_prop) _)

open Real in
/-- `ex-1-26`: `e` is injective: `e(s) = e(t)` gives `cos 2π(t - s) = 1`, so `t - s` is an
integer (Analysis I, `Real.cos_eq_one_iff`), and `|t - s| < 1`. -/
theorem injective_expIco : Function.Injective expIco := by
  -- Let `e(s) = e(t)`; compare the first and the second coordinates.
  intro s t hst
  have h1 : cos (2 * π * s) = cos (2 * π * t) := congrArg (fun z : circle => z.1.1) hst
  have h2 : sin (2 * π * s) = sin (2 * π * t) := congrArg (fun z : circle => z.1.2) hst
  -- Step 1. `cos(2πt - 2πs) = cos 2πt cos 2πs + sin 2πt sin 2πs = cos² 2πs + sin² 2πs = 1`.
  have hc : cos (2 * π * t - 2 * π * s) = 1 := by
    rw [cos_sub, ← h1, ← h2]; nlinarith [sin_sq_add_cos_sq (2 * π * s)]
  -- Step 2. So `2πt - 2πs = 2πn` for an integer `n` (Analysis I: `cos_eq_one_iff`), and
  -- `n = t - s`.
  obtain ⟨n, hn⟩ := (cos_eq_one_iff _).mp hc
  have hπ : (0 : ℝ) < π := pi_pos
  have hn' : (n : ℝ) = t.1 - s.1 := by
    have : (n : ℝ) * (2 * π) = (t.1 - s.1) * (2 * π) := by rw [hn]; ring
    exact mul_right_cancel₀ (by positivity) this
  -- Step 3. As `s, t ∈ [0, 1)`, `-1 < t - s < 1`; the only integer there is `0`
  -- (`omega` decides such statements about integers; `exact_mod_cast` moves the inequalities
  -- from `ℝ` to `ℤ`). So `t = s`.
  have hlo : (-1 : ℝ) < n := by rw [hn']; linarith [s.2.2, t.2.1]
  have hhi : (n : ℝ) < 1 := by rw [hn']; linarith [s.2.1, t.2.2]
  have : n = 0 := by
    have := (show (-1 : ℤ) < n by exact_mod_cast hlo)
    have := (show n < (1 : ℤ) by exact_mod_cast hhi)
    omega
  apply Subtype.ext
  rw [this, Int.cast_zero] at hn'
  linarith

open Real in
/-- `ex-1-26`: `e` is surjective: for `(x, y) ∈ S¹` put `θ = arccos x ∈ [0, π]`, so that
`cos θ = x` and `sin θ = √(1 - x²) = |y|`; take `t = θ/2π` if `y ≥ 0` and `t = 1 - θ/2π` if
`y < 0` (Analysis I: the inverse cosine, `Real.cos_arccos`, `Real.sin_arccos`). -/
theorem surjective_expIco : Function.Surjective expIco := by
  -- Let `(x, y) ∈ S¹`, so `x² + y² = 1` (`hxy`), and hence `-1 ≤ x ≤ 1`.
  rintro ⟨⟨x, y⟩, hxy⟩
  change x ^ 2 + y ^ 2 = 1 at hxy
  have hx₁ : -1 ≤ x := by nlinarith [sq_nonneg y, sq_nonneg (x + 1)]
  have hx₂ : x ≤ 1 := by nlinarith [sq_nonneg y, sq_nonneg (x - 1)]
  -- Step 1. `θ = arccos x` has `cos θ = x`, `sin θ = √(1 - x²) = √(y²) = |y|`, `0 ≤ θ ≤ π`.
  have hπ : (0 : ℝ) < π := pi_pos
  have hcos : cos (arccos x) = x := cos_arccos hx₁ hx₂
  have hsin : sin (arccos x) = |y| := by
    rw [sin_arccos, show 1 - x ^ 2 = y ^ 2 by linarith, Real.sqrt_sq_eq_abs]
  have hθ₀ : 0 ≤ arccos x := arccos_nonneg x
  have hθπ : arccos x ≤ π := arccos_le_pi x
  rcases le_or_gt 0 y with hy | hy
  -- Step 2, the case `y ≥ 0`: `t = θ/2π`. It lies in `[0, 1)`, as `0 ≤ θ ≤ π < 2π` (the
  -- first two goals), and `e(t) = (cos θ, sin θ) = (x, |y|) = (x, y)` (the third).
  · refine ⟨⟨arccos x / (2 * π), ?_, ?_⟩, ?_⟩
    · positivity
    · rw [div_lt_one (by positivity)]; linarith
    · have e : 2 * π * (arccos x / (2 * π)) = arccos x := by field_simp
      apply Subtype.ext
      change (cos (2 * π * (arccos x / (2 * π))), sin (2 * π * (arccos x / (2 * π)))) = (x, y)
      rw [e, hcos, hsin, abs_of_nonneg hy]
  -- Step 3, the case `y < 0`: then `x ≠ 1` (else `y = 0`), so `θ > 0`; take `t = 1 - θ/2π`.
  -- It lies in `[0, 1)`, as `0 < θ ≤ π`, and
  -- `e(t) = (cos(2π - θ), sin(2π - θ)) = (cos θ, -sin θ) = (x, -|y|) = (x, y)`.
  · have hx1 : x < 1 := by nlinarith
    have hθ : 0 < arccos x := arccos_pos.mpr hx1
    refine ⟨⟨1 - arccos x / (2 * π), ?_, ?_⟩, ?_⟩
    · rw [sub_nonneg, div_le_one (by positivity)]; linarith
    · have : 0 < arccos x / (2 * π) := by positivity
      linarith
    · have e : 2 * π * (1 - arccos x / (2 * π)) = 2 * π - arccos x := by field_simp
      apply Subtype.ext
      change (cos (2 * π * (1 - arccos x / (2 * π))), sin (2 * π * (1 - arccos x / (2 * π))))
        = (x, y)
      rw [e, cos_two_pi_sub, sin_two_pi_sub, hcos, hsin, abs_of_neg hy, neg_neg]

/-- `ex-1-26`: `[0, 1)` and `S¹` are not homeomorphic: `S¹` is compact and `[0, 1)` is not, and
a continuous image of a compact space is compact (Analysis I 5.3(iii)). -/
theorem not_homeomorph_Ico_circle : ¬ Nonempty (Homeomorph (Ico (0 : ℝ) 1) circle) := by
  -- Let `h : [0, 1) → S¹` be a homeomorphism. Its inverse `h⁻¹ : S¹ → [0, 1)` is continuous
  -- and surjective, so `[0, 1)` is a continuous image of the compact `S¹`
  -- (`isCompactSpace_circle`), hence compact (`IsCompactSpace.of_surjective`); but it is not
  -- (`not_isCompactSpace_Ico`).
  rintro ⟨h⟩
  exact not_isCompactSpace_Ico
    (isCompactSpace_circle.of_surjective h.continuous_invFun h.toEquiv.symm.surjective)

/-- `ex-1-26`, `ex-1n-10`: `e : [0, 1) → S¹`, `e(t) = (cos 2πt, sin 2πt)`, is a continuous
bijection and not a homeomorphism: no homeomorphism `h` has `e` as its underlying map. -/
theorem expIco_not_homeomorph :
    Continuous expIco ∧ Function.Bijective expIco ∧
      ¬ ∃ h : Homeomorph (Ico (0 : ℝ) 1) circle, ⇑h.toEquiv = expIco :=
  -- Continuous, injective, surjective: the three lemmas above. If a homeomorphism `h` had `e`
  -- as its map, `[0, 1)` and `S¹` would be homeomorphic, against `not_homeomorph_Ico_circle`.
  ⟨continuous_expIco, ⟨injective_expIco, surjective_expIco⟩,
    fun ⟨h, _⟩ => not_homeomorph_Ico_circle ⟨h⟩⟩

end Course

