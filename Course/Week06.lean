/-
Machine-generated (Claude, Aristotle), no line written by a person. Copyleft: GPL-3.0-or-later.

# Week 6: the circle, path and homotopy lifting, `π₁(S¹) ≅ ℤ`

This file proves the main theorem of week 6, `π₁(S¹, 1) ≅ ℤ` (`thm:pi1-circle`), by the book's
road (week 6, "Unwinding the circle", "Lifting", "The fundamental group of the
circle"). The map `p(t) = (cos 2πt, sin 2πt) = e^{2πit}` winds the line `ℝ` round the circle, and
every arc of `S¹` missing one point is evenly covered by it (`prop:evenly-covered`,
`def:evenly-covered`). Two lifts of the same map from a connected space that agree at one point
agree everywhere (`lem:integer-difference`). Every path in `S¹` lifts to `ℝ` (`thm:path-lifting`),
and so does every map `I × I → S¹` (`thm:homotopy-lifting`). The end `f̃(1)` of the lift of a loop
`f` at `1` is its degree (`def:degree-circle`), and `[f] ↦ f̃(1)` is the isomorphism
`π₁(S¹, 1) → ℤ`, sending the loop once round to `1`. Week 6's other files build on it: Brouwer's
theorem in the plane (`Week06Brouwer.lean`) and the consequences (`Week06Circle.lean`).

Departures from the book:
* The circle is the subspace `x² + y² = 1` of the course's plane `ℝ × ℝ` (weeks 1 and 2), not
  the unit complex numbers.
* The book proves that `p` is a homeomorphism from each interval `(a + n, a + n + 1)` onto
  `S¹ \ {p(a)}` by showing it is open (via compactness). Here only two arcs are used,
  `S¹ \ {-1}` and `S¹ \ {1}`, and each gets an explicit continuous inverse of `p`, by the
  half-angle formula `t = arctan(y / (1 + x)) / π` (Analysis I); the sheets over an arc are the
  integer translates of that inverse (`p_eq_iff_of_mem_arc`).
* The book's chain of intervals in `thm:path-lifting` is replaced by a grid of mesh `1/N`, `N`
  given by the Lebesgue number lemma, as in its proof of `thm:homotopy-lifting`; the squares of
  that proof are lifted a strip at a time (`strip_lift`).
* From Analysis I, through the bridges: the continuity of `cos`, `sin`, `arctan` and of real
  arithmetic; the trigonometric identities (`2π`-periodicity, `cos x = 1` only at multiples of
  `2π`, the half-angle formulas); the connectedness of `I` and of `I × I` (through the
  intermediate value theorem); the compactness of `I` and `I × I` with the Lebesgue number
  lemma. Each use says so. Mathlib's covering maps and its fundamental group of the circle are
  not used. Mathlib's names below were checked against Lean and Mathlib v4.34.1.

New to Lean? Read `Course/README.md` first.
-/
import Course.Week04
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Topology.Order.IntermediateValue

-- Bookkeeping. `X`, `Y` below are spaces (types; `u v` are their "universe levels", which you
-- may ignore). `open Set Real` lets us write `cos`, `π`, `Icc` without prefixes, and
-- `noncomputable section` says that some definitions use real numbers, which Lean cannot compute.
universe u v

set_option warn.classDefReducibility false

namespace Course

open Set Real

noncomputable section

variable {X : Type u} {Y : Type v}

/-! ## The circle and `p(t) = e^{2πit}` -/

/-- The circle `S¹ = {(x, y) | x² + y² = 1}`, with the subspace topology of the plane `ℝ × ℝ`
(`def-1-14`, `thm:product-top`). Mathlib: `Circle` (in `ℂ`), `Metric.sphere (0 : ℝ × ℝ) 1`.

Lean: `S1` is a subset of `ℝ × ℝ`; used as a space, its points are pairs `⟨q, hq⟩` of a point
`q` of the plane and a proof `hq` that `q ∈ S¹` (`README.md`). For `z : S1`, `z.1 : ℝ × ℝ` is
the point of the plane and `z.2` the proof; so `z.1.1` and `z.1.2` are its coordinates `x`, `y`.
-/
def S1 : Set (ℝ × ℝ) := {q | q.1 ^ 2 + q.2 ^ 2 = 1}

namespace S1

/-- A point `(x, y)` of `S¹` has `x² + y² = 1`: this is the proof `z.2` that `z ∈ S¹`. -/
theorem sq_add_sq (z : S1) : z.1.1 ^ 2 + z.1.2 ^ 2 = 1 := z.2

/-- The base point `1 = (1, 0)`, which is on `S¹` since `1² + 0² = 1`. Mathlib: `1 : Circle`.
(Lean: `instance : One S1` lets us write `1` for this point.) -/
instance : One S1 := ⟨⟨(1, 0), by simp [S1]⟩⟩

/-- The antipode `-z = (-x, -y)`, on `S¹` since `(-x)² + (-y)² = x² + y² = 1`. Mathlib: `Neg`
on `Circle` (via `ℂ`). -/
instance : Neg S1 := ⟨fun z => ⟨(-z.1.1, -z.1.2), by simp [S1, (S1.sq_add_sq z)]⟩⟩

/-- Unfolding: the point `1` of `S¹`, as a point of the plane, is `(1, 0)`. -/
@[simp] theorem coe_one : ((1 : S1) : ℝ × ℝ) = (1, 0) := rfl
/-- Unfolding: `-z` is `(-x, -y)` as a point of the plane. -/
@[simp] theorem coe_neg (z : S1) : ((-z : S1) : ℝ × ℝ) = (-z.1.1, -z.1.2) := rfl

/-- Two points of `S¹` are equal if their coordinates are: `x = x'` and `y = y'`. -/
theorem ext' {z w : S1} (h1 : z.1.1 = w.1.1) (h2 : z.1.2 = w.1.2) : z = w :=
  Subtype.ext (Prod.ext h1 h2)

/-- On `S¹`, `-1 ≤ x ≤ 1`, since `x² = 1 - y² ≤ 1` (routine algebra, `nlinarith`). -/
theorem neg_one_le (z : S1) : -1 ≤ z.1.1 := by nlinarith [(S1.sq_add_sq z), sq_nonneg z.1.2]
/-- On `S¹`, `x ≤ 1`. -/
theorem le_one (z : S1) : z.1.1 ≤ 1 := by nlinarith [(S1.sq_add_sq z), sq_nonneg z.1.2]

end S1

/-- **Bridge.** The course topology of `S¹` is Mathlib's subspace topology of `ℝ × ℝ`, from the
bridges `subspace_toMathlib`, `prod_toMathlib`, `real_toMathlib`. -/
theorem S1_toMathlib : (subspace S1).toMathlib = (inferInstance : TopologicalSpace S1) := by
  rw [subspace_toMathlib, prod_toMathlib, real_toMathlib]

/-- **Bridge.** The course topology of a subset of `S¹` is Mathlib's subspace topology (the
subspace of a subspace, through `subspace_toMathlib` and `S1_toMathlib`). -/
theorem subS1_toMathlib (A : Set S1) :
    (subspace A).toMathlib = (inferInstance : TopologicalSpace A) := by
  rw [subspace_toMathlib, S1_toMathlib]

/-- `p : ℝ → S¹`, `p(t) = (cos 2πt, sin 2πt) = e^{2πit}`, on `S¹` since `cos² + sin² = 1`
(Analysis I). The book's map of "Unwinding the circle". Mathlib: `Circle.exp` (up to the
factor `2π`), `AddCircle`. -/
def p (t : ℝ) : S1 := ⟨(cos (2 * π * t), sin (2 * π * t)), by simp [S1]⟩

/-- Unfolding: `p(t)`, as a point of the plane, is `(cos 2πt, sin 2πt)`. -/
@[simp] theorem coe_p (t : ℝ) : (p t : ℝ × ℝ) = (cos (2 * π * t), sin (2 * π * t)) := rfl

/-- `p` is continuous: `cos` and `sin` are (Analysis I), through the bridges `real_toMathlib`
and `S1_toMathlib`. Mathlib: `Circle.exp`'s continuity, `Real.continuous_cos`. -/
theorem continuous_p : Continuous p :=
  continuous_of_mathlib_eq real_toMathlib S1_toMathlib (Continuous.subtype_mk (by fun_prop) _)

/-- `p(0) = 1`. -/
@[simp] theorem p_zero : p 0 = 1 := S1.ext' (by simp) (by simp)

/-- `p(t + n) = p(t)` for an integer `n`: `cos` and `sin` have period `2π` (Analysis I).
Mathlib: `Real.cos_add_int_mul_two_pi`. -/
theorem p_add_int (t : ℝ) (n : ℤ) : p (t + n) = p t := by
  -- `2π(t + n) = 2πt + n·2π`, and `cos`, `sin` do not change when `n·2π` is added. (Lean:
  -- `(n : ℝ)`, printed `↑n`, is the integer `n` seen as a real number.)
  have e : 2 * π * (t + n) = 2 * π * t + n * (2 * π) := by ring
  exact S1.ext' (by simp only [coe_p, e, cos_add_int_mul_two_pi])
    (by simp only [coe_p, e, sin_add_int_mul_two_pi])

/-- `p(n) = 1` for an integer `n`: `p(0 + n) = p(0) = 1`. -/
theorem p_int (n : ℤ) : p n = 1 := by simpa using p_add_int 0 n

/-- `p(1/2 + t) = -p(t)`: half a turn is the antipode, since `cos(θ + π) = -cos θ` and
`sin(θ + π) = -sin θ` (Analysis I). -/
theorem p_add_half (t : ℝ) : p (1 / 2 + t) = -p t := by
  have e : 2 * π * (1 / 2 + t) = 2 * π * t + π := by ring
  exact S1.ext' (by simp only [coe_p, S1.coe_neg, e, cos_add_pi])
    (by simp only [coe_p, S1.coe_neg, e, sin_add_pi])

/-- `p(t) = p(t')` exactly when `t' - t ∈ ℤ` (the book, "Unwinding the circle", stated before
`prop:evenly-covered`). Mathlib: `Circle.exp_eq_exp`, `AddCircle`. -/
theorem p_eq_iff {t t' : ℝ} : p t = p t' ↔ ∃ n : ℤ, t' - t = n := by
  constructor
  · -- (⇒) Suppose `p(t) = p(t')`. Comparing coordinates, `cos 2πt = cos 2πt'` and
    -- `sin 2πt = sin 2πt'`.
    intro h
    have h1 : cos (2 * π * t) = cos (2 * π * t') := congrArg (fun z : S1 => z.1.1) h
    have h2 : sin (2 * π * t) = sin (2 * π * t') := congrArg (fun z : S1 => z.1.2) h
    -- So `cos(2πt' - 2πt) = cos 2πt' cos 2πt + sin 2πt' sin 2πt = cos² 2πt + sin² 2πt = 1`.
    have hc : cos (2 * π * t' - 2 * π * t) = 1 := by
      rw [cos_sub, ← h1, ← h2]; nlinarith [sin_sq_add_cos_sq (2 * π * t)]
    -- `cos x = 1` only for `x = n·2π`, `n ∈ ℤ` (Analysis I); so `2π(t' - t) = n·2π`, and
    -- dividing by `2π > 0`, `t' - t = n`.
    obtain ⟨n, hn⟩ := (cos_eq_one_iff _).mp hc
    refine ⟨n, ?_⟩
    have hπ : (0 : ℝ) < π := pi_pos
    have : (n : ℝ) * (2 * π) = (t' - t) * (2 * π) := by rw [hn]; ring
    exact (mul_right_cancel₀ (by positivity) this).symm
  · -- (⇐) If `t' = t + n`, then `p(t') = p(t + n) = p(t)` (`p_add_int`).
    rintro ⟨n, hn⟩
    rw [show t' = t + n by linarith, p_add_int]

/-! ## Evenly covered arcs (`prop:evenly-covered`, `def:evenly-covered`) -/

/-- The two arcs used by the lifting proofs: `arc false = S¹ \ {-1}` (`x > -1`) and
`arc true = S¹ \ {1}` (`x < 1`), the book's two evenly covered arcs in `thm:path-lifting`.

Lean: `Bool` is the two-element set `{false, true}`, used here only to name the two arcs; the
definition is by cases, one line for each. `{z | -1 < z.1.1}` is the set of `z` with `x > -1`. -/
def arc : Bool → Set S1
  | false => {z | -1 < z.1.1}
  | true => {z | z.1.1 < 1}

/-- The two arcs cover `S¹`: every point `z = (x, y)` has `x > -1` or `x < 1`. -/
theorem arc_cover (z : S1) : ∃ b, z ∈ arc b := by
  -- If `x > -1`, `z` is in the first arc; otherwise `x ≤ -1 < 1`, and it is in the second.
  by_cases h : -1 < z.1.1
  · exact ⟨false, h⟩
  · exact ⟨true, show z.1.1 < 1 by linarith⟩

/-- Analysis I, the half-angle formula: for `x² + y² = 1` with `x > -1`, the angle
`2 arctan(y / (1 + x))` has cosine `x` and sine `y`. Mathlib: `Real.cos_sq_arctan`,
`Real.sin_arctan`, `Real.cos_arctan`, `Real.cos_two_mul`, `Real.sin_two_mul`. -/
theorem half_angle {x y : ℝ} (hxy : x ^ 2 + y ^ 2 = 1) (hx : -1 < x) :
    cos (2 * arctan (y / (1 + x))) = x ∧ sin (2 * arctan (y / (1 + x))) = y := by
  -- Put `u = y / (1 + x)` and `θ = arctan u`, so `tan θ = u`. (Lean: `set` names an expression.)
  set u := y / (1 + x) with hu
  have h1x : 0 < 1 + x := by linarith
  -- `1 + u² = ((1 + x)² + y²)/(1 + x)² = (2 + 2x)/(1 + x)² = 2/(1 + x)`, using `x² + y² = 1`.
  have hu2 : 1 + u ^ 2 = 2 / (1 + x) := by
    rw [hu, div_pow]; field_simp; nlinarith
  -- So `cos² θ = 1/(1 + tan² θ) = (1 + x)/2`.
  have hc2 : cos (arctan u) ^ 2 = (1 + x) / 2 := by
    rw [cos_sq_arctan, hu2]; field_simp
  -- And `sin θ = tan θ · cos θ = u cos θ`.
  have hsc : sin (arctan u) = u * cos (arctan u) := by
    rw [sin_arctan, cos_arctan]; ring
  -- The cosine: `cos 2θ = 2 cos² θ - 1 = (1 + x) - 1 = x`.
  -- The sine: `sin 2θ = 2 sin θ cos θ = 2u cos² θ = 2 · y/(1 + x) · (1 + x)/2 = y`.
  constructor
  · rw [cos_two_mul, hc2]; ring
  · rw [sin_two_mul, hsc,
      show 2 * (u * cos (arctan u)) * cos (arctan u) = 2 * u * cos (arctan u) ^ 2 by ring, hc2, hu]
    field_simp

/-- The inverse `σ` of `p` on each arc (`prop:evenly-covered`), landing in `(-1/2, 1/2)` over
`S¹ \ {-1}` and in `(0, 1)` over `S¹ \ {1}`: on the first, `σ(x, y) = arctan(y / (1 + x)) / π`
(the half-angle formula: `p(σ(z)) = (cos 2θ, sin 2θ)` with `θ = arctan(y / (1 + x))`); on the
second, `σ(z) = 1/2 + σ(-z)`, half a turn after the antipode, which is in the first arc. The
formula makes sense on all of `S¹` (Lean divides by `0` to give `0`), but it is an inverse of
`p` only on the arc. -/
def sec : Bool → S1 → ℝ
  | false, z => arctan (z.1.2 / (1 + z.1.1)) / π
  | true, z => 1 / 2 + arctan (-z.1.2 / (1 + -z.1.1)) / π

/-- `prop:evenly-covered`: `σ` is a right inverse of `p` on its arc: `p(σ(z)) = z` for `z` in
the arc (`hz`). -/
theorem p_sec {b : Bool} {z : S1} (hz : z ∈ arc b) : p (sec b z) = z := by
  have hπ : π ≠ 0 := pi_ne_zero
  cases b with
  | false =>
    -- On `S¹ \ {-1}`: `2π σ(z) = 2θ` with `θ = arctan(y / (1 + x))`, and `cos 2θ = x`,
    -- `sin 2θ = y` by the half-angle formula (`half_angle`), as `x > -1`.
    have h := half_angle (S1.sq_add_sq z) hz
    exact S1.ext' (by simp only [coe_p, sec]; rw [show 2 * π * (arctan (z.1.2 / (1 + z.1.1)) / π)
      = 2 * arctan (z.1.2 / (1 + z.1.1)) by field_simp]; exact h.1)
      (by simp only [coe_p, sec]; rw [show 2 * π * (arctan (z.1.2 / (1 + z.1.1)) / π)
      = 2 * arctan (z.1.2 / (1 + z.1.1)) by field_simp]; exact h.2)
  | true =>
    -- On `S¹ \ {1}`: `-z = (-x, -y)` has `-x > -1`, so by the first case `p(σ(-z)) = -z`;
    -- then `p(1/2 + σ(-z)) = -p(σ(-z)) = -(-z) = z` (`p_add_half`).
    have hz' : -1 < -z.1.1 := by simp only [arc, mem_ofPred_eq] at hz; linarith
    have h := half_angle (x := -z.1.1) (y := -z.1.2) (by nlinarith [(S1.sq_add_sq z)]) hz'
    have e : p (arctan (-z.1.2 / (1 + -z.1.1)) / π) = -z := by
      refine S1.ext' ?_ ?_ <;> simp only [coe_p, S1.coe_neg] <;>
        rw [show 2 * π * (arctan (-z.1.2 / (1 + -z.1.1)) / π)
          = 2 * arctan (-z.1.2 / (1 + -z.1.1)) by field_simp]
      · exact h.1
      · exact h.2
    simp only [sec]
    rw [p_add_half, e]
    exact S1.ext' (by simp) (by simp)

/-- The arcs are open in `S¹`: each is cut out by a strict inequality in the coordinate `x`
(Analysis I, through `S1_toMathlib`). -/
theorem isOpen_arc (b : Bool) : IsOpen (arc b) := by
  -- In Mathlib's terms, `{x > -1}` and `{x < 1}` are `{f < g}` for continuous `f`, `g`.
  rw [isOpen_iff_mathlib, S1_toMathlib]
  cases b
  · exact isOpen_lt _root_.continuous_const (by fun_prop)
  · exact isOpen_lt (by fun_prop) _root_.continuous_const

/-- `prop:evenly-covered`: `σ` is continuous on its arc (Analysis I: `arctan`, division where
the denominator `1 ± x` is positive), through the bridges.

Lean: `z : arc b` is a point of the arc with its proof of membership, `z.1` the point of `S¹`
and `z.2` the proof; so the map is `σ` restricted to the arc. -/
theorem continuous_sec (b : Bool) : Continuous (fun z : arc b => sec b z.1) := by
  refine continuous_of_mathlib_eq (subS1_toMathlib _) real_toMathlib ?_
  cases b with
  | false =>
    -- `z ↦ arctan(y / (1 + x)) / π` is continuous where `1 + x ≠ 0`, and on the arc `x > -1`.
    refine continuous_arctan.comp
      ((by fun_prop : _root_.Continuous fun z : arc false => z.1.1.2).div
        (by fun_prop) fun z => ?_) |>.div_const _
    have : -1 < z.1.1.1 := z.2; linarith
  | true =>
    -- `z ↦ 1/2 + arctan(-y / (1 - x)) / π` is continuous where `1 - x ≠ 0`; on the arc `x < 1`.
    refine _root_.continuous_const.add (continuous_arctan.comp
      ((by fun_prop : _root_.Continuous fun z : arc true => -z.1.1.2).div
      (by fun_prop) fun z => ?_) |>.div_const _)
    have : z.1.1.1 < 1 := z.2; linarith

/-- `prop:evenly-covered`: the preimage of an arc is the disjoint union of the integer
translates of `σ`'s image, its sheets: over a point `z` of the arc, `p(t) = z` exactly when
`t = σ(z) + n` for an integer `n`, and `n` is unique. Mathlib: `IsEvenlyCovered`,
`IsCoveringMap`. -/
theorem p_eq_iff_of_mem_arc {b : Bool} {z : S1} (hz : z ∈ arc b) (t : ℝ) :
    p t = z ↔ ∃ n : ℤ, t = sec b z + n := by
  -- `z = p(σ(z))`, so `p(t) = z` iff `p(t) = p(σ(z))` iff `t - σ(z) ∈ ℤ` (`p_eq_iff`).
  have hs := p_sec hz
  constructor
  · intro h
    obtain ⟨n, hn⟩ := p_eq_iff.mp (hs.trans h.symm)
    exact ⟨n, by linarith⟩
  · rintro ⟨n, hn⟩
    rw [hn, p_add_int, hs]

/-! ## Lifts and `lem:integer-difference` -/

/-- `def:lift-circle`: a lift of `f : Y → S¹` is a continuous `f̃ : Y → ℝ` with `p ∘ f̃ = f`.
Mathlib: `IsCoveringMap.liftPath` and the lifting predicates of `IsCoveringMap`.

Lean: `IsLift f g` is a statement (a `Prop`), "`g` is a lift of `f`"; a proof `hg` of it is a
pair, `hg.1` that `g` is continuous and `hg.2` that `p(g(y)) = f(y)` for every `y`. -/
def IsLift [TopSpace Y] (f : Y → S1) (g : Y → ℝ) : Prop := Continuous g ∧ ∀ y, p (g y) = f y

/-! ### Tools: real-valued maps, maps into a subspace, gluing along `u = c`, clamping in `I`

Small facts the lifting proofs use. The clamp `I.clamp a b` squeezes `I` onto `[a, b]`; a map on
the strip `[a, b] × I` composed with it becomes a map on all of `I × I`, which is how the proofs
below work with one column or one row of the grid at a time. -/

section Tools

/-- A real-valued map is continuous in the course's sense iff in Mathlib's (`real_toMathlib`). -/
theorem continuous_real_iff [t : TopSpace X] {g : X → ℝ} :
    Continuous g ↔ @_root_.Continuous X ℝ t.toMathlib _ g := by
  rw [continuous_iff_mathlib, real_toMathlib]

/-- `x ↦ g(x) + c` is continuous if `g` is (Analysis I). -/
theorem Continuous.add_const_real [t : TopSpace X] {g : X → ℝ} (hg : Continuous g) (c : ℝ) :
    Continuous (fun x => g x + c) := by
  -- Pass to Mathlib's continuity, where sums of continuous maps are continuous. (Lean: `let _`
  -- equips `X` with Mathlib's version of its topology for the rest of the proof.)
  let _ := t.toMathlib
  exact continuous_real_iff.mpr ((continuous_real_iff.mp hg).add _root_.continuous_const)

/-- `prop-1-15`: a map into a subspace is continuous if it is continuous into the whole space.
Mathlib: `Continuous.subtype_mk`. -/
theorem continuous_subtype_mk' [TopSpace X] [TopSpace Y] {A : Set Y} {g : X → Y}
    (hg : Continuous g) (h : ∀ x, g x ∈ A) : Continuous (fun x => (⟨g x, h x⟩ : A)) := by
  -- An open set of the subspace `A` is `U ∩ A` with `U` open in `Y` (`def-1-14`); its preimage
  -- is `g⁻¹(U)`, open since `g` is continuous.
  rintro _ ⟨U, hU, rfl⟩
  exact hg U hU

/-- `prop-1-20`, the gluing lemma, for the closed pieces `u ≤ c` and `u ≥ c` of `X`, where
`u : X → ℝ` is continuous; the half-lines are closed in `ℝ` (Analysis I). If `f = g` where
`u = c` (`hfg`), the map equal to `f` where `u ≤ c` and to `g` where `u > c` is continuous.
Lean: `if P then a else b` is "`a` if `P` holds, `b` otherwise". -/
theorem continuous_glue_le [TopSpace X] [TopSpace Y] {u : X → ℝ} (hu : Continuous u) (c : ℝ)
    {f g : X → Y} (hf : Continuous f) (hg : Continuous g) (hfg : ∀ x, u x = c → f x = g x) :
    Continuous (fun x => if u x ≤ c then f x else g x) := by
  -- The pieces `C₁ = u⁻¹(-∞, c]` and `C₂ = u⁻¹[c, ∞)` are closed, as preimages of closed
  -- half-lines, and they cover `X`.
  have hC₁ : IsClosed {r : ℝ | r ≤ c} :=
    isClosed_of_mathlib_eq real_toMathlib (isClosed_le _root_.continuous_id _root_.continuous_const)
  have hC₂ : IsClosed {r : ℝ | c ≤ r} :=
    isClosed_of_mathlib_eq real_toMathlib (isClosed_le _root_.continuous_const _root_.continuous_id)
  refine continuous_of_closed_cover (C₁ := u ⁻¹' {r | r ≤ c}) (C₂ := u ⁻¹' {r | c ≤ r})
    (continuous_iff_isClosed.mp hu _ hC₁) (continuous_iff_isClosed.mp hu _ hC₂)
    (eq_univ_of_forall fun x => (le_total (u x) c).imp id id) ?_ ?_
  -- On `C₁` the glued map is `f`, continuous.
  · have : (fun x : (u ⁻¹' {r | r ≤ c}) => if u x ≤ c then f x else g x) = fun x => f x.1 := by
      funext x
      have hx : u x ≤ c := x.2
      simp only [hx, ite_true]
    rw [this]
    exact hf.comp continuous_subtype_val
  -- On `C₂` it is `g`: where `u > c` by definition, and where `u = c` because `f = g` there.
  · have : (fun x : (u ⁻¹' {r | c ≤ r}) => if u x ≤ c then f x else g x) = fun x => g x.1 := by
      funext x
      have hx : c ≤ u x := x.2
      by_cases h : u x ≤ c
      · simp only [h, ite_true]; exact hfg x (le_antisymm h hx)
      · simp only [h, ite_false]
    rw [this]
    exact hg.comp continuous_subtype_val

namespace I

/-- The point of `I` nearest to `x ∈ ℝ`: `0` if `x < 0`, `1` if `x > 1`, `x` otherwise.
Mathlib: `Set.projIcc`. -/
def pt (x : ℝ) : I := Set.projIcc 0 1 zero_le_one x

/-- If `0 ≤ x ≤ 1`, the nearest point is `x` itself. -/
theorem coe_pt {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) : (pt x : ℝ) = x := by
  rw [pt, Set.coe_projIcc, min_eq_right h1, max_eq_right h0]

/-- The clamp `s ↦ max(a, min(s, b))` of `I` onto `[a, b]`: it fixes `[a, b]`, sends `[0, a]`
to `a` and `[b, 1]` to `b`. -/
def clamp (a b : ℝ) (s : I) : I := pt (max a (min (s : ℝ) b))

/-- Unfolding: for `0 ≤ a ≤ b ≤ 1`, the clamp of `s` is `max(a, min(s, b))`. -/
theorem coe_clamp {a b : ℝ} (h0 : 0 ≤ a) (hab : a ≤ b) (h1 : b ≤ 1) (s : I) :
    (clamp a b s : ℝ) = max a (min (s : ℝ) b) :=
  coe_pt (le_max_of_le_left h0) (max_le (by linarith) (min_le_of_right_le h1))

/-- The clamp is continuous (Analysis I: `min`, `max`, `Set.projIcc`). -/
theorem continuous_clamp (a b : ℝ) : Continuous (clamp a b) :=
  continuous_of_mathlib_eq I_toMathlib I_toMathlib (continuous_projIcc.comp (by fun_prop))

/-- The clamp lands in `[a, b]`. -/
theorem mem_clamp {a b : ℝ} (h0 : 0 ≤ a) (hab : a ≤ b) (h1 : b ≤ 1) (s : I) :
    a ≤ (clamp a b s : ℝ) ∧ (clamp a b s : ℝ) ≤ b := by
  rw [coe_clamp h0 hab h1]; exact ⟨le_max_left _ _, max_le hab (min_le_right _ _)⟩

/-- The clamp fixes the points of `[a, b]`. -/
theorem clamp_of_mem {a b : ℝ} (h0 : 0 ≤ a) (hab : a ≤ b) (h1 : b ≤ 1) {s : I}
    (hs1 : a ≤ (s : ℝ)) (hs2 : (s : ℝ) ≤ b) : clamp a b s = s :=
  Subtype.ext (by rw [coe_clamp h0 hab h1, min_eq_left hs2, max_eq_right hs1])

/-- For `s ≥ a`, clamping onto `[a, b]` and onto `[0, b]` give the same point. -/
theorem clamp_eq_clamp {a b : ℝ} (h0 : 0 ≤ a) (hab : a ≤ b) (h1 : b ≤ 1) {s : I}
    (hs : a ≤ (s : ℝ)) : clamp a b s = clamp 0 b s :=
  Subtype.ext (by
    rw [coe_clamp h0 hab h1, coe_clamp le_rfl (h0.trans hab) h1, max_eq_right (le_min hs hab),
      max_eq_right (h0.trans (le_min hs hab))])

/-- Clamping onto `[0, 0]` sends everything to `0`. -/
theorem clamp_zero_zero (s : I) : clamp 0 0 s = 0 :=
  Subtype.ext (by rw [coe_clamp le_rfl le_rfl zero_le_one, min_eq_right s.2.1, max_self,
    Set.Icc.coe_zero])

/-- Clamping onto `[0, 1] = I` is the identity. -/
theorem clamp_zero_one (s : I) : clamp 0 1 s = s :=
  clamp_of_mem le_rfl zero_le_one le_rfl s.2.1 s.2.2

end I

/-- The `j`-th division point `j / N` and the next, `(j + 1)/N`, for `j + 1 ≤ N`: they satisfy
`0 ≤ j/N ≤ (j + 1)/N ≤ 1`. (Lean: `(j : ℝ)` is the natural number `j` seen as a real number.) -/
theorem grid_facts {j N : ℕ} (hN : 0 < N) (hj : j + 1 ≤ N) :
    0 ≤ (j : ℝ) / N ∧ (j : ℝ) / N ≤ ((j : ℝ) + 1) / N ∧ ((j : ℝ) + 1) / N ≤ 1 := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  refine ⟨by positivity, by gcongr; linarith, (div_le_one hN').mpr (by exact_mod_cast hj)⟩

end Tools

/-- Analysis I: `I` is connected (Mathlib: `unitInterval`'s `ConnectedSpace` instance), through
the bridge `I_toMathlib`. -/
theorem preconnected_I : @PreconnectedSpace I (subspace I).toMathlib := by
  rw [I_toMathlib]; infer_instance

/-- Analysis I: `I × I` is connected (Mathlib: `Prod.instConnectedSpace`), through the bridge
`II_toMathlib`. -/
theorem preconnected_II : @PreconnectedSpace (I × I) (prod : TopSpace (I × I)).toMathlib := by
  rw [II_toMathlib]; infer_instance

/-- **`lem:integer-difference`**: if `Y` is connected and `f̃₁, f̃₂ : Y → ℝ` are continuous with
`p f̃₁ = p f̃₂` and `f̃₁(y₀) = f̃₂(y₀)`, then `f̃₁ = f̃₂`. Mathlib: `IsSeparatedMap.eq_of_comp_eq`.

In Lean `f̃₁, f̃₂` are `g₁, g₂`; `hp` says `p(g₁(y)) = p(g₂(y))` for every `y`, `h0` that they
agree at `y₀`, and the conclusion is `g₁(y) = g₂(y)` for every `y`. `hY` says `Y` is connected,
in Mathlib's sense (`PreconnectedSpace`, which allows `Y` to be empty), for Mathlib's version of
`Y`'s topology (`t.toMathlib`).

The book's proof: `f̃₂ - f̃₁` takes integer values, so, continuous on a connected space, it is
constant. Here "constant" is the intermediate value theorem (Analysis I, Mathlib's
`intermediate_value_univ`): a value `n ≠ 0` would force the non-integer `± 1/2` to be a value
too. -/
theorem lift_eq_of_preconnected [t : TopSpace Y] (hY : @PreconnectedSpace Y t.toMathlib)
    {g₁ g₂ : Y → ℝ} (h₁ : Continuous g₁) (h₂ : Continuous g₂) (hp : ∀ y, p (g₁ y) = p (g₂ y))
    {y₀ : Y} (h0 : g₁ y₀ = g₂ y₀) (y : Y) : g₁ y = g₂ y := by
  let _ := t.toMathlib
  -- Step 1. `d = g₂ - g₁` is continuous (Analysis I, through the bridge).
  have hd : _root_.Continuous (fun y => g₂ y - g₁ y) :=
    (continuous_real_iff.mp h₂).sub (continuous_real_iff.mp h₁)
  -- Step 2. `d` takes integer values: `p(g₁(y)) = p(g₂(y))` means `g₂(y) - g₁(y) ∈ ℤ`
  -- (`p_eq_iff`).
  have hint : ∀ y, ∃ n : ℤ, g₂ y - g₁ y = n := fun y => p_eq_iff.mp (hp y)
  -- Step 3. So `d` never takes the values `1/2` and `-1/2`: `2m = ±1` has no integer solution.
  -- (Lean: `constructor <;> intro h` splits the "and" into two goals and assumes, in each, the
  -- equation `h` to be refuted; `omega` settles statements about integers.)
  have half : ∀ z, g₂ z - g₁ z ≠ 1 / 2 ∧ g₂ z - g₁ z ≠ -1 / 2 := by
    intro z
    obtain ⟨m, hm⟩ := hint z
    rw [hm]
    constructor <;> intro h
    · have : ((2 * m : ℤ) : ℝ) = 1 := by push_cast; linarith
      have : 2 * m = 1 := by exact_mod_cast this
      omega
    · have : ((2 * m : ℤ) : ℝ) = -1 := by push_cast; linarith
      have : 2 * m = -1 := by exact_mod_cast this
      omega
  -- Step 4. Let `y ∈ Y`, with `d(y) = n ∈ ℤ`; we know `d(y₀) = 0`. Suppose `g₁(y) ≠ g₂(y)`;
  -- then `n ≠ 0`. (Lean: `by_contra hne` assumes the negation `hne` of the goal and asks for a
  -- contradiction.)
  obtain ⟨n, hn⟩ := hint y
  have hy0 : g₂ y₀ - g₁ y₀ = 0 := by rw [h0]; ring
  by_contra hne
  have hn0 : n ≠ 0 := by
    rintro rfl; apply hne; simp only [Int.cast_zero] at hn; linarith
  rcases lt_or_gt_of_ne hn0 with hneg | hpos
  -- Step 5, `n < 0`: then `d(y) = n ≤ -1 < -1/2 < 0 = d(y₀)`, so by the intermediate value
  -- theorem on the connected `Y` (Analysis I), `d(z) = -1/2` for some `z`, against Step 3.
  · have hle : (n : ℝ) ≤ -1 := by exact_mod_cast (show n ≤ -1 by omega)
    obtain ⟨z, hz⟩ := intermediate_value_univ y y₀ hd
      (show (-1 / 2 : ℝ) ∈ Icc _ _ from ⟨by rw [hn]; linarith, by rw [hy0]; norm_num⟩)
    exact (half z).2 hz
  -- Step 5, `n > 0`: likewise `d(y₀) = 0 < 1/2 < 1 ≤ d(y)`, so `d(z) = 1/2` for some `z`.
  · have hle : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
    obtain ⟨z, hz⟩ := intermediate_value_univ y₀ y hd
      (show (1 / 2 : ℝ) ∈ Icc _ _ from ⟨by rw [hy0]; norm_num, by rw [hn]; linarith⟩)
    exact (half z).1 hz

/-- `lem:integer-difference` for `Y = I`, which is connected: two lifts `I → ℝ` of the same
path that agree at one point `s₀` agree everywhere. -/
theorem lift_eq_I {g₁ g₂ : I → ℝ} (h₁ : Continuous g₁) (h₂ : Continuous g₂)
    (hp : ∀ s, p (g₁ s) = p (g₂ s)) {s₀ : I} (h0 : g₁ s₀ = g₂ s₀) (s : I) : g₁ s = g₂ s :=
  lift_eq_of_preconnected preconnected_I h₁ h₂ hp h0 s

/-- `lem:integer-difference` for `Y = I × I`, which is connected. -/
theorem lift_eq_II {g₁ g₂ : I × I → ℝ} (h₁ : Continuous g₁) (h₂ : Continuous g₂)
    (hp : ∀ q, p (g₁ q) = p (g₂ q)) {q₀ : I × I} (h0 : g₁ q₀ = g₂ q₀) (q : I × I) :
    g₁ q = g₂ q :=
  lift_eq_of_preconnected preconnected_II h₁ h₂ hp h0 q

/-! ## Path lifting (`thm:path-lifting`) -/

/-- The Lebesgue number lemma on `I` (Analysis I: `I` is compact, Mathlib's
`lebesgue_number_lemma_of_metric`, through `isOpen_I_iff`), for the cover of `I` by the
preimages of the two arcs under `f`: for some `N ≥ 1`, `f` carries each `[j/N, (j+1)/N]`,
`j < N`, into one of the arcs. This replaces the book's chain of intervals in
`thm:path-lifting`. -/
theorem exists_grid_I {f : I → S1} (hf : Continuous f) :
    ∃ N : ℕ, 0 < N ∧ ∀ j : ℕ, j < N → ∃ b, ∀ s : I, (j : ℝ) / N ≤ s →
      (s : ℝ) ≤ ((j : ℝ) + 1) / N → f s ∈ arc b := by
  -- The sets `f⁻¹(arc b)` are open in `I` (`f` is continuous, the arcs are open) and cover it.
  -- So there is `δ > 0` such that every ball `B(s, δ)` of `I` lies in one of them (Analysis I).
  obtain ⟨δ, hδ, hball⟩ := lebesgue_number_lemma_of_metric (isCompact_univ (X := unitInterval))
    (c := fun b => f ⁻¹' arc b) (fun b => (isOpen_I_iff _).mp (hf _ (isOpen_arc b)))
    (fun s _ => mem_iUnion.mpr (arc_cover (f s)))
  -- Take `N = n + 1` with `1/(n + 1) < δ` (Analysis I: the Archimedean property).
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hδ
  refine ⟨n + 1, n.succ_pos, fun j hj => ?_⟩
  obtain ⟨h0, h01, h1⟩ := grid_facts n.succ_pos hj
  -- The ball of radius `δ` about `j/N` lies in some `f⁻¹(arc b)`; and every `s` in
  -- `[j/N, (j + 1)/N]` is within `1/N < δ` of `j/N`, so `f(s) ∈ arc b`.
  obtain ⟨b, hb⟩ := hball (I.pt ((j : ℝ) / (n + 1 : ℕ))) (mem_univ _)
  refine ⟨b, fun s hs1 hs2 => hb ?_⟩
  have e : ((j : ℝ) + 1) / (n + 1 : ℕ) = (j : ℝ) / (n + 1 : ℕ) + 1 / ((n : ℝ) + 1) := by
    push_cast; ring
  rw [Metric.mem_ball, Subtype.dist_eq, Real.dist_eq, I.coe_pt h0 (h01.trans h1), abs_lt]
  constructor <;> linarith

/-- The heart of both lifting theorems (`thm:path-lifting`, `thm:homotopy-lifting`): a
continuous map `G : I × I → S¹` that carries each column `[j/N, (j+1)/N] × I` into an arc
(`hcol`), and has a lift `ℓ` along its left edge (`hpℓ`: `p(ℓ(t)) = G(0, t)`), has a lift `L`
with `L(0, t) = ℓ(t)`.

The proof is the book's "lifting piece by piece", a column at a time from the left: over column
`j`, take the inverse `σ` of `p` on the arc, moved by the integer that makes it agree with the
lift already built at the point `(j/N, 0)` (that is, the inverse of `p` on the sheet through
that point); the two then agree along the whole edge `{j/N} × I` by `lem:integer-difference`,
and the gluing lemma (`prop-1-20`) assembles them. -/
theorem strip_lift {G : I × I → S1} (hG : Continuous G) {N : ℕ} (hN : 0 < N)
    (hcol : ∀ j : ℕ, j < N → ∃ b, ∀ q : I × I, (j : ℝ) / N ≤ q.1 →
      (q.1 : ℝ) ≤ ((j : ℝ) + 1) / N → G q ∈ arc b)
    {ℓ : I → ℝ} (hℓ : Continuous ℓ) (hpℓ : ∀ t, p (ℓ t) = G (0, t)) :
    ∃ L : I × I → ℝ, Continuous L ∧ (∀ q, p (L q) = G q) ∧ ∀ t, L (0, t) = ℓ t := by
  -- The claim, by induction on `j ≤ N`: `G` restricted to the first `j` columns,
  -- `[0, j/N] × I`, has a lift `L` with `L(0, t) = ℓ(t)`. To keep every map defined on all of
  -- `I × I`, "`G` restricted to `[0, j/N] × I`" is written `(s, t) ↦ G(clamp(s), t)`, with the
  -- clamp of `I` onto `[0, j/N]`; it is `G` on the first `j` columns.
  have key : ∀ j : ℕ, j ≤ N → ∃ L : I × I → ℝ, Continuous L ∧
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
      -- `[a, a'] × I` with `a' = (j + 1)/N`, is carried by `G` into the arc `b`.
      intro hj
      obtain ⟨L, hL, hpL, hL0⟩ := ih (by omega)
      obtain ⟨b, hb⟩ := hcol j (by omega)
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
      -- `G` on the column `[a, a'] × I`, as the map `(s, t) ↦ G(clamp(s), t)`, lands in the arc.
      have hmem : ∀ q : I × I, G (I.clamp a a' q.1, q.2) ∈ arc b := fun q =>
        hb _ (I.mem_clamp ha0 haa' ha'1 q.1).1 (I.mem_clamp ha0 haa' ha'1 q.1).2
      -- The sheet: `L(a, 0)` and `σ(G(a, 0))` both lie over `G(a, 0)`, so they differ by an
      -- integer `n` (`p_eq_iff`); `σ + n` is the inverse of `p` on the sheet through `L(a, 0)`.
      obtain ⟨n, hn⟩ : ∃ n : ℤ, L (c, 0) - sec b (G (c, 0)) = n := by
        apply p_eq_iff.mp
        rw [hpL, hcl0, p_sec (hcl ▸ hmem (c, 0))]
      -- The lift of the column: `P(s, t) = σ(G(s, t)) + n`, for `(s, t) ∈ [a, a'] × I`.
      set P : I × I → ℝ := fun q => sec b (G (I.clamp a a' q.1, q.2)) +
        (L (c, 0) - sec b (G (c, 0))) with hP
      -- `P` is continuous: `σ` is continuous on the arc (`prop:evenly-covered`), `G` and the
      -- clamp are continuous, and adding a constant keeps continuity.
      have hPc : Continuous P :=
        ((continuous_sec b).comp (continuous_subtype_mk'
          (hG.comp (((I.continuous_clamp a a').comp continuous_fst).prodMk continuous_snd))
          hmem)).add_const_real _
      -- `P` is a lift: `p(σ(z) + n) = p(σ(z)) = z` (`p_add_int`, `p_sec`).
      have hpP : ∀ q, p (P q) = G (I.clamp a a' q.1, q.2) := by
        intro q; simp only [hP, hn, p_add_int, p_sec (hmem q)]
      -- The old lift `L` and the new `P` agree along the edge `{a} × I`: `t ↦ L(a, t)` and
      -- `t ↦ P(a, t)` both lift `t ↦ G(a, t)`, and agree at `t = 0` by the choice of `n`;
      -- so they are equal by `lem:integer-difference` (`lift_eq_I`).
      have hagree : ∀ q : I × I, (q.1 : ℝ) = a → L q = P q := by
        rintro ⟨s, t⟩ hs
        have hs' : s = c := Subtype.ext (hs.trans hcc.symm)
        subst hs'
        refine lift_eq_I (g₁ := fun t => L (c, t)) (g₂ := fun t => P (c, t))
          (hL.comp (continuous_const.prodMk continuous_id))
          (hPc.comp (continuous_const.prodMk continuous_id)) (fun t => ?_) (s₀ := 0) ?_ t
        -- Both lie over `G(a, t)`, since both clamps fix `a`.
        · simp only [hpL, hpP, hcl0, hcl]
        -- At `t = 0`: `P(a, 0) = σ(G(a, 0)) + (L(a, 0) - σ(G(a, 0))) = L(a, 0)`.
        · simp only [hP, hcl]; ring
      -- Glue: the new lift is `L` where `s ≤ a` and `P` where `s ≥ a`, continuous by the gluing
      -- lemma (`continuous_glue_le`, `prop-1-20`), since `L = P` where `s = a`.
      refine ⟨fun q => if (q.1 : ℝ) ≤ a then L q else P q,
        continuous_glue_le (continuous_subtype_val.comp continuous_fst) a hL hPc hagree,
        fun q => ?_, fun t => ?_⟩
      -- It lifts `G` on `[0, a'] × I`: for `s ≤ a` both clamps fix `s` and `L` lifts `G`
      -- there; for `s > a`, clamping onto `[a, a']` or onto `[0, a']` is the same, and `P`
      -- lifts `G` there.
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

/-- `p` is onto: some point of `ℝ` lies over each point `z` of `S¹`, namely `σ(z)` for the
inverse `σ` on an arc containing `z`. -/
theorem p_surjective (z : S1) : ∃ a, p a = z := by
  obtain ⟨b, hb⟩ := arc_cover z
  exact ⟨sec b z, p_sec hb⟩

/-- **`thm:path-lifting`**, existence: every path `f : I → S¹` has a lift `f̃` with `f̃(s₀) = a`,
for any point `s₀ ∈ I` and any `a` over `f(s₀)` (`ha : p(a) = f(s₀)`). The book takes
`s₀ = 0`; any `s₀` costs nothing more, and the homotopy lifting below uses `s₀ = k/N`.
Mathlib: `IsCoveringMap.exists_path_lifts`, `IsCoveringMap.liftPath`.

The book's proof, with the chain of intervals replaced by a grid of mesh `1/N` below a Lebesgue
number (Analysis I): lift along `[0, 1/N]`, `[1/N, 2/N]`, … by the inverses of `p` on the arcs
(`strip_lift`, for the map `(s, t) ↦ f(s)`), then move the lift by an integer to take the value
`a` at `s₀`. -/
theorem exists_lift_path {f : I → S1} (hf : Continuous f) (s₀ : I) (a : ℝ) (ha : p a = f s₀) :
    ∃ g : I → ℝ, IsLift f g ∧ g s₀ = a := by
  -- Step 1. A grid: `f` carries each `[j/N, (j + 1)/N]` into an arc (Lebesgue number).
  obtain ⟨N, hN, hgrid⟩ := exists_grid_I hf
  -- Step 2. Lift piece by piece from some `a₀` over `f(0)`: apply `strip_lift` to the map
  -- `(s, t) ↦ f(s)` of the square, which does not depend on `t`, with the constant `a₀` as the
  -- lift of its left edge. This gives `L` with `p(L(s, t)) = f(s)`. (Lean: `-` in a pattern
  -- discards a fact we do not need.)
  obtain ⟨a₀, ha₀⟩ := p_surjective (f 0)
  obtain ⟨L, hL, hpL, -⟩ := strip_lift (G := fun q => f q.1) (hf.comp continuous_fst) hN
    (fun j hj => (hgrid j hj).imp fun b hb q h1 h2 => hb q.1 h1 h2) (ℓ := fun _ => a₀)
    continuous_const (fun _ => ha₀)
  -- Step 3. `s ↦ L(s, 0)` is a lift of `f`. Both `L(s₀, 0)` and `a` lie over `f(s₀)`, so they
  -- differ by an integer `n`; then `f̃(s) = L(s, 0) + n` is a lift too (`p(t + n) = p(t)`),
  -- and `f̃(s₀) = a`.
  have hg₀ : Continuous (fun s : I => L (s, 0)) := hL.comp (continuous_id.prodMk continuous_const)
  obtain ⟨n, hn⟩ : ∃ n : ℤ, a - L (s₀, 0) = n := p_eq_iff.mp (by rw [hpL, ha])
  refine ⟨fun s => L (s, 0) + (a - L (s₀, 0)), ⟨hg₀.add_const_real _, fun s => ?_⟩, by ring⟩
  simp only [hn, p_add_int, hpL]

/-- **`thm:path-lifting`**, uniqueness: two lifts `g₁, g₂` of the same `f : I → S¹` that agree at
one point `s₀` are equal, by `lem:integer-difference`, `I` being connected: `p(g₁(s)) = f(s) =
p(g₂(s))` for every `s`. Mathlib: `IsSeparatedMap.eq_of_comp_eq`. (Lean: `funext` says that two
maps are equal if they agree at every point.) -/
theorem lift_path_unique {f : I → S1} {g₁ g₂ : I → ℝ} (h₁ : IsLift f g₁) (h₂ : IsLift f g₂)
    {s₀ : I} (h0 : g₁ s₀ = g₂ s₀) : g₁ = g₂ :=
  funext (lift_eq_I h₁.1 h₂.1 (fun s => by rw [h₁.2, h₂.2]) h0)

/-! ## Homotopy lifting (`thm:homotopy-lifting`) -/

/-- The Lebesgue number lemma on `I × I` (Analysis I: `I × I` is a compact metric space,
Mathlib's `lebesgue_number_lemma_of_metric`, through `II_toMathlib`): for some `N`, `F`
carries each square `[j/N, (j+1)/N] × [k/N, (k+1)/N]` of the grid into an arc. The proof is
that of `exists_grid_I`, in two coordinates; the distance on `I × I` is the larger of the
distances of the coordinates. -/
theorem exists_grid_II {F : I × I → S1} (hF : Continuous F) :
    ∃ N : ℕ, 0 < N ∧ ∀ j k : ℕ, j < N → k < N → ∃ b, ∀ q : I × I,
      (j : ℝ) / N ≤ q.1 → (q.1 : ℝ) ≤ ((j : ℝ) + 1) / N →
      (k : ℝ) / N ≤ q.2 → (q.2 : ℝ) ≤ ((k : ℝ) + 1) / N → F q ∈ arc b := by
  -- The sets `F⁻¹(arc b)` are open (in Mathlib's terms, through the bridge) and cover `I × I`;
  -- take a Lebesgue number `δ` (Analysis I) and `N` with `1/N < δ`. A point of the square
  -- with corner `(j/N, k/N)` is within `1/N` of that corner in each coordinate.
  have hopen : ∀ b, _root_.IsOpen (F ⁻¹' arc b) := fun b => by
    have := (isOpen_iff_mathlib _).mp (hF _ (isOpen_arc b))
    rwa [II_toMathlib] at this
  obtain ⟨δ, hδ, hball⟩ := lebesgue_number_lemma_of_metric
    (isCompact_univ (X := unitInterval × unitInterval)) (c := fun b => F ⁻¹' arc b) hopen
    (fun q _ => mem_iUnion.mpr (arc_cover (F q)))
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hδ
  refine ⟨n + 1, n.succ_pos, fun j k hj hk => ?_⟩
  obtain ⟨h0, h01, h1⟩ := grid_facts n.succ_pos hj
  obtain ⟨k0, k01, k1⟩ := grid_facts n.succ_pos hk
  obtain ⟨b, hb⟩ := hball (I.pt ((j : ℝ) / (n + 1 : ℕ)), I.pt ((k : ℝ) / (n + 1 : ℕ))) (mem_univ _)
  refine ⟨b, fun q hs1 hs2 ht1 ht2 => hb ?_⟩
  have e : ((j : ℝ) + 1) / (n + 1 : ℕ) = (j : ℝ) / (n + 1 : ℕ) + 1 / ((n : ℝ) + 1) := by
    push_cast; ring
  have e' : ((k : ℝ) + 1) / (n + 1 : ℕ) = (k : ℝ) / (n + 1 : ℕ) + 1 / ((n : ℝ) + 1) := by
    push_cast; ring
  rw [Metric.mem_ball, Prod.dist_eq, max_lt_iff, Subtype.dist_eq, Subtype.dist_eq, Real.dist_eq,
    Real.dist_eq, I.coe_pt h0 (h01.trans h1), I.coe_pt k0 (k01.trans k1), abs_lt, abs_lt]
  refine ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩

/-- **`thm:homotopy-lifting`**, existence: every continuous `F : I × I → S¹` has a lift `F̃`
with `F̃(0, 0) = a`, for any `a` over `F(0, 0)` (`ha : p(a) = F(0, 0)`).
Mathlib: `IsCoveringMap.liftHomotopy`.

The book's proof: a grid of squares, each carried by `F` into an evenly covered arc (Lebesgue
number, Analysis I), lifted row by row from the bottom. Row `k` is the strip
`I × [k/N, (k+1)/N]`, lifted square by square from the left (`strip_lift`) starting from the
lift of its left edge through the point already lifted at `(0, k/N)`; it agrees with the rows
below along `I × {k/N}` by `lem:integer-difference`, and the gluing lemma assembles the rows.
Where the book checks that the new square's lift agrees with the old on the part of its boundary
already lifted, here the agreement along a whole edge is `lem:integer-difference` for an
interval. -/
theorem exists_lift_homotopy {F : I × I → S1} (hF : Continuous F) (a : ℝ) (ha : p a = F (0, 0)) :
    ∃ G : I × I → ℝ, IsLift F G ∧ G (0, 0) = a := by
  -- Step 1. A grid: `F` carries each square of side `1/N` into an arc (Lebesgue number).
  obtain ⟨N, hN, hgrid⟩ := exists_grid_II hF
  -- Step 2, the claim, by induction on `k ≤ N`: `F` on the first `k` rows, `I × [0, k/N]`,
  -- has a lift `L` with `L(0, 0) = a`. As in `strip_lift`, "`F` on `I × [0, k/N]`" is the map
  -- `(s, t) ↦ F(s, clamp(t))` with the clamp of `I` onto `[0, k/N]`.
  have key : ∀ k : ℕ, k ≤ N → ∃ L : I × I → ℝ, Continuous L ∧
      (∀ q : I × I, p (L q) = F (q.1, I.clamp 0 ((k : ℝ) / N) q.2)) ∧ L (0, 0) = a := by
    intro k
    induction k with
    | zero =>
      -- `k = 0`: the map is `(s, t) ↦ F(s, 0)`. Lift the bottom edge `s ↦ F(s, 0)` from `a`
      -- (`thm:path-lifting`) to `g`; then `(s, t) ↦ g(s)` is the lift.
      intro _
      obtain ⟨g, ⟨hg, hpg⟩, hg0⟩ := exists_lift_path (f := fun s => F (s, 0))
        (hF.comp (continuous_id.prodMk continuous_const)) 0 a ha
      refine ⟨fun q => g q.1, hg.comp continuous_fst, fun q => ?_, hg0⟩
      simp only [Nat.cast_zero, zero_div, I.clamp_zero_zero]
      exact hpg q.1
    | succ k ih =>
      -- `k → k + 1`. By induction `L` lifts `F` on `I × [0, e]`, `e = k/N`; row `k` is
      -- `I × [e, e']`, `e' = (k + 1)/N`, and `c` is the point `e` of `I`.
      intro hk
      obtain ⟨L, hL, hpL, hL0⟩ := ih (by omega)
      obtain ⟨ha0, haa', ha'1⟩ := grid_facts hN hk
      set e : ℝ := (k : ℝ) / N with he
      set e' : ℝ := ((k : ℝ) + 1) / N with he'
      have hk' : ((k + 1 : ℕ) : ℝ) / N = e' := by rw [he']; push_cast; ring
      rw [hk']
      set c : I := I.pt e with hc
      have hcc : (c : ℝ) = e := I.coe_pt ha0 (haa'.trans ha'1)
      have hcl0 : I.clamp 0 e c = c :=
        I.clamp_of_mem le_rfl ha0 (haa'.trans ha'1) (hcc ▸ ha0) hcc.le
      have hcl : I.clamp e e' c = c := I.clamp_of_mem ha0 haa' ha'1 hcc.ge (hcc ▸ haa')
      -- Row `k`, as the map `G_k(s, t) = F(s, clamp(t))` with the clamp onto `[e, e']`.
      set Gk : I × I → S1 := fun q => F (q.1, I.clamp e e' q.2) with hGk
      have hGkc : Continuous Gk :=
        hF.comp (continuous_fst.prodMk ((I.continuous_clamp e e').comp continuous_snd))
      -- Its left edge `t ↦ G_k(0, t)`, lifted (`thm:path-lifting`) to `ℓ` through the point
      -- already lifted: `ℓ(e) = L(0, e)`, which lies over `F(0, e) = G_k(0, e)`.
      obtain ⟨ℓ, ⟨hℓ, hpℓ⟩, hℓc⟩ := exists_lift_path (f := fun t => Gk (0, t))
        (hGkc.comp (continuous_const.prodMk continuous_id)) c (L (0, c))
        (by simp only [hGk, hpL, hcl0, hcl])
      -- Lift the row square by square from the left (`strip_lift`), starting from `ℓ`: the
      -- squares of row `k` are carried into arcs (Step 1). This gives `M` with `M(0, t) = ℓ(t)`.
      obtain ⟨M, hM, hpM, hM0⟩ := strip_lift hGkc hN (fun j hj => (hgrid j k hj (by omega)).imp
        fun b hb q h1 h2 => hb _ h1 h2 (I.mem_clamp ha0 haa' ha'1 q.2).1
          (I.mem_clamp ha0 haa' ha'1 q.2).2) hℓ hpℓ
      -- The old lift `L` and the new `M` agree along the edge `I × {e}`: `s ↦ L(s, e)` and
      -- `s ↦ M(s, e)` both lift `s ↦ F(s, e)` and agree at `s = 0`; so they are equal by
      -- `lem:integer-difference` (`lift_eq_I`).
      have hagree : ∀ q : I × I, (q.2 : ℝ) = e → L q = M q := by
        rintro ⟨s, t⟩ ht
        have ht' : t = c := Subtype.ext (ht.trans hcc.symm)
        subst ht'
        refine lift_eq_I (g₁ := fun s => L (s, c)) (g₂ := fun s => M (s, c))
          (hL.comp (continuous_id.prodMk continuous_const))
          (hM.comp (continuous_id.prodMk continuous_const)) (fun s => ?_) (s₀ := 0) ?_ s
        -- Both lie over `F(s, k/N)`, since both clamps fix `k/N`.
        · simp only [hpL, hpM, hGk, hcl0, hcl]
        -- At `s = 0`: `M(0, k/N) = ℓ(k/N) = L(0, k/N)`, by the choice of `ℓ`.
        · simp only [hM0, hℓc]
      -- Glue: `L` where `t ≤ e`, `M` where `t ≥ e` (`continuous_glue_le`, `prop-1-20`). It lifts
      -- `F` on `I × [0, e']`, the clamps agreeing as in `strip_lift`, and at `(0, 0)` it is
      -- `L(0, 0) = a`.
      refine ⟨fun q => if (q.2 : ℝ) ≤ e then L q else M q,
        continuous_glue_le (continuous_subtype_val.comp continuous_snd) e hL hM hagree,
        fun q => ?_, ?_⟩
      · by_cases h : (q.2 : ℝ) ≤ e
        · simp only [h, ite_true, hpL]
          rw [I.clamp_of_mem le_rfl ha0 (haa'.trans ha'1) q.2.2.1 h,
            I.clamp_of_mem le_rfl (ha0.trans haa') ha'1 q.2.2.1 (h.trans haa')]
        · simp only [h, ite_false, hpM, hGk]
          rw [I.clamp_eq_clamp ha0 haa' ha'1 (le_of_lt (not_le.mp h))]
      · have h : ((0 : I) : ℝ) ≤ e := by simpa using ha0
        simp only [h, ite_true, hL0]
  -- Step 3. For `k = N` the clamp is the identity of `I`, and `L` lifts `F`.
  obtain ⟨L, hL, hpL, hL0⟩ := key N le_rfl
  have hNN : (N : ℝ) / N = 1 := div_self (by exact_mod_cast hN.ne')
  refine ⟨L, ⟨hL, fun q => ?_⟩, hL0⟩
  rw [hpL, hNN, I.clamp_zero_one]

/-- **`thm:homotopy-lifting`**, uniqueness: two lifts of the same `F : I × I → S¹` that agree at
one point are equal, by `lem:integer-difference`, `I × I` being connected. -/
theorem lift_homotopy_unique {F : I × I → S1} {G₁ G₂ : I × I → ℝ} (h₁ : IsLift F G₁)
    (h₂ : IsLift F G₂) {q₀ : I × I} (h0 : G₁ q₀ = G₂ q₀) : G₁ = G₂ :=
  funext (lift_eq_II h₁.1 h₂.1 (fun q => by rw [h₁.2, h₂.2]) h0)

/-- `thm:homotopy-lifting`, last part: if `F(s, t)` is constant in `t` for one `s` (`hs`), then
so is its lift `G`: `G(s, t) = G(s, 0)`. The book's proof: `t ↦ G(s, t)` and the constant path
at `G(s, 0)` lift the same constant path and agree at `t = 0`, so they are equal
(`lem:integer-difference`). Applied at `s = 0` and `s = 1`, it says that the lift of a path
homotopy is a path homotopy. Mathlib: `IsCoveringMap.liftHomotopyRel`. -/
theorem lift_edge_const {F : I × I → S1} {G : I × I → ℝ} (hG : IsLift F G) (s : I)
    (hs : ∀ t, F (s, t) = F (s, 0)) (t : I) : G (s, t) = G (s, 0) :=
  lift_eq_I (g₁ := fun t => G (s, t)) (g₂ := fun _ => G (s, 0))
    (hG.1.comp (continuous_const.prodMk continuous_id)) continuous_const
    (fun t => by simp only [hG.2, hs]) (s₀ := 0) rfl t

/-! ## The fundamental group of the circle (`def:degree-circle`, `thm:pi1-circle`)

The book's proof of `thm:pi1-circle`, in four parts: the degree `deg [f] = f̃(1)` is well defined
(`degLoop_eq_of_homotopic`), a homomorphism (`degLoop_trans`), onto (`degLoop_windLoop`) and one
to one (`homotopic_refl_of_degLoop_eq_zero`); `pi1Circle` puts them together. Here `f̃` is the
lift of the loop `f` at `1` that starts at `0`. A loop at `1` is a `Path (1 : S1) 1` (week 4). -/

/-- Every loop `f` at `1` has a lift starting at `0` (`thm:path-lifting`, as `p(0) = 1 = f(0)`).
(Lean: `f.toFun : I → S¹` is the map underlying the path `f`.) -/
theorem exists_loopLift (f : Path (1 : S1) 1) : ∃ g : I → ℝ, IsLift f.toFun g ∧ g 0 = 0 :=
  exists_lift_path f.continuous 0 0 (by rw [p_zero]; exact f.source.symm)

/-- `thm:pi1-circle`: the lift `f̃` of a loop `f` at `1` starting at `0`.
Mathlib: `IsCoveringMap.liftPath`.

Lean: `Classical.choose h`, for a proof `h` of `∃ g, P g`, is "a `g` with `P g`", chosen once and
for all; `Classical.choose_spec h` says that it has the property `P`. -/
def loopLift (f : Path (1 : S1) 1) : I → ℝ := Classical.choose (exists_loopLift f)

/-- `f̃` is a lift of `f`. -/
theorem loopLift_isLift (f : Path (1 : S1) 1) : IsLift f.toFun (loopLift f) :=
  (Classical.choose_spec (exists_loopLift f)).1

/-- `f̃(0) = 0`. -/
theorem loopLift_zero (f : Path (1 : S1) 1) : loopLift f 0 = 0 :=
  (Classical.choose_spec (exists_loopLift f)).2

/-- Any lift `g` of `f` with `g(0) = 0` is `f̃` (`thm:path-lifting`, uniqueness). -/
theorem loopLift_eq {f : Path (1 : S1) 1} {g : I → ℝ} (hg : IsLift f.toFun g) (h0 : g 0 = 0) :
    loopLift f = g :=
  lift_path_unique (loopLift_isLift f) hg (s₀ := 0) ((loopLift_zero f).trans h0.symm)

/-- The end `f̃(1)` lies in `p⁻¹(1) = ℤ`. -/
theorem exists_degLoop (f : Path (1 : S1) 1) : ∃ n : ℤ, loopLift f 1 = n := by
  -- `p(f̃(1)) = f(1) = 1 = p(0)`, so `f̃(1) - 0` is an integer (`p_eq_iff`).
  obtain ⟨n, hn⟩ := p_eq_iff.mp
    (show p 0 = p (loopLift f 1) by rw [p_zero, (loopLift_isLift f).2]; exact f.target.symm)
  exact ⟨n, by linarith⟩

/-- `def:degree-circle`, `thm:pi1-circle`: the degree of a loop `f` at `1`, the integer
`f̃(1)` (`= f̃(1) - f̃(0)`, as `f̃(0) = 0`). The book defines the degree of a map `φ : S¹ → S¹`
through the loop `s ↦ φ(e^{2πis})`; here it is defined for the loop itself. Mathlib v4.34.1 has
no degree of a circle map; the nearest are `IsCoveringMap.liftPath` and
`IsCoveringMap.liftPathQuotient`. -/
def degLoop (f : Path (1 : S1) 1) : ℤ := Classical.choose (exists_degLoop f)

/-- The degree, as a real number, is `f̃(1)`. -/
theorem coe_degLoop (f : Path (1 : S1) 1) : (degLoop f : ℝ) = loopLift f 1 :=
  (Classical.choose_spec (exists_degLoop f)).symm

/-- The degree is the end `g(1)` of any lift `g` of `f` starting at `0`: such a `g` is `f̃`. -/
theorem degLoop_eq_of_lift {f : Path (1 : S1) 1} {g : I → ℝ} (hg : IsLift f.toFun g)
    (h0 : g 0 = 0) : (degLoop f : ℝ) = g 1 := by
  rw [coe_degLoop, loopLift_eq hg h0]

/-- **`thm:pi1-circle`**, well defined: if `f ≃ₚ g` (rel endpoints), then `deg f = deg g`.

The book's proof: lift the path homotopy from `0` (`thm:homotopy-lifting`); its left and right
edges are constant, and its bottom and top edges are lifts of `f` and `g` from `0`, so they are
`f̃` and `g̃`, which therefore have the same end. -/
theorem degLoop_eq_of_homotopic {f g : Path (1 : S1) 1} (h : f.Homotopic g) :
    degLoop f = degLoop g := by
  -- Let `H` be a path homotopy from `f` to `g` (`def:path-homotopy`): `H(s, 0) = f(s)`,
  -- `H(s, 1) = g(s)`, `H(0, t) = H(1, t) = 1`. (Lean: `obtain ⟨H⟩ := h` takes the `H` whose
  -- existence `h : Nonempty (PathHomotopy f g)` asserts.)
  obtain ⟨H⟩ := h
  -- Lift it to `K : I × I → ℝ` with `K(0, 0) = 0` (`thm:homotopy-lifting`), as `p(0) = 1`.
  obtain ⟨K, hK, hK0⟩ := exists_lift_homotopy H.continuous_toFun 0 (by rw [p_zero, H.source'])
  -- The edges `s = 0` and `s = 1` of `H` are constant, so those of `K` are
  -- (`lift_edge_const`): `K(0, t) = K(0, 0) = 0` and `K(1, t) = K(1, 0)`.
  have hleft : ∀ t, K (0, t) = 0 := fun t =>
    (lift_edge_const hK 0 (fun t => by rw [H.source', H.source']) t).trans hK0
  have hright : ∀ t, K (1, t) = K (1, 0) :=
    lift_edge_const hK 1 (fun t => by rw [H.target', H.target'])
  -- The bottom edge `s ↦ K(s, 0)` lifts `f` and starts at `0`, so `deg f = K(1, 0)`.
  have hf : (degLoop f : ℝ) = K (1, 0) :=
    degLoop_eq_of_lift (g := fun s => K (s, 0))
      ⟨hK.1.comp (continuous_id.prodMk continuous_const), fun s => by rw [hK.2, H.zero']⟩ hK0
  -- The top edge `s ↦ K(s, 1)` lifts `g` and starts at `K(0, 1) = 0`, so `deg g = K(1, 1)`.
  have hg : (degLoop g : ℝ) = K (1, 1) :=
    degLoop_eq_of_lift (g := fun s => K (s, 1))
      ⟨hK.1.comp (continuous_id.prodMk continuous_const), fun s => by rw [hK.2, H.one']⟩
      (hleft 1)
  -- So `deg f = K(1, 0) = K(1, 1) = deg g`. (Lean: `exact_mod_cast` passes from this equation
  -- of real numbers to the same equation of integers.)
  exact_mod_cast hf.trans ((hright 1).symm.trans hg.symm)

/-- `thm:pi1-circle`: the degree on `π₁(S¹, 1)`, `deg [f] = f̃(1)`, well defined by
`degLoop_eq_of_homotopic`. (Lean: `Quotient.lift u w` is the map `[f] ↦ u(f)` on classes, given
the proof `w` that `u` takes the same value on equivalent loops.) -/
def deg : pi1 (1 : S1) → ℤ := Quotient.lift degLoop fun _ _ h => degLoop_eq_of_homotopic h

/-- Unfolding: `deg [f] = deg f`. -/
theorem deg_mk (f : Path (1 : S1) 1) : deg ⟦f⟧ = degLoop f := rfl

/-- The constant loop has degree `0`: its lift from `0` is the constant `0`, as `p(0) = 1`. -/
theorem degLoop_refl : degLoop (Path.refl (1 : S1)) = 0 := by
  have := degLoop_eq_of_lift (f := Path.refl 1) (g := fun _ => 0)
    ⟨continuous_const, fun _ => p_zero⟩ rfl
  exact_mod_cast this

/-- **`thm:pi1-circle`**, homomorphism: `deg(f · g) = deg f + deg g`.

The book's proof: if `f̃` ends at `m`, the lift of `f · g` from `0` is `f̃` followed by `m + g̃`
(a lift, since `p(m + t) = p(t)`), continuous by the gluing lemma, and it ends at `m + g̃(1)`. -/
theorem degLoop_trans (f g : Path (1 : S1) 1) :
    degLoop (f.trans g) = degLoop f + degLoop g := by
  have hf := loopLift_isLift f
  have hg := loopLift_isLift g
  set m : ℤ := degLoop f with hm
  have hm' : (m : ℝ) = loopLift f 1 := coe_degLoop f
  -- The candidate lift, at the speed of `f · g` (`def:concatenation`): `L(s) = f̃(2s)` for
  -- `s ≤ 1/2` and `L(s) = g̃(2s - 1) + m` for `s ≥ 1/2`. (Lean: `I.dbl s = 2s` and
  -- `I.dbl' s = 2s - 1`, cut off to stay in `I`.)
  set L : I → ℝ := fun s => if (s : ℝ) ≤ 1 / 2 then loopLift f (I.dbl s)
    else loopLift g (I.dbl' s) + m with hL
  -- `L` is continuous by the gluing lemma: at `s = 1/2` the two halves give `f̃(1) = m` and
  -- `g̃(0) + m = 0 + m`.
  have hLc : Continuous L :=
    continuous_glue_half continuous_id (hf.1.comp I.continuous_dbl)
      ((hg.1.comp I.continuous_dbl').add_const_real _) (fun s hs => by
        show loopLift f (I.dbl s) = loopLift g (I.dbl' s) + m
        rw [I.dbl_of_half (s := s) hs, I.dbl'_of_half (s := s) hs, loopLift_zero, hm']; ring)
  -- `L` lifts `f · g`: for `s ≤ 1/2`, `p(f̃(2s)) = f(2s)`; for `s ≥ 1/2`,
  -- `p(g̃(2s - 1) + m) = p(g̃(2s - 1)) = g(2s - 1)` (`p_add_int`).
  have hpL : ∀ s, p (L s) = (f.trans g).toFun s := by
    intro s
    by_cases h : (s : ℝ) ≤ 1 / 2
    · simp only [hL, h, ite_true]
      rw [hf.2, Path.trans_apply_of_le _ _ s h]
    · simp only [hL, h, ite_false]
      rw [p_add_int, hg.2, Path.trans_apply_of_ge _ _ s (le_of_lt (not_le.mp h))]
  -- `L(0) = f̃(0) = 0` and `L(1) = g̃(1) + m`.
  have hL0 : L 0 = 0 := by
    have h : ((0 : I) : ℝ) ≤ 1 / 2 := by norm_num
    simp only [hL, h, ite_true, I.dbl_zero, loopLift_zero]
  have hL1 : L 1 = loopLift g 1 + m := by
    have h : ¬ ((1 : I) : ℝ) ≤ 1 / 2 := by norm_num
    simp only [hL, h, ite_false, I.dbl'_one]
  -- So `deg(f · g) = L(1) = deg g + deg f`.
  have := degLoop_eq_of_lift (f := f.trans g) ⟨hLc, hpL⟩ hL0
  rw [hL1, ← coe_degLoop g] at this
  exact_mod_cast (this.trans (add_comm _ _))

/-- The loop `s ↦ p(ns) = e^{2πins}`, going `n` times round the circle. -/
def windLoop (n : ℤ) : Path (1 : S1) 1 where
  -- The map `s ↦ p(ns)`, continuous as a composite (`p` and `s ↦ ns` are continuous); it
  -- starts at `p(0) = 1` and ends at `p(n) = 1` (`p_int`).
  toFun s := p ((n : ℝ) * (s : ℝ))
  continuous_toFun := continuous_p.comp
    (continuous_of_mathlib_eq I_toMathlib real_toMathlib (f := fun s : I => (n : ℝ) * (s : ℝ))
      (by fun_prop))
  source' := by simp
  target' := by simp [p_int]

/-- **`thm:pi1-circle`**, onto: `s ↦ e^{2πins}` has degree `n`. Its lift from `0` is `s ↦ ns`
(continuous, and `p(ns)` is the loop by definition), which ends at `n`. -/
theorem degLoop_windLoop (n : ℤ) : degLoop (windLoop n) = n := by
  have := degLoop_eq_of_lift (f := windLoop n) (g := fun s => (n : ℝ) * (s : ℝ))
    ⟨continuous_of_mathlib_eq I_toMathlib real_toMathlib (by fun_prop), fun _ => rfl⟩ (by simp)
  simp only [Set.Icc.coe_one, mul_one] at this
  exact_mod_cast this

/-- **`thm:pi1-circle`**, one to one: a loop `f` at `1` of degree `0` is path homotopic to the
constant loop `c₁` (`Path.refl 1`).

The book's proof: if `f̃(1) = 0`, then `f̃` is a loop in `ℝ`, contracted by the straight-line
homotopy `(1 - t) f̃(s)`, which fixes both ends at `0`; `p` of it is a path homotopy from `f` to
the constant loop. -/
theorem homotopic_refl_of_degLoop_eq_zero {f : Path (1 : S1) 1} (h : degLoop f = 0) :
    f.Homotopic (Path.refl 1) := by
  have hf := loopLift_isLift f
  -- `f̃(1) = deg f = 0`.
  have h1 : loopLift f 1 = 0 := by rw [← coe_degLoop, h, Int.cast_zero]
  -- `(s, t) ↦ (1 - t) f̃(s)` is continuous (Analysis I, through the bridges).
  have hc : Continuous (fun q : I × I => (1 - (q.2 : ℝ)) * loopLift f q.1) := by
    have := mathlib_continuous_of_eq I_toMathlib real_toMathlib hf.1
    exact continuous_of_mathlib_eq II_toMathlib real_toMathlib (by fun_prop)
  -- The path homotopy `H(s, t) = p((1 - t) f̃(s))`, field by field: it is continuous; at
  -- `t = 0` it is `p(f̃(s)) = f(s)`; at `t = 1` it is `p(0) = 1`; at `s = 0` and `s = 1` it is
  -- `p((1 - t)·0) = 1`, since `f̃(0) = f̃(1) = 0`. (Lean: `{ toFun := …, … }` builds the
  -- structure `PathHomotopy` field by field, and `⟨…⟩` says that one exists.)
  exact ⟨{ toFun := fun q => p ((1 - (q.2 : ℝ)) * loopLift f q.1)
           continuous_toFun := continuous_p.comp hc
           zero' := fun s => by simp [hf.2 s]
           one' := fun s => by simp
           source' := fun t => by simp [loopLift_zero]
           target' := fun t => by simp [h1] }⟩

/-- `thm:pi1-circle`: the degree is a homomorphism `π₁(S¹, 1) → ℤ` (`ℤ` written
multiplicatively, `README.md`). -/
def degHom : pi1 (1 : S1) →* Multiplicative ℤ where
  toFun a := Multiplicative.ofAdd (deg a)
  -- `deg 1 = deg c₁ = 0` (`degLoop_refl`).
  map_one' := by
    show Multiplicative.ofAdd (degLoop (Path.refl 1)) = 1
    rw [degLoop_refl]; rfl
  -- `deg([f][g]) = deg[f · g] = deg f + deg g` (`degLoop_trans`); every element of `π₁` is a
  -- class `[f]` (Lean: `induction a using Quotient.ind` says "write `a = [f]`").
  map_mul' a b := by
    induction a using Quotient.ind with | _ f => ?_
    induction b using Quotient.ind with | _ g => ?_
    show Multiplicative.ofAdd (degLoop (f.trans g)) =
      Multiplicative.ofAdd (degLoop f) * Multiplicative.ofAdd (degLoop g)
    rw [degLoop_trans, ofAdd_add]

/-- **`thm:pi1-circle`**: `π₁(S¹, 1) ≅ ℤ`, the isomorphism being the degree `[f] ↦ f̃(1)`:
a homomorphism (`degLoop_trans`), onto (`degLoop_windLoop`) and one to one
(`homotopic_refl_of_degLoop_eq_zero`). Mathlib: `FundamentalGroup`, `Circle`, `IsCoveringMap`;
Mathlib v4.34.1 does not contain this theorem, and none of its covering theory is used here.

Lean: `MulEquiv.ofBijective φ ⟨inj, surj⟩` is the isomorphism given by a homomorphism `φ` that is
one to one (`inj`) and onto (`surj`). -/
def pi1Circle : pi1 (1 : S1) ≃* Multiplicative ℤ :=
  MulEquiv.ofBijective degHom
    -- One to one: a homomorphism is one to one when only `1` goes to `0`. If `deg [f] = 0`,
    -- then `f ≃ₚ c₁` (`homotopic_refl_of_degLoop_eq_zero`), so `[f] = [c₁] = 1`.
    ⟨(injective_iff_map_eq_one degHom).mpr fun a ha => by
        induction a using Quotient.ind with | _ f => ?_
        have h0 : degLoop f = 0 := ofAdd_eq_one.mp ha
        exact Quotient.sound (homotopic_refl_of_degLoop_eq_zero h0),
      -- Onto: `m` is the degree of `[s ↦ e^{2πims}]` (`degLoop_windLoop`).
      fun m => ⟨⟦windLoop (Multiplicative.toAdd m)⟧, by
        show Multiplicative.ofAdd (degLoop _) = m
        rw [degLoop_windLoop]; rfl⟩⟩

/-- Unfolding: the isomorphism sends `[f]` to `deg f`. -/
theorem pi1Circle_mk (f : Path (1 : S1) 1) :
    pi1Circle ⟦f⟧ = Multiplicative.ofAdd (degLoop f) := rfl

/-- `thm:pi1-circle`: `π₁(S¹, 1)` is generated by the class of `s ↦ e^{2πis}`, which goes to
the generator `1` of `ℤ`: its degree is `1` (`degLoop_windLoop`). -/
theorem pi1Circle_windLoop_one : pi1Circle ⟦windLoop 1⟧ = Multiplicative.ofAdd 1 := by
  rw [pi1Circle_mk, degLoop_windLoop]

end

end Course

