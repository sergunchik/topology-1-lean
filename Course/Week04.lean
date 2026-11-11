/-
Machine-generated (Claude, Aristotle), no line written by a person. Copyleft: GPL-3.0-or-later.

# Week 4: homotopy, paths, path homotopy, the groupoid laws, `π₁` is a group

This file proves that the loop classes at a point form a group, `π₁(X, x)` (`cor:pi1-group`).
A homotopy is a continuous `H : X × I → Y` (`def:homotopy`), and a path homotopy `f ≃ₚ g`
between two paths from `x` to `y` is one that keeps the two ends fixed (`def:path-homotopy`).
The product `f · g` runs through `f`, then through `g`, each at double speed
(`def:concatenation`). It is not associative on paths, but it is on classes, because a path
read through any reparametrisation `φ : I → I` with `φ(0) = 0`, `φ(1) = 1` is path homotopic
to itself (`lem:reparam`). The same lemma gives the identity laws, a "go out and come back"
homotopy gives the inverse laws, and together they are the groupoid laws
(`thm:groupoid-laws`): the fundamental groupoid `Π₁(X)` of `def:fundamental-groupoid` is a
groupoid, and `π₁(X, x)` a group. The book: week 3 (`def:homotopy`,
`prop:hot-is-a-category`, `def:fundamental-groupoid`) and week 4.

Conventions. A homotopy is a map `X × I → Y`, time second (`def:homotopy`); a path homotopy is
a homotopy `I × I → X` of paths, `(s, t) ↦ H(s, t)` with `s` along the path and `t` the time
(`def:path-homotopy`). Picture the square `I × I` with `s` across and `t` up: the bottom edge
`t = 0` is the first path, the top edge `t = 1` the second, and the left and right edges
`s = 0`, `s = 1` go to the two ends `x`, `y`.

Departures from the book:
* To keep every map defined on all of `I`, the doublings `s ↦ 2s` and `s ↦ 2s - 1` of
  `def:concatenation` are clamped into `I` (`I.dbl`, `I.dbl'`); on the half where each is used
  the clamp does nothing.
* Associativity is proved by the book's second argument (`rem:pushout-paths`): `(f · g) · h` is
  `f · (g · h)` read through a piecewise linear `φ`, so `lem:reparam` applies. The identity
  laws (`exr-4-unit`) are proved the same way, and the inverse law (`exr-4-inverse`) by
  `H(s, t) = f((1 - t) · min(2s, 2 - 2s))`.
* From Analysis I, through week 1's bridges: the continuity of concrete maps `I → I` and
  `I × I → I` built from `+`, `·`, `min`, `max`, and that `[0, 1/2]` and `[1/2, 1]` are closed.
  Mathlib's homotopies put the time first; the bridge at the end swaps the factors. Mathlib's
  names below were checked against Lean and Mathlib v4.34.1.

New to Lean? Read `Course/README.md` first.
-/
import Course.Week02
import Mathlib.Topology.Homotopy.Path
import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup

-- Bookkeeping. `X`, `Y`, `Z` below are spaces (types; `u v w` are their "universe levels", which
-- you may ignore). `noncomputable section` says that some definitions use real numbers, which
-- Lean cannot compute.
universe u v w

set_option warn.classDefReducibility false

namespace Course

open Set

noncomputable section

variable {X : Type u} {Y : Type v} {Z : Type w}

/-! ## Analysis I: maps of the unit interval

The continuity of the concrete maps below is Analysis I (sums, products, `min`, `max` of
continuous real functions), entering through the bridges `I_toMathlib` and `prod_toMathlib`.

Lean: a point `s : I` is a real number with a proof that it lies in `[0, 1]`; `(s : ℝ)` is that
real number, and `s.2.1 : 0 ≤ s`, `s.2.2 : s ≤ 1` are the two inequalities. To define a map into
`I`, such as `rev` below, one gives a real number and proves it lies in `[0, 1]`. -/

section IntervalMaps

/-- If `X` and `Y` carry the Mathlib topologies `mX`, `mY` of their course topologies (`hX`,
`hY`), then a map `f : X → Y` continuous in Mathlib's sense is continuous in the course's
(week 1's bridge `continuous_iff_mathlib`). This is how Analysis I enters. -/
theorem continuous_of_mathlib_eq [tX : TopSpace X] [tY : TopSpace Y]
    {mX : TopologicalSpace X} {mY : TopologicalSpace Y} (hX : tX.toMathlib = mX)
    (hY : tY.toMathlib = mY) {f : X → Y} (hf : @_root_.Continuous X Y mX mY f) :
    Continuous f := by
  subst hX hY; exact (continuous_iff_mathlib f).mpr hf

/-- The converse of `continuous_of_mathlib_eq`: a map continuous in the course's sense is
continuous in Mathlib's. -/
theorem mathlib_continuous_of_eq [tX : TopSpace X] [tY : TopSpace Y]
    {mX : TopologicalSpace X} {mY : TopologicalSpace Y} (hX : tX.toMathlib = mX)
    (hY : tY.toMathlib = mY) {f : X → Y} (hf : Continuous f) :
    @_root_.Continuous X Y mX mY f := by
  subst hX hY; exact (continuous_iff_mathlib f).mp hf

/-- A set closed in Mathlib's sense is closed in the course's (week 1's bridge). -/
theorem isClosed_of_mathlib_eq [tX : TopSpace X] {mX : TopologicalSpace X}
    (hX : tX.toMathlib = mX) {C : Set X} (hC : @_root_.IsClosed X mX C) : IsClosed C := by
  subst hX; exact (isClosed_iff_mathlib C).mpr hC

/-- **Bridge.** The course topology of the square `I × I` (the product topology,
`thm:product-top`) is Mathlib's. -/
theorem II_toMathlib :
    (prod : TopSpace (I × I)).toMathlib = (inferInstance : TopologicalSpace (I × I)) := by
  rw [prod_toMathlib, I_toMathlib]

/-- `[0, 1/2]` is closed in `I` (Analysis I: `{s | s ≤ 1/2}` is closed in `ℝ`). -/
theorem isClosed_le_half : IsClosed {s : I | (s : ℝ) ≤ 1 / 2} :=
  isClosed_of_mathlib_eq I_toMathlib
    (isClosed_le _root_.continuous_subtype_val _root_.continuous_const)

/-- `[1/2, 1]` is closed in `I` (Analysis I). -/
theorem isClosed_half_le : IsClosed {s : I | 1 / 2 ≤ (s : ℝ)} :=
  isClosed_of_mathlib_eq I_toMathlib
    (isClosed_le _root_.continuous_const _root_.continuous_subtype_val)

namespace I

/-- The reversal `s ↦ 1 - s` of `I`. Mathlib: `unitInterval.symm`.

Lean: `⟨1 - s, proof⟩` is the real number `1 - s` together with the proof that it lies in
`[0, 1]`; the proof is two inequalities (`constructor` splits them), each by `linarith` from
`0 ≤ s ≤ 1`. -/
def rev (s : I) : I := ⟨1 - s, by constructor <;> linarith [s.2.1, s.2.2]⟩

/-- The first doubling `s ↦ min(2s, 1)`: `s ↦ 2s` on `[0, 1/2]`, clamped to `1` after. -/
def dbl (s : I) : I := ⟨min (2 * s) 1, le_min (by linarith [s.2.1]) zero_le_one, min_le_right _ _⟩

/-- The second doubling `s ↦ max(2s - 1, 0)`: `s ↦ 2s - 1` on `[1/2, 1]`, clamped to `0`
before. -/
def dbl' (s : I) : I :=
  ⟨max (2 * s - 1) 0, le_max_right _ _, max_le (by linarith [s.2.2]) zero_le_one⟩

/-- Unfolding: `rev s = 1 - s` as a real number. -/
@[simp] theorem coe_rev (s : I) : (rev s : ℝ) = 1 - s := rfl
/-- Unfolding: `dbl s = min(2s, 1)`. -/
@[simp] theorem coe_dbl (s : I) : (dbl s : ℝ) = min (2 * (s : ℝ)) 1 := rfl
/-- Unfolding: `dbl' s = max(2s - 1, 0)`. -/
@[simp] theorem coe_dbl' (s : I) : (dbl' s : ℝ) = max (2 * (s : ℝ) - 1) 0 := rfl

/-- For `s ≤ 1/2` the clamp does nothing: `dbl s = 2s`. -/
theorem coe_dbl_of_le {s : I} (h : (s : ℝ) ≤ 1 / 2) : (dbl s : ℝ) = 2 * s :=
  min_eq_left (by linarith)

/-- For `s ≥ 1/2` the clamp does nothing: `dbl' s = 2s - 1`. -/
theorem coe_dbl'_of_ge {s : I} (h : 1 / 2 ≤ (s : ℝ)) : (dbl' s : ℝ) = 2 * s - 1 :=
  max_eq_left (by linarith)

/-- Two points of `I` are equal if they are equal as real numbers. -/
theorem ext_iff' {a b : I} : a = b ↔ (a : ℝ) = b := Subtype.ext_iff

/-- `1 - 0 = 1`. -/
@[simp] theorem rev_zero : rev 0 = 1 := Subtype.ext (by simp)
/-- `1 - 1 = 0`. -/
@[simp] theorem rev_one : rev 1 = 0 := Subtype.ext (by simp)
/-- `1 - (1 - s) = s`. -/
@[simp] theorem rev_rev (s : I) : rev (rev s) = s := Subtype.ext (by simp)
/-- `dbl 0 = 0`. -/
@[simp] theorem dbl_zero : dbl 0 = 0 := Subtype.ext (by simp)
/-- `dbl' 1 = 1`. -/
@[simp] theorem dbl'_one : dbl' 1 = 1 := Subtype.ext (by norm_num)

/-- At the midpoint, the first doubling has reached the end: `dbl (1/2) = 1`. -/
theorem dbl_of_half {s : I} (h : (s : ℝ) = 1 / 2) : dbl s = 1 := Subtype.ext (by simp [h])
/-- At the midpoint, the second doubling starts: `dbl' (1/2) = 0`. -/
theorem dbl'_of_half {s : I} (h : (s : ℝ) = 1 / 2) : dbl' s = 0 := Subtype.ext (by simp [h])


/-- `dbl 1 = 1`. -/
@[simp] theorem dbl_one : dbl 1 = 1 := Subtype.ext (by norm_num)
/-- `dbl' 0 = 0`. -/
@[simp] theorem dbl'_zero : dbl' 0 = 0 := Subtype.ext (by norm_num)

/-- On `[1/2, 1]` the first doubling is clamped at `1`. -/
theorem dbl_of_ge {s : I} (h : 1 / 2 ≤ (s : ℝ)) : dbl s = 1 :=
  Subtype.ext (by simp only [coe_dbl, Set.Icc.coe_one]; exact min_eq_right (by linarith))

/-- On `[0, 1/2]` the second doubling is clamped at `0`. -/
theorem dbl'_of_le {s : I} (h : (s : ℝ) ≤ 1 / 2) : dbl' s = 0 :=
  Subtype.ext (by simp only [coe_dbl', Set.Icc.coe_zero]; exact max_eq_right (by linarith))

/-- The straight-line homotopy `(s, t) ↦ (1 - t) φ(s) + t ψ(s)` between two maps `φ, ψ : I → I`;
it stays in `I` because `I` is convex (`lem:reparam`). Here `p = (s, t)`, `p.1 = s`, `p.2 = t`. -/
def line (φ ψ : I → I) (p : I × I) : I :=
  ⟨(1 - p.2) * φ p.1 + p.2 * ψ p.1, by
    -- Convexity: with `a = φ(s)`, `b = ψ(s)` and `t` in `[0, 1]`, the number `(1 - t) a + t b`
    -- is `≥ 0` (a sum of products of numbers `≥ 0`) and `≤ (1 - t) + t = 1`.
    have ha := (φ p.1).2; have hb := (ψ p.1).2; have ht := p.2.2
    constructor
    · nlinarith [mul_nonneg (sub_nonneg.2 ht.2) ha.1, mul_nonneg ht.1 hb.1]
    · nlinarith [mul_le_mul_of_nonneg_left ha.2 (sub_nonneg.2 ht.2),
        mul_le_mul_of_nonneg_left hb.2 ht.1]⟩

/-- Unfolding: `line φ ψ (s, t) = (1 - t) φ(s) + t ψ(s)`. -/
@[simp] theorem coe_line (φ ψ : I → I) (p : I × I) :
    (line φ ψ p : ℝ) = (1 - (p.2 : ℝ)) * φ p.1 + p.2 * ψ p.1 := rfl

/-- At time `t = 0` the straight-line homotopy is `φ`. -/
@[simp] theorem line_zero (φ ψ : I → I) (s : I) : line φ ψ (s, 0) = φ s := Subtype.ext (by simp)
/-- At time `t = 1` the straight-line homotopy is `ψ`. -/
@[simp] theorem line_one (φ ψ : I → I) (s : I) : line φ ψ (s, 1) = ψ s := Subtype.ext (by simp)

/-- The tent `s ↦ min(2s, 2 - 2s)`: out along `[0, 1]` and back. -/
def tent (s : I) : I :=
  ⟨min (2 * (s : ℝ)) (2 - 2 * s), le_min (by linarith [s.2.1]) (by linarith [s.2.2]), by
    -- `min(2s, 2 - 2s) ≤ 1`: for `s ≤ 1/2` because `2s ≤ 1`, for `s ≥ 1/2` because `2 - 2s ≤ 1`.
    rcases le_total (s : ℝ) (1 / 2) with h | h
    · exact min_le_of_left_le (by linarith)
    · exact min_le_of_right_le (by linarith)⟩

/-- Unfolding: `tent s = min(2s, 2 - 2s)`. -/
@[simp] theorem coe_tent (s : I) : (tent s : ℝ) = min (2 * (s : ℝ)) (2 - 2 * s) := rfl

/-- The reparametrisation `φ` of `rem:pushout-paths`, piecewise linear with `φ(0) = 0`,
`φ(1/4) = 1/2`, `φ(1/2) = 3/4`, `φ(1) = 1`; as it is concave, it is the minimum of its three
pieces `2s`, `s + 1/4`, `(s + 1)/2`. -/
def assoc (s : I) : I :=
  ⟨min (2 * (s : ℝ)) (min (s + 1 / 4) ((s + 1) / 2)),
    le_min (by linarith [s.2.1]) (le_min (by linarith [s.2.1]) (by linarith [s.2.1])),
    min_le_of_right_le (min_le_of_right_le (by linarith [s.2.2]))⟩

/-- Unfolding: `φ(s) = min(2s, s + 1/4, (s + 1)/2)`. -/
@[simp] theorem coe_assoc (s : I) :
    (assoc s : ℝ) = min (2 * (s : ℝ)) (min (s + 1 / 4) ((s + 1) / 2)) := rfl

/-- On `[0, 1/4]`, `φ(s) = 2s`. -/
theorem coe_assoc_of_le {s : I} (h : (s : ℝ) ≤ 1 / 4) : (assoc s : ℝ) = 2 * s := by
  -- There `2s` is the smallest of the three pieces.
  have := s.2.1
  simp only [coe_assoc]; exact min_eq_left (le_min (by linarith) (by linarith))

/-- On `[1/4, 1/2]`, `φ(s) = s + 1/4`. -/
theorem coe_assoc_of_mid {s : I} (h₁ : 1 / 4 ≤ (s : ℝ)) (h₂ : (s : ℝ) ≤ 1 / 2) :
    (assoc s : ℝ) = s + 1 / 4 := by
  -- There `s + 1/4` is the smallest: `s + 1/4 ≤ (s + 1)/2` as `s ≤ 1/2`, and `s + 1/4 ≤ 2s`
  -- as `s ≥ 1/4`.
  simp only [coe_assoc]
  rw [min_eq_left (show (s : ℝ) + 1 / 4 ≤ (s + 1) / 2 by linarith),
    min_eq_right (show (s : ℝ) + 1 / 4 ≤ 2 * s by linarith)]

/-- On `[1/2, 1]`, `φ(s) = (s + 1)/2`. -/
theorem coe_assoc_of_ge {s : I} (h : 1 / 2 ≤ (s : ℝ)) : (assoc s : ℝ) = (s + 1) / 2 := by
  -- There `(s + 1)/2` is the smallest of the three pieces, as `s ≥ 1/2`.
  simp only [coe_assoc]
  rw [min_eq_right (show ((s : ℝ) + 1) / 2 ≤ s + 1 / 4 by linarith),
    min_eq_right (show ((s : ℝ) + 1) / 2 ≤ 2 * s by linarith)]

/-- `φ(0) = 0`. -/
@[simp] theorem assoc_zero : assoc 0 = 0 := Subtype.ext (by norm_num [coe_assoc_of_le])
/-- `φ(1) = 1`. -/
@[simp] theorem assoc_one : assoc 1 = 1 := Subtype.ext (by norm_num [coe_assoc_of_ge])

/-- `s ↦ 1 - s` is continuous (Analysis I). -/
theorem continuous_rev : Continuous rev :=
  continuous_of_mathlib_eq I_toMathlib I_toMathlib
    ((_root_.continuous_const.sub _root_.continuous_subtype_val).subtype_mk _)

/-- `s ↦ min(2s, 1)` is continuous (Analysis I). -/
theorem continuous_dbl : Continuous dbl :=
  continuous_of_mathlib_eq I_toMathlib I_toMathlib
    (((_root_.continuous_const.mul _root_.continuous_subtype_val).min
      _root_.continuous_const).subtype_mk _)

/-- `s ↦ max(2s - 1, 0)` is continuous (Analysis I). -/
theorem continuous_dbl' : Continuous dbl' :=
  continuous_of_mathlib_eq I_toMathlib I_toMathlib
    ((((_root_.continuous_const.mul _root_.continuous_subtype_val).sub _root_.continuous_const).max
      _root_.continuous_const).subtype_mk _)

/-- If `φ, ψ : I → I` are continuous, so is the straight-line homotopy
`(s, t) ↦ (1 - t) φ(s) + t ψ(s)` (Analysis I: sums and products of continuous functions). -/
theorem continuous_line {φ ψ : I → I} (hφ : Continuous φ) (hψ : Continuous ψ) :
    Continuous (line φ ψ) := by
  -- Pass to Mathlib's continuity, where `fun_prop` checks the formula piece by piece.
  have hφ' := mathlib_continuous_of_eq I_toMathlib I_toMathlib hφ
  have hψ' := mathlib_continuous_of_eq I_toMathlib I_toMathlib hψ
  refine continuous_of_mathlib_eq II_toMathlib I_toMathlib (Continuous.subtype_mk ?_ _)
  fun_prop

/-- The tent `s ↦ min(2s, 2 - 2s)` is continuous (Analysis I). -/
theorem continuous_tent : Continuous tent :=
  continuous_of_mathlib_eq I_toMathlib I_toMathlib (Continuous.subtype_mk (by fun_prop) _)

/-- `φ(s) = min(2s, s + 1/4, (s + 1)/2)` is continuous (Analysis I). -/
theorem continuous_assoc : Continuous assoc :=
  continuous_of_mathlib_eq I_toMathlib I_toMathlib (Continuous.subtype_mk (by fun_prop) _)

end I

end IntervalMaps

/-! ## Two tools: maps into a product, gluing at `1/2` -/

section Tools
variable [TopSpace X] [TopSpace Y] [TopSpace Z]

/-- `thm:product-top`: a map `z ↦ (f(z), g(z))` into a product with continuous components `f`,
`g` is continuous. Mathlib: `Continuous.prodMk`. -/
theorem Continuous.prodMk {f : Z → X} {g : Z → Y} (hf : Continuous f) (hg : Continuous g) :
    Continuous (fun z => (f z, g z)) :=
  continuous_prodMk.mpr ⟨hf, hg⟩

/-- `prop-1-20`, the gluing lemma, in the form used for every concatenation: if `u : X → I` is
continuous, `f` and `g` are continuous, and they agree where `u = 1/2` (`hfg`), then the map that
is `f` where `u ≤ 1/2` and `g` where `u ≥ 1/2` is continuous. The two pieces `u⁻¹[0, 1/2]` and
`u⁻¹[1/2, 1]` are closed and cover `X`. Mathlib: `Continuous.if_le`.

Lean: `if P then a else b` is `a` when `P` holds and `b` otherwise. -/
theorem continuous_glue_half {u : X → I} (hu : Continuous u) {f g : X → Y} (hf : Continuous f)
    (hg : Continuous g) (hfg : ∀ x, (u x : ℝ) = 1 / 2 → f x = g x) :
    Continuous (fun x => if (u x : ℝ) ≤ 1 / 2 then f x else g x) := by
  -- Apply the gluing lemma `prop-1-20` to `C₁ = u⁻¹[0, 1/2]` and `C₂ = u⁻¹[1/2, 1]`. They are
  -- closed, as preimages of closed sets under the continuous `u`; they cover `X`, since every
  -- real number is `≤ 1/2` or `≥ 1/2`. It remains to see that the map is continuous on each.
  refine continuous_of_closed_cover (C₁ := u ⁻¹' {s : I | (s : ℝ) ≤ 1 / 2})
    (C₂ := u ⁻¹' {s : I | 1 / 2 ≤ (s : ℝ)})
    (continuous_iff_isClosed.mp hu _ isClosed_le_half)
    (continuous_iff_isClosed.mp hu _ isClosed_half_le)
    (eq_univ_of_forall fun x => (le_total (u x : ℝ) (1 / 2)).imp id id) ?_ ?_
  -- On `C₁` the map is `f`, which is continuous. (Lean: a point of the subspace `C₁` is a pair
  -- `x = ⟨x.1, x.2⟩` of a point `x.1` of `X` and the proof `x.2` that `u(x.1) ≤ 1/2`.)
  · have : (fun x : (u ⁻¹' {s : I | (s : ℝ) ≤ 1 / 2}) =>
        if (u x : ℝ) ≤ 1 / 2 then f x else g x) = fun x => f x.1 := by
      funext x
      have hx : (u x : ℝ) ≤ 1 / 2 := x.2
      simp only [hx, ite_true]
    rw [this]
    exact hf.comp continuous_subtype_val
  -- On `C₂` the map is `g`: where `u > 1/2` by definition, and where `u = 1/2` because there
  -- `f = g` (`hfg`).
  · have : (fun x : (u ⁻¹' {s : I | 1 / 2 ≤ (s : ℝ)}) =>
        if (u x : ℝ) ≤ 1 / 2 then f x else g x) = fun x => g x.1 := by
      funext x
      have hx : 1 / 2 ≤ (u x : ℝ) := x.2
      by_cases h : (u x : ℝ) ≤ 1 / 2
      · simp only [h, ite_true]; exact hfg x (le_antisymm h hx)
      · simp only [h, ite_false]
    rw [this]
    exact hg.comp continuous_subtype_val

end Tools

/-! ## Homotopy (`def:homotopy`, `prop:hot-is-a-category`) -/

/-- `def:homotopy`: a homotopy from `f` to `g` is a continuous `H : X × I → Y` with
`H(-, 0) = f` and `H(-, 1) = g`. Mathlib: `ContinuousMap.Homotopy` (time first).

Lean: a `structure` is a bundle of data and properties, here the map `toFun` and the three
facts about it; a homotopy `F` has them as `F.toFun`, `F.continuous_toFun`, `F.zero'`,
`F.one'`. -/
structure Homotopy [TopSpace X] [TopSpace Y] (f g : X → Y) where
  /-- The map `H : X × I → Y`. -/
  toFun : X × I → Y
  /-- `H` is continuous. -/
  continuous_toFun : Continuous toFun
  /-- `H(x, 0) = f(x)` for every `x`. -/
  zero' : ∀ x, toFun (x, 0) = f x
  /-- `H(x, 1) = g(x)` for every `x`. -/
  one' : ∀ x, toFun (x, 1) = g x

/-- `def:homotopy`: `f ≃ g`, there is a homotopy from `f` to `g`.
Mathlib: `ContinuousMap.Homotopic`. -/
def Homotopic [TopSpace X] [TopSpace Y] (f g : X → Y) : Prop := Nonempty (Homotopy f g)

namespace Homotopy
variable [TopSpace X] [TopSpace Y] {f g h : X → Y}

/-- `prop:hot-is-a-category`, reflexive: `H(x, t) = f(x)`, a homotopy from `f` to `f` for
continuous `f`. Mathlib: `ContinuousMap.Homotopy.refl`. -/
def refl (f : X → Y) (hf : Continuous f) : Homotopy f f where
  -- `(x, t) ↦ f(x)` is `f` composed with the projection `X × I → X`, so it is continuous; at
  -- `t = 0` and `t = 1` it is `f` by definition (`rfl`).
  toFun p := f p.1
  continuous_toFun := hf.comp continuous_fst
  zero' _ := rfl
  one' _ := rfl

/-- `prop:hot-is-a-category`, symmetric: from `F : f ≃ g`, the homotopy `H(x, t) = F(x, 1 - t)`
from `g` to `f`. Mathlib: `ContinuousMap.Homotopy.symm`. -/
def symm (F : Homotopy f g) : Homotopy g f where
  -- Run `F` backwards in time.
  toFun p := F.toFun (p.1, I.rev p.2)
  -- A composite of `F` with `(x, t) ↦ (x, 1 - t)`, continuous by `thm:product-top`.
  continuous_toFun :=
    F.continuous_toFun.comp (continuous_fst.prodMk (I.continuous_rev.comp continuous_snd))
  -- At `t = 0` it is `F(x, 1) = g(x)`, at `t = 1` it is `F(x, 0) = f(x)`.
  zero' x := by simp [F.one']
  one' x := by simp [F.zero']

/-- `prop:hot-is-a-category`, transitive: from `F : f ≃ g` and `G : g ≃ h`, run `F` at double
speed on `[0, 1/2]` and `G` on `[1/2, 1]`, continuous by the gluing lemma for the closed pieces
`X × [0, 1/2]` and `X × [1/2, 1]`. Mathlib: `ContinuousMap.Homotopy.trans`. -/
def trans (F : Homotopy f g) (G : Homotopy g h) : Homotopy f h where
  -- `H(x, t) = F(x, 2t)` for `t ≤ 1/2` and `G(x, 2t - 1)` for `t ≥ 1/2`.
  toFun p := if (p.2 : ℝ) ≤ 1 / 2 then F.toFun (p.1, I.dbl p.2) else G.toFun (p.1, I.dbl' p.2)
  -- The gluing lemma (`continuous_glue_half`, with `u(x, t) = t`): each piece is continuous,
  -- and at `t = 1/2` both are `g(x)`: `F(x, 1) = g(x) = G(x, 0)`.
  continuous_toFun :=
    continuous_glue_half continuous_snd
      (F.continuous_toFun.comp (continuous_fst.prodMk (I.continuous_dbl.comp continuous_snd)))
      (G.continuous_toFun.comp (continuous_fst.prodMk (I.continuous_dbl'.comp continuous_snd)))
      (fun p hp => by
        rw [I.dbl_of_half hp, I.dbl'_of_half hp, F.one', G.zero'])
  -- At `t = 0` it is `F(x, 0) = f(x)`, at `t = 1` it is `G(x, 1) = h(x)`.
  zero' x := by simp [F.zero']
  one' x := by norm_num [G.one']

/-- Unfolding: `(F · G)(x, t)` is `F(x, 2t)` for `t ≤ 1/2` and `G(x, 2t - 1)` otherwise. -/
theorem trans_apply (F : Homotopy f g) (G : Homotopy g h) (p : X × I) :
    (F.trans G).toFun p =
      if (p.2 : ℝ) ≤ 1 / 2 then F.toFun (p.1, I.dbl p.2) else G.toFun (p.1, I.dbl' p.2) := rfl

end Homotopy

namespace Homotopic
variable [TopSpace X] [TopSpace Y] {f g h : X → Y}

/-- `prop:hot-is-a-category`: `f ≃ f` for continuous `f`. -/
theorem refl (hf : Continuous f) : Homotopic f f := ⟨Homotopy.refl f hf⟩

/-- `prop:hot-is-a-category`: `f ≃ g` implies `g ≃ f`.

Lean: `hfg.map Homotopy.symm` turns "there is a homotopy `F` from `f` to `g`" into "there is a
homotopy, `F.symm`, from `g` to `f`" (`Nonempty.map`). -/
theorem symm (hfg : Homotopic f g) : Homotopic g f := hfg.map Homotopy.symm

/-- `prop:hot-is-a-category`: `f ≃ g ≃ h` implies `f ≃ h`.

Lean: `hfg.elim fun F => …` says "take a homotopy `F` from `f` to `g`, as `hfg` provides". -/
theorem trans (hfg : Homotopic f g) (hgh : Homotopic g h) : Homotopic f h :=
  hfg.elim fun F => hgh.elim fun G => ⟨F.trans G⟩

end Homotopic

/-! ## Paths (`def:path-homotopy`, `def:concatenation`) -/

/-- A path from `x` to `y`: a continuous `f : I → X` with `f(0) = x` and `f(1) = y`; a loop at
`x` is a path from `x` to `x`. Mathlib: `Path`. -/
structure Path [TopSpace X] (x y : X) where
  /-- The map `f : I → X`. -/
  toFun : I → X
  /-- `f` is continuous. -/
  continuous_toFun : Continuous toFun
  /-- `f(0) = x`. -/
  source' : toFun 0 = x
  /-- `f(1) = y`. -/
  target' : toFun 1 = y

namespace Path
variable [TopSpace X] {x y z w : X}

/-- Lean: this lets us write `f s` for `f.toFun s`, a path applied to `s ∈ I`. -/
instance : CoeFun (Path x y) (fun _ => I → X) := ⟨Path.toFun⟩

/-- A path from `x` starts at `x`: `f(0) = x`. -/
@[simp] theorem source (f : Path x y) : f 0 = x := f.source'
/-- A path to `y` ends at `y`: `f(1) = y`. -/
@[simp] theorem target (f : Path x y) : f 1 = y := f.target'
/-- A path is continuous. -/
theorem continuous (f : Path x y) : Continuous f := f.continuous_toFun

/-- Two paths that agree at every `s ∈ I` are equal. -/
@[ext] theorem ext {f g : Path x y} (h : ∀ s, f s = g s) : f = g := by
  -- The maps are equal (`funext`), and the other fields are proofs, which Lean regards as equal.
  cases f; cases g; congr; funext s; exact h s

/-- A path takes equal values at points of `I` with equal coordinates. -/
theorem congr_coe (f : Path x y) {a b : I} (h : (a : ℝ) = b) : f a = f b :=
  congrArg f (Subtype.ext h)

/-- `def:concatenation`: the constant path `c_x`. Mathlib: `Path.refl`. -/
def refl (x : X) : Path x x := ⟨fun _ => x, continuous_const, rfl, rfl⟩

/-- Unfolding: `c_x(s) = x`. -/
@[simp] theorem refl_apply (x : X) (s : I) : refl x s = x := rfl

/-- `def:concatenation`: the reverse `f̄(s) = f(1 - s)`, a path from `y` to `x`, continuous as a
composite of continuous maps. Mathlib: `Path.symm`. -/
def symm (f : Path x y) : Path y x :=
  ⟨fun s => f (I.rev s), f.continuous.comp I.continuous_rev, by simp, by simp⟩

/-- Unfolding: `f̄(s) = f(1 - s)`. -/
@[simp] theorem symm_apply (f : Path x y) (s : I) : f.symm s = f (I.rev s) := rfl

/-- The reverse of the reverse is the path itself: `f(1 - (1 - s)) = f(s)`. -/
@[simp] theorem symm_symm (f : Path x y) : f.symm.symm = f := by ext s; simp

/-- `def:concatenation`: the product `f · g`, which is `f(2s)` on `[0, 1/2]` and `g(2s - 1)` on
`[1/2, 1]`, continuous by the gluing lemma. Mathlib: `Path.trans`. -/
def trans (f : Path x y) (g : Path y z) : Path x z where
  toFun s := if (s : ℝ) ≤ 1 / 2 then f (I.dbl s) else g (I.dbl' s)
  -- The gluing lemma (`continuous_glue_half` with `u = id`): the two pieces are continuous, and
  -- at `s = 1/2` both are `f(1) = y = g(0)`.
  continuous_toFun :=
    continuous_glue_half continuous_id (f.continuous.comp I.continuous_dbl)
      (g.continuous.comp I.continuous_dbl') (fun s hs => by
        show f (I.dbl s) = g (I.dbl' s)
        rw [I.dbl_of_half (s := s) hs, I.dbl'_of_half (s := s) hs, f.target, g.source])
  -- `(f · g)(0) = f(0) = x` and `(f · g)(1) = g(1) = z`.
  source' := by simp
  target' := by norm_num

/-- Unfolding: `(f · g)(s)` is `f(2s)` for `s ≤ 1/2` and `g(2s - 1)` otherwise. -/
theorem trans_apply (f : Path x y) (g : Path y z) (s : I) :
    f.trans g s = if (s : ℝ) ≤ 1 / 2 then f (I.dbl s) else g (I.dbl' s) := rfl

/-- `(f · g)(s) = f(2s)` for `s ≤ 1/2`. -/
theorem trans_apply_of_le (f : Path x y) (g : Path y z) (s : I) (h : (s : ℝ) ≤ 1 / 2) :
    f.trans g s = f (I.dbl s) := by
  rw [trans_apply]; simp only [h, ite_true]

/-- `(f · g)(s) = g(2s - 1)` for `s ≥ 1/2`, including `s = 1/2`, where `f(1) = g(0)`. -/
theorem trans_apply_of_ge (f : Path x y) (g : Path y z) (s : I) (h : 1 / 2 ≤ (s : ℝ)) :
    f.trans g s = g (I.dbl' s) := by
  rw [trans_apply]
  by_cases h' : (s : ℝ) ≤ 1 / 2
  -- At `s = 1/2` the definition says `f(2s) = f(1) = y`, which is `g(0) = g(2s - 1)`.
  · have hs : (s : ℝ) = 1 / 2 := le_antisymm h' h
    simp only [h', ite_true]
    rw [I.dbl_of_half hs, I.dbl'_of_half hs, f.target, g.source]
  -- For `s > 1/2` it is `g(2s - 1)` by definition.
  · simp only [h', ite_false]

end Path

/-! ## Path homotopy (`def:path-homotopy`) -/

/-- `def:path-homotopy`: a path homotopy from `f` to `g`, paths from `x` to `y`, is a homotopy
`H : I × I → X` from `f` to `g` (`def:homotopy`) with `H(0, t) = x` and `H(1, t) = y`: a
homotopy rel `{0, 1}`. In the square `I × I`, with `s` across and `t` up, the bottom edge is
`f`, the top edge is `g`, and the left and right edges go to the points `x` and `y`.
Mathlib: `Path.Homotopy` (time first).

Lean: `extends Homotopy …` says that a path homotopy has all the fields of a homotopy
(`toFun`, `zero'`, …) and two more; `F.toHomotopy` is `F` seen as a homotopy. -/
structure PathHomotopy [TopSpace X] {x y : X} (f g : Path x y) extends Homotopy (f : I → X) g where
  /-- The left edge goes to `x`: `H(0, t) = x` for every `t`. -/
  source' : ∀ t, toFun (0, t) = x
  /-- The right edge goes to `y`: `H(1, t) = y` for every `t`. -/
  target' : ∀ t, toFun (1, t) = y

/-- `def:path-homotopy`: `f ≃ₚ g`, there is a path homotopy from `f` to `g`.
Mathlib: `Path.Homotopic`. -/
def Path.Homotopic [TopSpace X] {x y : X} (f g : Path x y) : Prop := Nonempty (PathHomotopy f g)

namespace PathHomotopy
variable [TopSpace X] {x y z : X} {f g h : Path x y}

/-- `prop:hot-is-a-category` with the ends fixed: the constant homotopy `H(s, t) = f(s)`.

Lean: `{ A with … }` is the structure `A` with the listed fields added or replaced. -/
def refl (f : Path x y) : PathHomotopy f f :=
  { Homotopy.refl f f.continuous with
    source' := fun _ => f.source
    target' := fun _ => f.target }

/-- `prop:hot-is-a-category` with the ends fixed: `H(s, 1 - t)`; the side edges still go to `x`
and `y`. -/
def symm (F : PathHomotopy f g) : PathHomotopy g f :=
  { F.toHomotopy.symm with
    source' := fun _ => F.source' _
    target' := fun _ => F.target' _ }

/-- `prop:hot-is-a-category` with the ends fixed: `F` then `G`, glued at `t = 1/2`; the square
of `F` sits below the square of `G`, each squeezed to half height. -/
def trans (F : PathHomotopy f g) (G : PathHomotopy g h) : PathHomotopy f h :=
  { F.toHomotopy.trans G.toHomotopy with
    -- On the left edge, both halves are `x`; on the right edge, both are `y`.
    source' := fun t => by
      rw [Homotopy.trans_apply]; split_ifs
      · exact F.source' _
      · exact G.source' _
    target' := fun t => by
      rw [Homotopy.trans_apply]; split_ifs
      · exact F.target' _
      · exact G.target' _ }

/-- `thm:groupoid-laws`, well defined: `F : f ≃ₚ f'` and `G : g ≃ₚ g'` placed side by side,
`F(2s, t)` for `s ≤ 1/2` and `G(2s - 1, t)` for `s ≥ 1/2`, give `f · g ≃ₚ f' · g'`. In the
square: the left half is `F` squeezed to half width, the right half is `G`, and they meet along
the vertical segment `s = 1/2`, which both send to `y`. Mathlib: `Path.Homotopy.hcomp`. -/
def hcomp {f f' : Path x y} {g g' : Path y z} (F : PathHomotopy f f') (G : PathHomotopy g g') :
    PathHomotopy (f.trans g) (f'.trans g') where
  toFun p := if (p.1 : ℝ) ≤ 1 / 2 then F.toFun (I.dbl p.1, p.2) else G.toFun (I.dbl' p.1, p.2)
  -- The gluing lemma along `s = 1/2`: there `F(1, t) = y = G(0, t)`, because `F` and `G` keep
  -- their ends fixed.
  continuous_toFun :=
    continuous_glue_half continuous_fst
      (F.continuous_toFun.comp ((I.continuous_dbl.comp continuous_fst).prodMk continuous_snd))
      (G.continuous_toFun.comp ((I.continuous_dbl'.comp continuous_fst).prodMk continuous_snd))
      (fun p hp => by
        show F.toFun (I.dbl p.1, p.2) = G.toFun (I.dbl' p.1, p.2)
        rw [I.dbl_of_half hp, I.dbl'_of_half hp, F.target', G.source'])
  -- The bottom edge `t = 0` is `f · g` and the top edge `t = 1` is `f' · g'`; the left edge
  -- is `F(0, t) = x`, the right edge `G(1, t) = z`.
  zero' s := by simp only [Path.trans_apply, F.zero', G.zero']
  one' s := by simp only [Path.trans_apply, F.one', G.one']
  source' t := by simp [F.source']
  target' t := by norm_num [G.target']

/-- The reverse respects path homotopy: from `F : f ≃ₚ g`, the square flipped left to right,
`H(1 - s, t)`, is a path homotopy `f̄ ≃ₚ ḡ`. Mathlib: `Path.Homotopy.symm₂`. -/
def symm₂ (F : PathHomotopy f g) : PathHomotopy f.symm g.symm where
  toFun p := F.toFun (I.rev p.1, p.2)
  continuous_toFun :=
    F.continuous_toFun.comp ((I.continuous_rev.comp continuous_fst).prodMk continuous_snd)
  zero' _ := F.zero' _
  one' _ := F.one' _
  -- The flip swaps the two side edges: the left edge now goes to `y`, the right one to `x`.
  source' _ := by simp [F.target']
  target' _ := by simp [F.source']

/-- A path homotopy of the form `(s, t) ↦ f(G(s, t))`, for a continuous `G : I × I → I`: all the
homotopies of the groupoid laws below are of this form. To be a path homotopy from `p` to `q`
(paths from `a` to `b`), it needs: on the bottom edge `f(G(s, 0)) = p(s)` (`h0`), on the top
edge `f(G(s, 1)) = q(s)` (`h1`), and the left and right edges sent to `a` (`hl`) and `b`
(`hr`). -/
def ofMap (f : Path x y) {a b : X} {p q : Path a b} (G : I × I → I) (hG : Continuous G)
    (h0 : ∀ s, f (G (s, 0)) = p s) (h1 : ∀ s, f (G (s, 1)) = q s)
    (hl : ∀ t, f (G (0, t)) = a) (hr : ∀ t, f (G (1, t)) = b) : PathHomotopy p q where
  toFun st := f (G st)
  continuous_toFun := f.continuous.comp hG
  zero' := h0
  one' := h1
  source' := hl
  target' := hr

end PathHomotopy

namespace Path.Homotopic
variable [TopSpace X] {x y z : X} {f g h : Path x y}

/-- `def:path-homotopy`: path homotopy is reflexive (`prop:hot-is-a-category`, ends fixed). -/
theorem refl (f : Path x y) : f.Homotopic f := ⟨PathHomotopy.refl f⟩

/-- Path homotopy is symmetric (`prop:hot-is-a-category`, ends fixed). -/
theorem symm (hfg : f.Homotopic g) : g.Homotopic f := hfg.map PathHomotopy.symm

/-- Path homotopy is transitive (`prop:hot-is-a-category`, ends fixed). -/
theorem trans (hfg : f.Homotopic g) (hgh : g.Homotopic h) : f.Homotopic h :=
  hfg.elim fun F => hgh.elim fun G => ⟨F.trans G⟩

/-- Path homotopy is an equivalence relation. Mathlib: `Path.Homotopic.equivalence`. -/
theorem equivalence : Equivalence (@Path.Homotopic X _ x y) := ⟨refl, symm, trans⟩

/-- `thm:groupoid-laws`, well defined: `f ≃ₚ f'` and `g ≃ₚ g'` give `f · g ≃ₚ f' · g'`.
Mathlib: `Path.Homotopic.hcomp`. -/
theorem hcomp {f f' : Path x y} {g g' : Path y z} (hf : f.Homotopic f') (hg : g.Homotopic g') :
    (f.trans g).Homotopic (f'.trans g') :=
  hf.elim fun F => hg.elim fun G => ⟨F.hcomp G⟩

/-- `f ≃ₚ g` gives `f̄ ≃ₚ ḡ`. Mathlib: `Path.Homotopic.symm₂`. -/
theorem symm₂ (hfg : f.Homotopic g) : f.symm.Homotopic g.symm := hfg.map PathHomotopy.symm₂

end Path.Homotopic

/-! ## Reparametrisation (`lem:reparam`) -/

namespace Path
variable [TopSpace X] {x y z w : X}

/-- `f ∘ φ`, the path `f` read through `φ : I → I`, for `φ` continuous (`hφ`) with `φ(0) = 0`
(`h0`) and `φ(1) = 1` (`h1`): it is again a path from `x` to `y`. Mathlib: `Path.reparam`. -/
def reparam (f : Path x y) (φ : I → I) (hφ : Continuous φ) (h0 : φ 0 = 0) (h1 : φ 1 = 1) :
    Path x y :=
  ⟨fun s => f (φ s), f.continuous.comp hφ, by simp [h0], by simp [h1]⟩

/-- Unfolding: `(f ∘ φ)(s) = f(φ(s))`. -/
@[simp] theorem reparam_apply (f : Path x y) (φ : I → I) (hφ : Continuous φ) (h0 : φ 0 = 0)
    (h1 : φ 1 = 1) (s : I) : f.reparam φ hφ h0 h1 s = f (φ s) := rfl

/-- **`lem:reparam`**: if `φ : I → I` is continuous with `φ(0) = 0` and `φ(1) = 1`, then
`f ∘ φ ≃ₚ f`. Mathlib: `Path.Homotopic.reparam` (stated the other way round).

The book's homotopy is `H(s, t) = f((1 - t) φ(s) + t s)`: at each time `t`, read `f` through
the map `(1 - t) φ + t · id`, which moves in a straight line from `φ` to the identity. In the
square `I × I`, with `s` across and `t` up:
* the bottom edge `t = 0` is `s ↦ f(φ(s))`, the path `f ∘ φ`;
* the top edge `t = 1` is `s ↦ f(s)`, the path `f`;
* the left edge `s = 0` is `f((1 - t) φ(0) + t · 0) = f(0) = x`, since `φ(0) = 0`;
* the right edge `s = 1` is `f((1 - t) φ(1) + t · 1) = f(1) = y`, since `φ(1) = 1`.
The argument `(1 - t) φ(s) + t s` stays in `I` because `I` is convex (`I.line`). -/
theorem reparam_homotopic (f : Path x y) (φ : I → I) (hφ : Continuous φ) (h0 : φ 0 = 0)
    (h1 : φ 1 = 1) : (f.reparam φ hφ h0 h1).Homotopic f :=
  -- `H = f ∘ G` with `G(s, t) = (1 - t) φ(s) + t s` (`I.line φ id`), continuous by Analysis I;
  -- `ofMap` asks for the four edges.
  ⟨PathHomotopy.ofMap f (I.line φ id) (I.continuous_line hφ continuous_id)
    -- Bottom edge: `G(s, 0) = φ(s)`. Top edge: `G(s, 1) = s`.
    (fun s => by simp) (fun s => by simp)
    -- Left edge: `G(0, t) = (1 - t) φ(0) + t · 0 = 0`, and `f(0) = x`.
    (fun t => by
      have : I.line φ id (0, t) = 0 := Subtype.ext (by simp [h0])
      rw [this, f.source])
    -- Right edge: `G(1, t) = (1 - t) φ(1) + t · 1 = 1`, and `f(1) = y`.
    (fun t => by
      have : I.line φ id (1, t) = 1 := Subtype.ext (by simp [h1])
      rw [this, f.target])⟩

/-! ## The groupoid laws (`prop:associativity`, `thm:groupoid-laws`) -/

/-- `rem:pushout-paths`: `(f · g) · h = (f · (g · h)) ∘ φ`, with `φ` piecewise linear,
`φ(1/4) = 1/2` and `φ(1/2) = 3/4` (`I.assoc`). The two products of three paths are one map
read through two parametrisations: `(f · g) · h` runs through `f`, `g`, `h` on `[0, 1/4]`,
`[1/4, 1/2]`, `[1/2, 1]`, and `f · (g · h)` on `[0, 1/2]`, `[1/2, 3/4]`, `[3/4, 1]`; `φ` sends
each interval of the first list linearly onto the matching one of the second. -/
theorem trans_assoc_eq (f : Path x y) (g : Path y z) (h : Path z w) :
    (f.trans g).trans h = (f.trans (g.trans h)).reparam I.assoc I.continuous_assoc
      I.assoc_zero I.assoc_one := by
  -- Two paths are equal if they agree at every `s ∈ I`; we compare the two sides at `s`,
  -- in three cases.
  ext s
  have hs0 := s.2.1
  rw [reparam_apply]
  rcases le_total (s : ℝ) (1 / 4) with h₁ | h₁
  -- Case `s ≤ 1/4`. Left: `((f · g) · h)(s) = (f · g)(2s) = f(4s)`, as `2s ≤ 1/2`.
  -- Right: `φ(s) = 2s ≤ 1/2`, so `(f · (g · h))(φ(s)) = f(2 · 2s) = f(4s)`.
  · have e := I.coe_assoc_of_le h₁
    have d := I.coe_dbl_of_le (s := s) (by linarith)
    rw [trans_apply_of_le (f.trans g) h s (by linarith),
      trans_apply_of_le f g (I.dbl s) (by rw [d]; linarith),
      trans_apply_of_le f (g.trans h) (I.assoc s) (by rw [e]; linarith)]
    -- Both sides are `f` at the same point; it remains to compare the arguments, `4s = 4s`.
    apply f.congr_coe
    rw [I.coe_dbl_of_le (by rw [d]; linarith), d, I.coe_dbl_of_le (by rw [e]; linarith), e]
  rcases le_total (s : ℝ) (1 / 2) with h₂ | h₂
  -- Case `1/4 ≤ s ≤ 1/2`. Left: `((f · g) · h)(s) = (f · g)(2s) = g(4s - 1)`, as `2s ≥ 1/2`.
  -- Right: `φ(s) = s + 1/4 ≥ 1/2`, so `(f · (g · h))(φ(s)) = (g · h)(2s - 1/2)`, and as
  -- `2s - 1/2 ≤ 1/2` this is `g(4s - 1)`.
  · have e := I.coe_assoc_of_mid h₁ h₂
    have d := I.coe_dbl_of_le h₂
    have e' : (I.dbl' (I.assoc s) : ℝ) = 2 * s - 1 / 2 := by
      rw [I.coe_dbl'_of_ge (by rw [e]; linarith), e]; ring
    rw [trans_apply_of_le (f.trans g) h s h₂,
      trans_apply_of_ge f g (I.dbl s) (by rw [d]; linarith),
      trans_apply_of_ge f (g.trans h) (I.assoc s) (by rw [e]; linarith),
      trans_apply_of_le g h (I.dbl' (I.assoc s)) (by rw [e']; linarith)]
    -- Both sides are `g` at `4s - 1`.
    apply g.congr_coe
    rw [I.coe_dbl'_of_ge (by rw [d]; linarith), d, I.coe_dbl_of_le (by rw [e']; linarith), e']
    ring
  -- Case `s ≥ 1/2`. Left: `((f · g) · h)(s) = h(2s - 1)`. Right: `φ(s) = (s + 1)/2 ≥ 1/2`, so
  -- `(f · (g · h))(φ(s)) = (g · h)(2φ(s) - 1) = (g · h)(s) = h(2s - 1)`, as `s ≥ 1/2`.
  · have e := I.coe_assoc_of_ge h₂
    have e' : (I.dbl' (I.assoc s) : ℝ) = s := by
      rw [I.coe_dbl'_of_ge (by rw [e]; linarith), e]; ring
    rw [trans_apply_of_ge (f.trans g) h s h₂,
      trans_apply_of_ge f (g.trans h) (I.assoc s) (by rw [e]; linarith),
      trans_apply_of_ge g h (I.dbl' (I.assoc s)) (by rw [e']; linarith)]
    -- Both sides are `h` at `2s - 1`.
    apply h.congr_coe
    rw [I.coe_dbl'_of_ge h₂, I.coe_dbl'_of_ge (by rw [e']; linarith), e']

/-- **`prop:associativity`**: if `f(1) = g(0)` and `g(1) = h(0)`, then
`(f · g) · h ≃ₚ f · (g · h)`. Mathlib: `Path.Homotopic.trans_assoc`.

The proof is the book's second one, `rem:pushout-paths` with `lem:reparam`: in the square
`I × I`, the straight-line homotopy of `lem:reparam` moves the break points of the bottom edge,
`1/4` and `1/2`, along straight lines to the break points `1/2` and `3/4` of the top edge;
these are the two slanted segments of the book's picture. -/
theorem Homotopic.trans_assoc (f : Path x y) (g : Path y z) (h : Path z w) :
    ((f.trans g).trans h).Homotopic (f.trans (g.trans h)) := by
  -- `(f · g) · h = (f · (g · h)) ∘ φ` (`rem:pushout-paths`), and `(f · (g · h)) ∘ φ ≃ₚ
  -- f · (g · h)` by `lem:reparam`.
  rw [trans_assoc_eq]; exact reparam_homotopic _ _ _ _ _

/-- `exr-4-unit`: `c_x · f` is `f` reparametrised by `s ↦ max(2s - 1, 0)`: it stays at `x` for
`s ≤ 1/2`, and then runs through `f` at double speed. -/
theorem refl_trans_eq (f : Path x y) :
    (refl x).trans f = f.reparam I.dbl' I.continuous_dbl' I.dbl'_zero I.dbl'_one := by
  ext s
  rcases le_total (s : ℝ) (1 / 2) with h | h
  -- For `s ≤ 1/2`: `(c_x · f)(s) = x`, and `f(max(2s - 1, 0)) = f(0) = x`.
  · rw [trans_apply_of_le _ _ s h, reparam_apply, I.dbl'_of_le h, refl_apply, f.source]
  -- For `s ≥ 1/2`: both sides are `f(2s - 1)`.
  · rw [trans_apply_of_ge _ _ s h, reparam_apply]

/-- `exr-4-unit`: `f · c_y` is `f` reparametrised by `s ↦ min(2s, 1)`: it runs through `f` at
double speed, and then stays at `y`. -/
theorem trans_refl_eq (f : Path x y) :
    f.trans (refl y) = f.reparam I.dbl I.continuous_dbl I.dbl_zero I.dbl_one := by
  ext s
  rcases le_total (s : ℝ) (1 / 2) with h | h
  -- For `s ≤ 1/2`: both sides are `f(2s)`.
  · rw [trans_apply_of_le _ _ s h, reparam_apply]
  -- For `s ≥ 1/2`: `(f · c_y)(s) = y`, and `f(min(2s, 1)) = f(1) = y`.
  · rw [trans_apply_of_ge _ _ s h, reparam_apply, I.dbl_of_ge h, refl_apply, f.target]

/-- **`thm:groupoid-laws`**, `exr-4-unit`: `c_x · f ≃ₚ f`, for `f` a path from `x` to `y`.
Mathlib: `Path.Homotopic.refl_trans`.

`c_x · f` is `f ∘ φ` with `φ(s) = max(2s - 1, 0)` (`refl_trans_eq`), so `lem:reparam` applies.
The homotopy is `H(s, t) = f((1 - t) max(2s - 1, 0) + t s)`: in the square, the bottom edge
waits at `x` until `s = 1/2`, the top edge is `f`, and the waiting shrinks to nothing. -/
theorem Homotopic.refl_trans (f : Path x y) : ((Path.refl x).trans f).Homotopic f := by
  rw [refl_trans_eq]; exact reparam_homotopic _ _ _ _ _

/-- **`thm:groupoid-laws`**, `exr-4-unit`: `f · c_y ≃ₚ f`. Mathlib: `Path.Homotopic.trans_refl`.

`f · c_y` is `f ∘ φ` with `φ(s) = min(2s, 1)` (`trans_refl_eq`), so `lem:reparam` applies. -/
theorem Homotopic.trans_refl (f : Path x y) : (f.trans (Path.refl y)).Homotopic f := by
  rw [trans_refl_eq]; exact reparam_homotopic _ _ _ _ _

/-- **`thm:groupoid-laws`**, `exr-4-inverse`: `f · f̄ ≃ₚ c_x`, for `f` a path from `x` to `y`.
Mathlib: `Path.Homotopic.trans_symm`.

At time `t`, go along `f` only as far as `f(1 - t)`, and come back:
`H(s, t) = f((1 - t) · min(2s, 2 - 2s))`. In the square `I × I`, with `s` across and `t` up:
* the bottom edge `t = 0` is `f(min(2s, 2 - 2s))`: `f(2s)` on `[0, 1/2]` and
  `f(2 - 2s) = f̄(2s - 1)` on `[1/2, 1]`, which is `f · f̄`;
* the top edge `t = 1` is `f(0) = x`, the constant path `c_x`;
* the left and right edges `s = 0`, `s = 1` are `f(0) = x`, since the tent is `0` there. -/
theorem Homotopic.trans_symm (f : Path x y) : (f.trans f.symm).Homotopic (Path.refl x) :=
  -- `H = f ∘ G` with `G(s, t) = (1 - t) tent(s) + t · 0` (`I.line I.tent 0`), continuous by
  -- Analysis I; `ofMap` asks for the four edges.
  ⟨PathHomotopy.ofMap f (I.line I.tent fun _ => 0)
    (I.continuous_line I.continuous_tent continuous_const)
    -- Bottom edge: `f(tent(s)) = (f · f̄)(s)`.
    (fun s => by
      rw [I.line_zero]
      rcases le_total (s : ℝ) (1 / 2) with h | h
      -- For `s ≤ 1/2`: `(f · f̄)(s) = f(2s)`, and `tent(s) = min(2s, 2 - 2s) = 2s`.
      · rw [trans_apply_of_le _ _ s h]
        apply f.congr_coe
        rw [I.coe_dbl_of_le h, I.coe_tent]; exact min_eq_left (by linarith)
      -- For `s ≥ 1/2`: `(f · f̄)(s) = f̄(2s - 1) = f(1 - (2s - 1)) = f(2 - 2s)`, and
      -- `tent(s) = 2 - 2s`.
      · rw [trans_apply_of_ge _ _ s h, symm_apply]
        apply f.congr_coe
        rw [I.coe_rev, I.coe_dbl'_of_ge h, I.coe_tent, min_eq_right (by linarith)]; ring)
    -- Top edge: `G(s, 1) = 0`, so `H(s, 1) = f(0) = x = c_x(s)`.
    (fun s => by simp)
    -- Left edge: `G(0, t) = (1 - t) · tent(0) = 0`, and `f(0) = x`.
    (fun t => by
      have : I.line I.tent (fun _ => 0) (0, t) = 0 := Subtype.ext (by simp)
      rw [this, f.source])
    -- Right edge: `G(1, t) = (1 - t) · tent(1) = 0`, and `f(0) = x`.
    (fun t => by
      have : I.line I.tent (fun _ => 0) (1, t) = 0 := Subtype.ext (by norm_num)
      rw [this, f.source])⟩

/-- **`thm:groupoid-laws`**, `exr-4-inverse`: `f̄ · f ≃ₚ c_y`, without a second picture: apply
the first law to `f̄`, whose reverse is `f`. Mathlib: `Path.Homotopic.symm_trans`. -/
theorem Homotopic.symm_trans (f : Path x y) : (f.symm.trans f).Homotopic (Path.refl y) := by
  -- The first inverse law for the path `f̄` from `y` to `x` gives `f̄ · f̄̄ ≃ₚ c_y`, and
  -- `f̄̄ = f` (`symm_symm`).
  have := Homotopic.trans_symm f.symm
  rwa [symm_symm] at this

end Path

/-! ## The fundamental groupoid and `π₁` (`def:fundamental-groupoid`, `cor:pi1-group`) -/

/-- Path homotopy as a setoid on the paths from `x` to `y`: the set of paths together with the
equivalence relation `≃ₚ`, ready to be divided by it. Mathlib: `Path.Homotopic.setoid`. -/
instance pathSetoid [TopSpace X] (x y : X) : Setoid (Path x y) :=
  ⟨Path.Homotopic, Path.Homotopic.equivalence⟩

/-- `def:fundamental-groupoid`: the morphisms `x → y` of `Π₁(X)`, the path classes `[f]`: the
quotient of the paths from `x` to `y` by `≃ₚ`. Mathlib: `Path.Homotopic.Quotient`. -/
abbrev PathClass [TopSpace X] (x y : X) := Quotient (pathSetoid x y)

namespace PathClass
variable [TopSpace X] {x y z w : X}

/-- `thm:groupoid-laws`: `[f][g] = [f · g]`, well defined by `Path.Homotopic.hcomp`: if
`f ≃ₚ f'` and `g ≃ₚ g'`, then `f · g ≃ₚ f' · g'`. Mathlib: `Path.Homotopic.Quotient.trans`.

Lean: `Quotient.map₂ F h` defines a map on classes by `[f], [g] ↦ [F f g]`, and `h` is the
proof that the result does not depend on the representatives. -/
def comp : PathClass x y → PathClass y z → PathClass x z :=
  Quotient.map₂ Path.trans fun _ _ hf _ _ hg => Path.Homotopic.hcomp hf hg

/-- The inverse `[f̄]`, well defined because `f ≃ₚ g` gives `f̄ ≃ₚ ḡ` (`Path.Homotopic.symm₂`).
Mathlib: `Path.Homotopic.Quotient.symm`. -/
def inv : PathClass x y → PathClass y x :=
  Quotient.map Path.symm fun _ _ h => Path.Homotopic.symm₂ h

/-- The identity `[c_x]`. Mathlib: `Path.Homotopic.Quotient.refl`. -/
def refl (x : X) : PathClass x x := ⟦Path.refl x⟧

/-- Unfolding: `[f][g] = [f · g]`. -/
theorem comp_mk (f : Path x y) (g : Path y z) :
    comp (⟦f⟧ : PathClass x y) ⟦g⟧ = ⟦f.trans g⟧ := rfl

/-- Unfolding: `[f]⁻¹ = [f̄]`. -/
theorem inv_mk (f : Path x y) : inv (⟦f⟧ : PathClass x y) = ⟦f.symm⟧ := rfl

/-- `thm:groupoid-laws`: the product of classes is associative (`prop:associativity`). -/
theorem comp_assoc (a : PathClass x y) (b : PathClass y z) (c : PathClass z w) :
    comp (comp a b) c = comp a (comp b c) := by
  -- Write `a = [f]`, `b = [g]`, `c = [h]`. Then the claim is `[(f · g) · h] = [f · (g · h)]`,
  -- which is `prop:associativity`.
  induction a using Quotient.ind; induction b using Quotient.ind; induction c using Quotient.ind
  exact Quotient.sound (Path.Homotopic.trans_assoc _ _ _)

/-- `thm:groupoid-laws`: `[c_x][f] = [f]`. -/
theorem id_comp (a : PathClass x y) : comp (refl x) a = a := by
  -- Write `a = [f]`; then `[c_x · f] = [f]` because `c_x · f ≃ₚ f`.
  induction a using Quotient.ind
  exact Quotient.sound (Path.Homotopic.refl_trans _)

/-- `thm:groupoid-laws`: `[f][c_y] = [f]`. -/
theorem comp_id (a : PathClass x y) : comp a (refl y) = a := by
  -- Write `a = [f]`; then `[f · c_y] = [f]` because `f · c_y ≃ₚ f`.
  induction a using Quotient.ind
  exact Quotient.sound (Path.Homotopic.trans_refl _)

/-- `thm:groupoid-laws`: `[f][f̄] = [c_x]`. -/
theorem comp_inv (a : PathClass x y) : comp a (inv a) = refl x := by
  -- Write `a = [f]`; then `[f · f̄] = [c_x]` because `f · f̄ ≃ₚ c_x`.
  induction a using Quotient.ind
  exact Quotient.sound (Path.Homotopic.trans_symm _)

/-- `thm:groupoid-laws`: `[f̄][f] = [c_y]`. -/
theorem inv_comp (a : PathClass x y) : comp (inv a) a = refl y := by
  -- Write `a = [f]`; then `[f̄ · f] = [c_y]` because `f̄ · f ≃ₚ c_y`.
  induction a using Quotient.ind
  exact Quotient.sound (Path.Homotopic.symm_trans _)

end PathClass

/-- `def:fundamental-groupoid`, `cor:pi1-group`: `π₁(X, x)`, the classes of loops at `x`, the
morphisms `x → x` of `Π₁(X)`. Mathlib: `FundamentalGroup` (see `pi1MulEquiv`). -/
abbrev pi1 [TopSpace X] (x : X) : Type u := PathClass x x

/-- **`cor:pi1-group`**: `π₁(X, x)` is a group under `[f][g] = [f · g]`, with identity `[c_x]`
and inverse `[f̄]`, by `thm:groupoid-laws`. Mathlib: `FundamentalGroup`'s `Group` instance,
whose product is written the other way round (`FundamentalGroup.mul_def`).

Lean: an `instance` of `Group` gives the product, the identity, the inverse and the proofs of
the group axioms; after it, Lean writes `a * b`, `1`, `a⁻¹` in `π₁(X, x)`. -/
instance pi1.instGroup [TopSpace X] (x : X) : Group (pi1 x) where
  mul := PathClass.comp
  one := PathClass.refl x
  inv := PathClass.inv
  -- The axioms are the groupoid laws for loops at `x`.
  mul_assoc := PathClass.comp_assoc
  one_mul := PathClass.id_comp
  mul_one := PathClass.comp_id
  inv_mul_cancel := PathClass.inv_comp

/-! ## Bridges to Mathlib's paths, path homotopies and fundamental group

With the Mathlib topology `t.toMathlib` on `X` (week 1's bridge), a course path is a Mathlib
`Path`, and back; path homotopy is Mathlib's `Path.Homotopic`; and `π₁` is `FundamentalGroup`.
These are for comparison only; nothing above uses them. -/

/-- The reverse of a product is the product of the reverses, in the other order:
`(f · g)‾ = ḡ · f̄`. Mathlib: `Path.trans_symm`. -/
theorem Path.trans_symm_eq [TopSpace X] {x y z : X} (f : Path x y) (g : Path y z) :
    (f.trans g).symm = g.symm.trans f.symm := by
  -- Compare at `s`: the left side is `(f · g)(1 - s)`.
  ext s
  have hs := s.2
  rw [Path.symm_apply]
  rcases le_total (s : ℝ) (1 / 2) with h | h
  -- For `s ≤ 1/2`, `1 - s ≥ 1/2`, so the left side is `g(2(1 - s) - 1) = g(1 - 2s)`; the right
  -- side is `ḡ(2s) = g(1 - 2s)`.
  · rw [Path.trans_apply_of_ge _ _ _ (by simp; linarith), Path.trans_apply_of_le _ _ _ h,
      Path.symm_apply]
    apply g.congr_coe
    rw [I.coe_dbl'_of_ge (by simp; linarith), I.coe_rev, I.coe_rev, I.coe_dbl_of_le h]; ring
  -- For `s ≥ 1/2`, `1 - s ≤ 1/2`, so the left side is `f(2 - 2s)`; the right side is
  -- `f̄(2s - 1) = f(2 - 2s)`.
  · rw [Path.trans_apply_of_le _ _ _ (by simp; linarith), Path.trans_apply_of_ge _ _ _ h,
      Path.symm_apply]
    apply f.congr_coe
    rw [I.coe_dbl_of_le (by simp; linarith), I.coe_rev, I.coe_rev, I.coe_dbl'_of_ge h]; ring

section Bridge
variable [t : TopSpace X] {x y z : X}

/-- **Bridge.** A course path is a Mathlib `Path` (for the topology `t.toMathlib`): the same map,
continuous in Mathlib's sense by the bridge. -/
def Path.toMathlib (f : Path x y) : @_root_.Path X t.toMathlib x y :=
  @_root_.Path.mk X t.toMathlib x y
    (@ContinuousMap.mk unitInterval X _ t.toMathlib f.toFun
      (mathlib_continuous_of_eq I_toMathlib rfl f.continuous))
    f.source f.target

/-- **Bridge.** A Mathlib `Path` is a course path. -/
def Path.ofMathlib (f : @_root_.Path X t.toMathlib x y) : Path x y :=
  let _ := t.toMathlib
  ⟨f, continuous_of_mathlib_eq I_toMathlib rfl f.continuous, f.source, f.target⟩

/-- Unfolding: the Mathlib path `f.toMathlib` is the map `f`. -/
theorem Path.toMathlib_apply (f : Path x y) (s : I) : f.toMathlib s = f s := rfl

/-- The two bridges are inverse: course → Mathlib → course is the identity. -/
theorem Path.ofMathlib_toMathlib (f : Path x y) : Path.ofMathlib f.toMathlib = f := rfl

/-- The two bridges are inverse: Mathlib → course → Mathlib is the identity. -/
theorem Path.toMathlib_ofMathlib (f : @_root_.Path X t.toMathlib x y) :
    (Path.ofMathlib f).toMathlib = f := rfl

/-- **Bridge.** The course's product of paths is Mathlib's `Path.trans`. -/
theorem Path.toMathlib_trans (f : Path x y) (g : Path y z) :
    (f.trans g).toMathlib = @_root_.Path.trans X t.toMathlib x y z f.toMathlib g.toMathlib := by
  let _ := t.toMathlib
  -- Compare at `s`: Mathlib's product is also `f(2s)` for `s ≤ 1/2` and `g(2s - 1)` otherwise,
  -- without the clamps.
  ext s
  rw [_root_.Path.trans_apply, Path.toMathlib_apply]
  split_ifs with h
  · rw [Path.trans_apply_of_le _ _ _ h]
    exact f.congr_coe (I.coe_dbl_of_le h)
  · rw [Path.trans_apply_of_ge _ _ _ (le_of_lt (not_le.1 h))]
    exact g.congr_coe (I.coe_dbl'_of_ge (le_of_lt (not_le.1 h)))

/-- **Bridge.** The course's path homotopy is Mathlib's `Path.Homotopic`; Mathlib's homotopies
put the time first, so the two factors of `I × I` are swapped. -/
theorem Path.homotopic_iff_mathlib {f g : Path x y} :
    f.Homotopic g ↔ @_root_.Path.Homotopic X t.toMathlib x y f.toMathlib g.toMathlib := by
  let _ := t.toMathlib
  constructor
  -- From a course path homotopy `F`, Mathlib's is `(t, s) ↦ F(s, t)`; its ends are fixed
  -- because `F`'s are.
  · rintro ⟨F⟩
    have hF : _root_.Continuous F.toFun :=
      mathlib_continuous_of_eq II_toMathlib rfl F.continuous_toFun
    refine ⟨{ toFun := fun p => F.toFun (p.2, p.1)
              continuous_toFun := hF.comp _root_.continuous_swap
              map_zero_left := fun s => F.zero' s
              map_one_left := fun s => F.one' s
              prop' := ?_ }⟩
    intro τ s hs
    rcases hs with rfl | rfl
    · exact (F.source' τ).trans f.source.symm
    · exact (F.target' τ).trans f.target.symm
  -- Conversely, from Mathlib's `F`, the course's is `(s, t) ↦ F(t, s)`.
  · rintro ⟨F⟩
    refine ⟨{ toFun := fun p => F (p.2, p.1)
              continuous_toFun :=
                continuous_of_mathlib_eq II_toMathlib rfl (F.continuous.comp _root_.continuous_swap)
              zero' := fun s => F.apply_zero s
              one' := fun s => F.apply_one s
              source' := fun τ => (F.eq_fst τ (by simp)).trans f.source
              target' := fun τ => (F.eq_fst τ (by simp)).trans f.target }⟩

/-- **Bridge.** `π₁(X, x)` is Mathlib's `FundamentalGroup X x`. Mathlib writes the product of
its loop classes the other way round (`FundamentalGroup.mul_def`: `p * q` is `q` then `p`, as
morphisms compose), so the isomorphism sends `[f]` to the class of the reverse `f̄`, and
`[f · g] ↦ [ḡ · f̄]`, which is the product of `[f̄]` and `[ḡ]` in Mathlib's order. -/
def pi1MulEquiv (x : X) : pi1 x ≃* @FundamentalGroup X t.toMathlib x := by
  let _ := t.toMathlib
  exact
  -- The map `[f] ↦ [f̄]`, well defined because `f ≃ₚ g` gives `f̄ ≃ₚ ḡ`.
  { toFun := Quotient.lift
      (fun f : Path x x =>
        (_root_.Path.Homotopic.Quotient.mk f.symm.toMathlib : FundamentalGroup X x))
      (fun _ _ h => _root_.Path.Homotopic.Quotient.eq.mpr
        (Path.homotopic_iff_mathlib.mp (Path.Homotopic.symm₂ h)))
    -- Its inverse is again `[q] ↦ [q̄]`, since `f̄̄ = f`.
    invFun := fun p => Quotient.lift
      (fun q : _root_.Path x x => (⟦(Path.ofMathlib q).symm⟧ : PathClass x x))
      (fun _ _ h => Quotient.sound (Path.Homotopic.symm₂ (Path.homotopic_iff_mathlib.mpr h)))
      (FundamentalGroup.toPath p)
    left_inv := by
      intro a
      induction a using Quotient.ind with | _ f => ?_
      show (⟦(Path.ofMathlib f.symm.toMathlib).symm⟧ : PathClass x x) = ⟦f⟧
      rw [Path.ofMathlib_toMathlib, Path.symm_symm]
    right_inv := by
      intro p
      induction p using _root_.Path.Homotopic.Quotient.ind with | _ q => ?_
      show _root_.Path.Homotopic.Quotient.mk (Path.ofMathlib q).symm.symm.toMathlib = _
      rw [Path.symm_symm, Path.toMathlib_ofMathlib]
    -- It is a homomorphism because `(f · g)‾ = ḡ · f̄` (`Path.trans_symm_eq`).
    map_mul' := by
      intro a b
      induction a using Quotient.ind with | _ f => ?_
      induction b using Quotient.ind with | _ g => ?_
      show _root_.Path.Homotopic.Quotient.mk (f.trans g).symm.toMathlib =
        _root_.Path.Homotopic.Quotient.mk (g.symm.toMathlib.trans f.symm.toMathlib)
      rw [Path.trans_symm_eq, Path.toMathlib_trans] }

end Bridge

end

end Course
