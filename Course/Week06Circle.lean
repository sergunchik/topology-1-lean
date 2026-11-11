/-
Machine-generated (Claude, Aristotle), no line written by a person. Copyleft: GPL-3.0-or-later.

# Week 6: consequences of `π₁(S¹) ≅ ℤ`; the circle among the one-dimensional spaces

This file draws the consequences of `π₁(S¹, 1) ≅ ℤ` (`thm:pi1-circle`, `Week06.lean`) that the
book lists in `cor:circle-consequences`: `π₁(T²) ≅ ℤ²` for the torus `T² = S¹ × S¹`,
`π₁(ℝ² ∖ {0}) ≅ ℤ` and `π₁` of the cylinder `S¹ × [0, 1]` is `ℤ`; so `S¹` and `T²` are not
homotopy equivalent and neither is contractible, and the disc is not homeomorphic to the circle.
The tools are the product formula `π₁(X × Y) ≅ π₁(X) × π₁(Y)` (`prop:pi1-product`) and the
homotopy invariance of `π₁` (`thm:pi1-homotopy-invariant`). It also proves the three cases of
`thm:one-dimensional` that involve the circle, `S¹ ≇ ℝ, [0, 1], [0, 1)` (week 2): removing a
point never disconnects `S¹`, and it does disconnect the other three.

Departures from the book:
* `ℤ ≇ ℤ²` is proved without counting `G/2G` (see `int_not_mulEquiv_int_prod`).
* `S¹` is separated from `ℝ` and `[0, 1)` by cut points, as in `rem:non-cut-count`, rather than
  by compactness.
* The Möbius band is not done.
* From Analysis I, through the bridges: the continuity of real formulas (arithmetic, `√`,
  division by a non-vanishing function), `(√a)² = a` for `a ≥ 0`, and the integer part `⌊x⌋`
  with `⌊x⌋ ≤ x < ⌊x⌋ + 1`. The connectedness of intervals is week 2's
  (`connected_of_ordConnected`, from the connectedness of `[0, 1]`). Mathlib's names below were
  checked against Lean and Mathlib v4.34.1.

New to Lean? Read `Course/README.md` first.
-/
import Course.Week03Hot
import Course.Week02Glue

-- Bookkeeping, as in `Week06.lean`: `X`, `Y` are spaces, and `open Set Real` shortens names.
universe u v

set_option warn.classDefReducibility false

namespace Course

open Set Real

noncomputable section

variable {X : Type u} {Y : Type v}

/-! ## `π₁` of the circle at any point -/

/-- The path `s ↦ p(a s)` from `1` to `p(a)` in `S¹`. -/
def S1.pathTo (a : ℝ) : Path (1 : S1) (p a) where
  -- Continuous as a composite; it starts at `p(0) = 1` and ends at `p(a)`.
  toFun s := p (a * (s : ℝ))
  continuous_toFun := continuous_p.comp
    (continuous_of_mathlib_eq I_toMathlib real_toMathlib (f := fun s : I => a * (s : ℝ))
      (by fun_prop))
  source' := by simp
  target' := by simp

/-- `S¹` is path-connected: every point `z = p(a)` is joined to `1` by `s ↦ p(a s)`. -/
theorem S1.exists_path (z : S1) : Nonempty (Path (1 : S1) z) := by
  -- Write `z = p(a)` (`p` is onto). (Lean: `rfl` in the pattern replaces `z` by `p(a)`.)
  obtain ⟨a, rfl⟩ := p_surjective z
  exact ⟨S1.pathTo a⟩

/-- `thm:pi1-circle` at any base point `z ∈ S¹`: `π₁(S¹, z) ≅ ℤ`, by `thm:change-basepoint`
along a path `h` from `1` to `z`: `π₁(S¹, z) ≅ π₁(S¹, 1) ≅ ℤ` (the inverse of `β_h`, then the
degree). Mathlib: none (see `pi1Circle`).

Lean: `Classical.choice` picks a path from the proof that one exists; `e.symm` is the inverse
of an isomorphism `e`, and `e.trans e'` the composite "first `e`, then `e'`". -/
def pi1CircleAt (z : S1) : pi1 z ≃* Multiplicative ℤ :=
  (beta (Classical.choice (S1.exists_path z))).symm.trans pi1Circle

/-- `thm:pi1-circle`: `π₁(S¹, 1)` is not trivial: the class of `s ↦ e^{2πis}` is not `1`. -/
theorem pi1Circle_ne_one : (⟦windLoop 1⟧ : pi1 (1 : S1)) ≠ 1 := by
  -- If it were `1`, its degree would be `0`; but it is `1` (`pi1Circle_windLoop_one`), and
  -- `1 ≠ 0` in `ℤ`. (`ℤ` is written multiplicatively, `README.md`: there `0` is written `1`.)
  intro h
  have h2 := congrArg pi1Circle h
  rw [map_one, pi1Circle_windLoop_one] at h2
  exact one_ne_zero (ofAdd_eq_one.mp h2)

/-! ## The torus (`cor:circle-consequences`) -/

/-- **`cor:circle-consequences`**, the torus `T² = S¹ × S¹`: `π₁(T², (1, 1)) ≅ ℤ²`, by
`prop:pi1-product` and `thm:pi1-circle`: `π₁(T²) ≅ π₁(S¹) × π₁(S¹) ≅ ℤ × ℤ`. Mathlib: none
(`FundamentalGroupoidFunctor.prodIso` for the product). (Lean: `MulEquiv.prodCongr e e'` is the
isomorphism `(a, b) ↦ (e a, e' b)` of products.) -/
def pi1Torus : pi1 (((1 : S1), (1 : S1)) : S1 × S1) ≃* Multiplicative ℤ × Multiplicative ℤ :=
  (pi1Prod (1 : S1) (1 : S1)).trans (MulEquiv.prodCongr pi1Circle pi1Circle)

/-- `cor:circle-consequences`, the torus at any base point `(z, w)`: `π₁(T², (z, w)) ≅ ℤ²`. -/
def pi1TorusAt (z w : S1) : pi1 ((z, w) : S1 × S1) ≃* Multiplicative ℤ × Multiplicative ℤ :=
  (pi1Prod z w).trans (MulEquiv.prodCongr (pi1CircleAt z) (pi1CircleAt w))

/-! ## `ℤ ≇ ℤ²`, and the circle is neither the torus nor contractible -/

/-- `cor:circle-consequences`, the algebra: `ℤ ≇ ℤ²`. Mathlib: none as such
(`Module.finrank`).

The book counts `G/2G` (two elements against four); here a shorter argument: in `ℤ` any two
elements `a`, `b` satisfy `b·a = a·b` (as multiples of `1`), so an isomorphism `e : ℤ ≅ ℤ²` would
give `b·(1, 0) = a·(0, 1)` for `a = e⁻¹(1, 0)`, `b = e⁻¹(0, 1)`, forcing `b = 0` and
`e⁻¹(0, 1) = 0`.

(Lean: in `ℤ` written multiplicatively, the multiple `b·a` is the power `A ^ b`, and
`toAdd` turns `A` back into an ordinary integer.) -/
theorem int_not_mulEquiv_int_prod :
    ¬ Nonempty (Multiplicative ℤ ≃* Multiplicative ℤ × Multiplicative ℤ) := by
  -- Suppose `e : ℤ ≅ ℤ²`; let `a = e⁻¹(1, 0)` and `b = e⁻¹(0, 1)` (`A`, `B` below).
  rintro ⟨e⟩
  set A := e.symm (Multiplicative.ofAdd 1, 1)
  set B := e.symm (1, Multiplicative.ofAdd 1)
  -- Step 1. `b·a = a·b` in `ℤ`: multiplication of integers is commutative.
  have hcomm : A ^ (Multiplicative.toAdd B) = B ^ (Multiplicative.toAdd A) := by
    apply Multiplicative.toAdd.injective
    simp only [toAdd_zpow, smul_eq_mul, mul_comm]
  -- Step 2. Apply the homomorphism `e`: `b·(1, 0) = a·(0, 1)`, that is `(b, 0) = (0, a)`.
  have h := congrArg e hcomm
  rw [map_zpow, map_zpow, e.apply_symm_apply, e.apply_symm_apply] at h
  -- Step 3. First coordinates: `b = 0`.
  have hB : Multiplicative.toAdd B = 0 := by
    have := congrArg (fun q => Multiplicative.toAdd q.1) h
    simpa using this
  have hB1 : B = 1 := Multiplicative.toAdd.injective hB
  -- Step 4. Then `(0, 1) = e(b) = e(0) = (0, 0)`; second coordinates give `1 = 0`.
  have he : e B = (1, Multiplicative.ofAdd 1) := e.apply_symm_apply _
  rw [hB1, MulEquiv.map_one e] at he
  have := congrArg (fun q => Multiplicative.toAdd q.2) he
  simp at this

/-- `thm:pi1-homotopy-invariant` applied to the circle: a space `Y` homotopy equivalent to `S¹`
by `φ : S¹ → Y` (`hφ`: `φ` is a homotopy equivalence, `def:homotopy-equivalence`) has
`π₁(Y, φ(1)) ≅ ℤ`: `π₁(Y, φ(1)) ≅ π₁(S¹, 1) ≅ ℤ`. -/
def pi1EquivCircle {φ : S1 → Y} [TopSpace Y] (hφ : IsHomotopyEquiv φ) :
    pi1 (φ 1) ≃* Multiplicative ℤ :=
  (pi1EquivOfIsHomotopyEquiv hφ 1).symm.trans pi1Circle

/-- **`cor:circle-consequences`**: `S¹` and `T² = S¹ × S¹` are not homotopy equivalent. A
homotopy equivalence `φ : S¹ → T²` would give `ℤ ≅ π₁(S¹, 1) ≅ π₁(T², φ(1)) ≅ ℤ²`
(`thm:pi1-homotopy-invariant`, `prop:pi1-product`, `thm:pi1-circle` at `φ(1)`), and `ℤ ≇ ℤ²`.
Mathlib: none. -/
theorem S1_not_homotopyEquivalent_torus : ¬ HomotopyEquivalent S1 (S1 × S1) := by
  -- Let `φ : S¹ → T²` be a homotopy equivalence. With `φ(1) = (z, w)`, compose
  -- `ℤ ≅ π₁(S¹, 1) ≅ π₁(T², (z, w)) ≅ ℤ²` and contradict `ℤ ≇ ℤ²`.
  rintro ⟨φ, hφ⟩
  exact int_not_mulEquiv_int_prod
    ⟨(pi1EquivCircle hφ).symm.trans (pi1TorusAt (φ 1).1 (φ 1).2)⟩

/-- `cor:circle-consequences`: a space `Y` whose fundamental groups are all trivial (`hY`; e.g.
a contractible space, or the disc) is not homotopy equivalent to `S¹`: `ℤ ≅ π₁(Y, φ(1)) = 1` is
absurd. -/
theorem S1_not_homotopyEquivalent_of_pi1_trivial [TopSpace Y]
    (hY : ∀ (y : Y) (a : pi1 y), a = 1) : ¬ HomotopyEquivalent S1 Y := by
  -- `φ_* : π₁(S¹, 1) → π₁(Y, φ(1))` is one to one (`thm:pi1-homotopy-invariant`), and
  -- `φ_*[s ↦ e^{2πis}] = 1 = φ_*(1)` since `π₁(Y, φ(1)) = 1`; so `[s ↦ e^{2πis}] = 1`, which
  -- `pi1Circle_ne_one` forbids.
  rintro ⟨φ, hφ⟩
  apply pi1Circle_ne_one
  apply (pi1EquivOfIsHomotopyEquiv hφ 1).injective
  rw [map_one]
  exact hY _ _

/-- **`cor:circle-consequences`**: `S¹` is not contractible. A contractible space is simply
connected (`cor:contractible-sc`), while `π₁(S¹, 1) ≅ ℤ` is not trivial. Mathlib: none in
v4.34.1 (the statement would be `¬ ContractibleSpace Circle`). (Lean: `h.simplyConnected.2`
is the second half of "simply connected": every `π₁(X, x)` is trivial.) -/
theorem S1_not_contractible : ¬ Contractible S1 := fun h =>
  pi1Circle_ne_one (h.simplyConnected.2 1 _)

/-- **`cor:circle-consequences`**: the torus `T²` is not contractible: `π₁(T²) ≅ ℤ² ≠ 1`.
Mathlib: none. -/
theorem torus_not_contractible : ¬ Contractible (S1 × S1) := fun h => by
  -- If `T²` were contractible, `π₁(T², (1, 1))` would be trivial (`cor:contractible-sc`), so
  -- the element that `π₁(T²) ≅ ℤ²` sends to `(1, 0)` would be `1`, and `(1, 0) = (0, 0)`.
  have h1 := h.simplyConnected.2 (1, 1) (pi1Torus.symm (Multiplicative.ofAdd 1, 1))
  have h2 := congrArg pi1Torus h1
  rw [MulEquiv.apply_symm_apply, MulEquiv.map_one pi1Torus] at h2
  have := congrArg (fun q => Multiplicative.toAdd q.1) h2
  simp at this

/-! ## The cylinder (`cor:circle-consequences`) -/

/-- `def:contractible`: `I = [0, 1]` is contractible, by the straight-line homotopy
`(s, t) ↦ (1 - t) s` to the constant `0` (`I` is convex). Mathlib: `Convex.contractibleSpace`
(for the convex set `Set.Icc 0 1`). -/
theorem I_contractible : Contractible I :=
  -- The point `0` and the homotopy `I.line` from `s ↦ s` to `s ↦ 0`, which is
  -- `(s, t) ↦ (1 - t) s + t · 0` (week 4); it is continuous, the identity at `t = 0` and `0` at
  -- `t = 1`.
  ⟨0, ⟨{ toFun := I.line (fun s => s) (fun _ => 0)
         continuous_toFun := I.continuous_line continuous_id continuous_const
         zero' := I.line_zero _ _
         one' := I.line_one _ _ }⟩⟩

/-- **`cor:circle-consequences`**, the cylinder: `π₁(S¹ × [0, 1]) ≅ ℤ`, by `prop:pi1-product`
and `π₁([0, 1]) = 1` (`I` is contractible, `cor:contractible-sc`): the projection
`π₁(S¹) × π₁(I) → π₁(S¹)` is an isomorphism. Mathlib: none.

The projection `(a, b) ↦ a` (`MonoidHom.fst`) is one to one because the second coordinate `b`
lies in `π₁(I, 0) = 1` (`hI`), and onto since `a = (a, 1) ↦ a`. -/
def pi1Cylinder : pi1 (((1 : S1), (0 : I)) : S1 × I) ≃* Multiplicative ℤ :=
  have hI := I_contractible.simplyConnected.2 (0 : I)
  (pi1Prod (1 : S1) (0 : I)).trans
    ((MulEquiv.ofBijective (MonoidHom.fst (pi1 (1 : S1)) (pi1 (0 : I)))
      ⟨fun a b hab => Prod.ext hab ((hI a.2).trans (hI b.2).symm),
        fun a => ⟨(a, 1), rfl⟩⟩).trans pi1Circle)

/-! ## The punctured plane `ℝ² ∖ {0}` (`cor:circle-consequences`, `ex-3n-he`) -/

/-- The punctured plane `ℝ² ∖ {0}`, a subspace of the course's `ℝ × ℝ` (`def-1-14`).
Mathlib: `({0}ᶜ : Set (ℝ × ℝ))`. -/
def Plane0 : Set (ℝ × ℝ) := {q | q ≠ 0}

/-- A point of `S¹` is not `0`: `0² + 0² ≠ 1`. -/
theorem S1.ne_zero (z : S1) : (z : ℝ × ℝ) ≠ 0 := fun h => by
  have := S1.sq_add_sq z
  rw [h] at this
  norm_num at this

namespace Plane0

/-- The base point `(1, 0)`, which is not `(0, 0)` as its first coordinate is `1 ≠ 0`. -/
def one : Plane0 := ⟨(1, 0), fun h => by simpa using congrArg Prod.fst h⟩

/-- `|x|² > 0` for `x ≠ 0` (Analysis I). -/
theorem sq_pos (x : Plane0) : 0 < x.1.1 ^ 2 + x.1.2 ^ 2 := by
  -- If `x₁² + x₂² ≤ 0`, then `x₁² = x₂² = 0` (squares are `≥ 0`), so `x₁ = x₂ = 0` and `x = 0`.
  have hx : x.1 ≠ 0 := x.2
  by_contra h
  have h1 : x.1.1 ^ 2 = 0 := by nlinarith [sq_nonneg x.1.1, sq_nonneg x.1.2]
  have h2 : x.1.2 ^ 2 = 0 := by nlinarith [sq_nonneg x.1.1, sq_nonneg x.1.2]
  exact hx (Prod.ext (pow_eq_zero_iff two_ne_zero |>.mp h1) (pow_eq_zero_iff two_ne_zero |>.mp h2))

/-- `|x| = √(x₁² + x₂²) > 0` for `x ≠ 0` (Analysis I, `Real.sqrt_pos`). -/
theorem norm_pos (x : Plane0) : 0 < √(x.1.1 ^ 2 + x.1.2 ^ 2) := Real.sqrt_pos.mpr (sq_pos x)

/-- The factor `c(x, t) = (1 - t) + t/|x|` of `H(x, t) = (1 - t) x + t x/|x| = c(x, t) x`. -/
def scale (x : Plane0) (t : I) : ℝ := (1 - (t : ℝ)) + (t : ℝ) / √(x.1.1 ^ 2 + x.1.2 ^ 2)

/-- `c(x, t) > 0`: for `t < 1`, `1 - t > 0` and `t/|x| ≥ 0`; for `t = 1`, `c = 1/|x| > 0`. -/
theorem scale_pos (x : Plane0) (t : I) : 0 < scale x t := by
  have hn := norm_pos x
  have h0 : 0 ≤ (t : ℝ) / √(x.1.1 ^ 2 + x.1.2 ^ 2) := div_nonneg t.2.1 hn.le
  rcases lt_or_eq_of_le t.2.2 with h | h
  · unfold scale; linarith
  · unfold scale; rw [h, sub_self, zero_add]; exact div_pos one_pos hn

/-- `cor:circle-consequences`, `ex-3n-he`: the deformation `H(x, t) = (1 - t) x + t x/|x|`
of `ℝ² ∖ {0}` onto `S¹`; it stays away from `0`, being a positive multiple of `x`. -/
def deform (q : Plane0 × I) : Plane0 :=
  -- The point `c x` with the proof that it is not `0`: if `c x = 0`, then `x = 0` as `c ≠ 0`.
  ⟨(scale q.1 q.2 * q.1.1.1, scale q.1 q.2 * q.1.1.2), fun h => by
    have hc := (scale_pos q.1 q.2).ne'
    have h1 : q.1.1.1 = 0 := (mul_eq_zero.mp (congrArg Prod.fst h)).resolve_left hc
    have h2 : q.1.1.2 = 0 := (mul_eq_zero.mp (congrArg Prod.snd h)).resolve_left hc
    exact q.1.2 (Prod.ext h1 h2)⟩

/-- The circle inside `ℝ² ∖ {0}`: the points `x` with `x ∈ S¹`. (Lean: `x.1` is `x` as a point
of the plane.) -/
def circ : Set Plane0 := {x | x.1 ∈ S1}

/-- **Bridge.** The course topology of `(ℝ² ∖ {0}) × I` is Mathlib's, from the bridges
`prod_toMathlib`, `subspace_toMathlib`, `real_toMathlib`, `I_toMathlib`. -/
theorem prod_I_toMathlib :
    (prod : TopSpace (Plane0 × I)).toMathlib = (inferInstance : TopologicalSpace (Plane0 × I)) := by
  rw [prod_toMathlib, subspace_toMathlib, prod_toMathlib, real_toMathlib, I_toMathlib]

/-- **`cor:circle-consequences`**, `ex-3n-he`: `S¹` is a deformation retract of `ℝ² ∖ {0}`, by
`H(x, t) = (1 - t) x + t x/|x|`: `H(x, 0) = x`, `H(x, 1) = x/|x| ∈ S¹`, and `H(a, t) = a` for
`|a| = 1`. The continuity of `H` is Analysis I (arithmetic, `√`, division by `|x| ≠ 0`),
through the bridge `prod_I_toMathlib`; `(√a)² = a` is `Real.sq_sqrt`. Mathlib: none (no
deformation retracts in v4.34.1). -/
theorem isDeformationRetract_circ : IsDeformationRetract circ := by
  -- Take `H = deform`; four things to check (`def:deformation-retract`).
  refine ⟨deform, ?_, fun x => ?_, fun x => ?_, fun a ha t => ?_⟩
  -- `H` is continuous: `|x|` is continuous, and so is `c(x, t) = (1 - t) + t/|x|`, as
  -- `|x| ≠ 0`; then `c x` is (Analysis I, through the bridges).
  · refine continuous_of_mathlib_eq prod_I_toMathlib (subspace_toMathlib _) ?_
    rw [prod_toMathlib, real_toMathlib]
    have hn : _root_.Continuous (fun q : Plane0 × I => √(q.1.1.1 ^ 2 + q.1.1.2 ^ 2)) := by
      fun_prop
    have hs : _root_.Continuous (fun q : Plane0 × I => scale q.1 q.2) :=
      (_root_.continuous_const.sub (by fun_prop)).add
        ((by fun_prop : _root_.Continuous (fun q : Plane0 × I => (q.2 : ℝ))).div hn
          fun q => (norm_pos q.1).ne')
    exact Continuous.subtype_mk ((hs.mul (by fun_prop)).prodMk (hs.mul (by fun_prop))) _
  -- `H(x, 0) = (1 - 0 + 0) x = x`.
  · apply Subtype.ext
    simp [deform, scale]
  -- `H(x, 1) = x/|x|` is on `S¹`: `(x₁/|x|)² + (x₂/|x|)² = (x₁² + x₂²)/|x|² = 1`, since
  -- `|x|² = x₁² + x₂²`.
  · show (scale x 1 * x.1.1) ^ 2 + (scale x 1 * x.1.2) ^ 2 = 1
    have hn := norm_pos x
    have hsq := Real.sq_sqrt (sq_pos x).le
    simp only [scale, Set.Icc.coe_one, sub_self, zero_add]
    field_simp
    linarith
  -- For `a ∈ S¹`, `|a| = 1`, so `c(a, t) = 1 - t + t = 1` and `H(a, t) = a`.
  · have ha' : a.1.1 ^ 2 + a.1.2 ^ 2 = 1 := ha
    apply Subtype.ext
    simp [deform, scale, ha']

/-- The inclusion `S¹ → ℝ² ∖ {0}`, `z ↦ z`, with the proof `S1.ne_zero` that `z ≠ 0`. -/
def incl (z : S1) : Plane0 := ⟨z.1, S1.ne_zero z⟩

/-- `S¹` is homeomorphic to the circle inside `ℝ² ∖ {0}`: both are the same subset of `ℝ²` with
the subspace topology, and the maps both ways are continuous by `prop-1-15` (a map into a
subspace is continuous if it is into the whole space). Lean: `Homeomorph S1 circ` is a
homeomorphism, given by the map `toFun`, its inverse `invFun`, the proofs that they are
inverse (`left_inv`, `right_inv`), and their continuity. -/
def circHomeo : Homeomorph S1 circ where
  toFun z := ⟨incl z, z.2⟩
  invFun a := ⟨a.1.1, a.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun :=
    continuous_subtype_mk' (g := incl) (continuous_subtype_mk' continuous_subtype_val _) _
  continuous_invFun :=
    continuous_subtype_mk' (g := fun a : circ => a.1.1)
      (continuous_subtype_val.comp continuous_subtype_val) _

/-- `cor:circle-consequences`: the inclusion `S¹ → ℝ² ∖ {0}` is a homotopy equivalence, as the
composite of a homeomorphism onto `circ` and the inclusion of a deformation retract
(`def:deformation-retract`). Mathlib: none. -/
theorem isHomotopyEquiv_incl : IsHomotopyEquiv incl :=
  circHomeo.isHomotopyEquiv.comp isDeformationRetract_circ.isHomotopyEquiv

/-- `cor:circle-consequences`: `S¹` and `ℝ² ∖ {0}` are homotopy equivalent, by the inclusion.
Mathlib: none. -/
theorem homotopyEquivalent_S1 : HomotopyEquivalent S1 Plane0 := ⟨incl, isHomotopyEquiv_incl⟩

end Plane0

/-- **`cor:circle-consequences`**: `π₁(ℝ² ∖ {0}, (1, 0)) ≅ ℤ`, by homotopy invariance
(`thm:pi1-homotopy-invariant`) for the inclusion `S¹ → ℝ² ∖ {0}`, a homotopy equivalence since
`S¹` is a deformation retract. Mathlib: none. -/
def pi1Plane0 : pi1 Plane0.one ≃* Multiplicative ℤ := pi1EquivCircle Plane0.isHomotopyEquiv_incl

/-! ## The circle among the one-dimensional spaces (`thm:one-dimensional`, `rem:non-cut-count`)

The book separates `S¹` from `ℝ` and `[0, 1)` by compactness and from `[0, 1]` by a cut point;
here, as in `rem:non-cut-count`, all three by cut points: no point of `S¹` is a cut point,
while `ℝ`, `[0, 1]` and `[0, 1)` each have one. A cut point of a connected `X` is a point `x`
with `X ∖ {x}` not connected (`def:cut-point`, `IsCutPoint`); a homeomorphism carries cut points
to cut points. (Lean: `{z}ᶜ` is the complement `S¹ ∖ {z}`, as a space.) -/

/-- `thm:one-dimensional`: `S¹ ∖ {z}` is connected for every `z ∈ S¹`. With `z = p(a)`, it is
the continuous image under `p` of the open interval `(a, a + 1)`, which is connected (week 2's
`connected_of_ordConnected`, Analysis I): `p(t) ≠ p(a)` for `a < t < a + 1`, as `t - a ∉ ℤ`;
and each `w = p(b) ≠ z` is `p(b - ⌊b - a⌋)`, with `b - ⌊b - a⌋ ∈ [a, a + 1)` and `≠ a`.
Mathlib: none for `S¹` (the book's "homeomorphic to an open interval"). -/
theorem connected_S1_compl (z : S1) : Connected ({z}ᶜ : Set S1) := by
  -- Write `z = p(a)`.
  obtain ⟨a, rfl⟩ := p_surjective z
  -- Step 1. `(a, a + 1)` is connected: with any two points it contains the segment between
  -- them (`connected_of_ordConnected`, week 2).
  have hJ : Connected (Ioo a (a + 1)) := connected_of_ordConnected fun x hx y hy t => by
    obtain ⟨h1, h2⟩ := segment_bounds x y t
    exact ⟨lt_of_lt_of_le (lt_min hx.1 hy.1) h1, lt_of_le_of_lt h2 (max_lt hx.2 hy.2)⟩
  -- Step 2. `p` maps `(a, a + 1)` into `S¹ ∖ {p(a)}`: if `p(t) = p(a)`, then `a - t = n ∈ ℤ`
  -- (`p_eq_iff`) with `-1 < n < 0`, and there is no such integer.
  have hne : ∀ t : Ioo a (a + 1), p t.1 ∈ ({p a}ᶜ : Set S1) := fun t ht => by
    obtain ⟨n, hn⟩ := p_eq_iff.mp (show p t.1 = p a from ht)
    have h1 : ((-1 : ℤ) : ℝ) < n := by rw [← hn]; push_cast; linarith [t.2.2]
    have h2 : (n : ℝ) < ((0 : ℤ) : ℝ) := by rw [← hn]; push_cast; linarith [t.2.1]
    have h1' := Int.cast_lt.mp h1
    have h2' := Int.cast_lt.mp h2
    omega
  -- Step 3. A continuous image of a connected space is connected (week 2,
  -- `Connected.of_surjective`), so it is enough that `p : (a, a + 1) → S¹ ∖ {p(a)}` is onto.
  refine hJ.of_surjective (φ := fun t => ⟨p t.1, hne t⟩)
    (continuous_into_subspace (continuous_p.comp continuous_subtype_val) _) ?_
  -- Step 4, onto: let `w = p(b) ≠ p(a)`. Then `b' = b - ⌊b - a⌋` has `a ≤ b' < a + 1`
  -- (Analysis I: `⌊x⌋ ≤ x < ⌊x⌋ + 1`), `p(b') = p(b) = w` (`p_add_int`), and `b' ≠ a` since
  -- `p(b') ≠ p(a)`; so `b' ∈ (a, a + 1)` and `p(b') = w`.
  rintro ⟨w, hw⟩
  obtain ⟨b, rfl⟩ := p_surjective w
  have hb0 : a ≤ b - ⌊b - a⌋ := by linarith [Int.floor_le (b - a)]
  have hb1 : b - ⌊b - a⌋ < a + 1 := by linarith [Int.lt_floor_add_one (b - a)]
  have hpb : p (b - ⌊b - a⌋) = p b := by
    have := p_add_int b (-⌊b - a⌋)
    rwa [Int.cast_neg, ← sub_eq_add_neg] at this
  have hba : b - ⌊b - a⌋ ≠ a := fun h => hw (by rw [← hpb, h]; rfl)
  exact ⟨⟨b - ⌊b - a⌋, lt_of_le_of_ne hb0 (Ne.symm hba), hb1⟩, Subtype.ext hpb⟩

/-- **`rem:non-cut-count`**: no point of `S¹` is a cut point, as `S¹ ∖ {z}` is connected
(`connected_S1_compl`). Mathlib: none. -/
theorem not_isCutPoint_S1 (z : S1) : ¬ IsCutPoint z := fun h => h.2 (connected_S1_compl z)

/-- `thm:one-dimensional`: `1/2` is a cut point of `[0, 1]`: `[0, 1]` is connected, and
`[0, 1] ∖ {1/2}` is not, being split into `[0, 1/2)` and `(1/2, 1]`. -/
theorem isCutPoint_I_half : IsCutPoint (⟨1 / 2, by norm_num, by norm_num⟩ : I) :=
  -- `I` is connected (week 2). For the complement, `not_connected_of_real` (week 2): a space
  -- with a continuous real function `e` that misses `c` but takes values below and above `c`
  -- is not connected. Here `e(w) = w`, `c = 1/2`, with `e(0) = 0 < 1/2 < 1 = e(1)`.
  ⟨connected_I, not_connected_of_real
    (e := fun w : ({⟨1 / 2, by norm_num, by norm_num⟩}ᶜ : Set I) => ((w : I) : ℝ))
    (continuous_subtype_val.comp continuous_subtype_val)
    (fun w h => w.2 (Subtype.ext h)) (c := 1 / 2)
    (a := ⟨I.zero, fun h => by simpa [I.zero] using congrArg Subtype.val h⟩)
    (b := ⟨I.one, fun h => by have := congrArg Subtype.val h; norm_num [I.one] at this⟩)
    (by simp [I.zero]) (by norm_num [I.one])⟩

/-- If `Y` has a cut point `y` (`hy`), then `S¹ ≇ Y`: a homeomorphism `h : S¹ → Y` would pull
it back to a cut point `h⁻¹(y)` of `S¹` (`Homeomorph.isCutPoint_iff`), and `S¹` has none. -/
theorem not_homeomorph_S1_of_isCutPoint [TopSpace Y] {y : Y} (hy : IsCutPoint y) :
    ¬ Nonempty (Homeomorph S1 Y) := by
  rintro ⟨h⟩
  have := (h.isCutPoint_iff (h.toEquiv.symm y)).mp (by rwa [h.toEquiv.apply_symm_apply])
  exact not_isCutPoint_S1 _ this

/-- **`thm:one-dimensional`**: `S¹ ≇ ℝ`: every point of `ℝ` is a cut point, none of `S¹` is
(`rem:non-cut-count`; the book uses compactness). Mathlib: none. -/
theorem S1_not_homeomorph_real : ¬ Nonempty (Homeomorph S1 ℝ) :=
  not_homeomorph_S1_of_isCutPoint (isCutPoint_real 0)

/-- **`thm:one-dimensional`**: `S¹ ≇ [0, 1]`: `1/2` is a cut point of `[0, 1]`, and no point of
`S¹` is (the book's proof). Mathlib: none. -/
theorem S1_not_homeomorph_I : ¬ Nonempty (Homeomorph S1 I) :=
  not_homeomorph_S1_of_isCutPoint isCutPoint_I_half

/-- **`thm:one-dimensional`**: `S¹ ≇ [0, 1)`: `1/2` is a cut point of `[0, 1)` (as every point
other than `0` is, `isCutPoint_Ico01`), and no point of `S¹` is (`rem:non-cut-count`; the book
uses compactness). Mathlib: none. -/
theorem S1_not_homeomorph_Ico01 : ¬ Nonempty (Homeomorph S1 Ico01) :=
  not_homeomorph_S1_of_isCutPoint (isCutPoint_Ico01 ⟨1 / 2, by norm_num, by norm_num⟩
    fun h => by simpa [Ico01.zero] using congrArg Subtype.val h)

/-! ## The disc is not the circle -/

/-- `cor:circle-consequences` ("and so does the disc"): `S¹` and `D²` are not even homotopy
equivalent: `π₁(D²)` is trivial (`pi1_D2_eq_one`, the disc being convex) and `π₁(S¹) ≅ ℤ` is
not. Mathlib: none. -/
theorem S1_not_homotopyEquivalent_D2 : ¬ HomotopyEquivalent S1 D2 :=
  S1_not_homotopyEquivalent_of_pi1_trivial fun _ a => pi1_D2_eq_one a

/-- `cor:circle-consequences`: `S¹ ≇ D²`, since homeomorphic spaces are homotopy equivalent
(`def:homotopy-equivalence`) and these are not. Mathlib: none. -/
theorem S1_not_homeomorph_D2 : ¬ Nonempty (Homeomorph S1 D2) := fun ⟨h⟩ =>
  S1_not_homotopyEquivalent_D2 h.homotopyEquivalent

end

end Course
