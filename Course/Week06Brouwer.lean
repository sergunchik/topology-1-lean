/-
Machine-generated (Claude, Aristotle), no line written by a person. Copyleft: GPL-3.0-or-later.

# Week 6: induced homomorphisms, retracts, no retraction `D² → S¹`, Brouwer in the plane

This file proves Brouwer's fixed point theorem in the plane (`cor:brouwer-2`): every continuous
`h : D² → D²` has a fixed point. The road is the book's (week 6). A continuous
pointed map `φ : (X, x) → (Y, y)` induces a homomorphism `φ_* [f] = [φ ∘ f]`, and
`(ψ ∘ φ)_* = ψ_* ∘ φ_*`, `(id)_* = id` (`prop:induced`); so a retraction `r : X → A` has
`r_* ∘ i_* = id`, and `i_*` is injective, `r_*` surjective (`prop:retract-pi1`). For `S¹ ⊆ D²`
this would make the identity of `π₁(S¹, 1) ≅ ℤ` factor through `π₁(D², 1) = 1`, so there is no
retraction `D² → S¹` (`thm:no-retraction-2`); and a map `h` with no fixed point would give one,
by sending `x` to the point where the ray from `h(x)` through `x` leaves the disc
(`cor:brouwer-from-retraction` for `n = 2`).

Departures from the book:
* The disc `D²` is `{(x, y) | x² + y² ≤ 1}` in the course's plane `ℝ × ℝ`, and `|v|`, `⟨v, w⟩`
  are written out in coordinates.
* `π₁(D²) = 1` (the case of `cor:contractible-sc` the book uses) is proved directly by the
  straight-line homotopy, since the disc is convex. Homotopy invariance and
  `lem:homotopy-basepoint` are in `Week06Invariance.lean`; the functor `Π₁(φ)` on fundamental
  groupoids is not formalised.
* In `thm:no-retraction-2` the contradiction is made concrete: the loop `s ↦ e^{2πis}` has
  degree `1`, yet its class would be `1`, of degree `0`.
* From Analysis I, through the bridges: the continuity of real arithmetic, of `√` and of division
  by a function that does not vanish, and `(√a)² = a` for `a ≥ 0`; each use says so. Mathlib's
  fundamental group, retractions, covering spaces and Brouwer theorem are not used. Mathlib's
  names below were checked against Lean and Mathlib v4.34.1.

New to Lean? Read `Course/README.md` first.
-/
import Course.Week06

-- Bookkeeping. `X`, `Y`, `Z` below are spaces (types; `u v w` are their "universe levels", which
-- you may ignore). `open Set Real` lets us write `√` and `Icc` without prefixes, and
-- `noncomputable section` says that some definitions use real numbers, which Lean cannot compute.
universe u v w

set_option warn.classDefReducibility false

namespace Course

open Set Real

noncomputable section

variable {X : Type u} {Y : Type v} {Z : Type w}

/-! ## Induced homomorphisms (`prop:induced`) -/

section Induced
variable [TopSpace X] [TopSpace Y] [TopSpace Z]

/-- If `f` is a path from `x` to `x'` in `X` and `φ : X → Y` is continuous, then `φ ∘ f` is a
path in `Y` from `φ(x)` to `φ(x')`. `prop:induced`. Mathlib: `Path.map`.

The hypotheses `hx : φ x = y` and `hx' : φ x' = y'` say that `φ` sends the ends `x`, `x'` of `f`
to `y`, `y'`; carrying them lets us call the ends of `φ ∘ f` by the names we want (for instance
`1 ∈ S¹` rather than `r(1)` for a retraction `r`).

Lean: `def … where` builds an object field by field. A `Path y y'` (week 4) is a map `toFun`
from `I` to `Y`, a proof `continuous_toFun` that it is continuous, and proofs `source'`,
`target'` that it starts at `y` and ends at `y'`. -/
def Path.map {x x' : X} (f : Path x x') {φ : X → Y} (hφ : Continuous φ) {y y' : Y}
    (hx : φ x = y) (hx' : φ x' = y') : Path y y' where
  -- The map `s ↦ φ(f(s))`, continuous as a composite of continuous maps (`prop-1n-composite`).
  toFun s := φ (f s)
  continuous_toFun := hφ.comp f.continuous
  -- It starts at `φ(f(0)) = φ(x) = y` and ends at `φ(f(1)) = φ(x') = y'`.
  source' := by
    show φ (f 0) = y
    rw [f.source, hx]
  target' := by
    show φ (f 1) = y'
    rw [f.target, hx']

/-- Unfolding: `(φ ∘ f)(s) = φ(f(s))`. (`rfl`: true by definition.) -/
theorem Path.map_apply {x x' : X} (f : Path x x') {φ : X → Y} (hφ : Continuous φ) {y y' : Y}
    (hx : φ x = y) (hx' : φ x' = y') (s : I) : f.map hφ hx hx' s = φ (f s) := rfl

/-- If `H` is a path homotopy from `f` to `g` and `φ` is continuous, then `φ ∘ H`,
`(s, t) ↦ φ(H(s, t))`, is a path homotopy from `φ ∘ f` to `φ ∘ g`. `prop:induced` (its proof's
first claim). Mathlib: `Path.Homotopy.map`. -/
def PathHomotopy.map {x x' : X} {f g : Path x x'} (F : PathHomotopy f g) {φ : X → Y}
    (hφ : Continuous φ) {y y' : Y} (hx : φ x = y) (hx' : φ x' = y') :
    PathHomotopy (f.map hφ hx hx') (g.map hφ hx hx') where
  -- `φ ∘ F` is continuous as a composite (`prop-1n-composite`). Its four sides are `φ` of `F`'s:
  -- bottom `φ(F(s, 0)) = φ(f(s))`, top `φ(F(s, 1)) = φ(g(s))`,
  -- left `φ(F(0, t)) = φ(x) = y`, right `φ(F(1, t)) = φ(x') = y'`. (Lean: `;` separates two
  -- tactics on one line.)
  toFun q := φ (F.toFun q)
  continuous_toFun := hφ.comp F.continuous_toFun
  zero' s := by show φ (F.toFun (s, 0)) = φ (f s); rw [F.zero']
  one' s := by show φ (F.toFun (s, 1)) = φ (g s); rw [F.one']
  source' t := by show φ (F.toFun (0, t)) = y; rw [F.source', hx]
  target' t := by show φ (F.toFun (1, t)) = y'; rw [F.target', hx']

/-- If `f ≃ₚ g` and `φ` is continuous, then `φ ∘ f ≃ₚ φ ∘ g`. `prop:induced`. Mathlib:
`Path.Homotopic.map`.

Proof: `f ≃ₚ g` means there is a path homotopy `F` from `f` to `g` (`Nonempty (PathHomotopy f g)`);
then `φ ∘ F` is one from `φ ∘ f` to `φ ∘ g` (`PathHomotopy.map`). Lean: `Nonempty.map u`
turns "there is an `F`" into "there is a `u F`". -/
theorem Path.Homotopic.map {x x' : X} {f g : Path x x'} (h : f.Homotopic g) {φ : X → Y}
    (hφ : Continuous φ) {y y' : Y} (hx : φ x = y) (hx' : φ x' = y') :
    (f.map hφ hx hx').Homotopic (g.map hφ hx hx') :=
  Nonempty.map (fun F : PathHomotopy f g => F.map hφ hx hx') h

/-- `φ` carries products to products: `φ ∘ (f · g) = (φ ∘ f) · (φ ∘ g)`. `prop:induced`.
Mathlib: `Path.map_trans`. -/
theorem Path.map_trans {x x' x'' : X} (f : Path x x') (g : Path x' x'') {φ : X → Y}
    (hφ : Continuous φ) {y y' y'' : Y} (hx : φ x = y) (hx' : φ x' = y') (hx'' : φ x'' = y'') :
    (f.trans g).map hφ hx hx'' = (f.map hφ hx hx').trans (g.map hφ hx' hx'') := by
  -- Two paths are equal if they agree at every time `s`.
  ext s
  -- Both sides are defined by cases (`def:concatenation`): at `s` they are `φ(f(2s))` if
  -- `s ≤ 1/2` and `φ(g(2s - 1))` otherwise. `split_ifs` splits into these two cases, and in each
  -- the two sides are the same expression.
  rw [Path.map_apply, Path.trans_apply, Path.trans_apply]
  split_ifs <;> rfl

/-- `φ` carries constant paths to constant paths: if `φ(x) = y`, then `φ ∘ c_x = c_y`.
`prop:induced`. Mathlib: `Path.map` of `Path.refl` (by `rfl`). -/
theorem Path.map_refl (x : X) {φ : X → Y} (hφ : Continuous φ) {y : Y} (hx : φ x = y) :
    (Path.refl x).map hφ hx hx = Path.refl y := by
  -- At every time `s`, the left side is `φ(x)` and the right side is `y`; they are equal by `hx`.
  ext s
  exact hx

/-- **`prop:induced`**: a pointed map `φ : (X, x) → (Y, y)` induces a homomorphism
`φ_* : π₁(X, x) → π₁(Y, y)`, `φ_* [f] = [φ ∘ f]`. Mathlib: `FundamentalGroup.map`.

Lean: `G →* H` is the type of group homomorphisms from `G` to `H`; one is given by its map
`toFun` and proofs `map_one'` (`φ_* 1 = 1`) and `map_mul'` (`φ_*(ab) = φ_*(a) φ_*(b)`). `⟦f⟧` is
the class `[f]` of `f` in the quotient. -/
def induced (φ : X → Y) (hφ : Continuous φ) {x : X} {y : Y} (hx : φ x = y) : pi1 x →* pi1 y where
  -- `[f] ↦ [φ ∘ f]` is well defined because `f ≃ₚ g` implies `φ ∘ f ≃ₚ φ ∘ g`
  -- (`Path.Homotopic.map`). Lean: `Quotient.map u w` is the map of classes `[f] ↦ [u f]`,
  -- given the proof `w` that `u` respects the relation.
  toFun := Quotient.map (fun f => f.map hφ hx hx) fun _ _ h => Path.Homotopic.map h hφ hx hx
  -- `φ_* 1 = 1`: `φ_*[c_x] = [φ ∘ c_x] = [c_y]` (`Path.map_refl`).
  map_one' := by
    show (⟦(Path.refl x).map hφ hx hx⟧ : pi1 y) = ⟦Path.refl y⟧
    rw [Path.map_refl]
  -- `φ_*([f][g]) = φ_*[f] φ_*[g]`. Every element of `π₁(X, x)` is a class `[f]` of a loop
  -- (Lean: `induction a using Quotient.ind` says "write `a = [f]`"), so it is enough to check
  -- `[φ ∘ (f · g)] = [(φ ∘ f) · (φ ∘ g)]`, which holds already for the paths (`Path.map_trans`).
  map_mul' a b := by
    induction a using Quotient.ind with | _ f => ?_
    induction b using Quotient.ind with | _ g => ?_
    show (⟦(f.trans g).map hφ hx hx⟧ : pi1 y) = ⟦(f.map hφ hx hx).trans (g.map hφ hx hx)⟧
    rw [Path.map_trans]

/-- Unfolding: `φ_* [f] = [φ ∘ f]`. -/
theorem induced_mk (φ : X → Y) (hφ : Continuous φ) {x : X} {y : Y} (hx : φ x = y)
    (f : Path x x) : induced φ hφ hx ⟦f⟧ = ⟦f.map hφ hx hx⟧ := rfl

/-- `(ψ ∘ φ)_* = ψ_* ∘ φ_*`. `prop:induced`. Mathlib: `FundamentalGroupoid.map_comp`
(`FundamentalGroupoid.fundamentalGroupoidFunctor`). The base point of `(ψ ∘ φ)_*` is
`ψ(φ(x)) = ψ(y) = z`, from `hx : φ x = y` and `hy : ψ y = z`. -/
theorem induced_comp (φ : X → Y) (ψ : Y → Z) (hφ : Continuous φ) (hψ : Continuous ψ) {x : X}
    {y : Y} {z : Z} (hx : φ x = y) (hy : ψ y = z) :
    induced (ψ ∘ φ) (hψ.comp hφ) (by rw [Function.comp_apply, hx, hy]) =
      (induced ψ hψ hy).comp (induced φ hφ hx) := by
  -- Two homomorphisms are equal if they agree at every `a = [f]`; and at `[f]` both sides are,
  -- by definition, the class of the loop `s ↦ ψ(φ(f(s)))`.
  ext a
  induction a using Quotient.ind with | _ f => ?_
  rfl

/-- `(id)_* = id`. `prop:induced`. Mathlib: `FundamentalGroupoid.map_id`. -/
theorem induced_id (x : X) : induced (fun a : X => a) continuous_id (rfl : x = x) =
    MonoidHom.id (pi1 x) := by
  -- At every `a = [f]` both sides are `[f]`, by definition.
  ext a
  induction a using Quotient.ind with | _ f => ?_
  rfl

/-- If `φ(a) = ψ(a)` for every `a`, then `φ_* = ψ_*`: the induced homomorphism depends only on
the map. -/
theorem induced_congr {φ ψ : X → Y} (h : ∀ a, φ a = ψ a) (hφ : Continuous φ)
    (hψ : Continuous ψ) {x : X} {y : Y} (hx : φ x = y) (hx' : ψ x = y) :
    induced φ hφ hx = induced ψ hψ hx' := by
  -- `φ = ψ` as maps (`funext`: maps that agree everywhere are equal); Lean then replaces `ψ` by
  -- `φ` everywhere (`obtain rfl`), and the two sides become the same.
  obtain rfl : φ = ψ := funext h
  rfl

/-- If `r ∘ i = id`, then `r_* ∘ i_* = id`. This is the heart of `prop:retract-pi1`, for any
`i : A → X` and `r : X → A` (here `Y` plays `A`), with base points `i(a) = x` (`hx`) and
`r(x) = a` (`hxa`). -/
theorem induced_comp_eq_id {i : Y → X} {r : X → Y} (hi : Continuous i) (hr : Continuous r)
    (hri : ∀ a, r (i a) = a) (a : Y) {x : X} (hx : i a = x) (hxa : r x = a) :
    (induced r hr hxa).comp (induced i hi hx) = MonoidHom.id (pi1 a) := by
  -- The book's chain `r_* ∘ i_* = (r ∘ i)_* = (id)_* = id`, by `prop:induced`.
  calc (induced r hr hxa).comp (induced i hi hx)
      -- `r_* ∘ i_* = (r ∘ i)_*`: functoriality (`induced_comp`).
      = induced (r ∘ i) (hr.comp hi) (by rw [Function.comp_apply, hx, hxa]) :=
        (induced_comp i r hi hr hx hxa).symm
    -- `(r ∘ i)_* = (id)_*`, because `r(i(a)) = a` for every `a` (`induced_congr`).
    _ = induced (fun b : Y => b) continuous_id rfl := induced_congr hri _ continuous_id _ rfl
    -- `(id)_* = id` (`induced_id`).
    _ = MonoidHom.id (pi1 a) := induced_id a

end Induced

/-! ## Retracts (`prop:retract-pi1`) -/

/-- **`prop:retract-pi1`**: if `r : X → A` is a retraction onto a subspace `A`, `r(a) = a` on
`A` (`hra`), then for every `a ∈ A`, `i_* : π₁(A, a) → π₁(X, a)` is injective and
`r_* : π₁(X, a) → π₁(A, a)` is surjective. Mathlib v4.34.1: no counterpart of the statement;
the homomorphisms are `FundamentalGroup.map`.

Lean: the inclusion `i : A → X` is `Subtype.val`, which forgets that a point lies in `A`;
`(a : X)` is `a` seen as a point of `X`. -/
theorem retract_pi1 [TopSpace X] {A : Set X} (r : X → A) (hr : Continuous r)
    (hra : ∀ a : A, r a = a) (a : A) :
    Function.Injective (induced Subtype.val continuous_subtype_val (rfl : (a : X) = a)) ∧
      Function.Surjective (induced r hr (hra a)) := by
  -- Step 1. `r_* ∘ i_* = id` (`induced_comp_eq_id`), so `r_*(i_*(b)) = b` for every `b`:
  -- `r_*` is a left inverse of `i_*`. (Lean: `DFunLike.congr_fun` evaluates an equality of
  -- homomorphisms at `b`.)
  have hs : Function.LeftInverse (induced r hr (hra a))
      (induced Subtype.val continuous_subtype_val (rfl : (a : X) = a)) := fun b =>
    DFunLike.congr_fun (induced_comp_eq_id continuous_subtype_val hr hra a rfl (hra a)) b
  -- Step 2. A map with a left inverse is injective: if `i_*[f] = i_*[g]`, then
  -- `[f] = r_* i_*[f] = r_* i_*[g] = [g]`. A map with a right inverse is surjective: every `b`
  -- is `r_*(i_* b)`.
  exact ⟨hs.injective, hs.surjective⟩

/-! ## The disc `D²` and its trivial fundamental group -/

/-- The disc `D² = {(x, y) | x² + y² ≤ 1}`, with the subspace topology of the plane `ℝ × ℝ`
(`def-1-14`, `thm:product-top`). Mathlib: `Metric.closedBall (0 : ℝ × ℝ) 1` (for the
Euclidean norm, `Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1`).

Lean: a point `x : D2` is a pair `⟨x.1, x.2⟩` of a point `x.1 : ℝ × ℝ` and a proof `x.2` that it
lies in `D²`; its coordinates are `x.1.1` and `x.1.2`. -/
def D2 : Set (ℝ × ℝ) := {q | q.1 ^ 2 + q.2 ^ 2 ≤ 1}

namespace D2

/-- A point `x` of `D²` has `x₁² + x₂² ≤ 1`. -/
theorem sq_add_sq_le (x : D2) : x.1.1 ^ 2 + x.1.2 ^ 2 ≤ 1 := x.2

/-- `S¹ ⊆ D²`: if `x² + y² = 1`, then `x² + y² ≤ 1`. -/
theorem S1_subset : S1 ⊆ D2 := fun _ h => le_of_eq h

/-- The inclusion `ι : S¹ → D²`, `z ↦ z`. -/
def incl (z : S1) : D2 := ⟨z.1, S1_subset z.2⟩

/-- Unfolding: `ι(z)` is the point `z` of the plane. -/
@[simp] theorem coe_incl (z : S1) : (incl z : ℝ × ℝ) = z := rfl

/-- `ι : S¹ → D²` is continuous (`prop-1-15`): it is the inclusion `S¹ → ℝ × ℝ`, continuous,
with values in `D²`. -/
theorem continuous_incl : Continuous incl :=
  continuous_subtype_mk' continuous_subtype_val _

/-- The disc is convex: `(1 - t) a + t b ∈ D²` for `a, b ∈ D²` and `t ∈ I`. Analysis I
(arithmetic): `|(1 - t) a + t b|² = (1 - t)|a|² + t|b|² - t(1 - t)|a - b|² ≤ 1`. -/
theorem lerp_mem (a b : D2) (t : I) :
    ((1 - (t : ℝ)) * a.1.1 + t * b.1.1, (1 - (t : ℝ)) * a.1.2 + t * b.1.2) ∈ D2 := by
  -- The facts we use: `|a|² ≤ 1`, `|b|² ≤ 1`, and `0 ≤ t ≤ 1` (`t : I` is a real number `(t : ℝ)`
  -- with the proof `t.2` that it lies in `[0, 1]`).
  have ha := sq_add_sq_le a
  have hb := sq_add_sq_le b
  have ht0 : 0 ≤ (t : ℝ) := t.2.1
  have ht1 : (t : ℝ) ≤ 1 := t.2.2
  show ((1 - (t : ℝ)) * a.1.1 + t * b.1.1) ^ 2 + ((1 - (t : ℝ)) * a.1.2 + t * b.1.2) ^ 2 ≤ 1
  -- By the identity above, `1 - |(1 - t) a + t b|²` is the sum of three numbers `≥ 0`:
  -- `(1 - t)(1 - |a|²)`, `t(1 - |b|²)` and `t(1 - t)|a - b|²`. We give `nlinarith` these three,
  -- and it finds the identity. (Lean: for an `↔`, `.mp` is the direction `→` and `.mpr` the
  -- direction `←`; `sub_nonneg.mpr` turns `a ≤ b` into `0 ≤ b - a`.)
  nlinarith [mul_nonneg (sub_nonneg.mpr ht1) (sub_nonneg.mpr ha),
    mul_nonneg ht0 (sub_nonneg.mpr hb),
    mul_nonneg (mul_nonneg ht0 (sub_nonneg.mpr ht1))
      (add_nonneg (sq_nonneg (a.1.1 - b.1.1)) (sq_nonneg (a.1.2 - b.1.2)))]

/-- The point `(1 - t) a + t b` of the segment from `a` to `b` in `D²` (it is in `D²` by
`lerp_mem`). -/
def lerp (a b : D2) (t : I) : D2 := ⟨_, lerp_mem a b t⟩

end D2

/-- **Bridge.** The course topology of `D²`, as a subspace of the plane, is Mathlib's subspace
topology of `ℝ × ℝ`, from the bridges `subspace_toMathlib`, `prod_toMathlib`,
`real_toMathlib`. -/
theorem D2_toMathlib : (subspace D2).toMathlib = (inferInstance : TopologicalSpace D2) := by
  rw [subspace_toMathlib, prod_toMathlib, real_toMathlib]

/-- Every loop `f` at `x₀ ∈ D²` is path homotopic to the constant loop, by the straight-line
homotopy `H(s, t) = (1 - t) f(s) + t x₀`. `cor:contractible-sc` for `D²`. Mathlib:
`Convex.contractibleSpace`, `ContractibleSpace`, `SimplyConnectedSpace`. -/
def D2.contraction {x₀ : D2} (f : Path x₀ x₀) : PathHomotopy f (Path.refl x₀) where
  -- `H(s, t) = (1 - t) f(s) + t x₀`, which lies in `D²` because `D²` is convex (`D2.lerp_mem`).
  toFun q := D2.lerp (f q.1) x₀ q.2
  -- `H` is continuous: a formula in `t` and in the coordinates of `f(s)`, which are continuous
  -- (Analysis I, arithmetic). Lean: `mathlib_continuous_of_eq` turns the course's continuity of
  -- `f` into Mathlib's, `fun_prop` checks the formula, `Continuous.subtype_mk` says that a map
  -- into the plane with values in `D²` is continuous into `D²`, and `continuous_of_mathlib_eq`
  -- turns Mathlib's continuity back into the course's. The bridges `II_toMathlib`, `I_toMathlib`
  -- and `D2_toMathlib` say that the two topologies agree.
  continuous_toFun := by
    have hf := mathlib_continuous_of_eq I_toMathlib D2_toMathlib f.continuous
    exact continuous_of_mathlib_eq II_toMathlib D2_toMathlib
      (Continuous.subtype_mk (by fun_prop) _)
  -- The four sides, checked coordinate by coordinate. Lean: two points of `D²` are equal when
  -- they are equal in the plane (`Subtype.ext`), that is, when both coordinates agree
  -- (`Prod.ext`). Bottom: `H(s, 0) = f(s)`. Top: `H(s, 1) = x₀`.
  zero' s := Subtype.ext (Prod.ext (by simp [D2.lerp]) (by simp [D2.lerp]))
  one' s := Subtype.ext (Prod.ext (by simp [D2.lerp]) (by simp [D2.lerp]))
  -- Left and right: `f(0) = f(1) = x₀`, so `H(0, t) = H(1, t) = (1 - t) x₀ + t x₀ = x₀`.
  source' t := Subtype.ext (Prod.ext (by simp [D2.lerp]; ring) (by simp [D2.lerp]; ring))
  target' t := Subtype.ext (Prod.ext (by simp [D2.lerp]; ring) (by simp [D2.lerp]; ring))

/-- `π₁(D², x₀) = 1`: every element `a` is the identity. `cor:contractible-sc` for `D²`.
Mathlib: `SimplyConnectedSpace`. -/
theorem pi1_D2_eq_one {x₀ : D2} (a : pi1 x₀) : a = 1 := by
  -- Write `a = [f]`. The loop `f` is path homotopic to the constant loop (`D2.contraction`), so
  -- `[f] = [c_{x₀}] = 1`. Lean: `Quotient.sound` says that related elements have equal classes,
  -- and `⟨D2.contraction f⟩` proves "there is a path homotopy" by giving one.
  induction a using Quotient.ind with | _ f => ?_
  exact Quotient.sound ⟨D2.contraction f⟩

/-! ## No retraction of `D²` onto `S¹` (`thm:no-retraction-2`) -/

/-- **`thm:no-retraction-2`**: there is no retraction `D² → S¹`, that is, no continuous
`r : D² → S¹` with `r(ι z) = z` for `z ∈ S¹` (`hri`). Mathlib: none in v4.34.1 (the nearest is
`FundamentalGroup.map`).

Lean: a theorem whose conclusion is `False` says that its hypotheses cannot all hold. -/
theorem no_retraction_D2 (r : D2 → S1) (hr : Continuous r) (hri : ∀ z : S1, r (D2.incl z) = z) :
    False := by
  -- Step 1. Take `1 ∈ S¹` as base point; `r` fixes it (`hri 1`). Since `r ∘ ι = id`,
  -- `r_* ∘ ι_* = id` on `π₁(S¹, 1)` (`prop:induced`, as in `prop:retract-pi1`):
  -- `r_*(ι_*(b)) = b` for every `b`.
  have hs : ∀ b : pi1 (1 : S1),
      induced r hr (hri 1) (induced D2.incl D2.continuous_incl rfl b) = b := fun b =>
    DFunLike.congr_fun (induced_comp_eq_id D2.continuous_incl hr hri 1 rfl (hri 1)) b
  -- Step 2. Apply this to the class of the loop `f(s) = e^{2πis}` (`windLoop 1`):
  -- `r_*(ι_*[f]) = [f]`.
  have h1 := hs ⟦windLoop 1⟧
  -- Step 3. But `ι_*[f]` lies in `π₁(D², 1) = 1` (`cor:contractible-sc`, `pi1_D2_eq_one`), so
  -- `ι_*[f] = 1`, and `r_*(1) = 1` since `r_*` is a homomorphism (`map_one`). So `1 = [f]`.
  -- (Lean: `rw [...] at h1` rewrites inside the hypothesis `h1` instead of the goal.)
  rw [pi1_D2_eq_one (induced D2.incl D2.continuous_incl rfl ⟦windLoop 1⟧), map_one] at h1
  -- Step 4. Apply the degree, the isomorphism `π₁(S¹, 1) ≅ ℤ` (`thm:pi1-circle`, `pi1Circle`):
  -- the degree of `1` is `0`, and that of `[f]` is `1` (`pi1Circle_windLoop_one`). Lean writes
  -- `ℤ` multiplicatively (`Multiplicative ℤ`, the integer `n` written `ofAdd n`), so that it is a
  -- group under `*` like `π₁`; there `0` is written `1`, and `ofAdd_eq_one` says that
  -- `ofAdd n = 1` exactly when `n = 0`. So `1 = 0` in `ℤ`, which is false. (Lean: `congrArg F h`
  -- applies `F` to both sides of the equation `h`.)
  have h2 := congrArg pi1Circle h1
  rw [map_one, pi1Circle_windLoop_one] at h2
  exact one_ne_zero (ofAdd_eq_one.mp h2.symm)

/-! ## Brouwer in the plane (`cor:brouwer-from-retraction` for `n = 2`, `cor:brouwer-2`)

The ray construction, in the coordinates of `ℝ × ℝ`. For `x ≠ y` in the plane (in the theorem,
`y = h(x)`), `u = (x - y)/|x - y|` is the unit vector from `y` to `x`, and the ray from `y`
through `x` leaves the disc at `x + t u`, where `t = -⟨x, u⟩ + √(⟨x, u⟩² + 1 - |x|²)` is the
larger root of `|x + t u|² = 1`.

The continuity of these formulas is Analysis I, so it is stated with Mathlib's continuity,
written `_root_.Continuous`, for Mathlib's topologies; plain `Continuous` in this file is the
course's (week 1, Analysis I 4.18). The two agree through the bridges, as in `D2.contraction`. -/

namespace Brouwer

/-- The unit vector `u = (x - y)/|x - y|`, with `|x - y| = √((x₁ - y₁)² + (x₂ - y₂)²)`.
`cor:brouwer-from-retraction`. -/
def dir (x y : ℝ × ℝ) : ℝ × ℝ :=
  ((x.1 - y.1) / √((x.1 - y.1) ^ 2 + (x.2 - y.2) ^ 2),
    (x.2 - y.2) / √((x.1 - y.1) ^ 2 + (x.2 - y.2) ^ 2))

/-- The time `t = -⟨x, u⟩ + √(⟨x, u⟩² + 1 - |x|²)` at which the ray `x + t u` meets the circle.
`cor:brouwer-from-retraction`. -/
def exitTime (x u : ℝ × ℝ) : ℝ :=
  -(x.1 * u.1 + x.2 * u.2) + √((x.1 * u.1 + x.2 * u.2) ^ 2 + 1 - (x.1 ^ 2 + x.2 ^ 2))

/-- The point `x + t u` where the ray leaves the disc. `cor:brouwer-from-retraction`. -/
def exitPoint (x u : ℝ × ℝ) : ℝ × ℝ :=
  (x.1 + exitTime x u * u.1, x.2 + exitTime x u * u.2)

/-- `r(x) = x + t(x) u(x)`, the point where the ray from `y` through `x` leaves the disc.
`cor:brouwer-from-retraction`. -/
def ray (x y : ℝ × ℝ) : ℝ × ℝ := exitPoint x (dir x y)

/-- If `x ≠ y`, then `|x - y|² > 0` (Analysis I). -/
theorem dist_sq_pos {x y : ℝ × ℝ} (h : x ≠ y) : 0 < (x.1 - y.1) ^ 2 + (x.2 - y.2) ^ 2 := by
  -- Suppose not: `(x₁ - y₁)² + (x₂ - y₂)² ≤ 0`. (Lean: `by_contra` assumes the negation, and
  -- `push Not` turns `¬ (0 < s)` into `s ≤ 0`.)
  by_contra hle
  push Not at hle
  -- Both squares are `≥ 0`, so both are `0`.
  have h1 : (x.1 - y.1) ^ 2 = 0 := by linarith [sq_nonneg (x.1 - y.1), sq_nonneg (x.2 - y.2)]
  have h2 : (x.2 - y.2) ^ 2 = 0 := by linarith [sq_nonneg (x.1 - y.1), sq_nonneg (x.2 - y.2)]
  -- So `x₁ - y₁ = 0` and `x₂ - y₂ = 0` (`a² = 0` implies `a = 0`), that is `x = y`, against `h`.
  exact h (Prod.ext (sub_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h1))
    (sub_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h2)))

/-- If `x ≠ y`, then `u` is a unit vector: `|u|² = 1`. -/
theorem dir_sq {x y : ℝ × ℝ} (h : x ≠ y) : (dir x y).1 ^ 2 + (dir x y).2 ^ 2 = 1 := by
  -- `|u|² = (x₁ - y₁)²/N² + (x₂ - y₂)²/N²` with `N = |x - y| > 0` (`dist_sq_pos`), and
  -- `N² = (x₁ - y₁)² + (x₂ - y₂)²` because `(√a)² = a` for `a ≥ 0` (Analysis I, Mathlib's
  -- `Real.sq_sqrt`). So `|u|² = N²/N² = 1`; `field_simp` clears the denominators.
  have hpos := dist_sq_pos h
  have hs := Real.sq_sqrt hpos.le
  have hne : √((x.1 - y.1) ^ 2 + (x.2 - y.2) ^ 2) ≠ 0 := (Real.sqrt_pos.mpr hpos).ne'
  simp only [dir, div_pow, hs]
  field_simp

/-- If `|x| ≤ 1` and `|u| = 1`, then `x + t u` lies on the circle. `cor:brouwer-from-retraction`.
-/
theorem exitPoint_mem {x u : ℝ × ℝ} (hx : x.1 ^ 2 + x.2 ^ 2 ≤ 1)
    (hu : u.1 ^ 2 + u.2 ^ 2 = 1) : exitPoint x u ∈ S1 := by
  -- Write `b = ⟨x, u⟩` and `d = b² + 1 - |x|²`.
  -- Step 1. The root is real: `d ≥ 0`, because `|x|² ≤ 1`.
  have hd : 0 ≤ (x.1 * u.1 + x.2 * u.2) ^ 2 + 1 - (x.1 ^ 2 + x.2 ^ 2) := by
    nlinarith [sq_nonneg (x.1 * u.1 + x.2 * u.2)]
  -- Step 2. So `s = √d` has `s² = d` (Analysis I, Mathlib's `Real.sq_sqrt`).
  have hs := Real.sq_sqrt hd
  -- Step 3. With `t = s - b` and `|u|² = 1`,
  -- `|x + t u|² = |x|² + 2tb + t² = |x|² + s² - b² = |x|² + d - b² = 1`.
  -- Lean: `linear_combination t² · hu + hs` checks that the goal follows from `hu` and `hs`
  -- by the algebra of polynomials.
  show (x.1 + exitTime x u * u.1) ^ 2 + (x.2 + exitTime x u * u.2) ^ 2 = 1
  simp only [exitTime]
  linear_combination (-(x.1 * u.1 + x.2 * u.2) +
    √((x.1 * u.1 + x.2 * u.2) ^ 2 + 1 - (x.1 ^ 2 + x.2 ^ 2))) ^ 2 * hu + hs

/-- If `|x| ≤ 1` and `x ≠ y`, then `r(x) ∈ S¹`: `u` is a unit vector (`dir_sq`), so
`exitPoint_mem` applies. `cor:brouwer-from-retraction`. -/
theorem ray_mem {x y : ℝ × ℝ} (hx : x.1 ^ 2 + x.2 ^ 2 ≤ 1) (h : x ≠ y) : ray x y ∈ S1 :=
  exitPoint_mem hx (dir_sq h)

/-- If `|x| = 1` and `|y| ≤ 1`, then `r(x) = x`: a point of the circle is already where its ray
leaves the disc. `cor:brouwer-from-retraction`. -/
theorem ray_of_mem_S1 {x y : ℝ × ℝ} (hx : x ∈ S1) (hy : y.1 ^ 2 + y.2 ^ 2 ≤ 1) :
    ray x y = x := by
  have hx' : x.1 ^ 2 + x.2 ^ 2 = 1 := hx
  -- `N = |x - y|`. (Lean: `set` names an expression; `hN` records what it stands for.)
  set N := √((x.1 - y.1) ^ 2 + (x.2 - y.2) ^ 2) with hN
  -- Step 1. `⟨x, u⟩ ≥ 0`. Indeed `⟨x, u⟩ = ⟨x, x - y⟩/N = (1 - ⟨x, y⟩)/N`, and
  -- `⟨x, y⟩ ≤ (|x|² + |y|²)/2 ≤ 1` because `|x - y|² ≥ 0`.
  have hb : 0 ≤ x.1 * (dir x y).1 + x.2 * (dir x y).2 := by
    have e : x.1 * (dir x y).1 + x.2 * (dir x y).2 =
        (x.1 * (x.1 - y.1) + x.2 * (x.2 - y.2)) / N := by
      simp only [dir, ← hN]; ring
    rw [e]
    exact div_nonneg (by nlinarith [sq_nonneg (x.1 - y.1), sq_nonneg (x.2 - y.2)])
      (Real.sqrt_nonneg _)
  -- Step 2. Since `|x|² = 1`, `t = -⟨x, u⟩ + √(⟨x, u⟩²) = -⟨x, u⟩ + ⟨x, u⟩ = 0`, because
  -- `√(b²) = b` for `b ≥ 0` (Analysis I, Mathlib's `Real.sqrt_sq`).
  have ht : exitTime x (dir x y) = 0 := by
    simp only [exitTime, hx', add_sub_cancel_right, Real.sqrt_sq hb, neg_add_cancel]
  -- Step 3. So `r(x) = x + 0 · u = x`.
  simp only [ray, exitPoint, ht, zero_mul, add_zero]

/-- The map `(x, u) ↦ x + t u` is continuous on `ℝ² × ℝ²`. `cor:brouwer-from-retraction`.
Analysis I: it is built from the coordinates by arithmetic and `√` (Mathlib's
`Real.continuous_sqrt`), and `fun_prop` checks this. -/
theorem continuous_exitPoint :
    _root_.Continuous (fun q : (ℝ × ℝ) × (ℝ × ℝ) => exitPoint q.1 q.2) := by
  unfold exitPoint exitTime
  fun_prop

/-- If `f, g : W → ℝ²` are continuous and `f(w) ≠ g(w)` for every `w` (`hne`), then
`w ↦ r(f(w))`, for the ray from `g(w)` through `f(w)`, is continuous: `r` is continuous where
`x - y` never vanishes. `cor:brouwer-from-retraction`. Analysis I: arithmetic, `√`, and division
by a function that does not vanish (Mathlib's `Continuous.div`). Here `W` is any space with a
Mathlib topology (`[TopologicalSpace W]`); it will be `D²`. -/
theorem continuous_ray {W : Type*} [TopologicalSpace W] {f g : W → ℝ × ℝ}
    (hf : _root_.Continuous f) (hg : _root_.Continuous g) (hne : ∀ w, f w ≠ g w) :
    _root_.Continuous (fun w => ray (f w) (g w)) := by
  -- Step 1. `N(w) = |f(w) - g(w)|` is continuous (arithmetic and `√`) …
  have hN : _root_.Continuous
      (fun w => √(((f w).1 - (g w).1) ^ 2 + ((f w).2 - (g w).2) ^ 2)) := by fun_prop
  -- … and never `0`, because `f(w) ≠ g(w)` (`dist_sq_pos`).
  have hN0 : ∀ w, √(((f w).1 - (g w).1) ^ 2 + ((f w).2 - (g w).2) ^ 2) ≠ 0 := fun w =>
    (Real.sqrt_pos.mpr (dist_sq_pos (hne w))).ne'
  -- Step 2. So `u(w) = (f(w) - g(w))/N(w)` is continuous, coordinate by coordinate: a quotient
  -- of continuous functions whose denominator does not vanish.
  have hdir : _root_.Continuous (fun w => dir (f w) (g w)) :=
    ((hf.fst.sub hg.fst).div hN hN0).prodMk ((hf.snd.sub hg.snd).div hN hN0)
  -- Step 3. `r = (x, u) ↦ x + t u` composed with `w ↦ (f(w), u(w))`: continuous
  -- (`continuous_exitPoint`).
  exact continuous_exitPoint.comp (hf.prodMk hdir)

end Brouwer

/-- **`cor:brouwer-2`** (Brouwer's fixed point theorem in the plane): every continuous
`h : D² → D²` has a fixed point, a point `x` with `h(x) = x`. The proof is the book's
(`cor:brouwer-from-retraction`). Mathlib v4.34.1 has no Brouwer theorem. -/
theorem brouwer_D2 (h : D2 → D2) (hh : Continuous h) : ∃ x, h x = x := by
  -- Step 1. Suppose not: `h(x) ≠ x` for every `x ∈ D²`. (Lean: `by_contra` assumes the
  -- negation; `push Not` turns `¬ ∃ x, h x = x` into `∀ x, h x ≠ x`.) Then also `x ≠ h(x)` as
  -- points of the plane (`Subtype.ext`: points of `D²` equal in the plane are equal).
  by_contra hno
  push Not at hno
  have hne : ∀ x : D2, (x : ℝ × ℝ) ≠ (h x : ℝ × ℝ) := fun x hx => hno x (Subtype.ext hx.symm)
  -- `h` is continuous for Mathlib's topologies too (the bridge `D2_toMathlib`).
  have hh' := mathlib_continuous_of_eq D2_toMathlib D2_toMathlib hh
  -- Step 2. Let `r(x)` be the point where the ray from `h(x)` through `x` leaves the disc.
  -- It lies on `S¹` because `|x| ≤ 1` and `x ≠ h(x)` (`Brouwer.ray_mem`), so `r : D² → S¹`.
  -- (Lean: `let` gives a name to a definition inside a proof; `⟨p, hp⟩` is the point `p` of
  -- `S¹` with the proof `hp` that it lies on `S¹`.)
  let r : D2 → S1 := fun x => ⟨Brouwer.ray x (h x), Brouwer.ray_mem (D2.sq_add_sq_le x) (hne x)⟩
  -- Step 3. `r` is continuous, because `x - h(x)` never vanishes (`Brouwer.continuous_ray`
  -- with `f` the inclusion of `D²` in the plane and `g = f ∘ h`), brought back to the course's
  -- continuity through the bridges `D2_toMathlib` and `S1_toMathlib`.
  have hr : Continuous r := continuous_of_mathlib_eq D2_toMathlib S1_toMathlib
    (Continuous.subtype_mk (Brouwer.continuous_ray _root_.continuous_subtype_val
      (_root_.continuous_subtype_val.comp hh') hne) _)
  -- Step 4. `r(z) = z` for `z ∈ S¹`, because `|z| = 1` and `|h(z)| ≤ 1`
  -- (`Brouwer.ray_of_mem_S1`). So `r` is a retraction of `D²` onto `S¹`, which
  -- `thm:no-retraction-2` (`no_retraction_D2`) forbids.
  exact no_retraction_D2 r hr fun z =>
    Subtype.ext (Brouwer.ray_of_mem_S1 z.2 (D2.sq_add_sq_le (h (D2.incl z))))

/-! ## Bridge: the induced homomorphism is Mathlib's `FundamentalGroup.map` -/

/-- **Bridge.** Under the isomorphisms `pi1MulEquiv : π₁(X, x) ≃* FundamentalGroup X x` (week 4),
`φ_*` is Mathlib's `FundamentalGroup.map` for the continuous map `φ` (with the Mathlib
topologies `toMathlib`; Lean: `let _ := tX.toMathlib` puts Mathlib's topology on `X` inside the
parentheses). Proof: on a class `[f]`, both sides are the class of `φ ∘ f`, by definition. -/
theorem induced_toMathlib [tX : TopSpace X] [tY : TopSpace Y] (φ : X → Y) (hφ : Continuous φ)
    (x : X) (a : pi1 x) :
    pi1MulEquiv (φ x) (induced φ hφ rfl a) =
      (let _ := tX.toMathlib; let _ := tY.toMathlib
       FundamentalGroup.map ⟨φ, mathlib_continuous_of_eq rfl rfl hφ⟩ x (pi1MulEquiv x a)) := by
  induction a using Quotient.ind with | _ f => ?_
  rfl

end

end Course
