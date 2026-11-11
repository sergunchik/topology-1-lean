/-
Machine-generated (Claude, Aristotle), no line written by a person. Copyleft: GPL-3.0-or-later.

# Week 6: change of base point, homotopy invariance, contractible spaces, products

This file proves that the fundamental group does not see the choice of base point nor homotopy.
A path `h` from `x` to `y` gives an isomorphism `β_h : π₁(X, x) → π₁(X, y)`, `[f] ↦ [h̄ · f · h]`
(`thm:change-basepoint`), so for a path-connected space "`π₁ = 1`" does not depend on the base
point (`def:simply-connected`). A homotopy `H : φ ≃ ψ` moves the base point along the track
`h_x(t) = H(x, t)`, and `ψ_* = β_{h_x} ∘ φ_*` (`lem:homotopy-basepoint`); hence a homotopy
equivalence induces isomorphisms of fundamental groups (`thm:pi1-homotopy-invariant`), and a
contractible space is simply connected (`cor:contractible-sc`). Last,
`π₁(X × Y) ≅ π₁(X) × π₁(Y)` (`prop:pi1-product`). The book: week 6, "Change of
base point" and "Induced homomorphisms and homotopy invariance", with `def:homotopy-equivalence`
and `def:contractible` from week 3.

Departures from the book:
* `thm:change-basepoint`: the formula `β_{h'}⁻¹ β_h [f] = [α]⁻¹[f][α]` is proved; its
  consequence "`β_h` is the same for every `h` exactly when `π₁(X, x)` is abelian" is not.
* `lem:homotopy-basepoint`: the natural isomorphism `Π₁(φ) ⇒ Π₁(ψ)` of fundamental groupoids is
  not formalised; the square `φf · h_{x'} ≃ₚ h_x · ψf` and `ψ_* = β_{h_x} ∘ φ_*` are.
* `thm:pi1-homotopy-invariant` is proved as "`φ_*` is bijective", then packaged as an
  isomorphism.
* `cor:contractible-sc`: the book uses `thm:pi1-homotopy-invariant` for `X → ∗`; here the same
  idea is applied directly to the contraction `id ≃ c` by `lem:homotopy-basepoint`.
* `prop:pi1-product` is proved for loops, not for all of `[Z, X × Y]_*`.
* The only Analysis I input is the continuity of the straight-line homotopy in the square
  `I × I` (`I.continuous_line`, week 4). Mathlib's fundamental group, homotopy equivalences and
  contractible spaces are not used. Mathlib's names below were checked against Lean and Mathlib
  v4.34.1.

New to Lean? Read `Course/README.md` first.
-/
import Course.Week06Brouwer

-- Bookkeeping. `X`, `Y`, `Z` below are spaces (types; `u v w` are their "universe levels", which
-- you may ignore), and `noncomputable section` says that some definitions use real numbers,
-- which Lean cannot compute.
universe u v w

set_option warn.classDefReducibility false

namespace Course

open Set

noncomputable section

variable {X : Type u} {Y : Type v} {Z : Type w}

/-! ## Change of base point (`thm:change-basepoint`)

First the algebra of path classes that the theorem needs, all from `thm:groupoid-laws`. Here
`comp a b` is the product `ab` of a class `a` from `x` to `y` and a class `b` from `y` to `z`,
`inv a` is `a⁻¹ = [f̄]`, and `refl x` is `[c_x]`. -/

namespace PathClass
variable [TopSpace X] {x y z : X}

/-- `[f̄̄] = [f]`: reversing twice gives back the path.

Lean: `induction a using Quotient.ind with | _ f => ?_` says "write `a = [f]`": to prove
something for every class it suffices to prove it for the class of every path `f`. -/
theorem inv_inv (a : PathClass x y) : inv (inv a) = a := by
  induction a using Quotient.ind with | _ f => ?_
  -- `[f]⁻¹⁻¹ = [f̄̄]`, and `f̄̄ = f` already as paths (`Path.symm_symm`).
  show (⟦f.symm.symm⟧ : PathClass x y) = ⟦f⟧
  rw [Path.symm_symm]

/-- `[f · g]⁻¹ = [ḡ][f̄]`: the reverse of `f · g` is `ḡ · f̄` (`Path.trans_symm_eq`). -/
theorem inv_comp_eq (a : PathClass x y) (b : PathClass y z) :
    inv (comp a b) = comp (inv b) (inv a) := by
  induction a using Quotient.ind with | _ f => ?_
  induction b using Quotient.ind with | _ g => ?_
  show (⟦(f.trans g).symm⟧ : PathClass z x) = ⟦g.symm.trans f.symm⟧
  rw [Path.trans_symm_eq]

/-- `[c_x]⁻¹ = [c_x]`: the constant path is its own reverse. -/
theorem inv_refl (x : X) : inv (refl x) = refl x := by
  -- `c̄_x = c_x` as paths; `congr 1` reduces `[c̄_x] = [c_x]` to that.
  show (⟦(Path.refl x).symm⟧ : PathClass x x) = ⟦Path.refl x⟧
  congr 1

/-- `[f]([f̄][g]) = [g]`, by `thm:groupoid-laws`: regroup to `([f][f̄])[g]`, and `[f][f̄] = [c_x]`
is the identity. -/
theorem comp_inv_comp (a : PathClass x y) (b : PathClass x z) : comp a (comp (inv a) b) = b := by
  rw [← comp_assoc, comp_inv, id_comp]

/-- `[f̄]([f][g]) = [g]`, by `thm:groupoid-laws`: regroup to `([f̄][f])[g]`, and `[f̄][f] = [c_y]`
is the identity. -/
theorem inv_comp_comp (a : PathClass x y) (b : PathClass y z) : comp (inv a) (comp a b) = b := by
  rw [← comp_assoc, inv_comp, id_comp]

/-- `thm:change-basepoint`, on classes: for a class `a = [h]` from `x` to `y` and a loop class
`c = [f]` at `x`, `β_{[h]}[f] = [h̄]([f][h])`, a loop class at `y`. -/
def conj (a : PathClass x y) (c : PathClass x x) : PathClass y y := comp (inv a) (comp c a)

/-- `thm:change-basepoint`: `β_h` is a homomorphism, `[h̄fh][h̄gh] = [h̄fgh]`: regroup, and the
middle `[h][h̄]` cancels (`thm:groupoid-laws`). -/
theorem conj_mul (a : PathClass x y) (c d : PathClass x x) :
    conj a (comp c d) = comp (conj a c) (conj a d) := by
  simp only [conj, comp_assoc, comp_inv_comp]

/-- `thm:change-basepoint`: `β_{h̄} β_h [f] = [h h̄ f h h̄] = [f]`. -/
theorem conj_inv_conj (a : PathClass x y) (c : PathClass x x) : conj (inv a) (conj a c) = c := by
  -- `[h̄]⁻¹ = [h]`; regroup; `[h][h̄] = 1` on the left and on the right.
  simp only [conj, inv_inv, comp_assoc, comp_inv_comp, comp_inv, comp_id]

/-- `thm:change-basepoint`: `β_h β_{h̄} [g] = [h̄ h g h̄ h] = [g]`, for a loop `g` at `y`. -/
theorem conj_conj_inv (a : PathClass x y) (c : PathClass y y) : conj a (conj (inv a) c) = c := by
  simp only [conj, inv_inv, comp_assoc, inv_comp_comp, inv_comp, comp_id]

end PathClass

section ChangeBasepoint
variable [TopSpace X] {x y z : X}

/-- **`thm:change-basepoint`**, on path classes: `β_{[h]} : π₁(X, x) ≃* π₁(X, y)`,
`[f] ↦ [h̄ · f · h]`, a homomorphism by `thm:groupoid-laws`
(`[h̄fh][h̄gh] = [h̄fgh]`), with inverse `β_{[h̄]}`.

Lean: an isomorphism of groups `≃*` is given by the map `toFun`, its inverse `invFun`, the proofs
`left_inv`, `right_inv` that they are inverse to each other, and the proof `map_mul'` that the
map is a homomorphism. -/
def betaClass (a : PathClass x y) : pi1 x ≃* pi1 y where
  toFun := PathClass.conj a
  invFun := PathClass.conj (PathClass.inv a)
  left_inv := PathClass.conj_inv_conj a
  right_inv := PathClass.conj_conj_inv a
  map_mul' := PathClass.conj_mul a

/-- **`thm:change-basepoint`**: a path `h` from `x` to `y` gives the isomorphism
`β_h : π₁(X, x) ≃* π₁(X, y)`, `β_h[f] = [h̄ · f · h]`, with inverse `β_{h̄}`. The book's
direction (Lee's `Φ_h`; Hatcher's `β_h` is our `β_{h̄}`, `rem:beta-direction`).
Mathlib: `FundamentalGroup.fundamentalGroupMulEquivOfPath`. -/
def beta (h : Path x y) : pi1 x ≃* pi1 y := betaClass ⟦h⟧

/-- Unfolding: `β_h[f] = [h̄ · (f · h)]`. -/
theorem beta_mk (h : Path x y) (f : Path x x) :
    beta h ⟦f⟧ = ⟦h.symm.trans (f.trans h)⟧ := rfl

/-- `thm:change-basepoint`: the inverse of `β_h` is `β_{h̄}`. (By definition: `MulEquiv.ext`
says two isomorphisms are equal if they agree at every element.) -/
theorem beta_symm (h : Path x y) : (beta h).symm = beta h.symm :=
  MulEquiv.ext fun _ => rfl

/-- `exr-6-basepoint`: `β_h` depends only on the path class of `h`: if `h ≃ₚ h'` then
`β_h = β_{h'}`. -/
theorem beta_congr {h h' : Path x y} (hh : h.Homotopic h') : beta h = beta h' := by
  -- `β_h` is defined from `[h]` alone, and `[h] = [h']` (`Quotient.sound`).
  unfold beta
  rw [Quotient.sound hh]

/-- `exr-6-basepoint`: `β_{c_x}` is the identity: `[c̄_x][f][c_x] = [f]`. -/
theorem beta_refl (x : X) : beta (Path.refl x) = MulEquiv.refl (pi1 x) := by
  -- Check at every `c ∈ π₁(X, x)`: `[c_x]⁻¹ = [c_x]`, and `[c_x]` is a two-sided identity.
  ext c
  show PathClass.conj (PathClass.refl x) c = c
  simp only [PathClass.conj, PathClass.inv_refl, PathClass.comp_id, PathClass.id_comp]

/-- `exr-6-basepoint`: `β_{h · k} = β_k ∘ β_h`, for `h` from `x` to `y` and `k` from `y` to `z`.
Mathlib: none stated (the functoriality of `FundamentalGroupoid`). -/
theorem beta_trans (h : Path x y) (k : Path y z) :
    beta (h.trans k) = (beta h).trans (beta k) := by
  -- At `c = [f]`: `[hk]⁻¹ [f] [hk] = [k̄]([h̄][f][h])[k]`, since `[hk]⁻¹ = [k̄][h̄]`; regroup.
  -- (Lean writes the composite `β_k ∘ β_h` as `(beta h).trans (beta k)`, first `β_h`.)
  ext c
  show PathClass.conj (PathClass.comp ⟦h⟧ ⟦k⟧) c = PathClass.conj ⟦k⟧ (PathClass.conj ⟦h⟧ c)
  simp only [PathClass.conj, PathClass.inv_comp_eq, PathClass.comp_assoc]

/-- **`thm:change-basepoint`**: for two paths `h, h'` from `x` to `y` and the loop
`α = h · h̄'` at `x`, `β_{h'}⁻¹ β_h [f] = [α]⁻¹[f][α]`. -/
theorem beta_symm_beta (h h' : Path x y) (c : pi1 x) :
    (beta h').symm (beta h c) =
      (⟦h.trans h'.symm⟧ : pi1 x)⁻¹ * c * ⟦h.trans h'.symm⟧ := by
  -- The book's proof: `β_{h'}⁻¹ = β_{h̄'}`, so the left side is `[h' h̄ f h h̄']`; and the
  -- reverse of `α = h h̄'` is `h' h̄`, so the right side is the same class. Below, the goal
  -- written out with classes; `simp` uses `[ab]⁻¹ = b⁻¹a⁻¹`, `[h̄']⁻¹ = [h']` and associativity.
  show PathClass.conj (PathClass.inv ⟦h'⟧) (PathClass.conj ⟦h⟧ c) =
    PathClass.comp (PathClass.comp (PathClass.inv (PathClass.comp ⟦h⟧ (PathClass.inv ⟦h'⟧))) c)
      (PathClass.comp ⟦h⟧ (PathClass.inv ⟦h'⟧))
  simp only [PathClass.conj, PathClass.inv_comp_eq, PathClass.inv_inv, PathClass.comp_assoc]

end ChangeBasepoint

/-! ## Simply connected spaces (`def:simply-connected`) -/

/-- Path-connected, as `def:simply-connected` uses it: non-empty, and any two points are joined
by a path. Mathlib: `PathConnectedSpace`.

Lean: `Nonempty X` says "`X` has a point", and `Nonempty (Path x y)` says "there is a path from
`x` to `y`", without naming one. `∧` is "and". -/
def PathConnected (X : Type u) [TopSpace X] : Prop := Nonempty X ∧ ∀ x y : X, Nonempty (Path x y)

/-- **`def:simply-connected`**: `X` is simply connected if it is non-empty, path-connected and
`π₁(X, x) = 1` for every `x ∈ X`. Mathlib: `SimplyConnectedSpace`. -/
def SimplyConnected (X : Type u) [TopSpace X] : Prop :=
  PathConnected X ∧ ∀ (x : X) (a : pi1 x), a = 1

/-- `thm:change-basepoint`: if `π₁(X, x) = 1` (`hx`) and `h` is a path from `x` to `y`, then
`π₁(X, y) = 1`, since `β_h` is an isomorphism. -/
theorem pi1_eq_one_of_path [TopSpace X] {x y : X} (h : Path x y) (hx : ∀ a : pi1 x, a = 1)
    (b : pi1 y) : b = 1 := by
  -- `b = β_h(β_h⁻¹ b) = β_h(1) = 1`: the middle step is `π₁(X, x) = 1`, the last one holds for
  -- every homomorphism (`map_one`).
  rw [← (beta h).apply_symm_apply b, hx ((beta h).symm b), map_one]

/-- `def:simply-connected`: `π₁(X, x) = 1` "for some, and then by `thm:change-basepoint` for
every, `x ∈ X`". Mathlib: `simply_connected_iff_loops_nullhomotopic` (a different form). -/
theorem simplyConnected_iff_exists [TopSpace X] :
    SimplyConnected X ↔ PathConnected X ∧ ∃ x : X, ∀ a : pi1 x, a = 1 := by
  constructor
  -- "For every `x`" gives "for some `x`", since `X` has a point `x`. (Lean: `rintro ⟨hp, h⟩` is
  -- `intro` that at once splits the hypothesis "`hp` and `h`" into its two halves.)
  · rintro ⟨hp, h⟩
    obtain ⟨x⟩ := hp.1
    exact ⟨hp, x, h x⟩
  -- Conversely, if `π₁(X, x) = 1`, take any `y`: a path `h` from `x` to `y` exists since `X` is
  -- path-connected, and `π₁(X, y) = 1` by `β_h` (`pi1_eq_one_of_path`).
  · rintro ⟨hp, x, hx⟩
    refine ⟨hp, fun y b => ?_⟩
    obtain ⟨h⟩ := hp.2 x y
    exact pi1_eq_one_of_path h hx b

/-! ## Moving the base point along a homotopy (`lem:homotopy-basepoint`)

The picture (`fig-6-homotopy-basepoint`). A homotopy `H : φ ≃ ψ : X → Y` and a path `f` from
`x` to `x'` give the square `F(s, t) = H(f(s), t)`, `F : I × I → Y`. Its bottom edge is `φ ∘ f`,
its top edge is `ψ ∘ f`, its left edge is the track `h_x` of the base point `x`, which `H` drags
from `φ(x)` to `ψ(x)`, and its right edge is the track `h_{x'}` of the end `x'`. Going along the
bottom and up the right side is homotopic, ends fixed, to going up the left side and along the
top, so `φf · h_{x'} ≃ₚ h_x · ψf`. -/

namespace Homotopy
variable [TopSpace X] [TopSpace Y] {φ ψ : X → Y}

/-- `lem:homotopy-basepoint`: the path `h_x(t) = H(x, t)` that a homotopy `H : φ ≃ ψ` traces
from `φ(x)` to `ψ(x)`, the track of the point `x`. Mathlib: `ContinuousMap.Homotopy.evalAt`. -/
def track (H : Homotopy φ ψ) (x : X) : Path (φ x) (ψ x) where
  -- `t ↦ H(x, t)`, continuous as `H` composed with the continuous `t ↦ (x, t)`.
  toFun t := H.toFun (x, t)
  continuous_toFun := H.continuous_toFun.comp (continuous_const.prodMk continuous_id)
  -- It starts at `H(x, 0) = φ(x)` and ends at `H(x, 1) = ψ(x)` (`def:homotopy`).
  source' := H.zero' x
  target' := H.one' x

/-- Unfolding: `h_x(t) = H(x, t)`. -/
theorem track_apply (H : Homotopy φ ψ) (x : X) (t : I) : H.track x t = H.toFun (x, t) := rfl

/-- The square of `lem:homotopy-basepoint` (`fig-6-homotopy-basepoint`), as an explicit path
homotopy `φf · h_{x'} ≃ₚ h_x · ψf`.

The square `F(s, t) = H(f(s), t)` has edges `φf` (bottom), `ψf` (top), `h_x` (left), `h_{x'}`
(right). The route along the bottom and up the right side of `I × I` is
`s ↦ (min(2s, 1), max(2s - 1, 0)) = (dbl s, dbl' s)`; the route up the left side and along the
top is `s ↦ (max(2s - 1, 0), min(2s, 1)) = (dbl' s, dbl s)`. Both stay in the convex square, so
the straight-line homotopy `(s, t) ↦ (1 - t)·(first route) + t·(second route)` moves one to the
other with the corners `(0, 0)` and `(1, 1)` fixed; composed with `F`, it is the path homotopy.
In the code, `I.line α β (s, t) = (1 - t) α(s) + t β(s)` is that straight line, one coordinate
at a time. -/
def square (H : Homotopy φ ψ) (hφ : Continuous φ) (hψ : Continuous ψ) {x x' : X}
    (f : Path x x') :
    PathHomotopy ((f.map hφ rfl rfl).trans (H.track x'))
      ((H.track x).trans (f.map hψ rfl rfl)) where
  -- `(s, t) ↦ F(σ(s, t), τ(s, t)) = H(f(σ), τ)`, where `(σ, τ)` moves along the straight line
  -- from the first route to the second.
  toFun q := H.toFun (f (I.line I.dbl I.dbl' q), I.line I.dbl' I.dbl q)
  -- Continuous: `H`, `f` and the straight lines are continuous (`I.continuous_line`, week 4).
  continuous_toFun := H.continuous_toFun.comp
    ((f.continuous.comp (I.continuous_line I.continuous_dbl I.continuous_dbl')).prodMk
      (I.continuous_line I.continuous_dbl' I.continuous_dbl))
  -- At `t = 0` it is `φf · h_{x'}`: the point `(σ, τ)` runs along the first route
  -- `(dbl s, dbl' s)`.
  zero' s := by
    show H.toFun (f (I.line I.dbl I.dbl' (s, 0)), I.line I.dbl' I.dbl (s, 0)) = _
    rw [I.line_zero, I.line_zero]
    rcases le_total (s : ℝ) (1 / 2) with h | h
    -- For `s ≤ 1/2`, along the bottom: `H(f(2s), 0) = φ(f(2s)) = (φf · h_{x'})(s)`.
    · rw [Path.trans_apply_of_le _ _ s h, I.dbl'_of_le h, H.zero']; rfl
    -- For `s ≥ 1/2`, up the right side: `H(f(1), 2s - 1) = H(x', 2s - 1) = h_{x'}(2s - 1)`.
    · rw [Path.trans_apply_of_ge _ _ s h, I.dbl_of_ge h, f.target]; rfl
  -- At `t = 1` it is `h_x · ψf`: the point runs along the second route `(dbl' s, dbl s)`.
  one' s := by
    show H.toFun (f (I.line I.dbl I.dbl' (s, 1)), I.line I.dbl' I.dbl (s, 1)) = _
    rw [I.line_one, I.line_one]
    rcases le_total (s : ℝ) (1 / 2) with h | h
    -- For `s ≤ 1/2`, up the left side: `H(f(0), 2s) = H(x, 2s) = h_x(2s)`.
    · rw [Path.trans_apply_of_le _ _ s h, I.dbl'_of_le h, f.source]; rfl
    -- For `s ≥ 1/2`, along the top: `H(f(2s - 1), 1) = ψ(f(2s - 1)) = (ψf)(2s - 1)`.
    · rw [Path.trans_apply_of_ge _ _ s h, I.dbl_of_ge h, H.one']; rfl
  -- The start stays at `φ(x)`: both routes start at the corner `(0, 0)`, so the straight line
  -- between them does too, and `F(0, 0) = H(f(0), 0) = φ(x)`.
  source' t := by
    have h0 : ∀ α β : I → I, α 0 = 0 → β 0 = 0 → I.line α β (0, t) = 0 :=
      fun α β h1 h2 => Subtype.ext (by simp [h1, h2])
    show H.toFun (f (I.line I.dbl I.dbl' (0, t)), I.line I.dbl' I.dbl (0, t)) = φ x
    rw [h0 _ _ I.dbl_zero I.dbl'_zero, h0 _ _ I.dbl'_zero I.dbl_zero, f.source, H.zero']
  -- The end stays at `ψ(x')`: both routes end at the corner `(1, 1)`, and
  -- `F(1, 1) = H(f(1), 1) = ψ(x')`.
  target' t := by
    have h1 : ∀ α β : I → I, α 1 = 1 → β 1 = 1 → I.line α β (1, t) = 1 :=
      fun α β h1 h2 => Subtype.ext (by simp [h1, h2])
    show H.toFun (f (I.line I.dbl I.dbl' (1, t)), I.line I.dbl' I.dbl (1, t)) = ψ x'
    rw [h1 _ _ I.dbl_one I.dbl'_one, h1 _ _ I.dbl'_one I.dbl_one, f.target, H.one']

/-- **`lem:homotopy-basepoint`**: for a homotopy `H : φ ≃ ψ : X → Y`, not necessarily pointed,
and a path `f` from `x` to `x'`, `φf · h_{x'} ≃ₚ h_x · ψf`. The book's proof: the square
(`Homotopy.square`). Mathlib: `ContinuousMap.Homotopy.eq_diag_path`,
`FundamentalGroupoidFunctor.homotopicMapsNatIso`.

Lean: `f.map hφ rfl rfl` is the path `φ ∘ f` (`Path.map`, week 6); `(H.track x).trans g` is the
product `h_x · g`. -/
theorem homotopic_square (H : Homotopy φ ψ) (hφ : Continuous φ) (hψ : Continuous ψ) {x x' : X}
    (f : Path x x') :
    ((f.map hφ rfl rfl).trans (H.track x')).Homotopic ((H.track x).trans (f.map hψ rfl rfl)) :=
  ⟨H.square hφ hψ f⟩

end Homotopy

section HomotopyBasepoint
variable [TopSpace X] [TopSpace Y] {φ ψ : X → Y}

/-- **`lem:homotopy-basepoint`**, the consequence: `ψ_* = β_{h_x} ∘ φ_*` on `π₁(X, x)`, that is,
`[ψf] = [h̄_x · φf · h_x]` for every loop `f` at `x`.
Mathlib: `FundamentalGroupoidFunctor.homotopicMapsNatIso`. -/
theorem induced_homotopy (H : Homotopy φ ψ) (hφ : Continuous φ) (hψ : Continuous ψ) (x : X)
    (a : pi1 x) : induced ψ hψ rfl a = beta (H.track x) (induced φ hφ rfl a) := by
  -- Write `a = [f]` for a loop `f` at `x`.
  induction a using Quotient.ind with | _ f => ?_
  -- The square for the loop `f` (so `x' = x`), as an equation of classes:
  -- `[φf][h_x] = [h_x][ψf]` (`Homotopy.homotopic_square`).
  have hsq : PathClass.comp ⟦f.map hφ rfl rfl⟧ ⟦H.track x⟧ =
      PathClass.comp ⟦H.track x⟧ ⟦f.map hψ rfl rfl⟧ :=
    (PathClass.comp_mk _ _).trans
      ((Quotient.sound (H.homotopic_square hφ hψ f)).trans (PathClass.comp_mk _ _).symm)
  -- So `β_{h_x}[φf] = [h̄_x]([φf][h_x]) = [h̄_x]([h_x][ψf]) = [ψf]`.
  show (⟦f.map hψ rfl rfl⟧ : pi1 (ψ x)) = PathClass.conj ⟦H.track x⟧ ⟦f.map hφ rfl rfl⟧
  rw [PathClass.conj, hsq, PathClass.inv_comp_comp]

/-- **`lem:homotopy-basepoint`**: `ψ_* = β_{h_x} ∘ φ_*` as homomorphisms
`π₁(X, x) → π₁(Y, ψ(x))`. (Two homomorphisms that agree at every element are equal,
`MonoidHom.ext`.) -/
theorem induced_eq_beta_comp (H : Homotopy φ ψ) (hφ : Continuous φ) (hψ : Continuous ψ) (x : X) :
    induced ψ hψ rfl = (beta (H.track x)).toMonoidHom.comp (induced φ hφ rfl) :=
  MonoidHom.ext (induced_homotopy H hφ hψ x)

end HomotopyBasepoint

/-! ## Homotopy equivalence and homotopy invariance (`def:homotopy-equivalence`,
`thm:pi1-homotopy-invariant`) -/

/-- **`def:homotopy-equivalence`**: a continuous `φ : X → Y` is a homotopy equivalence if it has
a homotopy inverse, a continuous `ψ : Y → X` with `ψφ ≃ id_X` and `φψ ≃ id_Y`.
Mathlib: `ContinuousMap.HomotopyEquiv` (a structure carrying `ψ` and the homotopies).

Lean: `fun a => a` is the identity map. -/
def IsHomotopyEquiv [TopSpace X] [TopSpace Y] (φ : X → Y) : Prop :=
  Continuous φ ∧ ∃ ψ : Y → X, Continuous ψ ∧ Homotopic (ψ ∘ φ) (fun a => a) ∧
    Homotopic (φ ∘ ψ) (fun b => b)

/-- **`def:homotopy-equivalence`**: `X ≃ Y`, `X` and `Y` are homotopy equivalent.
Mathlib: `Nonempty (ContinuousMap.HomotopyEquiv X Y)`. -/
def HomotopyEquivalent (X : Type u) (Y : Type v) [TopSpace X] [TopSpace Y] : Prop :=
  ∃ φ : X → Y, IsHomotopyEquiv φ

section Invariance
variable [TopSpace X] [TopSpace Y]

/-- The step of `thm:pi1-homotopy-invariant` used twice: if `χ : X → X` is homotopic to the
identity (`h`), then `χ_* : π₁(X, x) → π₁(X, χ(x))` is bijective, because by
`lem:homotopy-basepoint` `id = β_{h_x} ∘ χ_*` with `β_{h_x}` an isomorphism. -/
theorem induced_bijective_of_homotopic_id {χ : X → X} (hχ : Continuous χ)
    (h : Homotopic χ (fun a => a)) (x : X) :
    Function.Bijective (induced χ hχ (rfl : χ x = χ x)) := by
  -- Take a homotopy `H : χ ≃ id`; its track `h_x` runs from `χ(x)` to `x`.
  obtain ⟨H⟩ := h
  -- `lem:homotopy-basepoint` for `H`: `a = id_*(a) = β_{h_x}(χ_*(a))` for every `a`
  -- (`induced_id`, `induced_homotopy`). (Lean: `DFunLike.congr_fun e a` evaluates an equation
  -- `e` of maps at the point `a`.)
  have key : ∀ a : pi1 x, a = beta (H.track x) (induced χ hχ rfl a) := fun a =>
    (DFunLike.congr_fun (induced_id x) a).symm.trans (induced_homotopy H hχ continuous_id x a)
  -- One to one: if `χ_*(a) = χ_*(b)`, then `a = β(χ_*(a)) = β(χ_*(b)) = b`.
  -- Onto: `c ∈ π₁(X, χ(x))` is `χ_*(β(c))`; to see it, apply the injective `β`:
  -- `β(χ_*(β(c))) = β(c)` by `key` for `a = β(c)`.
  refine ⟨fun a b hab => by rw [key a, key b, hab], fun c => ⟨(beta (H.track x)) c, ?_⟩⟩
  apply (beta (H.track x)).injective
  rw [← key]

/-- **`thm:pi1-homotopy-invariant`**: if `φ : X → Y` is a homotopy equivalence then
`φ_* : π₁(X, x) → π₁(Y, φ(x))` is bijective. The book's proof, with `ψ` a homotopy inverse:
`ψ_* φ_* = (ψφ)_*` is bijective (`lem:homotopy-basepoint` for `ψφ ≃ id_X`), so
`ψ_* : π₁(Y, φ(x)) → π₁(X, ψφ(x))` is onto; `φ_* ψ_* = (φψ)_*` is bijective (the same lemma for
`φψ ≃ id_Y` at `φ(x)`), so the same `ψ_*` is one to one; hence `φ_* = ψ_*⁻¹ (ψφ)_*` is
bijective. Mathlib: `FundamentalGroupoidFunctor.equivOfHomotopyEquiv` (on fundamental
groupoids). -/
theorem induced_bijective_of_isHomotopyEquiv {φ : X → Y} (hφ : IsHomotopyEquiv φ) (x : X) :
    Function.Bijective (induced φ hφ.1 (rfl : φ x = φ x)) := by
  -- Let `ψ` be a homotopy inverse, `h1 : ψφ ≃ id_X`, `h2 : φψ ≃ id_Y`.
  obtain ⟨hφc, ψ, hψ, h1, h2⟩ := hφ
  -- Step 1. `(ψφ)_* = ψ_* ∘ φ_*` (`prop:induced`) is bijective on `π₁(X, x)`.
  have hA := induced_bijective_of_homotopic_id (hψ.comp hφc) h1 x
  rw [induced_comp φ ψ hφc hψ rfl rfl, MonoidHom.coe_comp] at hA
  -- Step 2. `(φψ)_* = φ_* ∘ ψ_*` is bijective on `π₁(Y, φ(x))`.
  have hB := induced_bijective_of_homotopic_id (hφc.comp hψ) h2 (φ x)
  rw [induced_comp ψ φ hψ hφc rfl rfl, MonoidHom.coe_comp] at hB
  -- Step 3. So `ψ_* : π₁(Y, φ(x)) → π₁(X, ψφ(x))` is one to one: if `φ_* ∘ ψ_*` is, so is `ψ_*`
  -- (`Function.Injective.of_comp`).
  have hψi : Function.Injective (induced ψ hψ (rfl : ψ (φ x) = ψ (φ x))) :=
    Function.Injective.of_comp hB.1
  -- Step 4. `φ_*` is one to one, because `ψ_* ∘ φ_*` is. It is onto: for `c ∈ π₁(Y, φ(x))`,
  -- Step 1 gives `a` with `ψ_*(φ_*(a)) = ψ_*(c)`, and Step 3 cancels `ψ_*`: `φ_*(a) = c`.
  -- (This is the book's `φ_* = ψ_*⁻¹ (ψφ)_*`, said element by element.)
  refine ⟨Function.Injective.of_comp hA.1, fun c => ?_⟩
  obtain ⟨a, ha⟩ := hA.2 (induced ψ hψ rfl c)
  exact ⟨a, hψi ha⟩

/-- **`thm:pi1-homotopy-invariant`**, packaged: a homotopy equivalence `φ` gives the
isomorphism `φ_* : π₁(X, x) ≃* π₁(Y, φ(x))` (a bijective homomorphism is an isomorphism,
`MulEquiv.ofBijective`). Mathlib: `FundamentalGroupoidFunctor.equivOfHomotopyEquiv`. -/
def pi1EquivOfIsHomotopyEquiv {φ : X → Y} (hφ : IsHomotopyEquiv φ) (x : X) :
    pi1 x ≃* pi1 (φ x) :=
  MulEquiv.ofBijective (induced φ hφ.1 rfl) (induced_bijective_of_isHomotopyEquiv hφ x)

/-- Unfolding: the isomorphism of `thm:pi1-homotopy-invariant` is `φ_*`. -/
theorem pi1EquivOfIsHomotopyEquiv_apply {φ : X → Y} (hφ : IsHomotopyEquiv φ) (x : X)
    (a : pi1 x) : pi1EquivOfIsHomotopyEquiv hφ x a = induced φ hφ.1 rfl a := rfl

end Invariance

/-! ## Contractible spaces (`def:contractible`, `cor:contractible-sc`) -/

/-- **`def:contractible`**: `X` is contractible if `id_X` is homotopic to a constant map. (So
`X` is non-empty: the constant takes a value in `X`.) Mathlib: `ContractibleSpace` (defined as
`X ≃ₕ Unit`), `ContinuousMap.Nullhomotopic`. -/
def Contractible (X : Type u) [TopSpace X] : Prop :=
  ∃ c : X, Homotopic (fun a : X => a) (fun _ => c)

section Contractible
variable [TopSpace X] [TopSpace Y]

/-- `prop:induced`: a constant map `X → Y` with value `c` induces the trivial homomorphism,
since `c ∘ f` is the constant loop `c_c`. -/
theorem induced_const (c : Y) (x : X) (a : pi1 x) :
    induced (fun _ : X => c) continuous_const rfl a = 1 := by
  -- Write `a = [f]`; then `[c ∘ f] = [c_c]`, because `c ∘ f` is the constant path itself.
  induction a using Quotient.ind with | _ f => ?_
  show (⟦f.map continuous_const rfl rfl⟧ : pi1 c) = ⟦Path.refl c⟧
  congr 1

/-- **`cor:contractible-sc`**: a contractible space is simply connected. A contraction `H` of
`id` to the constant `c` gives the path `t ↦ H(x, t)` from each `x` to `c`, so `X` is
path-connected. The book gets `π₁(X, x) = 1` from `thm:pi1-homotopy-invariant` for `X → ∗`; here
the same argument runs for `id ≃ c` itself: by `lem:homotopy-basepoint`,
`1 = c_* = β_{h_x} ∘ id_*`, and `β_{h_x}` is an isomorphism, so `π₁(X, x) = 1`.
Mathlib: `SimplyConnectedSpace.ofContractible`. -/
theorem Contractible.simplyConnected (hX : Contractible X) : SimplyConnected X := by
  -- Let `H : id ≃ c` be a contraction; its track `h_x` runs from `x` to `c`.
  obtain ⟨c, ⟨H⟩⟩ := hX
  -- Non-empty: `c ∈ X`. Path-connected: `h_x · h̄_y` runs from `x` through `c` to `y`.
  -- It remains to show `a = 1` for every `a ∈ π₁(X, x)`.
  refine ⟨⟨⟨c⟩, fun x y => ⟨(H.track x).trans (H.track y).symm⟩⟩, fun x a => ?_⟩
  -- `lem:homotopy-basepoint` for `H`: `c_*(a) = β_{h_x}(id_*(a))`, that is, `1 = β_{h_x}(a)`
  -- (`induced_const`, `induced_id`).
  have h := induced_homotopy H continuous_id continuous_const x a
  rw [induced_const c x a, DFunLike.congr_fun (induced_id x) a] at h
  -- So `β_{h_x}(a) = 1 = β_{h_x}(1)`, and `a = 1` since `β_{h_x}` is one to one.
  exact (beta (H.track x)).injective (h.symm.trans (map_one _).symm)

end Contractible

/-! ## The fundamental group of a product (`prop:pi1-product`)

The book's proof: a map into `X × Y` is exactly a pair of maps, into `X` and into `Y`
(`thm:product-top`); so a loop in `X × Y` is a pair of loops, and a path homotopy in `X × Y` is a
pair of path homotopies. Here `p_X`, `p_Y` are the projections, `Prod.fst`, `Prod.snd` in
Lean. -/

section Product
variable [TopSpace X] [TopSpace Y]

/-- `prop:pi1-product`: two paths `f` in `X` and `g` in `Y` make the path `s ↦ (f(s), g(s))` in
`X × Y` (`thm:product-top`). Mathlib: `Path.prod`. -/
def Path.prod {x x' : X} {y y' : Y} (f : Path x x') (g : Path y y') : Path (x, y) (x', y') where
  toFun s := (f s, g s)
  continuous_toFun := f.continuous.prodMk g.continuous
  -- It starts at `(f(0), g(0)) = (x, y)` and ends at `(f(1), g(1)) = (x', y')`.
  source' := by show (f 0, g 0) = (x, y); rw [f.source, g.source]
  target' := by show (f 1, g 1) = (x', y'); rw [f.target, g.target]

/-- `prop:pi1-product`: a path homotopy into `X × Y` is a pair of path homotopies of the
components (`thm:product-top`): if `F : p_X p ≃ₚ p_X q` and `G : p_Y p ≃ₚ p_Y q`, then
`(s, t) ↦ (F(s, t), G(s, t))` is a path homotopy `p ≃ₚ q`.
Mathlib: `Path.Homotopic.prodHomotopy`.

Lean: `p.map continuous_fst rfl rfl` is the path `p_X ∘ p`; the `(rfl : (x, y).1 = x)` say that
`p_X` sends the ends `(x, y)`, `(x', y')` to `x`, `x'`. Each field below holds coordinate by
coordinate (`Prod.ext`: two pairs are equal if their coordinates are). -/
def PathHomotopy.pair {x x' : X} {y y' : Y} {p q : Path (x, y) (x', y')}
    (F : PathHomotopy (p.map continuous_fst (rfl : (x, y).1 = x) (rfl : (x', y').1 = x'))
      (q.map continuous_fst (rfl : (x, y).1 = x) (rfl : (x', y').1 = x')))
    (G : PathHomotopy (p.map continuous_snd (rfl : (x, y).2 = y) (rfl : (x', y').2 = y'))
      (q.map continuous_snd (rfl : (x, y).2 = y) (rfl : (x', y').2 = y'))) :
    PathHomotopy p q where
  toFun r := (F.toFun r, G.toFun r)
  continuous_toFun := F.continuous_toFun.prodMk G.continuous_toFun
  zero' s := Prod.ext (F.zero' s) (G.zero' s)
  one' s := Prod.ext (F.one' s) (G.one' s)
  source' t := Prod.ext (F.source' t) (G.source' t)
  target' t := Prod.ext (F.target' t) (G.target' t)

/-- `prop:pi1-product`: the homomorphism `[f] ↦ ([p_X f], [p_Y f])`, whose components are the
induced homomorphisms `(p_X)_*`, `(p_Y)_*` (`prop:induced`). -/
def pi1ProdHom (x : X) (y : Y) : pi1 ((x, y) : X × Y) →* pi1 x × pi1 y :=
  (induced Prod.fst continuous_fst (rfl : (x, y).1 = x)).prod
    (induced Prod.snd continuous_snd (rfl : (x, y).2 = y))

/-- `prop:pi1-product`: `[f] ↦ ([p_X f], [p_Y f])` is one to one: if the components of two
loops are path homotopic, the pair of the homotopies is a path homotopy of the loops. -/
theorem pi1ProdHom_injective (x : X) (y : Y) : Function.Injective (pi1ProdHom x y) := by
  -- Let `[f]`, `[g]` have the same image.
  intro a b hab
  induction a using Quotient.ind with | _ f => ?_
  induction b using Quotient.ind with | _ g => ?_
  -- Then `[p_X f] = [p_X g]` in `π₁(X, x)` and `[p_Y f] = [p_Y g]` in `π₁(Y, y)`.
  have h1 : (⟦f.map continuous_fst (rfl : (x, y).1 = x) rfl⟧ : pi1 x) =
      ⟦g.map continuous_fst (rfl : (x, y).1 = x) rfl⟧ := congrArg Prod.fst hab
  have h2 : (⟦f.map continuous_snd (rfl : (x, y).2 = y) rfl⟧ : pi1 y) =
      ⟦g.map continuous_snd (rfl : (x, y).2 = y) rfl⟧ := congrArg Prod.snd hab
  -- Equal classes come from path homotopies `F : p_X f ≃ₚ p_X g`, `G : p_Y f ≃ₚ p_Y g`
  -- (`Quotient.exact`, the converse of `Quotient.sound`).
  obtain ⟨F⟩ := Quotient.exact h1
  obtain ⟨G⟩ := Quotient.exact h2
  -- The pair `(F, G)` is a path homotopy `f ≃ₚ g`, so `[f] = [g]`.
  exact Quotient.sound ⟨PathHomotopy.pair F G⟩

/-- `prop:pi1-product`: `[f] ↦ ([p_X f], [p_Y f])` is onto: `([a], [b])` is the image of the
class of the loop `s ↦ (a(s), b(s))`. -/
theorem pi1ProdHom_surjective (x : X) (y : Y) : Function.Surjective (pi1ProdHom x y) := by
  -- Take `([f], [g])`; the loop `s ↦ (f(s), g(s))` has components `f` and `g` by definition.
  rintro ⟨a, b⟩
  induction a using Quotient.ind with | _ f => ?_
  induction b using Quotient.ind with | _ g => ?_
  exact ⟨⟦f.prod g⟧, rfl⟩

/-- **`prop:pi1-product`**: `π₁(X × Y, (x, y)) ≃* π₁(X, x) × π₁(Y, y)`,
`[f] ↦ ([p_X f], [p_Y f])`, for the course product (`thm:product-top`). The book's proof, for
loops: a loop, and a path homotopy, into `X × Y` is exactly a pair of them in `X` and `Y`; the
map is a homomorphism because its components are induced homomorphisms. Mathlib:
`FundamentalGroupoidFunctor.prodIso` (on fundamental groupoids); no `FundamentalGroup`
version in v4.34.1. -/
def pi1Prod (x : X) (y : Y) : pi1 ((x, y) : X × Y) ≃* pi1 x × pi1 y :=
  MulEquiv.ofBijective (pi1ProdHom x y) ⟨pi1ProdHom_injective x y, pi1ProdHom_surjective x y⟩

/-- Unfolding: `[f] ↦ ([p_X f], [p_Y f])`. -/
theorem pi1Prod_mk (x : X) (y : Y) (f : Path ((x, y) : X × Y) (x, y)) :
    pi1Prod x y ⟦f⟧ = (⟦f.map continuous_fst rfl rfl⟧, ⟦f.map continuous_snd rfl rfl⟧) := rfl

end Product

end

end Course
