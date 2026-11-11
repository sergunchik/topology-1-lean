/-
Machine-generated (Claude, Aristotle), no line written by a person. Copyleft: GPL-3.0-or-later.

# Week 2, continued: pullbacks, pushouts, cut points

This file builds the two gluing constructions of week 2 of the book and uses
connectedness to tell spaces apart. The pullback of `f : X → Z`, `g : Y → Z` is the fibre product
`X ×_Z Y = {(x, y) | f(x) = g(y)}` (`def:pullback`, `prop:pullback-top`); the pushout of
`f : A → X`, `g : A → Y` is `X ⊔_A Y = (X ⊔ Y)/∼` with `f(a) ∼ g(a)` (`def:pushout`,
`thm:pushout-top`), and gluing `Y` to `X` along `φ : B → X` is a special case (`def:adjunction`);
both universal properties are proved as the book proves them. A cut point is a point whose removal
disconnects (`def:cut-point`); a homeomorphism carries cut points to cut points, and counting
them gives `ℝ ≇ [0, 1) ≇ [0, 1] ≇ ℝ` (`thm:one-dimensional`, `rem:non-cut-count`) and
`ℝ ≇ ℝ²` (`prop:line-not-plane`). Last, stereographic projection `S^n ∖ {N} ≅ ℝ^n` for
`n = 1, 2` (`prop:stereographic`). Each declaration names the book's label and Mathlib's
counterpart, checked against Lean and Mathlib v4.34.1.

Departures from the book:
* Connectedness is defined as in Analysis I (no splitting into two disjoint non-empty open
  sets), with a bridge to Mathlib's `PreconnectedSpace`; so the empty space counts as connected.
  "Joined by paths implies connected" (Analysis I §8), which the book cites, is proved here from
  the connectedness of `[0, 1]`.
* `thm:one-dimensional`: the circle is defined only in week 6 (`Course.S1`), so the three cases
  without `S¹` are proved. `ℝ ≇ [0, 1)` is the book's argument; `ℝ ≇ [0, 1]` and
  `[0, 1] ≇ [0, 1)`, which the book settles by compactness, are settled by counting non-cut
  points, as `rem:non-cut-count` suggests.
* `prop:line-not-plane` only for `n = 2`, and with two fixed points instead of "a third point off
  the line" (see `connected_plane_compl`).
* `prop:stereographic` only for `n = 1, 2` and `p` the north pole (the book rotates `p` there).
* From Analysis I, through the bridges `real_toMathlib`, `prod_toMathlib`, `subspace_toMathlib`,
  `I_toMathlib`: the connectedness of `[0, 1]` (Mathlib's `unitInterval` is a `ConnectedSpace`),
  the openness of the half-lines `(-∞, c)` and `(c, ∞)`, and the continuity of real formulas
  (segments, stereographic projection); each use says so.

New to Lean? Read `Course/README.md` first.
-/
import Course.Week02
import Mathlib.Topology.Algebra.GroupWithZero
import Mathlib.Tactic.LinearCombination

-- Bookkeeping. `X`, `Y`, `Z`, `W`, `A` below are spaces (types; `u v w u'` are their "universe
-- levels", which you may ignore). `open Set` lets us write `univ`, `Iio c` without the prefix
-- `Set.`.
universe u v w u'

set_option warn.classDefReducibility false
set_option linter.unusedSectionVars false

namespace Course

open Set

variable {X : Type u} {Y : Type v} {Z : Type w}

/-! ## Maps into a subspace (`prop-1-15`, `ex:initial-final`) -/

section IntoSubspace
variable [TopSpace X] [TopSpace Y]

/-- If `g : X → Y` is continuous and takes its values in `A ⊆ Y` (`h`), then `g`, seen as a map
`X → A`, is continuous. `ex:initial-final` for a subspace. Mathlib: `Continuous.subtype_mk`.

Lean: `fun x => ⟨g x, h x⟩` is the map `x ↦ g(x)` into `A`; each value is the point `g x` with
the proof `h x` that it lies in `A`. -/
theorem continuous_into_subspace {A : Set Y} {g : X → Y} (hg : Continuous g)
    (h : ∀ x, g x ∈ A) : Continuous (fun x => (⟨g x, h x⟩ : A)) := by
  -- An open set of `A` is `U ∩ A` for an open `U ⊆ Y` (`def-1-14`; Lean writes `U ∩ A` as the
  -- preimage of `U` under the inclusion `A → Y`). Its preimage under `g` is `g⁻¹(U)`, open since
  -- `g` is continuous. (Lean: `rintro _ ⟨U, hU, rfl⟩` says "let the open set be `U ∩ A`, with
  -- `hU : U open`".)
  rintro _ ⟨U, hU, rfl⟩
  exact hg U hU

/-- Conversely, if `k : X → A` is continuous, then so is `k` seen as a map into `Y`: it is the
composite of `k` with the inclusion `A → Y`, which is continuous (`prop-1-15`).
Mathlib: `Continuous.subtype_val`. -/
theorem continuous_val_comp {A : Set Y} {k : X → A} (hk : Continuous k) :
    Continuous (fun x => (k x : Y)) :=
  continuous_subtype_val.comp hk

end IntoSubspace

/-! ## Pullbacks (`def:pullback`, `prop:pullback-top`) -/

section Pullback
variable [TopSpace X] [TopSpace Y] [TopSpace Z] {W : Type u'} [TopSpace W]

/-- The fibre product `X ×_Z Y = {(x, y) | f(x) = g(y)}` of `f : X → Z` and `g : Y → Z`, a
subspace of the product `X × Y` (`thm:product-top`). `prop:pullback-top`.
Mathlib: `TopCat.pullbackCone` (on `{ p : X × Y // f p.1 = g p.2 }`),
`TopCat.pullbackIsoProdSubtype`. -/
def fibreProduct (f : X → Z) (g : Y → Z) : Set (X × Y) := {z | f z.1 = g z.2}

variable {f : X → Z} {g : Y → Z}

/-- The first projection `p : X ×_Z Y → X`, `(x, y) ↦ x`. `prop:pullback-top`.
Mathlib: `TopCat.pullbackFst`.

Lean: a point `z` of `X ×_Z Y` is a pair `z.1 = (x, y)` with a proof `z.2` that `f(x) = g(y)`;
so `x` is `z.1.1` and `y` is `z.1.2`. -/
def fibreProduct.fst (z : fibreProduct f g) : X := z.1.1

/-- The second projection `q : X ×_Z Y → Y`, `(x, y) ↦ y`. `prop:pullback-top`.
Mathlib: `TopCat.pullbackSnd`. -/
def fibreProduct.snd (z : fibreProduct f g) : Y := z.1.2

/-- `p` is continuous: it is the inclusion `X ×_Z Y → X × Y` followed by the projection
`X × Y → X`, both continuous (`prop-1-15`, `thm:product-top`). `prop:pullback-top`. -/
theorem continuous_fibreProduct_fst : Continuous (fibreProduct.fst : fibreProduct f g → X) :=
  continuous_fst.comp continuous_subtype_val

/-- `q` is continuous, for the same reason. `prop:pullback-top`. -/
theorem continuous_fibreProduct_snd : Continuous (fibreProduct.snd : fibreProduct f g → Y) :=
  continuous_snd.comp continuous_subtype_val

/-- `f ∘ p = g ∘ q` on `X ×_Z Y`. `def:pullback`. Mathlib: `TopCat.pullbackCone`'s `condition`.

Proof: two maps are equal if they agree at every point (`funext`); at `z = (x, y)` this says
`f(x) = g(y)`, which is the proof `z.2` that `z` lies in the fibre product. -/
theorem fibreProduct_comm : f ∘ fibreProduct.fst = g ∘ (fibreProduct.snd : fibreProduct f g → Y) :=
  funext fun z => z.2

/-- Given `a : W → X` and `b : W → Y` with `f(a(w)) = g(b(w))` for every `w` (`h`), the map
`k : W → X ×_Z Y`, `w ↦ (a(w), b(w))`. `prop:pullback-top`.
Mathlib: `CategoryTheory.Limits.pullback.lift` (in `TopCat`). -/
def fibreProduct.lift (a : W → X) (b : W → Y) (h : ∀ w, f (a w) = g (b w)) :
    W → fibreProduct f g :=
  fun w => ⟨(a w, b w), h w⟩

/-- If `a` and `b` are continuous, so is `k = (a, b) : W → X ×_Z Y`. `prop:pullback-top`, existence.

Proof, the book's: a map into the subspace `X ×_Z Y` is continuous if it is continuous into
`X × Y` (`ex:initial-final`, `continuous_into_subspace`), and a map into `X × Y` is continuous if
both its coordinates are (`thm:product-top`, `continuous_prodMk`). -/
theorem continuous_fibreProduct_lift {a : W → X} {b : W → Y} (ha : Continuous a)
    (hb : Continuous b) (h : ∀ w, f (a w) = g (b w)) :
    Continuous (fibreProduct.lift a b h) :=
  continuous_into_subspace (continuous_prodMk.mpr ⟨ha, hb⟩) h

/-- **`prop:pullback-top`**, the universal property: for continuous `a : W → X`, `b : W → Y`
with `f ∘ a = g ∘ b` there is exactly one continuous `k : W → X ×_Z Y` with `p ∘ k = a` and
`q ∘ k = b`. Mathlib: `CategoryTheory.Limits.pullback.hom_ext`,
`TopCat.pullbackIsoProdSubtype`.

Lean: `∃! k, P k` is "there is exactly one `k` with `P k`"; it is proved by giving `k`, a proof
of `P k`, and a proof that every `k'` with `P k'` equals `k`. -/
theorem fibreProduct_universal {a : W → X} {b : W → Y} (ha : Continuous a) (hb : Continuous b)
    (h : f ∘ a = g ∘ b) :
    ∃! k : W → fibreProduct f g,
      Continuous k ∧ fibreProduct.fst ∘ k = a ∧ fibreProduct.snd ∘ k = b := by
  -- Existence: `k(w) = (a(w), b(w))`, which lies in `X ×_Z Y` because `f(a(w)) = g(b(w))`
  -- (Lean: `congrFun h w` evaluates the equality of maps `h` at `w`). It is continuous
  -- (`continuous_fibreProduct_lift`), and `p ∘ k = a`, `q ∘ k = b` hold by definition (`rfl`).
  refine ⟨fibreProduct.lift a b (congrFun h),
    ⟨continuous_fibreProduct_lift ha hb _, rfl, rfl⟩, ?_⟩
  -- Uniqueness, as in `thm:product-top`: let `k'` have `p ∘ k' = a` (`hka`) and `q ∘ k' = b`
  -- (`hkb`); its continuity is not needed (`-` drops it). At every `w` the point `k'(w)` of
  -- `X × Y` has coordinates `a(w)` and `b(w)`, so it is `(a(w), b(w))` (`Prod.ext`), and
  -- equal points of `X × Y` are equal points of the subspace (`Subtype.ext`).
  rintro k' ⟨-, hka, hkb⟩
  funext w
  exact Subtype.ext (Prod.ext (congrFun hka w) (congrFun hkb w))

end Pullback

/-! ## Pushouts (`def:pushout`, `thm:pushout-top`, `def:adjunction`) -/

/-!
### How Lean writes `(X ⊔ Y)/∼`

The smallest example: the circle as `[0, 1]` with its two ends glued to one point. Take `X = {∗}`
a point, `Y = [0, 1]`, `A = {0, 1}`, `f : A → X` the constant map and `g : A → Y` the inclusion.
The book's pushout is `X ⊔_A Y = (X ⊔ Y)/∼`, where `∼` is the smallest equivalence relation with
`f(a) ∼ g(a)`, that is `∗ ∼ 0` and `∗ ∼ 1`. It contains `0 ∼ 1` too (`0 ∼ ∗` by symmetry, then
`∗ ∼ 1`, by transitivity), so its classes are `{∗, 0, 1}` and the single points `{t}` for
`0 < t < 1`: a circle. (`Week02Graphs.lean` builds this as `circleGraph`.) In Lean, step by step:

* `X ⊕ Y` is the disjoint union `X ⊔ Y` (`prop:coproduct-top`). Its points are `Sum.inl x` for
  `x ∈ X` and `Sum.inr y` for `y ∈ Y` (the book's `ι₁ x`, `ι₂ y`). Here: `Sum.inl ∗` and
  `Sum.inr t` for `t ∈ [0, 1]`.
* `pushoutRel f g u v` says "`u = ι₁ f(a)` and `v = ι₂ g(a)` for some `a ∈ A`": only the pairs
  we asked for, here `(ι₁ ∗, ι₂ 0)` and `(ι₁ ∗, ι₂ 1)`. It is not an equivalence relation.
* `Relation.EqvGen r` is the smallest equivalence relation containing `r`: `u ∼ v` when one gets
  from `u` to `v` by a finite chain of steps, each a pair of `r` or its reverse. Here
  `ι₂ 0 ∼ ι₁ ∗ ∼ ι₂ 1`. Lean records how `u ∼ v` was obtained: from a pair of `r`
  (`EqvGen.rel`), as `u ∼ u` (`refl`), by symmetry (`symm`) or by transitivity (`trans`).
* A `Setoid T` is a set `T` with an equivalence relation, and `Quotient s` is the set `T/∼` of
  its classes; `pushoutSetoid f g` is `X ⊔ Y` with `EqvGen (pushoutRel f g)`, and `Pushout f g`
  is `(X ⊔ Y)/∼` with the quotient topology (`def:quotient`).
* `Quotient.mk _ u` is the class `[u]`, and the map `q : u ↦ [u]` is the quotient map.
  `Quotient.sound` says that `u ∼ v` implies `[u] = [v]`. `Quotient.lift g h` is the map
  `ḡ : [u] ↦ g(u)` out of `T/∼`, which needs the proof `h` that `g` is constant on classes
  (`prop:quotient-univ`). `Quotient.ind` says that every element of `T/∼` is a class `[u]`.
-/

section Pushout
variable {A : Type u'} [TopSpace A] [TopSpace X] [TopSpace Y] [TopSpace Z]

/-- The generating pairs: `u` and `v` in `X ⊔ Y` are related if `u = ι₁ f(a)` and `v = ι₂ g(a)` for
some `a ∈ A`. `thm:pushout-top`, before closing up to an equivalence relation. -/
def pushoutRel (f : A → X) (g : A → Y) (u v : X ⊕ Y) : Prop :=
  ∃ a, u = Sum.inl (f a) ∧ v = Sum.inr (g a)

/-- The smallest equivalence relation `∼` on `X ⊔ Y` with `f(a) ∼ g(a)` for every `a ∈ A`.
`thm:pushout-top`. Mathlib: `Relation.EqvGen.setoid`. -/
def pushoutSetoid (f : A → X) (g : A → Y) : Setoid (X ⊕ Y) :=
  Relation.EqvGen.setoid (pushoutRel f g)

/-- The pushout `X ⊔_A Y = (X ⊔ Y)/∼`: the disjoint union (`prop:coproduct-top`) divided by `∼`,
with the quotient topology (`def:quotient`). `thm:pushout-top`.
Mathlib: `CategoryTheory.Limits.pushout` in
`TopCat` (an abstract colimit; Mathlib has no explicit construction of it). -/
abbrev Pushout (f : A → X) (g : A → Y) : Type _ := Quotient (pushoutSetoid f g)

variable {f : A → X} {g : A → Y}

/-- The map `i : X → X ⊔_A Y`, `x ↦ [ι₁ x]`: the first inclusion followed by the quotient map.
`thm:pushout-top`. Mathlib: `CategoryTheory.Limits.pushout.inl`. -/
def Pushout.inl (x : X) : Pushout f g := Quotient.mk _ (Sum.inl x)

/-- The map `j : Y → X ⊔_A Y`, `y ↦ [ι₂ y]`. `thm:pushout-top`.
Mathlib: `CategoryTheory.Limits.pushout.inr`. -/
def Pushout.inr (y : Y) : Pushout f g := Quotient.mk _ (Sum.inr y)

/-- `i` is continuous: the composite of the inclusion `ι₁` (`prop:coproduct-top`) and the quotient
map `q` (`prop:quotient-univ`), both continuous. `thm:pushout-top`. -/
theorem continuous_pushout_inl : Continuous (Pushout.inl : X → Pushout f g) :=
  continuous_quotient_mk.comp continuous_inl

/-- `j` is continuous, for the same reason. `thm:pushout-top`. -/
theorem continuous_pushout_inr : Continuous (Pushout.inr : Y → Pushout f g) :=
  continuous_quotient_mk.comp continuous_inr

/-- `i ∘ f = j ∘ g`. `thm:pushout-top`. Mathlib: `CategoryTheory.Limits.pushout.condition`.

Proof: at every `a ∈ A`, `[ι₁ f(a)] = [ι₂ g(a)]` because `(ι₁ f(a), ι₂ g(a))` is a generating
pair (`EqvGen.rel`, with `a` as the witness) and related points have equal classes
(`Quotient.sound`). -/
theorem pushout_comm : Pushout.inl ∘ f = (Pushout.inr ∘ g : A → Pushout f g) :=
  funext fun a => Quotient.sound (Relation.EqvGen.rel _ _ ⟨a, rfl, rfl⟩)

/-- If `u : X → Z` and `v : Y → Z` have `u(f(a)) = v(g(a))` for every `a` (`h`), then the map
`(u, v) : X ⊔ Y → Z` (`Sum.elim u v`: `u` on `X`, `v` on `Y`) is constant on the classes of `∼`:
`s ∼ t` implies `(u, v)(s) = (u, v)(t)`. `thm:pushout-top` ("constant on the classes precisely
because `uf = vg`").

Proof: the pairs `(s, t)` with `(u, v)(s) = (u, v)(t)` form an equivalence relation that contains
the generating pairs, so it contains the smallest one, `∼`. In Lean this is an induction on how
`s ∼ t` was obtained (`induction hst`), one case for each way. -/
theorem pushout_elim_resp {u : X → Z} {v : Y → Z} (h : ∀ a, u (f a) = v (g a)) (s t : X ⊕ Y)
    (hst : Relation.EqvGen (pushoutRel f g) s t) : Sum.elim u v s = Sum.elim u v t := by
  induction hst with
  -- A generating pair: `s = ι₁ f(a)`, `t = ι₂ g(a)`, and `u(f(a)) = v(g(a))` is `h a`.
  | rel s t hst =>
    obtain ⟨a, rfl, rfl⟩ := hst
    exact h a
  -- `s ∼ s`: both sides are `(u, v)(s)`.
  | refl => rfl
  -- `t ∼ s` from `s ∼ t`: the equation `ih` read backwards.
  | symm _ _ _ ih => exact ih.symm
  -- `s ∼ t'` from `s ∼ t` and `t ∼ t'`: two equations chained.
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- The map `k : X ⊔_A Y → Z`, `[s] ↦ (u, v)(s)`, for `u : X → Z`, `v : Y → Z` with
`u(f(a)) = v(g(a))` for every `a` (`h`). It is well defined by `pushout_elim_resp`.
`thm:pushout-top`. Mathlib: `CategoryTheory.Limits.pushout.desc`. -/
def Pushout.desc (u : X → Z) (v : Y → Z) (h : ∀ a, u (f a) = v (g a)) : Pushout f g → Z :=
  Quotient.lift (Sum.elim u v) fun s t hst => pushout_elim_resp h s t hst

/-- If `u` and `v` are continuous, so is `k : X ⊔_A Y → Z`. `thm:pushout-top`, existence.

Proof, the book's: `(u, v)` is continuous on `X ⊔ Y` because `u` and `v` are
(`prop:coproduct-top`, `continuous_sum_elim`), and a continuous map constant on the classes
induces a continuous map on the quotient (`prop:quotient-univ`, `continuous_quotient_lift`). -/
theorem continuous_pushout_desc {u : X → Z} {v : Y → Z} (hu : Continuous u) (hv : Continuous v)
    (h : ∀ a, u (f a) = v (g a)) : Continuous (Pushout.desc u v h : Pushout f g → Z) :=
  continuous_quotient_lift (continuous_sum_elim.mpr ⟨hu, hv⟩) _

/-- **`thm:pushout-top`**, the universal property: for continuous `u : X → Z`, `v : Y → Z` with
`u ∘ f = v ∘ g` there is exactly one continuous `k : X ⊔_A Y → Z` with `k ∘ i = u` and
`k ∘ j = v`. Mathlib: `CategoryTheory.Limits.pushout.hom_ext`. -/
theorem pushout_universal {u : X → Z} {v : Y → Z} (hu : Continuous u) (hv : Continuous v)
    (h : u ∘ f = v ∘ g) :
    ∃! k : Pushout f g → Z, Continuous k ∧ k ∘ Pushout.inl = u ∧ k ∘ Pushout.inr = v := by
  -- Existence: `k = Pushout.desc u v`, continuous (`continuous_pushout_desc`), and
  -- `k(i(x)) = u(x)`, `k(j(y)) = v(y)` by definition (`rfl`).
  refine ⟨Pushout.desc u v (congrFun h), ⟨continuous_pushout_desc hu hv _, rfl, rfl⟩, ?_⟩
  -- Uniqueness: let `k'` have `k' ∘ i = u` (`hku`) and `k' ∘ j = v` (`hkv`). By
  -- `prop:quotient-univ` (`quotient_lift_unique`) it is enough that `k' ∘ q = (u, v)` on `X ⊔ Y`.
  rintro k' ⟨-, hku, hkv⟩
  apply quotient_lift_unique
  funext s
  -- A point `s` of `X ⊔ Y` is `ι₁ x` or `ι₂ y` (`cases s`); there `k'(q(s))` is `k'(i(x)) = u(x)`,
  -- or `k'(j(y)) = v(y)`.
  cases s with
  | inl x => exact congrFun hku x
  | inr y => exact congrFun hkv y

/-- The adjunction space `X ∪_φ Y` for `B ⊆ Y` and `φ : B → X`: the pushout of `X ← B ↪ Y`,
that is `X` with `Y` glued to it along `φ`. `def:adjunction`. As `rem:adjunction-embedding` says,
nothing asks `B` to be closed for it to exist; the construction does not even ask `φ` to be
continuous. Mathlib: none (`TopCat` pushouts).

Lean: `Subtype.val : B → Y` is the inclusion of `B` in `Y`, which forgets that a point lies in
`B`. -/
abbrev AdjunctionSpace {B : Set Y} (φ : B → X) : Type _ := Pushout φ (Subtype.val : B → Y)

/-- In `X ∪_φ Y` each `b ∈ B` is glued to `φ(b)`: `i(φ(b)) = j(b)`. `def:adjunction`; it is
`pushout_comm` at `b`. -/
theorem adjunctionSpace_glue {B : Set Y} (φ : B → X) (b : B) :
    (Pushout.inl (φ b) : AdjunctionSpace φ) = Pushout.inr (b : Y) :=
  congrFun pushout_comm b

end Pushout

/-! ## Connectedness and cut points (`def:cut-point`) -/

section Connected

-- (Lean: `variable (X) in` makes `X` an explicit argument of the next definition, so that one
-- writes `Connected X`.)
variable (X) in
/-- Connectedness, as Analysis I defines it: `X` is not the union of two disjoint non-empty open
sets; that is, if `X = U ∪ V` with `U`, `V` open and disjoint, one of them is empty. (The empty
space is connected.) Mathlib: `PreconnectedSpace` (see `connected_iff_preconnectedSpace`);
Mathlib's `ConnectedSpace` asks also for a point. (`univ` is the whole space `X`, and
`Disjoint U V` says `U ∩ V = ∅`.) -/
def Connected [TopSpace X] : Prop :=
  ∀ U V : Set X, IsOpen U → IsOpen V → U ∪ V = univ → Disjoint U V → U = ∅ ∨ V = ∅

/-- **Bridge.** The course's connectedness is Mathlib's `PreconnectedSpace` for the course
topology. Mathlib: `PreconnectedSpace`, `IsPreconnected`. -/
theorem connected_iff_preconnectedSpace [t : TopSpace X] :
    Connected X ↔ @PreconnectedSpace X t.toMathlib := by
  -- Mathlib's definition says: if `X ⊆ U ∪ V` with `U`, `V` open and both meeting `X`, then
  -- `U ∩ V` meets `X`. It is the same statement turned around. (Lean: `let _ := t.toMathlib`
  -- gives `X` Mathlib's version of the course's topology, so that Mathlib's notions apply.)
  let _ := t.toMathlib
  constructor
  -- (→) Let `U`, `V` be open, cover `X`, and both be non-empty (`hU'`, `hV'`). Suppose
  -- `U ∩ V = ∅`. Then `U`, `V` split `X`, so one of them is empty, a contradiction. (Lean:
  -- `by_contra hne` assumes the negation of the goal, calls it `hne`, and seeks a contradiction.)
  · intro h
    refine ⟨fun U V hU hV hUV hU' hV' => ?_⟩
    by_contra hne
    rw [univ_inter, not_nonempty_iff_eq_empty] at hne
    rcases h U V hU hV (eq_univ_of_univ_subset hUV) (disjoint_iff_inter_eq_empty.mpr hne) with
      h' | h'
    · rw [univ_inter, h'] at hU'; exact not_nonempty_empty hU'
    · rw [univ_inter, h'] at hV'; exact not_nonempty_empty hV'
  -- (←) Let `X = U ∪ V` with `U`, `V` open and disjoint, and suppose neither is empty. Then by
  -- Mathlib's definition `U ∩ V` has a point `x`, against `U ∩ V = ∅`.
  · intro h U V hU hV hUV hdisj
    by_contra hne
    rw [not_or, ← ne_eq, ← ne_eq, ← nonempty_iff_ne_empty, ← nonempty_iff_ne_empty] at hne
    obtain ⟨x, -, hx⟩ := h.isPreconnected_univ U V hU hV hUV.symm.subset
      (by rw [univ_inter]; exact hne.1) (by rw [univ_inter]; exact hne.2)
    exact hdisj.le_bot hx

/-- If `X` is connected and `φ : X → Y` is continuous and onto, then `Y` is connected
(Analysis I). Mathlib: `PreconnectedSpace` via `IsPreconnected.image`. -/
theorem Connected.of_surjective [TopSpace X] [TopSpace Y] (hX : Connected X) {φ : X → Y}
    (hφ : Continuous φ) (hs : Function.Surjective φ) : Connected Y := by
  -- Step 1. Since `φ` is onto, `φ⁻¹(W) = ∅` implies `W = ∅`: a point `y ∈ W` is `φ(x)` for some
  -- `x`, and then `x ∈ φ⁻¹(W)`.
  have key : ∀ W : Set Y, φ ⁻¹' W = ∅ → W = ∅ := fun W hW =>
    eq_empty_iff_forall_notMem.mpr fun y hy => by
      obtain ⟨x, rfl⟩ := hs y
      exact eq_empty_iff_forall_notMem.mp hW x hy
  -- Step 2. Let `Y = U ∪ V` with `U`, `V` open and disjoint. Then `φ⁻¹(U)`, `φ⁻¹(V)` are open
  -- (`φ` is continuous), disjoint, and cover `X`; since `X` is connected, one of them is empty,
  -- and by Step 1 so is `U` or `V`.
  intro U V hU hV hUV hdisj
  rcases hX _ _ (hφ U hU) (hφ V hV) (by rw [← preimage_union, hUV, preimage_univ])
    (hdisj.preimage φ) with h | h
  · exact Or.inl (key U h)
  · exact Or.inr (key V h)

/-- Connectedness is a topological property: if `X ≅ Y` and `X` is connected, so is `Y`.
`def-1-27`. Mathlib: `Homeomorph.connectedSpace_iff`.

Proof: a homeomorphism `h` is continuous and onto, so `Connected.of_surjective` applies.
(Lean: `h.toEquiv` is the bijection underlying `h`, and `h.continuous_toFun` the proof that it is
continuous.) -/
theorem isTopologicalProperty_connected :
    IsTopologicalProperty.{u} fun X _ => Connected X :=
  fun _ _ _ _ h hX => hX.of_surjective h.continuous_toFun h.toEquiv.surjective

/-- `x` is a cut point of `X` if `X` is connected and `X ∖ {x}` is not. `def:cut-point`.
Mathlib: none.

Lean: `{x}ᶜ` is the complement `X ∖ {x}`, a subspace of `X`. -/
def IsCutPoint [TopSpace X] (x : X) : Prop :=
  Connected X ∧ ¬ Connected ({x}ᶜ : Set X)

/-- The inverse `h⁻¹ : Y → X` of a homeomorphism `h : X → Y` is a homeomorphism: the inverse
bijection (`h.toEquiv.symm`), continuous because `h` has a continuous inverse.
Mathlib: `Homeomorph.symm`. -/
def Homeomorph.inv [TopSpace X] [TopSpace Y] (h : Homeomorph X Y) : Homeomorph Y X where
  toEquiv := h.toEquiv.symm
  continuous_toFun := h.continuous_invFun
  continuous_invFun := h.continuous_toFun

/-- If `h : X → Y` is a homeomorphism and `X ∖ {x}` is connected, then `Y ∖ {h(x)}` is
connected. This is the book's "a homeomorphism restricts to `X ∖ {x} → Y ∖ {h(x)}`", in the part
the cut-point arguments use. -/
theorem Homeomorph.connected_compl [TopSpace X] [TopSpace Y] (h : Homeomorph X Y) (x : X)
    (hx : Connected ({x}ᶜ : Set X)) : Connected ({h.toEquiv x}ᶜ : Set Y) := by
  -- Step 1. `h` sends `X ∖ {x}` into `Y ∖ {h(x)}`: if `h(z) = h(x)` then `z = x`, as `h` is
  -- injective. The restriction `z ↦ h(z)` is continuous (`continuous_into_subspace`), so by
  -- `Connected.of_surjective` it remains to see that it is onto.
  refine hx.of_surjective (φ := fun z => ⟨h.toEquiv z.1, fun hz => z.2 (h.toEquiv.injective hz)⟩)
    (continuous_into_subspace (h.continuous_toFun.comp continuous_subtype_val) _) ?_
  -- Step 2. Onto: for `y ≠ h(x)`, the point `h⁻¹(y)` is not `x` (otherwise
  -- `y = h(h⁻¹(y)) = h(x)`), and `h(h⁻¹(y)) = y`.
  rintro ⟨y, hy⟩
  refine ⟨⟨h.toEquiv.symm y, fun hy' => hy ?_⟩, Subtype.ext (h.toEquiv.apply_symm_apply y)⟩
  rw [← hy', h.toEquiv.apply_symm_apply]
  rfl

/-- If `h : X → Y` is a homeomorphism, then `h(x)` is a cut point of `Y` if and only if `x` is
a cut point of `X`: a homeomorphism carries cut points to cut points, and non-cut points to
non-cut points. `def:cut-point`, as used in `thm:one-dimensional` and `prop:line-not-plane`. -/
theorem Homeomorph.isCutPoint_iff [TopSpace X] [TopSpace Y] (h : Homeomorph X Y) (x : X) :
    IsCutPoint (h.toEquiv x) ↔ IsCutPoint x := by
  constructor
  -- (→) `X = h⁻¹(Y)` is connected (`Connected.of_surjective` for `h⁻¹`). If `X ∖ {x}` were
  -- connected, so would be `Y ∖ {h(x)}` (`connected_compl`), against `h(x)` being a cut point.
  · rintro ⟨hY, hYx⟩
    refine ⟨hY.of_surjective h.continuous_invFun h.toEquiv.symm.surjective, fun hx => hYx ?_⟩
    exact h.connected_compl x hx
  -- (←) The same with `h` and `h⁻¹` exchanged: `Y = h(X)` is connected, and if `Y ∖ {h(x)}`
  -- were connected, so would be `X ∖ {h⁻¹(h(x))} = X ∖ {x}`.
  · rintro ⟨hX, hXx⟩
    refine ⟨hX.of_surjective h.continuous_toFun h.toEquiv.surjective, fun hx => hXx ?_⟩
    have := h.inv.connected_compl (h.toEquiv x) hx
    have e : h.inv.toEquiv (h.toEquiv x) = x := h.toEquiv.symm_apply_apply x
    rwa [e] at this

end Connected

/-! ## Paths and connectedness (Analysis I §8, for `thm:one-dimensional`, `prop:line-not-plane`)

The book cites "path-connected implies connected" from Analysis I §8. It is proved here from
the connectedness of `[0, 1]`, which is the Analysis I input (Mathlib: `unitInterval`'s
`ConnectedSpace` instance, through the bridge `I_toMathlib`). -/

section Paths

/-- If the course topologies on `X` and `Y` are Mathlib's topologies `mX`, `mY` (`hX`, `hY`), then
a map continuous for `mX`, `mY` is continuous in the course's sense. The bridge through which the
continuity of real formulas (Analysis I) enters. -/
private theorem cont_of_mathlib [tX : TopSpace X] [tY : TopSpace Y]
    {mX : TopologicalSpace X} {mY : TopologicalSpace Y} (hX : tX.toMathlib = mX)
    (hY : tY.toMathlib = mY) {f : X → Y} (hf : @_root_.Continuous X Y mX mY f) :
    Continuous f := by
  subst hX hY; exact (continuous_iff_mathlib f).mpr hf

/-- `[0, 1]` is connected (Analysis I). From Mathlib (`unitInterval`'s `ConnectedSpace`, through
the intermediate value theorem) via the bridges `connected_iff_preconnectedSpace` and
`I_toMathlib`. -/
theorem connected_I : Connected I := by
  -- Translate to Mathlib's notion and topology; there it is a known fact (`infer_instance`
  -- finds it).
  rw [connected_iff_preconnectedSpace, I_toMathlib]
  infer_instance

/-- The end point `0 ∈ I = [0, 1]`. (`left_mem_Icc.mpr zero_le_one` proves `0 ∈ [0, 1]`.) -/
def I.zero : I := ⟨0, left_mem_Icc.mpr zero_le_one⟩
/-- The end point `1 ∈ I = [0, 1]`. -/
def I.one : I := ⟨1, right_mem_Icc.mpr zero_le_one⟩

/-- `x` and `y` are joined by a path: a continuous `γ : [0, 1] → X` with `γ 0 = x`, `γ 1 = y`
(Analysis I §8). Mathlib: `Joined`. -/
def Joined [TopSpace X] (x y : X) : Prop :=
  ∃ γ : I → X, Continuous γ ∧ γ I.zero = x ∧ γ I.one = y

/-- If `X = U ∪ V` with `U`, `V` open and disjoint, and `x`, `y` are joined by a path, then
`x ∈ U` implies `y ∈ U`. -/
theorem Joined.mem_of_mem [TopSpace X] {U V : Set X} (hU : IsOpen U) (hV : IsOpen V)
    (hUV : U ∪ V = univ) (hdisj : Disjoint U V) {x y : X} (hxy : Joined x y) (hx : x ∈ U) :
    y ∈ U := by
  -- Let `γ` be the path, `γ(0) = x`, `γ(1) = y` (`rfl` replaces `x`, `y` by `γ(0)`, `γ(1)`).
  obtain ⟨γ, hγ, rfl, rfl⟩ := hxy
  -- `γ⁻¹(U)` and `γ⁻¹(V)` are open (`γ` is continuous), disjoint, and cover `[0, 1]`; since
  -- `[0, 1]` is connected (`connected_I`), one of them is empty.
  have hcov : γ ⁻¹' U ∪ γ ⁻¹' V = univ := by rw [← preimage_union, hUV, preimage_univ]
  rcases connected_I _ _ (hγ U hU) (hγ V hV) hcov (hdisj.preimage γ) with h | h
  -- `γ⁻¹(U) = ∅` is impossible: it contains `0`, as `γ(0) = x ∈ U`. (Lean: `absurd hp hnp`
  -- concludes anything from a statement `hp` and its negation `hnp`.)
  · exact absurd (show I.zero ∈ γ ⁻¹' U from hx) (by rw [h]; exact notMem_empty _)
  -- So `γ⁻¹(V) = ∅`. Now `γ(1)` lies in `U ∪ V`, and not in `V`; so it lies in `U`.
  · have : γ I.one ∈ U ∪ V := by rw [hUV]; trivial
    rcases this with h1 | h1
    · exact h1
    · exact absurd (show I.one ∈ γ ⁻¹' V from h1) (by rw [h]; exact notMem_empty _)

/-- If `X = U ∪ V` with `U`, `V` open and disjoint, the two ends of a path are on the same side:
`x ∈ U ↔ y ∈ U`. -/
theorem Joined.mem_iff [TopSpace X] {U V : Set X} (hU : IsOpen U) (hV : IsOpen V)
    (hUV : U ∪ V = univ) (hdisj : Disjoint U V) {x y : X} (hxy : Joined x y) :
    x ∈ U ↔ y ∈ U := by
  -- (→) is `mem_of_mem`. (←) Let `y ∈ U` and suppose `x ∉ U`. Then `x ∈ V`, so `y ∈ V` by
  -- `mem_of_mem` with `U` and `V` exchanged, and `y ∈ U ∩ V = ∅`.
  refine ⟨hxy.mem_of_mem hU hV hUV hdisj, fun hy => ?_⟩
  by_contra hx
  have hxV : x ∈ V := by
    have : x ∈ U ∪ V := by rw [hUV]; trivial
    exact this.resolve_left hx
  have hyV := hxy.mem_of_mem hV hU (by rw [union_comm, hUV]) hdisj.symm hxV
  exact hdisj.le_bot ⟨hy, hyV⟩

/-- A space in which every two points are joined by a path is connected (Analysis I §8).
Mathlib: `PathConnectedSpace.connectedSpace`. -/
theorem connected_of_joined [TopSpace X] (h : ∀ x y : X, Joined x y) : Connected X := by
  -- Let `X = U ∪ V` with `U`, `V` open and disjoint, and suppose both are non-empty: `x ∈ U`,
  -- `y ∈ V`. The path from `x` to `y` ends in `U` (`mem_of_mem`), so `y ∈ U ∩ V = ∅`.
  intro U V hU hV hUV hdisj
  by_contra hne
  rw [not_or, ← ne_eq, ← ne_eq, ← nonempty_iff_ne_empty, ← nonempty_iff_ne_empty] at hne
  obtain ⟨⟨x, hx⟩, ⟨y, hy⟩⟩ := hne
  exact hdisj.le_bot ⟨(h x y).mem_of_mem hU hV hUV hdisj hx, hy⟩

/-- The segment `t ↦ (1 - t) a + t b`, `[0, 1] → ℝ`, is continuous (Analysis I, through the
bridges `I_toMathlib`, `real_toMathlib`; `fun_prop` checks the formula). Lean: `(t : ℝ)` is the
point `t ∈ I` seen as a real number. -/
theorem continuous_segment (a b : ℝ) : Continuous (fun t : I => (1 - (t : ℝ)) * a + (t : ℝ) * b) :=
  cont_of_mathlib I_toMathlib real_toMathlib (by fun_prop)

/-- A point `(1 - t) a + t b` with `t ∈ [0, 1]` lies between `min(a, b)` and `max(a, b)`. -/
theorem segment_bounds (a b : ℝ) (t : I) :
    min a b ≤ (1 - (t : ℝ)) * a + (t : ℝ) * b ∧ (1 - (t : ℝ)) * a + (t : ℝ) * b ≤ max a b := by
  -- `t ∈ I` is a real number `t` with `0 ≤ t` and `t ≤ 1`. The weights `1 - t` and `t` are
  -- `≥ 0` and add up to `1`, so `(1 - t) a + t b ≥ (1 - t) min + t min = min`, and likewise
  -- `≤ max`; `nlinarith` does this algebra.
  obtain ⟨t, ht0, ht1⟩ := t
  have h1 : 0 ≤ 1 - t := by linarith
  constructor
  · nlinarith [mul_le_mul_of_nonneg_left (min_le_left a b) h1,
      mul_le_mul_of_nonneg_left (min_le_right a b) ht0]
  · nlinarith [mul_le_mul_of_nonneg_left (le_max_left a b) h1,
      mul_le_mul_of_nonneg_left (le_max_right a b) ht0]

/-- Two points `a`, `b` of `S ⊆ ℝ` whose segment stays in `S` (`h`) are joined in `S`. -/
theorem joined_of_segment {S : Set ℝ} (a b : S)
    (h : ∀ t : I, (1 - (t : ℝ)) * a + (t : ℝ) * b ∈ S) : Joined a b := by
  -- The path is `γ(t) = (1 - t) a + t b`, continuous into `S` (`continuous_segment`,
  -- `continuous_into_subspace`); `γ(0) = a` and `γ(1) = b` by computation.
  refine ⟨fun t => ⟨_, h t⟩, continuous_into_subspace (continuous_segment a b) h, ?_, ?_⟩ <;>
    apply Subtype.ext <;> simp [I.zero, I.one]

/-- Two points `a`, `b` of `S ∖ {x}`, `S ⊆ ℝ`, whose segment stays in `S` and misses `x` (`h`),
are joined in `S ∖ {x}`.

Lean: `S ∖ {x}` is a subspace of the subspace `S`. So a point `a` of it is a point `a.1 ∈ S`
with the proof `a.2` that `a.1 ≠ x`, and `a.1` is in turn a real number with a proof that it
lies in `S`; that is why `Subtype.ext` appears twice below. -/
theorem joined_of_segment_compl {S : Set ℝ} {x : S} (a b : ({x}ᶜ : Set S))
    (h : ∀ t : I, (1 - (t : ℝ)) * a.1 + (t : ℝ) * b.1 ∈ S ∧
      (1 - (t : ℝ)) * a.1 + (t : ℝ) * b.1 ≠ x) : Joined a b := by
  -- The same path `γ(t) = (1 - t) a + t b` as in `joined_of_segment`, now with values in
  -- `S ∖ {x}`; continuous by `continuous_into_subspace` twice.
  refine ⟨fun t => ⟨⟨_, (h t).1⟩, fun he => (h t).2 (congrArg Subtype.val he)⟩,
    continuous_into_subspace (continuous_into_subspace (continuous_segment a.1 b.1) _) _,
    Subtype.ext (Subtype.ext (by simp [I.zero])), Subtype.ext (Subtype.ext (by simp [I.one]))⟩

/-- `ℝ` is connected (Analysis I): any two points are joined by the segment between them. -/
theorem connected_real : Connected ℝ :=
  connected_of_joined fun a b =>
    ⟨_, continuous_segment a b, by simp [I.zero], by simp [I.one]⟩

/-- If `e : X → ℝ` is continuous, never takes the value `c` (`hc`), and takes a value below `c`
(at `a`) and one above it (at `b`), then `X` is not connected (Analysis I).

Proof: `e⁻¹(-∞, c)` and `e⁻¹(c, ∞)` split `X`. The half-lines are open (Analysis I; Mathlib's
`isOpen_Iio`, `isOpen_Ioi`, through `isOpen_real_iff`). Lean: `Iio c` is `(-∞, c)` and `Ioi c`
is `(c, ∞)`. -/
theorem not_connected_of_real [TopSpace X] {e : X → ℝ} (he : Continuous e) {c : ℝ}
    (hc : ∀ w, e w ≠ c) {a b : X} (ha : e a < c) (hb : c < e b) : ¬ Connected X := by
  -- Suppose `X` is connected (`hX`). The half-lines are open, so their preimages are.
  intro hX
  have hU : IsOpen (Iio c) := (isOpen_real_iff _).mpr isOpen_Iio
  have hV : IsOpen (Ioi c) := (isOpen_real_iff _).mpr isOpen_Ioi
  -- They cover `X`, since `e(w) ≠ c` means `e(w) < c` or `e(w) > c` …
  have hcov : e ⁻¹' Iio c ∪ e ⁻¹' Ioi c = univ := by
    ext w
    simp only [mem_union, mem_preimage, mem_Iio, mem_Ioi, mem_univ, iff_true]
    exact lt_or_gt_of_ne (hc w)
  -- … and are disjoint, since `e(w) < c < e(w)` is impossible.
  have hdisj : Disjoint (e ⁻¹' Iio c) (e ⁻¹' Ioi c) :=
    disjoint_left.mpr fun w (h1 : e w < c) (h2 : c < e w) => lt_asymm h1 h2
  -- So one of them is empty; but the first contains `a` and the second `b`.
  rcases hX _ _ (he _ hU) (he _ hV) hcov hdisj with h | h
  · exact (eq_empty_iff_forall_notMem.mp h) a ha
  · exact (eq_empty_iff_forall_notMem.mp h) b hb

/-- Every point `x` of `ℝ` is a cut point. `thm:one-dimensional`, `prop:line-not-plane`.

Proof: `ℝ` is connected (`connected_real`), and `ℝ ∖ {x}` is not: apply `not_connected_of_real`
to the inclusion `e : ℝ ∖ {x} → ℝ` and `c = x`, with `x - 1` below `x` and `x + 1` above it.
(Lean: `(e := …)` names an argument that is otherwise implicit.) -/
theorem isCutPoint_real (x : ℝ) : IsCutPoint x :=
  ⟨connected_real, not_connected_of_real (e := fun w : ({x}ᶜ : Set ℝ) => (w : ℝ))
    continuous_subtype_val (fun w => w.2) (a := ⟨x - 1, by simp⟩) (b := ⟨x + 1, by simp⟩)
    (by simp) (by simp)⟩

end Paths

/-! ## The line is not the plane (`prop:line-not-plane`, `n = 2`) -/

section LineNotPlane

/-- Two points `x`, `y` of `ℝ² ∖ {p}` whose segment misses `p` (`h`) are joined in `ℝ² ∖ {p}`.
The path is `t ↦ (1 - t) x + t y`, continuous by `thm:product-top`, its two coordinates being
segments in `ℝ`. -/
theorem joined_plane_compl {p : ℝ × ℝ} (x y : ({p}ᶜ : Set (ℝ × ℝ)))
    (h : ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      ((1 - t) * x.1.1 + t * y.1.1, (1 - t) * x.1.2 + t * y.1.2) ≠ p) : Joined x y :=
  ⟨fun t => ⟨_, h t t.2.1 t.2.2⟩,
    continuous_into_subspace (continuous_prodMk.mpr
      ⟨continuous_segment x.1.1 y.1.1, continuous_segment x.1.2 y.1.2⟩) _,
    Subtype.ext (by simp [I.zero]), Subtype.ext (by simp [I.one])⟩

/-- For every `p ∈ ℝ²`, `ℝ² ∖ {p}` is connected: no point of `ℝ²` is a cut point.
`prop:line-not-plane` for `n = 2`.

The book's segments argument, with two fixed points `b = p + (0, 1)` and `c = p + (1, 0)` in
place of "a third point off the line": the segment `[b, c]` misses `p`; and for `x ≠ p` the
segment `[x, b]` misses `p` unless `x` lies on the vertical ray below `p`, and then `[x, c]`
misses it. So every point is joined to `b`, directly or through `c`, and a splitting of
`ℝ² ∖ {p}` would put all of it on `b`'s side. -/
theorem connected_plane_compl (p : ℝ × ℝ) : Connected ({p}ᶜ : Set (ℝ × ℝ)) := by
  -- A point with the coordinates of `p` is `p`.
  have hne : ∀ q : ℝ × ℝ, q.1 = p.1 → q.2 = p.2 → q = p := fun q h1 h2 => Prod.ext h1 h2
  -- The two fixed points `b = (p₁, p₂ + 1)` and `c = (p₁ + 1, p₂)`; neither is `p`, by the
  -- second and the first coordinate.
  let b : ({p}ᶜ : Set (ℝ × ℝ)) := ⟨(p.1, p.2 + 1), fun h => by
    have := congrArg Prod.snd h; simp at this⟩
  let c : ({p}ᶜ : Set (ℝ × ℝ)) := ⟨(p.1 + 1, p.2), fun h => by
    have := congrArg Prod.fst h; simp at this⟩
  -- Step 1. `[c, b]` misses `p`: its point at `t` is `(p₁ + 1 - t, p₂ + t)`, and equal to `p`
  -- it would need `t = 1` (first coordinate) and `t = 0` (second).
  have hcb : Joined c b := joined_plane_compl c b fun t _ _ he => by
    have h1 := congrArg Prod.fst he
    have h2 := congrArg Prod.snd he
    simp only [b, c] at h1 h2
    have : t = 1 := by linear_combination -h1
    have : t = 0 := by linear_combination h2
    linarith
  -- Step 2. Every `x ≠ p` is joined to `b` or to `c`. (`x.1` is `x` as a point of the plane,
  -- with coordinates `x.1.1`, `x.1.2`. Lean: `left` and `right` choose which side of an "or" to
  -- prove.)
  have hx : ∀ x : ({p}ᶜ : Set (ℝ × ℝ)), Joined x b ∨ Joined x c := by
    intro x
    have hxp : x.1 ≠ p := x.2
    by_cases hray : x.1.1 = p.1 ∧ x.1.2 < p.2
    -- Case 1: `x` lies on the vertical ray below `p` (`x₁ = p₁`, `x₂ < p₂`). Then `[x, c]`
    -- misses `p`: its point at `t` is `(p₁ + t, (1 - t) x₂ + t p₂)`; equal to `p`, it would need
    -- `t = 0`, and then its second coordinate `x₂` would be `p₂`, against `x₂ < p₂`.
    · right
      refine joined_plane_compl x c fun t _ _ he => ?_
      have h1 := congrArg Prod.fst he
      have h2 := congrArg Prod.snd he
      simp only [c] at h1 h2
      rw [hray.1] at h1
      have ht : t = 0 := by linear_combination h1
      rw [ht] at h2
      linarith [hray.2]
    -- Case 2: otherwise `[x, b]` misses `p`. Suppose its point at `t` is `p`:
    -- `(1 - t)(x₁ - p₁) = 0` and `(1 - t)(x₂ - p₂) + t = 0` (`e1`, `e2`).
    · left
      refine joined_plane_compl x b fun t ht0 ht1 he => ?_
      have h1 := congrArg Prod.fst he
      have h2 := congrArg Prod.snd he
      simp only [b] at h1 h2
      have e1 : (1 - t) * (x.1.1 - p.1) = 0 := by linear_combination h1
      have e2 : (1 - t) * (x.1.2 - p.2) + t = 0 := by linear_combination h2
      -- `t ≠ 1`, for `t = 1` turns `e2` into `1 = 0`. So `1 - t > 0`, and `e1` gives `x₁ = p₁`.
      have ht : t ≠ 1 := by
        rintro rfl
        simp at e2
      have h1t : 0 < 1 - t := by
        rcases lt_or_eq_of_le ht1 with h | h
        · linarith
        · exact absurd h ht
      have hx1 : x.1.1 = p.1 := by
        rcases mul_eq_zero.mp e1 with h | h
        · linarith
        · linarith
      -- `x` is not on the ray below `p`, so `x₂ ≥ p₂`. Then in `e2` both terms
      -- `(1 - t)(x₂ - p₂)` and `t` are `≥ 0`, so both are `0`: `t = 0` and `x₂ = p₂`. So `x = p`,
      -- a contradiction.
      have hx2 : p.2 ≤ x.1.2 := by
        by_contra hlt
        exact hray ⟨hx1, lt_of_not_ge hlt⟩
      have : 0 ≤ (1 - t) * (x.1.2 - p.2) := mul_nonneg h1t.le (by linarith)
      have ht0' : t = 0 := by linarith
      rw [ht0'] at e2
      have hx2' : x.1.2 = p.2 := by linarith
      exact hxp (hne _ hx1 hx2')
  -- Step 3. Let `ℝ² ∖ {p} = U ∪ V` with `U`, `V` open and disjoint. Every point is on `b`'s side
  -- (`Joined.mem_iff`), directly or through `c`.
  intro U V hU hV hUV hdisj
  have hall : ∀ x, x ∈ U ↔ b ∈ U := by
    intro x
    rcases hx x with h | h
    · exact h.mem_iff hU hV hUV hdisj
    · exact (h.mem_iff hU hV hUV hdisj).trans (hcb.mem_iff hU hV hUV hdisj)
  -- So if `b ∈ U`, every point is in `U` and `V = ∅`; if `b ∉ U`, no point is in `U`.
  by_cases hb : b ∈ U
  · right
    refine eq_empty_iff_forall_notMem.mpr fun x hxV => ?_
    exact hdisj.le_bot ⟨(hall x).mpr hb, hxV⟩
  · left
    exact eq_empty_iff_forall_notMem.mpr fun x hxU => hb ((hall x).mp hxU)

/-- **`prop:line-not-plane`** for `n = 2`: `ℝ ≇ ℝ²`. Mathlib: none.

Lean: `¬ Nonempty (Homeomorph X Y)` says "there is no homeomorphism `X → Y`". -/
theorem real_not_homeomorph_plane : ¬ Nonempty (Homeomorph ℝ (ℝ × ℝ)) := by
  -- Suppose `h : ℝ → ℝ²` is a homeomorphism. `0` is a cut point of `ℝ` (`isCutPoint_real`), so
  -- `h(0)` is a cut point of `ℝ²` (`isCutPoint_iff`); but `ℝ² ∖ {h(0)}` is connected
  -- (`connected_plane_compl`).
  rintro ⟨h⟩
  exact ((h.isCutPoint_iff 0).mpr (isCutPoint_real 0)).2 (connected_plane_compl _)

end LineNotPlane

/-! ## `ℝ`, `[0, 1]` and `[0, 1)` (`thm:one-dimensional`, `rem:non-cut-count`)

The circle is defined in week 6 (`Course.S1`), which this file does not import; so of the six
cases of `thm:one-dimensional` the three among `ℝ`, `[0, 1]` and `[0, 1)` are proved here, by
counting non-cut points as in `rem:non-cut-count`: `ℝ` has none, `[0, 1)` has one, `[0, 1]`
has two. -/

section OneDimensional

/-- The half-open interval `[0, 1)`, a subspace of `ℝ` (`def-1-14`). Mathlib: `Set.Ico 0 1`. -/
abbrev Ico01 : Set ℝ := Ico 0 1

/-- The end point `0 ∈ [0, 1)`. -/
def Ico01.zero : Ico01 := ⟨0, left_mem_Ico.mpr zero_lt_one⟩

/-- If `S ⊆ ℝ` contains the segment between any two of its points (`hS`: `S` is an interval),
then `S` is connected: its points are joined by segments (`joined_of_segment`). -/
theorem connected_of_ordConnected {S : Set ℝ}
    (hS : ∀ a ∈ S, ∀ b ∈ S, ∀ t : I, (1 - (t : ℝ)) * a + (t : ℝ) * b ∈ S) : Connected S :=
  connected_of_joined fun a b => joined_of_segment a b (hS a a.2 b b.2)

/-- `[0, 1)` is connected, by segments. -/
theorem connected_Ico01 : Connected Ico01 :=
  -- The segment between `a, b ∈ [0, 1)` stays `≥ min(a, b) ≥ 0` and `≤ max(a, b) < 1`
  -- (`segment_bounds`).
  connected_of_ordConnected fun a ha b hb t => by
    obtain ⟨h1, h2⟩ := segment_bounds a b t
    exact ⟨le_trans (le_min ha.1 hb.1) h1, lt_of_le_of_lt h2 (max_lt ha.2 hb.2)⟩

/-- `0` is not a cut point of `[0, 1)`, since `[0, 1) ∖ {0} = (0, 1)` is connected.
`thm:one-dimensional`. -/
theorem not_isCutPoint_Ico01_zero : ¬ IsCutPoint Ico01.zero := by
  -- Suppose it is; then `[0, 1) ∖ {0}` is not connected (`h`). We show that it is.
  rintro ⟨-, h⟩
  apply h
  -- Every point `a` of `[0, 1) ∖ {0}` has `a > 0`, since `a ≥ 0` and `a ≠ 0`.
  have hpos : ∀ a : ({Ico01.zero}ᶜ : Set Ico01), 0 < (a : ℝ) := fun a => by
    rcases lt_or_eq_of_le a.1.2.1 with h | h
    · exact h
    · exact absurd (Subtype.ext h.symm) a.2
  -- Two points `a`, `b` are joined by their segment: its points are `≥ min(a, b) > 0` and
  -- `≤ max(a, b) < 1`, so they lie in `[0, 1)` and are not `0`. (Lean: `change` restates the
  -- goal in an equal form, here "the point is not the real number `0`".)
  refine connected_of_joined fun a b => joined_of_segment_compl a b fun t => ?_
  obtain ⟨h1, h2⟩ := segment_bounds a.1 b.1 t
  have hm : 0 < min (a.1 : ℝ) b.1 := lt_min (hpos a) (hpos b)
  refine ⟨⟨by linarith, lt_of_le_of_lt h2 (max_lt a.1.2.2 b.1.2.2)⟩, ?_⟩
  change _ ≠ (0 : ℝ)
  linarith

/-- Every point `c ≠ 0` of `[0, 1)` is a cut point. `thm:one-dimensional`, `rem:non-cut-count`. -/
theorem isCutPoint_Ico01 (c : Ico01) (hc : c ≠ Ico01.zero) : IsCutPoint c := by
  -- `c > 0`, since `c ≥ 0` and `c ≠ 0`.
  have hc0 : 0 < (c : ℝ) := by
    rcases lt_or_eq_of_le c.2.1 with h | h
    · exact h
    · exact absurd (Subtype.ext h.symm) hc
  -- `[0, 1)` is connected (`connected_Ico01`). `[0, 1) ∖ {c}` is not (`not_connected_of_real`):
  -- the inclusion `e` into `ℝ` misses `c`, and `0 < c < (c + 1)/2`, both points lying in
  -- `[0, 1) ∖ {c}` because `c < 1`.
  refine ⟨connected_Ico01, not_connected_of_real
    (e := fun w : ({c}ᶜ : Set Ico01) => ((w : Ico01) : ℝ))
    (continuous_subtype_val.comp continuous_subtype_val)
    (fun w he => w.2 (Subtype.ext he))
    (a := ⟨Ico01.zero, fun h => hc h.symm⟩)
    (b := ⟨⟨((c : ℝ) + 1) / 2, by linarith, by linarith [c.2.2]⟩,
      fun h => by have := congrArg Subtype.val h; simp at this; linarith [c.2.2]⟩)
    hc0 (by linarith [c.2.2])⟩

/-- The end points `0` and `1` are not cut points of `[0, 1]`: `(0, 1]` and `[0, 1)` are
connected, by segments. `thm:one-dimensional`, `rem:non-cut-count`. -/
theorem not_isCutPoint_I_end (x : I) (hx : x = I.zero ∨ x = I.one) : ¬ IsCutPoint x := by
  -- Suppose `x` is a cut point; we show that `[0, 1] ∖ {x}` is connected after all. Two of its
  -- points `a`, `b` are joined by their segment, which stays in `[0, 1]` (`segment_bounds`) …
  rintro ⟨-, h⟩
  apply h
  refine connected_of_joined fun a b => joined_of_segment_compl a b fun t => ?_
  obtain ⟨h1, h2⟩ := segment_bounds a.1 b.1 t
  have ha : (a.1 : ℝ) ≠ x := fun e => a.2 (Subtype.ext e)
  have hb : (b.1 : ℝ) ≠ x := fun e => b.2 (Subtype.ext e)
  refine ⟨⟨le_trans (le_min a.1.2.1 b.1.2.1) h1, le_trans h2 (max_le a.1.2.2 b.1.2.2)⟩, ?_⟩
  -- … and misses `x`: for `x = 0` its points are `≥ min(a, b) > 0`, for `x = 1` they are
  -- `≤ max(a, b) < 1`.
  rcases hx with rfl | rfl
  · have hm : 0 < min (a.1 : ℝ) b.1 :=
      lt_min (lt_of_le_of_ne a.1.2.1 (Ne.symm ha)) (lt_of_le_of_ne b.1.2.1 (Ne.symm hb))
    change _ ≠ (0 : ℝ)
    linarith
  · have hm : max (a.1 : ℝ) b.1 < 1 :=
      max_lt (lt_of_le_of_ne a.1.2.2 ha) (lt_of_le_of_ne b.1.2.2 hb)
    change _ ≠ (1 : ℝ)
    linarith

/-- **`thm:one-dimensional`**: `ℝ ≇ [0, 1)`. Mathlib: none. -/
theorem real_not_homeomorph_Ico01 : ¬ Nonempty (Homeomorph ℝ Ico01) := by
  -- The book's proof. Suppose `h : ℝ → [0, 1)` is a homeomorphism, and let `x = h⁻¹(0)`. Every
  -- point of `ℝ` is a cut point, `x` too (`isCutPoint_real`), so `h(x) = 0` is a cut point of
  -- `[0, 1)` (`isCutPoint_iff`); but it is not (`not_isCutPoint_Ico01_zero`).
  rintro ⟨h⟩
  have := (h.isCutPoint_iff (h.toEquiv.symm Ico01.zero)).mpr (isCutPoint_real _)
  rw [h.toEquiv.apply_symm_apply] at this
  exact not_isCutPoint_Ico01_zero this

/-- **`thm:one-dimensional`**: `ℝ ≇ [0, 1]`. The book separates them by compactness; here, as in
`rem:non-cut-count`, the non-cut point `0` does it. Mathlib: none. -/
theorem real_not_homeomorph_I : ¬ Nonempty (Homeomorph ℝ I) := by
  -- As for `[0, 1)`: if `h : ℝ → [0, 1]` were a homeomorphism, `0 = h(h⁻¹(0))` would be a cut
  -- point of `[0, 1]`, and it is not (`not_isCutPoint_I_end`).
  rintro ⟨h⟩
  have := (h.isCutPoint_iff (h.toEquiv.symm I.zero)).mpr (isCutPoint_real _)
  rw [h.toEquiv.apply_symm_apply] at this
  exact not_isCutPoint_I_end _ (Or.inl rfl) this

/-- **`thm:one-dimensional`**: `[0, 1] ≇ [0, 1)`. The book separates them by compactness; here, as
in `rem:non-cut-count`, by counting non-cut points: `[0, 1]` has two, `[0, 1)` only one.
Mathlib: none. -/
theorem I_not_homeomorph_Ico01 : ¬ Nonempty (Homeomorph I Ico01) := by
  -- Suppose `h : [0, 1] → [0, 1)` is a homeomorphism.
  rintro ⟨h⟩
  -- Step 1. `h` sends the end points `0`, `1` to `0`. For an end point `x`, if `h(x) ≠ 0` then
  -- `h(x)` is a cut point of `[0, 1)` (`isCutPoint_Ico01`), so `x` is a cut point of `[0, 1]`
  -- (`isCutPoint_iff`), which it is not (`not_isCutPoint_I_end`).
  have key : ∀ x : I, (x = I.zero ∨ x = I.one) → h.toEquiv x = Ico01.zero := by
    intro x hx
    by_contra hne
    exact not_isCutPoint_I_end x hx ((h.isCutPoint_iff x).mp (isCutPoint_Ico01 _ hne))
  -- Step 2. So `h(0) = h(1)`, and `0 = 1` since `h` is injective; false in `ℝ`.
  have := h.toEquiv.injective ((key _ (Or.inl rfl)).trans (key _ (Or.inr rfl)).symm)
  have := congrArg Subtype.val this
  simp [I.zero, I.one] at this

end OneDimensional

/-! ## Stereographic projection (`prop:stereographic`, `n = 1, 2`)

The punctured spheres are defined directly as subspaces of `ℝ²` and `ℝ³ = ℝ × ℝ²`; the
continuity of `σ` and `τ`, quotients of polynomials with non-vanishing denominators, is
Analysis I, entering through the bridges `subspace_toMathlib`, `prod_toMathlib`,
`real_toMathlib`. The book takes `p` to be the north pole after a rotation; only that case is
formalised. -/

section Stereographic


/-- The circle minus its north pole `N = (0, 1)`,
`S¹ ∖ {N} = {(x, y) | x² + y² = 1, (x, y) ≠ (0, 1)}`, a subspace of `ℝ²`.
Mathlib: `Metric.sphere (0 : ℝ × ℝ) 1` minus a point (Mathlib's stereographic projection is
`stereographic`, on spheres in inner product spaces). -/
def circleMinusN : Set (ℝ × ℝ) := {q | q.1 ^ 2 + q.2 ^ 2 = 1 ∧ q ≠ (0, 1)}

/-- On `S¹ ∖ {N}`, `1 - y ≠ 0`: the denominator of `σ` does not vanish. -/
theorem circleMinusN_ne_one (q : circleMinusN) : 1 - q.1.2 ≠ 0 := by
  -- If `y = 1`, then `x² + 1 = 1`, so `x = 0` and `(x, y) = (0, 1) = N`, which was removed.
  -- (`q.1` is the point `(x, y)` of the plane, `q.2.1` the proof that `x² + y² = 1`, and `q.2.2`
  -- the proof that `(x, y) ≠ N`.)
  intro h
  have hy : q.1.2 = 1 := by linarith
  have h1 := q.2.1
  rw [hy] at h1
  have hx : q.1.1 = 0 := by nlinarith [sq_nonneg q.1.1]
  exact q.2.2 (Prod.ext hx hy)

/-- **Bridge.** The course topology of `S¹ ∖ {N}`, as a subspace of the plane, is Mathlib's. -/
private theorem circleMinusN_toMathlib :
    (subspace circleMinusN).toMathlib = (inferInstance : TopologicalSpace circleMinusN) := by
  rw [subspace_toMathlib, prod_toMathlib, real_toMathlib]

/-- Stereographic projection `σ : S¹ ∖ {N} → ℝ`, `σ(x, y) = x / (1 - y)`: the line through `N`
and `(x, y)` meets the horizontal axis at `σ(x, y)`. `prop:stereographic`, `n = 1`. -/
noncomputable def stereo1 (q : circleMinusN) : ℝ := q.1.1 / (1 - q.1.2)

/-- The inverse `τ : ℝ → S¹ ∖ {N}`, `τ(u) = (2u, u² - 1) / (u² + 1)`. `prop:stereographic`,
`n = 1`. -/
noncomputable def stereo1Inv (u : ℝ) : circleMinusN :=
  ⟨(2 * u / (u ^ 2 + 1), (u ^ 2 - 1) / (u ^ 2 + 1)), by
    -- `τ(u)` lies on the circle, since `(2u)² + (u² - 1)² = (u² + 1)²` (`u² + 1 > 0`, so we may
    -- clear the denominator: `field_simp`), and is not `N`: its second coordinate is not `1`,
    -- as `u² - 1 ≠ u² + 1`.
    have hd : u ^ 2 + 1 ≠ 0 := by positivity
    refine ⟨by field_simp; ring, fun h => ?_⟩
    have := congrArg Prod.snd h
    simp only at this
    rw [div_eq_one_iff_eq hd] at this
    linarith⟩

/-- **`prop:stereographic`** for `n = 1`: `S¹ ∖ {N} ≅ ℝ`, by `σ` with inverse `τ`.
Mathlib: `stereographic'` (as an `OpenPartialHomeomorph` of `Metric.sphere`).

Lean: a homeomorphism is given by the map (`toFun`), its inverse (`invFun`), proofs that
`τ(σ(q)) = q` (`left_inv`) and `σ(τ(u)) = u` (`right_inv`), and the continuity of both. -/
noncomputable def stereographic1 : Homeomorph circleMinusN ℝ where
  toFun := stereo1
  invFun := stereo1Inv
  -- `τ(σ(x, y)) = (x, y)`. Clearing the denominators `1 - y` and `u² + 1` (`field_simp`), each
  -- coordinate becomes a polynomial identity that holds because `x² + y² = 1` (`hq`):
  -- `linear_combination k * hq` checks that the two sides differ by `k` times `x² + y² - 1`.
  left_inv q := by
    have hd := circleMinusN_ne_one q
    have hq := q.2.1
    apply Subtype.ext
    apply Prod.ext
    · simp only [stereo1Inv, stereo1]
      field_simp
      linear_combination (-(q.1.1)) * hq
    · simp only [stereo1Inv, stereo1]
      field_simp
      linear_combination (1 - q.1.2) * hq
  -- `σ(τ(u)) = u`: `1 - (u² - 1)/(u² + 1) = 2/(u² + 1)`, so `σ(τ(u)) = (2u/(u² + 1))·(u² + 1)/2`.
  right_inv u := by
    have hd : u ^ 2 + 1 ≠ 0 := by positivity
    simp only [stereo1Inv, stereo1]
    field_simp
    ring
  -- `σ` is continuous: a quotient of continuous functions whose denominator `1 - y` does not
  -- vanish (`circleMinusN_ne_one`; Analysis I, Mathlib's `Continuous.div`, through the bridges).
  continuous_toFun :=
    cont_of_mathlib circleMinusN_toMathlib real_toMathlib
      (Continuous.div (by fun_prop) (by fun_prop) circleMinusN_ne_one)
  -- `τ` is continuous into the plane, coordinate by coordinate (denominator `u² + 1 > 0`), and
  -- so into the subspace `S¹ ∖ {N}` (`Continuous.subtype_mk`).
  continuous_invFun :=
    cont_of_mathlib real_toMathlib circleMinusN_toMathlib
      (Continuous.subtype_mk (by
        refine Continuous.prodMk ?_ ?_ <;>
          exact Continuous.div (by fun_prop) (by fun_prop) (fun u => by positivity)) _)

/-- The 2-sphere minus its north pole, `S² ∖ {N}`, `N = (0, 0, 1)`, a subspace of
`ℝ³ = ℝ × ℝ²`. Mathlib: `Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1` minus a point. -/
def sphere2MinusN : Set (ℝ × ℝ × ℝ) :=
  {q | q.1 ^ 2 + q.2.1 ^ 2 + q.2.2 ^ 2 = 1 ∧ q ≠ (0, 0, 1)}

/-- On `S² ∖ {N}`, `1 - z ≠ 0`: the denominator of `σ` does not vanish. -/
theorem sphere2MinusN_ne_one (q : sphere2MinusN) : 1 - q.1.2.2 ≠ 0 := by
  -- If `z = 1`, then `x² + y² = 0`, so `x = y = 0` and the point is `N`, which was removed.
  -- (A point of `ℝ × ℝ²` is `(x, (y, z))`: `x = q.1.1`, `y = q.1.2.1`, `z = q.1.2.2`.)
  intro h
  have hz : q.1.2.2 = 1 := by linarith
  have h1 := q.2.1
  rw [hz] at h1
  have hx : q.1.1 = 0 := by nlinarith [sq_nonneg q.1.1, sq_nonneg q.1.2.1]
  have hy : q.1.2.1 = 0 := by nlinarith [sq_nonneg q.1.1, sq_nonneg q.1.2.1]
  exact q.2.2 (Prod.ext hx (Prod.ext hy hz))

/-- **Bridge.** The course topology of `S² ∖ {N}`, as a subspace of `ℝ³`, is Mathlib's. -/
private theorem sphere2MinusN_toMathlib :
    (subspace sphere2MinusN).toMathlib = (inferInstance : TopologicalSpace sphere2MinusN) := by
  rw [subspace_toMathlib, prod_toMathlib, prod_toMathlib, real_toMathlib]

/-- **Bridge.** The course topology of the plane `ℝ × ℝ` is Mathlib's. -/
private theorem plane_toMathlib :
    (prod : TopSpace (ℝ × ℝ)).toMathlib = (inferInstance : TopologicalSpace (ℝ × ℝ)) := by
  rw [prod_toMathlib, real_toMathlib]

/-- Stereographic projection `σ : S² ∖ {N} → ℝ²`, `σ(x, y, z) = (x, y) / (1 - z)`.
`prop:stereographic`, `n = 2`. -/
noncomputable def stereo2 (q : sphere2MinusN) : ℝ × ℝ :=
  (q.1.1 / (1 - q.1.2.2), q.1.2.1 / (1 - q.1.2.2))

/-- The inverse `τ : ℝ² → S² ∖ {N}`, `τ(w) = (2w, ‖w‖² - 1) / (‖w‖² + 1)`, with
`‖w‖² = w₁² + w₂²`. `prop:stereographic`, `n = 2`. -/
noncomputable def stereo2Inv (w : ℝ × ℝ) : sphere2MinusN :=
  ⟨(2 * w.1 / (w.1 ^ 2 + w.2 ^ 2 + 1), 2 * w.2 / (w.1 ^ 2 + w.2 ^ 2 + 1),
      (w.1 ^ 2 + w.2 ^ 2 - 1) / (w.1 ^ 2 + w.2 ^ 2 + 1)), by
    -- As for `n = 1`: `(2w₁)² + (2w₂)² + (‖w‖² - 1)² = (‖w‖² + 1)²`, and the last coordinate is
    -- not `1`.
    have hd : w.1 ^ 2 + w.2 ^ 2 + 1 ≠ 0 := by positivity
    refine ⟨by field_simp; ring, fun h => ?_⟩
    have := congrArg (fun q : ℝ × ℝ × ℝ => q.2.2) h
    simp only at this
    rw [div_eq_one_iff_eq hd] at this
    linarith⟩

/-- **`prop:stereographic`** for `n = 2`: `S² ∖ {N} ≅ ℝ²`, by `σ` with inverse `τ`.
Mathlib: `stereographic'`. -/
noncomputable def stereographic2 : Homeomorph sphere2MinusN (ℝ × ℝ) where
  toFun := stereo2
  invFun := stereo2Inv
  -- `τ(σ(q)) = q`, coordinate by coordinate, as for `n = 1`: after clearing denominators, a
  -- polynomial identity modulo `x² + y² + z² = 1` (`hq`).
  left_inv q := by
    have hd := sphere2MinusN_ne_one q
    have hq := q.2.1
    apply Subtype.ext
    refine Prod.ext ?_ (Prod.ext ?_ ?_)
    · simp only [stereo2Inv, stereo2]
      field_simp
      linear_combination (-(q.1.1)) * hq
    · simp only [stereo2Inv, stereo2]
      field_simp
      linear_combination (-(q.1.2.1)) * hq
    · simp only [stereo2Inv, stereo2]
      field_simp
      linear_combination (1 - q.1.2.2) * hq
  -- `σ(τ(w)) = w`: `1 - (‖w‖² - 1)/(‖w‖² + 1) = 2/(‖w‖² + 1)`, and the factors cancel.
  right_inv w := by
    have hd : w.1 ^ 2 + w.2 ^ 2 + 1 ≠ 0 := by positivity
    simp only [stereo2Inv, stereo2]
    refine Prod.ext ?_ ?_
    · field_simp
      ring
    · field_simp
      ring
  -- Both continuous, as for `n = 1` (Analysis I, through the bridges): quotients whose
  -- denominators `1 - z` and `‖w‖² + 1` do not vanish.
  continuous_toFun :=
    cont_of_mathlib sphere2MinusN_toMathlib plane_toMathlib
      (Continuous.prodMk (Continuous.div (by fun_prop) (by fun_prop) sphere2MinusN_ne_one)
        (Continuous.div (by fun_prop) (by fun_prop) sphere2MinusN_ne_one))
  continuous_invFun :=
    cont_of_mathlib plane_toMathlib sphere2MinusN_toMathlib
      (Continuous.subtype_mk (by
        refine Continuous.prodMk ?_ (Continuous.prodMk ?_ ?_) <;>
          exact Continuous.div (by fun_prop) (by fun_prop) (fun w => by positivity)) _)

end Stereographic

end Course
