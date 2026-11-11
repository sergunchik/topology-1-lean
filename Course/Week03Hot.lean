/-
Machine-generated (Claude, Aristotle), no line written by a person. Copyleft: GPL-3.0-or-later.

# Week 3: the homotopy category, deformation retracts, the cone, topological groups

This file proves the facts of week 3 about homotopy as a relation between maps. Homotopy is an
equivalence relation compatible with composition (`prop:hot-is-a-category`), so the homotopy
classes `[X, Y]` of maps form a category `Hot` (`def:hot`). Its isomorphisms are the homotopy
equivalences (`def:homotopy-equivalence`); a deformation retract `A ⊆ X` is homotopy equivalent
to `X` (`def:deformation-retract`); the cone `CX` on a non-empty space is contractible
(`prop:cone-contractible`), hence simply connected (`cor:contractible-sc`). Last, for a
topological group `G` (`def:topological-group`), the pointwise product of loops and the
interchange law of `thm-3n-eh` (week 3 of the book, its second proof) show that `π₁(G, e)` is
abelian (`hw-6-3`). The book: week 3, "The lecture in full", sections C, D and J.

Where the notions live. This week-3 file imports a week-6 file because the course's `Homotopy`
and `Homotopic` were written in `Course/Week04.lean`, `π₁` in weeks 4–6, and `IsHomotopyEquiv`,
`HomotopyEquivalent`, `Contractible` in `Course/Week06Invariance.lean`, where those weeks needed
them first, and this file uses all of them.

Departures from the book:
* `Hot` is a quotient type with composition `Hot.comp`, and the category laws are proved as
  theorems; the pointed `Hot_*` is not formalised. Lean writes `Hot.comp a b` for `b ∘ a`
  ("first `a`, then `b`").
* `thm-3n-eh` is stated in the book for `π_n`, `n ≥ 2`, with two concatenations; here
  the same interchange-law argument is run on `π₁(G, e)` with the group law of `G` as the second
  product, which is `hw-6-3`.
* From Mathlib: the continuity of the concrete map `(s, t) ↦ s + t(1 - s)` of the square
  (Analysis I, through `I.continuous_line`, week 4), and, for the cone, the result the book cites
  as Munkres, Exercise 29.11 (a quotient map times `[0, 1]` is a quotient map), taken in
  Mathlib's form `Topology.IsQuotientMap.continuous_lift_prod_left` through the bridges
  `prod_toMathlib`, `quotient_toMathlib`, `I_toMathlib`. Everything else is the book's proof.
  Mathlib's names below were checked against Lean and Mathlib v4.34.1.

New to Lean? Read `Course/README.md` first.
-/
import Course.Week06Invariance
import Mathlib.Topology.CompactOpen

-- Bookkeeping. `X`, `Y`, `Z`, `W` below are spaces (types; `u v w u'` are their "universe
-- levels", which you may ignore), and `noncomputable section` says that some definitions use
-- real numbers, which Lean cannot compute.
universe u v w u'

set_option warn.classDefReducibility false

namespace Course

open Set

noncomputable section

variable {X : Type u} {Y : Type v} {Z : Type w} {W : Type u'}

/-! ## Homotopy is compatible with composition (`prop:hot-is-a-category`, `def:hot`)

Reflexivity, symmetry and transitivity of homotopy (`Homotopic.refl`, `.symm`, `.trans`) are in
`Course/Week04.lean`; here is the compatibility with composition. -/

namespace Homotopy
variable [TopSpace X] [TopSpace Y] [TopSpace Z] {f f' : X → Y} {g g' : Y → Z}

/-- **`prop:hot-is-a-category`**, compatibility with composition: if `H` joins `f` to `f'` and
`K` joins `g` to `g'`, then `(x, t) ↦ K(H(x, t), t)` joins `g ∘ f` to `g' ∘ f'`.
Mathlib: `ContinuousMap.Homotopy.comp`. -/
def comp (H : Homotopy f f') (K : Homotopy g g') : Homotopy (g ∘ f) (g' ∘ f') where
  -- `p = (x, t)`, `p.2 = t`. Continuous as a composite of continuous maps.
  toFun p := K.toFun (H.toFun p, p.2)
  continuous_toFun := K.continuous_toFun.comp (H.continuous_toFun.prodMk continuous_snd)
  -- At `t = 0`: `K(H(x, 0), 0) = K(f(x), 0) = g(f(x))`.
  zero' x := by
    show K.toFun (H.toFun (x, 0), 0) = g (f x)
    rw [H.zero', K.zero']
  -- At `t = 1`: `K(H(x, 1), 1) = K(f'(x), 1) = g'(f'(x))`.
  one' x := by
    show K.toFun (H.toFun (x, 1), 1) = g' (f' x)
    rw [H.one', K.one']

/-- Unfolding: `(H ∘ K)(x, t) = K(H(x, t), t)`. -/
theorem comp_apply (H : Homotopy f f') (K : Homotopy g g') (p : X × I) :
    (H.comp K).toFun p = K.toFun (H.toFun p, p.2) := rfl

end Homotopy

namespace Homotopic
variable [TopSpace X] [TopSpace Y] [TopSpace Z] {f f' : X → Y} {g g' : Y → Z}

/-- **`prop:hot-is-a-category`**: `f ≃ f'` and `g ≃ g'` imply `g ∘ f ≃ g' ∘ f'`.
Mathlib: `ContinuousMap.Homotopic.comp`.

Lean: `hf.elim fun H => …` says "take a homotopy `H` that `hf` says exists". -/
theorem comp (hf : Homotopic f f') (hg : Homotopic g g') : Homotopic (g ∘ f) (g' ∘ f') :=
  hf.elim fun H => hg.elim fun K => ⟨H.comp K⟩

/-- `prop:hot-is-a-category`, composing on the left with a fixed map: `f ≃ f'` implies
`g ∘ f ≃ g ∘ f'` for continuous `g` (take `g ≃ g` the constant homotopy). Mathlib:
`ContinuousMap.Homotopic.comp` with `Homotopic.refl`. -/
theorem comp_left (hg : Continuous g) (hf : Homotopic f f') : Homotopic (g ∘ f) (g ∘ f') :=
  hf.comp (refl hg)

/-- `prop:hot-is-a-category`, composing on the right with a fixed map: `g ≃ g'` implies
`g ∘ f ≃ g' ∘ f` for continuous `f`. Mathlib: `ContinuousMap.Homotopy.compContinuousMap`. -/
theorem comp_right (hf : Continuous f) (hg : Homotopic g g') : Homotopic (g ∘ f) (g' ∘ f) :=
  (refl hf).comp hg

end Homotopic

section Hot
variable [TopSpace X] [TopSpace Y] [TopSpace Z] [TopSpace W]

-- Lean: `variable (X Y) in` makes the spaces `X`, `Y` explicit arguments of the next
-- definition, so that one writes `ContMap X Y`.
variable (X Y) in
/-- The continuous maps `X → Y`, `Map(X, Y)` of `prop:hot-is-a-category`. Mathlib: `C(X, Y)`.

Lean: an element `f` of `{f : X → Y // Continuous f}` is a map with its proof of continuity:
`f.1` is the map, `f.2` the proof. -/
def ContMap : Type (max u v) := {f : X → Y // Continuous f}

variable (X Y) in
/-- `prop:hot-is-a-category`: homotopy is an equivalence relation on `Map(X, Y)` (week 4).
Mathlib: `ContinuousMap.Homotopic.equivalence` (no named setoid in v4.34.1).

Lean: a `Setoid` is a set with an equivalence relation `r`; `iseqv` is the proof that `r` is
reflexive, symmetric and transitive, the three facts of `prop:hot-is-a-category`. -/
instance homotopySetoid : Setoid (ContMap X Y) where
  r f g := Homotopic f.1 g.1
  iseqv := ⟨fun f => Homotopic.refl f.2, Homotopic.symm, Homotopic.trans⟩

variable (X Y) in
/-- **`def:hot`**: `[X, Y] = Hot(X, Y)`, the homotopy classes of continuous maps `X → Y`.
Mathlib: none; v4.34.1 has no homotopy category of spaces (`Topology/Homotopy` has the relation
`ContinuousMap.Homotopic` only). -/
abbrev Hot : Type (max u v) := Quotient (homotopySetoid X Y)

/-- `def:hot`: the class `[f]` of a continuous map, the functor `Top → Hot` on morphisms. -/
def Hot.mk (f : X → Y) (hf : Continuous f) : Hot X Y := ⟦⟨f, hf⟩⟧

/-- `def:hot`: composition of classes, `[g] ∘ [f] = [g ∘ f]`, well defined by
`prop:hot-is-a-category` (`Homotopic.comp`). Lean's order: `Hot.comp [f] [g] = [g ∘ f]`.

Lean: `Quotient.map₂ F h` defines a map on classes by `[f], [g] ↦ [F f g]`, and `h` is the
proof that the result does not depend on the representatives: if `f ≃ f'` and `g ≃ g'` then
`g ∘ f ≃ g' ∘ f'`. -/
def Hot.comp : Hot X Y → Hot Y Z → Hot X Z :=
  Quotient.map₂ (fun (f : ContMap X Y) (g : ContMap Y Z) =>
      (⟨g.1 ∘ f.1, g.2.comp f.2⟩ : ContMap X Z))
    (fun (f f' : ContMap X Y) (hf : Homotopic f.1 f'.1) (g g' : ContMap Y Z)
      (hg : Homotopic g.1 g'.1) => (Homotopic.comp hf hg : Homotopic (g.1 ∘ f.1) (g'.1 ∘ f'.1)))

variable (X) in
/-- `def:hot`: the identity class `[id_X]`. -/
def Hot.id : Hot X X := Hot.mk (fun a => a) continuous_id

/-- `def:hot`: `Top → Hot` respects composition, `[g ∘ f] = [g] ∘ [f]`. -/
theorem Hot.mk_comp (f : X → Y) (g : Y → Z) (hf : Continuous f) (hg : Continuous g) :
    Hot.comp (Hot.mk f hf) (Hot.mk g hg) = Hot.mk (g ∘ f) (hg.comp hf) := rfl

/-- `def:hot`: `[f] = [g]` iff `f ≃ g`. -/
theorem Hot.mk_eq_mk {f g : X → Y} (hf : Continuous f) (hg : Continuous g) :
    Hot.mk f hf = Hot.mk g hg ↔ Homotopic f g :=
  Quotient.eq

/-- **`def:hot`**: `Hot` is a category: composition is associative,
`[h] ∘ ([g] ∘ [f]) = ([h] ∘ [g]) ∘ [f]`. -/
theorem Hot.comp_assoc (a : Hot X Y) (b : Hot Y Z) (c : Hot Z W) :
    Hot.comp (Hot.comp a b) c = Hot.comp a (Hot.comp b c) := by
  -- Write `a = [f]`, `b = [g]`, `c = [h]`; both sides are `[h ∘ g ∘ f]` by definition.
  induction a using Quotient.ind
  induction b using Quotient.ind
  induction c using Quotient.ind
  rfl

/-- **`def:hot`**: `a ∘ [id] = a` (in Lean's order, `Hot.comp [id] a`). -/
theorem Hot.id_comp (a : Hot X Y) : Hot.comp (Hot.id X) a = a := by
  -- `a = [f]`, and `f ∘ id = f` by definition.
  induction a using Quotient.ind
  rfl

/-- **`def:hot`**: `[id] ∘ a = a` (in Lean's order, `Hot.comp a [id]`). -/
theorem Hot.comp_id (a : Hot X Y) : Hot.comp a (Hot.id Y) = a := by
  induction a using Quotient.ind
  rfl

end Hot

/-! ## Homotopy equivalence (`def:homotopy-equivalence`) -/

section HomotopyEquiv
variable [TopSpace X] [TopSpace Y] [TopSpace Z]

/-- `def:homotopy-equivalence`: the identity is a homotopy equivalence, its own homotopy inverse.
Mathlib: `ContinuousMap.HomotopyEquiv.refl`. -/
theorem isHomotopyEquiv_id : IsHomotopyEquiv (fun a : X => a) :=
  ⟨continuous_id, fun a => a, continuous_id, Homotopic.refl continuous_id,
    Homotopic.refl continuous_id⟩

/-- `def:homotopy-equivalence`: a homotopy inverse `ψ` of `φ` (`h1 : ψφ ≃ id`,
`h2 : φψ ≃ id`) is a homotopy equivalence, with homotopy inverse `φ`.
Mathlib: `ContinuousMap.HomotopyEquiv.symm`. -/
theorem IsHomotopyEquiv.inverse {φ : X → Y} {ψ : Y → X} (hφ : Continuous φ) (hψ : Continuous ψ)
    (h1 : Homotopic (ψ ∘ φ) (fun a => a)) (h2 : Homotopic (φ ∘ ψ) (fun b => b)) :
    IsHomotopyEquiv ψ :=
  ⟨hψ, φ, hφ, h2, h1⟩

/-- `def:homotopy-equivalence`: a composite of homotopy equivalences is one, since homotopy
is compatible with composition (`prop:hot-is-a-category`): with homotopy inverses `ψ`, `ψ'`,
`(ψ ψ')(φ' φ) = ψ (ψ' φ') φ ≃ ψ φ ≃ id`, and the same on the other side.
Mathlib: `ContinuousMap.HomotopyEquiv.trans`. -/
theorem IsHomotopyEquiv.comp {φ : X → Y} {φ' : Y → Z} (hφ : IsHomotopyEquiv φ)
    (hφ' : IsHomotopyEquiv φ') : IsHomotopyEquiv (φ' ∘ φ) := by
  -- Homotopy inverses `ψ` of `φ` and `ψ'` of `φ'`; the candidate inverse of `φ' φ` is `ψ ψ'`.
  obtain ⟨hφc, ψ, hψ, h1, h2⟩ := hφ
  obtain ⟨hφc', ψ', hψ', h1', h2'⟩ := hφ'
  refine ⟨hφc'.comp hφc, ψ ∘ ψ', hψ.comp hψ', ?_, ?_⟩
  -- `ψ (ψ' φ') φ ≃ ψ id φ`, since `ψ' φ' ≃ id` (`prop:hot-is-a-category`), and `ψ φ ≃ id`.
  · have : Homotopic (ψ ∘ ((ψ' ∘ φ') ∘ φ)) (ψ ∘ ((fun b => b) ∘ φ)) :=
      Homotopic.comp_left hψ (Homotopic.comp_right hφc h1')
    exact this.trans h1
  -- `φ' (φ ψ) ψ' ≃ φ' id ψ'`, since `φ ψ ≃ id`, and `φ' ψ' ≃ id`.
  · have : Homotopic (φ' ∘ ((φ ∘ ψ) ∘ ψ')) (φ' ∘ ((fun b => b) ∘ ψ')) :=
      Homotopic.comp_left hφc' (Homotopic.comp_right hψ' h2)
    exact this.trans h2'

/-- `def:homotopy-equivalence`: `X ≃ X`. -/
theorem HomotopyEquivalent.refl (X : Type u) [TopSpace X] : HomotopyEquivalent X X :=
  ⟨_, isHomotopyEquiv_id⟩

/-- `def:homotopy-equivalence`: `X ≃ Y` implies `Y ≃ X`, by a homotopy inverse. -/
theorem HomotopyEquivalent.symm (h : HomotopyEquivalent X Y) : HomotopyEquivalent Y X := by
  obtain ⟨φ, hφc, ψ, hψ, h1, h2⟩ := h
  exact ⟨ψ, IsHomotopyEquiv.inverse hφc hψ h1 h2⟩

/-- `def:homotopy-equivalence`: `X ≃ Y ≃ Z` implies `X ≃ Z`, by the composite. -/
theorem HomotopyEquivalent.trans (h : HomotopyEquivalent X Y) (h' : HomotopyEquivalent Y Z) :
    HomotopyEquivalent X Z := by
  obtain ⟨φ, hφ⟩ := h
  obtain ⟨φ', hφ'⟩ := h'
  exact ⟨_, hφ.comp hφ'⟩

/-- **`def:homotopy-equivalence`**: homeomorphic implies homotopy equivalent; a homeomorphism
is a homotopy equivalence, its inverse a homotopy inverse (`ψ φ = id` exactly).
Mathlib: `Homeomorph.toHomotopyEquiv`. -/
theorem Homeomorph.isHomotopyEquiv (h : Homeomorph X Y) : IsHomotopyEquiv h.toFun := by
  refine ⟨h.continuous_toFun, h.invFun, h.continuous_invFun, ?_, ?_⟩
  -- `h⁻¹ ∘ h = id` as maps (`funext`: maps that agree at every point are equal), and
  -- `id ≃ id`.
  · have : h.invFun ∘ h.toFun = fun a => a := funext h.left_inv
    rw [this]; exact Homotopic.refl continuous_id
  -- `h ∘ h⁻¹ = id` likewise.
  · have : h.toFun ∘ h.invFun = fun b => b := funext h.right_inv
    rw [this]; exact Homotopic.refl continuous_id

/-- **`def:homotopy-equivalence`**: homeomorphic spaces are homotopy equivalent.
Mathlib: `Homeomorph.toHomotopyEquiv`. -/
theorem Homeomorph.homotopyEquivalent (h : Homeomorph X Y) : HomotopyEquivalent X Y :=
  ⟨_, h.isHomotopyEquiv⟩

end HomotopyEquiv

/-! ## Deformation retracts (`def:deformation-retract`) -/

section DeformationRetract
variable [TopSpace X]

/-- **`def:deformation-retract`**: `A ⊆ X` is a deformation retract if there is a continuous
`H : X × I → X` with `H(-, 0) = id_X`, `H(X × {1}) ⊆ A` and `H(a, t) = a` for all `a ∈ A`.
Mathlib: none (v4.34.1 has `ContinuousMap.HomotopyRel` and `HomotopyEquiv`, but no deformation
retract). -/
def IsDeformationRetract (A : Set X) : Prop :=
  ∃ H : X × I → X, Continuous H ∧ (∀ x, H (x, 0) = x) ∧ (∀ x, H (x, 1) ∈ A) ∧
    ∀ a ∈ A, ∀ t, H (a, t) = a

/-- `def:deformation-retract`: the retraction `r = H(-, 1) : X → A` (a map into the subspace
`A`, continuous by `prop-1-15`); `h1` says that `H(x, 1)` lies in `A`.

Lean: `⟨H (x, 1), h1 x⟩` is the point `H(x, 1)` with the proof that it is in `A`, so a point of
the subspace `A`. -/
def deformationRetraction {A : Set X} (H : X × I → X) (h1 : ∀ x, H (x, 1) ∈ A) : X → A :=
  fun x => ⟨H (x, 1), h1 x⟩

/-- **`def:deformation-retract`**, the claim: the inclusion of a deformation retract is a
homotopy equivalence, with homotopy inverse the retraction `r = H(-, 1)`: `r ∘ i = id_A`
because `H` fixes `A`, and `H` itself is a homotopy from `id_X` to `i ∘ r`.
Mathlib: none (see `IsDeformationRetract`).

Lean: the inclusion `i : A → X` is `Subtype.val`, which forgets that a point lies in `A`. -/
theorem IsDeformationRetract.isHomotopyEquiv {A : Set X} (hA : IsDeformationRetract A) :
    IsHomotopyEquiv (Subtype.val : A → X) := by
  -- `H` with `hc` (continuous), `h0` (`H(-, 0) = id`), `h1` (`H(X × {1}) ⊆ A`), `hfix`.
  obtain ⟨H, hc, h0, h1, hfix⟩ := hA
  -- `i` is continuous; the inverse is `r = H(-, 1)`, continuous into `A` by `prop-1-15`
  -- because `x ↦ H(x, 1)` is continuous into `X`.
  refine ⟨continuous_subtype_val, deformationRetraction H h1,
    continuous_subtype_mk' (hc.comp (continuous_id.prodMk continuous_const)) h1, ?_, ?_⟩
  -- `r ∘ i = id_A` exactly: `r(a) = H(a, 1) = a` for `a ∈ A`, by `hfix`.
  · have : deformationRetraction H h1 ∘ Subtype.val = fun a : A => a :=
      funext fun a => Subtype.ext (hfix a.1 a.2 1)
    rw [this]; exact Homotopic.refl continuous_id
  -- `i ∘ r ≃ id_X`: `H` is a homotopy from `id_X` (at `t = 0`, `h0`) to `i ∘ r` (at `t = 1`,
  -- `i(r(x)) = H(x, 1)` by definition); reverse it (`Homotopic.symm`).
  · exact Homotopic.symm ⟨{ toFun := H, continuous_toFun := hc, zero' := h0, one' := fun _ => rfl }⟩

/-- `def:deformation-retract`: a deformation retract is homotopy equivalent to the whole
space. -/
theorem IsDeformationRetract.homotopyEquivalent {A : Set X} (hA : IsDeformationRetract A) :
    HomotopyEquivalent A X :=
  ⟨_, hA.isHomotopyEquiv⟩

end DeformationRetract

/-! ## The cone is contractible (`prop:cone-contractible`)

The book's proof: on `CX = X × [0, 1] / (X × {1})`, with apex `v`, the contraction is
`H([x, s], t) = [x, s + t(1 - s)]`. It slides every point up its own cone line `s ↦ [x, s]`,
covering at time `t` the fraction `t` of the distance still to go; it is well defined because
it keeps `s = 1` at `s = 1`, and continuous because `CX × I` is a quotient of `X × I × I`. -/

section QuotientTimesI
variable {A : Type u} [TopSpace A] [TopSpace Z] {s : Setoid A}

/-- The input `prop:cone-contractible` cites, **Munkres, Exercise 29.11**: the product of a
quotient map with the compact Hausdorff `[0, 1]` is a quotient map. In the form used, the
universal property of that quotient: a map `g : (A/∼) × I → Z` is continuous as soon as
`(a, t) ↦ g([a], t)` is. Taken from Mathlib, `Topology.IsQuotientMap.continuous_lift_prod_left`
(for a locally compact factor; `unitInterval` is one), through the bridges `prod_toMathlib`,
`quotient_toMathlib` and `I_toMathlib`. -/
theorem continuous_quotient_prod_I {g : Quotient s × I → Z}
    (hg : Continuous (fun p : A × I => g (Quotient.mk s p.1, p.2))) : Continuous g := by
  -- Give `A` and `Z` Mathlib's versions of their course topologies (`toMathlib`).
  let tA : TopologicalSpace A := (‹TopSpace A›).toMathlib
  let tZ : TopologicalSpace Z := (‹TopSpace Z›).toMathlib
  -- `a ↦ [a]` is a quotient map in Mathlib's sense.
  have hq : Topology.IsQuotientMap (Quotient.mk s) := isQuotientMap_quotient_mk'
  -- The hypothesis, read in Mathlib's language: `(a, t) ↦ g([a], t)` is continuous.
  have hg' : _root_.Continuous (fun p : A × unitInterval => g (Quotient.mk s p.1, p.2)) :=
    mathlib_continuous_of_eq (by rw [prod_toMathlib, I_toMathlib]) rfl hg
  -- Munkres 29.11 (Mathlib): so `g` is continuous on `(A/∼) × I`; read it back in the course's
  -- language.
  have h := hq.continuous_lift_prod_left (Y := unitInterval) hg'
  exact continuous_of_mathlib_eq (by rw [prod_toMathlib, quotient_toMathlib, I_toMathlib]) rfl h

end QuotientTimesI

variable (X) in
/-- `prop:cone-contractible`: the relation on `X × I` that collapses `X × {1}` to a point:
`(x, s) ∼ (x', s')` iff they are equal or `s = s' = 1`. -/
def coneSetoid : Setoid (X × I) where
  r p q := p = q ∨ (p.2 = 1 ∧ q.2 = 1)
  iseqv := by
    -- Reflexive (`p = p`) and symmetric (swap the two halves); it remains to show transitive.
    refine ⟨fun p => Or.inl rfl, fun h => h.elim (fun h => Or.inl h.symm)
      (fun h => Or.inr ⟨h.2, h.1⟩), ?_⟩
    -- If `p ∼ q` and `q ∼ r`, four cases: each relation is an equality or "both at `s = 1`".
    -- (Lean: the pattern `rfl` substitutes the equality at once.)
    rintro p q r (rfl | ⟨hp, hq⟩) (rfl | ⟨hq', hr⟩)
    · exact Or.inl rfl
    · exact Or.inr ⟨hq', hr⟩
    · exact Or.inr ⟨hp, hq⟩
    · exact Or.inr ⟨hp, hr⟩

variable (X) in
/-- **`prop:cone-contractible`**: the cone `CX = X × [0, 1] / (X × {1})`, the course quotient
(`def:quotient`) of the course product (`thm:product-top`). Mathlib: none as a space
(`CategoryTheory.Limits.Cone` is unrelated). -/
abbrev Cone [TopSpace X] : Type u := Quotient (coneSetoid X)

namespace Cone
variable [TopSpace X]

/-- `prop:cone-contractible`: the point `[x, s]` of the cone. -/
def mk (x : X) (s : I) : Cone X := Quotient.mk (coneSetoid X) (x, s)

/-- `prop:cone-contractible`: the apex `v = [x, 1]`; it does not depend on `x` (`apex_eq`), but a
point `x` is needed: the cone on the empty space is empty. -/
def apex (x : X) : Cone X := mk x 1

/-- `[x, 1] = [y, 1]`: all of `X × {1}` is one point. -/
theorem apex_eq (x y : X) : apex x = apex y := Quotient.sound (Or.inr ⟨rfl, rfl⟩)

/-- `[x, 1] = v`. -/
theorem mk_one (x : X) (y : X) : mk x 1 = apex y := apex_eq x y

/-- `prop:cone-contractible`: `s + t(1 - s)`, the point the fraction `t` of the way from `s` to
`1`; it is the straight line `(1 - t)s + t · 1` of week 4, continuous by Analysis I. -/
def up (p : I × I) : I := I.line id (fun _ => 1) p

/-- Unfolding: `up(s, t) = (1 - t)s + t · 1`. -/
theorem coe_up (p : I × I) : (up p : ℝ) = (1 - (p.2 : ℝ)) * p.1 + p.2 * 1 := rfl

/-- `(s, t) ↦ s + t(1 - s)` is continuous (Analysis I, `I.continuous_line`). -/
theorem continuous_up : Continuous up := I.continuous_line continuous_id continuous_const

/-- At `t = 0` nothing moves: `up(s, 0) = s`. -/
theorem up_zero (s : I) : up (s, 0) = s := I.line_zero _ _ s

/-- At `t = 1` everything is at the top: `up(s, 1) = 1`. -/
theorem up_one (s : I) : up (s, 1) = 1 := I.line_one _ _ s

/-- The top stays at the top: `up(1, t) = 1 + t · 0 = 1`. -/
theorem one_up (t : I) : up (1, t) = 1 := Subtype.ext (by rw [coe_up]; simp)

/-- **`prop:cone-contractible`**: `H([x, s], t) = [x, s + t(1 - s)]`, well defined because at
`s = 1` the formula gives `s + t(1 - s) = 1` again.

Lean: `Quotient.lift F h c` defines a map on classes by `[q] ↦ F(q)`, and `h` is the proof that
related `q`'s give the same value; here `p = (c, t)` with `c = p.1` a point of the cone. -/
def contract (p : Cone X × I) : Cone X :=
  Quotient.lift (fun q : X × I => mk q.1 (up (q.2, p.2)))
    (fun a b (h : a = b ∨ (a.2 = 1 ∧ b.2 = 1)) => by
      -- If `a = b` there is nothing to show. If `a = (x, 1)` and `b = (x', 1)`, both go to
      -- `[-, up(1, t)] = [-, 1] = v`.
      rcases h with rfl | ⟨ha, hb⟩
      · rfl
      · show mk a.1 (up (a.2, p.2)) = mk b.1 (up (b.2, p.2))
        rw [ha, hb, one_up]
        exact apex_eq _ _) p.1

/-- Unfolding: `H([x, s], t) = [x, s + t(1 - s)]`. -/
theorem contract_mk (x : X) (s t : I) : contract (mk x s, t) = mk x (up (s, t)) := rfl

/-- **`prop:cone-contractible`**: the contraction is continuous, because `CX × I` is a quotient
of `X × I × I` (Munkres, Exercise 29.11: `continuous_quotient_prod_I`) and on `X × I × I` it is
`(x, s, t) ↦ [x, s + t(1 - s)]`, continuous by `thm:product-top` and Analysis I. -/
theorem continuous_contract : Continuous (contract : Cone X × I → Cone X) := by
  -- By Munkres 29.11 it suffices that `((x, s), t) ↦ [x, s + t(1 - s)]` is continuous on
  -- `(X × I) × I`.
  apply continuous_quotient_prod_I
  -- It is `q ∘ (x, up(s, t))` with `q : X × I → CX` the quotient map: continuous (week 2), and
  -- the coordinates `x`, `s`, `t` and `up` are continuous (`thm:product-top`, Analysis I).
  have h : Continuous (fun p : (X × I) × I =>
      Quotient.mk (coneSetoid X) (p.1.1, up (p.1.2, p.2))) :=
    continuous_quotient_mk.comp ((continuous_fst.comp continuous_fst).prodMk
      (continuous_up.comp ((continuous_snd.comp continuous_fst).prodMk continuous_snd)))
  exact h

/-- **`prop:cone-contractible`**: the contraction of `CX`, a homotopy from `id` to the constant
map at the apex: at `t = 0` it is `[x, s]`, at `t = 1` it is `[x, 1] = v`. -/
def contraction (x₀ : X) : Homotopy (fun c : Cone X => c) (fun _ => apex x₀) where
  toFun := contract
  continuous_toFun := continuous_contract
  -- At `t = 0`, on `c = [x, s]`: `[x, up(s, 0)] = [x, s]`.
  zero' c := by
    induction c using Quotient.ind with | _ q => ?_
    show mk q.1 (up (q.2, 0)) = Quotient.mk _ q
    rw [up_zero]; rfl
  -- At `t = 1`: `[x, up(s, 1)] = [x, 1] = v`.
  one' c := by
    induction c using Quotient.ind with | _ q => ?_
    show mk q.1 (up (q.2, 1)) = apex x₀
    rw [up_one]; exact mk_one _ _

/-- **`prop:cone-contractible`**: the contraction fixes the apex throughout, `H(v, t) = v`; so
it is even a pointed contraction. Mathlib: none. -/
theorem contraction_apex (x₀ y : X) (t : I) : (contraction x₀).toFun (apex y, t) = apex y := by
  -- `H([y, 1], t) = [y, up(1, t)] = [y, 1]`.
  show mk y (up (1, t)) = mk y 1
  rw [one_up]

end Cone

/-- **`prop:cone-contractible`**: the cone on a non-empty space is contractible
(`def:contractible`): `id_{CX}` is homotopic to the constant map at the apex. Mathlib: none for
the cone; the notion is `ContractibleSpace`.

Lean: `[Nonempty X]` says `X` has a point, and `Classical.arbitrary X` picks one. -/
theorem cone_contractible [TopSpace X] [Nonempty X] : Contractible (Cone X) :=
  ⟨Cone.apex (Classical.arbitrary X), ⟨Cone.contraction (Classical.arbitrary X)⟩⟩

/-- `prop:cone-contractible` with `cor:contractible-sc`: the cone on a non-empty space is simply
connected. -/
theorem cone_simplyConnected [TopSpace X] [Nonempty X] : SimplyConnected (Cone X) :=
  cone_contractible.simplyConnected

/-! ## Topological groups, and `π₁` of a topological group is abelian (`def:topological-group`,
`hw-6-3`, by `thm-3n-eh`'s interchange law)

The plan, from `hw-6-3`. On loops at the identity `e` of `G` there are two products: the
concatenation `f · g` of week 4, and the pointwise product `(f ∗ g)(s) = f(s) g(s)`. Both have
the constant loop as unit, and they satisfy the interchange law
`(f · g) ∗ (h · k) = (f ∗ h) · (g ∗ k)`. As in `thm-3n-eh`, putting `g = h = 1` shows
that `∗` and `·` agree on `π₁(G, e)`, and putting `f = k = 1` shows that the product is
commutative. In Lean, `e` is written `1`. -/

/-- **`def:topological-group`**: a group `G` with a topology in which multiplication
`G × G → G` (course product, `thm:product-top`) and inversion `G → G` are continuous.
Mathlib: `IsTopologicalGroup` (see `topGroup_iff_mathlib`).

Lean: a `class` is a structure that Lean finds by itself when asked for `[TopGroup G]`, like
`[TopSpace X]`. -/
class TopGroup (G : Type u) [Group G] [TopSpace G] : Prop where
  continuous_mul : Continuous (fun p : G × G => p.1 * p.2)
  continuous_inv : Continuous (fun g : G => g⁻¹)

section TopGroup
variable {G : Type u} [Group G] [TopSpace G] [TopGroup G]

/-- `hw-6-3`: the pointwise product `(f ∗ g)(s) = f(s) g(s)` of two paths, a path from `a c` to
`b d`; continuous because multiplication is (`def:topological-group`). The end points are
given as equations (`he : a c = e`, `he' : b d = e'`), so that for loops at `e` the product is
again a loop at `e`. Mathlib: none (`IsTopologicalGroup.hSpace` is the same product on `G`). -/
def Path.pmul {a b c d e e' : G} (f : Path a b) (g : Path c d) (he : a * c = e)
    (he' : b * d = e') : Path e e' where
  toFun s := f s * g s
  continuous_toFun := TopGroup.continuous_mul.comp (f.continuous.prodMk g.continuous)
  -- It starts at `f(0) g(0) = a c = e` and ends at `f(1) g(1) = b d = e'`.
  source' := by show f 0 * g 0 = e; rw [f.source, g.source, he]
  target' := by show f 1 * g 1 = e'; rw [f.target, g.target, he']

/-- Unfolding: `(f ∗ g)(s) = f(s) g(s)`. -/
theorem Path.pmul_apply {a b c d e e' : G} (f : Path a b) (g : Path c d) (he : a * c = e)
    (he' : b * d = e') (s : I) : f.pmul g he he' s = f s * g s := rfl

/-- `hw-6-3`: the pointwise product respects path homotopy: if `F : f ≃ₚ f'` and `K : g ≃ₚ g'`,
then `(F ∗ K)(s, t) = F(s, t) K(s, t)` is a path homotopy `f ∗ g ≃ₚ f' ∗ g'`. -/
def PathHomotopy.pmul {a b c d e e' : G} {f f' : Path a b} {g g' : Path c d} (he : a * c = e)
    (he' : b * d = e') (F : PathHomotopy f f') (K : PathHomotopy g g') :
    PathHomotopy (f.pmul g he he') (f'.pmul g' he he') where
  toFun p := F.toFun p * K.toFun p
  continuous_toFun := TopGroup.continuous_mul.comp (F.continuous_toFun.prodMk K.continuous_toFun)
  -- Each edge of the square is the product of the corresponding edges of `F` and `K`.
  zero' s := by show F.toFun (s, 0) * K.toFun (s, 0) = f s * g s; rw [F.zero', K.zero']
  one' s := by show F.toFun (s, 1) * K.toFun (s, 1) = f' s * g' s; rw [F.one', K.one']
  source' t := by show F.toFun (0, t) * K.toFun (0, t) = e; rw [F.source', K.source', he]
  target' t := by show F.toFun (1, t) * K.toFun (1, t) = e'; rw [F.target', K.target', he']

/-- **The interchange law** (`thm-3n-eh`, for `hw-6-3`): `(f · g) ∗ (h · k) =
(f ∗ h) · (g ∗ k)`, both sides being `f(2s) h(2s)` on `[0, 1/2]` and `g(2s - 1) k(2s - 1)` on
`[1/2, 1]`; an equality of paths, not only a homotopy. -/
theorem Path.pmul_trans {a b c e e' e'' : G} {a' b' c' : G} (f : Path a b) (g : Path b c)
    (h : Path a' b') (k : Path b' c') (he : a * a' = e) (he' : b * b' = e') (he'' : c * c' = e'') :
    (f.trans g).pmul (h.trans k) he he'' = (f.pmul h he he').trans (g.pmul k he' he'') := by
  -- Compare at every `s`, unfolding `·` and `∗`; then split into `s ≤ 1/2` and `s > 1/2`
  -- (`split_ifs`), where both sides are the same formula.
  ext s
  rw [Path.pmul_apply, Path.trans_apply, Path.trans_apply, Path.trans_apply]
  split_ifs <;> rfl

/-- `hw-6-3`: the constant loop at `e` is a unit for `∗` on the left, exactly:
`e f(s) = f(s)`. -/
theorem Path.refl_pmul (f : Path (1 : G) 1) :
    (Path.refl (1 : G)).pmul f (mul_one 1) (mul_one 1) = f := by
  ext s; exact one_mul _

/-- `hw-6-3`: and on the right: `f(s) e = f(s)`. -/
theorem Path.pmul_refl (f : Path (1 : G) 1) :
    f.pmul (Path.refl (1 : G)) (mul_one 1) (mul_one 1) = f := by
  ext s; exact mul_one _

/-- `hw-6-3`: the second product on `π₁(G, e)`, `[f] ∗ [g] = [f ∗ g]`, well defined by
`PathHomotopy.pmul`. (Lean's `mul_one 1` is the proof that `e e = e`.) -/
def pi1PMul : pi1 (1 : G) → pi1 (1 : G) → pi1 (1 : G) :=
  Quotient.map₂ (fun f g : Path (1 : G) 1 => f.pmul g (mul_one 1) (mul_one 1))
    (fun (f f' : Path (1 : G) 1) (hf : f.Homotopic f') (g g' : Path (1 : G) 1)
      (hg : g.Homotopic g') =>
      (hf.elim fun F => hg.elim fun K => ⟨PathHomotopy.pmul _ _ F K⟩ :
        (f.pmul g (mul_one 1) (mul_one 1)).Homotopic (f'.pmul g' (mul_one 1) (mul_one 1))))

/-- Unfolding: `[f] ∗ [g] = [f ∗ g]`. -/
theorem pi1PMul_mk (f g : Path (1 : G) 1) :
    pi1PMul (⟦f⟧ : pi1 (1 : G)) ⟦g⟧ = ⟦f.pmul g (mul_one 1) (mul_one 1)⟧ := rfl

/-- `thm-3n-eh`'s interchange law, on classes:
`(a · b) ∗ (c · d) = (a ∗ c) · (b ∗ d)`. -/
theorem pi1PMul_interchange (a b c d : pi1 (1 : G)) :
    pi1PMul (a * b) (c * d) = pi1PMul a c * pi1PMul b d := by
  -- Write `a = [f]`, `b = [g]`, `c = [h]`, `d = [k]`; then it is the interchange law for paths.
  induction a using Quotient.ind with | _ f => ?_
  induction b using Quotient.ind with | _ g => ?_
  induction c using Quotient.ind with | _ h => ?_
  induction d using Quotient.ind with | _ k => ?_
  show (⟦(f.trans g).pmul (h.trans k) (mul_one 1) (mul_one 1)⟧ : pi1 (1 : G)) =
    ⟦(f.pmul h (mul_one 1) (mul_one 1)).trans (g.pmul k (mul_one 1) (mul_one 1))⟧
  rw [Path.pmul_trans f g h k (mul_one 1) (mul_one 1) (mul_one 1)]

/-- `thm-3n-eh`: the two products share the unit `1 = [c_e]`: `1 ∗ a = a`. -/
theorem pi1PMul_one_left (a : pi1 (1 : G)) : pi1PMul 1 a = a := by
  induction a using Quotient.ind with | _ f => ?_
  show (⟦(Path.refl (1 : G)).pmul f (mul_one 1) (mul_one 1)⟧ : pi1 (1 : G)) = ⟦f⟧
  rw [Path.refl_pmul]

/-- `thm-3n-eh`: `a ∗ 1 = a`. -/
theorem pi1PMul_one_right (a : pi1 (1 : G)) : pi1PMul a 1 = a := by
  induction a using Quotient.ind with | _ f => ?_
  show (⟦f.pmul (Path.refl (1 : G)) (mul_one 1) (mul_one 1)⟧ : pi1 (1 : G)) = ⟦f⟧
  rw [Path.pmul_refl]

/-- **`hw-6-3`**: `f ∗ g ≃ₚ f · g`, i.e. the two products on `π₁(G, e)` agree. By the interchange
law with `b = c = 1` (`thm-3n-eh`): `a ∗ d = (a · 1) ∗ (1 · d) = (a ∗ 1) · (1 ∗ d) =
a · d`. -/
theorem pi1PMul_eq_mul (a d : pi1 (1 : G)) : pi1PMul a d = a * d := by
  -- The interchange law for `a, 1, 1, d`: `(a · 1) ∗ (1 · d) = (a ∗ 1) · (1 ∗ d)`; simplify both
  -- sides with the units. (Lean: `rwa` is `rw`, then "this is exactly the hypothesis".)
  have h := pi1PMul_interchange a 1 1 d
  rwa [mul_one, one_mul, pi1PMul_one_right, pi1PMul_one_left] at h

/-- `hw-6-3`, the statement for loops: `f ∗ g ≃ₚ f · g` (equal classes come from a path
homotopy, `Quotient.exact`). -/
theorem Path.pmul_homotopic_trans (f g : Path (1 : G) 1) :
    (f.pmul g (mul_one 1) (mul_one 1)).Homotopic (f.trans g) :=
  Quotient.exact (pi1PMul_eq_mul (⟦f⟧ : pi1 (1 : G)) ⟦g⟧)

/-- **Eckmann–Hilton for a topological group** (`hw-6-3`, by the interchange law of
`thm-3n-eh`): `π₁(G, e)` is abelian. With `a = d = 1` the interchange law gives
`b ∗ c = (1 · b) ∗ (c · 1) = (1 ∗ c) · (b ∗ 1) = c · b`, and `b ∗ c = b · c` by
`pi1PMul_eq_mul`. Mathlib: none for `π₁`; the algebra is `EckmannHilton.mul_comm`, and
Mathlib's higher homotopy groups use it (`HomotopyGroup.commGroup`). -/
theorem pi1_mul_comm (b c : pi1 (1 : G)) : b * c = c * b := by
  -- The interchange law for `1, b, c, 1`, simplified with the units, is `b ∗ c = c · b`; and
  -- `b ∗ c = b · c`.
  have h := pi1PMul_interchange 1 b c 1
  rw [one_mul, mul_one, pi1PMul_one_left, pi1PMul_one_right, pi1PMul_eq_mul] at h
  exact h

/-- **Eckmann–Hilton for a topological group**: `π₁(G, e)` as a commutative group. -/
instance pi1.instCommGroup : CommGroup (pi1 (1 : G)) where
  mul_comm := pi1_mul_comm

end TopGroup

/-! ## Bridges to Mathlib (`def:homotopy`, `def:topological-group`)

These say that the course's notions are Mathlib's, so that one may compare. They are not used in
the proofs above. `IsDeformationRetract` has no Mathlib counterpart in v4.34.1, so no bridge. -/

section Bridge
variable [tX : TopSpace X] [tY : TopSpace Y]

/-- The course topology of `X × I` is Mathlib's product of `X`'s with `unitInterval`'s. -/
theorem prod_I_toMathlib :
    (prod : TopSpace (X × I)).toMathlib =
      @instTopologicalSpaceProd X unitInterval tX.toMathlib _ := by
  rw [prod_toMathlib, I_toMathlib]

/-- **Bridge** (`def:homotopy`). For continuous `f, g`, the course's `f ≃ g` is Mathlib's
`ContinuousMap.Homotopic` for the topologies `toMathlib`; Mathlib's homotopies put the time
first, so the factors of `X × I` are swapped. -/
theorem homotopic_iff_mathlib {f g : X → Y} (hf : Continuous f) (hg : Continuous g) :
    Homotopic f g ↔ @ContinuousMap.Homotopic X Y tX.toMathlib tY.toMathlib
      (@ContinuousMap.mk X Y tX.toMathlib tY.toMathlib f ((continuous_iff_mathlib f).mp hf))
      (@ContinuousMap.mk X Y tX.toMathlib tY.toMathlib g ((continuous_iff_mathlib g).mp hg)) := by
  let _ := tX.toMathlib
  let _ := tY.toMathlib
  constructor
  -- A course homotopy `F(x, t)` gives Mathlib's `(t, x) ↦ F(x, t)`.
  · rintro ⟨F⟩
    have hF : _root_.Continuous F.toFun :=
      mathlib_continuous_of_eq prod_I_toMathlib rfl F.continuous_toFun
    exact ⟨{ toFun := fun p => F.toFun (p.2, p.1)
             continuous_toFun := hF.comp _root_.continuous_swap
             map_zero_left := fun x => F.zero' x
             map_one_left := fun x => F.one' x }⟩
  -- And Mathlib's `F(t, x)` gives the course's `(x, t) ↦ F(t, x)`.
  · rintro ⟨F⟩
    exact ⟨{ toFun := fun p => F (p.2, p.1)
             continuous_toFun :=
               continuous_of_mathlib_eq prod_I_toMathlib rfl
                 (F.continuous.comp _root_.continuous_swap)
             zero' := fun x => F.apply_zero x
             one' := fun x => F.apply_one x }⟩

/-- **Bridge** (`def:topological-group`): a course topological group is Mathlib's
`IsTopologicalGroup` for the topology `toMathlib`, and conversely. -/
theorem topGroup_iff_mathlib (G : Type u) [Group G] [t : TopSpace G] :
    TopGroup G ↔ @IsTopologicalGroup G t.toMathlib _ := by
  let _ := t.toMathlib
  -- The course product topology on `G × G` is Mathlib's; then translate the continuity of
  -- multiplication and of inversion each way (`continuous_iff_mathlib`).
  have hp : (prod : TopSpace (G × G)).toMathlib = instTopologicalSpaceProd := prod_toMathlib
  constructor
  · rintro ⟨hm, hi⟩
    exact { continuous_mul := mathlib_continuous_of_eq hp rfl hm
            continuous_inv := (continuous_iff_mathlib _).mp hi }
  · intro h
    exact ⟨continuous_of_mathlib_eq hp rfl h.continuous_mul,
      (continuous_iff_mathlib _).mpr h.continuous_inv⟩

end Bridge

end

end Course
