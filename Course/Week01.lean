/-
Machine-generated (Claude, Aristotle), no line written by a person. Copyleft: GPL-3.0-or-later.

# Week 1: topological spaces, bases, subspaces, continuity

This file builds week 1 of the book (its core, and "The lecture in full") from
nothing. A topology on `X` is the family of its
open sets; from it come closed sets and the closure, continuous maps (identities and composites
are continuous, `prop-1n-composite`), bases and the base criterion (`prop-1-10`), neighbourhood
bases and the local criterion (`prop-1-13`), the subspace topology (`def-1-14`, `prop-1-15`,
`prop-1-17`), continuity checked on a subbase (`prop-1-19`), the gluing lemma (`prop-1-20`),
homeomorphisms as continuous bijections that are open (`prop-1-22`), and topological properties
(`prop-1-28`). Then the first spaces of the course, from (pseudo-)metrics: the space of words,
whose cylinders `C_u` are open and closed (`prop-1-5`), and `ℤ` with the `p`-adic metric, whose
balls are residue classes (`prop-1-8`). Every later file builds on these definitions.

**Why the course does not use Mathlib's topology.** Mathlib, Lean's library of mathematics,
already has topological spaces, open sets and continuous maps. Had we used them, each fact
below would be a citation of a proof written elsewhere, in another way. So the course defines
its own `TopSpace`, `IsOpen`, `Continuous`, and proves everything from the axioms, as the book
does. To check that these are the usual notions, the file also proves **bridges**: theorems
named `…_iff_mathlib`, `…_toMathlib` or `toMathlib`, which say that the course's notion is
Mathlib's (`TopSpace.equivMathlib`: a topology of the course is the same thing as a topology of
Mathlib). No proof of a topological result of the course uses a bridge: they check the
definitions and supply no arguments. The one exception is deliberate: in later files a few
bridges carry facts of Analysis I about `ℝ`, such as the continuity of `+` and `·`, into the
course, and each such use says so.

Departures from the book:
* A topology is a structure `TopSpace X` with four fields: the property "is open" of subsets,
  and three axioms (`X` is open; the intersection of two open sets and the union of any family
  of open sets are open). That `∅` is open is then a theorem (`isOpen_empty`): it is the union
  of the empty family.
* A subset `A ⊆ X` becomes a space in its own right, whose points are the points of `A`;
  `U ∩ A` is written as the preimage of `U` under the inclusion `A → X`.
* The topology of a pseudo-metric, which the book recalls from Analysis I, is built here from
  the balls by the base criterion.
* In the space of words the letters are numbered from `0`, not `1` (see that section), and the
  alphabet may be any set.
* A homeomorphism comes together with its inverse: a bijection `X ≃ Y` with both directions
  continuous.
* From Analysis I and algebra, through Mathlib: the arithmetic and order of `ℝ`, powers such as
  `2^{-k}` and `p^{-k}`, cardinalities, and the exponent `v_p(n)` of `p` in `n`
  (`padicValInt`). Mathlib's names below were checked against Lean and Mathlib v4.34.1.

New to Lean? Read `Course/README.md` first.
-/
import Mathlib.Topology.Bases
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.Homeomorph.Defs
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.SetTheory.Cardinal.Defs

-- Bookkeeping. `universe u v w` lets the spaces below live in any "universe" of types (you may
-- ignore it); the `set_option` silences one of Lean's warnings. `namespace Course` puts every
-- name below under `Course.`, so that the course's `Continuous` does not clash with Mathlib's
-- (which is then written `_root_.Continuous`). `open Set` lets us write `univ` for `Set.univ`,
-- the whole of `X` seen as a subset of itself.
universe u v w

set_option warn.classDefReducibility false

namespace Course

open Set

/-! ## Topological spaces -/

/-- A topology on a set `X`, given by its open sets: Analysis I 4.1, recalled in the book's
week 1. Mathlib: `TopologicalSpace` (the same four fields; see `TopSpace.equivMathlib`).

Lean: a `class` is a structure (here: a property of subsets and three axioms about it) that
Lean finds by itself. Once we declare that `X` carries a `TopSpace X` (an *instance* of the
class), every statement about open subsets of `X` uses it without our naming it, just as the
book says "`U` is open in `X`" without repeating which topology. `Set X → Prop` is the type of
properties of subsets of `X`: `IsOpen U` is the statement "`U` is open". -/
class TopSpace (X : Type u) where
  /-- The open sets. -/
  IsOpen : Set X → Prop
  /-- `X` itself is open. -/
  isOpen_univ : IsOpen univ
  /-- The intersection of two open sets is open. -/
  isOpen_inter : ∀ U V, IsOpen U → IsOpen V → IsOpen (U ∩ V)
  /-- The union `⋃₀ 𝒰` of any family `𝒰` of open sets is open. -/
  isOpen_sUnion : ∀ 𝒰 : Set (Set X), (∀ U ∈ 𝒰, IsOpen U) → IsOpen (⋃₀ 𝒰)

-- From here on `X`, `Y`, `Z` are sets (types), and any statement below may mention them; the
-- curly brackets say that Lean works out which sets are meant from the rest of the statement.
variable {X : Type u} {Y : Type v} {Z : Type w}

/-- Two topologies `s`, `t` on `X` with the same open sets are equal. Mathlib:
`TopologicalSpace.ext`. -/
theorem TopSpace.ext {s t : TopSpace X} (h : ∀ U, s.IsOpen U ↔ t.IsOpen U) : s = t := by
  -- A topology is its four fields. The last three are proofs, and Lean counts two proofs of the
  -- same statement as equal; so it suffices that the properties "is open" agree on every `U`
  -- (`funext`: maps that agree everywhere are equal; `propext`: equivalent statements are equal).
  cases s; cases t; congr; funext U; exact propext (h U)

-- In the next section `X` carries a topology. `[TopSpace X]` in square brackets: an instance of
-- the class, which every statement below uses without naming it.
section Basic
variable [TopSpace X]

/-- `U` is open (in the topology of `X`, which Lean finds itself). Mathlib: `IsOpen`. -/
def IsOpen (U : Set X) : Prop := TopSpace.IsOpen U

/-- `C` is closed: its complement `X ∖ C` (written `Cᶜ`) is open (Analysis I 4.10).
Mathlib: `IsClosed`. -/
def IsClosed (C : Set X) : Prop := IsOpen Cᶜ

/-- The axiom: `X` is open. Mathlib: `isOpen_univ`. -/
theorem isOpen_univ : IsOpen (univ : Set X) := TopSpace.isOpen_univ

/-- The axiom: if `U` and `V` are open, so is `U ∩ V`. Mathlib: `IsOpen.inter`. -/
theorem IsOpen.inter {U V : Set X} (hU : IsOpen U) (hV : IsOpen V) : IsOpen (U ∩ V) :=
  TopSpace.isOpen_inter U V hU hV

/-- The axiom: if every member of the family `𝒰` is open, so is the union `⋃₀ 𝒰`.
Mathlib: `isOpen_sUnion`. -/
theorem isOpen_sUnion {𝒰 : Set (Set X)} (h : ∀ U ∈ 𝒰, IsOpen U) : IsOpen (⋃₀ 𝒰) :=
  TopSpace.isOpen_sUnion 𝒰 h

/-- The empty set is open: it is the union of the empty family. Mathlib: `isOpen_empty`. -/
theorem isOpen_empty : IsOpen (∅ : Set X) := by
  -- `∅ = ⋃₀ ∅`, and every member of the empty family is open (there are none).
  simpa using isOpen_sUnion (𝒰 := (∅ : Set (Set X))) (by simp)

/-- A union `⋃ᵢ Uᵢ` of open sets, indexed by any set `ι`, is open. Mathlib: `isOpen_iUnion`. -/
theorem isOpen_iUnion {ι : Sort*} {U : ι → Set X} (h : ∀ i, IsOpen (U i)) :
    IsOpen (⋃ i, U i) := by
  -- `⋃ᵢ Uᵢ` is the union `⋃₀` of the family `{Uᵢ : i ∈ ι}`, all of whose members are open.
  -- (Lean: `rintro` is `intro` that also unpacks; a member of the family is some `U i`.)
  rw [← sUnion_range]
  exact isOpen_sUnion (by rintro _ ⟨i, rfl⟩; exact h i)

/-- If `U` and `V` are open, so is `U ∪ V`. Mathlib: `IsOpen.union`. -/
theorem IsOpen.union {U V : Set X} (hU : IsOpen U) (hV : IsOpen V) : IsOpen (U ∪ V) := by
  -- `U ∪ V = ⋃₀ {U, V}`, and both members are open. (Lean: `assumption`: the goal is one of the
  -- hypotheses.)
  rw [← sUnion_pair]
  exact isOpen_sUnion (by rintro W (rfl | rfl) <;> assumption)

/-- `X` is closed: its complement `∅` is open. Mathlib: `isClosed_univ`. -/
theorem isClosed_univ : IsClosed (univ : Set X) := by
  simpa [IsClosed] using (isOpen_empty : IsOpen (∅ : Set X))

/-- `∅` is closed: its complement `X` is open. Mathlib: `isClosed_empty`. -/
theorem isClosed_empty : IsClosed (∅ : Set X) := by
  simpa [IsClosed] using (isOpen_univ : IsOpen (univ : Set X))

/-- `X ∖ U` is open iff `U` is closed: the definition. Mathlib: `isOpen_compl_iff`. -/
theorem isOpen_compl_iff {U : Set X} : IsOpen Uᶜ ↔ IsClosed U := Iff.rfl

/-- If `U` is open, `X ∖ U` is closed, since `X ∖ (X ∖ U) = U`. Mathlib: `IsOpen.isClosed_compl`. -/
theorem IsOpen.isClosed_compl {U : Set X} (h : IsOpen U) : IsClosed Uᶜ := by
  simpa [IsClosed] using h

/-- If `C` and `D` are closed, so is `C ∪ D`. Mathlib: `IsClosed.union`. -/
theorem IsClosed.union {C D : Set X} (hC : IsClosed C) (hD : IsClosed D) :
    IsClosed (C ∪ D) := by
  -- De Morgan: `X ∖ (C ∪ D) = (X ∖ C) ∩ (X ∖ D)`, an intersection of two open sets.
  -- (Lean: `unfold IsClosed` replaces the word by its definition.)
  unfold IsClosed; rw [compl_union]; exact hC.inter hD

/-- If `C` and `D` are closed, so is `C ∩ D`. Mathlib: `IsClosed.inter`. -/
theorem IsClosed.inter {C D : Set X} (hC : IsClosed C) (hD : IsClosed D) :
    IsClosed (C ∩ D) := by
  -- De Morgan: `X ∖ (C ∩ D) = (X ∖ C) ∪ (X ∖ D)`, a union of two open sets.
  unfold IsClosed; rw [compl_inter]; exact IsOpen.union hC hD

/-- The intersection `⋂₀ 𝒞` of any family of closed sets is closed. Mathlib: `isClosed_sInter`. -/
theorem isClosed_sInter {𝒞 : Set (Set X)} (h : ∀ C ∈ 𝒞, IsClosed C) : IsClosed (⋂₀ 𝒞) := by
  -- De Morgan: `X ∖ ⋂₀ 𝒞` is the union of the open sets `X ∖ C`, `C ∈ 𝒞`.
  unfold IsClosed
  rw [compl_sInter]
  exact isOpen_sUnion (by rintro _ ⟨C, hC, rfl⟩; exact h C hC)

/-- The closure of `S`: the intersection of the closed sets containing it, so the smallest
closed set containing it (Analysis I 4.11(v)). Mathlib: `closure`. -/
def closure (S : Set X) : Set X := ⋂₀ {C | IsClosed C ∧ S ⊆ C}

/-- The closure is closed, as an intersection of closed sets. Mathlib: `isClosed_closure`. -/
theorem isClosed_closure (S : Set X) : IsClosed (closure S) :=
  isClosed_sInter fun _ hC => hC.1

/-- `S ⊆ closure S`: every set of the intersection contains `S`. Mathlib: `subset_closure`. -/
theorem subset_closure (S : Set X) : S ⊆ closure S :=
  subset_sInter fun _ hC => hC.2

/-- If `C` is closed and contains `S`, then `closure S ⊆ C`: `C` is one of the sets of the
intersection. Mathlib: `closure_minimal`. -/
theorem closure_minimal {S C : Set X} (hS : S ⊆ C) (hC : IsClosed C) : closure S ⊆ C :=
  sInter_subset_of_mem ⟨hC, hS⟩

end Basic

/-! ## The bridge to Mathlib's topological spaces

The bridges: a topology of the course and one of Mathlib's are the same four fields, so each
can be read as the other. Nothing in the course's proofs uses this section. -/

/-- The course's topology as Mathlib's: the same open sets. -/
def TopSpace.toMathlib (t : TopSpace X) : TopologicalSpace X where
  IsOpen := t.IsOpen
  isOpen_univ := t.isOpen_univ
  isOpen_inter := t.isOpen_inter
  isOpen_sUnion := t.isOpen_sUnion

/-- Mathlib's topology as the course's: the same open sets. -/
def TopSpace.ofMathlib (t : TopologicalSpace X) : TopSpace X where
  IsOpen := t.IsOpen
  isOpen_univ := t.isOpen_univ
  isOpen_inter := t.isOpen_inter
  isOpen_sUnion := t.isOpen_sUnion

/-- **Bridge.** The course's topologies on `X` are exactly Mathlib's `TopologicalSpace X`:
`toMathlib` and `ofMathlib` are inverse bijections (`≃`). Both round trips give back what we
started with by definition (`rfl`). -/
def TopSpace.equivMathlib : TopSpace X ≃ TopologicalSpace X where
  toFun := toMathlib
  invFun := ofMathlib
  left_inv _ := rfl
  right_inv _ := rfl

/-- **Bridge.** `U` is open for the course iff it is open for Mathlib (`_root_.IsOpen`), in the
same topology. The two say the same thing by definition (`Iff.rfl`).

Lean: `[t : TopSpace X]` names the instance `t`, so that we can write `t.toMathlib`; and
`@_root_.IsOpen X t.toMathlib U` says "`U` is open in Mathlib's sense, for the topology
`t.toMathlib`" (`@` lets us give that topology by hand instead of letting Lean find one). -/
theorem isOpen_iff_mathlib [t : TopSpace X] (U : Set X) :
    IsOpen U ↔ @_root_.IsOpen X t.toMathlib U := Iff.rfl

/-- **Bridge.** `C` is closed for the course iff it is closed for Mathlib. -/
theorem isClosed_iff_mathlib [t : TopSpace X] (C : Set X) :
    IsClosed C ↔ @_root_.IsClosed X t.toMathlib C := by
  -- Mathlib defines "closed" differently (as a structure), but proves that it means "the
  -- complement is open", which is the course's definition.
  let _ := t.toMathlib; exact _root_.isOpen_compl_iff (s := C)

/-! ## Continuous maps (Analysis I 4.18, 4.21; the book's `prop-1n-composite`) -/

section Continuity
variable [TopSpace X] [TopSpace Y] [TopSpace Z]

/-- `f : X → Y` is continuous: the preimage `f⁻¹(V)` of every open `V ⊆ Y` is open in `X`
(Analysis I 4.18). Mathlib: `Continuous`. -/
def Continuous (f : X → Y) : Prop := ∀ V : Set Y, IsOpen V → IsOpen (f ⁻¹' V)

/-- **Bridge.** `f` is continuous for the course iff it is for Mathlib. Mathlib defines
continuity as a structure with one field, "preimages of open sets are open"
(`continuous_def`); the proof unpacks and repacks that field, translating "open" both ways by
`isOpen_iff_mathlib`. -/
theorem continuous_iff_mathlib (f : X → Y) :
    Continuous f ↔ @_root_.Continuous X Y (‹TopSpace X›).toMathlib (‹TopSpace Y›).toMathlib f :=
  ⟨fun h => @Continuous.mk X Y (‹TopSpace X›).toMathlib (‹TopSpace Y›).toMathlib f
      fun V hV => (isOpen_iff_mathlib _).mp (h V ((isOpen_iff_mathlib V).mpr hV)),
    fun h V hV => (isOpen_iff_mathlib _).mpr
      (@Continuous.isOpen_preimage X Y (‹TopSpace X›).toMathlib (‹TopSpace Y›).toMathlib f h V
        ((isOpen_iff_mathlib V).mp hV))⟩

/-- `f` is continuous iff the preimage of every closed `C ⊆ Y` is closed (Analysis I 4.21).
Mathlib: `continuous_iff_isClosed`. -/
theorem continuous_iff_isClosed {f : X → Y} :
    Continuous f ↔ ∀ C : Set Y, IsClosed C → IsClosed (f ⁻¹' C) := by
  -- Both directions rest on `f⁻¹(Y ∖ C) = X ∖ f⁻¹(C)`: preimage commutes with complements.
  constructor
  · -- If `C` is closed, `Y ∖ C` is open, so `f⁻¹(Y ∖ C) = X ∖ f⁻¹(C)` is open.
    intro hf C hC
    unfold IsClosed; rw [← preimage_compl]; exact hf _ hC
  · -- If `V` is open, `Y ∖ V` is closed, so `f⁻¹(Y ∖ V) = X ∖ f⁻¹(V)` is closed.
    intro hf V hV
    have := hf Vᶜ (by simpa [IsClosed] using hV)
    simpa [IsClosed, preimage_compl] using this

/-- `prop-1n-composite`: every identity map is continuous, since `id⁻¹(V) = V`.
Mathlib: `continuous_id`. -/
theorem continuous_id : Continuous (id : X → X) := fun _ hV => hV

/-- `prop-1n-composite`: a composite of continuous maps is continuous:
`(g ∘ f)⁻¹(V) = f⁻¹(g⁻¹(V))` is open when `V` is. Mathlib: `Continuous.comp`.

Lean: the name `Continuous.comp` lets us write `hg.comp hf` for `Continuous.comp hg hf`. -/
theorem Continuous.comp {g : Y → Z} {f : X → Y} (hg : Continuous g) (hf : Continuous f) :
    Continuous (g ∘ f) := fun V hV => hf _ (hg V hV)

/-- A constant map `x ↦ y` is continuous. Mathlib: `continuous_const`. -/
theorem continuous_const {y : Y} : Continuous (fun _ : X => y) := by
  -- The preimage of `V` is `X` if `y ∈ V` and `∅` if not; both are open.
  intro V _
  by_cases hy : y ∈ V
  · simpa [preimage_const_of_mem hy] using (isOpen_univ : IsOpen (univ : Set X))
  · simpa [preimage_const_of_notMem hy] using (isOpen_empty : IsOpen (∅ : Set X))

end Continuity

/-! ## Bases (the book's `prop-1-10`, `prop-1n-5`) -/

section Bases
variable [TopSpace X]

/-- `𝓑` is a base: its members are open and every open set is a union of members
(Analysis I 4.14). Mathlib: `TopologicalSpace.IsTopologicalBasis` (see `isBase_iff_mathlib`). -/
def IsBase (𝓑 : Set (Set X)) : Prop :=
  (∀ B ∈ 𝓑, IsOpen B) ∧ ∀ U, IsOpen U → ∃ 𝒞 ⊆ 𝓑, U = ⋃₀ 𝒞

/-- A family `𝓑` of open sets is a base as soon as every open `U` contains, about each of its
points `x`, a member `B ∋ x` of `𝓑`: then `U` is the union of the members of `𝓑` inside it.
Mathlib: `TopologicalSpace.isTopologicalBasis_of_isOpen_of_nhds`. -/
theorem isBase_of_local {𝓑 : Set (Set X)} (hopen : ∀ B ∈ 𝓑, IsOpen B)
    (h : ∀ U, IsOpen U → ∀ x ∈ U, ∃ B ∈ 𝓑, x ∈ B ∧ B ⊆ U) : IsBase 𝓑 := by
  -- Take `𝒞 = {B ∈ 𝓑 | B ⊆ U}`; we show `U = ⋃₀ 𝒞`. (Lean: `refine ⟨a, ?_⟩` gives the parts we
  -- know now and leaves each `?_` as a goal; `ext x` reduces an equality of sets to
  -- "`x` is in one iff it is in the other".)
  refine ⟨hopen, fun U hU => ⟨{B | B ∈ 𝓑 ∧ B ⊆ U}, fun B hB => hB.1, ?_⟩⟩
  ext x
  constructor
  · -- `x ∈ U` lies in some `B ∈ 𝓑` with `B ⊆ U`, by the hypothesis.
    intro hx
    obtain ⟨B, hB, hxB, hBU⟩ := h U hU x hx
    exact ⟨B, ⟨hB, hBU⟩, hxB⟩
  · -- Each member of `𝒞` lies inside `U`.
    rintro ⟨B, ⟨_, hBU⟩, hxB⟩
    exact hBU hxB

/-- For a base `𝓑`, every open `U` contains, about each of its points `x`, a member `B ∋ x` of
`𝓑`. Mathlib: `TopologicalSpace.IsTopologicalBasis.exists_subset_of_mem_open`. -/
theorem IsBase.exists_subset {𝓑 : Set (Set X)} (h𝓑 : IsBase 𝓑) {U : Set X} (hU : IsOpen U)
    {x : X} (hx : x ∈ U) : ∃ B ∈ 𝓑, x ∈ B ∧ B ⊆ U := by
  -- `U = ⋃₀ 𝒞` with `𝒞 ⊆ 𝓑`, and `x` lies in some member `B` of `𝒞`, which lies inside `U`.
  -- (Lean: `obtain ⟨𝒞, h𝒞, rfl⟩` also replaces `U` by `⋃₀ 𝒞` everywhere.)
  obtain ⟨𝒞, h𝒞, rfl⟩ := h𝓑.2 U hU
  obtain ⟨B, hB, hxB⟩ := hx
  exact ⟨B, h𝒞 hB, hxB, subset_sUnion_of_mem hB⟩

/-- `prop-1-10`, the converse half: a base `𝓑` of any topology covers `X`, `⋃₀ 𝓑 = X`, and has
the intersection property: for `B₁, B₂ ∈ 𝓑` and `x ∈ B₁ ∩ B₂` there is `B₃ ∈ 𝓑` with
`x ∈ B₃ ⊆ B₁ ∩ B₂`. Mathlib: `TopologicalSpace.IsTopologicalBasis.sUnion_eq`,
`TopologicalSpace.IsTopologicalBasis.exists_subset_inter`. -/
theorem IsBase.criterion {𝓑 : Set (Set X)} (h𝓑 : IsBase 𝓑) :
    ⋃₀ 𝓑 = univ ∧ ∀ B₁ ∈ 𝓑, ∀ B₂ ∈ 𝓑, ∀ x ∈ B₁ ∩ B₂, ∃ B₃ ∈ 𝓑, x ∈ B₃ ∧ B₃ ⊆ B₁ ∩ B₂ := by
  refine ⟨?_, fun B₁ h₁ B₂ h₂ x hx => ?_⟩
  · -- `X` is open, so it is a union of members of `𝓑`: each `x` lies in one.
    apply eq_univ_of_forall
    intro x
    obtain ⟨B, hB, hxB, -⟩ := h𝓑.exists_subset isOpen_univ (mem_univ x)
    exact ⟨B, hB, hxB⟩
  · -- `B₁ ∩ B₂` is open, so it is a union of members of `𝓑`: one of them is the `B₃` about `x`.
    exact h𝓑.exists_subset ((h𝓑.1 B₁ h₁).inter (h𝓑.1 B₂ h₂)) hx

end Bases

/-- `prop-1-10`, the main half: if `𝓑` covers `X` (`hcover`) and has the intersection property
(`hinter`), then the unions of members of `𝓑` are the open sets of a topology on `X`.
Mathlib: `TopologicalSpace.generateFrom` (with `TopologicalSpace.IsTopologicalBasis`).

Lean: `def … where` builds the topology field by field: first the open sets, then a proof of
each of the three axioms. -/
def TopSpace.ofBase (𝓑 : Set (Set X)) (hcover : ⋃₀ 𝓑 = univ)
    (hinter : ∀ B₁ ∈ 𝓑, ∀ B₂ ∈ 𝓑, ∀ x ∈ B₁ ∩ B₂, ∃ B₃ ∈ 𝓑, x ∈ B₃ ∧ B₃ ⊆ B₁ ∩ B₂) :
    TopSpace X where
  -- The open sets: the unions `⋃₀ 𝒞` of subfamilies `𝒞 ⊆ 𝓑`.
  IsOpen U := ∃ 𝒞 ⊆ 𝓑, U = ⋃₀ 𝒞
  -- `X` is the union of all of `𝓑`, by the covering hypothesis.
  isOpen_univ := ⟨𝓑, subset_rfl, hcover.symm⟩
  isOpen_inter := by
    -- Let `U = ⋃₀ 𝒞` and `V = ⋃₀ 𝒟`. We show that `U ∩ V` is the union of the members of `𝓑`
    -- inside it.
    rintro _ _ ⟨𝒞, h𝒞, rfl⟩ ⟨𝒟, h𝒟, rfl⟩
    refine ⟨{B | B ∈ 𝓑 ∧ B ⊆ ⋃₀ 𝒞 ∩ ⋃₀ 𝒟}, fun B hB => hB.1, ?_⟩
    ext x
    constructor
    · -- Take `x ∈ U ∩ V`: then `x ∈ B` and `x ∈ C` for some `B ∈ 𝒞`, `C ∈ 𝒟`, and the
      -- intersection property gives `B₃ ∈ 𝓑` with `x ∈ B₃ ⊆ B ∩ C ⊆ U ∩ V`.
      rintro ⟨⟨B, hB, hxB⟩, ⟨C, hC, hxC⟩⟩
      obtain ⟨B₃, h₃, hx₃, h₃sub⟩ := hinter B (h𝒞 hB) C (h𝒟 hC) x ⟨hxB, hxC⟩
      exact ⟨B₃, ⟨h₃, fun y hy => ⟨⟨B, hB, (h₃sub hy).1⟩, ⟨C, hC, (h₃sub hy).2⟩⟩⟩, hx₃⟩
    · -- Conversely, each member of the union lies inside `U ∩ V`.
      rintro ⟨B, ⟨_, hBsub⟩, hxB⟩
      exact hBsub hxB
  isOpen_sUnion := by
    -- A union of unions is a union. Write each `U ∈ 𝒰` as `U = ⋃₀ 𝒞(U)` with `𝒞(U) ⊆ 𝓑`
    -- (Lean: `choose!` picks such a `𝒞(U)` for every `U` at once); then `⋃₀ 𝒰` is the union of
    -- all the families `𝒞(U)`, `U ∈ 𝒰`, put together.
    intro 𝒰 h𝒰
    choose! 𝒞 h𝒞 hU using h𝒰
    refine ⟨⋃₀ (𝒞 '' 𝒰), ?_, ?_⟩
    · -- That family is inside `𝓑`.
      rintro B ⟨_, ⟨U, hU𝒰, rfl⟩, hB⟩
      exact h𝒞 U hU𝒰 hB
    · -- Its union is `⋃₀ 𝒰`: `x` lies in some `U ∈ 𝒰` iff it lies in some `B ∈ 𝒞(U)`.
      ext x
      constructor
      · rintro ⟨U, hU𝒰, hxU⟩
        rw [hU U hU𝒰] at hxU
        obtain ⟨B, hB, hxB⟩ := hxU
        exact ⟨B, ⟨𝒞 U, ⟨U, hU𝒰, rfl⟩, hB⟩, hxB⟩
      · rintro ⟨B, ⟨_, ⟨U, hU𝒰, rfl⟩, hB⟩, hxB⟩
        refine ⟨U, hU𝒰, ?_⟩
        rw [hU U hU𝒰]
        exact ⟨B, hB, hxB⟩

/-- `prop-1-10`: `𝓑` is a base of the topology it generates: each `B ∈ 𝓑` is the union of
`{B}`, and every open set is a union of members of `𝓑` by definition.
Mathlib: `TopologicalSpace.IsTopologicalBasis`.

Lean: `@IsBase X (TopSpace.ofBase …) 𝓑` names the topology by hand (`@`), since `X` may carry
no topology that Lean would find by itself. -/
theorem TopSpace.isBase_ofBase (𝓑 : Set (Set X)) (hcover : ⋃₀ 𝓑 = univ)
    (hinter : ∀ B₁ ∈ 𝓑, ∀ B₂ ∈ 𝓑, ∀ x ∈ B₁ ∩ B₂, ∃ B₃ ∈ 𝓑, x ∈ B₃ ∧ B₃ ⊆ B₁ ∩ B₂) :
    @IsBase X (TopSpace.ofBase 𝓑 hcover hinter) 𝓑 :=
  ⟨fun B hB => ⟨{B}, singleton_subset_iff.mpr hB, (sUnion_singleton B).symm⟩, fun _ hU => hU⟩

/-- **Bridge.** `IsBase` is Mathlib's `TopologicalSpace.IsTopologicalBasis`. -/
theorem isBase_iff_mathlib [t : TopSpace X] (𝓑 : Set (Set X)) :
    IsBase 𝓑 ↔ @TopologicalSpace.IsTopologicalBasis X t.toMathlib 𝓑 := by
  -- Both say: the members are open, and every open set is the union of members (Mathlib's
  -- `isTopologicalBasis_of_isOpen_of_nhds` and `open_eq_sUnion` translate the two ways).
  -- (Lean: `let _ := t.toMathlib` makes Mathlib's topology available to Lean in this proof.)
  let _ := t.toMathlib
  constructor
  · intro h
    refine TopologicalSpace.isTopologicalBasis_of_isOpen_of_nhds (fun B hB => h.1 B hB) ?_
    intro x U hxU hU
    exact h.exists_subset hU hxU
  · intro h
    refine ⟨fun B hB => h.isOpen hB, fun U hU => ?_⟩
    obtain ⟨𝒞, h𝒞, hU⟩ := h.open_eq_sUnion hU
    exact ⟨𝒞, h𝒞, hU⟩

/-! ## Neighbourhood bases and the local criterion (`def-1-12`, `prop-1-13`) -/

section Local
variable [TopSpace X]

/-- `def-1-12`: a neighbourhood base at `x`, a family of neighbourhoods of `x` (open sets
containing `x`: the course's convention) such that every neighbourhood of `x` contains one.
Mathlib: `(nhds x).HasBasis`, for filters. -/
def IsNbhdBase (x : X) (𝓑x : Set (Set X)) : Prop :=
  (∀ B ∈ 𝓑x, IsOpen B ∧ x ∈ B) ∧ ∀ U, IsOpen U → x ∈ U → ∃ B ∈ 𝓑x, B ⊆ U

/-- `prop-1-13`, the local criterion: given a neighbourhood base at every point, `U` is open
iff it contains a member of the base at each of its points.
Mathlib: `isOpen_iff_mem_nhds` with `Filter.HasBasis.mem_iff`. -/
theorem isOpen_iff_local (𝓑 : X → Set (Set X)) (h𝓑 : ∀ x, IsNbhdBase x (𝓑 x)) (U : Set X) :
    IsOpen U ↔ ∀ x ∈ U, ∃ B ∈ 𝓑 x, B ⊆ U := by
  constructor
  · -- If `U` is open, it is a neighbourhood of each of its points `x`, so it contains a member
    -- of `𝓑ₓ`.
    intro hU x hx
    exact (h𝓑 x).2 U hU hx
  · -- Conversely, choose for each `x ∈ U` a member `Bₓ ∈ 𝓑ₓ` with `Bₓ ⊆ U`.
    intro h
    choose! B hB hBU using h
    -- Then `U = ⋃_{x ∈ U} Bₓ`: each `y ∈ U` lies in its own `B_y`, and each `Bₓ` lies in `U`.
    -- (Lean: `⋃ x : U, B x` is the union over the points `x` of `U`.)
    have : U = ⋃ x : U, B x := by
      ext y
      constructor
      · intro hy
        exact mem_iUnion.mpr ⟨⟨y, hy⟩, ((h𝓑 y).1 _ (hB y hy)).2⟩
      · intro hy
        obtain ⟨⟨x, hx⟩, hy⟩ := mem_iUnion.mp hy
        exact hBU x hx hy
    -- A union of open sets is open.
    rw [this]
    exact isOpen_iUnion fun ⟨x, hx⟩ => ((h𝓑 x).1 _ (hB x hx)).1

end Local

/-! ## The subspace topology (`def-1-14`, `def-1n-6`, `prop-1-15`, `prop-1-17`) -/

/-- `def-1-14`, `def-1n-6`: the subspace topology on `A ⊆ X`, whose open sets are the
`U ∩ A` with `U` open in `X`; in Lean a set `A` is the type of its points, and `U ∩ A` is the
preimage of `U` under the inclusion. That it is a topology is Analysis I 4.8.
Mathlib: `instTopologicalSpaceSubtype`, i.e. `TopologicalSpace.induced Subtype.val`.

Lean: a set `A : Set X` used as a type is the subtype `{x // x ∈ A}`: a point `a : A` is a pair
`⟨x, hx⟩` of a point `x : X` and a proof `hx : x ∈ A`. The inclusion `ι : A → X` is
`Subtype.val`, which forgets `hx`; Lean often prints `ι(a)` as `↑a`. So `Subtype.val ⁻¹' U` is
`ι⁻¹(U)`, the book's `U ∩ A`. `instance` (rather than `def`) makes this the topology Lean finds by
itself on every subset of a space: from now on `A` is a space whenever `X` is. -/
instance subspace [TopSpace X] (A : Set X) : TopSpace A where
  IsOpen V := ∃ U : Set X, IsOpen U ∧ V = Subtype.val ⁻¹' U
  -- `A = X ∩ A`.
  isOpen_univ := ⟨univ, isOpen_univ, rfl⟩
  -- `(U ∩ A) ∩ (U' ∩ A) = (U ∩ U') ∩ A`.
  isOpen_inter := by
    rintro _ _ ⟨U, hU, rfl⟩ ⟨U', hU', rfl⟩
    exact ⟨U ∩ U', hU.inter hU', rfl⟩
  isOpen_sUnion := by
    -- Write each `V ∈ 𝒱` as `V = U(V) ∩ A` with `U(V)` open in `X`; then
    -- `⋃₀ 𝒱 = (⋃_{V ∈ 𝒱} U(V)) ∩ A`, and that union is open in `X`.
    intro 𝒱 h𝒱
    choose! U hU hV using h𝒱
    refine ⟨⋃₀ (U '' 𝒱), isOpen_sUnion (by rintro _ ⟨V, hV𝒱, rfl⟩; exact hU V hV𝒱), ?_⟩
    ext a
    simp only [mem_sUnion, mem_preimage, mem_image, exists_exists_and_eq_and]
    -- `a` is in some `V ∈ 𝒱` iff `ι(a)` is in the corresponding `U(V)`.
    -- (Lean: `h ▸ e` rewrites `e` with the equation `h`.)
    constructor
    · rintro ⟨V, hV𝒱, haV⟩
      refine ⟨V, hV𝒱, ?_⟩
      have := hV V hV𝒱 ▸ haV
      exact this
    · rintro ⟨V, hV𝒱, haU⟩
      refine ⟨V, hV𝒱, ?_⟩
      rw [hV V hV𝒱]
      exact haU

section Subspace
variable [TopSpace X] {A : Set X}

/-- `V ⊆ A` is open in `A` iff `V = U ∩ A` with `U` open in `X`: the definition.
Mathlib: `isOpen_induced_iff`. -/
theorem isOpen_subspace_iff {V : Set A} :
    IsOpen V ↔ ∃ U : Set X, IsOpen U ∧ V = Subtype.val ⁻¹' U := Iff.rfl

/-- **Bridge.** The subspace topology is Mathlib's. Mathlib: `isOpen_induced_iff`.

Lean: `‹TopSpace X›` is the topology of `X` that Lean has found, written out. -/
theorem subspace_toMathlib (A : Set X) :
    (subspace A).toMathlib = @instTopologicalSpaceSubtype X A (‹TopSpace X›).toMathlib := by
  -- Mathlib's open sets of `A` are also the `ι⁻¹(U)` with `U` open (`isOpen_induced_iff`).
  let _ := (‹TopSpace X›).toMathlib
  apply TopologicalSpace.ext
  funext V
  apply propext
  rw [@isOpen_induced_iff]
  constructor
  · rintro ⟨U, hU, rfl⟩; exact ⟨U, hU, rfl⟩
  · rintro ⟨U, hU, rfl⟩; exact ⟨U, hU, rfl⟩

/-- `prop-1-15`: the inclusion `ι : A → X` of a subspace is continuous: `ι⁻¹(U) = U ∩ A` is
open in `A` by definition. Mathlib: `continuous_subtype_val`. -/
theorem continuous_subtype_val : Continuous (Subtype.val : A → X) :=
  fun U hU => ⟨U, hU, rfl⟩

/-- `prop-1-15`: the subspace topology is the coarsest making the inclusion continuous: if `τ`
is any topology on `A` for which `ι` is continuous (`hτ`), every open set `V` of the subspace
topology (`hV`) is open for `τ`. Mathlib: `continuous_iff_le_induced`.

Lean: `@Continuous A X τ _ Subtype.val` is "`ι` is continuous for the topology `τ` on `A`";
the `@` lets us name `τ`, and `_` lets Lean find the topology of `X`. -/
theorem subspace_coarsest (τ : TopSpace A) (hτ : @Continuous A X τ _ Subtype.val)
    (V : Set A) (hV : @IsOpen A (subspace A) V) : τ.IsOpen V := by
  -- `V = U ∩ A = ι⁻¹(U)` with `U` open in `X`, and `ι⁻¹(U)` is open for `τ` since `ι` is
  -- continuous for `τ`.
  obtain ⟨U, hU, rfl⟩ := hV
  exact hτ U hU

/-- `prop-1-17`, first part: `C ⊆ A` is closed in `A` iff `C = D ∩ A` with `D` closed in `X`.
Mathlib: `isClosed_induced_iff`. -/
theorem isClosed_subspace_iff {C : Set A} :
    IsClosed C ↔ ∃ D : Set X, IsClosed D ∧ C = Subtype.val ⁻¹' D := by
  constructor
  · -- `C` closed in `A` means `A ∖ C = U ∩ A` with `U` open in `X`; then `C = (X ∖ U) ∩ A`.
    rintro ⟨U, hU, hCU⟩
    refine ⟨Uᶜ, hU.isClosed_compl, ?_⟩
    rw [preimage_compl, ← hCU, compl_compl]
  · -- Conversely `A ∖ (D ∩ A) = (X ∖ D) ∩ A`, and `X ∖ D` is open.
    rintro ⟨D, hD, rfl⟩
    exact ⟨Dᶜ, hD, by rw [preimage_compl]⟩

/-- `prop-1-17`, second part: if `𝓑` is a base of `X`, then `{B ∩ A : B ∈ 𝓑}` is a base of `A`.
Mathlib: `TopologicalSpace.IsTopologicalBasis.isInducing`. -/
theorem IsBase.subspace {𝓑 : Set (Set X)} (h𝓑 : IsBase 𝓑) :
    IsBase ((fun B => Subtype.val ⁻¹' B) '' 𝓑 : Set (Set A)) := by
  refine ⟨?_, ?_⟩
  · -- Each `B ∩ A` is open in `A`, as `B` is open in `X`.
    rintro _ ⟨B, hB, rfl⟩
    exact ⟨B, h𝓑.1 B hB, rfl⟩
  · -- An open set of `A` is `U ∩ A` with `U = ⋃₀ 𝒞`, `𝒞 ⊆ 𝓑`; and intersecting a union with
    -- `A` distributes: `(⋃₀ 𝒞) ∩ A` is the union of the `B ∩ A`, `B ∈ 𝒞`.
    rintro _ ⟨U, hU, rfl⟩
    obtain ⟨𝒞, h𝒞, rfl⟩ := h𝓑.2 U hU
    refine ⟨(fun B => Subtype.val ⁻¹' B) '' 𝒞, image_mono h𝒞, ?_⟩
    rw [preimage_sUnion, sUnion_image]

/-- `prop-1-17`, third part: the closure of `S ⊆ A` in `A` is `S̄ ∩ A`, where `S̄` is the
closure of `S` in `X`. Lean writes `S̄ ∩ A` as `ι⁻¹(closure (ι(S)))`. Mathlib:
`closure_subtype`, `Topology.IsInducing.closure_eq_preimage_closure_image`. -/
theorem closure_subspace (S : Set A) :
    closure S = Subtype.val ⁻¹' closure (Subtype.val '' S) := by
  -- The closure of `S` in `A` is the smallest closed subset of `A` containing `S`
  -- (Analysis I 4.11(v)); we show it is `S̄ ∩ A` by inclusion both ways.
  apply Subset.antisymm
  · -- `⊆`: `S̄ ∩ A` contains `S` and is closed in `A` (first part), so it contains the
    -- smallest such set.
    apply closure_minimal
    · intro a ha
      exact subset_closure _ ⟨a, ha, rfl⟩
    · exact isClosed_subspace_iff.mpr ⟨_, isClosed_closure _, rfl⟩
  · -- `⊇`: by the first part, the closure of `S` in `A` is `D ∩ A` with `D` closed in `X`.
    -- Then `D ⊇ S`, so `D ⊇ S̄` (Analysis I 4.11(v) in `X`), and `D ∩ A ⊇ S̄ ∩ A`.
    obtain ⟨D, hD, hDeq⟩ := isClosed_subspace_iff.mp (isClosed_closure S)
    have hSD : Subtype.val '' S ⊆ D := by
      rintro _ ⟨a, ha, rfl⟩
      have : a ∈ Subtype.val ⁻¹' D := hDeq ▸ subset_closure S ha
      exact this
    rw [hDeq]
    exact preimage_mono (closure_minimal hSD hD)

end Subspace

/-! ## Continuity on a base or a subbase (`prop-1-19`) -/

section Subbase
variable [TopSpace X] [TopSpace Y]

/-- A finite intersection of open sets is open (from the axiom for two, by induction on the
number of sets). Mathlib: `Set.Finite.isOpen_sInter`. -/
theorem isOpen_sInter_of_finite {F : Set (Set X)} (hF : F.Finite) :
    (∀ S ∈ F, IsOpen S) → IsOpen (⋂₀ F) := by
  -- Induction on the finite family `F`: add one set at a time.
  induction F, hF using Set.Finite.induction_on with
  | empty =>
    -- The intersection of the empty family is `X`, which is open.
    intro _; simpa using (isOpen_univ : IsOpen (univ : Set X))
  | @insert S F _ _ ih =>
    -- `⋂₀ (F ∪ {S}) = S ∩ ⋂₀ F`, an intersection of two open sets (the second by induction,
    -- `ih`).
    intro h
    rw [sInter_insert]
    exact (h S (mem_insert _ _)).inter (ih fun T hT => h T (mem_insert_of_mem _ hT))

/-- `𝓢` is a subbase: its members are open, and every open set is a union of finite
intersections of members. Mathlib: `TopologicalSpace.generateFrom` (`t = generateFrom 𝓢`). -/
def IsSubbase (𝓢 : Set (Set X)) : Prop :=
  (∀ S ∈ 𝓢, IsOpen S) ∧
    ∀ U, IsOpen U → ∃ 𝒞 : Set (Set X), U = ⋃₀ 𝒞 ∧ ∀ C ∈ 𝒞, ∃ F ⊆ 𝓢, F.Finite ∧ C = ⋂₀ F

/-- A base is a subbase: each member `C` is the intersection of the family `{C}`.
Mathlib: `TopologicalSpace.IsTopologicalBasis.eq_generateFrom`. -/
theorem IsBase.isSubbase {𝓑 : Set (Set X)} (h : IsBase 𝓑) : IsSubbase 𝓑 := by
  refine ⟨h.1, fun U hU => ?_⟩
  obtain ⟨𝒞, h𝒞, rfl⟩ := h.2 U hU
  exact ⟨𝒞, rfl, fun C hC => ⟨{C}, singleton_subset_iff.mpr (h𝒞 hC), finite_singleton C,
    (sInter_singleton C).symm⟩⟩

/-- `prop-1-19`: for a subbase `𝓢` of `Y`, `f` is continuous iff the preimage of every member
of `𝓢` is open. Mathlib: `continuous_generateFrom_iff`. -/
theorem continuous_iff_subbase {𝓢 : Set (Set Y)} (h𝓢 : IsSubbase 𝓢) {f : X → Y} :
    Continuous f ↔ ∀ S ∈ 𝓢, IsOpen (f ⁻¹' S) := by
  constructor
  · -- The members of `𝓢` are open, so their preimages are open if `f` is continuous.
    intro hf S hS
    exact hf S (h𝓢.1 S hS)
  · -- Conversely, an open `V ⊆ Y` is a union `⋃₀ 𝒞` of finite intersections of members of `𝓢`.
    -- Preimage commutes with unions: `f⁻¹(⋃₀ 𝒞) = ⋃_{C ∈ 𝒞} f⁻¹(C)`, so it is enough that each
    -- `f⁻¹(C)` is open.
    intro h V hV
    obtain ⟨𝒞, rfl, h𝒞⟩ := h𝓢.2 V hV
    rw [preimage_sUnion]
    refine isOpen_iUnion fun C => isOpen_iUnion fun hC => ?_
    -- `C = ⋂₀ F` with `F ⊆ 𝓢` finite, and preimage commutes with intersections:
    -- `f⁻¹(⋂₀ F) = ⋂_{S ∈ F} f⁻¹(S)`, a finite intersection of open sets.
    obtain ⟨F, hF𝓢, hFfin, rfl⟩ := h𝒞 C hC
    rw [preimage_sInter, ← sInter_image]
    exact isOpen_sInter_of_finite (hFfin.image _) (by
      rintro _ ⟨S, hS, rfl⟩
      exact h S (hF𝓢 hS))

/-- `prop-1-19` for a base: `f` is continuous iff `f⁻¹(B)` is open for every `B ∈ 𝓑`, since a
base is a subbase. Mathlib: `TopologicalSpace.IsTopologicalBasis.continuous_iff`. -/
theorem continuous_iff_base {𝓑 : Set (Set Y)} (h𝓑 : IsBase 𝓑) {f : X → Y} :
    Continuous f ↔ ∀ B ∈ 𝓑, IsOpen (f ⁻¹' B) :=
  continuous_iff_subbase h𝓑.isSubbase

end Subbase

/-! ## Gluing (`prop-1-20`, `prop-1n-7`) -/

section Gluing
variable [TopSpace X] [TopSpace Y]

/-- A set closed in a closed subspace is closed in the whole space (by `prop-1-17`, it is
`D ∩ A` with `D` closed). Mathlib: `IsClosed.isClosedMap_subtype_val`. -/
theorem IsClosed.image_val {A : Set X} (hA : IsClosed A) {E : Set A} (hE : IsClosed E) :
    IsClosed (Subtype.val '' E) := by
  -- `E = D ∩ A` with `D` closed in `X`, and `A` is closed: an intersection of two closed sets.
  -- (Lean: `Subtype.val '' E` is `E` seen as a subset of `X`.)
  obtain ⟨D, hD, rfl⟩ := isClosed_subspace_iff.mp hE
  rw [Subtype.image_preimage_coe]
  exact hA.inter hD

/-- A set open in an open subspace is open in the whole space (Analysis I 4.9).
Mathlib: `IsOpen.isOpenMap_subtype_val`. -/
theorem IsOpen.image_val {A : Set X} (hA : IsOpen A) {E : Set A} (hE : IsOpen E) :
    IsOpen (Subtype.val '' E) := by
  -- `E = U ∩ A` with `U` open in `X`, and `A` is open: an intersection of two open sets.
  obtain ⟨U, hU, rfl⟩ := hE
  rw [Subtype.image_preimage_coe]
  exact hA.inter hU

/-- `prop-1-20`, `prop-1n-7`, the gluing lemma for two closed sets: if `X = C₁ ∪ C₂` with both
closed (`h₁`, `h₂`, `hcover`) and the restrictions `f|C₁`, `f|C₂` are continuous (`hf₁`, `hf₂`),
then `f` is continuous. Mathlib: `Continuous.piecewise`, `continuous_if`.

Lean: `fun x : C₁ => f x` is the restriction `f|C₁ : C₁ → Y`; for a point `x` of the subspace
`C₁`, `f x` means `f(ι(x))`. -/
theorem continuous_of_closed_cover {C₁ C₂ : Set X} (h₁ : IsClosed C₁) (h₂ : IsClosed C₂)
    (hcover : C₁ ∪ C₂ = univ) {f : X → Y}
    (hf₁ : Continuous (fun x : C₁ => f x)) (hf₂ : Continuous (fun x : C₂ => f x)) :
    Continuous f := by
  -- By Analysis I 4.21 (`continuous_iff_isClosed`), it suffices that `f⁻¹(F)` is closed for
  -- every closed `F ⊆ Y`.
  rw [continuous_iff_isClosed]
  intro F hF
  -- Step 1. `f⁻¹(F) = (f|C₁)⁻¹(F) ∪ (f|C₂)⁻¹(F)`, the pieces seen as subsets of `X`, since every
  -- point lies in `C₁` or in `C₂`.
  have : f ⁻¹' F = Subtype.val '' ((fun x : C₁ => f x) ⁻¹' F) ∪
      Subtype.val '' ((fun x : C₂ => f x) ⁻¹' F) := by
    ext x
    constructor
    · intro hx
      have : x ∈ C₁ ∪ C₂ := hcover ▸ mem_univ x
      rcases this with hx₁ | hx₂
      · exact Or.inl ⟨⟨x, hx₁⟩, hx, rfl⟩
      · exact Or.inr ⟨⟨x, hx₂⟩, hx, rfl⟩
    · rintro (⟨⟨y, _⟩, hy, rfl⟩ | ⟨⟨y, _⟩, hy, rfl⟩) <;> exact hy
  rw [this]
  -- Step 2. Each piece is closed in `Cᵢ`, as `f|Cᵢ` is continuous, hence closed in `X` because
  -- `Cᵢ` is (`IsClosed.image_val`); and a union of two closed sets is closed.
  exact (h₁.image_val (continuous_iff_isClosed.mp hf₁ F hF)).union
    (h₂.image_val (continuous_iff_isClosed.mp hf₂ F hF))

/-- `prop-1-20`, `prop-1n-7`, the gluing lemma for any cover by open sets: if `X = ⋃ᵢ Uᵢ` with
every `Uᵢ` open and every restriction `f|Uᵢ` continuous, then `f` is continuous.
Mathlib: `continuous_of_cover_nhds`, `IsOpenCover.continuous_iff_restrict`. -/
theorem continuous_of_open_cover {ι : Sort*} {U : ι → Set X} (hU : ∀ i, IsOpen (U i))
    (hcover : ⋃ i, U i = univ) {f : X → Y} (hf : ∀ i, Continuous (fun x : U i => f x)) :
    Continuous f := by
  -- Take an open `V ⊆ Y`. Step 1. `f⁻¹(V) = ⋃ᵢ (f|Uᵢ)⁻¹(V)`, the pieces seen as subsets of `X`,
  -- since every point lies in some `Uᵢ`.
  intro V hV
  have : f ⁻¹' V = ⋃ i, Subtype.val '' ((fun x : U i => f x) ⁻¹' V) := by
    ext x
    constructor
    · intro hx
      obtain ⟨i, hi⟩ := mem_iUnion.mp (hcover ▸ mem_univ x)
      exact mem_iUnion.mpr ⟨i, ⟨x, hi⟩, hx, rfl⟩
    · intro hx
      obtain ⟨i, ⟨y, _⟩, hy, rfl⟩ := mem_iUnion.mp hx
      exact hy
  -- Step 2. Each piece is open in `Uᵢ`, hence open in `X` because `Uᵢ` is (`IsOpen.image_val`);
  -- and a union of open sets is open.
  rw [this]
  exact isOpen_iUnion fun i => (hU i).image_val (hf i V hV)

end Gluing

/-! ## Open maps, closed maps, homeomorphisms (`def-1-21`, `prop-1-22`, `prop-1n-8`) -/

section Homeomorphisms
variable [TopSpace X] [TopSpace Y]

/-- `def-1-21`: `f` is open if it sends open sets to open sets. Mathlib: `IsOpenMap`. -/
def IsOpenMap (f : X → Y) : Prop := ∀ U : Set X, IsOpen U → IsOpen (f '' U)

/-- `def-1-21`: `f` is closed if it sends closed sets to closed sets. Mathlib: `IsClosedMap`. -/
def IsClosedMap (f : X → Y) : Prop := ∀ C : Set X, IsClosed C → IsClosed (f '' C)

variable (X Y) in
/-- A homeomorphism: a bijection, continuous with continuous inverse (Analysis I 4.18, recalled
in `def-1-21`). Mathlib: `Homeomorph` (see `Homeomorph.toMathlib`).

Lean: `extends X ≃ Y` says that a homeomorphism `h` is first of all a bijection `h.toEquiv`,
given as a pair of inverse maps `toFun : X → Y` and `invFun : Y → X`, to which we add the two
fields below. (`variable (X Y) in` makes `X`, `Y` explicit: we write `Homeomorph X Y`.) -/
structure Homeomorph extends X ≃ Y where
  /-- The map `X → Y` is continuous. -/
  continuous_toFun : Continuous toFun
  /-- The inverse `Y → X` is continuous. -/
  continuous_invFun : Continuous invFun

/-- **Bridge.** A homeomorphism of the course is one of Mathlib's: the same bijection, with
continuity translated by `continuous_iff_mathlib`. -/
def Homeomorph.toMathlib (h : Homeomorph X Y) :
    @_root_.Homeomorph X Y (‹TopSpace X›).toMathlib (‹TopSpace Y›).toMathlib :=
  @_root_.Homeomorph.mk X Y (‹TopSpace X›).toMathlib (‹TopSpace Y›).toMathlib h.toEquiv
    ((continuous_iff_mathlib _).mp h.continuous_toFun)
    ((continuous_iff_mathlib _).mp h.continuous_invFun)

/-- **Bridge.** And conversely. -/
def Homeomorph.ofMathlib
    (h : @_root_.Homeomorph X Y (‹TopSpace X›).toMathlib (‹TopSpace Y›).toMathlib) :
    Homeomorph X Y where
  toEquiv := @_root_.Homeomorph.toEquiv X Y (‹TopSpace X›).toMathlib (‹TopSpace Y›).toMathlib h
  continuous_toFun := (continuous_iff_mathlib _).mpr
    (@_root_.Homeomorph.continuous_toFun X Y (‹TopSpace X›).toMathlib (‹TopSpace Y›).toMathlib h)
  continuous_invFun := (continuous_iff_mathlib _).mpr
    (@_root_.Homeomorph.continuous_invFun X Y (‹TopSpace X›).toMathlib (‹TopSpace Y›).toMathlib h)

/-- `prop-1-22`, `prop-1n-8`: for a continuous bijection `f`, being a homeomorphism (that is,
having a continuous inverse) is the same as being open. For a bijection
`f(U) = (f⁻¹)⁻¹(U)`, so "`f` is open" says that `f⁻¹` is continuous.
Mathlib: `Homeomorph.homeomorphOfContinuousOpen`, `Homeomorph.isOpenMap`. -/
theorem homeomorph_iff_isOpenMap {f : X → Y} (hf : Continuous f) (hbij : Function.Bijective f) :
    (∃ h : Homeomorph X Y, ⇑h.toEquiv = f) ↔ IsOpenMap f := by
  -- The statement reads: "there is a homeomorphism `h` whose map is `f`" iff "`f` is open".
  -- (Lean: `⇑h.toEquiv` is the bijection `h.toEquiv` used as a map.)
  constructor
  · -- If `f` is a homeomorphism, `f(U) = (f⁻¹)⁻¹(U)` is open for open `U`, since `f⁻¹` is
    -- continuous.
    rintro ⟨h, rfl⟩ U hU
    rw [Equiv.image_eq_preimage_symm]
    exact h.continuous_invFun U hU
  · -- If `f` is open: let `e` be `f` with its inverse `f⁻¹` (`f` is a bijection). Then
    -- `(f⁻¹)⁻¹(U) = f(U)` is open for open `U`, so `f⁻¹` is continuous.
    intro hopen
    let e := Equiv.ofBijective f hbij
    refine ⟨⟨e, hf, fun U hU => ?_⟩, rfl⟩
    have : e.invFun ⁻¹' U = f '' U := by
      change e.symm ⁻¹' U = f '' U
      rw [← Equiv.image_eq_preimage_symm]
      rfl
    rw [this]
    exact hopen U hU

/-- `prop-1-22`, `prop-1n-8`: for a bijection, open and closed are the same, since
`f(X ∖ C) = Y ∖ f(C)`. Mathlib: `Homeomorph.isClosedMap`, `Set.image_compl_eq`. -/
theorem isOpenMap_iff_isClosedMap {f : X → Y} (hbij : Function.Bijective f) :
    IsOpenMap f ↔ IsClosedMap f := by
  constructor
  · -- `f` open, `C` closed: `Y ∖ f(C) = f(X ∖ C)` is open.
    intro h C hC
    unfold IsClosed
    rw [← image_compl_eq hbij]
    exact h _ hC
  · -- `f` closed, `U` open: `f(X ∖ U) = Y ∖ f(U)` is closed, so `f(U)` is open.
    -- (Lean: `rwa` is `rw` followed by `assumption`.)
    intro h U hU
    have := h Uᶜ (hU.isClosed_compl)
    unfold IsClosed at this
    rwa [image_compl_eq hbij, compl_compl] at this

end Homeomorphisms

/-! ## Topological properties (`def-1-27`, `prop-1-28`) -/

/-- `def-1-27`: a property `P` of spaces preserved by every homeomorphism: if `X ≅ Y` and `X`
has `P`, so does `Y`. Mathlib: no counterpart (Mathlib states each invariance separately).

Lean: `P : ∀ (X : Type u) [TopSpace X], Prop` is a property of spaces: for each set `X` with a
topology, a statement `P X`. -/
def IsTopologicalProperty (P : ∀ (X : Type u) [TopSpace X], Prop) : Prop :=
  ∀ (X Y : Type u) [TopSpace X] [TopSpace Y], Homeomorph X Y → P X → P Y

section Properties
variable [TopSpace X] [TopSpace Y]

/-- `prop-1-28`: a homeomorphism `f` induces a bijection `𝒯 → 𝒯'` of the open sets,
`U ↦ f(U)` (by `prop-1-22`, `f` is open, and so is its inverse). Mathlib: `Homeomorph.isOpen_image`.

Lean: `{U : Set X // IsOpen U}` is the set `𝒯` of open subsets of `X`; an element is a pair
`⟨U, hU⟩` of a set `U = U.1` and a proof `hU = U.2` that it is open. -/
def Homeomorph.opensEquiv (h : Homeomorph X Y) :
    {U : Set X // IsOpen U} ≃ {V : Set Y // IsOpen V} where
  -- `U ↦ f(U)`, open because `f(U) = (f⁻¹)⁻¹(U)` and `f⁻¹` is continuous.
  toFun U := ⟨h.toEquiv '' U.1, by
    rw [Equiv.image_eq_preimage_symm]; exact h.continuous_invFun U.1 U.2⟩
  -- `V ↦ f⁻¹(V)`, open because `f` is continuous.
  invFun V := ⟨h.toEquiv.symm '' V.1, by
    rw [Equiv.image_symm_eq_preimage]; exact h.continuous_toFun V.1 V.2⟩
  -- The two are inverse: `f⁻¹(f(U)) = U` and `f(f⁻¹(V)) = V`.
  left_inv U := by simp
  right_inv V := by simp

/-- `prop-1-28`: `{x}` is open iff `{f(x)}` is, so a homeomorphism `f` gives a bijection
between the isolated points of `X` and those of `Y`. Mathlib: `Homeomorph.isOpen_image`. -/
def Homeomorph.isolatedEquiv (h : Homeomorph X Y) :
    {x : X // IsOpen ({x} : Set X)} ≃ {y : Y // IsOpen ({y} : Set Y)} where
  -- `x ↦ f(x)`: `{f(x)} = f({x})` is open, by the bijection of open sets above.
  toFun x := ⟨h.toEquiv x.1, by
    have := (h.opensEquiv ⟨{x.1}, x.2⟩).2
    simpa [Homeomorph.opensEquiv, image_singleton] using this⟩
  -- `y ↦ f⁻¹(y)`, in the same way.
  invFun y := ⟨h.toEquiv.symm y.1, by
    have := (h.opensEquiv.symm ⟨{y.1}, y.2⟩).2
    simpa [Homeomorph.opensEquiv, image_singleton] using this⟩
  left_inv x := by simp
  right_inv y := by simp

end Properties

/-- `prop-1-28`: cardinality is a topological property: "`X` has `κ` points" passes to every
`Y ≅ X`. Mathlib: `Cardinal.mk_congr`.

Lean: `Cardinal.mk X` is the cardinality `|X|`; `fun X _ => …` is the property, and `_` stands
for the topology of `X`, which it does not use. -/
theorem isTopologicalProperty_card (κ : Cardinal.{u}) :
    IsTopologicalProperty fun X _ => Cardinal.mk X = κ := by
  -- A homeomorphism is a bijection `X → Y`, so `|Y| = |X| = κ`.
  intro X Y _ _ h hX
  rw [← hX]
  exact (Cardinal.mk_congr h.toEquiv).symm

/-- `prop-1-28`: the number of open sets is a topological property. Mathlib:
`Cardinal.mk_congr`. -/
theorem isTopologicalProperty_card_opens (κ : Cardinal.{u}) :
    IsTopologicalProperty fun X _ => Cardinal.mk {U : Set X // IsOpen U} = κ := by
  -- The open sets of `X` and of `Y` are in bijection, `U ↦ f(U)` (`Homeomorph.opensEquiv`).
  intro X Y _ _ h hX
  rw [← hX]
  exact (Cardinal.mk_congr h.opensEquiv).symm

/-- `prop-1-28`: the number of isolated points is a topological property. Mathlib:
`Cardinal.mk_congr`. -/
theorem isTopologicalProperty_card_isolated (κ : Cardinal.{u}) :
    IsTopologicalProperty fun X _ => Cardinal.mk {x : X // IsOpen ({x} : Set X)} = κ := by
  -- The isolated points of `X` and of `Y` are in bijection, `x ↦ f(x)`
  -- (`Homeomorph.isolatedEquiv`).
  intro X Y _ _ h hX
  rw [← hX]
  exact (Cardinal.mk_congr h.isolatedEquiv).symm

/-! ## Pseudo-metrics and their topology (`def-1-1`, `def-1n-1`) -/

/-- `def-1-1`, `def-1n-1`: a pseudo-metric, every condition of a metric (Analysis I 1.1) except
that `d x y = 0` is allowed for `x ≠ y`. Mathlib: `PseudoMetricSpace` (see `toMathlib`).

Lean: a `structure` is a definition by fields: a pseudo-metric `m` is the distance function
`m.d : X → X → ℝ` (so `m.d x y` is `d(x, y)`) together with proofs of the four conditions. -/
structure PseudoMetric (X : Type u) where
  /-- The distance `d(x, y)`. -/
  d : X → X → ℝ
  /-- `d(x, y) ≥ 0`. -/
  nonneg : ∀ x y, 0 ≤ d x y
  /-- `d(x, x) = 0`. -/
  self : ∀ x, d x x = 0
  /-- `d(x, y) = d(y, x)`. -/
  symm : ∀ x y, d x y = d y x
  /-- The triangle inequality `d(x, z) ≤ d(x, y) + d(y, z)`. -/
  triangle : ∀ x y z, d x z ≤ d x y + d y z

namespace PseudoMetric

-- In this namespace `m` is a pseudo-metric on `X`, and `m.ball`, `m.toTopSpace`, … are its
-- balls, its topology, ….
variable (m : PseudoMetric X)

/-- The open ball `{y | d(x, y) < r}`. Mathlib: `Metric.ball` (which writes `dist y x`). -/
def ball (x : X) (r : ℝ) : Set X := {y | m.d x y < r}

/-- A ball about `y` contains a ball about each of its points `x`, of radius `r - d(y, x)`.
Mathlib: `Metric.ball_subset_ball'`. -/
theorem ball_subset_ball {x y : X} {r : ℝ} (_hx : x ∈ m.ball y r) :
    m.ball x (r - m.d y x) ⊆ m.ball y r := by
  -- If `d(x, z) < r - d(y, x)`, then `d(y, z) ≤ d(y, x) + d(x, z) < r`, by the triangle
  -- inequality.
  intro z hz
  have := m.triangle y x z
  simp only [ball, mem_ofPred_eq] at hz ⊢
  linarith

/-- The balls of positive radius. -/
def balls : Set (Set X) := {B | ∃ x, ∃ r > 0, B = m.ball x r}

/-- `def-1n-1`: the balls are a base for a topology, by the base criterion `prop-1-10`
(Analysis I 4.2(iii), 4.14(i)); definiteness is never needed.
Mathlib: `PseudoMetricSpace.toUniformSpace`, `UniformSpace.toTopologicalSpace`. -/
def toTopSpace : TopSpace X :=
  -- We check the two hypotheses of the base criterion (`TopSpace.ofBase`).
  TopSpace.ofBase m.balls
    -- The balls cover `X`: `x` lies in its own ball of radius `1`, as `d(x, x) = 0 < 1`.
    (by
      apply eq_univ_of_forall
      intro x
      exact ⟨m.ball x 1, ⟨x, 1, one_pos, rfl⟩, by simp [ball, m.self]⟩)
    -- The intersection property. Let `z` lie in the balls `B(x₁, r₁)` and `B(x₂, r₂)`. Then
    -- `rᵢ - d(xᵢ, z) > 0`, and the ball about `z` of radius `ρ = min(r₁ - d(x₁, z), r₂ - d(x₂, z))`
    -- contains `z` and lies in both (`ball_subset_ball`).
    (by
      rintro _ ⟨x₁, r₁, hr₁, rfl⟩ _ ⟨x₂, r₂, hr₂, rfl⟩ z ⟨hz₁, hz₂⟩
      have h₁ : 0 < r₁ - m.d x₁ z := by simp only [ball, mem_ofPred_eq] at hz₁; linarith
      have h₂ : 0 < r₂ - m.d x₂ z := by simp only [ball, mem_ofPred_eq] at hz₂; linarith
      refine ⟨m.ball z (min (r₁ - m.d x₁ z) (r₂ - m.d x₂ z)), ⟨z, _, lt_min h₁ h₂, rfl⟩,
        by simp [ball, m.self, h₁, h₂], fun y hy => ⟨?_, ?_⟩⟩
      · -- `d(z, y) < ρ ≤ r₁ - d(x₁, z)`, so `y ∈ B(x₁, r₁)`.
        exact m.ball_subset_ball hz₁
          (show m.d z y < _ from lt_of_lt_of_le (show m.d z y < _ from hy) (min_le_left _ _))
      · -- `d(z, y) < ρ ≤ r₂ - d(x₂, z)`, so `y ∈ B(x₂, r₂)`.
        exact m.ball_subset_ball hz₂
          (show m.d z y < _ from lt_of_lt_of_le (show m.d z y < _ from hy) (min_le_right _ _)))

/-- `def-1n-1`: the balls are a base of `m.toTopSpace` (`prop-1-10`).
Mathlib: `Metric.nhds_basis_ball` (the balls about `x` are a neighbourhood base at `x`). -/
theorem isBase_balls : @IsBase X m.toTopSpace m.balls := TopSpace.isBase_ofBase _ _ _

/-- The open sets of a pseudo-metric: `U` is open iff it contains a ball about each of its
points (Analysis I 4.2(iii)). Mathlib: `Metric.isOpen_iff`. -/
theorem isOpen_iff (U : Set X) :
    @IsOpen X m.toTopSpace U ↔ ∀ x ∈ U, ∃ ε > 0, m.ball x ε ⊆ U := by
  constructor
  · -- If `U` is open and `x ∈ U`, some ball `B(y, r)` has `x ∈ B(y, r) ⊆ U`, since the balls
    -- are a base; and the ball about `x` of radius `ε = r - d(y, x) > 0` lies in `B(y, r)`.
    intro hU x hx
    obtain ⟨_, ⟨y, r, -, rfl⟩, hxB, hBU⟩ := @IsBase.exists_subset X m.toTopSpace _ m.isBase_balls
      U hU x hx
    exact ⟨r - m.d y x, by simp only [ball, mem_ofPred_eq] at hxB; linarith,
      (m.ball_subset_ball hxB).trans hBU⟩
  · -- Conversely, choose for each `x ∈ U` a radius `εₓ > 0` with `B(x, εₓ) ⊆ U`; then `U` is
    -- the union of these balls, a union of members of the base.
    intro h
    choose! ε hε hεU using h
    refine ⟨{B | ∃ x ∈ U, B = m.ball x (ε x)}, ?_, ?_⟩
    · rintro _ ⟨x, hx, rfl⟩; exact ⟨x, ε x, hε x hx, rfl⟩
    · ext y
      constructor
      · intro hy; exact ⟨_, ⟨y, hy, rfl⟩, by simp [ball, m.self, hε y hy]⟩
      · rintro ⟨_, ⟨x, hx, rfl⟩, hyB⟩; exact hεU x hx hyB

/-- Every ball `B(x, r)` is open (also for `r ≤ 0`, when it is empty). Mathlib:
`Metric.isOpen_ball`. -/
theorem isOpen_ball (x : X) (r : ℝ) : @IsOpen X m.toTopSpace (m.ball x r) := by
  -- About each `y ∈ B(x, r)`, the ball of radius `r - d(x, y) > 0` lies in `B(x, r)`.
  rw [isOpen_iff]
  intro y hy
  exact ⟨r - m.d x y, by simp only [ball, mem_ofPred_eq] at hy; linarith, m.ball_subset_ball hy⟩

/-- **Bridge.** The pseudo-metric as Mathlib's `PseudoMetricSpace`. -/
noncomputable def toMathlib : PseudoMetricSpace X where
  dist := m.d
  dist_self := m.self
  dist_comm := m.symm
  dist_triangle := m.triangle

/-- **Bridge.** The course's topology of a pseudo-metric is Mathlib's.
Mathlib: `Metric.isOpen_iff`. -/
theorem toTopSpace_toMathlib :
    m.toTopSpace.toMathlib = m.toMathlib.toUniformSpace.toTopologicalSpace := by
  -- Both say: `U` is open iff it contains a ball about each of its points (`isOpen_iff` and
  -- Mathlib's `Metric.isOpen_iff`); Mathlib's ball `{y | d(y, x) < ε}` is ours by symmetry.
  let _ := m.toMathlib
  apply TopologicalSpace.ext
  funext U
  apply propext
  change @IsOpen X m.toTopSpace U ↔ _
  rw [m.isOpen_iff, Metric.isOpen_iff]
  have hball : ∀ x ε, Metric.ball x ε = m.ball x ε := by
    intro x ε; ext y
    change m.d y x < ε ↔ m.d x y < ε
    rw [m.symm]
  simp only [hball]

end PseudoMetric

/-! ## The space of words (`def-1-4`, `ex-1n-3`, `prop-1-5`)

The book indexes the letters of a word from 1, `w = w₁w₂w₃⋯`; here a word is `w : ℕ → A` and
its letters are `w 0, w 1, …`, so the book's `wᵢ` is `w (i - 1)`, and the first difference
`k = min {i : vᵢ ≠ wᵢ}` of the book is `firstDiff v w + 1`. So the book's `d(v, w) = 2^{-k}` is
`(1/2)^(firstDiff + 1)` here, and "`v`, `w` agree on the first `n` letters" is
`∀ i < n, v i = w i`. A finite word `u` of length `n` is `u : Fin n → A`, where
`Fin n = {0, 1, …, n - 1}`. -/

namespace Words

-- `A` is the alphabet. The book takes it finite with at least two letters; nothing below needs
-- that.
variable {A : Type u}

open Classical in
/-- The first index (from 0) at which two different words differ: the least `i` with
`v i ≠ w i`, which exists because `v ≠ w`. The book's `k` is `firstDiff + 1`.

Lean: `Nat.find` is the least natural number with a property, given a proof that there is one;
`open Classical` lets us use it for any property, decidable or not. -/
noncomputable def firstDiff {v w : ℕ → A} (h : v ≠ w) : ℕ :=
  Nat.find (Function.ne_iff.mp h)

open Classical in
/-- `def-1-4`: `d(v, w) = 2^{-k}` with `k` the first (1-based) place where `v` and `w` differ,
and `d(w, w) = 0`. Mathlib: the metric of `PiNat` (`PiNat.dist`), which is the same formula.

Lean: `if h : v = w then … else …` is a definition by cases, and in the second case `h` is the
proof of `v ≠ w` that `firstDiff` needs. -/
noncomputable def dist (v w : ℕ → A) : ℝ :=
  if h : v = w then 0 else (1 / 2 : ℝ) ^ (firstDiff h + 1)

/-- `def-1-4`: the cylinder `C_u` of the finite word `u` (of length `n`): the words that
begin with `u`. Mathlib: `PiNat.cylinder`. -/
def cylinder {n : ℕ} (u : Fin n → A) : Set (ℕ → A) := {w | ∀ i : Fin n, w i = u i}

/-- The first `n` letters `w 0, …, w (n - 1)` of a word, as a finite word. -/
def prefix_ (n : ℕ) (w : ℕ → A) : Fin n → A := fun i => w i

/-- `d(w, w) = 0`. Mathlib: `dist_self`. -/
theorem dist_self (w : ℕ → A) : dist w w = 0 := by simp [dist]

/-- For `v ≠ w`, `d(v, w) = 2^{-k}`, `k = firstDiff + 1`: unfolding the definition. -/
theorem dist_of_ne {v w : ℕ → A} (h : v ≠ w) : dist v w = (1 / 2 : ℝ) ^ (firstDiff h + 1) := by
  simp [dist, h]

/-- `d(v, w) ≥ 0`: it is `0` or a power of `1/2`. Mathlib: `dist_nonneg`. -/
theorem dist_nonneg (v w : ℕ → A) : 0 ≤ dist v w := by
  unfold dist; split_ifs <;> positivity

/-- The distance takes only the values `0` and `2^{-k}`, `k ≥ 1`. -/
theorem dist_values (v w : ℕ → A) : dist v w = 0 ∨ ∃ n : ℕ, dist v w = (1 / 2 : ℝ) ^ (n + 1) := by
  by_cases h : v = w
  · left; rw [h, dist_self]
  · right; exact ⟨_, dist_of_ne h⟩

/-- `d(v, w) ≤ 2^{-(n+1)}` says exactly that `v` and `w` agree on their first `n` letters.
Mathlib: `PiNat.mem_cylinder_iff_dist_le`. -/
theorem dist_le_iff (v w : ℕ → A) (n : ℕ) :
    dist v w ≤ (1 / 2 : ℝ) ^ (n + 1) ↔ ∀ i < n, v i = w i := by
  classical
  by_cases h : v = w
  · -- `v = w`: both sides hold.
    subst h; simp [dist_self]
  · -- `v ≠ w`: since `1/2 < 1`, `2^{-(k)} ≤ 2^{-(n+1)}` iff `k ≥ n + 1`, that is, the first
    -- difference `firstDiff` is at least `n`: the words agree at every `i < n`.
    rw [dist_of_ne h, pow_le_pow_iff_right_of_lt_one₀ (by norm_num) (by norm_num),
      Nat.add_le_add_iff_right, firstDiff, Nat.le_find_iff]
    simp

/-- `d(v, w) < 2^{-n}` iff `d(v, w) ≤ 2^{-(n+1)}`: the distance takes no value in between. -/
theorem dist_lt_iff (v w : ℕ → A) (n : ℕ) :
    dist v w < (1 / 2 : ℝ) ^ n ↔ dist v w ≤ (1 / 2 : ℝ) ^ (n + 1) := by
  -- `d(v, w)` is `0`, when both sides hold, or `2^{-(m+1)}`, when both say `m + 1 > n`
  -- (powers of `1/2` decrease).
  rcases dist_values v w with h | ⟨m, h⟩ <;> rw [h]
  · constructor <;> intro <;> positivity
  · rw [pow_lt_pow_iff_right_of_lt_one₀ (by norm_num) (by norm_num),
      pow_le_pow_iff_right_of_lt_one₀ (by norm_num) (by norm_num)]
    omega

/-- Symmetry, `d(v, w) = d(w, v)`: the first place where `v` and `w` differ is the first
place where `w` and `v` differ. Mathlib: `dist_comm`. -/
theorem dist_comm (v w : ℕ → A) : dist v w = dist w v := by
  classical
  by_cases h : v = w
  · subst h; rfl
  · rw [dist_of_ne h, dist_of_ne (Ne.symm h), firstDiff, firstDiff,
      Nat.find_congr' (p := fun i => v i ≠ w i) (q := fun i => w i ≠ v i) ne_comm]

/-- `prop-1-5`: `d` is a metric: `d(v, w) = 0` only for `v = w`. Mathlib: `dist_eq_zero`. -/
theorem dist_eq_zero {v w : ℕ → A} : dist v w = 0 ↔ v = w := by
  constructor
  · -- If `v ≠ w`, then `d(v, w) = 2^{-k} > 0`. (Lean: `by_contra h` assumes the opposite,
    -- `h : v ≠ w`, and looks for a contradiction.)
    intro h0
    by_contra h
    rw [dist_of_ne h] at h0
    exact absurd h0 (by positivity)
  · rintro rfl; exact dist_self v

/-- `prop-1-5`, the ultrametric inequality `d(u, w) ≤ max(d(u, v), d(v, w))`. The book's proof:
if both distances are at most `2^{-m}` then `u, v` and `v, w` agree on the first `m - 1`
letters, hence so do `u, w`; take `2^{-m}` to be the larger of the two distances.
Mathlib: `PiNat.dist_triangle_nonarch`. -/
theorem dist_ultra (u v w : ℕ → A) : dist u w ≤ max (dist u v) (dist v w) := by
  -- Step 1. The larger of the two distances is itself a value of `d`: `0` or `2^{-(n+1)}`.
  have hM : max (dist u v) (dist v w) = 0 ∨
      ∃ n : ℕ, max (dist u v) (dist v w) = (1 / 2 : ℝ) ^ (n + 1) := by
    rcases max_choice (dist u v) (dist v w) with h | h <;> rw [h]
    · exact dist_values u v
    · exact dist_values v w
  rcases hM with h0 | ⟨n, hn⟩
  · -- Step 2. If it is `0`, both distances vanish, so `u = v = w` and `d(u, w) = 0`.
    have h1 : dist u v = 0 := le_antisymm (h0 ▸ le_max_left _ _) (dist_nonneg _ _)
    have h2 : dist v w = 0 := le_antisymm (h0 ▸ le_max_right _ _) (dist_nonneg _ _)
    rw [dist_eq_zero.mp h1, dist_eq_zero.mp h2, dist_self]
    exact le_max_left _ _
  · -- Step 3. If it is `2^{-(n+1)}` (the book's `2^{-m}`, `m = n + 1`), then `u, v` agree on the
    -- first `n` letters, and so do `v, w` (`dist_le_iff`); hence so do `u, w`, which says
    -- `d(u, w) ≤ 2^{-(n+1)}`.
    rw [hn, dist_le_iff]
    have h1 := (dist_le_iff u v n).mp (hn ▸ le_max_left _ _)
    have h2 := (dist_le_iff v w n).mp (hn ▸ le_max_right _ _)
    intro i hi
    rw [h1 i hi, h2 i hi]

/-- `prop-1-5`: the ultrametric inequality gives the triangle inequality
`d(u, w) ≤ d(u, v) + d(v, w)`, as `max ≤` sum for numbers `≥ 0`. Mathlib: `dist_triangle`. -/
theorem dist_triangle (u v w : ℕ → A) : dist u w ≤ dist u v + dist v w :=
  (dist_ultra u v w).trans (max_le_add_of_nonneg (dist_nonneg _ _) (dist_nonneg _ _))

/-- `prop-1-5`: the metric of `def-1-4`, with the four conditions proved above.
Mathlib: `PiNat.metricSpaceOfDiscreteUniformity`. -/
noncomputable def metric : PseudoMetric (ℕ → A) where
  d := dist
  nonneg := dist_nonneg
  self := dist_self
  symm := dist_comm
  triangle := dist_triangle

/-- `prop-1-5`: the ball of radius `2^{-n}` about `w` is the cylinder `C_u` of its first `n`
letters. Mathlib: `PiNat.mem_cylinder_iff_dist_le` (for Mathlib's `dist`). -/
theorem ball_eq_cylinder (w : ℕ → A) (n : ℕ) :
    metric.ball w ((1 / 2 : ℝ) ^ n) = cylinder (prefix_ n w) := by
  -- `d(w, v) < 2^{-n}` iff `d(w, v) ≤ 2^{-(n+1)}` (`dist_lt_iff`) iff `v` and `w` agree on the
  -- first `n` letters (`dist_le_iff`) iff `v` begins with `w 0 ⋯ w (n - 1)`. (Lean: `change`
  -- restates the goal in a form equal to it by definition.)
  ext v
  change dist w v < _ ↔ ∀ i : Fin n, v i = w i
  rw [dist_lt_iff, dist_le_iff]
  constructor
  · intro h i; exact (h i i.2).symm
  · intro h i hi; exact (h ⟨i, hi⟩).symm

/-- A cylinder `C_u` is the ball of radius `2^{-n}` about each of its points `w`: every
ball is centred at each of its points. -/
theorem cylinder_eq_ball {n : ℕ} {u : Fin n → A} {w : ℕ → A} (hw : w ∈ cylinder u) :
    cylinder u = metric.ball w ((1 / 2 : ℝ) ^ n) := by
  -- The ball is the cylinder of the first `n` letters of `w` (`ball_eq_cylinder`), and these
  -- letters are `u`, as `w ∈ C_u`.
  rw [ball_eq_cylinder]
  have : prefix_ n w = u := funext hw
  rw [this]

/-- The topology of the space of words, from its metric (`def-1n-1`). Mathlib: the topology
of `PiNat.metricSpaceOfDiscreteUniformity`, which is the product topology. -/
noncomputable instance : TopSpace (ℕ → A) := metric.toTopSpace

/-- `prop-1-5`: each cylinder is open: it is a ball about each of its points. -/
theorem isOpen_cylinder {n : ℕ} (u : Fin n → A) : IsOpen (cylinder u) := by
  -- By `PseudoMetric.isOpen_iff` it suffices to find a ball about each `w ∈ C_u` inside `C_u`;
  -- `C_u` is itself the ball of radius `2^{-n}` about `w` (`cylinder_eq_ball`).
  rw [show IsOpen (cylinder u) ↔ @IsOpen _ metric.toTopSpace (cylinder u) from Iff.rfl,
    PseudoMetric.isOpen_iff]
  intro w hw
  refine ⟨(1 / 2 : ℝ) ^ n, by positivity, ?_⟩
  rw [cylinder_eq_ball hw]

/-- `prop-1-5`: the cylinders are a base: every ball about `w` contains a ball of radius
`2^{-n}`, which is a cylinder. Mathlib: `PiNat.isTopologicalBasis_cylinders`. -/
theorem isBase_cylinders : IsBase {C : Set (ℕ → A) | ∃ n, ∃ u : Fin n → A, C = cylinder u} := by
  -- By `isBase_of_local`: the cylinders are open, and each open `U ∋ w` contains one about `w`.
  apply isBase_of_local
  · rintro _ ⟨n, u, rfl⟩; exact isOpen_cylinder u
  · -- `U` contains a ball `B(w, ε)`; take `n` with `2^{-n} < ε` (Analysis I: `(1/2)^n → 0`).
    -- Then `C_u` with `u` the first `n` letters of `w` is `B(w, 2^{-n}) ⊆ B(w, ε) ⊆ U`.
    intro U hU w hw
    obtain ⟨ε, hε, hεU⟩ := (metric.isOpen_iff U).mp hU w hw
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε (by norm_num : (1 / 2 : ℝ) < 1)
    refine ⟨cylinder (prefix_ n w), ⟨n, _, rfl⟩, fun i => rfl, ?_⟩
    rw [← ball_eq_cylinder]
    intro v hv
    exact hεU (lt_trans (show dist w v < _ from hv) hn)

/-- `prop-1-5`: each cylinder is closed: its complement is the union of the cylinders of the
other words of the same length. Mathlib: `PiNat.isClosed_cylinder`. -/
theorem isClosed_cylinder {n : ℕ} (u : Fin n → A) : IsClosed (cylinder u) := by
  -- Step 1. `w ∉ C_u` iff `w` begins with some other word `u' ≠ u` of length `n` (its own first
  -- `n` letters).
  have : (cylinder u)ᶜ = ⋃₀ {C | ∃ u' : Fin n → A, u' ≠ u ∧ C = cylinder u'} := by
    ext w
    constructor
    · intro hw
      refine ⟨cylinder (prefix_ n w), ⟨prefix_ n w, fun h => hw ?_, rfl⟩, fun i => rfl⟩
      intro i; rw [← h]; rfl
    · rintro ⟨_, ⟨u', hne, rfl⟩, hw⟩ hwu
      exact hne (funext fun i => (hw i).symm.trans (hwu i))
  -- Step 2. So the complement of `C_u` is a union of cylinders, which are open.
  unfold IsClosed
  rw [this]
  exact isOpen_sUnion (by rintro _ ⟨u', -, rfl⟩; exact isOpen_cylinder u')

end Words

/-! ## The `p`-adic metric on `ℤ` (`def-1-7`, `ex-1n-4`, `prop-1-8`) -/

namespace PAdic

-- Throughout, `p` is a prime. (Lean: `[hp : Fact p.Prime]` is the hypothesis "`p` is prime",
-- passed in square brackets so that Lean supplies it wherever it is needed.)
variable (p : ℕ) [hp : Fact p.Prime]

set_option linter.unusedSectionVars false

/-- `def-1-7`: `|n|_p = p^{-v_p(n)}` and `|0|_p = 0`, with `v_p` the exponent of `p` in `n`
(Mathlib's `padicValInt`, number theory). Mathlib: `padicNorm` (on `ℚ`).

Lean: `(p : ℝ)` is the natural number `p` seen as a real number, and `-(v : ℤ)` the exponent
`-v_p(n)` as an integer, so that `(p : ℝ) ^ (-(v : ℤ))` is `p^{-v_p(n)}`. -/
noncomputable def abs (n : ℤ) : ℝ := if n = 0 then 0 else (p : ℝ) ^ (-(padicValInt p n : ℤ))

/-- `def-1-7`: `d_p(m, n) = |m - n|_p`. Mathlib: `Padic` and `PadicInt` with their norms. -/
noncomputable def dist (m n : ℤ) : ℝ := abs p (m - n)

variable {p}

/-- `1 < p`, as real numbers: a prime is at least `2`. -/
theorem one_lt_p : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt

/-- `p^k > 0` for every integer `k`. -/
theorem zpow_p_pos (k : ℤ) : (0 : ℝ) < (p : ℝ) ^ k := zpow_pos (by linarith [one_lt_p (p := p)]) _

/-- `|n|_p ≥ 0`: it is `0` or a power of `p`. Mathlib: `padicNorm.nonneg`. -/
theorem abs_nonneg (n : ℤ) : 0 ≤ abs p n := by
  unfold abs; split_ifs
  · exact le_rfl
  · exact zpow_nonneg (by positivity) _

/-- `|n|_p ≤ p^{-k}` says exactly that `p^k` divides `n`. -/
theorem abs_le_iff (n : ℤ) (k : ℕ) : abs p n ≤ (p : ℝ) ^ (-(k : ℤ)) ↔ (p : ℤ) ^ k ∣ n := by
  -- `p^k ∣ n` iff `n = 0` or `k ≤ v_p(n)` (number theory, `padicValInt_dvd_iff`). For `n = 0`
  -- both sides hold; for `n ≠ 0`, `p^{-v_p(n)} ≤ p^{-k}` iff `k ≤ v_p(n)`, since `p > 1`.
  rw [padicValInt_dvd_iff]
  unfold abs
  split_ifs with h
  · simp [h]
  · rw [zpow_le_zpow_iff_right₀ one_lt_p]
    simp [h]

/-- `|n|_p < p^{-k}` says exactly that `p^{k+1}` divides `n`. -/
theorem abs_lt_iff (n : ℤ) (k : ℕ) : abs p n < (p : ℝ) ^ (-(k : ℤ)) ↔ (p : ℤ) ^ (k + 1) ∣ n := by
  -- As for `abs_le_iff`: for `n ≠ 0`, `p^{-v_p(n)} < p^{-k}` iff `v_p(n) > k`, i.e.
  -- `v_p(n) ≥ k + 1`; for `n = 0` both sides hold.
  rw [padicValInt_dvd_iff]
  unfold abs
  split_ifs with h
  · simp [h]; exact pow_pos (by linarith [one_lt_p (p := p)]) _
  · rw [zpow_lt_zpow_iff_right₀ one_lt_p]
    simp [h]

/-- `|n|_p` takes only the values `0` and `p^{-k}`. -/
theorem abs_values (n : ℤ) : abs p n = 0 ∨ ∃ k : ℕ, abs p n = (p : ℝ) ^ (-(k : ℤ)) := by
  unfold abs
  split_ifs
  · left; rfl
  · right; exact ⟨_, rfl⟩

/-- `|-n|_p = |n|_p`: `n` and `-n` have the same power of `p`. Mathlib: `padicNorm.neg`. -/
theorem abs_neg (n : ℤ) : abs p (-n) = abs p n := by
  simp [abs, padicValInt]

/-- The strong triangle inequality `|m + n|_p ≤ max(|m|_p, |n|_p)` (Analysis I 1.2(iv)), proved
as for words: if `p^k` divides both, it divides the sum. Mathlib: `padicNorm.nonarchimedean`. -/
theorem abs_add_le (m n : ℤ) : abs p (m + n) ≤ max (abs p m) (abs p n) := by
  -- Step 1. The larger of `|m|_p`, `|n|_p` is itself `0` or a power `p^{-k}`.
  have hM : max (abs p m) (abs p n) = 0 ∨
      ∃ k : ℕ, max (abs p m) (abs p n) = (p : ℝ) ^ (-(k : ℤ)) := by
    rcases max_choice (abs p m) (abs p n) with h | h <;> rw [h]
    · exact abs_values m
    · exact abs_values n
  rcases hM with h0 | ⟨k, hk⟩
  · -- Step 2. If it is `0`, then `|m|_p = |n|_p = 0`, so `m = n = 0` (a nonzero `n` has
    -- `|n|_p = p^{-v_p(n)} > 0`), and `|m + n|_p = 0`.
    have h1 : abs p m = 0 := le_antisymm (h0 ▸ le_max_left _ _) (abs_nonneg _)
    have h2 : abs p n = 0 := le_antisymm (h0 ▸ le_max_right _ _) (abs_nonneg _)
    have hm : m = 0 := by
      by_contra hm; simp only [abs, hm, ite_false] at h1; exact (zpow_p_pos _).ne' h1
    have hn : n = 0 := by
      by_contra hn; simp only [abs, hn, ite_false] at h2; exact (zpow_p_pos _).ne' h2
    simp [hm, hn, abs]
  · -- Step 3. If it is `p^{-k}`, then `|m|_p, |n|_p ≤ p^{-k}`, so `p^k` divides `m` and `n`
    -- (`abs_le_iff`), hence divides `m + n`: `|m + n|_p ≤ p^{-k}`.
    rw [hk, abs_le_iff]
    exact dvd_add ((abs_le_iff m k).mp (hk ▸ le_max_left _ _))
      ((abs_le_iff n k).mp (hk ▸ le_max_right _ _))

variable (p) in
/-- `def-1-7`: the `p`-adic metric `d_p(m, n) = |m - n|_p` on `ℤ`. Mathlib: the metric of
`PadicInt` restricted to `ℤ`. -/
noncomputable def metric : PseudoMetric ℤ where
  d := dist p
  nonneg _ _ := abs_nonneg _
  -- `d_p(n, n) = |0|_p = 0`.
  self _ := by simp [dist, abs]
  -- `|m - n|_p = |-(n - m)|_p = |n - m|_p`.
  symm m n := by rw [dist, dist, ← neg_sub, abs_neg]
  -- `a - c = (a - b) + (b - c)`, so by the strong triangle inequality
  -- `|a - c|_p ≤ max(|a - b|_p, |b - c|_p) ≤ |a - b|_p + |b - c|_p`.
  triangle a b c := by
    have : a - c = (a - b) + (b - c) := by ring
    rw [dist, this]
    exact (abs_add_le _ _).trans (max_le_add_of_nonneg (abs_nonneg _) (abs_nonneg _))

/-- `prop-1-8`: the open ball of radius `p^{-k}` about `a` is the residue class
`a + p^{k+1}ℤ`. -/
theorem ball_eq (a : ℤ) (k : ℕ) :
    (metric p).ball a ((p : ℝ) ^ (-(k : ℤ))) = {n | (p : ℤ) ^ (k + 1) ∣ n - a} := by
  -- The book's proof: `d_p(a, n) < p^{-k}` says `v_p(n - a) > k` (`abs_lt_iff`), that is,
  -- `p^{k+1}` divides `n - a` (which is `-(a - n)`).
  ext n
  change abs p (a - n) < _ ↔ _
  rw [abs_lt_iff, ← neg_sub, dvd_neg]
  rfl

/-- The residue classes `a + p^{k+1}ℤ`, `a ∈ ℤ`, `k ≥ 0`. -/
def classes : Set (Set ℤ) := {C | ∃ a : ℤ, ∃ k : ℕ, C = {n | (p : ℤ) ^ (k + 1) ∣ n - a}}

/-- `prop-1-8`: the residue classes are a base of `(ℤ, d_p)`: each is a ball, and every ball
about `a` contains one about `a` of radius `p^{-k}`. -/
theorem isBase_classes : @IsBase ℤ (metric p).toTopSpace (classes (p := p)) := by
  -- By `isBase_of_local`: the classes are open, and each open `U ∋ a` contains one about `a`.
  apply @isBase_of_local ℤ (metric p).toTopSpace
  · -- Each class is a ball (`ball_eq`), and balls are open.
    rintro _ ⟨a, k, rfl⟩
    rw [← ball_eq]
    exact (metric p).isOpen_ball _ _
  · -- `U` contains a ball `B(a, ε)`; take `k` with `p^{-k} < ε` (Analysis I: `(1/p)^k → 0`).
    -- Then the class `a + p^{k+1}ℤ` is `B(a, p^{-k}) ⊆ B(a, ε) ⊆ U`.
    intro U hU a ha
    obtain ⟨ε, hε, hεU⟩ := ((metric p).isOpen_iff U).mp hU a ha
    obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hε (inv_lt_one_of_one_lt₀ (one_lt_p (p := p)))
    refine ⟨_, ⟨a, k, rfl⟩, by simp, ?_⟩
    rw [← ball_eq]
    intro n hn
    apply hεU
    change dist p a n < ε
    have : (p : ℝ) ^ (-(k : ℤ)) = (p : ℝ)⁻¹ ^ k := by rw [zpow_neg, zpow_natCast, inv_pow]
    exact lt_trans (show dist p a n < _ from hn) (this ▸ hk)

/-- `prop-1-8`: each residue class is closed: its complement is the union of the other classes
mod `p^{k+1}`, each open. -/
theorem isClosed_class (a : ℤ) (k : ℕ) :
    @IsClosed ℤ (metric p).toTopSpace {n | (p : ℤ) ^ (k + 1) ∣ n - a} := by
  -- Step 1. `n ∉ a + p^{k+1}ℤ` iff `n` lies in another class `b + p^{k+1}ℤ` (its own, `b = n`):
  -- if `n` lay in both, `p^{k+1}` would divide `b - a = (n - a) - (n - b)`.
  have : {n | (p : ℤ) ^ (k + 1) ∣ n - a}ᶜ =
      ⋃₀ {C | ∃ b : ℤ, ¬ (p : ℤ) ^ (k + 1) ∣ b - a ∧ C = {n | (p : ℤ) ^ (k + 1) ∣ n - b}} := by
    ext n
    constructor
    · intro hn
      exact ⟨_, ⟨n, hn, rfl⟩, by simp⟩
    · rintro ⟨_, ⟨b, hb, rfl⟩, hnb⟩ hna
      apply hb
      have : b - a = (n - a) - (n - b) := by ring
      rw [this]
      exact dvd_sub hna hnb
  -- Step 2. So the complement is a union of classes, each open as a ball (`ball_eq`).
  unfold IsClosed
  rw [this]
  apply @isOpen_sUnion ℤ (metric p).toTopSpace
  rintro _ ⟨b, -, rfl⟩
  rw [← ball_eq]
  exact (metric p).isOpen_ball _ _

end PAdic

end Course
