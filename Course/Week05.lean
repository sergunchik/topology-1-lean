/-
Machine-generated (Claude, Aristotle), no line written by a person. Copyleft: GPL-3.0-or-later.

# Week 5: polygonal presentations, elementary transformations, the Euler characteristic

A compact surface is presented by polygons whose edges carry letters and are glued in pairs:
the torus is the square `aba⁻¹b⁻¹` (`def:presentation`, `ex:standard-presentations`). This file
does the combinatorial core of the classification of surfaces (week 5 of the book) on the
words themselves. It defines the elementary transformations (`def:elementary`) and the Euler
characteristic `χ = V − E + F` of a presentation (`def:euler-presentation`), and proves that
every elementary transformation leaves `χ` unchanged (`prop:chi-invariant`, `chi_equiv`) and
that `χ(S²) = 2`, `χ(#_g T²) = 2 − 2g`, `χ(#_k RP²) = 2 − k` for the standard words
(`prop:chi-standard`). It carries out the word manipulations of `lem:twisted-pair`, `lem:klein`,
`lem:torus-rp2` and the word-level part of `prop:connected-sum-words`. Last, and topologically,
`prop:attach-injects`: attaching a cell to `X` keeps `X` as a closed subspace and the open cell
as an open one, for an adjunction space of `Course.Week02Glue`. Each declaration names the
book's label and Mathlib's counterpart (Mathlib v4.34.1 has no polygonal presentations),
checked against Lean and Mathlib v4.34.1.

**How words, presentations and moves are written in Lean.** Take the torus `⟨a, b | aba⁻¹b⁻¹⟩`.
* A *letter* is a symbol with a direction (`Letter`): `⟨a, true⟩` is `a` and `⟨a, false⟩` is
  `a⁻¹`. The symbols may be the elements of any type `α`; the standard words use natural
  numbers, here `a = 0` and `b = 1`.
* A *word* is a list of letters (`Word`), read round its polygon anticlockwise: an edge whose
  arrow points the way one is going is `a`, one whose arrow points back is `a⁻¹`. So `aba⁻¹b⁻¹`
  is `[⟨0, true⟩, ⟨1, true⟩, ⟨0, false⟩, ⟨1, false⟩]` (this is `handle 0`). On lists: `[]` is
  the empty word, `x :: w` is the word `w` with the letter `x` put in front, and `u ++ v` is
  the word `uv`; so `aW` is `⟨a, true⟩ :: W` and `Wa` is `W ++ [⟨a, true⟩]`.
* A *presentation* is a list of words, one polygon each (`Presentation`). The torus is
  `[[⟨0, true⟩, ⟨1, true⟩, ⟨0, false⟩, ⟨1, false⟩]]`: a list with one word, one square. The set
  `S` of symbols is not stored: it is the set of symbols that occur (`syms`). A presentation
  `W :: Q` has first word `W` and further words `Q`.
* A *move* is a proof. `Move P Q` says "`Q` comes from `P` by one elementary transformation",
  and each kind of transformation is one way of giving such a proof. For instance
  `Move.rotate ⟨0, true⟩ [⟨1, true⟩, ⟨0, false⟩, ⟨1, false⟩] []` proves that rotating the torus
  `aba⁻¹b⁻¹` gives `ba⁻¹b⁻¹a`: in the polygon, the same square read from the next vertex.
  `Equiv P Q`, the book's "equivalent", says that a finite chain of moves and inverse moves
  leads from `P` to `Q`; most proofs below build such a chain one move at a time
  (`h₁.trans h₂`: first the chain `h₁`, then the chain `h₂`).

**Out of scope here.** The topology: the realisation `|P|` of a presentation
(`prop:realisation-surface`), that elementary transformations do not change it
(`prop:elementary-homeo`), and that `W₁W₂` presents a connected sum. What is proved is the word
calculus those statements are about. The combinatorial half of `thm:classification-I` (every
surface presentation is equivalent to a standard one) is not done. `prop:attach-injects` is
proved for `X ∪_φ Y` with `B ⊆ Y` closed and `φ : B → X` continuous, the book's `Sⁿ⁻¹ ⊆ Dⁿ`
being one case; "closed embedding" is stated as continuous (week 2), injective and closed, and
"homeomorphism onto the open cell" as injective on `Y ∖ B` and open on its open subsets.

**Conventions, and where they differ from the book.**
* A letter is a symbol with a direction, `⟨a, true⟩ = a`, `⟨a, false⟩ = a⁻¹`; a word is a list
  of letters, a presentation a list of words. The book's words form an unordered family; here the
  family is a list, and permuting it is one more move (`Move.permute`).
* The moves act on the first word of the list; with `Move.permute` any word can be brought there.
* *Relabelling* renames the symbols by any permutation `π : α ≃ α` (the book renames one symbol at
  a time), or interchanges `a` and `a⁻¹` throughout (`Move.flip`).
* *Cutting* may introduce the new edge with either direction (`W₁e`, `e⁻¹W₂` or `W₁e⁻¹`, `eW₂`),
  and *folding* removes `ee⁻¹` or `e⁻¹e`: the other case is a relabelling away.
* *Folding* asks, besides the book's length condition, that `e` occur nowhere else. In a surface
  presentation this holds automatically; it is stated so that the moves make sense for all
  presentations.
* *Consolidating*, *pasting* and *unfolding* are the inverses of subdividing, cutting and folding:
  `Elementary P Q` is `Move P Q ∨ Move Q P`.
* Vertex classes. A corner of a polygon lies between a letter `x` and the next letter `y`
  (cyclically); its vertex is the end of the edge `x` arrives at and the end of the edge `y`
  leaves from. So the vertices of the realisation are the classes of the *edge ends*
  `(a, true)` (the head of the edge `a`) and `(a, false)` (its tail) under the equivalence
  generated by `fin x ∼ ini y` for consecutive letters: `V` counts these classes. This is the
  book's count of corner classes (`prop:realisation-surface`), read on edge ends instead of
  corners: two corners at the same edge end are glued, and every edge end lies at a corner, so
  the two counts agree. `χ` is proved invariant under every move, subdividing included.

New to Lean? Read `Course/README.md` first.
-/
import Course.Week02Glue
import Mathlib.Data.Set.Card
import Mathlib.Data.Finset.Card
import Mathlib.Logic.Equiv.Basic
import Mathlib.Logic.Relation
import Mathlib.Data.List.Perm.Basic

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Course

namespace Surface

open Relation

/-! ## Letters, words, presentations (`def:presentation`) -/

/-- A letter: a symbol `a` with a direction, `⟨a, true⟩` for `a` and `⟨a, false⟩` for `a⁻¹`
(`def:presentation`). Mathlib: none (compare `FreeGroup`'s `α × Bool`).

Lean: a `structure` is a record with named fields; a letter `x` has the fields `x.sym` and
`x.dir`, and `⟨a, d⟩` is the letter with `sym = a`, `dir = d`. `Bool` is `{true, false}`, and
`!d` is the other value. `deriving DecidableEq` lets Lean test whether two letters are equal. -/
structure Letter (α : Type*) where
  /-- the symbol -/
  sym : α
  /-- `true` for `a`, `false` for `a⁻¹` -/
  dir : Bool
  deriving DecidableEq

-- From here on `α` is the type the symbols are taken from.
variable {α : Type*}

namespace Letter

/-- The inverse letter: `a ↦ a⁻¹`, `a⁻¹ ↦ a`. -/
def inv (x : Letter α) : Letter α := ⟨x.sym, !x.dir⟩

/-- The end of the edge `x.sym` at which one arrives reading the letter `x`: the head
`(a, true)` for `a`, the tail `(a, false)` for `a⁻¹`. -/
def fin (x : Letter α) : α × Bool := (x.sym, x.dir)

/-- The end of the edge `x.sym` from which one leaves reading the letter `x`: the tail
`(a, false)` for `a`, the head `(a, true)` for `a⁻¹`. -/
def ini (x : Letter α) : α × Bool := (x.sym, !x.dir)

/-- `x⁻¹` has the symbol of `x`. -/
@[simp] theorem inv_sym (x : Letter α) : x.inv.sym = x.sym := rfl
/-- `x⁻¹` has the other direction. -/
@[simp] theorem inv_dir (x : Letter α) : x.inv.dir = !x.dir := rfl
/-- `(x⁻¹)⁻¹ = x`. -/
@[simp] theorem inv_inv (x : Letter α) : x.inv.inv = x := by cases x; simp [inv]
/-- Reading `x⁻¹` one arrives where reading `x` one leaves. -/
@[simp] theorem fin_inv (x : Letter α) : x.inv.fin = x.ini := rfl
/-- Reading `x⁻¹` one leaves from where reading `x` one arrives. -/
@[simp] theorem ini_inv (x : Letter α) : x.inv.ini = x.fin := by simp [ini, fin, inv]

end Letter

/-- A word: a finite sequence of letters (`def:presentation`), read round its polygon.
(`abbrev` is a definition that Lean unfolds freely: a word *is* a list of letters.) -/
abbrev Word (α : Type*) := List (Letter α)

/-- The formal inverse `W⁻¹` of a word: reverse it and invert each letter, so
`(a₁ ⋯ aₘ)⁻¹ = aₘ⁻¹ ⋯ a₁⁻¹`. It is the same polygon read clockwise. (`w.map f` applies `f` to
every letter of `w`; `.reverse` reverses a list.) -/
def Word.inv (w : Word α) : Word α := (w.map Letter.inv).reverse

/-- The empty word is its own inverse. -/
@[simp] theorem Word.inv_nil : Word.inv ([] : Word α) = [] := rfl
/-- `(xw)⁻¹ = w⁻¹x⁻¹`. -/
@[simp] theorem Word.inv_cons (x : Letter α) (w : Word α) :
    Word.inv (x :: w) = Word.inv w ++ [x.inv] := by simp [Word.inv]
/-- `(uv)⁻¹ = v⁻¹u⁻¹`. -/
@[simp] theorem Word.inv_append (u v : Word α) :
    Word.inv (u ++ v) = Word.inv v ++ Word.inv u := by simp [Word.inv]
/-- `(W⁻¹)⁻¹ = W`. -/
@[simp] theorem Word.inv_inv (w : Word α) : Word.inv (Word.inv w) = w := by
  simp [Word.inv, List.map_reverse, Function.comp_def]
/-- `W⁻¹` has as many letters as `W`. -/
@[simp] theorem Word.length_inv (w : Word α) : (Word.inv w).length = w.length := by
  simp [Word.inv]

/-- A polygonal presentation `⟨S | W₁, …, Wₖ⟩`, as the list of its words (`def:presentation`);
its symbols are those that occur. The book's length conditions are not part of the type; the
moves keep them. Mathlib: none. -/
abbrev Presentation (α : Type*) := List (Word α)

/-- The number of occurrences of the symbol `a` in all the words together.

Lean: `[DecidableEq α]` says that Lean can test whether two symbols are equal, which counting
needs. `w.countP p` counts the letters of `w` with the property `p`, and `.sum` adds the counts
over the words. -/
def occ [DecidableEq α] (P : Presentation α) (a : α) : ℕ :=
  (P.map fun w => w.countP fun x => x.sym = a).sum

/-- A *surface presentation*: every symbol occurs exactly twice in all the words together
(`def:presentation`). -/
def IsSurface [DecidableEq α] (P : Presentation α) : Prop :=
  ∀ w ∈ P, ∀ x ∈ w, occ P x.sym = 2

/-- The directions with which the symbol `a` occurs, in order: for `aba⁻¹b⁻¹` and `a`, the
list `[true, false]`. (`P.flatten` is all the words of `P` written one after another, and
`.filter p` keeps the letters with the property `p`.) -/
def dirs [DecidableEq α] (P : Presentation α) (a : α) : List Bool :=
  (P.flatten.filter fun x => x.sym = a).map Letter.dir

/-- The two edges labelled `a` form a *twisted pair*: they appear as `a` and `a`, or as `a⁻¹`
and `a⁻¹` (`def:presentation`). -/
def IsTwisted [DecidableEq α] (P : Presentation α) (a : α) : Prop :=
  ∃ d, dirs P a = [d, d]

/-- The two edges labelled `a` form a *complementary pair*: they appear as `a` and `a⁻¹`, or
as `a⁻¹` and `a` (`def:presentation`). -/
def IsComplementary [DecidableEq α] (P : Presentation α) (a : α) : Prop :=
  ∃ d, dirs P a = [d, !d]

/-- The symbols of a presentation, the set `S` of `⟨S | W₁, …, Wₖ⟩`: those that occur in some
word. (`Finset α` is a finite subset of `α`; `.card` is its number of elements.) -/
def syms [DecidableEq α] (P : Presentation α) : Finset α :=
  (P.flatMap fun w => w.map Letter.sym).toFinset

/-- `a ∈ S` exactly when `a` is the symbol of some letter of some word. -/
@[simp] theorem mem_syms [DecidableEq α] {P : Presentation α} {a : α} :
    a ∈ syms P ↔ ∃ w ∈ P, ∃ x ∈ w, x.sym = a := by
  simp [syms]

/-- `a ∉ S` exactly when no letter of any word has the symbol `a`: `a` is a *new* symbol. -/
theorem notMem_syms_iff [DecidableEq α] {P : Presentation α} {a : α} :
    a ∉ syms P ↔ ∀ w ∈ P, ∀ y ∈ w, y.sym ≠ a := by
  simp

/-- Every letter of `W⁻¹` has a property `p` exactly when, for every letter `y` of `W`, `y⁻¹`
has it. -/
theorem Word.forall_mem_inv {w : Word α} {p : Letter α → Prop} :
    (∀ y ∈ Word.inv w, p y) ↔ ∀ y ∈ w, p y.inv := by
  simp [Word.inv]

/-- Closes a goal `a ∉ syms P` ("`a` is a new symbol for `P`") from hypotheses
`∀ y ∈ W, y.sym ≠ a` on the pieces `W` of `P`.

Lean: a `macro` names a sequence of tactics, so that `by surface_fresh` can be written each time
this routine check comes up. It unfolds "`a` is new" into "no letter of any piece has the
symbol `a`", splits that into one statement per piece, and finds each among the hypotheses. -/
macro "surface_fresh" : tactic => `(tactic| (
  simp only [notMem_syms_iff, List.forall_mem_cons, List.forall_mem_append, Word.forall_mem_inv,
    Letter.inv_sym, List.cons_append, List.nil_append, List.append_assoc, Word.inv_append,
    Word.inv_cons, Word.inv_nil]
  repeat' apply And.intro
  all_goals first | assumption | exact Ne.symm ‹_› | simp_all))

/-- The standard presentation of the sphere, `⟨a | aa⁻¹⟩` (`ex:standard-presentations`). -/
def sphere : Presentation ℕ := [[⟨0, true⟩, ⟨0, false⟩]]

/-- The block `aᵢbᵢaᵢ⁻¹bᵢ⁻¹`, with `aᵢ = 2i`, `bᵢ = 2i + 1`. `handle 0` is the torus
`aba⁻¹b⁻¹` with `a = 0`, `b = 1`. -/
def handle (i : ℕ) : Word ℕ := [⟨2 * i, true⟩, ⟨2 * i + 1, true⟩, ⟨2 * i, false⟩, ⟨2 * i + 1, false⟩]

/-- The word `a₁b₁a₁⁻¹b₁⁻¹ ⋯ a_g b_g a_g⁻¹ b_g⁻¹` of `#_g T²` (`ex:standard-presentations`).

Lean: the definition is by recursion on `g`: the empty word for `g = 0`, and the word for `g`
followed by one more block for `g + 1`. Lean counts the blocks from `0`, so `handle i` is the
book's block `a_{i+1}b_{i+1}a_{i+1}⁻¹b_{i+1}⁻¹`. -/
def torusWord : ℕ → Word ℕ
  | 0 => []
  | g + 1 => torusWord g ++ handle g

/-- The block `aᵢaᵢ`, with `aᵢ = i`. `crosscap 0` is `RP²`, `aa` with `a = 0`. -/
def crosscap (i : ℕ) : Word ℕ := [⟨i, true⟩, ⟨i, true⟩]

/-- The word `a₁a₁a₂a₂ ⋯ a_ka_k` of `#_k RP²` (`ex:standard-presentations`), by recursion on
`k` as `torusWord`. -/
def crossWord : ℕ → Word ℕ
  | 0 => []
  | k + 1 => crossWord k ++ crosscap k

/-! ## Elementary transformations (`def:elementary`) -/

/-- Rename the symbols by a permutation `π` of `α`: every letter `a^{±1}` becomes `π(a)^{±1}`.
(`α ≃ α` is the type of bijections `α → α`; `π x.sym` is `π` applied to the symbol of `x`.) -/
def relabel (π : α ≃ α) (P : Presentation α) : Presentation α :=
  P.map fun w => w.map fun x => ⟨π x.sym, x.dir⟩

/-- Interchange `a` and `a⁻¹` throughout: invert every letter with the symbol `a`, keep the
others. -/
def flipSym [DecidableEq α] (a : α) (P : Presentation α) : Presentation α :=
  P.map fun w => w.map fun x => if x.sym = a then x.inv else x

/-- Replace `a` by `ae` and `a⁻¹` by `e⁻¹a⁻¹` throughout. (`w.flatMap f` replaces each letter
`x` of `w` by the word `f x` and writes the results one after another.) -/
def subdivide [DecidableEq α] (a e : α) (P : Presentation α) : Presentation α :=
  P.map fun w => w.flatMap fun x =>
    if x.sym = a then (if x.dir then [x, ⟨e, true⟩] else [⟨e, false⟩, x]) else [x]

/-- `Move P Q`: `Q` comes from `P` by one of the elementary transformations of `def:elementary`
that are not inverses of others: relabelling (`rename`, `flip`), subdividing, reflecting,
rotating, cutting and folding, plus permuting the words (the book's words form an unordered
family). Mathlib: none.

Lean: an `inductive` proposition is defined by its *rules*, the lines starting with `|`; each
rule says "in this situation, `Move P Q` holds", and there is no other way to prove
`Move P Q`. A rule takes data (the words, the new symbol) and hypotheses (the book's conditions)
and gives a proof of `Move P Q`; for instance `Move.rotate x w Q` proves
`Move ((x :: w) :: Q) ((w ++ [x]) :: Q)`. In each rule `Q` is the list of the other words,
which the move leaves alone. -/
inductive Move [DecidableEq α] : Presentation α → Presentation α → Prop
  /-- *Relabelling*: rename the symbols by a bijection `π`. The polygons and their arrows stay
  as they are; only the labels on the edges change, and edges with the same label before
  still have the same label after. -/ | rename (π : α ≃ α) (P : Presentation α) :
      Move P (relabel π P)
  /-- *Relabelling*: interchange `a` and `a⁻¹` throughout. In the picture, reverse the arrows
  on both edges labelled `a`; the two edges are still glued arrow onto arrow, in the same
  way. -/ | flip (a : α) (P : Presentation α) : Move P (flipSym a P)
  /-- *Subdividing*: a new vertex in the middle of each edge labelled `a`; the first half,
  along the arrow, keeps the label `a`, and the second half gets a new label `e`. So `a`
  becomes `ae` and `a⁻¹` becomes `e⁻¹a⁻¹`. Hypotheses: `ha`, `a` is a symbol of `P`;
  `he`, `e` is a new symbol. -/ | subdivide (a e : α) (P : Presentation α)
      (ha : a ∈ syms P) (he : e ∉ syms P) : Move P (subdivide a e P)
  /-- *Reflecting*: turn the first polygon over, that is, read its word clockwise instead of
  anticlockwise: `W` becomes `W⁻¹`. -/ | reflect (w : Word α) (Q : Presentation α) :
      Move (w :: Q) (Word.inv w :: Q)
  /-- *Rotating*: read the first polygon from the next vertex on, so that its first letter
  `x` comes last: `xw` becomes `wx`. -/ | rotate (x : Letter α) (w : Word α)
      (Q : Presentation α) : Move ((x :: w) :: Q) ((w ++ [x]) :: Q)
  /-- *Cutting*: cut the first polygon `W₁W₂` along the diagonal from the vertex where `W₁`
  ends to the vertex where it begins. The two pieces are the polygons `W₁e` and `e⁻¹W₂`,
  where the diagonal gets a new label `e` (either direction may be chosen: `e` is a letter),
  so that gluing them along `e` gives the old polygon back. Hypotheses: `h₁`, `h₂`, the book's
  "`W₁`, `W₂` of length at least `2`", so that each piece is a polygon with at least three
  edges; `he`, the symbol of `e` is new. -/ | cut (W₁ W₂ : Word α) (e : Letter α)
      (Q : Presentation α) (h₁ : 2 ≤ W₁.length)
      (h₂ : 2 ≤ W₂.length) (he : e.sym ∉ syms ((W₁ ++ W₂) :: Q)) :
      Move ((W₁ ++ W₂) :: Q) ((W₁ ++ [e]) :: (e.inv :: W₂) :: Q)
  /-- *Folding*: the edges `e` and `e⁻¹` are next to each other at the end of the first
  polygon; fold the polygon along the bisector of the angle between them, zipping the two
  edges together, and the polygon `W₁` is left. Hypotheses: `h`, the book's "`W₁` of length at
  least `3`, or length `2` if the presentation has only one word"; `he`, the symbol of `e`
  occurs nowhere else. -/ | fold (W₁ : Word α) (e : Letter α) (Q : Presentation α)
      (h : 3 ≤ W₁.length ∨ (W₁.length = 2 ∧ Q = [])) (he : e.sym ∉ syms (W₁ :: Q)) :
      Move ((W₁ ++ [e, e.inv]) :: Q) (W₁ :: Q)
  /-- Permuting the words: the same polygons, listed in another order (`P.Perm Q`: `Q` is a
  rearrangement of the list `P`). Nothing changes in the picture; with it, any word can be
  brought to the front, where the other moves act. -/ | permute (P Q : Presentation α)
      (h : P.Perm Q) : Move P Q

/-- An elementary transformation (`def:elementary`): a move or the inverse of one, so that
consolidating, pasting and unfolding are the moves `Move Q P` read backwards. -/
def Elementary [DecidableEq α] (P Q : Presentation α) : Prop := Move P Q ∨ Move Q P

/-- Two presentations are equivalent when a finite chain of elementary transformations carries
one to the other. Mathlib: none.

Lean: `ReflTransGen r` is the relation "there is a chain `P = P₀ r P₁ r ⋯ r Pₙ = Q`", with
`n = 0` allowed. -/
def Equiv [DecidableEq α] : Presentation α → Presentation α → Prop :=
  ReflTransGen Elementary

section Equiv

variable [DecidableEq α]

/-- Every presentation is equivalent to itself (the chain of no steps). -/
@[refl] theorem Equiv.refl (P : Presentation α) : Equiv P P := ReflTransGen.refl

/-- If `P ~ Q` and `Q ~ R`, then `P ~ R`: follow one chain, then the other. -/
theorem Equiv.trans {P Q R : Presentation α} (h₁ : Equiv P Q) (h₂ : Equiv Q R) : Equiv P R :=
  ReflTransGen.trans h₁ h₂

/-- If `P ~ Q`, then `Q ~ P`: read the chain backwards; each step read backwards is again an
elementary transformation, since `Elementary` contains the inverses. -/
theorem Equiv.symm {P Q : Presentation α} (h : Equiv P Q) : Equiv Q P := by
  -- Induction on the length of the chain. (Lean: `induction h with` takes the cases of how
  -- the chain `h` was built, one `|` each.) The empty chain: `P ~ P`.
  induction h with
  | refl => exact ReflTransGen.refl
  -- A chain `P ~ S` followed by one step `S → T` (`hst`): by induction `S ~ P` (`ih`), so
  -- `T → S` (`hst` backwards, `Or.symm`) followed by `S ~ P` gives `T ~ P`.
  | tail _ hst ih => exact ReflTransGen.head (Or.symm hst) ih

/-- One move is a chain of one step: if `Move P Q`, then `P ~ Q`. (`Or.inl h` proves
`Move P Q ∨ Move Q P` from its left half.) -/
theorem Move.equiv {P Q : Presentation α} (h : Move P Q) : Equiv P Q :=
  ReflTransGen.single (Or.inl h)

/-- Listing the same words in another order gives an equivalent presentation. -/
theorem Equiv.perm {P Q : Presentation α} (h : P.Perm Q) : Equiv P Q :=
  (Move.permute P Q h).equiv

/-- If `P ~ Q`, `P = P'` and `Q = Q'`, then `P' ~ Q'`. Used to rewrite the two ends of a chain
into the form a statement asks for. (`hP ▸ h` rewrites `h` with the equation `hP`.) -/
theorem Equiv.of_eq {P Q P' Q' : Presentation α} (h : Equiv P Q) (hP : P = P') (hQ : Q = Q') :
    Equiv P' Q' := hP ▸ hQ ▸ h

/-- One move read backwards: if `Move P Q`, then `Q ~ P` (pasting, unfolding, consolidating
are of this kind). -/
theorem Move.equiv_symm {P Q : Presentation α} (h : Move P Q) : Equiv Q P :=
  ReflTransGen.single (Or.inr h)

/-- Rotating by a whole block: `UV ~ VU`, by repeated single rotations: the same polygon
read from the vertex where `U` ends. -/
theorem Equiv.rotate (u v : Word α) (Q : Presentation α) :
    Equiv ((u ++ v) :: Q) ((v ++ u) :: Q) := by
  -- Induction on the length of `U`, for all `V` at once (`generalizing v`).
  induction u generalizing v with
  -- `U` empty: both sides are `V`.
  | nil => simp; rfl
  -- `U = xU'`: one rotation takes `xU'V` to `U'Vx`, and by induction (with `Vx` for `V`)
  -- `U'(Vx) ~ (Vx)U' = V(xU')`.
  | cons x u ih =>
    refine (Move.rotate x (u ++ v) Q).equiv.trans ?_
    simpa using ih (v ++ [x])

/-- Reflecting the first word, as an equivalence: `W ~ W⁻¹`. -/
theorem Equiv.reflect (w : Word α) (Q : Presentation α) : Equiv (w :: Q) (Word.inv w :: Q) :=
  (Move.reflect w Q).equiv

/-- Moves inside the second word: if `⟨W₂, W₁, …⟩ ~ ⟨W₂', W₁, …⟩`, then
`⟨W₁, W₂, …⟩ ~ ⟨W₁, W₂', …⟩`. Proof: interchange the first two words, apply the chain `h`,
and interchange them back (`List.Perm.swap`, a permutation of the list). -/
theorem Equiv.second {w₁ w₂ w₂' : Word α} {Q : Presentation α}
    (h : Equiv (w₂ :: w₁ :: Q) (w₂' :: w₁ :: Q)) :
    Equiv (w₁ :: w₂ :: Q) (w₁ :: w₂' :: Q) :=
  ((Equiv.perm (List.Perm.swap _ _ _)).trans h).trans (Equiv.perm (List.Perm.swap _ _ _))

end Equiv

/-! ## The word lemmas (`lem:twisted-pair`, `lem:klein`, `lem:torus-rp2`,
`prop:connected-sum-words`) -/

section Words

variable [DecidableEq α]

/-- Unfolding: relabelling `⟨W, …⟩` relabels `W` and the other words. -/
theorem relabel_cons (π : α ≃ α) (w : Word α) (Q : Presentation α) :
    relabel π (w :: Q) = (w.map fun x => ⟨π x.sym, x.dir⟩) :: relabel π Q := rfl

/-- A renaming `π` that fixes every symbol of `W` leaves `W` unchanged. -/
theorem map_relabel_of_fix {π : α ≃ α} {w : Word α} (h : ∀ y ∈ w, π y.sym = y.sym) :
    (w.map fun x => (⟨π x.sym, x.dir⟩ : Letter α)) = w := by
  -- Write the right side `W` as `W` with the identity applied to every letter (`conv_rhs`
  -- rewrites the right side only); the two maps agree on every letter of `W`, by `h`.
  conv_rhs => rw [← List.map_id w]
  exact List.map_congr_left fun y hy => by rw [h y hy]; rfl

/-- A renaming that fixes every symbol of a presentation leaves it unchanged. -/
theorem relabel_of_fix {π : α ≃ α} {Q : Presentation α}
    (h : ∀ w ∈ Q, ∀ y ∈ w, π y.sym = y.sym) : relabel π Q = Q := by
  conv_rhs => rw [← List.map_id Q]
  exact List.map_congr_left fun w hw => map_relabel_of_fix (h w hw)

/-- Interchanging `a` and `a⁻¹` leaves a word without `a` unchanged. -/
theorem map_flip_of_fix {a : α} {w : Word α} (h : ∀ y ∈ w, y.sym ≠ a) :
    (w.map fun x => if x.sym = a then x.inv else x) = w := by
  conv_rhs => rw [← List.map_id w]
  exact List.map_congr_left fun y hy => by simp [h y hy]

/-- Unfolding: flipping `a` in `⟨W, …⟩` flips it in `W` and in the other words. -/
theorem flipSym_cons (a : α) (w : Word α) (Q : Presentation α) :
    flipSym a (w :: Q) = (w.map fun x => if x.sym = a then x.inv else x) :: flipSym a Q := rfl

/-- Interchanging `a` and `a⁻¹` leaves a presentation without `a` unchanged. -/
theorem flipSym_of_fix {a : α} {Q : Presentation α} (h : ∀ w ∈ Q, ∀ y ∈ w, y.sym ≠ a) :
    flipSym a Q = Q := by
  conv_rhs => rw [← List.map_id Q]
  exact List.map_congr_left fun w hw => map_flip_of_fix (h w hw)

/-- **`lem:twisted-pair`**, bringing a twisted pair together: `XaYaZ ~ aaY⁻¹ZX`, where `X`, `Y`,
`Z` are words and `Y⁻¹` is the formal inverse of `Y`. The book writes `ccY⁻¹ZX`, with a new
symbol `c` replacing `a`; here `c` is named `a` again, which a renaming does. The other words
`Q` of the presentation are carried along. Mathlib: none.

Hypotheses: `x` is the letter `a` (which may be `a` or `a⁻¹`: the lemma holds for both), and
`h` says that its symbol occurs nowhere in `X`, `Y`, `Z` or `Q`. `[Infinite α]`: there are
infinitely many symbols, so a new one can always be found.

The proof is the book's: rotate, cut along a new edge `e`, reflect and rotate the first piece,
rotate the second, paste along `a`, rename and rotate. -/
theorem twisted_pair [Infinite α] (X Y Z : Word α) (x : Letter α) (Q : Presentation α)
    (h : x.sym ∉ syms ((X ++ Y ++ Z) :: Q)) :
    Equiv ((X ++ x :: Y ++ x :: Z) :: Q) ((x :: x :: (Word.inv Y ++ Z ++ X)) :: Q) := by
  -- The symbol `a` of `x` is not in `X`, `Y`, `Z` (`hX`, `hY`, `hZ`) or in the other words `Q`
  -- (`hQ`).
  simp only [mem_syms, List.mem_cons, List.mem_append, not_exists, not_and] at h
  have hX : ∀ y ∈ X, y.sym ≠ x.sym := fun y hy => h _ (Or.inl rfl) y (by simp [hy])
  have hY : ∀ y ∈ Y, y.sym ≠ x.sym := fun y hy => h _ (Or.inl rfl) y (by simp [hy])
  have hZ : ∀ y ∈ Z, y.sym ≠ x.sym := fun y hy => h _ (Or.inl rfl) y (by simp [hy])
  have hQ : ∀ w ∈ Q, ∀ y ∈ w, y.sym ≠ x.sym := fun w hw y hy => h w (Or.inr hw) y hy
  -- Step 1. Rotate `XaYaZ` to `aYaZX` (`Equiv.rotate`, with `X` as the block moved).
  have h₀ : Equiv ((X ++ x :: Y ++ x :: Z) :: Q) ((x :: Y ++ x :: (Z ++ X)) :: Q) := by
    simpa using Equiv.rotate X (x :: Y ++ x :: Z) Q
  refine h₀.trans ?_
  -- Case 1: `Y` is empty. Then `aaZX` is already the word wanted: rotating was enough.
  -- (`rcases eq_or_ne Y [] with rfl | hYne`: either `Y = []`, put in for `Y`, or `Y ≠ []`.)
  rcases eq_or_ne Y [] with rfl | hYne
  · simpa using Equiv.refl _
  -- Case 2: `ZX` is empty, so the word is `aYa`. Reflect it to `a⁻¹Y⁻¹a⁻¹`, rotate to
  -- `a⁻¹a⁻¹Y⁻¹`, and interchange `a` and `a⁻¹` (the book renames `a⁻¹` as `c`): `aaY⁻¹`.
  rcases eq_or_ne (Z ++ X) [] with hZX | hZXne
  · rw [hZX]
    have hZ0 : Z = [] := (List.append_eq_nil_iff.mp hZX).1
    have hX0 : X = [] := (List.append_eq_nil_iff.mp hZX).2
    subst hZ0 hX0
    refine (Equiv.reflect _ Q).trans ?_
    simp only [List.cons_append, Word.inv_cons, Word.inv_append, Word.inv_nil, List.nil_append,
      List.append_assoc, List.singleton_append, List.append_nil]
    refine (Equiv.rotate (x.inv :: Word.inv Y) [x.inv] Q).trans ?_
    refine ((Move.flip x.sym _).equiv).trans ?_
    -- The flip changes only the two letters `a⁻¹`: `Y⁻¹` and `Q` do not contain `a`.
    have hYi : ∀ y ∈ Word.inv Y, y.sym ≠ x.sym := by
      intro y hy
      simp only [Word.inv, List.mem_reverse, List.mem_map] at hy
      obtain ⟨z, hz, rfl⟩ := hy
      exact hY z hz
    simp only [flipSym, List.map_cons, List.singleton_append, List.cons_append, List.nil_append,
      Letter.inv_sym, ite_true, Letter.inv_inv, map_flip_of_fix hYi]
    rw [show (Q.map fun w => w.map fun y => if y.sym = x.sym then y.inv else y) = Q from
      flipSym_of_fix hQ]
  -- Case 3, the general case: `Y` and `ZX` are not empty.
  · -- Take a new symbol `e`, not `a` and not in `X`, `Y`, `Z`, `Q`: it exists because there are
    -- infinitely many symbols and a presentation uses finitely many.
    obtain ⟨e, he⟩ := Infinite.exists_notMem_finset (insert x.sym (syms ((X ++ Y ++ Z) :: Q)))
    simp only [Finset.mem_insert, mem_syms, List.mem_cons, List.mem_append, not_or, not_exists,
      not_and] at he
    obtain ⟨hex, he⟩ := he
    have eX : ∀ y ∈ X, y.sym ≠ e := fun y hy => he _ (Or.inl rfl) y (by simp [hy])
    have eY : ∀ y ∈ Y, y.sym ≠ e := fun y hy => he _ (Or.inl rfl) y (by simp [hy])
    have eZ : ∀ y ∈ Z, y.sym ≠ e := fun y hy => he _ (Or.inl rfl) y (by simp [hy])
    have eQ : ∀ w ∈ Q, ∀ y ∈ w, y.sym ≠ e := fun w hw y hy => he w (Or.inr hw) y hy
    -- The new edge is the letter `E = e^{∓1}`, of the direction opposite to `x`; with `x = a` it
    -- is `e⁻¹`, so the pieces below are the book's with `e` and `e⁻¹` interchanged, and the
    -- last renaming gives `aa` with no flip. (`set E := … with hE` names `E` and records the
    -- definition as `hE`.)
    set E : Letter α := ⟨e, !x.dir⟩ with hE
    -- The two pieces `aY` and `aZX` have length at least `2`, as cutting asks. (`omega` does
    -- routine arithmetic with whole numbers.)
    have hYlen : 2 ≤ (x :: Y).length := by
      have := List.length_pos_iff.mpr hYne; simp; omega
    have hZXlen : 2 ≤ (x :: (Z ++ X)).length := by
      have := List.length_pos_iff.mpr hZXne; simp only [List.length_cons]; omega
    -- Step 2. Cut `aY | aZX` along the new edge: `aYE` and `E⁻¹aZX`.
    have h₁ := Move.cut (x :: Y) (x :: (Z ++ X)) E Q hYlen hZXlen (by surface_fresh)
    simp only [List.cons_append] at h₁
    refine h₁.equiv.trans ?_
    -- Step 3. Reflect the first piece to `E⁻¹Y⁻¹a⁻¹`, and rotate it to `a⁻¹E⁻¹Y⁻¹`.
    refine (Equiv.reflect _ _).trans ?_
    simp only [Word.inv_cons, Word.inv_append, Word.inv_nil, List.nil_append, List.append_assoc,
      List.singleton_append]
    refine (Equiv.rotate (E.inv :: Word.inv Y) [x.inv] _).trans ?_
    simp only [List.cons_append, List.nil_append]
    -- Step 4. Rotate the second piece to `ZXE⁻¹a` (`Equiv.second`: a move in the second word),
    -- and interchange the two words.
    refine (Equiv.second (Equiv.rotate [E.inv, x] (Z ++ X) _)).trans ?_
    refine (Equiv.perm (List.Perm.swap _ _ _)).trans ?_
    -- Step 5. Paste along `a`: `ZXE⁻¹a` and `a⁻¹E⁻¹Y⁻¹` become `ZXE⁻¹E⁻¹Y⁻¹`. Pasting is
    -- cutting read backwards, so this is the cut `h₂` of `ZXE⁻¹ | E⁻¹Y⁻¹` along `a`, used
    -- backwards (`Or.inr`). Both pieces have length at least `2`, and `a` occurs nowhere else.
    have h₂ := Move.cut (Z ++ X ++ [E.inv]) (E.inv :: Word.inv Y) x Q
      (by have := List.length_pos_iff.mpr hZXne
          simp only [List.length_append, List.length_singleton] at this ⊢; omega)
      (by have := List.length_pos_iff.mpr hYne; simp; omega)
      (by surface_fresh)
    simp only [List.append_assoc, List.singleton_append, List.cons_append] at h₂ ⊢
    refine (show Equiv _ _ from ReflTransGen.single (Or.inr h₂)).trans ?_
    -- Step 6. Rotate to `E⁻¹E⁻¹Y⁻¹ZX`, and rename by the bijection interchanging `e` and `a`
    -- (`Equiv.swap e x.sym`). It turns `E⁻¹`, which is `e` with the direction of `x`, into `x`,
    -- and fixes every other symbol (`hfix`, and the same for `Q`): the result is `aaY⁻¹ZX`.
    have h₃ := Equiv.rotate (Z ++ X) (E.inv :: E.inv :: Word.inv Y) Q
    simp only [List.append_assoc, List.cons_append] at h₃
    simp only [List.nil_append]
    refine h₃.trans ?_
    refine (Move.rename (_root_.Equiv.swap e x.sym) _).equiv.trans ?_
    have hfix : ∀ y ∈ Word.inv Y ++ (Z ++ X), _root_.Equiv.swap e x.sym y.sym = y.sym := by
      intro y hy
      simp only [List.mem_append, Word.inv, List.mem_reverse, List.mem_map] at hy
      have h1 : y.sym ≠ e ∧ y.sym ≠ x.sym := by
        rcases hy with ⟨z, hz, rfl⟩ | hy | hy
        · exact ⟨eY z hz, hY z hz⟩
        · exact ⟨eZ y hy, hZ y hy⟩
        · exact ⟨eX y hy, hX y hy⟩
      exact _root_.Equiv.swap_apply_of_ne_of_ne h1.1 h1.2
    rw [relabel_cons, relabel_of_fix (fun w hw y hy =>
      _root_.Equiv.swap_apply_of_ne_of_ne (eQ w hw y hy) (hQ w hw y hy))]
    simp only [List.map_cons, map_relabel_of_fix hfix, hE, Letter.inv, Bool.not_not,
      _root_.Equiv.swap_apply_left]
    exact Equiv.refl _

/-- **`lem:klein`** at the level of words: the Klein bottle `aba⁻¹b` is equivalent to `bbaa`,
the word of `RP² # RP²` (`prop:connected-sum-words`). Here `a ≠ b` are any two symbols.
Mathlib: none.

Proof (the book's): `b` is a twisted pair. `lem:twisted-pair` (`twisted_pair`) with `X = a`,
`Y = a⁻¹`, `Z` empty turns `XbYbZ = aba⁻¹b` into `bbY⁻¹ZX = bb(a⁻¹)⁻¹a = bbaa`. (Lean:
`.of_eq` rewrites the two ends of the chain into the form of the statement, by `simp`.) -/
theorem klein [Infinite α] (a b : α) (hab : a ≠ b) :
    Equiv [[⟨a, true⟩, ⟨b, true⟩, ⟨a, false⟩, ⟨b, true⟩]]
      [[⟨b, true⟩, ⟨b, true⟩, ⟨a, true⟩, ⟨a, true⟩]] :=
  (twisted_pair [⟨a, true⟩] [⟨a, false⟩] [] ⟨b, true⟩ [] (by simp [hab])).of_eq
    (by simp) (by simp [Word.inv, Letter.inv])

/-- **`lem:torus-rp2`** at the level of words: for any word `W` in other symbols,
`ccaba⁻¹b⁻¹W ~ W ccaabb`; with `W` empty, `T² # RP² ~ RP² # RP² # RP²`. The book writes
`W ddeeff`; here the new symbols are named `c`, `a`, `b` again. The other words `Q` of the
presentation are carried along. Hypotheses: `a`, `b`, `c` are distinct (`hab`, `hac`, `hbc`)
and occur neither in `W` nor in `Q` (`ha`, `hb`, `hc`). Mathlib: none.

The proof is the book's: `lem:twisted-pair` read backwards, then forwards three times, then a
reflection, a rotation and two relabellings. Each step is one `have`; the last line chains them.
(The book treats `W` empty separately; here the twisted pair `c` with `Y = W` empty is the
first case of `twisted_pair`, so no case split is needed.) -/
theorem torus_rp2 [Infinite α] (a b c : α) (W : Word α) (Q : Presentation α)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (ha : a ∉ syms (W :: Q)) (hb : b ∉ syms (W :: Q)) (hc : c ∉ syms (W :: Q)) :
    Equiv ((⟨c, true⟩ :: ⟨c, true⟩ :: ⟨a, true⟩ :: ⟨b, true⟩ :: ⟨a, false⟩ :: ⟨b, false⟩ :: W) :: Q)
      ((W ++ [⟨c, true⟩, ⟨c, true⟩, ⟨a, true⟩, ⟨a, true⟩, ⟨b, true⟩, ⟨b, true⟩]) :: Q) := by
  simp only [notMem_syms_iff, List.forall_mem_cons] at ha hb hc
  obtain ⟨haW, haQ⟩ := ha
  obtain ⟨hbW, hbQ⟩ := hb
  obtain ⟨hcW, hcQ⟩ := hc
  -- `a`, `b`, `c` are not in `W` and not in `Q`; the six facts are named `haW`, …, `hcQ`.
  -- Step 1. Read `lem:twisted-pair` backwards, with `X` empty, `Y = b⁻¹a⁻¹` (so `Y⁻¹ = ab`),
  -- `Z = a⁻¹b⁻¹W`: the word `ccaba⁻¹b⁻¹W` becomes `c b⁻¹a⁻¹ c a⁻¹b⁻¹ W`. (Each
  -- `by surface_fresh` checks that the twisted symbol occurs nowhere else.)
  have h₁ := (twisted_pair [] [⟨b, false⟩, ⟨a, false⟩] ([⟨a, false⟩, ⟨b, false⟩] ++ W)
    ⟨c, true⟩ Q (by surface_fresh)).symm
  -- Step 2. The twisted pair `b⁻¹` (the book's `β`), with `X = c`, `Y = a⁻¹ca⁻¹`, `Z = W`:
  -- `b⁻¹b⁻¹ a c⁻¹ a W c`.
  have h₂ := twisted_pair [⟨c, true⟩] [⟨a, false⟩, ⟨c, true⟩, ⟨a, false⟩] W ⟨b, false⟩ Q
    (by surface_fresh)
  -- Step 3. The twisted pair `a` (the book's `α⁻¹`), with `X = b⁻¹b⁻¹`, `Y = c⁻¹`, `Z = Wc`:
  -- `aa c W c b⁻¹b⁻¹`. Here `Y⁻¹` turns `c⁻¹` into `c`, and the complementary pair `c⁻¹, c`
  -- becomes the twisted pair `c, c`: this is where the torus goes.
  have h₃ := twisted_pair [⟨b, false⟩, ⟨b, false⟩] [⟨c, false⟩] (W ++ [⟨c, true⟩]) ⟨a, true⟩ Q
    (by surface_fresh)
  -- Step 4. The twisted pair `c`, with `X = aa`, `Y = W`, `Z = b⁻¹b⁻¹`: `cc W⁻¹ b⁻¹b⁻¹ aa`.
  have h₄ := twisted_pair [⟨a, true⟩, ⟨a, true⟩] W [⟨b, false⟩, ⟨b, false⟩] ⟨c, true⟩ Q
    (by surface_fresh)
  -- Step 5. Reflect, to `a⁻¹a⁻¹ bb W c⁻¹c⁻¹`, and rotate: `W c⁻¹c⁻¹ a⁻¹a⁻¹ bb`.
  have h₅ := Equiv.reflect (⟨c, true⟩ :: ⟨c, true⟩ :: (Word.inv W ++ [⟨b, false⟩, ⟨b, false⟩] ++
    [⟨a, true⟩, ⟨a, true⟩])) Q
  have h₅' :=
    Equiv.rotate [⟨a, false⟩, ⟨a, false⟩, ⟨b, true⟩, ⟨b, true⟩] (W ++ [⟨c, false⟩, ⟨c, false⟩]) Q
  -- Step 6. Relabel: interchange `c` and `c⁻¹` (`h₆`: `W cc a⁻¹a⁻¹ bb`), then `a` and `a⁻¹`
  -- (`h₆'`: `W cc aa bb`). The flips do not touch `W`, `Q` or the other symbols (`hfc`, `hfa`).
  have h₆ := (Move.flip c ((W ++ [⟨c, false⟩, ⟨c, false⟩] ++
    [⟨a, false⟩, ⟨a, false⟩, ⟨b, true⟩, ⟨b, true⟩]) :: Q)).equiv
  have h₆' := (Move.flip a ((W ++ [⟨c, true⟩, ⟨c, true⟩] ++
    [⟨a, false⟩, ⟨a, false⟩, ⟨b, true⟩, ⟨b, true⟩]) :: Q)).equiv
  have hfc : flipSym c ((W ++ [⟨c, false⟩, ⟨c, false⟩] ++
      [⟨a, false⟩, ⟨a, false⟩, ⟨b, true⟩, ⟨b, true⟩]) :: Q) = (W ++ [⟨c, true⟩, ⟨c, true⟩] ++
      [⟨a, false⟩, ⟨a, false⟩, ⟨b, true⟩, ⟨b, true⟩]) :: Q := by
    rw [flipSym_cons, flipSym_of_fix hcQ]
    simp only [List.map_append, map_flip_of_fix hcW]
    simp [Letter.inv, hac, hbc]
  have hfa : flipSym a ((W ++ [⟨c, true⟩, ⟨c, true⟩] ++
      [⟨a, false⟩, ⟨a, false⟩, ⟨b, true⟩, ⟨b, true⟩]) :: Q) = (W ++ [⟨c, true⟩, ⟨c, true⟩] ++
      [⟨a, true⟩, ⟨a, true⟩, ⟨b, true⟩, ⟨b, true⟩]) :: Q := by
    rw [flipSym_cons, flipSym_of_fix haQ]
    simp only [List.map_append, map_flip_of_fix haW]
    simp [Letter.inv, hac.symm, hab.symm, hac, hab]
  rw [hfc] at h₆
  rw [hfa] at h₆'
  -- Write every step's two ends in the same normal form (inverses computed, lists flattened),
  -- so that the end of each step is literally the start of the next; then chain them.
  simp only [Word.inv_cons, Word.inv_nil, Word.inv_append, Word.inv_inv, List.nil_append,
    List.cons_append, List.append_assoc, List.singleton_append, Letter.inv, Bool.not_true,
    Bool.not_false, List.append_nil] at h₁ h₂ h₃ h₄ h₅ h₅' h₆ h₆' ⊢
  exact h₁.trans (h₂.trans (h₃.trans (h₄.trans (h₅.trans (h₅'.trans (h₆.trans h₆'))))))

/-- **`prop:connected-sum-words`**, the part about words: `⟨W₁c⁻¹b⁻¹a⁻¹, abcW₂⟩ ~ ⟨W₁W₂⟩`, by
pasting along `a` and folding `b` and then `c`. Hypotheses: `a`, `b`, `c` are distinct new
symbols (not in `W₁W₂`), and `W₁W₂` has at least two letters (`hlen`), as folding asks. With
`W₂` empty this is the book's `⟨W₁c⁻¹b⁻¹a⁻¹, abc⟩ ~ ⟨W₁⟩`; that the two presentations realise
`M₁` minus a disc glued to `M₂` minus a disc is the topological half, not formalised.
Mathlib: none. -/
theorem connected_sum_words (W₁ W₂ : Word α) (a b c : α) (hab : a ≠ b) (hac : a ≠ c)
    (hbc : b ≠ c) (ha : a ∉ syms [W₁ ++ W₂]) (hb : b ∉ syms [W₁ ++ W₂])
    (hc : c ∉ syms [W₁ ++ W₂]) (hlen : 2 ≤ (W₁ ++ W₂).length) :
    Equiv [W₁ ++ [⟨c, false⟩, ⟨b, false⟩, ⟨a, false⟩], ⟨a, true⟩ :: ⟨b, true⟩ :: ⟨c, true⟩ :: W₂]
      [W₁ ++ W₂] := by
  simp only [notMem_syms_iff, List.forall_mem_cons, List.forall_mem_append,
    List.not_mem_nil, false_imp_iff, implies_true, and_true] at ha hb hc
  obtain ⟨haW₁, haW₂⟩ := ha
  obtain ⟨hbW₁, hbW₂⟩ := hb
  obtain ⟨hcW₁, hcW₂⟩ := hc
  -- `a`, `b`, `c` are in neither `W₁` nor `W₂`.
  -- Step 1. Rotate both words, to `a⁻¹W₁c⁻¹b⁻¹` and `bcW₂a`, and interchange them.
  have h₁ := (Equiv.rotate (W₁ ++ [⟨c, false⟩, ⟨b, false⟩]) [⟨a, false⟩]
    [⟨a, true⟩ :: ⟨b, true⟩ :: ⟨c, true⟩ :: W₂]).trans
    ((Equiv.second (Equiv.rotate [⟨a, true⟩] (⟨b, true⟩ :: ⟨c, true⟩ :: W₂) _)).trans
      (Equiv.perm (List.Perm.swap _ _ [])))
  -- Step 2. Paste along `a`: `bcW₂a` and `a⁻¹W₁c⁻¹b⁻¹` become `bcW₂W₁c⁻¹b⁻¹` (the cut of
  -- `bcW₂ | W₁c⁻¹b⁻¹` along `a`, read backwards).
  have h₂ := (Move.cut (⟨b, true⟩ :: ⟨c, true⟩ :: W₂) (W₁ ++ [⟨c, false⟩, ⟨b, false⟩])
    ⟨a, true⟩ [] (by simp) (by simp) (by surface_fresh)).equiv_symm
  -- Step 3. Rotate to `cW₂W₁c⁻¹ b⁻¹b` and fold the adjacent pair `b⁻¹b`: `cW₂W₁c⁻¹`. What is
  -- left has length `|W₁W₂| + 2 ≥ 4`, as folding asks.
  have h₃ := Equiv.rotate [⟨b, true⟩] (⟨c, true⟩ :: W₂ ++ W₁ ++ [⟨c, false⟩, ⟨b, false⟩]) []
  have h₃' := (Move.fold (⟨c, true⟩ :: W₂ ++ W₁ ++ [⟨c, false⟩]) ⟨b, false⟩ []
      (Or.inl (by simp at hlen ⊢; omega)) (by surface_fresh)).equiv
  -- Step 4. Rotate to `W₂W₁ c⁻¹c` and fold `c⁻¹c`: `W₂W₁` (one word, of length at least `2`).
  -- Step 5. Rotate: `W₁W₂`.
  have h₄ := Equiv.rotate [⟨c, true⟩] (W₂ ++ W₁ ++ [⟨c, false⟩]) []
  have h₄' := (Move.fold (W₂ ++ W₁) ⟨c, false⟩ [] (by simp at hlen ⊢; omega)
    (by surface_fresh)).equiv
  have h₅ := Equiv.rotate W₂ W₁ []
  simp only [List.cons_append, List.nil_append, List.append_assoc, List.singleton_append,
    Letter.inv, Bool.not_true, Bool.not_false] at h₁ h₂ h₃ h₃' h₄ h₄' h₅ ⊢
  -- With the ends of the steps in the same normal form, chain them.
  exact h₁.trans (h₂.trans (h₃.trans (h₃'.trans (h₄.trans (h₄'.trans h₅)))))

end Words

/-! ## The Euler characteristic (`def:euler-presentation`, `prop:chi-invariant`)

`χ(P) = V − E + F`, with `E` the number of symbols, `F` the number of words and `V` the number
of vertex classes. To count `V`, each corner of a polygon is recorded as the pair of letters
(before it, after it), and each corner glues the end of the edge one arrives at to the end of
the edge one leaves from (see the header). `prop:chi-invariant` is then proved move by move:
for each move, `V`, `E` and `F` change so that `V − E + F` does not. -/

section Chi

variable {β γ : Type*}

/-- The pairs of consecutive entries of a list: `lin [u, v, w] = [(u, v), (v, w)]`.

Lean: the definition is by cases on the shape of the list. A list `u :: v :: t` that starts
with two entries `u`, `v` gives the pair `(u, v)` and then the pairs of `v :: t`; any shorter
list (`_`, "anything else") gives none. -/
def lin : List β → List (β × β)
  | u :: v :: t => (u, v) :: lin (v :: t)
  | _ => []

/-- The pairs of cyclically consecutive entries of a list: the corners of a polygon, each as the
pair (letter before it, letter after it). For the torus `aba⁻¹b⁻¹` they are `(a, b)`,
`(b, a⁻¹)`, `(a⁻¹, b⁻¹)`, `(b⁻¹, a)`: the consecutive pairs of `aba⁻¹b⁻¹a`. -/
def cyc : List β → List (β × β)
  | [] => []
  | x :: t => lin (x :: t ++ [x])

/-- The empty list has no consecutive pairs. -/
@[simp] theorem lin_nil : lin ([] : List β) = [] := rfl
/-- A list of one entry has no consecutive pairs. -/
@[simp] theorem lin_singleton (x : β) : lin [x] = [] := rfl

/-- The consecutive pairs of `x t` are `(x, first entry of t)` and those of `t`. (`t.head?` is
the first entry of `t`, as `some v`, or `none` if `t` is empty.) -/
theorem mem_lin_cons {x : β} {t : List β} {p : β × β} :
    p ∈ lin (x :: t) ↔ (p.1 = x ∧ t.head? = some p.2) ∨ p ∈ lin t := by
  rcases t with _ | ⟨v, t⟩
  · simp
  · simp only [lin, List.mem_cons, List.head?_cons, Option.some.injEq]
    constructor
    · rintro (rfl | h)
      · exact Or.inl ⟨rfl, rfl⟩
      · exact Or.inr h
    · rintro (⟨h1, h2⟩ | h)
      · exact Or.inl (Prod.ext h1 h2.symm)
      · exact Or.inr h

/-- The consecutive pairs of `ab` are those of `a`, those of `b`, and (last entry of `a`, first
entry of `b`). -/
theorem mem_lin_append {a b : List β} {p : β × β} :
    p ∈ lin (a ++ b) ↔ p ∈ lin a ∨ p ∈ lin b ∨ (a.getLast? = some p.1 ∧ b.head? = some p.2) := by
  -- Induction on `a`; each step unfolds one pair and finishes by propositional logic (`tauto`).
  induction a with
  | nil => simp
  | cons x a ih =>
    rw [List.cons_append, mem_lin_cons, ih, mem_lin_cons]
    rcases a with _ | ⟨y, a⟩
    · simp only [List.nil_append, List.head?_nil, reduceCtorEq, and_false, lin_nil,
        List.not_mem_nil, List.getLast?_singleton, Option.some.injEq, false_or]
      constructor
      · rintro (h | h | h)
        · exact Or.inr ⟨h.1.symm, h.2⟩
        · exact Or.inl h
        · exact absurd h.1 (by simp)
      · rintro (h | h)
        · exact Or.inr (Or.inl h)
        · exact Or.inl ⟨h.1.symm, h.2⟩
    · simp only [List.cons_append, List.head?_cons, List.getLast?_cons_cons]
      tauto

/-- The cyclic pairs of `w` are its consecutive pairs and (last entry, first entry). -/
theorem mem_cyc {w : List β} {p : β × β} :
    p ∈ cyc w ↔ p ∈ lin w ∨ (w.getLast? = some p.1 ∧ w.head? = some p.2) := by
  rcases w with _ | ⟨x, t⟩
  · simp [cyc]
  · simp only [cyc, mem_lin_append, lin_singleton, List.not_mem_nil, List.head?_cons,
      false_or]

/-- Applying `f` to every entry applies it to every consecutive pair. -/
theorem lin_map (f : β → γ) (l : List β) : lin (l.map f) = (lin l).map (Prod.map f f) := by
  induction l with
  | nil => rfl
  | cons x t ih =>
    rcases t with _ | ⟨y, t⟩
    · rfl
    · simp only [List.map_cons, lin] at ih ⊢
      rw [ih]; rfl

/-- Applying `f` to every entry applies it to every cyclic pair. -/
theorem cyc_map (f : β → γ) (l : List β) : cyc (l.map f) = (cyc l).map (Prod.map f f) := by
  rcases l with _ | ⟨x, t⟩
  · rfl
  · simp only [List.map_cons, cyc]
    rw [← lin_map]; simp

/-- Reversing a list reverses its consecutive pairs: `(u, v)` for the reversed list is
`(v, u)` for the list. -/
theorem mem_lin_reverse {l : List β} {p : β × β} :
    p ∈ lin l.reverse ↔ (p.2, p.1) ∈ lin l := by
  induction l with
  | nil => simp
  | cons x t ih =>
    -- Induction on `l`: the pairs of `(xt)` reversed, that is of `t` reversed followed by `x`.
    -- (`grind` finishes with the case analysis and the equations.)
    rw [List.reverse_cons, mem_lin_append, ih, mem_lin_cons (t := t)]
    simp only [lin_singleton, List.not_mem_nil, List.getLast?_reverse, List.head?_cons,
      Option.some.injEq, false_or]
    grind

/-- Reversing a list reverses its cyclic pairs. -/
theorem mem_cyc_reverse {l : List β} {p : β × β} :
    p ∈ cyc l.reverse ↔ (p.2, p.1) ∈ cyc l := by
  rw [mem_cyc, mem_cyc, mem_lin_reverse]
  simp only [List.getLast?_reverse, List.head?_reverse]
  tauto

variable [DecidableEq α]

/-- The identifications of edge ends: reading the letter `u` and then `v` across a corner, the
end `u.fin` at which `u` arrives is the end `v.ini` from which `v` leaves. For the torus
`aba⁻¹b⁻¹`, writing `a₊`, `a₋` for the head `(a, true)` and the tail `(a, false)` of `a`, the
four corners give `a₊ ∼ b₋`, `b₊ ∼ a₊`, `a₋ ∼ b₊`, `b₋ ∼ a₋`. (`P.flatMap cyc` lists the corners
of all the polygons of `P`.) -/
def edges (P : Presentation α) : List ((α × Bool) × (α × Bool)) :=
  (P.flatMap cyc).map fun p => (p.1.fin, p.2.ini)

/-- Two edge ends are adjacent, `x ∼ y`, when a corner identifies them. -/
def Adj (P : Presentation α) (x y : α × Bool) : Prop := (x, y) ∈ edges P

/-- `x ∼ y` exactly when some corner `(u, v)` of some word of `P` has `u.fin = x`,
`v.ini = y`. -/
theorem adj_iff {P : Presentation α} {x y : α × Bool} :
    Adj P x y ↔ ∃ w ∈ P, ∃ u v, (u, v) ∈ cyc w ∧ u.fin = x ∧ v.ini = y := by
  simp only [Adj, edges, List.mem_map, List.mem_flatMap, Prod.mk.injEq, Prod.exists]
  constructor
  · rintro ⟨u, v, ⟨w, hw, h⟩, rfl, rfl⟩; exact ⟨w, hw, u, v, h, rfl, rfl⟩
  · rintro ⟨w, hw, u, v, h, rfl, rfl⟩; exact ⟨u, v, ⟨w, hw, h⟩, rfl, rfl⟩

/-- In `⟨W, …⟩`, `x ∼ y` comes from a corner of `W` or from a corner of the other words. -/
theorem adj_cons {w : Word α} {Q : Presentation α} {x y : α × Bool} :
    Adj (w :: Q) x y ↔ (∃ u v, (u, v) ∈ cyc w ∧ u.fin = x ∧ v.ini = y) ∨ Adj Q x y := by
  simp only [adj_iff, List.mem_cons, exists_eq_or_imp]

/-- The edge ends of the symbols of a presentation: `(a, true)` and `(a, false)` for each
`a ∈ S`, as a set (`{x | …}`, the set of `x` such that …). -/
def ends (P : Presentation α) : Set (α × Bool) := {x | x.1 ∈ syms P}

/-- `V`, the number of vertex classes (`def:euler-presentation`): the classes of edge ends under
the equivalence relation generated by the identifications made at the corners. For the torus
`aba⁻¹b⁻¹` the four ends are all identified (`a₊ ∼ b₋ ∼ a₋ ∼ b₊`, see `edges`), so `V = 1`.
Mathlib: none.

Lean: `Quot.mk (Adj P) x` is the class `[x]` of `x` under the equivalence relation generated by
`Adj P`; `Quot.mk (Adj P) '' ends P` is the set of classes of the edge ends, and `.ncard` is its
number of elements. (`noncomputable`: Lean is not asked to compute this number.) -/
noncomputable def numV (P : Presentation α) : ℕ := (Quot.mk (Adj P) '' ends P).ncard

/-- `E`, the number of symbols (`def:euler-presentation`). -/
def numE (P : Presentation α) : ℕ := (syms P).card

/-- `F`, the number of words (`def:euler-presentation`). -/
def numF (P : Presentation α) : ℕ := P.length

/-- The Euler characteristic `χ(P) = V − E + F` of a presentation (`def:euler-presentation`).
For the torus `aba⁻¹b⁻¹`: `1 − 2 + 1 = 0`. Mathlib: none for presentations (for finite
simplicial complexes, compare `SimplicialComplex`; Mathlib v4.34.1 has no Euler characteristic
of a cell complex).

Lean: `V`, `E`, `F` are natural numbers (`ℕ`), where `1 − 2` would be `0`; Lean turns each into
an integer before subtracting, so the difference is taken in `ℤ`. -/
noncomputable def chi (P : Presentation α) : ℤ := numV P - numE P + numF P

/-! ### Counting classes -/

/-- If `f` sends every step `x r y` to a chain from `f x` to `f y`, it sends every chain to a
chain. (`EqvGen r`, the equivalence relation generated by `r`: `x` and `y` are joined by a
chain of `r`-steps, each taken forwards or backwards.) -/
theorem eqvGen_map {r : β → β → Prop} {s : γ → γ → Prop} (f : β → γ)
    (h : ∀ x y, r x y → EqvGen s (f x) (f y)) {x y : β} (hxy : EqvGen r x y) :
    EqvGen s (f x) (f y) := by
  -- Induction on how the chain `hxy` is built: one step (`h`), no step, a chain read
  -- backwards, two chains one after the other.
  induction hxy with
  | rel x y hr => exact h x y hr
  | refl x => exact EqvGen.refl _
  | symm x y _ ih => exact EqvGen.symm _ _ ih
  | trans x y z _ _ ih₁ ih₂ => exact EqvGen.trans _ _ _ ih₁ ih₂

/-- A step in either direction is a chain. -/
theorem eqvGen_of_or {r : β → β → Prop} {x y : β} (h : r y x ∨ r x y) : EqvGen r x y :=
  h.elim (fun h => EqvGen.symm _ _ (EqvGen.rel _ _ h)) (EqvGen.rel _ _)

/-- Two graphs with maps each way, each sending edges to paths and each composite moving every
vertex only within its component, have equally many components on the given vertex sets.

In the use below the vertices are edge ends, the edges are the identifications made at the
corners, and the components are the vertex classes: so this is how `V` is compared for two
presentations. Hypotheses: `hf`, `hg`, edges go to chains; `hgf`, `hfg`, `g(f(x))` is in the
class of `x` and `f(g(y))` in that of `y`; `hfS`, `hgT`, `f` and `g` map the vertex sets `S`,
`T` into each other. -/
theorem ncard_classes_eq {r : β → β → Prop} {s : γ → γ → Prop} {S : Set β} {T : Set γ}
    (f : β → γ) (g : γ → β)
    (hf : ∀ x y, r x y → EqvGen s (f x) (f y)) (hg : ∀ x y, s x y → EqvGen r (g x) (g y))
    (hgf : ∀ x ∈ S, EqvGen r (g (f x)) x) (hfg : ∀ y ∈ T, EqvGen s (f (g y)) y)
    (hfS : ∀ x ∈ S, f x ∈ T) (hgT : ∀ y ∈ T, g y ∈ S) :
    (Quot.mk r '' S).ncard = (Quot.mk s '' T).ncard := by
  -- The map of classes `F[x] = [f(x)]`, well defined because `f` sends steps to chains (`hf`).
  -- (`Quot.lift u w` is the map `[x] ↦ u(x)`, given the proof `w` that it is well defined.)
  let F : Quot r → Quot s :=
    Quot.lift (fun x => Quot.mk s (f x)) (fun x y h => Quot.eqvGen_sound (hf x y h))
  -- `F` maps the classes of `S` onto the classes of `T`: `F[x] = [f(x)]` with `f(x) ∈ T`, and
  -- every `[y]`, `y ∈ T`, is `[f(g(y))] = F[g(y)]`.
  have himg : F '' (Quot.mk r '' S) = Quot.mk s '' T := by
    ext q
    constructor
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨f x, hfS x hx, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨Quot.mk r (g y), ⟨g y, hgT y hy, rfl⟩, Quot.eqvGen_sound (hfg y hy)⟩
  -- So it suffices that `F` is injective on the classes of `S`. If `[f(x)] = [f(x')]`, then
  -- `g(f(x))` and `g(f(x'))` are joined by a chain (`hg`), and `x ∼ g(f(x))`, `x' ∼ g(f(x'))`
  -- (`hgf`): so `[x] = [x']`.
  rw [← himg]
  refine (Set.InjOn.ncard_image ?_).symm
  rintro _ ⟨x, hx, rfl⟩ _ ⟨x', hx', rfl⟩ hxx
  have h₁ : EqvGen r (g (f x)) (g (f x')) := eqvGen_map g hg (Quot.eqvGen_exact hxx)
  exact Quot.eqvGen_sound (EqvGen.trans _ _ _ (EqvGen.symm _ _ (hgf x hx))
    (EqvGen.trans _ _ _ h₁ (hgf x' hx')))

/-- Two presentations with the same identifications and the same edge ends have equally many
vertex classes. (`ncard_classes_eq` with `f = g = id`, the identity.) -/
theorem numV_eq_of_adj {P Q : Presentation α} (hadj : ∀ x y, Adj P x y ↔ Adj Q x y)
    (hends : ends P = ends Q) : numV P = numV Q := by
  unfold numV
  rw [← hends]
  exact ncard_classes_eq id id (fun x y h => EqvGen.rel _ _ ((hadj x y).1 h))
    (fun x y h => EqvGen.rel _ _ ((hadj x y).2 h)) (fun x _ => EqvGen.refl x)
    (fun x _ => EqvGen.refl x) (fun _ h => h) (fun _ h => h)

/-! ### Rotating, reflecting, permuting

These change none of `V`, `E`, `F` (`prop:chi-invariant`): they only rename or redraw the same
polygons. -/

/-- Rotating a word does not change its corners: the same polygon, read from another vertex. -/
theorem mem_cyc_rotate {x : Letter α} {w : Word α} {p : Letter α × Letter α} :
    p ∈ cyc (x :: w) ↔ p ∈ cyc (w ++ [x]) := by
  rw [mem_cyc, mem_cyc, mem_lin_cons, mem_lin_append]
  rcases w with _ | ⟨y, w⟩
  · simp
  · simp only [List.head?_cons, lin_singleton, List.not_mem_nil, List.getLast?_append,
      List.getLast?_singleton, Option.some_or, List.head?_append, Option.some.injEq, false_or]
    grind

/-- Rotating does not change `V`: the corners, so the identifications, are the same. -/
theorem numV_rotate (x : Letter α) (w : Word α) (Q : Presentation α) :
    numV ((w ++ [x]) :: Q) = numV ((x :: w) :: Q) := by
  refine numV_eq_of_adj (fun a b => ?_) ?_
  · simp only [adj_cons, mem_cyc_rotate]
  · ext; simp [ends, or_comm, or_left_comm]

/-- Rotating does not change `E`: the same letters. -/
theorem numE_rotate (x : Letter α) (w : Word α) (Q : Presentation α) :
    numE ((w ++ [x]) :: Q) = numE ((x :: w) :: Q) := by
  unfold numE; congr 1; ext; simp [or_comm, or_left_comm]

/-- The corners of `W⁻¹` are the corners `(u, v)` of `W` read backwards, as `(v⁻¹, u⁻¹)`. -/
theorem mem_cyc_inv {w : Word α} {p : Letter α × Letter α} :
    p ∈ cyc (Word.inv w) ↔ (p.2.inv, p.1.inv) ∈ cyc w := by
  rw [Word.inv, mem_cyc_reverse, cyc_map, List.mem_map]
  constructor
  · rintro ⟨q, hq, hqp⟩
    simp only [Prod.map, Prod.mk.injEq] at hqp
    rw [← hqp.1, ← hqp.2]; simpa using hq
  · intro h
    exact ⟨(p.2.inv, p.1.inv), h, by simp⟩

/-- Reflecting does not change `V`. A corner `(v⁻¹, u⁻¹)` of `W⁻¹` identifies
`(v⁻¹).fin = v.ini` with `(u⁻¹).ini = u.fin`: the same two ends as the corner `(u, v)` of `W`,
in the other order. -/
theorem numV_reflect (w : Word α) (Q : Presentation α) :
    numV (Word.inv w :: Q) = numV (w :: Q) := by
  unfold numV
  have hends : ends (Word.inv w :: Q) = ends (w :: Q) := by
    ext; simp [ends, Word.inv]
  rw [hends]
  -- Each identification after reflecting is one before, possibly in the other order (`k₁`),
  -- and conversely (`k₂`); then compare the classes with `f = g = id`.
  have k₁ : ∀ x y, Adj (Word.inv w :: Q) x y → Adj (w :: Q) y x ∨ Adj (w :: Q) x y := by
    intro x y
    simp only [adj_cons, mem_cyc_inv]
    rintro (⟨u, v, h, rfl, rfl⟩ | h)
    · exact Or.inl (Or.inl ⟨v.inv, u.inv, h, by simp, by simp⟩)
    · exact Or.inr (Or.inr h)
  have k₂ : ∀ x y, Adj (w :: Q) x y → Adj (Word.inv w :: Q) y x ∨ Adj (Word.inv w :: Q) x y := by
    intro x y
    simp only [adj_cons, mem_cyc_inv]
    rintro (⟨u, v, h, rfl, rfl⟩ | h)
    · exact Or.inl (Or.inl ⟨v.inv, u.inv, by simpa using h, by simp, by simp⟩)
    · exact Or.inr (Or.inr h)
  exact ncard_classes_eq id id (fun x y h => eqvGen_of_or (k₁ x y h))
    (fun x y h => eqvGen_of_or (k₂ x y h)) (fun x _ => EqvGen.refl x)
    (fun x _ => EqvGen.refl x) (fun _ h => h) (fun _ h => h)

/-- Reflecting does not change `E`: `W⁻¹` has the symbols of `W`. -/
theorem numE_reflect (w : Word α) (Q : Presentation α) :
    numE (Word.inv w :: Q) = numE (w :: Q) := by
  unfold numE; congr 1; ext; simp [Word.inv]

/-- Listing the words in another order does not change `V`: the same corners. -/
theorem numV_perm {P Q : Presentation α} (h : P.Perm Q) : numV P = numV Q := by
  refine numV_eq_of_adj (fun x y => ?_) ?_
  · simp only [adj_iff, h.mem_iff]
  · ext; simp [ends, h.mem_iff]

/-- Listing the words in another order does not change `E`. -/
theorem numE_perm {P Q : Presentation α} (h : P.Perm Q) : numE P = numE Q := by
  unfold numE; congr 1; ext; simp [h.mem_iff]

/-! ### Relabelling

Relabelling changes none of `V`, `E`, `F`: it renames the edge ends by a bijection. -/

/-- Unfolding: `(a, d)` is an edge end of `P` exactly when `a ∈ S`. -/
theorem mem_ends {P : Presentation α} {x : α × Bool} : x ∈ ends P ↔ x.1 ∈ syms P := Iff.rfl

/-- The symbols of `P` with the map `φ` applied to every letter: the symbols of the `φ(y)`. -/
theorem mem_syms_map {P : Presentation α} {φ : Letter α → Letter α} {b : α} :
    b ∈ syms (P.map (List.map φ)) ↔ ∃ w ∈ P, ∃ y ∈ w, (φ y).sym = b := by
  rw [mem_syms]
  constructor
  · rintro ⟨w', hw', y', hy', rfl⟩
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hw'
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hy'
    exact ⟨w, hw, y, hy, rfl⟩
  · rintro ⟨w, hw, y, hy, rfl⟩
    exact ⟨_, List.mem_map_of_mem hw, _, List.mem_map_of_mem hy, rfl⟩

/-- The identifications of `P` with `φ` applied to every letter: `(φ u).fin ∼ (φ v).ini` for each
corner `(u, v)` of `P`. -/
theorem adj_map {P : Presentation α} {φ : Letter α → Letter α} {x y : α × Bool} :
    Adj (P.map (List.map φ)) x y ↔ ∃ w ∈ P, ∃ u v, (u, v) ∈ cyc w ∧ (φ u).fin = x ∧ (φ v).ini = y := by
  rw [adj_iff]
  constructor
  · rintro ⟨w', hw', u', v', h, rfl, rfl⟩
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hw'
    rw [cyc_map] at h
    obtain ⟨⟨u, v⟩, huv, he⟩ := List.mem_map.1 h
    simp only [Prod.map, Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    exact ⟨w, hw, u, v, huv, rfl, rfl⟩
  · rintro ⟨w, hw, u, v, huv, rfl, rfl⟩
    refine ⟨_, List.mem_map_of_mem hw, φ u, φ v, ?_, rfl, rfl⟩
    rw [cyc_map]
    exact List.mem_map_of_mem (f := Prod.map φ φ) huv

/-- A map `φ` of letters that moves the edge ends by a bijection `ψ` does not change `V`.
Hypotheses: `hfin`, `hini`, `φ` moves the ends of every letter by `ψ`; `h₁`, `h₂`, `ψ'` is the
inverse of `ψ`; `hends`, `ψ'` carries the edge ends of the new presentation to those of the old.
Proof: `ψ` and `ψ'` carry corners to corners, so `ncard_classes_eq` applies. -/
theorem numV_map (P : Presentation α) (φ : Letter α → Letter α) (ψ ψ' : α × Bool → α × Bool)
    (hfin : ∀ u, (φ u).fin = ψ u.fin) (hini : ∀ u, (φ u).ini = ψ u.ini)
    (h₁ : ∀ x, ψ' (ψ x) = x) (h₂ : ∀ x, ψ (ψ' x) = x)
    (hends : ∀ x, x ∈ ends (P.map (List.map φ)) ↔ ψ' x ∈ ends P) :
    numV (P.map (List.map φ)) = numV P := by
  unfold numV
  refine ncard_classes_eq ψ' ψ (fun x y h => EqvGen.rel _ _ ?_) (fun x y h => EqvGen.rel _ _ ?_)
    (fun x _ => by rw [h₂]; exact EqvGen.refl x) (fun x _ => by rw [h₁]; exact EqvGen.refl x)
    (fun x hx => (hends x).1 hx) (fun y hy => (hends _).2 (by rwa [h₁]))
  · obtain ⟨w, hw, u, v, huv, rfl, rfl⟩ := adj_map.1 h
    exact adj_iff.2 ⟨w, hw, u, v, huv, by rw [hfin, h₁], by rw [hini, h₁]⟩
  · obtain ⟨w, hw, u, v, huv, rfl, rfl⟩ := adj_iff.1 h
    exact adj_map.2 ⟨w, hw, u, v, huv, hfin u, hini v⟩

/-- Renaming by `π` does not change `V`: it moves the end `(a, d)` to `(π(a), d)`, a bijection
with inverse `(a, d) ↦ (π⁻¹(a), d)` (`numV_map`). -/
theorem numV_relabel (π : α ≃ α) (P : Presentation α) : numV (relabel π P) = numV P :=
  numV_map P (fun x => ⟨π x.sym, x.dir⟩) (Prod.map π id) (Prod.map π.symm id) (fun _ => rfl)
    (fun _ => rfl) (fun x => by rcases x with ⟨b, d⟩; simp) (fun x => by rcases x with ⟨b, d⟩; simp)
    (fun x => by
      rw [mem_ends, mem_ends, mem_syms_map, mem_syms]
      simp only [Prod.map_fst]
      constructor
      · rintro ⟨w, hw, y, hy, h⟩
        exact ⟨w, hw, y, hy, by rw [← h]; simp⟩
      · rintro ⟨w, hw, y, hy, h⟩
        exact ⟨w, hw, y, hy, by simp [h]⟩)

/-- Renaming by `π` does not change `E`: the new symbol set is `π(S)`, which has as many
elements as `S` because `π` is injective. -/
theorem numE_relabel (π : α ≃ α) (P : Presentation α) : numE (relabel π P) = numE P := by
  unfold numE
  rw [show syms (relabel π P) = (syms P).map π.toEmbedding by
    ext b
    rw [relabel, mem_syms_map, Finset.mem_map]
    constructor
    · rintro ⟨w, hw, y, hy, rfl⟩
      exact ⟨y.sym, mem_syms.2 ⟨w, hw, y, hy, rfl⟩, rfl⟩
    · rintro ⟨_, hc, rfl⟩
      obtain ⟨w, hw, y, hy, rfl⟩ := mem_syms.1 hc
      exact ⟨w, hw, y, hy, rfl⟩]
  exact Finset.card_map _

/-- Interchanging the two ends of the edge `a`, `(a, d) ↦ (a, !d)`; the other ends stay. -/
def swapEnd (a : α) (x : α × Bool) : α × Bool := if x.1 = a then (x.1, !x.2) else x

/-- Interchanging the ends of `a` twice changes nothing. -/
theorem swapEnd_swapEnd (a : α) (x : α × Bool) : swapEnd a (swapEnd a x) = x := by
  rcases x with ⟨b, d⟩
  by_cases h : b = a <;> simp [swapEnd, h]

/-- `swapEnd a` keeps the symbol of an end. -/
theorem fst_swapEnd (a : α) (x : α × Bool) : (swapEnd a x).1 = x.1 := by
  -- (`split_ifs` splits the definition by `if` into its two cases.)
  unfold swapEnd; split_ifs <;> rfl

/-- Flipping `a` keeps the symbol of every letter. -/
theorem sym_flip (a : α) (y : Letter α) : (if y.sym = a then y.inv else y).sym = y.sym := by
  split_ifs <;> rfl

/-- Interchanging `a` and `a⁻¹` does not change `V`: it moves the edge ends by `swapEnd a`,
its own inverse (`numV_map`). -/
theorem numV_flip (a : α) (P : Presentation α) : numV (flipSym a P) = numV P :=
  numV_map P (fun x => if x.sym = a then x.inv else x) (swapEnd a) (swapEnd a)
    (fun u => by unfold swapEnd Letter.fin; split_ifs <;> simp_all [Letter.inv])
    (fun u => by unfold swapEnd Letter.ini; split_ifs <;> simp_all [Letter.inv])
    (swapEnd_swapEnd a) (swapEnd_swapEnd a) (fun x => by
      rw [mem_ends, mem_ends, mem_syms_map, mem_syms, fst_swapEnd]
      simp only [sym_flip])

/-- Interchanging `a` and `a⁻¹` does not change `E`: the symbols are the same. -/
theorem numE_flip (a : α) (P : Presentation α) : numE (flipSym a P) = numE P := by
  unfold numE; congr 1; ext b
  rw [flipSym, mem_syms_map, mem_syms]
  simp only [sym_flip]

/-! ### Cutting and folding

Cutting adds a symbol and a word and no vertex class; folding removes a symbol and a vertex
class (`prop:chi-invariant`). The vertex classes are compared with `ncard_classes_eq`, by maps
of edge ends that send the ends of the new edge `e` to ends they are glued to. -/

/-- Both entries of a consecutive pair of `l` are entries of `l`. -/
theorem mem_of_mem_lin {l : List β} {p : β × β} (h : p ∈ lin l) : p.1 ∈ l ∧ p.2 ∈ l := by
  induction l with
  | nil => simp at h
  | cons x t ih =>
    rcases mem_lin_cons.1 h with ⟨h1, h2⟩ | h
    · exact ⟨by simp [h1], List.mem_cons_of_mem _ (List.mem_of_mem_head? h2)⟩
    · exact ⟨List.mem_cons_of_mem _ (ih h).1, List.mem_cons_of_mem _ (ih h).2⟩

/-- Both letters at a corner of `l` are letters of `l`. -/
theorem mem_of_mem_cyc {l : List β} {p : β × β} (h : p ∈ cyc l) : p.1 ∈ l ∧ p.2 ∈ l := by
  rcases mem_cyc.1 h with h | ⟨h1, h2⟩
  · exact mem_of_mem_lin h
  · exact ⟨List.mem_of_getLast? h1, List.mem_of_mem_head? h2⟩

/-- A corner `(u, v)` of a word of `P` identifies `u.fin ∼ v.ini`. -/
theorem adj_of_cyc {P : Presentation α} {w : Word α} {u v : Letter α} (hw : w ∈ P)
    (h : (u, v) ∈ cyc w) : Adj P u.fin v.ini :=
  adj_iff.2 ⟨w, hw, u, v, h, rfl, rfl⟩

/-- A word of length at least `2` has a first letter `p` and a last letter `y`. -/
theorem exists_head_last {W : Word α} (h : 2 ≤ W.length) :
    ∃ p y, W.head? = some p ∧ W.getLast? = some y := by
  rcases W with _ | ⟨p, W⟩
  · simp at h
  · exact ⟨p, (p :: W).getLast (by simp), rfl, List.getLast?_eq_some_getLast _⟩

/-- A presentation has finitely many edge ends: they lie in `S × {true, false}`. (`×ˢ` is the
product of two finite sets.) -/
theorem ends_finite (P : Presentation α) : (ends P).Finite :=
  (Finset.finite_toSet (syms P ×ˢ (Finset.univ : Finset Bool))).subset
    (fun x hx => by
      simp only [Finset.coe_product, Finset.coe_univ, Set.mem_prod, Finset.mem_coe,
        Set.mem_univ, and_true]
      exact hx)

/-- A letter whose symbol is not `s` has neither end at `s`. -/
theorem letter_ne_of_sym {u : Letter α} {s : α} (hu : u.sym ≠ s) (d : Bool) :
    u.fin ≠ (s, d) ∧ u.ini ≠ (s, d) := by
  simp [Letter.fin, Letter.ini, hu]

/-- Cutting does not change `V` (`prop:chi-invariant`): the two ends of the new edge `e` are each
joined to the ends that the old corners joined directly.

Picture: let `W₁` run from `p` (its first letter) to `y` (its last), and `W₂` from `q` to `z`.
The old polygon `W₁W₂` has the corners `(y, q)` and `(z, p)` where `W₁` meets `W₂`, gluing
`y.fin ∼ q.ini` and `z.fin ∼ p.ini`. The new polygons `W₁e`, `e⁻¹W₂` have instead the corners
`(y, e)`, `(e, p)`, `(e⁻¹, q)`, `(z, e⁻¹)`, gluing `y.fin ∼ e.ini ∼ q.ini` and
`z.fin ∼ e.fin ∼ p.ini`: the two old identifications, each through one end of the diagonal `e`.
All the other corners are the same. So the classes correspond: send `e.ini ↦ y.fin`,
`e.fin ↦ z.fin` and every other end to itself (`f`), and compare with `ncard_classes_eq`. -/
theorem numV_cut (W₁ W₂ : Word α) (e : Letter α) (Q : Presentation α) (h₁ : 2 ≤ W₁.length)
    (h₂ : 2 ≤ W₂.length) (he : e.sym ∉ syms ((W₁ ++ W₂) :: Q)) :
    numV ((W₁ ++ [e]) :: (e.inv :: W₂) :: Q) = numV ((W₁ ++ W₂) :: Q) := by
  -- The first and last letters `p`, `y` of `W₁` and `q`, `z` of `W₂`; `s` is the symbol of `e`,
  -- which occurs in none of `W₁`, `W₂`, `Q` (`hW₁`, `hW₂`, `hQ`).
  obtain ⟨p, y, hp, hy⟩ := exists_head_last h₁
  obtain ⟨q, z, hq, hz⟩ := exists_head_last h₂
  have hpW := List.mem_of_mem_head? hp
  have hyW := List.mem_of_getLast? hy
  have hqW := List.mem_of_mem_head? hq
  have hzW := List.mem_of_getLast? hz
  set s := e.sym with hs
  simp only [mem_syms, List.mem_cons, List.mem_append, not_exists, not_and] at he
  have hW₁ : ∀ u ∈ W₁, u.sym ≠ s := fun u hu => he _ (Or.inl rfl) u (List.mem_append_left _ hu)
  have hW₂ : ∀ u ∈ W₂, u.sym ≠ s := fun u hu => he _ (Or.inl rfl) u (List.mem_append_right _ hu)
  have hQ : ∀ w ∈ Q, ∀ u ∈ w, u.sym ≠ s := fun w hw u hu => he w (Or.inr hw) u hu
  have hei : e.ini = (s, !e.dir) := rfl
  have hef : e.fin = (s, e.dir) := rfl
  -- The map `f` from the new ends to the old: `e.ini ↦ y.fin`, `e.fin ↦ z.fin`, the rest fixed.
  let f : α × Bool → α × Bool := fun x =>
    if x = e.ini then y.fin else if x = e.fin then z.fin else x
  have hfix : ∀ x : α × Bool, x.1 ≠ s → f x = x := by
    intro x hx
    have h1 : x ≠ e.ini := fun h => hx (by rw [h]; rfl)
    have h2 : x ≠ e.fin := fun h => hx (by rw [h]; rfl)
    simp only [f, h1, h2, ite_false]
  have fini : f e.ini = y.fin := by simp [f]
  have ffin : f e.fin = z.fin := by
    have : e.fin ≠ e.ini := by simp [Letter.fin, Letter.ini]
    simp [f, this]
  -- the cyclic pairs of the new words and of the old one
  -- The corners of the new words `W₁e` (`cyc₁`) and `e⁻¹W₂` (`cyc₂`) and of the old word
  -- `W₁W₂` (`cyc₀`), as in the picture of the docstring. (`grind` does the case analysis on
  -- the lists.)
  have cyc₁ : ∀ {u v : Letter α}, (u, v) ∈ cyc (W₁ ++ [e]) ↔
      (u, v) ∈ lin W₁ ∨ (u = y ∧ v = e) ∨ (u = e ∧ v = p) := by
    intro u v
    simp only [mem_cyc, mem_lin_append, lin_singleton, List.not_mem_nil, List.getLast?_append,
      List.getLast?_singleton, Option.some_or, List.head?_append, hp, hy, List.head?_cons,
      Option.some.injEq, false_or]
    grind
  have cyc₂ : ∀ {u v : Letter α}, (u, v) ∈ cyc (e.inv :: W₂) ↔
      (u = e.inv ∧ v = q) ∨ (u, v) ∈ lin W₂ ∨ (u = z ∧ v = e.inv) := by
    intro u v
    rw [mem_cyc, mem_lin_cons]
    rcases W₂ with _ | ⟨q', W₂'⟩
    · simp at h₂
    · simp only [List.head?_cons, Option.some.injEq] at hq hz ⊢
      rw [List.getLast?_cons_cons, hz]
      simp only [Option.some.injEq]
      grind
  have cyc₀ : ∀ {u v : Letter α}, (u, v) ∈ cyc (W₁ ++ W₂) ↔
      (u, v) ∈ lin W₁ ∨ (u, v) ∈ lin W₂ ∨ (u = y ∧ v = q) ∨ (u = z ∧ v = p) := by
    intro u v
    simp only [mem_cyc, mem_lin_append, List.getLast?_append, List.head?_append, hp, hy, hq, hz,
      Option.some_or, Option.some.injEq]
    grind
  -- The corners inside `W₁` or `W₂` are corners both before and after cutting.
  have old_lin : ∀ {u v : Letter α}, (u, v) ∈ lin W₁ ∨ (u, v) ∈ lin W₂ →
      Adj ((W₁ ++ W₂) :: Q) u.fin v.ini := fun h =>
    adj_of_cyc (List.mem_cons_self ..) (cyc₀.2 (h.elim Or.inl (fun h => Or.inr (Or.inl h))))
  have new_lin₁ : ∀ {u v : Letter α}, (u, v) ∈ lin W₁ →
      Adj ((W₁ ++ [e]) :: (e.inv :: W₂) :: Q) u.fin v.ini := fun h =>
    adj_of_cyc (List.mem_cons_self ..) (cyc₁.2 (Or.inl h))
  have new_lin₂ : ∀ {u v : Letter α}, (u, v) ∈ lin W₂ →
      Adj ((W₁ ++ [e]) :: (e.inv :: W₂) :: Q) u.fin v.ini := fun h =>
    adj_of_cyc (List.mem_cons_of_mem _ (List.mem_cons_self ..)) (cyc₂.2 (Or.inr (Or.inl h)))
  -- The four new identifications at the ends of `e`.
  have new_ye : Adj ((W₁ ++ [e]) :: (e.inv :: W₂) :: Q) y.fin e.ini :=
    adj_of_cyc (List.mem_cons_self ..) (cyc₁.2 (Or.inr (Or.inl ⟨rfl, rfl⟩)))
  have new_ep : Adj ((W₁ ++ [e]) :: (e.inv :: W₂) :: Q) e.fin p.ini :=
    adj_of_cyc (List.mem_cons_self ..) (cyc₁.2 (Or.inr (Or.inr ⟨rfl, rfl⟩)))
  have new_eq : Adj ((W₁ ++ [e]) :: (e.inv :: W₂) :: Q) e.ini q.ini := by
    have := adj_of_cyc (P := (W₁ ++ [e]) :: (e.inv :: W₂) :: Q)
      (List.mem_cons_of_mem _ (List.mem_cons_self ..)) (cyc₂.2 (Or.inl ⟨rfl, rfl⟩))
    simpa using this
  have new_ze : Adj ((W₁ ++ [e]) :: (e.inv :: W₂) :: Q) z.fin e.fin := by
    have := adj_of_cyc (P := (W₁ ++ [e]) :: (e.inv :: W₂) :: Q)
      (List.mem_cons_of_mem _ (List.mem_cons_self ..)) (cyc₂.2 (Or.inr (Or.inr ⟨rfl, rfl⟩)))
    simpa using this
  -- No letter at a corner inside `W₁` or `W₂` has the symbol `s`, so `f` fixes its ends.
  have symW : ∀ {u v : Letter α}, (u, v) ∈ lin W₁ ∨ (u, v) ∈ lin W₂ → u.sym ≠ s ∧ v.sym ≠ s := by
    rintro u v (h | h)
    · exact ⟨hW₁ _ (mem_of_mem_lin h).1, hW₁ _ (mem_of_mem_lin h).2⟩
    · exact ⟨hW₂ _ (mem_of_mem_lin h).1, hW₂ _ (mem_of_mem_lin h).2⟩
  -- Now compare the classes.
  unfold numV
  refine ncard_classes_eq f id ?_ ?_ ?_ ?_ ?_ ?_
  -- The six conditions of `ncard_classes_eq`, for `f` from the new ends to the old and the
  -- identity from the old ends to the new.
  -- (1) `f` sends each new identification to an old chain: the corners inside `W₁` and `W₂`
  -- and in `Q` are old corners; `(y, e)` and `(z, e⁻¹)` become trivial; `(e, p)` and `(e⁻¹, q)`
  -- become the old corners `(z, p)` and `(y, q)`.
  ·
    intro a b h
    rcases adj_cons.1 h with ⟨u, v, huv, rfl, rfl⟩ | h
    · rcases cyc₁.1 huv with huv | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · obtain ⟨hu, hv⟩ := symW (Or.inl huv)
        rw [hfix _ hu, hfix _ hv]; exact EqvGen.rel _ _ (old_lin (Or.inl huv))
      · rw [fini, hfix _ (hW₁ _ hyW)]; exact EqvGen.refl _
      · rw [ffin, hfix _ (hW₁ _ hpW)]
        exact EqvGen.rel _ _ (adj_of_cyc (List.mem_cons_self ..) (cyc₀.2 (Or.inr (Or.inr
          (Or.inr ⟨rfl, rfl⟩)))))
    rcases adj_cons.1 h with ⟨u, v, huv, rfl, rfl⟩ | h
    · rcases cyc₂.1 huv with ⟨rfl, rfl⟩ | huv | ⟨rfl, rfl⟩
      · simp only [Letter.fin_inv]
        rw [fini, hfix _ (hW₂ _ hqW)]
        exact EqvGen.rel _ _ (adj_of_cyc (List.mem_cons_self ..) (cyc₀.2 (Or.inr (Or.inr
          (Or.inl ⟨rfl, rfl⟩)))))
      · obtain ⟨hu, hv⟩ := symW (Or.inr huv)
        rw [hfix _ hu, hfix _ hv]; exact EqvGen.rel _ _ (old_lin (Or.inr huv))
      · simp only [Letter.ini_inv]
        rw [ffin, hfix _ (hW₂ _ hzW)]; exact EqvGen.refl _
    · obtain ⟨w, hw, u, v, huv, rfl, rfl⟩ := adj_iff.1 h
      have hu := hQ w hw u (mem_of_mem_cyc huv).1
      have hv := hQ w hw v (mem_of_mem_cyc huv).2
      rw [hfix _ hu, hfix _ hv]
      exact EqvGen.rel _ _ (adj_of_cyc (List.mem_cons_of_mem _ hw) huv)
  -- (2) Each old identification is a chain of new ones: the old corner `(y, q)` is the chain
  -- `y.fin ∼ e.ini ∼ q.ini`, and `(z, p)` is `z.fin ∼ e.fin ∼ p.ini`; the others are new corners.
  ·
    intro a b h
    rcases adj_cons.1 h with ⟨u, v, huv, rfl, rfl⟩ | h
    · rcases cyc₀.1 huv with huv | huv | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact EqvGen.rel _ _ (new_lin₁ huv)
      · exact EqvGen.rel _ _ (new_lin₂ huv)
      · exact EqvGen.trans _ _ _ (EqvGen.rel _ _ new_ye) (EqvGen.rel _ _ new_eq)
      · exact EqvGen.trans _ _ _ (EqvGen.rel _ _ new_ze) (EqvGen.rel _ _ new_ep)
    · obtain ⟨w, hw, u, v, huv, rfl, rfl⟩ := adj_iff.1 h
      exact EqvGen.rel _ _ (adj_of_cyc (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hw)) huv)
  -- (3) Every new end `x` is in the class of `f(x)`: `e.ini ∼ y.fin` and `e.fin ∼ z.fin` by
  -- the corners `(y, e)` and `(z, e⁻¹)`, and `f` fixes the other ends.
  · intro x _
    simp only [id]
    by_cases h1 : x = e.ini
    · subst h1; rw [fini]; exact EqvGen.rel _ _ new_ye
    by_cases h2 : x = e.fin
    · subst h2; rw [ffin]; exact EqvGen.rel _ _ new_ze
    simp only [f, h1, h2, ite_false]; exact EqvGen.refl _
  -- (4) `f` fixes every old end, since no old end has the symbol `s`.
  · intro x hx
    simp only [id]
    rw [hfix]
    · exact EqvGen.refl _
    · rintro hxs
      rw [mem_ends, mem_syms] at hx
      obtain ⟨w, hw, u, hu, hus⟩ := hx
      rcases List.mem_cons.1 hw with rfl | hw
      · rcases List.mem_append.1 hu with hu | hu
        · exact hW₁ u hu (hus.trans hxs)
        · exact hW₂ u hu (hus.trans hxs)
      · exact hQ w hw u hu (hus.trans hxs)
  -- (5) `f` sends new ends to old ends: `e.ini`, `e.fin` go to ends of `y`, `z`, and every
  -- other new end belongs to an old letter.
  · intro x hx
    by_cases h1 : x = e.ini
    · rw [h1, fini, mem_ends, mem_syms]; exact ⟨_, List.mem_cons_self .., y, by simp [hyW], rfl⟩
    by_cases h2 : x = e.fin
    · rw [h2, ffin, mem_ends, mem_syms]; exact ⟨_, List.mem_cons_self .., z, by simp [hzW], rfl⟩
    simp only [f, h1, h2, ite_false]
    rw [mem_ends, mem_syms] at hx ⊢
    obtain ⟨w, hw, u, hu, hus⟩ := hx
    have hxs : x.1 ≠ s := by
      intro hxs
      rcases x with ⟨b, d⟩
      simp only at hxs
      subst hxs
      cases d <;> cases hd : e.dir <;> simp_all [Letter.fin, Letter.ini]
    simp only [List.mem_cons] at hw
    rcases hw with rfl | rfl | hw
    · rcases List.mem_append.1 hu with hu | hu
      · exact ⟨_, List.mem_cons_self .., u, by simp [hu], hus⟩
      · rw [List.mem_singleton] at hu; subst hu; exact absurd hus.symm hxs
    · rcases List.mem_cons.1 hu with rfl | hu
      · exact absurd hus.symm hxs
      · exact ⟨_, List.mem_cons_self .., u, by simp [hu], hus⟩
    · exact ⟨w, List.mem_cons_of_mem _ hw, u, hu, hus⟩
  -- (6) Every old end is a new end: each letter of `W₁W₂` and of `Q` is still there.
  · intro x hx
    rw [mem_ends, mem_syms] at hx ⊢
    obtain ⟨w, hw, u, hu, hus⟩ := hx
    rcases List.mem_cons.1 hw with rfl | hw
    · rcases List.mem_append.1 hu with hu | hu
      · exact ⟨_, List.mem_cons_self .., u, by simp [hu], hus⟩
      · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), u, by simp [hu], hus⟩
    · exact ⟨w, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hw), u, hu, hus⟩

/-- Folding removes one vertex class (`prop:chi-invariant`): the end of `e` between `e` and
`e⁻¹`, identified with nothing else. (Here only `W₁` of length at least `2` is needed.)

Picture: the polygon `W₁ee⁻¹`, `W₁` running from its first letter `p` to its last `y`. Its
corners are those inside `W₁`, `(y, e)`, `(e, e⁻¹)` and `(e⁻¹, p)`. Folding zips `e` onto `e⁻¹`:
the vertex at the tip, the end `e.fin` between `e` and `e⁻¹`, disappears, and the vertex where
`y` meets `e`, the same as the one where `e⁻¹` meets `p`, becomes the corner `(y, p)` of `W₁`. -/
theorem numV_fold (W₁ : Word α) (e : Letter α) (Q : Presentation α) (h₁ : 2 ≤ W₁.length)
    (he : e.sym ∉ syms (W₁ :: Q)) :
    numV ((W₁ ++ [e, e.inv]) :: Q) = numV (W₁ :: Q) + 1 := by
  -- The first and last letters `p`, `y` of `W₁`; `s` is the symbol of `e`, which occurs in
  -- neither `W₁` nor `Q`. `Pold` is the presentation before folding, `Pnew` the one after.
  obtain ⟨p, y, hp, hy⟩ := exists_head_last h₁
  have hpW := List.mem_of_mem_head? hp
  have hyW := List.mem_of_getLast? hy
  set s := e.sym with hs
  simp only [mem_syms, List.mem_cons, not_exists, not_and] at he
  have hW₁ : ∀ u ∈ W₁, u.sym ≠ s := fun u hu => he _ (Or.inl rfl) u hu
  have hQ : ∀ w ∈ Q, ∀ u ∈ w, u.sym ≠ s := fun w hw u hu => he w (Or.inr hw) u hu
  set Pold := (W₁ ++ [e, e.inv]) :: Q with hPold
  set Pnew := W₁ :: Q with hPnew
  -- The corners of `W₁ee⁻¹` (`cyc₁`): those inside `W₁`, `(y, e)`, `(e, e⁻¹)`, `(e⁻¹, p)`;
  -- and of `W₁` (`cyc₀`): those inside `W₁` and `(y, p)`.
  have cyc₁ : ∀ {u v : Letter α}, (u, v) ∈ cyc (W₁ ++ [e, e.inv]) ↔
      (u, v) ∈ lin W₁ ∨ (u = y ∧ v = e) ∨ (u = e ∧ v = e.inv) ∨ (u = e.inv ∧ v = p) := by
    intro u v
    simp only [mem_cyc, mem_lin_append, List.getLast?_append, List.head?_append, hp, hy,
      Option.some_or, Option.some.injEq, lin, List.mem_singleton, List.head?_cons,
      List.getLast?_cons_cons, List.getLast?_singleton, Prod.mk.injEq, lin_singleton,
      List.mem_cons, List.not_mem_nil]
    grind
  have cyc₀ : ∀ {u v : Letter α}, (u, v) ∈ cyc W₁ ↔ (u, v) ∈ lin W₁ ∨ (u = y ∧ v = p) := by
    intro u v
    simp only [mem_cyc, hp, hy, Option.some.injEq]
    grind
  have symW : ∀ {u v : Letter α}, (u, v) ∈ lin W₁ → u.sym ≠ s ∧ v.sym ≠ s := fun h =>
    ⟨hW₁ _ (mem_of_mem_lin h).1, hW₁ _ (mem_of_mem_lin h).2⟩
  -- Before folding, `y.fin ∼ e.ini ∼ p.ini`, by the corners `(y, e)` and `(e⁻¹, p)`.
  have old_ye : Adj Pold y.fin e.ini :=
    adj_of_cyc (List.mem_cons_self ..) (cyc₁.2 (Or.inr (Or.inl ⟨rfl, rfl⟩)))
  have old_ep : Adj Pold e.ini p.ini := by
    have := adj_of_cyc (P := Pold) (List.mem_cons_self ..)
      (cyc₁.2 (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))))
    simpa using this
  -- Step 1. The end `e.fin`, the tip of the fold between `e` and `e⁻¹`, is identified with
  -- nothing else: the corner `(e, e⁻¹)` glues it to itself (`(e⁻¹).ini = e.fin`), and no other
  -- corner touches it, since `e` occurs nowhere else. So it is a class on its own (`iso'`
  -- extends this from one identification to chains).
  -- the end `e.fin` is identified with nothing else
  have iso : ∀ a b, Adj Pold a b → (a = e.fin ↔ b = e.fin) := by
    intro a b h
    have fin_ne : ∀ {u : Letter α}, u.sym ≠ s → u.fin ≠ e.fin := fun hu h =>
      hu (congrArg Prod.fst h)
    have ini_ne : ∀ {u : Letter α}, u.sym ≠ s → u.ini ≠ e.fin := fun hu h =>
      hu (congrArg Prod.fst h)
    have eini_ne : e.ini ≠ e.fin := by simp [Letter.ini, Letter.fin]
    rcases adj_cons.1 h with ⟨u, v, huv, rfl, rfl⟩ | h
    · rcases cyc₁.1 huv with huv | ⟨hu, hv⟩ | ⟨hu, hv⟩ | ⟨hu, hv⟩
      · exact iff_of_false (fin_ne (symW huv).1) (ini_ne (symW huv).2)
      · rw [hu, hv]; exact iff_of_false (fin_ne (hW₁ _ hyW)) eini_ne
      · rw [hu, hv, Letter.ini_inv]
      · rw [hu, hv, Letter.fin_inv]; exact iff_of_false eini_ne (ini_ne (hW₁ _ hpW))
    · obtain ⟨w, hw, u, v, huv, rfl, rfl⟩ := adj_iff.1 h
      exact iff_of_false (fin_ne (hQ w hw u (mem_of_mem_cyc huv).1))
        (ini_ne (hQ w hw v (mem_of_mem_cyc huv).2))
  have iso' : ∀ a b, EqvGen (Adj Pold) a b → (a = e.fin ↔ b = e.fin) := by
    intro a b h
    induction h with
    | rel a b h => exact iso a b h
    | refl => exact Iff.rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  -- Step 2. So the classes of `Pold` are the class `{e.fin}` and the classes of the other ends,
  -- which do not contain it: `V(Pold) = 1 + (number of classes of the ends other than e.fin)`.
  have hefin : e.fin ∈ ends Pold := by
    rw [mem_ends, mem_syms]; exact ⟨_, List.mem_cons_self .., e, by simp, rfl⟩
  have hsplit : ends Pold = insert e.fin (ends Pold \ {e.fin}) := by
    rw [Set.insert_sdiff_singleton, Set.insert_eq_of_mem hefin]
  have hnot : Quot.mk (Adj Pold) e.fin ∉ Quot.mk (Adj Pold) '' (ends Pold \ {e.fin}) := by
    rintro ⟨x, ⟨_, hx⟩, hxe⟩
    exact hx ((iso' _ _ (Quot.eqvGen_exact hxe)).2 rfl)
  have hfinite : (Quot.mk (Adj Pold) '' (ends Pold \ {e.fin})).Finite :=
    ((ends_finite _).subset Set.sdiff_subset).image _
  unfold numV
  rw [hsplit, Set.image_insert_eq, Set.ncard_insert_of_notMem hnot hfinite]
  congr 1
  -- Step 3. The other ends of `Pold` and the ends of `Pnew` have equally many classes. Send
  -- the remaining end `e.ini` of `e` to `y.fin` (`f`), and the old ends to themselves (`id`).
  let f : α × Bool → α × Bool := fun x => if x.1 = s then y.fin else x
  have hfix : ∀ x : α × Bool, x.1 ≠ s → f x = x := fun x hx => by simp [f, hx]
  have hfs : ∀ x : α × Bool, x.1 = s → f x = y.fin := fun x hx => by simp [f, hx]
  refine ncard_classes_eq f id ?_ ?_ ?_ ?_ ?_ ?_
  -- (1) `f` sends each identification of `Pold` to a chain of `Pnew`: corners inside `W₁` or in
  -- `Q` stay; `(y, e)`, `(e, e⁻¹)` become trivial; `(e⁻¹, p)` becomes the corner `(y, p)`.
  · intro a b h
    rcases adj_cons.1 h with ⟨u, v, huv, rfl, rfl⟩ | h
    · rcases cyc₁.1 huv with huv | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · obtain ⟨hu, hv⟩ := symW huv
        rw [hfix _ hu, hfix _ hv]
        exact EqvGen.rel _ _ (adj_of_cyc (List.mem_cons_self ..) (cyc₀.2 (Or.inl huv)))
      · rw [hfix _ (hW₁ _ hyW), hfs _ rfl]; exact EqvGen.refl _
      · rw [hfs _ rfl, hfs _ rfl]; exact EqvGen.refl _
      · rw [hfs _ rfl, hfix _ (hW₁ _ hpW)]
        exact EqvGen.rel _ _ (adj_of_cyc (List.mem_cons_self ..) (cyc₀.2 (Or.inr ⟨rfl, rfl⟩)))
    · obtain ⟨w, hw, u, v, huv, rfl, rfl⟩ := adj_iff.1 h
      have hu := hQ w hw u (mem_of_mem_cyc huv).1
      have hv := hQ w hw v (mem_of_mem_cyc huv).2
      rw [hfix _ hu, hfix _ hv]
      exact EqvGen.rel _ _ (adj_of_cyc (List.mem_cons_of_mem _ hw) huv)
  -- (2) The corner `(y, p)` of `W₁` is the chain `y.fin ∼ e.ini ∼ p.ini` of `Pold`; the other
  -- corners of `Pnew` are corners of `Pold`.
  · intro a b h
    rcases adj_cons.1 h with ⟨u, v, huv, rfl, rfl⟩ | h
    · rcases cyc₀.1 huv with huv | ⟨rfl, rfl⟩
      · exact EqvGen.rel _ _ (adj_of_cyc (List.mem_cons_self ..) (cyc₁.2 (Or.inl huv)))
      · exact EqvGen.trans _ _ _ (EqvGen.rel _ _ old_ye) (EqvGen.rel _ _ old_ep)
    · obtain ⟨w, hw, u, v, huv, rfl, rfl⟩ := adj_iff.1 h
      exact EqvGen.rel _ _ (adj_of_cyc (List.mem_cons_of_mem _ hw) huv)
  -- (3) Every remaining end `x` of `Pold` is in the class of `f(x)`: the only one moved is
  -- `e.ini ↦ y.fin`, and `y.fin ∼ e.ini`.
  · rintro x ⟨_, hxe⟩
    simp only [id]
    by_cases hx : x.1 = s
    · have : x = e.ini := by
        rcases x with ⟨b, d⟩
        simp only at hx; subst hx
        simp only [Set.mem_singleton_iff, Letter.fin, Prod.mk.injEq, true_and] at hxe
        simp [Letter.ini]; cases d <;> cases hd : e.dir <;> simp_all
      rw [hfs _ hx, this]; exact EqvGen.rel _ _ old_ye
    · rw [hfix _ hx]; exact EqvGen.refl _
  -- (4) `f` fixes every end of `Pnew`: none has the symbol `s`.
  · intro x hx
    simp only [id]
    rw [hfix]
    · exact EqvGen.refl _
    · rintro hxs
      rw [mem_ends, mem_syms] at hx
      obtain ⟨w, hw, u, hu, hus⟩ := hx
      rcases List.mem_cons.1 hw with rfl | hw
      · exact hW₁ u hu (hus.trans hxs)
      · exact hQ w hw u hu (hus.trans hxs)
  -- (5) `f` sends the remaining ends of `Pold` to ends of `Pnew`.
  · rintro x ⟨hx, -⟩
    by_cases hxs : x.1 = s
    · rw [hfs _ hxs, mem_ends, mem_syms]; exact ⟨_, List.mem_cons_self .., y, hyW, rfl⟩
    rw [hfix _ hxs]
    rw [mem_ends, mem_syms] at hx ⊢
    obtain ⟨w, hw, u, hu, hus⟩ := hx
    rcases List.mem_cons.1 hw with rfl | hw
    · rcases List.mem_append.1 hu with hu | hu
      · exact ⟨_, List.mem_cons_self .., u, hu, hus⟩
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
        rcases hu with rfl | rfl <;> exact absurd hus.symm hxs
    · exact ⟨w, List.mem_cons_of_mem _ hw, u, hu, hus⟩
  -- (6) Every end of `Pnew` is an end of `Pold` other than `e.fin`.
  · intro x hx
    have hxs : x.1 ≠ s := by
      rintro hxs
      rw [mem_ends, mem_syms] at hx
      obtain ⟨w, hw, u, hu, hus⟩ := hx
      rcases List.mem_cons.1 hw with rfl | hw
      · exact hW₁ u hu (hus.trans hxs)
      · exact hQ w hw u hu (hus.trans hxs)
    refine ⟨?_, fun h => hxs (by simp only [Set.mem_singleton_iff] at h; subst h; rfl)⟩
    rw [mem_ends, mem_syms] at hx ⊢
    obtain ⟨w, hw, u, hu, hus⟩ := hx
    rcases List.mem_cons.1 hw with rfl | hw
    · exact ⟨_, List.mem_cons_self .., u, List.mem_append_left _ hu, hus⟩
    · exact ⟨w, List.mem_cons_of_mem _ hw, u, hu, hus⟩

/-- The symbols of `⟨W, …⟩`: those of `W` and those of the other words. -/
theorem mem_syms_cons {w : Word α} {Q : Presentation α} {b : α} :
    b ∈ syms (w :: Q) ↔ (∃ x ∈ w, x.sym = b) ∨ b ∈ syms Q := by
  simp only [mem_syms, List.mem_cons, exists_eq_or_imp]

/-- Some entry of `uv` has `p` exactly when some entry of `u` or of `v` has. -/
theorem exists_mem_append' {u v : List γ} {p : γ → Prop} :
    (∃ x ∈ u ++ v, p x) ↔ (∃ x ∈ u, p x) ∨ ∃ x ∈ v, p x := by
  simp only [List.mem_append]
  constructor
  · rintro ⟨x, hx | hx, h⟩
    · exact Or.inl ⟨x, hx, h⟩
    · exact Or.inr ⟨x, hx, h⟩
  · rintro (⟨x, hx, h⟩ | ⟨x, hx, h⟩)
    · exact ⟨x, Or.inl hx, h⟩
    · exact ⟨x, Or.inr hx, h⟩

/-- Some entry of `xu` has `p` exactly when `x` has or some entry of `u` has. -/
theorem exists_mem_cons' {x : γ} {u : List γ} {p : γ → Prop} :
    (∃ y ∈ x :: u, p y) ↔ p x ∨ ∃ y ∈ u, p y := by
  simp

/-- Cutting adds one symbol, the new `e` (`prop:chi-invariant`): the symbols of `W₁e`,
`e⁻¹W₂` and `Q` are those of `W₁W₂` and `Q`, and `e`. -/
theorem numE_cut (W₁ W₂ : Word α) (e : Letter α) (Q : Presentation α)
    (he : e.sym ∉ syms ((W₁ ++ W₂) :: Q)) :
    numE ((W₁ ++ [e]) :: (e.inv :: W₂) :: Q) = numE ((W₁ ++ W₂) :: Q) + 1 := by
  unfold numE
  rw [← Finset.card_insert_of_notMem he]
  congr 1
  ext b
  simp only [Finset.mem_insert, mem_syms_cons, exists_mem_append', exists_mem_cons',
    Letter.inv_sym, List.not_mem_nil, false_and, exists_false, or_false]
  grind

/-- Folding removes one symbol, `e` (`prop:chi-invariant`), read as: the symbols before folding
are those after, and `e`. -/
theorem numE_fold (W₁ : Word α) (e : Letter α) (Q : Presentation α)
    (he : e.sym ∉ syms (W₁ :: Q)) :
    numE ((W₁ ++ [e, e.inv]) :: Q) = numE (W₁ :: Q) + 1 := by
  unfold numE
  rw [← Finset.card_insert_of_notMem he]
  congr 1
  ext b
  simp only [Finset.mem_insert, mem_syms_cons, exists_mem_append', exists_mem_cons',
    Letter.inv_sym, List.not_mem_nil, false_and, exists_false, or_false]
  grind

/-! ### Subdividing

Subdividing adds a symbol and a vertex class (`prop:chi-invariant`). First, four facts about
`w.flatMap σ`, the word in which each letter `x` of `w` is replaced by a non-empty word
`σ x`: its first and last letters, and its consecutive and cyclic pairs. -/

/-- The first letter of `w.flatMap σ` is the first letter of `σ v`, `v` the first of `w`. -/
theorem head?_flatMap_eq_some {σ : β → List γ} (hσ : ∀ x, σ x ≠ []) {w : List β} {q : γ} :
    (w.flatMap σ).head? = some q ↔ ∃ v, w.head? = some v ∧ (σ v).head? = some q := by
  rcases w with _ | ⟨v, t⟩
  · simp
  · have : (σ v).head?.isSome := by
      cases h : (σ v).head? with
      | none => exact absurd (List.head?_eq_none_iff.1 h) (hσ v)
      | some _ => rfl
    simp only [List.flatMap_cons, List.head?_append, List.head?_cons, Option.some.injEq,
      exists_eq_left']
    cases h : (σ v).head? with
    | none => simp [h] at this
    | some r => simp

/-- The last letter of `w.flatMap σ` is the last letter of `σ u`, `u` the last of `w`. -/
theorem getLast?_flatMap_eq_some {σ : β → List γ} (hσ : ∀ x, σ x ≠ []) {w : List β} {q : γ} :
    (w.flatMap σ).getLast? = some q ↔ ∃ u, w.getLast? = some u ∧ (σ u).getLast? = some q := by
  rw [← List.head?_reverse, List.reverse_flatMap,
    head?_flatMap_eq_some (σ := List.reverse ∘ σ) (fun x => by simpa using hσ x)]
  simp

/-- The consecutive pairs of `w.flatMap σ`: those inside some `σ x`, and, for each consecutive
pair `(u, v)` of `w`, (last letter of `σ u`, first letter of `σ v`). -/
theorem mem_lin_flatMap {σ : β → List γ} (hσ : ∀ x, σ x ≠ []) {w : List β} {p : γ × γ} :
    p ∈ lin (w.flatMap σ) ↔ (∃ x ∈ w, p ∈ lin (σ x)) ∨
      ∃ u v, (u, v) ∈ lin w ∧ (σ u).getLast? = some p.1 ∧ (σ v).head? = some p.2 := by
  induction w with
  | nil => simp
  | cons x t ih =>
    rw [List.flatMap_cons, mem_lin_append, ih, head?_flatMap_eq_some hσ]
    simp only [List.mem_cons, mem_lin_cons]
    constructor
    · rintro (h | (⟨y, hy, h⟩ | ⟨u, v, huv, h1, h2⟩) | ⟨h1, v, hv, h2⟩)
      · exact Or.inl ⟨x, Or.inl rfl, h⟩
      · exact Or.inl ⟨y, Or.inr hy, h⟩
      · exact Or.inr ⟨u, v, Or.inr huv, h1, h2⟩
      · exact Or.inr ⟨x, v, Or.inl ⟨rfl, hv⟩, h1, h2⟩
    · rintro (⟨y, (rfl | hy), h⟩ | ⟨u, v, (⟨rfl, hv⟩ | huv), h1, h2⟩)
      · exact Or.inl h
      · exact Or.inr (Or.inl (Or.inl ⟨y, hy, h⟩))
      · exact Or.inr (Or.inr ⟨h1, v, hv, h2⟩)
      · exact Or.inr (Or.inl (Or.inr ⟨u, v, huv, h1, h2⟩))

/-- The cyclic pairs of `w.flatMap σ`: those inside some `σ x`, and, for each cyclic pair
`(u, v)` of `w`, (last letter of `σ u`, first letter of `σ v`). -/
theorem mem_cyc_flatMap {σ : β → List γ} (hσ : ∀ x, σ x ≠ []) {w : List β} {p : γ × γ} :
    p ∈ cyc (w.flatMap σ) ↔ (∃ x ∈ w, p ∈ lin (σ x)) ∨
      ∃ u v, (u, v) ∈ cyc w ∧ (σ u).getLast? = some p.1 ∧ (σ v).head? = some p.2 := by
  rw [mem_cyc, mem_lin_flatMap hσ, getLast?_flatMap_eq_some hσ, head?_flatMap_eq_some hσ]
  simp only [mem_cyc]
  constructor
  · rintro ((h | ⟨u, v, huv, h1, h2⟩) | ⟨⟨u, hu, h1⟩, ⟨v, hv, h2⟩⟩)
    · exact Or.inl h
    · exact Or.inr ⟨u, v, Or.inl huv, h1, h2⟩
    · exact Or.inr ⟨u, v, Or.inr ⟨hu, hv⟩, h1, h2⟩
  · rintro (h | ⟨u, v, (huv | ⟨hu, hv⟩), h1, h2⟩)
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr ⟨u, v, huv, h1, h2⟩)
    · exact Or.inr ⟨⟨u, hu, h1⟩, ⟨v, hv, h2⟩⟩

/-- The letters a subdivision puts in place of one letter: `a ↦ ae`, `a⁻¹ ↦ e⁻¹a⁻¹`, and
`x ↦ x` for the other letters. -/
def subLetter (a e : α) (x : Letter α) : Word α :=
  if x.sym = a then (if x.dir then [x, ⟨e, true⟩] else [⟨e, false⟩, x]) else [x]

/-- Unfolding: subdividing applies `subLetter` to every letter. -/
theorem subdivide_eq (a e : α) (P : Presentation α) :
    subdivide a e P = P.map fun w => w.flatMap (subLetter a e) := rfl

/-- A subdivided letter is never the empty word. -/
theorem subLetter_ne_nil (a e : α) (x : Letter α) : subLetter a e x ≠ [] := by
  unfold subLetter; split_ifs <;> simp

/-- How subdividing renames the edge ends: the head of the old `a` is now the head of `e`,
`(a, true) ↦ (e, true)`; every other end keeps its name. -/
def rho (a e : α) (x : α × Bool) : α × Bool := if x = (a, true) then (e, true) else x

/-- The last letter of a subdivided `u` arrives at the end of `u` renamed by `rho`: for `a` it is
`e`, arriving at `(e, true)`. -/
theorem subLetter_last {a e : α} {u u' : Letter α} (h : (subLetter a e u).getLast? = some u') :
    u'.fin = rho a e u.fin := by
  unfold subLetter at h
  rcases u with ⟨b, d⟩
  by_cases hb : b = a <;> cases d <;> simp_all [rho, Letter.fin] <;> subst h <;> simp_all

/-- The first letter of a subdivided `v` leaves from the end of `v` renamed by `rho`: for `a⁻¹`
it is `e⁻¹`, leaving from `(e, true)`. -/
theorem subLetter_head {a e : α} {v v' : Letter α} (h : (subLetter a e v).head? = some v') :
    v'.ini = rho a e v.ini := by
  unfold subLetter at h
  rcases v with ⟨b, d⟩
  by_cases hb : b = a <;> cases d <;> simp_all [rho, Letter.ini] <;> subst h <;> simp_all

/-- The corner in the middle of a subdivided letter (`ae` or `e⁻¹a⁻¹`) glues `(a, true)` and
`(e, false)`. -/
theorem subLetter_lin {a e : α} {x : Letter α} {p : Letter α × Letter α}
    (h : p ∈ lin (subLetter a e x)) :
    (p.1.fin = (a, true) ∧ p.2.ini = (e, false)) ∨ (p.1.fin = (e, false) ∧ p.2.ini = (a, true)) := by
  unfold subLetter at h
  rcases x with ⟨b, d⟩
  by_cases hb : b = a <;> cases d <;> simp_all [lin, Letter.fin, Letter.ini]


/-- A letter of a subdivided `x` has the symbol of `x`, or is `e`, if `x` has the symbol `a`. -/
theorem mem_subLetter_sym {a e : α} {x y : Letter α} (h : y ∈ subLetter a e x) :
    y.sym = x.sym ∨ (y.sym = e ∧ x.sym = a) := by
  unfold subLetter at h
  split_ifs at h <;> simp at h <;> rcases h with rfl | rfl <;> simp_all

/-- The symbols after subdividing `a` (a symbol of `P`): those of `P`, and `e`. -/
theorem mem_syms_subdivide {a e : α} {P : Presentation α} (ha : a ∈ syms P) {b : α} :
    b ∈ syms (subdivide a e P) ↔ b = e ∨ b ∈ syms P := by
  rw [subdivide_eq, mem_syms, mem_syms]
  constructor
  · rintro ⟨_, hw', y, hy, rfl⟩
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hw'
    obtain ⟨x, hx, hyx⟩ := List.mem_flatMap.1 hy
    rcases mem_subLetter_sym hyx with h | ⟨h, -⟩
    · exact Or.inr ⟨w, hw, x, hx, h.symm⟩
    · exact Or.inl h
  · obtain ⟨w₀, hw₀, x₀, hx₀, hxa⟩ := mem_syms.1 ha
    rintro (rfl | ⟨w, hw, x, hx, rfl⟩)
    · refine ⟨_, List.mem_map_of_mem hw₀, ⟨b, x₀.dir⟩, List.mem_flatMap.2 ⟨x₀, hx₀, ?_⟩, rfl⟩
      unfold subLetter; rcases x₀ with ⟨c, d⟩; cases d <;> simp_all
    · refine ⟨_, List.mem_map_of_mem hw, x, List.mem_flatMap.2 ⟨x, hx, ?_⟩, rfl⟩
      unfold subLetter; split_ifs <;> simp

/-- Subdividing adds one symbol, the new `e` (`prop:chi-invariant`). -/
theorem numE_subdivide (a e : α) (P : Presentation α) (ha : a ∈ syms P) (he : e ∉ syms P) :
    numE (subdivide a e P) = numE P + 1 := by
  unfold numE
  rw [← Finset.card_insert_of_notMem he]
  congr 1
  ext b
  rw [mem_syms_subdivide ha, Finset.mem_insert]

/-- Subdividing adds one vertex class (`prop:chi-invariant`): the new vertex in the middle of
`a`, where the head `(a, true)` of the new, shorter `a` meets the tail `(e, false)` of `e`.

Picture: the old vertices are still there, with the end `(a, true)` renamed `(e, true)`
(`rho`); the corners are the old ones, so they glue the renamed ends as before; and the new
corners, in the middle of each edge `a`, glue `(a, true)` to `(e, false)` and nothing else. So
`{(a, true), (e, false)}` is one new class (`C`), and the other classes are the old ones. -/
theorem numV_subdivide (a e : α) (P : Presentation α) (ha : a ∈ syms P) (he : e ∉ syms P) :
    numV (subdivide a e P) = numV P + 1 := by
  -- `Pn` is the subdivided presentation; `e ≠ a` since `a` is a symbol and `e` is not.
  set Pn := subdivide a e P with hPn
  have hea : e ≠ a := fun h => he (h ▸ ha)
  have hσ := subLetter_ne_nil a e
  have hrho : ∀ x : α × Bool, x ≠ (a, true) → rho a e x = x := fun x hx => by simp [rho, hx]
  have hrhoa : rho a e (a, true) = (e, true) := by simp [rho]
  -- Old corners give new ones: a corner `(u, v)` of `P` becomes the corner (last letter of the
  -- subdivided `u`, first letter of the subdivided `v`), which glues the renamed ends.
  have hA : ∀ x' y', Adj P x' y' → Adj Pn (rho a e x') (rho a e y') := by
    intro x' y' h
    obtain ⟨w, hw, u, v, huv, rfl, rfl⟩ := adj_iff.1 h
    obtain ⟨u', hu'⟩ : ∃ u', (subLetter a e u).getLast? = some u' := by
      cases h : (subLetter a e u).getLast? with
      | none => exact absurd (List.getLast?_eq_none_iff.1 h) (hσ u)
      | some u' => exact ⟨u', rfl⟩
    obtain ⟨v', hv'⟩ : ∃ v', (subLetter a e v).head? = some v' := by
      cases h : (subLetter a e v).head? with
      | none => exact absurd (List.head?_eq_none_iff.1 h) (hσ v)
      | some v' => exact ⟨v', rfl⟩
    refine adj_iff.2 ⟨_, List.mem_map_of_mem hw, u', v', ?_, subLetter_last hu',
      subLetter_head hv'⟩
    exact (mem_cyc_flatMap hσ).2 (Or.inr ⟨u, v, huv, hu', hv'⟩)
  -- New corners are old ones, with the ends renamed, or in the middle of a subdivided `a`,
  -- where they glue `(a, true)` to `(e, false)`.
  have hB : ∀ x y, Adj Pn x y → ((x = (a, true) ∧ y = (e, false)) ∨ (x = (e, false) ∧ y = (a, true)))
      ∨ ∃ x' y', Adj P x' y' ∧ x' ∈ ends P ∧ y' ∈ ends P ∧ x = rho a e x' ∧ y = rho a e y' := by
    intro x y h
    obtain ⟨_, hw', u', v', huv', rfl, rfl⟩ := adj_iff.1 h
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hw'
    rcases (mem_cyc_flatMap hσ).1 huv' with ⟨z, _, hz⟩ | ⟨u, v, huv, hu', hv'⟩
    · exact Or.inl (subLetter_lin hz)
    · refine Or.inr ⟨u.fin, v.ini, adj_of_cyc hw huv, ?_, ?_, subLetter_last hu',
        subLetter_head hv'⟩
      · exact mem_ends.2 (mem_syms.2 ⟨w, hw, u, (mem_of_mem_cyc huv).1, rfl⟩)
      · exact mem_ends.2 (mem_syms.2 ⟨w, hw, v, (mem_of_mem_cyc huv).2, rfl⟩)
  -- No renamed old end is `(a, true)` or `(e, false)`: these two are new.
  have hC : ∀ y ∈ ends P, rho a e y ≠ (a, true) ∧ rho a e y ≠ (e, false) := by
    intro y hy
    have hye : y.1 ≠ e := fun h => he (h ▸ hy)
    by_cases hya : y = (a, true)
    · subst hya; rw [hrhoa]; simp [hea]
    · rw [hrho y hya]
      exact ⟨hya, fun h => hye (by rw [h])⟩
  -- So the set `C = {(a, true), (e, false)}` is a union of classes (`iso`): a chain that starts
  -- in `C` stays in `C`.
  let C : Set (α × Bool) := {(a, true), (e, false)}
  have iso : ∀ x y, EqvGen (Adj Pn) x y → (x ∈ C ↔ y ∈ C) := by
    intro x y h
    induction h with
    | rel x y h =>
      rcases hB x y h with (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) | ⟨x', y', -, hx', hy', rfl, rfl⟩
      · simp [C]
      · simp [C]
      · simp only [C, Set.mem_insert_iff, Set.mem_singleton_iff]
        exact iff_of_false (by simpa using hC x' hx') (by simpa using hC y' hy')
    | refl => exact Iff.rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  -- And `(a, true) ∼ (e, false)` does happen: `a` occurs (`ha`), and its subdivision has a
  -- corner in the middle.
  have hin : EqvGen (Adj Pn) (e, false) (a, true) := by
    obtain ⟨w, hw, x, hx, hxa⟩ := mem_syms.1 ha
    have hlin : ∃ p, p ∈ lin (subLetter a e x) := by
      unfold subLetter; rcases x with ⟨c, d⟩; simp only at hxa; subst hxa
      cases d <;> simp [lin]
    obtain ⟨p, hp⟩ := hlin
    have hadj : Adj Pn p.1.fin p.2.ini := adj_iff.2 ⟨_, List.mem_map_of_mem hw, p.1, p.2,
      (mem_cyc_flatMap hσ).2 (Or.inl ⟨x, hx, hp⟩), rfl, rfl⟩
    rcases subLetter_lin hp with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2] at hadj; exact EqvGen.symm _ _ (EqvGen.rel _ _ hadj)
    · rw [h1, h2] at hadj; exact EqvGen.rel _ _ hadj
  -- The new edge ends are those of `e` and the old ones.
  have hendsn : ∀ x, x ∈ ends Pn ↔ x.1 = e ∨ x.1 ∈ syms P := fun x => by
    rw [mem_ends, hPn, mem_syms_subdivide ha]
  -- Step 1. The classes after subdividing are the class of `(a, true)`, which is `C`, and the
  -- classes of the ends outside `C`; the first is not among the others (`hnot`). So
  -- `V(Pn) = 1 + (number of classes of the ends outside C)`.
  have hsplit : Quot.mk (Adj Pn) '' ends Pn =
      insert (Quot.mk (Adj Pn) (a, true)) (Quot.mk (Adj Pn) '' (ends Pn \ C)) := by
    ext q
    simp only [Set.mem_image, Set.mem_insert_iff, Set.mem_sdiff]
    constructor
    · rintro ⟨x, hx, rfl⟩
      by_cases hxC : x ∈ C
      · left
        simp only [C, Set.mem_insert_iff, Set.mem_singleton_iff] at hxC
        rcases hxC with rfl | rfl
        · rfl
        · exact Quot.eqvGen_sound hin
      · exact Or.inr ⟨x, ⟨hx, hxC⟩, rfl⟩
    · rintro (rfl | ⟨x, ⟨hx, -⟩, rfl⟩)
      · exact ⟨(a, true), (hendsn _).2 (Or.inr ha), rfl⟩
      · exact ⟨x, hx, rfl⟩
  have hnot : Quot.mk (Adj Pn) (a, true) ∉ Quot.mk (Adj Pn) '' (ends Pn \ C) := by
    rintro ⟨x, ⟨_, hx⟩, hxe⟩
    exact hx ((iso _ _ (Quot.eqvGen_exact hxe)).2 (by simp [C]))
  have hfinite : (Quot.mk (Adj Pn) '' (ends Pn \ C)).Finite :=
    ((ends_finite _).subset Set.sdiff_subset).image _
  unfold numV
  rw [hsplit, Set.ncard_insert_of_notMem hnot hfinite]
  congr 1
  -- Step 2. The ends outside `C` have as many classes as the old ends: compare by `f`, which
  -- sends the ends of `e` to `(a, true)` and keeps the others, and by `rho` back.
  let f : α × Bool → α × Bool := fun x => if x.1 = e then (a, true) else x
  have hfe : ∀ x : α × Bool, x.1 = e → f x = (a, true) := fun x hx => by simp [f, hx]
  have hfn : ∀ x : α × Bool, x.1 ≠ e → f x = x := fun x hx => by simp [f, hx]
  have hfrho : ∀ y ∈ ends P, f (rho a e y) = y := by
    intro y hy
    have hye : y.1 ≠ e := fun h => he (h ▸ hy)
    by_cases hya : y = (a, true)
    · subst hya; rw [hrhoa, hfe _ rfl]
    · rw [hrho y hya, hfn y hye]
  refine ncard_classes_eq f (rho a e) ?_ ?_ ?_ ?_ ?_ ?_
  -- (1) `f` sends each new identification to an old chain: a corner in the middle of `a` to a
  -- trivial one, and a renamed old corner to the old corner (`hfrho`: `f` undoes `rho`).
  · intro x y h
    rcases hB x y h with (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) | ⟨x', y', h', hx', hy', rfl, rfl⟩
    · rw [hfn (a, true) (Ne.symm hea), hfe (e, false) rfl]; exact EqvGen.refl _
    · rw [hfn (a, true) (Ne.symm hea), hfe (e, false) rfl]; exact EqvGen.refl _
    · rw [hfrho x' hx', hfrho y' hy']; exact EqvGen.rel _ _ h'
  -- (2) `rho` sends old identifications to new ones (`hA`).
  · intro x y h; exact EqvGen.rel _ _ (hA x y h)
  -- (3) `rho(f(x)) = x` for every new end outside `C`: the only one moved is `(e, true)`, sent
  -- to `(a, true)` and back.
  · rintro x ⟨hx, hxC⟩
    simp only [C, Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hxC
    by_cases hxe : x.1 = e
    · have : x = (e, true) := by
        rcases x with ⟨b, d⟩
        simp only at hxe; subst hxe
        cases d
        · exact absurd rfl hxC.2
        · rfl
      rw [hfe _ hxe, hrhoa, this]; exact EqvGen.refl _
    · rw [hfn _ hxe, hrho _ hxC.1]; exact EqvGen.refl _
  -- (4) `f(rho(y)) = y` for every old end.
  · intro y hy; rw [hfrho y hy]; exact EqvGen.refl _
  -- (5) `f` sends new ends outside `C` to old ends.
  · rintro x ⟨hx, hxC⟩
    by_cases hxe : x.1 = e
    · rw [hfe _ hxe]; exact ha
    · rw [hfn _ hxe]
      exact ((hendsn x).1 hx).resolve_left hxe
  -- (6) `rho` sends old ends to new ends outside `C` (`hC`).
  · intro y hy
    refine ⟨?_, ?_⟩
    · rw [hendsn]
      by_cases hya : y = (a, true)
      · subst hya; rw [hrhoa]; exact Or.inl rfl
      · rw [hrho y hya]; exact Or.inr hy
    · simp only [C, Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact hC y hy

/-- **`prop:chi-invariant`**: every move leaves `χ = V − E + F` unchanged. Mathlib: none.

Proof (the book's), move by move, from the counts above: relabelling, reflecting, rotating and
permuting change none of `V`, `E`, `F`; subdividing adds one to `V` and one to `E`; cutting adds
one to `E` and one to `F`; folding takes one from `V` and one from `E`. In each case `V − E + F`
is the same (`omega` does that arithmetic). -/
theorem chi_move {P Q : Presentation α} (h : Move P Q) : chi Q = chi P := by
  -- One case for each rule of `Move` (`cases h with`, one `|` per kind of move).
  cases h with
  | rename π P =>
    simp only [chi, numV_relabel, numE_relabel]; simp [numF, relabel]
  | flip a P => simp only [chi, numV_flip, numE_flip]; simp [numF, flipSym]
  | subdivide a e P ha he =>
    simp only [chi, numV_subdivide a e P ha he, numE_subdivide a e P ha he]
    simp only [numF, subdivide, List.length_map]
    omega
  | reflect w Q => simp only [chi, numV_reflect, numE_reflect, numF, List.length_cons]
  | rotate x w Q => simp only [chi, numV_rotate, numE_rotate, numF, List.length_cons]
  | cut W₁ W₂ e Q h₁ h₂ he =>
    simp only [chi, numV_cut W₁ W₂ e Q h₁ h₂ he, numE_cut W₁ W₂ e Q he, numF, List.length_cons]
    omega
  | fold W₁ e Q h he =>
    -- Either case of the folding condition gives `W₁` of length at least `2`.
    have h₁ : 2 ≤ W₁.length := by omega
    simp only [chi, numV_fold W₁ e Q h₁ he, numE_fold W₁ e Q he, numF, List.length_cons]
    omega
  | permute P Q h => simp only [chi, numV_perm h, numE_perm h, numF, h.length_eq]

/-- **`prop:chi-invariant`** for chains: equivalent presentations have the same `χ`. Each step
is a move or a move read backwards (consolidating, pasting, unfolding), and keeps `χ` by
`chi_move`; so does the chain. -/
theorem chi_equiv {P Q : Presentation α} (h : Equiv P Q) : chi P = chi Q := by
  -- Induction on the length of the chain: a chain of no steps, or a chain `P ~ S` (by
  -- induction `χ(P) = χ(S)`, `ih`) followed by one step `S — T` in either direction (`hst`).
  induction h with
  | refl => rfl
  | tail _ hst ih => exact ih.trans (hst.elim (fun h => (chi_move h).symm) chi_move)

/-! ### The standard presentations (`prop:chi-standard`)

The book's proof: `aa⁻¹` has two vertex classes, one symbol and one word. In the standard words
of `#_g T²` and `#_k RP²` the corners of each block identify all its edge ends, and the corner
between two consecutive blocks joins them; so there is one vertex class, and `χ = 1 − E + 1`.
Below, `a₊` and `a₋` are the head `(a, true)` and the tail `(a, false)` of `a`. -/

/-- If `l = s u v t`, then `(u, v)` is a consecutive pair of `l`. -/
theorem mem_lin_of_eq {l s t : List β} {u v : β} (h : l = s ++ u :: v :: t) : (u, v) ∈ lin l := by
  subst h
  rw [mem_lin_append, mem_lin_cons]
  simp

/-- If a word `W = s u v t` of `P` has the letters `u`, `v` next to each other, their corner
identifies `u.fin ∼ v.ini`. -/
theorem adj_of_split {P : Presentation α} {W s t : Word α} {u v : Letter α} (hW : W ∈ P)
    (h : W = s ++ u :: v :: t) : Adj P u.fin v.ini :=
  adj_of_cyc hW (mem_cyc.2 (Or.inl (mem_lin_of_eq h)))

/-- If all the edge ends are identified with one of them, there is one vertex class. -/
theorem numV_eq_one {P : Presentation α} {x₀ : α × Bool} (h₀ : x₀ ∈ ends P)
    (h : ∀ x ∈ ends P, EqvGen (Adj P) x x₀) : numV P = 1 := by
  unfold numV
  rw [show Quot.mk (Adj P) '' ends P = {Quot.mk (Adj P) x₀} by
    ext q
    simp only [Set.mem_image, Set.mem_singleton_iff]
    constructor
    · rintro ⟨x, hx, rfl⟩; exact Quot.eqvGen_sound (h x hx)
    · rintro rfl; exact ⟨x₀, h₀, rfl⟩]
  exact Set.ncard_singleton _

/-- The sphere `aa⁻¹` has the one symbol `a = 0`. -/
theorem syms_sphere : syms sphere = {0} := by
  ext b; simp [sphere, eq_comm]

/-- **`prop:chi-standard`** for the sphere: `χ(aa⁻¹) = 2 − 1 + 1 = 2`; its two vertices stay
apart. -/
theorem chi_sphere : chi sphere = 2 := by
  -- `V = 2`. The two corners of `aa⁻¹` are `(a, a⁻¹)`, which glues `a₊` to itself, and
  -- `(a⁻¹, a)`, which glues `a₋` to itself (`hadj`: every identification is trivial). So no
  -- chain joins `a₊` to `a₋` (`key`), and the two ends `a₊`, `a₋` give two classes.
  have hV : numV sphere = 2 := by
    have hadj : ∀ x y, Adj sphere x y → x = y := by
      intro x y h
      simp only [Adj, edges, sphere, List.flatMap_cons, List.flatMap_nil, List.append_nil, cyc,
        List.cons_append, List.nil_append, lin, List.map_cons, List.map_nil, List.mem_cons,
        Prod.mk.injEq, List.not_mem_nil, or_false, Letter.fin, Letter.ini] at h
      rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl
    have hends : ends sphere = {((0 : ℕ), true), (0, false)} := by
      ext ⟨b, d⟩
      simp only [mem_ends, syms_sphere, Finset.mem_singleton, Set.mem_insert_iff,
        Set.mem_singleton_iff, Prod.mk.injEq]
      cases d <;> simp
    have key : ∀ x y, EqvGen (Adj sphere) x y → x = y := by
      intro x y h
      induction h with
      | rel x y h => exact hadj x y h
      | refl => rfl
      | symm _ _ _ ih => exact ih.symm
      | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂
    unfold numV
    rw [Set.InjOn.ncard_image, hends, Set.ncard_pair (by simp)]
    intro x _ y _ hxy
    exact key x y (Quot.eqvGen_exact hxy)
  -- `E = 1` (the symbol `a = 0`), `F = 1`.
  simp only [chi, hV, numE, syms_sphere, Finset.card_singleton, numF]
  simp [sphere]

/-- The word of `#_{n+m} T²` begins with the word of `#_n T²`: it is `torusWord n` followed by
some word `R`. -/
theorem torusWord_add (n m : ℕ) : ∃ R, torusWord (n + m) = torusWord n ++ R := by
  induction m with
  | zero => exact ⟨[], by simp⟩
  | succ m ih =>
    obtain ⟨R, hR⟩ := ih
    exact ⟨R ++ handle (n + m), by rw [← Nat.add_assoc, torusWord, hR, List.append_assoc]⟩

/-- The letters of `torusWord g` are those of its blocks `handle i`, `i < g`. -/
theorem mem_torusWord {g : ℕ} {x : Letter ℕ} : x ∈ torusWord g ↔ ∃ i < g, x ∈ handle i := by
  induction g with
  | zero => simp [torusWord]
  | succ g ih =>
    rw [torusWord, List.mem_append, ih]
    constructor
    · rintro (⟨i, hi, hx⟩ | hx)
      · exact ⟨i, by omega, hx⟩
      · exact ⟨g, by omega, hx⟩
    · rintro ⟨i, hi, hx⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
      · exact Or.inl ⟨i, hi, hx⟩
      · exact Or.inr hx

/-- The symbols of `torusWord g` are `0, 1, …, 2g − 1`. -/
theorem mem_syms_torus {g b : ℕ} : b ∈ syms [torusWord g] ↔ b < 2 * g := by
  rw [mem_syms]
  simp only [List.mem_singleton, exists_eq_left]
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨i, hi, hx⟩ := mem_torusWord.1 hx
    simp only [handle, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> simp <;> omega
  · intro hb
    rcases Nat.even_or_odd' b with ⟨j, rfl | rfl⟩
    · exact ⟨⟨2 * j, true⟩, mem_torusWord.2 ⟨j, by omega, by simp [handle]⟩, rfl⟩
    · exact ⟨⟨2 * j + 1, true⟩, mem_torusWord.2 ⟨j, by omega, by simp [handle]⟩, rfl⟩

/-- **`prop:chi-standard`** for `#_g T²`, `g ≥ 1`: `χ = 1 − 2g + 1 = 2 − 2g`; all the vertices
are one. (For `g = 0` the word is empty, not a presentation.) -/
theorem chi_torus {g : ℕ} (hg : 1 ≤ g) : chi [torusWord g] = 2 - 2 * g := by
  -- `E = 2g`: the symbols are `0, 1, …, 2g − 1` (`mem_syms_torus`).
  have hE : numE [torusWord g] = 2 * g := by
    unfold numE
    rw [show syms [torusWord g] = Finset.range (2 * g) by
      ext b; rw [mem_syms_torus, Finset.mem_range]]
    simp
  -- `V = 1`: every edge end is identified with `a₁₋`, which is `(0, false)`.
  have hV : numV [torusWord g] = 1 := by
    set P := [torusWord g]
    have hW : torusWord g ∈ P := List.mem_singleton_self _
    -- Within the block `aba⁻¹b⁻¹` (`a = 2i`, `b = 2i + 1`) all four ends are identified with
    -- `a₋`: its corners `(a, b)`, `(b, a⁻¹)`, `(a⁻¹, b⁻¹)` give `a₊ ∼ b₋` (`e₁`), `b₊ ∼ a₊`
    -- (`e₂`), `a₋ ∼ b₊` (`e₃`), so `a₋ ∼ b₊ ∼ a₊ ∼ b₋`. (`torusWord_add` writes the word as
    -- the blocks before, this block, and the rest `R`, to locate the corners.)
    have hhandle : ∀ i < g, ∀ d : Bool, EqvGen (Adj P) (2 * i, d) (2 * i, false) ∧
        EqvGen (Adj P) (2 * i + 1, d) (2 * i, false) := by
      intro i hi
      obtain ⟨R, hR⟩ := torusWord_add (i + 1) (g - (i + 1))
      rw [show i + 1 + (g - (i + 1)) = g by omega, torusWord] at hR
      have e₁ : Adj P (2 * i, true) (2 * i + 1, false) := adj_of_split (u := ⟨2 * i, true⟩)
        (v := ⟨2 * i + 1, true⟩) hW (s := torusWord i)
        (t := [⟨2 * i, false⟩, ⟨2 * i + 1, false⟩] ++ R)
        (by rw [hR]; simp [handle])
      have e₂ : Adj P (2 * i + 1, true) (2 * i, true) := adj_of_split (u := ⟨2 * i + 1, true⟩)
        (v := ⟨2 * i, false⟩) hW (s := torusWord i ++ [⟨2 * i, true⟩])
        (t := [⟨2 * i + 1, false⟩] ++ R) (by rw [hR]; simp [handle])
      have e₃ : Adj P (2 * i, false) (2 * i + 1, true) := adj_of_split (u := ⟨2 * i, false⟩)
        (v := ⟨2 * i + 1, false⟩) hW (s := torusWord i ++ [⟨2 * i, true⟩, ⟨2 * i + 1, true⟩])
        (t := R) (by rw [hR]; simp [handle])
      have r₁ := EqvGen.rel _ _ e₁
      have r₂ := EqvGen.rel _ _ e₂
      have r₃ := EqvGen.rel _ _ e₃
      intro d
      cases d
      · exact ⟨EqvGen.refl _, EqvGen.trans _ _ _ (EqvGen.symm _ _ r₁)
          (EqvGen.trans _ _ _ (EqvGen.symm _ _ r₂) (EqvGen.trans _ _ _ r₂ (EqvGen.trans _ _ _
            (EqvGen.symm _ _ r₂) (EqvGen.symm _ _ r₃))))⟩
      · exact ⟨EqvGen.trans _ _ _ (EqvGen.symm _ _ r₂) (EqvGen.symm _ _ r₃),
          EqvGen.symm _ _ r₃⟩
    -- Consecutive blocks are joined at the corner `(bᵢ⁻¹, aᵢ₊₁)` between them, which glues
    -- `bᵢ₋ ∼ aᵢ₊₁₋`; so by induction on `i`, every `aᵢ₋` is identified with `a₁₋ = (0, false)`.
    have hchain : ∀ i < g, EqvGen (Adj P) (2 * i, false) (0, false) := by
      intro i hi
      induction i with
      | zero => exact EqvGen.refl _
      | succ i ih =>
        obtain ⟨R, hR⟩ := torusWord_add (i + 2) (g - (i + 2))
        rw [show i + 2 + (g - (i + 2)) = g by omega, torusWord, torusWord] at hR
        have e : Adj P (2 * i + 1, false) (2 * (i + 1), false) := adj_of_split
          (u := ⟨2 * i + 1, false⟩) (v := ⟨2 * (i + 1), true⟩) hW
          (s := torusWord i ++ [⟨2 * i, true⟩, ⟨2 * i + 1, true⟩, ⟨2 * i, false⟩])
          (t := [⟨2 * (i + 1) + 1, true⟩, ⟨2 * (i + 1), false⟩, ⟨2 * (i + 1) + 1, false⟩] ++ R)
          (by rw [hR]; simp [handle])
        exact EqvGen.trans _ _ _ (EqvGen.symm _ _ (EqvGen.rel _ _ e))
          (EqvGen.trans _ _ _ ((hhandle i (by omega) false).2) (ih (by omega)))
    -- Every end is that of a symbol `b < 2g`, which is `2i` or `2i + 1`, the `a` or `b` of the
    -- block `i`: identified with `(2i, false)`, and so with `(0, false)`.
    refine numV_eq_one (x₀ := (0, false)) (by rw [mem_ends, mem_syms_torus]; omega) ?_
    rintro ⟨b, d⟩ hb
    rw [mem_ends, mem_syms_torus] at hb
    rcases Nat.even_or_odd' b with ⟨i, rfl | rfl⟩
    · exact EqvGen.trans _ _ _ (hhandle i (by omega) d).1 (hchain i (by omega))
    · exact EqvGen.trans _ _ _ (hhandle i (by omega) d).2 (hchain i (by omega))
  -- `χ = 1 − 2g + 1`, computed in `ℤ` (`push_cast` moves the conversion `ℕ → ℤ` inside).
  simp only [chi, hV, hE, numF, List.length_singleton]
  push_cast
  omega

/-- `crossWord (n + m)` is `crossWord n` followed by some word `R`. -/
theorem crossWord_add (n m : ℕ) : ∃ R, crossWord (n + m) = crossWord n ++ R := by
  induction m with
  | zero => exact ⟨[], by simp⟩
  | succ m ih =>
    obtain ⟨R, hR⟩ := ih
    exact ⟨R ++ crosscap (n + m), by rw [← Nat.add_assoc, crossWord, hR, List.append_assoc]⟩

/-- The letters of `crossWord k` are those of its blocks `crosscap i`, `i < k`. -/
theorem mem_crossWord {k : ℕ} {x : Letter ℕ} : x ∈ crossWord k ↔ ∃ i < k, x ∈ crosscap i := by
  induction k with
  | zero => simp [crossWord]
  | succ k ih =>
    rw [crossWord, List.mem_append, ih]
    constructor
    · rintro (⟨i, hi, hx⟩ | hx)
      · exact ⟨i, by omega, hx⟩
      · exact ⟨k, by omega, hx⟩
    · rintro ⟨i, hi, hx⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
      · exact Or.inl ⟨i, hi, hx⟩
      · exact Or.inr hx

/-- The symbols of `crossWord k` are `0, 1, …, k − 1`. -/
theorem mem_syms_cross {k b : ℕ} : b ∈ syms [crossWord k] ↔ b < k := by
  rw [mem_syms]
  simp only [List.mem_singleton, exists_eq_left]
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨i, hi, hx⟩ := mem_crossWord.1 hx
    simp only [crosscap, List.mem_cons, List.not_mem_nil, or_false, or_self] at hx
    subst hx; exact hi
  · intro hb
    exact ⟨⟨b, true⟩, mem_crossWord.2 ⟨b, hb, by simp [crosscap]⟩, rfl⟩

/-- **`prop:chi-standard`** for `#_k RP²`, `k ≥ 1`: `χ = 1 − k + 1 = 2 − k`; all the vertices
are one. -/
theorem chi_cross {k : ℕ} (hk : 1 ≤ k) : chi [crossWord k] = 2 - k := by
  -- `E = k`: the symbols are `0, 1, …, k − 1` (`mem_syms_cross`).
  have hE : numE [crossWord k] = k := by
    unfold numE
    rw [show syms [crossWord k] = Finset.range k by ext b; rw [mem_syms_cross, Finset.mem_range]]
    simp
  -- `V = 1`: every edge end is identified with `a₁₋`, which is `(0, false)`.
  have hV : numV [crossWord k] = 1 := by
    set P := [crossWord k]
    have hW : crossWord k ∈ P := List.mem_singleton_self _
    -- The corner in the middle of the block `aa` (`a = i`) glues `a₊ ∼ a₋`: the head of the
    -- first `a` to the tail of the second.
    have hblock : ∀ i < k, EqvGen (Adj P) (i, true) (i, false) := by
      intro i hi
      obtain ⟨R, hR⟩ := crossWord_add (i + 1) (k - (i + 1))
      rw [show i + 1 + (k - (i + 1)) = k by omega, crossWord] at hR
      exact EqvGen.rel _ _ (adj_of_split (u := ⟨i, true⟩) (v := ⟨i, true⟩) hW
        (s := crossWord i) (t := R) (by rw [hR]; simp [crosscap]))
    -- Consecutive blocks are joined at the corner `(aᵢ, aᵢ₊₁)` between them, which glues
    -- `aᵢ₊ ∼ aᵢ₊₁₋`; so by induction on `i`, every `aᵢ₋` is identified with `(0, false)`.
    have hchain : ∀ i < k, EqvGen (Adj P) (i, false) (0, false) := by
      intro i hi
      induction i with
      | zero => exact EqvGen.refl _
      | succ i ih =>
        obtain ⟨R, hR⟩ := crossWord_add (i + 2) (k - (i + 2))
        rw [show i + 2 + (k - (i + 2)) = k by omega, crossWord, crossWord] at hR
        have e : Adj P (i, true) (i + 1, false) := adj_of_split (u := ⟨i, true⟩)
          (v := ⟨i + 1, true⟩) hW (s := crossWord i ++ [⟨i, true⟩]) (t := [⟨i + 1, true⟩] ++ R)
          (by rw [hR]; simp [crosscap])
        exact EqvGen.trans _ _ _ (EqvGen.symm _ _ (EqvGen.rel _ _ e))
          (EqvGen.trans _ _ _ (hblock i (by omega)) (ih (by omega)))
    -- Every end is `aᵢ₋` or `aᵢ₊ ∼ aᵢ₋` for some `i < k`.
    refine numV_eq_one (x₀ := (0, false)) (by rw [mem_ends, mem_syms_cross]; omega) ?_
    rintro ⟨b, d⟩ hb
    rw [mem_ends, mem_syms_cross] at hb
    cases d
    · exact hchain b hb
    · exact EqvGen.trans _ _ _ (hblock b hb) (hchain b hb)
  -- `χ = 1 − k + 1`, computed in `ℤ`.
  simp only [chi, hV, hE, numF, List.length_singleton]
  push_cast
  omega

end Chi

end Surface


/-! ## Attaching a cell (`def:attach-cell`, `prop:attach-injects`)

The book attaches `Dⁿ` along `φ : Sⁿ⁻¹ → X`. The argument uses only that `Sⁿ⁻¹` is closed in
`Dⁿ`, so it is stated here for any adjunction space `X ∪_φ Y` (`def:adjunction`) with `B ⊆ Y`
closed and `φ : B → X` continuous; `Y ∖ B` plays the part of the open disc.

The book's proof turns on one observation: the only identifications are `b ∼ φ(b)` for `b ∈ B`.
So each point of `X ⊔ Y` has a representative, `attachRep`: itself, or `φ(b)` for `b ∈ B`; and
two points are identified exactly when their representatives agree (`attach_rel_iff`). Then a
subset of `X ∪_φ Y` is open (closed) exactly when its preimages in `X` and in `Y` are
(`def:quotient`, `prop:coproduct-top`), and these preimages are read off the representatives.

Lean: `X ⊕ Y` is the disjoint union `X ⊔ Y`; its points are `Sum.inl x` for `x ∈ X` and
`Sum.inr y` for `y ∈ Y`. `Pushout.inl x` and `Pushout.inr y` are their classes in `X ∪_φ Y`. -/

section Attach

open Set

universe uX uY

variable {X : Type uX} {Y : Type uY} [TopSpace X] [TopSpace Y] {B : Set Y} (φ : B → X)

-- (`open Classical in`: the definition below asks "is `y ∈ B`?", which Lean answers only by
-- allowing the law of excluded middle.)
open Classical in
/-- The representative of a point of `X ⊔ Y` that the gluing picks: a point of `B` goes to its
image in `X`, every other point stays. (`if h : y ∈ B then … else …` names the proof `h` that
`y ∈ B`, to form the point `⟨y, h⟩` of `B`.) -/
noncomputable def attachRep : X ⊕ Y → X ⊕ Y
  | Sum.inl x => Sum.inl x
  | Sum.inr y => if h : y ∈ B then Sum.inl (φ ⟨y, h⟩) else Sum.inr y

/-- Unfolding: the representative of `b ∈ B` is `φ(b)`. -/
theorem attachRep_inr_of_mem {y : Y} (h : y ∈ B) : attachRep φ (Sum.inr y) = Sum.inl (φ ⟨y, h⟩) := by
  simp [attachRep, h]

/-- Unfolding: a point of `Y ∖ B` is its own representative. -/
theorem attachRep_inr_of_notMem {y : Y} (h : y ∉ B) : attachRep φ (Sum.inr y) = Sum.inr y := by
  simp [attachRep, h]

/-- Two points of `X ⊔ Y` are identified in `X ∪_φ Y` exactly when they have the same
representative: the only identifications are `b ∼ φ(b)`. -/
theorem attach_rel_iff {s t : X ⊕ Y} :
    (pushoutSetoid φ (Subtype.val : B → Y)).r s t ↔ attachRep φ s = attachRep φ t := by
  -- `⇒`: identified points have equal representatives. Induction on the chain of
  -- identifications: one step `φ(b) ∼ b` (both have the representative `φ(b)`); no step; a chain
  -- read backwards; two chains one after the other.
  constructor
  · intro h
    induction h with
    | rel u v huv =>
      obtain ⟨b, rfl, rfl⟩ := huv
      simp [attachRep, b.2]
    | refl => rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  -- `⇐`: every point is identified with its representative (`hrep`: a point of `X` or of `Y ∖ B`
  -- is its own, and `b ∈ B` is identified with `φ(b)`); so points with equal representatives
  -- are identified, through the representative.
  · intro h
    have hrep : ∀ u : X ⊕ Y, Relation.EqvGen (pushoutRel φ (Subtype.val : B → Y)) u
        (attachRep φ u) := by
      rintro (x | y)
      · exact Relation.EqvGen.refl _
      · by_cases hy : y ∈ B
        · rw [attachRep_inr_of_mem φ hy]
          exact Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ ⟨⟨y, hy⟩, rfl, rfl⟩)
        · rw [attachRep_inr_of_notMem φ hy]; exact Relation.EqvGen.refl _
    exact Relation.EqvGen.trans _ _ _ (hrep s)
      (h ▸ Relation.EqvGen.symm _ _ (hrep t))

/-- The same, for the classes: `[s] = [t]` in `X ∪_φ Y` exactly when `s` and `t` have the same
representative. -/
theorem attach_mk_eq_iff {s t : X ⊕ Y} :
    (Quotient.mk _ s : AdjunctionSpace φ) = Quotient.mk _ t ↔ attachRep φ s = attachRep φ t :=
  Quotient.eq.trans (attach_rel_iff φ)

/-- `prop:attach-injects`: no two points of `X` are identified, so `X → X ∪_φ Y` is injective. -/
theorem attach_inl_injective : Function.Injective (Pushout.inl : X → AdjunctionSpace φ) := by
  -- Two points `x`, `x'` of `X` with the same image have representatives `x`, `x'`.
  intro x x' h
  have := (attach_mk_eq_iff φ).1 h
  simpa [attachRep] using this

/-- `prop:attach-injects`: points off `B` are identified with nothing, so `Y ∖ B → X ∪_φ Y` is
injective: two points `y`, `y'` off `B` with the same image have representatives `y`, `y'`,
which must be equal. (`InjOn f Bᶜ`: `f` is injective on the complement of `B`.) -/
theorem attach_inr_injOn : InjOn (Pushout.inr : Y → AdjunctionSpace φ) Bᶜ := by
  intro y hy y' hy' h
  have := (attach_mk_eq_iff φ).1 h
  rw [attachRep_inr_of_notMem φ hy, attachRep_inr_of_notMem φ hy'] at this
  exact Sum.inr_injective this

/-- `prop:attach-injects`: for `B` closed and `φ` continuous, `X → X ∪_φ Y` is a closed map: the
image of a closed `F` has preimage `F` in `X` and `φ⁻¹(F)` in `Y`, closed in `B` and so in `Y`.
With `attach_inl_injective` and `continuous_pushout_inl`, a closed embedding.
Mathlib: `Topology.IsClosedEmbedding` (for `TopCat` pushouts, none). -/
theorem attach_inl_isClosedMap (hB : IsClosed B) (hφ : Continuous φ) :
    IsClosedMap (Pushout.inl : X → AdjunctionSpace φ) := by
  -- Let `F ⊆ X` be closed; we show that its image is closed, that is, that the preimage in
  -- `X ⊔ Y` of its complement is open.
  intro F hF
  -- A point of `X ⊔ Y` maps into the image of `F` exactly when its representative is in `F`.
  have hpre : Quotient.mk _ ⁻¹' (Pushout.inl '' F : Set (AdjunctionSpace φ)) =
      {s | attachRep φ s ∈ Sum.inl '' F} := by
    ext s
    simp only [mem_preimage, mem_image, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨x, hx, hxs⟩
      exact ⟨x, hx, by rw [← (attach_mk_eq_iff φ).1 hxs]; rfl⟩
    · rintro ⟨x, hx, hxs⟩
      exact ⟨x, hx, (attach_mk_eq_iff φ).2 (by rw [← hxs]; rfl)⟩
  show IsOpen (Quotient.mk (pushoutSetoid φ (Subtype.val : B → Y)) ⁻¹'
    (Pushout.inl '' F : Set (AdjunctionSpace φ))ᶜ)
  rw [preimage_compl, hpre]
  -- A subset of `X ⊔ Y` is open when its parts in `X` and in `Y` are open (`prop:coproduct-top`).
  refine ⟨?_, ?_⟩
  -- In `X`: the points not mapping into the image of `F` are those of `Fᶜ`, open since `F` is
  -- closed. (No two points of `X` are identified.)
  · have : (Sum.inl : X → X ⊕ Y) ⁻¹' {s | attachRep φ s ∈ Sum.inl '' F}ᶜ = Fᶜ := by
      ext x; simp [attachRep]
    rw [this]
    exact hF
  -- In `Y`: the points mapping into the image of `F` are the `b ∈ B` with `φ(b) ∈ F`, the set
  -- `φ⁻¹(F)`; it is closed in `B` since `φ` is continuous, and so closed in `Y`, since `B` is
  -- closed (`IsClosed.image_val`). Its complement is open.
  · have : (Sum.inr : Y → X ⊕ Y) ⁻¹' {s : X ⊕ Y | attachRep φ s ∈ Sum.inl '' F} =
        Subtype.val '' (φ ⁻¹' F) := by
      ext y
      simp only [mem_preimage, Set.mem_ofPred_eq, mem_image]
      by_cases hy : y ∈ B
      · rw [attachRep_inr_of_mem φ hy]
        constructor
        · rintro ⟨x, hx, hxy⟩
          exact ⟨⟨y, hy⟩, by show φ ⟨y, hy⟩ ∈ F; rw [← Sum.inl_injective hxy]; exact hx, rfl⟩
        · rintro ⟨b, hb, rfl⟩
          exact ⟨_, hb, rfl⟩
      · rw [attachRep_inr_of_notMem φ hy]
        constructor
        · rintro ⟨x, -, hx⟩; exact absurd hx (by simp)
        · rintro ⟨b, -, rfl⟩; exact absurd b.2 hy
    have hc : IsClosed (Subtype.val '' (φ ⁻¹' F)) :=
      hB.image_val (continuous_iff_isClosed.1 hφ F hF)
    rw [preimage_compl, this]
    exact hc

/-- `prop:attach-injects`: a set `U` open in `Y` and disjoint from `B` stays open in `X ∪_φ Y`:
its preimages are `∅` in `X` and `U` in `Y`. So `Y ∖ B → X ∪_φ Y` is an open map onto an open
set, and with `attach_inr_injOn` a homeomorphism onto its image. Mathlib: none. -/
theorem attach_inr_isOpen_image {U : Set Y} (hU : IsOpen U) (hUB : U ⊆ Bᶜ) :
    IsOpen (Pushout.inr '' U : Set (AdjunctionSpace φ)) := by
  -- A point of `X ⊔ Y` maps into the image of `U` exactly when its representative is in `U`
  -- (the points of `U` are off `B`, so each is its own representative).
  have hpre : Quotient.mk _ ⁻¹' (Pushout.inr '' U : Set (AdjunctionSpace φ)) =
      {s | attachRep φ s ∈ Sum.inr '' U} := by
    ext s
    simp only [mem_preimage, mem_image, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨y, hy, hys⟩
      refine ⟨y, hy, ?_⟩
      rw [← (attach_mk_eq_iff φ).1 hys]
      exact (attachRep_inr_of_notMem φ (hUB hy)).symm
    · rintro ⟨y, hy, hys⟩
      refine ⟨y, hy, (attach_mk_eq_iff φ).2 ?_⟩
      rw [← hys]
      exact attachRep_inr_of_notMem φ (hUB hy)
  show IsOpen (Quotient.mk (pushoutSetoid φ (Subtype.val : B → Y)) ⁻¹'
    (Pushout.inr '' U : Set (AdjunctionSpace φ)))
  rw [hpre]
  -- The preimage is open in `X ⊔ Y` when its parts in `X` and in `Y` are open.
  refine ⟨?_, ?_⟩
  -- In `X`: empty, since a representative in `U ⊆ Y ∖ B` comes from `Y`.
  · have : (Sum.inl : X → X ⊕ Y) ⁻¹' {s : X ⊕ Y | attachRep φ s ∈ Sum.inr '' U} = ∅ := by
      ext x; simp [attachRep]
    rw [this]; exact isOpen_empty
  -- In `Y`: exactly `U`, open by hypothesis.
  · have : (Sum.inr : Y → X ⊕ Y) ⁻¹' {s : X ⊕ Y | attachRep φ s ∈ Sum.inr '' U} = U := by
      ext y
      simp only [mem_preimage, Set.mem_ofPred_eq, mem_image]
      by_cases hy : y ∈ B
      · rw [attachRep_inr_of_mem φ hy]
        exact iff_of_false (by simp) (fun h => hUB h hy)
      · rw [attachRep_inr_of_notMem φ hy]
        simp
    rw [this]; exact hU

end Attach

end Course
