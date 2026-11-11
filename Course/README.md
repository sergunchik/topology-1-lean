# Reading the course in Lean

These files prove the theorems of *Topology 1* in Lean, a language in which a computer checks
every step of a proof (the book's appendix "Types, and Lean" says what Lean and Mathlib are).
You do not need to install anything to read them: read them like a book, next to the book.
Each theorem names its label in the book (`thm:pi1-circle`), and the book's statement points
back to its Lean name.

| Week | Files |
|---|---|
| 1 | `Week01.lean` (spaces, bases, continuity, metrics), `Week01Examples.lean` |
| 2 | `Week02.lean` (ℝ, products, quotients), `Week02Glue.lean` (gluing, connectedness), `Week02Graphs.lean` |
| 3 | `Week03Hot.lean` (homotopy equivalence, contractible spaces) |
| 4 | `Week04.lean` (paths, the fundamental group), `Week04More.lean` (limits, the Hopf map) |
| 5 | `Week05.lean` (surface words, the Euler characteristic), `Week05Classification.lean` |
| 6 | `Week06.lean` (the circle, lifting, `π₁(S¹) ≅ ℤ`), `Week06Brouwer.lean`, `Week06Invariance.lean`, `Week06Circle.lean` |
| 7 | `Week07Degree.lean` (the degree, winding numbers, the fundamental theorem of algebra, Borsuk–Ulam for `n = 2`), `Week07Spheres.lean` (the generation lemma, `π₁(Sⁿ) = 1` for `n ≥ 2`, `ℝ² ≇ ℝⁿ`, `[Sᵏ, Sⁿ] = *` for `k < n`), `Week07Covering.lean` (covering maps and lifting, fibrations, the mapping cylinder, `πₙ` abelian) |
| 8 | `Week08FreeGroups.lean` (the free abelian group `F(S)^ab ≅ ℤ^S`, the rank of `ℤ^m` is well defined by the count mod 2, free groups on finite sets of different sizes are not isomorphic, a free group is abelian only on at most one generator, `⟨a ∣ aⁿ⟩ ≅ ℤ/n`, `⟨a, b ∣ aba⁻¹b⁻¹⟩ ≅ ℤ²`, `ab` of infinite order in `⟨a, b ∣ a², b²⟩`, the ping-pong sets of `[[1, 2], [0, 1]]` and `[[1, 0], [2, 1]]`) |
| 9 | `Week09Homology.lean` (boundaries are cycles, the map a chain map induces on homology, chain homotopic maps agree on homology, `∂∂ = 0` for ordered simplicial chains and for singular chains, `b₀` of a graph is its number of components, `b₁ = |E| - |V| + c`, the Euler number from the chain groups, the zigzag lemma, the cone formula `∂ (v · c) = c - v · ∂ c`, the full ordered complex is acyclic (so is the point), and `H₀ ≅ ℤ` through the augmentation, for ordered chains and, on a path-connected space, for singular chains; a graph's `H₀` over `ℤ` is free on its components) |
| 10 | `Week10SurfaceGroups.lean` (the abelianised group of the orientable surface of genus `g` is `ℤ^{2g}`, and that of the connected sum of `k + 1` projective planes is `ℤ^k ⊕ ℤ/2`, from their presentations) |
| 12 | `Week12Deck.lean` (a plan until the lecture: the automorphisms of a transitive right `G`-set with point stabiliser `H` are `N(H)/H`, the algebraic core of the deck group theorem) |
| 13 | `Week13MayerVietoris.lean` (a plan until the lecture: the short sequence of Mayer–Vietoris is exact) |

## A first example

From `Week01.lean`:

```lean
/-- A composite of continuous maps is continuous. -/
theorem Continuous.comp {g : Y → Z} {f : X → Y} (hg : Continuous g) (hf : Continuous f) :
    Continuous (g ∘ f) := fun V hV => hf _ (hg V hV)
```

Read it as: **Theorem.** Let `f : X → Y` and `g : Y → Z`. If `g` is continuous (call this fact
`hg`) and `f` is continuous (`hf`), then `g ∘ f` is continuous. *Proof.* Take an open `V ⊆ Z`
(`hV` says it is open). Then `g⁻¹(V)` is open by `hg`, so `f⁻¹(g⁻¹(V)) = (g ∘ f)⁻¹(V)` is open
by `hf`. ∎

The pieces:

- `theorem name (hypotheses) : statement := proof`. Everything before `:=` is the statement.
- `(hf : Continuous f)` is a hypothesis with a name, `hf`, so that the proof can use it. A proof
  of a statement is itself an object, and `hf : P` means "`hf` is a proof of `P`".
- `{f : X → Y}` in curly brackets: the reader does not have to say which `f`, Lean works it out
  from `hf`. `[TopSpace X]` in square brackets: "`X` carries a topology", found automatically.
- `Continuous f` is defined in `Week01.lean` as `∀ V : Set Y, IsOpen V → IsOpen (f ⁻¹' V)`.
  So a proof of it is a function: given `V` and a proof `hV` that `V` is open, it returns a proof
  that `f⁻¹(V)` is open. That is why the proof above is `fun V hV => …`.

## Notation

| Lean | Mathematics |
|---|---|
| `x : X` | `x ∈ X` (`X` is a type, roughly a set) |
| `Set X`, `U : Set X` | subsets of `X`; `U ⊆ X` |
| `f ⁻¹' V`, `f '' U` | preimage `f⁻¹(V)`, image `f(U)` |
| `Uᶜ`, `⋃₀ 𝒰`, `⋃ i, U i` | complement, union of a family |
| `fun x => e` | the map `x ↦ e` |
| `X × Y`, `(x, y)`, `q.1`, `q.2` | product, a pair, its coordinates |
| `{x // P x}`, `⟨x, hx⟩` | the subset `{x : P(x)}` as a space; a point `x` with the proof `hx` that it is in it |
| `(z : ℝ × ℝ)` for `z : S1` | `z` seen as a point of the plane (a *coercion*, often printed `↑z`) |
| `P → Q`, `P ↔ Q`, `¬P` | implies, iff, not |
| `∀ x, P x`, `∃ x, P x` | for all, there exists |
| `A ≃* B` | an isomorphism of groups |
| `Nonempty (Homotopy f g)` | "there is a homotopy from `f` to `g`" |
| `Quotient`, `Quot.mk _ x` | a quotient set; the class `[x]` |
| `I` | the interval `[0, 1]` |

## Proofs written with `by`

Most proofs are a sequence of *tactics* after `by`. Lean keeps a list of *goals*, what remains
to prove, and each tactic changes it. You never have to guess the goal: the comments say it.

| Tactic | What it does, in words |
|---|---|
| `intro x hx` | "Let `x` be such that `hx`." |
| `exact e` | "This is exactly `e`." |
| `apply foo` | "By `foo`, it suffices to show its hypotheses." |
| `have h : P := …` | "We first show `P`; call it `h`." |
| `obtain ⟨x, hx⟩ := h` | "By `h`, there is `x` with `hx`." |
| `refine ⟨x, ?_⟩`, `use x` | "Take `x`; it remains to check …" |
| `constructor` | prove both halves of an `↔` or an `∧` |
| `rcases h with h1 \| h2`, `by_cases h : P` | split into cases |
| `rw [h]` | replace the left side of the equation `h` by its right side |
| `show P` | "The goal is `P`." (only for the reader) |
| `calc a = b := … _ = c := …` | a chain of equalities or inequalities, one reason per step |
| `ext x` | two maps (or sets) are equal if they agree at every `x` |
| `simp`, `simpa` | routine simplification with known identities |
| `linarith`, `nlinarith`, `ring`, `positivity`, `norm_num` | routine algebra and inequalities with real numbers |
| `continuity`, `fun_prop` | routine continuity of formulas |
| `·` | starts the proof of one of several goals |
| `t1 <;> t2` | do `t2` after `t1` in every case it creates |
| `t1; t2` | `t1`, then `t2` (two steps on one line) |
| `rw [h] at h'` | rewrite inside the hypothesis `h'` instead of the goal |
| `rfl` | "both sides are the same by definition" |
| `h.mp`, `h.mpr` | the two directions `P → Q`, `Q → P` of `h : P ↔ Q` |
| `congrArg F h` | from `a = b`, get `F a = F b` |
| `Subtype.ext` | two points of a subspace are equal if they are equal as points of the space |
| `Quotient.ind`, `Quotient.sound` | to prove something for every class `[x]`, prove it for every `x`; related elements have equal classes |

More notation that comes up often:

| Lean | Mathematics |
|---|---|
| `def name … where field := …` | a definition of a structure (a path, a homotopy, …) field by field |
| `⟦f⟧` | the class `[f]` of `f` (for instance a homotopy class) |
| `G →* H`, `G ≃* H` | a homomorphism, an isomorphism of groups |
| `Multiplicative ℤ`, `ofAdd n` | `ℤ` written multiplicatively, so `n + m` is written `ofAdd n * ofAdd m` and `0` is `1` |
| `False` | a contradiction: a theorem whose conclusion is `False` says its hypotheses cannot all hold |
| `_root_.Continuous`, `_root_.IsOpen` | Mathlib's notions, as opposed to the course's `Continuous`, `IsOpen` (see the bridges below) |

Lines starting with `--`, and text between `/-` and `-/`, are comments for people; `/-- … -/`
before a declaration is its docstring.

## What comes from where

The course's notions (topological space, continuity, homotopy, the fundamental group, …) are
defined here from scratch, so that each proof is the book's proof. Facts from Analysis I
(arithmetic of real numbers, continuity of `sin`, `cos`, `√`, the intermediate value theorem,
compactness of `[0, 1]`) are taken from Mathlib, Lean's library of mathematics, through
*bridges*: theorems named `…_iff_mathlib` or `toMathlib` that show the course's notion is
Mathlib's. Each docstring also names Mathlib's version of the result, for comparison.
