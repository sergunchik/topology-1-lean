/-
Machine-generated (Claude, Aristotle), no line written by a person. Copyleft: GPL-3.0-or-later.

# Week 7: the degree of a map `S¹ → S¹`, and what it proves

This file proves what the degree of a map of the circle does (week 7 of the book, "Degree and
winding number", "What the circle proves"). For a continuous `φ : S¹ → S¹`, `deg φ` is the net
change `g(1) - g(0)` of a lift `g` of `s ↦ φ(e^{2πis})` (`def:degree-circle`); for a loop at `1`
it is week 6's `degLoop`. Homotopic maps have the same degree and maps of the same degree are
homotopic; `deg (z ↦ zⁿ) = n` and `deg (ψ ∘ φ) = deg ψ · deg φ`, so `deg : [S¹, S¹] → ℤ` is a
bijection; a map of non-zero degree is onto (`prop:degree`). The winding number
`w(γ, q) = deg (z ↦ (γ(z) - q)/|γ(z) - q|)` (`def:winding-number`) is unchanged by homotopies
avoiding `q`, constant as `q` moves along a path avoiding `γ`, locally constant in `q`, and `0` for
`q` far away (`prop:winding`). Then the payoffs: the fundamental theorem of algebra (`thm:fta`),
odd maps have odd degree (`lem:odd-degree`), and Borsuk–Ulam for `S²` (`thm:borsuk-ulam-2`).

Departures from the book:
* `z ↦ zⁿ` is the map `p(t) ↦ p(nt)`, obtained by passing `s ↦ p(ns)` on `I` to the circle
  (week 4's `descend`, `prop:loops-circle`); complex numbers appear only in `thm:fta`, where the
  plane is identified with `ℂ` by `(x, y) ↔ x + iy`.
* `prop:degree` (1), converse: the straight-line homotopy between two lifts `g_φ`, `g_ψ` with the
  same net change already closes up on the circle, so the book's preliminary rotation of `φ`, `ψ`
  to fix `1` is not needed.
* `prop:degree` (3): instead of factoring through `S¹ ∖ {w} ≅ ℝ`, the lift is used directly: it
  misses `a + ℤ` (where `p(a) = w`), so by the intermediate value theorem its net change is `0`.
* `prop:winding`: the winding number is shown constant along paths avoiding `γ(S¹)` and on
  path-connected sets missing `γ(S¹)`, and locally constant (for Mathlib's distance on `ℝ × ℝ`,
  the larger coordinate difference); "far away" is `|q| > |γ(z)|` for all `z`. A component is
  a path component (`JoinedOff`), as the book's proof uses it; "unbounded" is Mathlib's "not
  bounded". That there is exactly one unbounded component is the lecturer's argument, "`ℝ²` has
  one end": the outside of a large square is path-connected (Analysis I, from Mathlib's
  `isPathConnected_sphere`) and misses `γ(S¹)`.
* `thm:borsuk-ulam-2`: the null-homotopy of `g` on the equator is written out, shrinking the
  equator through the upper hemisphere, `(z, t) ↦ ((1 - t)z, √(1 - (1 - t)²))`: the straight-line
  contraction of the disc `D²`, lifted to the hemisphere.
* `thm:fta` is stated for Mathlib's `Polynomial ℂ`; Mathlib's own proof (`Complex.exists_root`)
  is not used.
* From Analysis I, through the bridges: the arithmetic and continuity of real and complex
  formulas, `√`, de Moivre's formula, the intermediate value theorem, the compactness of `S¹`,
  and the triangle inequality for complex numbers; each use says so. Mathlib's names below were
  checked against Lean and Mathlib v4.34.1, which has no degree of circle maps, winding number of
  continuous loops or Borsuk–Ulam theorem.

New to Lean? Read `Course/README.md` first.
-/
import Course.Week04More
import Course.Week06Brouwer
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Analysis.Normed.Module.Connected

-- Bookkeeping. `u v` are "universe levels", which you may ignore. `open Set Real` lets us write
-- `π`, `√`, `Icc` without prefixes, and `noncomputable section` says that some definitions use
-- real numbers, which Lean cannot compute.
universe u v

set_option warn.classDefReducibility false

namespace Course

open Set Real

noncomputable section

variable {X : Type u} {Y : Type v}

/-! ## The degree (`def:degree-circle`) -/

/-- The path `s ↦ φ(e^{2πis}) = φ(p(s))`, `s ∈ I`, of a map `φ : S¹ → S¹`: the loop whose lift
defines the degree (`def:degree-circle`). It is week 4's `φ ∘ q`, with `q = qI`. -/
def loopOf (φ : S1 → S1) (s : I) : S1 := φ (p s)

/-- If `φ` is continuous, so is `s ↦ φ(p(s))`, a composite of continuous maps. -/
theorem continuous_loopOf {φ : S1 → S1} (hφ : Continuous φ) : Continuous (loopOf φ) :=
  hφ.comp continuous_qI

/-- `p(1) = p(0)`, as points of `S¹`: both are `1` (`p_int`, `p_zero`). -/
theorem p_one_eq_p_zero : p ((1 : I) : ℝ) = p ((0 : I) : ℝ) := by
  simpa using p_int 1

/-- Two lifts `g, g'` of the same path `f : I → S¹` have the same net change:
`g'(1) - g'(0) = g(1) - g(0)`. `def:degree-circle` ("It does not depend on the lift"). -/
theorem lift_sub_eq {f : I → S1} {g g' : I → ℝ} (hg : IsLift f g) (hg' : IsLift f g') :
    g' 1 - g' 0 = g 1 - g 0 := by
  -- Step 1. `p(g(0)) = f(0) = p(g'(0))`, so `g'(0) - g(0)` is an integer `m` (`p_eq_iff`).
  -- (Lean: `show P by …` proves `P` on the spot; `hg.2` is "`p(g(s)) = f(s)` for all `s`".)
  obtain ⟨m, hm⟩ := p_eq_iff.mp (show p (g 0) = p (g' 0) by rw [hg.2, hg'.2])
  -- Step 2. `g + m` is a lift of `f` too (`p(t + m) = p(t)`, `p_add_int`) and agrees with `g'`
  -- at `0`; so `g + m = g'` by `lem:integer-difference`. (Lean: `(s₀ := 0)` names the point
  -- `s₀ = 0` where the two agree.)
  have h : ∀ s, g s + m = g' s := lift_eq_I (hg.1.add_const_real _) hg'.1
    (fun s => by rw [p_add_int, hg.2, hg'.2]) (s₀ := 0) (by linarith)
  -- Step 3. So `g'(1) - g'(0) = (g(1) + m) - (g(0) + m) = g(1) - g(0)`.
  rw [← h 1, ← h 0]
  ring

/-- The net change `g(1) - g(0)` of a lift of `s ↦ φ(p(s))` is an integer `n`, the same for every
lift. `def:degree-circle`. (If `φ` is not continuous there may be no lift, and then any `n` will
do; for continuous `φ` a lift exists, `exists_lift_loopOf`.) -/
theorem exists_degree (φ : S1 → S1) :
    ∃ n : ℤ, ∀ g : I → ℝ, IsLift (loopOf φ) g → g 1 - g 0 = n := by
  by_cases h : ∃ g : I → ℝ, IsLift (loopOf φ) g
  · -- Take a lift `g`. Then `p(g(1)) = φ(p(1)) = φ(p(0)) = p(g(0))`, so `g(1) - g(0)` is an
    -- integer `n` (`p_eq_iff`); every other lift has the same net change (`lift_sub_eq`).
    obtain ⟨g, hg⟩ := h
    obtain ⟨n, hn⟩ := p_eq_iff.mp
      (show p (g 0) = p (g 1) by rw [hg.2, hg.2, loopOf, loopOf, p_one_eq_p_zero])
    exact ⟨n, fun g' hg' => by rw [lift_sub_eq hg hg', hn]⟩
  · -- No lift: nothing to check.
    exact ⟨0, fun g hg => (h ⟨g, hg⟩).elim⟩

/-- **`def:degree-circle`**: the degree `deg φ` of `φ : S¹ → S¹`, the net change
`g(1) - g(0)` of a lift `g` of `s ↦ φ(e^{2πis})`. Mathlib v4.34.1 has no degree of maps of the
circle.

Lean: `Classical.choose h` is a witness of the existence statement `h`, here the integer `n` of
`exists_degree`. The name `deg` is taken by week 6's degree of a loop class, so this is
`degree`. -/
def degree (φ : S1 → S1) : ℤ := Classical.choose (exists_degree φ)

/-- `deg φ = g(1) - g(0)` for every lift `g` of `s ↦ φ(p(s))`. `def:degree-circle`. -/
theorem degree_eq {φ : S1 → S1} {g : I → ℝ} (hg : IsLift (loopOf φ) g) :
    (degree φ : ℝ) = g 1 - g 0 :=
  (Classical.choose_spec (exists_degree φ) g hg).symm

/-- If `φ` is continuous, `s ↦ φ(p(s))` has a lift (`thm:path-lifting`), starting at any `a`
over `φ(p(0)) = φ(1)` (`p_surjective` gives one). -/
theorem exists_lift_loopOf {φ : S1 → S1} (hφ : Continuous φ) :
    ∃ g : I → ℝ, IsLift (loopOf φ) g := by
  obtain ⟨a, ha⟩ := p_surjective (loopOf φ 0)
  -- (Lean: `-` in the pattern discards the fact `g(0) = a`, not needed here.)
  obtain ⟨g, hg, -⟩ := exists_lift_path (continuous_loopOf hφ) 0 a ha
  exact ⟨g, hg⟩

/-- For a pointed map `φ : (S¹, 1) → (S¹, 1)`, the degree of the map is week 6's degree of the
loop `φ ∘ q` at `1` (`def:degree-circle`, `thm:pi1-circle`): with the lift `f̃` from `0`,
`deg φ = f̃(1) - f̃(0) = f̃(1)`. -/
theorem degLoop_loop (φ : PointedMap (1 : S1)) : (degLoop φ.loop : ℝ) = degree φ.1 := by
  rw [coe_degLoop, degree_eq (loopLift_isLift φ.loop), loopLift_zero, sub_zero]

/-! ## `prop:degree`: homotopy, powers, products, surjectivity -/

/-- **`prop:degree`** (1), first half: homotopic maps `φ ≃ ψ : S¹ → S¹` have the same degree.
Mathlib: none in v4.34.1.

The book's proof: the homotopy lifts (`thm:homotopy-lifting`, applied to
`(s, t) ↦ H(e^{2πis}, t)`), and `G(1, t) - G(0, t)` is a continuous integer, so constant. -/
theorem degree_eq_of_homotopic {φ ψ : S1 → S1} (h : Homotopic φ ψ) : degree φ = degree ψ := by
  -- Let `H : S¹ × I → S¹` be a homotopy from `φ` to `ψ`, and `F(s, t) = H(p(s), t)` on `I × I`.
  -- (Lean: `obtain ⟨H⟩ := h` takes a homotopy `H` whose existence `h` asserts; `set F := … with
  -- hFdef` names the map `F`, and `hFdef` is its definition.)
  obtain ⟨H⟩ := h
  set F : I × I → S1 := fun q => H.toFun (p q.1, q.2) with hFdef
  have hF : Continuous F :=
    H.continuous_toFun.comp ((continuous_qI.comp continuous_fst).prodMk continuous_snd)
  -- Step 1. `F` lifts to `G : I × I → ℝ` (`thm:homotopy-lifting`).
  obtain ⟨a, ha⟩ := p_surjective (F (0, 0))
  obtain ⟨G, hG, -⟩ := exists_lift_homotopy hF a ha
  -- Step 2. `F(0, t) = F(1, t)`, since `p(0) = p(1)`. So `p(G(0, 0)) = p(G(1, 0))` and
  -- `G(1, 0) - G(0, 0)` is an integer `m` (`p_eq_iff`).
  have hF01 : ∀ t, F (1, t) = F (0, t) := fun t => by
    simp only [hFdef, p_one_eq_p_zero]
  obtain ⟨m, hm⟩ := p_eq_iff.mp
    (show p (G (0, 0)) = p (G (1, 0)) by rw [hG.2, hG.2, hF01])
  -- Step 3. `t ↦ G(1, t)` and `t ↦ G(0, t) + m` are lifts of the same path `t ↦ F(1, t)` and
  -- agree at `t = 0`; so they agree everywhere (`lem:integer-difference`): the integer
  -- `G(1, t) - G(0, t)` is the constant `m`.
  have hconst : ∀ t, G (0, t) + m = G (1, t) := lift_eq_I
    ((hG.1.comp (continuous_const.prodMk continuous_id)).add_const_real _)
    (hG.1.comp (continuous_const.prodMk continuous_id))
    (fun t => by rw [p_add_int, hG.2, hG.2, hF01]) (s₀ := 0) (by linarith)
  -- Step 4. The bottom edge `s ↦ G(s, 0)` lifts `s ↦ φ(p(s))`, the top edge `s ↦ G(s, 1)` lifts
  -- `s ↦ ψ(p(s))`; so `deg φ = m = deg ψ`.
  have h0 : IsLift (loopOf φ) (fun s => G (s, 0)) :=
    ⟨hG.1.comp (continuous_id.prodMk continuous_const), fun s => by rw [hG.2]; exact H.zero' _⟩
  have h1 : IsLift (loopOf ψ) (fun s => G (s, 1)) :=
    ⟨hG.1.comp (continuous_id.prodMk continuous_const), fun s => by rw [hG.2]; exact H.one' _⟩
  have e0 := degree_eq h0
  have e1 := degree_eq h1
  rw [← hconst 0] at e0
  rw [← hconst 1] at e1
  have hφm : (degree φ : ℝ) = m := by rw [e0]; ring
  have hψm : (degree ψ : ℝ) = m := by rw [e1]; ring
  -- (Lean: `exact_mod_cast` reads the equation of real numbers `deg φ = deg ψ` as one of
  -- integers.)
  exact_mod_cast hφm.trans hψm.symm

/-- **`prop:degree`** (1), second half: continuous maps `φ, ψ : S¹ → S¹` of the same degree are
homotopic. Mathlib: none in v4.34.1.

The book's proof joins the lifts by the straight-line homotopy and projects it down. Here the
lifts `g_φ, g_ψ` are taken as they come, without first rotating `φ` and `ψ` to fix `1`: the
straight line `G(s, t) = (1 - t) g_φ(s) + t g_ψ(s)` has `G(1, t) - G(0, t) = n` for every `t`
already, so `p ∘ G` closes up and descends to `S¹ × I` (`prop:loops-circle`). -/
theorem homotopic_of_degree_eq {φ ψ : S1 → S1} (hφ : Continuous φ) (hψ : Continuous ψ)
    (h : degree φ = degree ψ) : Homotopic φ ψ := by
  -- Step 1. Lifts `g₀` of `s ↦ φ(p(s))` and `g₁` of `s ↦ ψ(p(s))` (`thm:path-lifting`), with
  -- the same net change `n = deg φ = deg ψ`.
  obtain ⟨g₀, hg₀⟩ := exists_lift_loopOf hφ
  obtain ⟨g₁, hg₁⟩ := exists_lift_loopOf hψ
  have e₀ := degree_eq hg₀
  have e₁ := degree_eq hg₁
  rw [h] at e₀
  -- Step 2. The straight line `G(s, t) = (1 - t) g₀(s) + t g₁(s)`, continuous (Analysis I,
  -- arithmetic, through the bridges).
  set G : I × I → ℝ := fun q => (1 - (q.2 : ℝ)) * g₀ q.1 + q.2 * g₁ q.1 with hGdef
  have hG : Continuous G := by
    have c₀ := mathlib_continuous_of_eq I_toMathlib real_toMathlib hg₀.1
    have c₁ := mathlib_continuous_of_eq I_toMathlib real_toMathlib hg₁.1
    exact continuous_of_mathlib_eq II_toMathlib real_toMathlib (by fun_prop)
  -- Step 3. `G(1, t) = G(0, t) + n`, so `F = p ∘ G` has `F(0, t) = F(1, t)` (`p_add_int`).
  have hG01 : ∀ t, G (1, t) = G (0, t) + degree ψ := fun t => by
    simp only [hGdef]; linear_combination -(1 - (t : ℝ)) * e₀ - (t : ℝ) * e₁
  have hF01 : ∀ t, p (G (0, t)) = p (G (1, t)) := fun t => by rw [hG01, p_add_int]
  -- Step 4. `F` descends to `H : S¹ × I → S¹`, `H(p(s), t) = F(s, t)`, continuous
  -- (`prop:loops-circle`); at `t = 0` it is `p(g₀(s)) = φ(p(s))`, at `t = 1` it is `ψ(p(s))`.
  refine ⟨⟨descend₂ (fun q => p (G q)), continuous_descend₂ (continuous_p.comp hG) hF01,
    fun z => ?_, fun z => ?_⟩⟩
  -- (Lean: `obtain ⟨s, rfl⟩ := qI_surjective z` writes `z = q(s)`, `q` being onto.)
  · obtain ⟨s, rfl⟩ := qI_surjective z
    rw [show ((qI s, (0 : I)) : S1 × I) = qII (s, 0) from rfl, descend₂_qII hF01]
    simp only [hGdef, Set.Icc.coe_zero, sub_zero, one_mul, zero_mul, add_zero]
    exact hg₀.2 s
  · obtain ⟨s, rfl⟩ := qI_surjective z
    rw [show ((qI s, (1 : I)) : S1 × I) = qII (s, 1) from rfl, descend₂_qII hF01]
    simp only [hGdef, Set.Icc.coe_one, sub_self, one_mul, zero_mul, zero_add]
    exact hg₁.2 s

/-- If `p(a) = p(b)` then `p(na) = p(nb)` for an integer `n`: `b - a = m ∈ ℤ` gives
`nb - na = nm ∈ ℤ` (`p_eq_iff`). -/
theorem p_mul_congr (n : ℤ) {a b : ℝ} (h : p a = p b) : p (n * a) = p (n * b) := by
  obtain ⟨m, hm⟩ := p_eq_iff.mp h
  exact p_eq_iff.mpr ⟨n * m, by push_cast; rw [← hm]; ring⟩

/-- The map `z ↦ zⁿ` of `S¹`, for `n ∈ ℤ`: `e^{2πit} ↦ e^{2πint}`, that is `p(t) ↦ p(nt)`.
`prop:degree` (2). Mathlib: `zpow` on `Circle`.

Lean: it is defined as the map that `s ↦ p(ns)` on `I` induces on the circle (`descend`,
`prop:loops-circle`), which makes sense because `p(n·0) = p(n·1)`. -/
def S1.pow (n : ℤ) : S1 → S1 := descend (fun s : I => p (n * s))

/-- `(e^{2πit})ⁿ = e^{2πint}`: `S1.pow n (p t) = p(nt)` for every real `t`. -/
theorem S1.pow_p (n : ℤ) (t : ℝ) : S1.pow n (p t) = p (n * t) :=
  -- `S1.pow n (p t) = p(ns)` for some `s ∈ I` with `p(s) = p(t)`, and then `p(ns) = p(nt)`.
  p_mul_congr n (Classical.choose_spec (qI_surjective (p t)))

/-- `z ↦ zⁿ` is continuous (`prop:loops-circle`: `s ↦ p(ns)` is, and `p(0) = p(n)`). -/
theorem S1.continuous_pow (n : ℤ) : Continuous (S1.pow n) :=
  continuous_descend (continuous_p.comp
      (continuous_of_mathlib_eq I_toMathlib real_toMathlib (by fun_prop)))
    (by simpa using (p_int n).symm)

/-- **`prop:degree`** (2): `deg (z ↦ zⁿ) = n`. The book's proof: the lift of `s ↦ e^{2πins}` is
`s ↦ ns`, from `0` to `n`. -/
theorem degree_pow (n : ℤ) : degree (S1.pow n) = n := by
  have h := degree_eq (φ := S1.pow n) (g := fun s => (n : ℝ) * s)
    ⟨continuous_of_mathlib_eq I_toMathlib real_toMathlib (by fun_prop),
      fun s => (S1.pow_p n s).symm⟩
  simp only [Set.Icc.coe_one, Set.Icc.coe_zero, mul_one, mul_zero, sub_zero] at h
  exact_mod_cast h

/-- `z ↦ (zᵃ)ᵇ` is `z ↦ z^{ba}`: at `z = p(t)`, both are `p(bat)`. -/
theorem S1.pow_comp_pow (a b : ℤ) : S1.pow b ∘ S1.pow a = S1.pow (b * a) := by
  -- (Lean: `funext z` proves an equality of maps at every point `z`.)
  funext z
  obtain ⟨t, rfl⟩ := p_surjective z
  simp only [Function.comp_apply, S1.pow_p]
  push_cast
  ring_nf

/-- A continuous `φ : S¹ → S¹` is homotopic to `z ↦ z^{deg φ}`, by `prop:degree` (1) and
`degree_pow`. -/
theorem homotopic_pow_degree {φ : S1 → S1} (hφ : Continuous φ) :
    Homotopic φ (S1.pow (degree φ)) :=
  homotopic_of_degree_eq hφ (S1.continuous_pow _) (degree_pow _).symm

/-- **`prop:degree`** (2): `deg (ψ ∘ φ) = deg ψ · deg φ`. The book's proof: `φ ≃ zᵃ` and
`ψ ≃ zᵇ` (`homotopic_pow_degree`), composition respects homotopy (`prop:hot-is-a-category`),
so `ψ ∘ φ ≃ zᵇ ∘ zᵃ = z^{ba}`, of degree `ba`. -/
theorem degree_comp {φ ψ : S1 → S1} (hφ : Continuous φ) (hψ : Continuous ψ) :
    degree (ψ ∘ φ) = degree ψ * degree φ := by
  have h := (homotopic_pow_degree hφ).comp (homotopic_pow_degree hψ)
  rw [degree_eq_of_homotopic h, S1.pow_comp_pow, degree_pow]

/-- **`prop:degree`** (2): the degree, on homotopy classes, `deg : [S¹, S¹] → ℤ`; well defined by
`prop:degree` (1) (`def:hot`).

Lean: `Quotient.lift F h` defines a map on classes by `[φ] ↦ F(φ)`, `h` saying that `F` takes
the same value on homotopic maps. -/
def degreeHot : Hot S1 S1 → ℤ :=
  Quotient.lift (fun φ : ContMap S1 S1 => degree φ.1)
    (fun _ _ h => degree_eq_of_homotopic h)

/-- **`prop:degree`** (2): `deg : [S¹, S¹] → ℤ` is a bijection. One to one by `prop:degree` (1),
onto because `deg (z ↦ zⁿ) = n`. Mathlib: none in v4.34.1. -/
theorem degreeHot_bijective : Function.Bijective degreeHot := by
  constructor
  · -- One to one: if `deg φ = deg ψ` then `φ ≃ ψ`, so `[φ] = [ψ]`.
    intro a b hab
    -- (Lean: `induction a using Quotient.ind` writes the class `a` as `[a]`; `rename_i a` gives
    -- the representative its name.)
    induction a using Quotient.ind
    rename_i a
    induction b using Quotient.ind
    rename_i b
    exact Quotient.sound (homotopic_of_degree_eq a.2 b.2 hab)
  · -- Onto: `n = deg [z ↦ zⁿ]`.
    intro n
    exact ⟨Hot.mk (S1.pow n) (S1.continuous_pow n), degree_pow n⟩

/-- **`prop:degree`** (3), in the form used below: a continuous `φ : S¹ → S¹` that misses a point
`w` has degree `0`.

The book factors `φ` through `S¹ ∖ {w} ≅ ℝ`, which is contractible. Here the same idea is said
with the lift: write `w = p(a)`; a lift `g` of `s ↦ φ(p(s))` never takes a value in `a + ℤ`,
since `p(a + k) = w`. If `|g(1) - g(0)| ≥ 1`, then `[g(0), g(1)]` (or `[g(1), g(0)]`) contains a
point `a + k`, and by the intermediate value theorem (Analysis I) `g` takes it. -/
theorem degree_eq_zero_of_not_mem {φ : S1 → S1} (hφ : Continuous φ) {w : S1}
    (hw : ∀ z, φ z ≠ w) : degree φ = 0 := by
  obtain ⟨g, hg⟩ := exists_lift_loopOf hφ
  obtain ⟨a, rfl⟩ := p_surjective w
  have e := degree_eq hg
  -- `g` misses `a + k` for every integer `k`: else `φ(p(s)) = p(g(s)) = p(a + k) = p(a)`.
  have hmiss : ∀ (s : I) (k : ℤ), g s ≠ a + k := fun s k hs =>
    hw (p s) (by show loopOf φ s = p a; rw [← hg.2 s, hs, p_add_int])
  -- The intermediate value theorem for `g` on the connected `I` (Analysis I, `preconnected_I`).
  have hgM := mathlib_continuous_of_eq I_toMathlib real_toMathlib hg.1
  have hconn : PreconnectedSpace I := by
    have := preconnected_I; rwa [I_toMathlib] at this
  -- Suppose `deg φ = n ≠ 0`. Let `lo` be the smaller of `g(0)`, `g(1)`; the point
  -- `c = a + ⌈lo - a⌉` lies in `[lo, lo + 1)`, so between `g(0)` and `g(1)`, which differ by
  -- `|n| ≥ 1`.
  -- (Lean: `by_contra hn` assumes `deg φ ≠ 0` and looks for a contradiction.)
  by_contra hn
  -- Two cases: `n ≤ -1` or `n ≥ 1`.
  rcases lt_or_gt_of_ne hn with hlt | hgt
  -- Case `n ≤ -1`: then `g(1) ≤ g(0) - 1`, so `a + ⌈g(1) - a⌉ ∈ [g(1), g(0)]` (Analysis I:
  -- `x ≤ ⌈x⌉ < x + 1`), and by the intermediate value theorem `g` takes this value.
  · have hle : (degree φ : ℝ) ≤ -1 := by
      have : degree φ ≤ -1 := by omega
      exact_mod_cast this
    obtain ⟨s, hs⟩ := intermediate_value_univ (1 : I) 0 hgM
      (show a + (⌈g 1 - a⌉ : ℤ) ∈ Icc (g 1) (g 0) from
        ⟨by linarith [Int.le_ceil (g 1 - a)], by linarith [Int.ceil_lt_add_one (g 1 - a)]⟩)
    exact hmiss s _ hs
  -- Case `n ≥ 1`: the same with `a + ⌈g(0) - a⌉ ∈ [g(0), g(1)]`.
  · have hle : (1 : ℝ) ≤ degree φ := by exact_mod_cast hgt
    obtain ⟨s, hs⟩ := intermediate_value_univ (0 : I) 1 hgM
      (show a + (⌈g 0 - a⌉ : ℤ) ∈ Icc (g 0) (g 1) from
        ⟨by linarith [Int.le_ceil (g 0 - a)], by linarith [Int.ceil_lt_add_one (g 0 - a)]⟩)
    exact hmiss s _ hs

/-- **`prop:degree`** (3): a continuous map `φ : S¹ → S¹` of non-zero degree is onto. -/
theorem surjective_of_degree_ne_zero {φ : S1 → S1} (hφ : Continuous φ) (h : degree φ ≠ 0) :
    Function.Surjective φ := by
  -- If `φ` missed `w`, its degree would be `0` (`degree_eq_zero_of_not_mem`). (Lean: `push Not`
  -- turns `¬ ∃ z, φ z = w` into `∀ z, φ z ≠ w`.)
  intro w
  by_contra hw
  push Not at hw
  exact h (degree_eq_zero_of_not_mem hφ hw)

/-! ## Normalising: `v ↦ v/|v|`, and maps given by formulas -/

/-- The point `v/|v|` of `S¹`, for `v ≠ 0` in the plane: week 6's unit vector `Brouwer.dir v 0`,
`(v - 0)/|v - 0|`, which lies on `S¹` (`Brouwer.dir_sq`). -/
def nrm (v : ℝ × ℝ) (hv : v ≠ 0) : S1 := ⟨Brouwer.dir v 0, Brouwer.dir_sq hv⟩

/-- Unfolding: `v/|v|`, as a point of the plane. -/
@[simp] theorem coe_nrm (v : ℝ × ℝ) (hv : v ≠ 0) : (nrm v hv : ℝ × ℝ) = Brouwer.dir v 0 := rfl

/-- Normalising a positive multiple `c u` of a point `u ∈ S¹` gives `u` back: `|cu| = c`. -/
theorem nrm_smul {c : ℝ} (hc : 0 < c) (u : S1) (h : ((c * u.1.1, c * u.1.2) : ℝ × ℝ) ≠ 0) :
    nrm (c * u.1.1, c * u.1.2) h = u := by
  -- `|cu|² = c²(x² + y²) = c²`, so `|cu| = √(c²) = c` (Analysis I), and `cu/c = u`.
  have hs : √((c * u.1.1) ^ 2 + (c * u.1.2) ^ 2) = c := by
    rw [show (c * u.1.1) ^ 2 + (c * u.1.2) ^ 2 = c ^ 2 by
      linear_combination c ^ 2 * S1.sq_add_sq u]
    exact Real.sqrt_sq hc.le
  apply S1.ext' <;>
  · simp only [coe_nrm, Brouwer.dir, Prod.fst_zero, Prod.snd_zero, sub_zero, hs]
    field_simp

/-- A map `w ↦ v(w)/|v(w)|` into `S¹` is continuous when `v` is continuous and never `0`.
Analysis I: arithmetic, `√` and division by a function that does not vanish (Mathlib's
`Continuous.div`), as in week 6's `Brouwer.continuous_ray`. Here `v` is continuous for Mathlib's
version `mW` of the topology of `W` (`hW`), which is how formulas are checked (`fun_prop`). -/
theorem continuous_nrm {W : Type u} [tW : TopSpace W] {mW : TopologicalSpace W}
    (hW : tW.toMathlib = mW) {v : W → ℝ × ℝ} (hv : @_root_.Continuous W _ mW _ v)
    (hne : ∀ w, v w ≠ 0) : Continuous (fun w => nrm (v w) (hne w)) := by
  -- (Lean: `subst hW` replaces `mW` by `tW.toMathlib`; `let _ := …` equips `W` with it.)
  subst hW
  let _ := tW.toMathlib
  -- `N(w) = |v(w)|` is continuous and never `0` (`Brouwer.dist_sq_pos`) …
  have hN : _root_.Continuous
      (fun w => √(((v w).1 - (0 : ℝ × ℝ).1) ^ 2 + ((v w).2 - (0 : ℝ × ℝ).2) ^ 2)) := by fun_prop
  have hN0 : ∀ w, √(((v w).1 - (0 : ℝ × ℝ).1) ^ 2 + ((v w).2 - (0 : ℝ × ℝ).2) ^ 2) ≠ 0 :=
    fun w => (Real.sqrt_pos.mpr (Brouwer.dist_sq_pos (hne w))).ne'
  -- … so `v/N` is continuous, coordinate by coordinate, and it takes values in `S¹`.
  exact continuous_of_mathlib_eq rfl S1_toMathlib (_root_.Continuous.subtype_mk
    (((hv.fst.sub _root_.continuous_const).div hN hN0).prodMk
      ((hv.snd.sub _root_.continuous_const).div hN hN0)) _)

/-- A continuous `H : S¹ × I → S¹` is a homotopy from `H(-, 0)` to `H(-, 1)` (`def:homotopy`). -/
theorem homotopic_ends {H : S1 × I → S1} (hH : Continuous H) :
    Homotopic (fun z => H (z, 0)) (fun z => H (z, 1)) :=
  ⟨⟨H, hH, fun _ => rfl, fun _ => rfl⟩⟩

/-- A constant map `S¹ → S¹` has degree `0`: a lift is the constant `a` with `p(a) = c`. -/
theorem degree_const (c : S1) : degree (fun _ : S1 => c) = 0 := by
  obtain ⟨a, ha⟩ := p_surjective c
  have h := degree_eq (φ := fun _ : S1 => c) (g := fun _ => a)
    ⟨continuous_const_real a, fun _ => ha⟩
  simp only [sub_self] at h
  exact_mod_cast h

/-! ## The fundamental theorem of algebra (`thm:fta`)

The plane `ℝ × ℝ` is identified with `ℂ` by `(x, y) ↔ x + iy` (`S1.toC`, `vec`).

Lean, for polynomials (Mathlib's): `q : Polynomial ℂ` is a polynomial with complex coefficients;
`q.eval x` is `q(x)`, `q.coeff i` is the coefficient `aᵢ` of `xⁱ`, `q.natDegree` its degree `n`,
`q.Monic` says `aₙ = 1`, `q.IsRoot z` says `q(z) = 0`. `‖x‖` is the absolute value `|x|` of a
complex number, `∑ i ∈ Finset.range n, f i` is `Σ_{i < n} f(i)`, and `(R : ℂ)` is the real
number `R` seen as a complex number. -/

/-- A point `z = (x, y)` of `S¹` as the complex number `x + iy`. -/
def S1.toC (z : S1) : ℂ := (z.1.1 : ℂ) + (z.1.2 : ℂ) * Complex.I

/-- A complex number `w` as the point `(Re w, Im w)` of the plane. -/
def vec (w : ℂ) : ℝ × ℝ := (w.re, w.im)

/-- `vec w = 0` only for `w = 0`. -/
theorem vec_ne_zero {w : ℂ} (hw : w ≠ 0) : vec w ≠ 0 := fun h =>
  hw (Complex.ext (congrArg Prod.fst h) (congrArg Prod.snd h))

/-- `|x + iy| = 1` for `(x, y) ∈ S¹`. -/
theorem S1.norm_toC (z : S1) : ‖S1.toC z‖ = 1 := by
  rw [Complex.norm_def, Complex.normSq_apply]
  simp [S1.toC, ← sq, S1.sq_add_sq z]

/-- de Moivre: `(cos θ + i sin θ)ⁿ = cos nθ + i sin nθ` for `θ = 2πt`, read in the plane:
`vec ((p t)ⁿ) = p(nt)`. Analysis I (Mathlib's `Complex.cos_add_sin_mul_I_pow`). -/
theorem vec_toC_p_pow (n : ℕ) (t : ℝ) : vec (S1.toC (p t) ^ n) = (p ((n : ℤ) * t) : ℝ × ℝ) := by
  have e : S1.toC (p t) =
      Complex.cos (2 * π * t : ℝ) + Complex.sin (2 * π * t : ℝ) * Complex.I := by
    simp [S1.toC, Complex.ofReal_cos, Complex.ofReal_sin]
  -- de Moivre, then read off the real and imaginary parts: `cos 2πnt` and `sin 2πnt`.
  rw [e, Complex.cos_add_sin_mul_I_pow, ← Complex.ofReal_natCast, ← Complex.ofReal_mul,
    ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  simp only [vec, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
    Complex.ofReal_im, Complex.I_im, mul_one, sub_self, add_zero, Complex.add_im,
    Complex.mul_im, zero_add, coe_p, Int.cast_natCast]
  ring_nf

/-- `thm:fta`, the estimate: if `q = zⁿ + a_{n-1}zⁿ⁻¹ + ⋯ + a₀` is monic of degree `n ≥ 1` and
`|z| = R = 1 + Σ |aᵢ|`, then `|q(z) - zⁿ| < Rⁿ = |zⁿ|`. The book's computation:
`|a_{n-1}zⁿ⁻¹ + ⋯ + a₀| ≤ Σ |aᵢ| Rⁱ ≤ (Σ |aᵢ|) Rⁿ⁻¹ < R · Rⁿ⁻¹`, as `R ≥ 1` and `R > Σ |aᵢ|`. -/
theorem fta_estimate {q : Polynomial ℂ} (hq : q.Monic) (hn : 1 ≤ q.natDegree) {x : ℂ}
    (hx : ‖x‖ = 1 + ∑ i ∈ Finset.range q.natDegree, ‖q.coeff i‖) :
    ‖q.eval x - x ^ q.natDegree‖ < ‖x‖ ^ q.natDegree := by
  set n := q.natDegree with hndef
  set S := ∑ i ∈ Finset.range n, ‖q.coeff i‖ with hSdef
  have hS : 0 ≤ S := Finset.sum_nonneg fun i _ => norm_nonneg _
  have hR1 : 1 ≤ ‖x‖ := by linarith
  -- Step 1. `q(x) - xⁿ = Σ_{i < n} aᵢ xⁱ`: the top coefficient is `1` (`q` is monic).
  have e : q.eval x - x ^ n = ∑ i ∈ Finset.range n, q.coeff i * x ^ i := by
    rw [Polynomial.eval_eq_sum_range, Finset.sum_range_succ, ← hndef, hq.coeff_natDegree,
      one_mul, add_sub_cancel_right]
  rw [e]
  -- Step 2. The chain of inequalities.
  calc ‖∑ i ∈ Finset.range n, q.coeff i * x ^ i‖
      ≤ ∑ i ∈ Finset.range n, ‖q.coeff i‖ * ‖x‖ ^ i := by
        refine (norm_sum_le _ _).trans (le_of_eq ?_)
        simp only [norm_mul, norm_pow]
    _ ≤ ∑ i ∈ Finset.range n, ‖q.coeff i‖ * ‖x‖ ^ (n - 1) := by
        refine Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_left
          (pow_le_pow_right₀ hR1 ?_) (norm_nonneg _)
        have := Finset.mem_range.mp hi
        omega
    _ = S * ‖x‖ ^ (n - 1) := by rw [Finset.sum_mul]
    _ < ‖x‖ * ‖x‖ ^ (n - 1) := by
        apply mul_lt_mul_of_pos_right (by linarith) (by positivity)
    _ = ‖x‖ ^ n := by
        rw [← pow_succ']
        congr 1
        omega

/-- **`thm:fta`** for a monic `q` of degree `n ≥ 1`: it has a root. The book's proof, by
contradiction. If `q` has no root, `f_r(z) = q(rz)/|q(rz)|` is a map `S¹ → S¹` for every `r ≥ 0`:
- as `r` runs from `0` to `R`, the `f_r` are a homotopy from a constant map to `f_R`, so
  `deg f_R = 0`;
- with `R = 1 + Σ |aᵢ|`, `zⁿ + t(q(z) - zⁿ)` has no zero on `|z| = R` (`fta_estimate`), and
  normalising it is a homotopy from `z ↦ zⁿ` to `f_R`, so `deg f_R = n ≥ 1`. -/
theorem fta_monic {q : Polynomial ℂ} (hq : q.Monic) (hn : 1 ≤ q.natDegree) :
    ∃ z, q.IsRoot z := by
  -- Suppose `q` has no root; `n = deg q`, `R = 1 + Σ |aᵢ| > 0`.
  by_contra hno
  push Not at hno
  have hno' : ∀ x, q.eval x ≠ 0 := hno
  set n := q.natDegree with hndef
  set R : ℝ := 1 + ∑ i ∈ Finset.range n, ‖q.coeff i‖ with hRdef
  have hR : 0 < R := by
    have : 0 ≤ ∑ i ∈ Finset.range n, ‖q.coeff i‖ := Finset.sum_nonneg fun i _ => norm_nonneg _
    linarith
  -- On `|z| = R`: `|Rz| = R`.
  have hnormR : ∀ z : S1, ‖(R : ℂ) * S1.toC z‖ = R := fun z => by
    rw [norm_mul, S1.norm_toC, mul_one, Complex.norm_real, Real.norm_of_nonneg hR.le]
  -- Continuity of the formulas below (Analysis I, through the bridge `S1I_toMathlib`): the
  -- coordinates of `z`, the time `t`, polynomials, `Re`, `Im`.
  have hzC : _root_.Continuous (fun w : S1 × I => S1.toC w.1) := by unfold S1.toC; fun_prop
  -- Step 1. The homotopy `H₁(z, t) = q(tRz)/|q(tRz)|`, from a constant map to `f_R`.
  have hne₁ : ∀ w : S1 × I, vec (q.eval (((w.2 : ℝ) : ℂ) * R * S1.toC w.1)) ≠ 0 :=
    fun w => vec_ne_zero (hno' _)
  have hH₁ := continuous_nrm S1I_toMathlib
    (v := fun w : S1 × I => vec (q.eval (((w.2 : ℝ) : ℂ) * R * S1.toC w.1)))
    (by unfold vec; fun_prop) hne₁
  have d₁ := degree_eq_of_homotopic (homotopic_ends hH₁)
  -- At `t = 0` it is the constant `q(0)/|q(0)|`, of degree `0`.
  have c₀ : (fun z : S1 => nrm _ (hne₁ (z, 0))) = fun _ => nrm _ (vec_ne_zero (hno' 0)) := by
    funext z; apply Subtype.ext; simp
  rw [c₀, degree_const] at d₁
  -- Step 2. The homotopy `H₂(z, t) = (Rz)ⁿ + t(q(Rz) - (Rz)ⁿ)`, normalised, from `z ↦ zⁿ` to
  -- `f_R`. It never vanishes: `|t(q(Rz) - (Rz)ⁿ)| < Rⁿ = |(Rz)ⁿ|`.
  have hne₂ : ∀ w : S1 × I, vec (((R : ℂ) * S1.toC w.1) ^ n + ((w.2 : ℝ) : ℂ) *
      (q.eval ((R : ℂ) * S1.toC w.1) - ((R : ℂ) * S1.toC w.1) ^ n)) ≠ 0 := by
    intro w
    apply vec_ne_zero
    intro h0
    have hest := fta_estimate hq hn (x := (R : ℂ) * S1.toC w.1) (by rw [hnormR])
    have ht0 : 0 ≤ (w.2 : ℝ) := w.2.2.1
    have ht1 : (w.2 : ℝ) ≤ 1 := w.2.2.2
    -- From `h0`: `(Rz)ⁿ = -t(q(Rz) - (Rz)ⁿ)`, so `Rⁿ ≤ |q(Rz) - (Rz)ⁿ| < Rⁿ`.
    have h1 : ((R : ℂ) * S1.toC w.1) ^ n = -(((w.2 : ℝ) : ℂ) *
        (q.eval ((R : ℂ) * S1.toC w.1) - ((R : ℂ) * S1.toC w.1) ^ n)) :=
      eq_neg_of_add_eq_zero_left h0
    have h2 := congrArg norm h1
    rw [norm_neg, norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg ht0] at h2
    have h3 : (w.2 : ℝ) * ‖q.eval ((R : ℂ) * S1.toC w.1) - ((R : ℂ) * S1.toC w.1) ^ n‖ ≤
        ‖q.eval ((R : ℂ) * S1.toC w.1) - ((R : ℂ) * S1.toC w.1) ^ n‖ :=
      mul_le_of_le_one_left (norm_nonneg _) ht1
    linarith
  have hH₂ := continuous_nrm S1I_toMathlib
    (v := fun w : S1 × I => vec (((R : ℂ) * S1.toC w.1) ^ n + ((w.2 : ℝ) : ℂ) *
      (q.eval ((R : ℂ) * S1.toC w.1) - ((R : ℂ) * S1.toC w.1) ^ n)))
    (by unfold vec; fun_prop) hne₂
  have d₂ := degree_eq_of_homotopic (homotopic_ends hH₂)
  -- At `t = 1` it is `f_R` again, the end of `H₁`.
  have c₁ : (fun z : S1 => nrm _ (hne₂ (z, 1))) = fun z => nrm _ (hne₁ (z, 1)) := by
    funext z; apply Subtype.ext; simp
  -- At `t = 0` it is `(Rz)ⁿ/|(Rz)ⁿ| = zⁿ`, since `(Rz)ⁿ = Rⁿ zⁿ` and `zⁿ = p(nt)` for `z = p(t)`
  -- (`vec_toC_p_pow`).
  have c₂ : (fun z : S1 => nrm _ (hne₂ (z, 0))) = S1.pow n := by
    funext z
    obtain ⟨t, rfl⟩ := p_surjective z
    rw [S1.pow_p]
    -- `(p(nt)) = (cos 2πnt, sin 2πnt)`, and `Rⁿ p(nt)` is not `0`.
    have hne : ((R ^ n * (p ((n : ℤ) * t)).1.1, R ^ n * (p ((n : ℤ) * t)).1.2) : ℝ × ℝ) ≠ 0 := by
      intro h
      have h1 := congrArg Prod.fst h
      have h2 := congrArg Prod.snd h
      simp only [Prod.fst_zero, Prod.snd_zero] at h1 h2
      have hs := S1.sq_add_sq (p ((n : ℤ) * t))
      have hRn : R ^ n ≠ 0 := (pow_pos hR n).ne'
      have e1 := (mul_eq_zero.mp h1).resolve_left hRn
      have e2 := (mul_eq_zero.mp h2).resolve_left hRn
      rw [e1, e2] at hs
      norm_num at hs
    refine Eq.trans ?_ (nrm_smul (pow_pos hR n) _ hne)
    apply Subtype.ext
    simp only [coe_nrm]
    congr 1
    have hv := vec_toC_p_pow n t
    simp only [vec, Prod.ext_iff] at hv
    simp only [vec, Set.Icc.coe_zero, Complex.ofReal_zero, zero_mul, add_zero, mul_pow,
      ← Complex.ofReal_pow, Complex.re_ofReal_mul, Complex.im_ofReal_mul, hv.1, hv.2]
  -- So `deg f_R = deg (z ↦ zⁿ) = n`.
  rw [c₁, c₂, degree_pow] at d₂
  -- Step 3. `n = deg f_R = 0`, against `n ≥ 1`.
  have : (n : ℤ) = 0 := d₂.trans d₁.symm
  omega

/-- **`thm:fta`** (the fundamental theorem of algebra): every non-constant complex polynomial
has a complex root. The proof is the book's, by the degree (`fta_monic`); dividing by the leading
coefficient makes `q` monic without changing its roots. Mathlib: `Complex.exists_root`
(not used here). -/
theorem fta (q : Polynomial ℂ) (hq : 0 < q.degree) : ∃ z, q.IsRoot z := by
  -- `q ≠ 0`, and `c = (leading coefficient)⁻¹ ≠ 0`.
  have hq0 : q ≠ 0 := Polynomial.ne_zero_of_degree_gt hq
  have hc : (q.leadingCoeff)⁻¹ ≠ 0 := inv_ne_zero (Polynomial.leadingCoeff_ne_zero.mpr hq0)
  -- `cq` is monic of the same degree `n ≥ 1`, so it has a root `z` (`fta_monic`) …
  obtain ⟨z, hz⟩ := fta_monic (Polynomial.monic_mul_leadingCoeff_inv hq0)
    (by rw [Polynomial.natDegree_mul_C hc]
        exact Polynomial.natDegree_pos_iff_degree_pos.mpr hq)
  -- … and `q(z) c = 0` with `c ≠ 0` gives `q(z) = 0`.
  refine ⟨z, ?_⟩
  have : q.eval z * (q.leadingCoeff)⁻¹ = 0 := by
    simpa [Polynomial.IsRoot, Polynomial.eval_mul] using hz
  exact (mul_eq_zero.mp this).resolve_right hc

/-! ## Odd maps (`lem:odd-degree`) and Borsuk–Ulam (`thm:borsuk-ulam-2`) -/

/-- The point `1/2` of `I`. -/
def I.midpoint : I := ⟨1 / 2, by norm_num, by norm_num⟩

/-- `s ↦ s/2`, a map `I → I` onto `[0, 1/2]`. -/
def I.lowerHalf (s : I) : I := ⟨(s : ℝ) / 2, by linarith [s.2.1], by linarith [s.2.2]⟩

/-- `s ↦ (s + 1)/2`, a map `I → I` onto `[1/2, 1]`. -/
def I.upperHalf (s : I) : I := ⟨((s : ℝ) + 1) / 2, by linarith [s.2.1], by linarith [s.2.2]⟩

/-- **`lem:odd-degree`**: if `h : S¹ → S¹` is continuous and odd, `h(-z) = -h(z)`, then `deg h`
is odd. Mathlib: none in v4.34.1. (Lean: `Odd m` says `m = 2k + 1` for an integer `k`.)

The book's proof: with `g` a lift of `s ↦ h(p(s))`, oddness gives
`p(g(s + 1/2)) = -p(g(s)) = p(g(s) + 1/2)` for `s ∈ [0, 1/2]` (`p_add_half`), so
`g(s + 1/2) - g(s) - 1/2` is a continuous integer, a constant `k`; then
`deg h = (g(1) - g(1/2)) + (g(1/2) - g(0)) = 2(k + 1/2) = 2k + 1`. Here `s ∈ [0, 1/2]` is written
`s/2` with `s ∈ I`. -/
theorem degree_odd {h : S1 → S1} (hh : Continuous h) (hodd : ∀ z, h (-z) = -h z) :
    Odd (degree h) := by
  obtain ⟨g, hg⟩ := exists_lift_loopOf hh
  -- `h(p(1/2 + t)) = h(-p(t)) = -h(p(t)) = -p(g(…)) = p(1/2 + g(…))` (`p_add_half` twice).
  have key : ∀ (t : ℝ) (a : ℝ), p a = h (p t) → h (p (1 / 2 + t)) = p (1 / 2 + a) := by
    intro t a ha
    rw [p_add_half, hodd, p_add_half, ha]
  -- Step 1. `p(g(1/2)) = p(1/2 + g(0))`, so `g(1/2) - (1/2 + g(0))` is an integer `k`.
  obtain ⟨k, hk⟩ := p_eq_iff.mp (show p (1 / 2 + g 0) = p (g I.midpoint) by
    rw [hg.2 I.midpoint, loopOf, ← key 0 (g 0) (by rw [hg.2]; simp [loopOf])]
    simp [I.midpoint])
  -- Step 2. `s ↦ g((s + 1)/2)` and `s ↦ g(s/2) + 1/2 + k` lift the same path, and agree at `0`;
  -- so they are equal (`lem:integer-difference`).
  have hlo : Continuous I.lowerHalf :=
    continuous_of_mathlib_eq I_toMathlib I_toMathlib (by unfold I.lowerHalf; fun_prop)
  have hhi : Continuous I.upperHalf :=
    continuous_of_mathlib_eq I_toMathlib I_toMathlib (by unfold I.upperHalf; fun_prop)
  have hlo0 : I.lowerHalf 0 = 0 := Subtype.ext (by simp [I.lowerHalf])
  have hlo1 : I.lowerHalf 1 = I.midpoint := Subtype.ext (by simp [I.lowerHalf, I.midpoint])
  have hhi0 : I.upperHalf 0 = I.midpoint := Subtype.ext (by simp [I.upperHalf, I.midpoint])
  have hhi1 : I.upperHalf 1 = 1 := Subtype.ext (by norm_num [I.upperHalf])
  have hsame : ∀ s, g (I.lowerHalf s) + 1 / 2 + k = g (I.upperHalf s) := lift_eq_I
    ((hg.1.comp hlo).add_const_real _ |>.add_const_real _) (hg.1.comp hhi)
    -- `p(g(s/2) + 1/2 + k) = p(1/2 + g(s/2)) = h(p(1/2 + s/2)) = h(p((s + 1)/2))`, by `key`
    -- and `p_add_int`; and `p(g((s + 1)/2)) = h(p((s + 1)/2))` since `g` is a lift. (Lean:
    -- `a |>.f b` is `a.f b`.)
    (fun s => by
      rw [show g (I.lowerHalf s) + 1 / 2 + k = (1 / 2 + g (I.lowerHalf s)) + k by ring,
        p_add_int, hg.2 (I.upperHalf s), loopOf,
        show ((I.upperHalf s : I) : ℝ) = 1 / 2 + (I.lowerHalf s : ℝ) by
          simp only [I.upperHalf, I.lowerHalf]; ring]
      exact (key _ _ (hg.2 _)).symm)
    (s₀ := 0) (by rw [hlo0, hhi0]; linarith)
  -- Step 3. `g(1) = g(1/2) + 1/2 + k = g(0) + 2k + 1`.
  have e := degree_eq hg
  have h1 := hsame 1
  rw [hlo1, hhi1] at h1
  refine ⟨k, ?_⟩
  have : (degree h : ℝ) = 2 * k + 1 := by rw [e]; linarith
  exact_mod_cast this

/-- The antipode `-v` of `v ∈ S²` (week 4's `S2`), on `S²` since
`(-x)² + (-y)² + (-z)² = x² + y² + z²`.

Lean: a point `v : ℝ × ℝ × ℝ` is a pair `(v.1, v.2)` with `v.2 = (v.2.1, v.2.2)`; so `x, y, z`
are `v.1`, `v.2.1`, `v.2.2`. -/
theorem S2.neg_mem (v : S2) : -v.1 ∈ S2 := by
  have := v.2
  simp only [S2, mem_ofPred_eq] at this ⊢
  simpa using this

/-- The antipodal map `v ↦ -v` on `S²`, by `S2.neg_mem`. -/
instance instNegS2 : Neg S2 := ⟨fun v => ⟨-v.1, S2.neg_mem v⟩⟩

/-- `-(-v) = v` on `S²`. -/
theorem S2.neg_neg (v : S2) : -(-v) = v := Subtype.ext (_root_.neg_neg v.1)

/-- **Bridge.** The course topology of the plane `ℝ × ℝ` is Mathlib's. -/
theorem R2_toMathlib :
    (prod : TopSpace (ℝ × ℝ)).toMathlib = (inferInstance : TopologicalSpace (ℝ × ℝ)) := by
  rw [prod_toMathlib, real_toMathlib]

/-- Normalising is odd: `(-v)/|-v| = -(v/|v|)`. -/
theorem nrm_neg (v : ℝ × ℝ) (hv : v ≠ 0) (hv' : -v ≠ 0) : nrm (-v) hv' = -nrm v hv := by
  apply S1.ext' <;> simp [Brouwer.dir, neg_div]

/-- **`thm:borsuk-ulam-2`** (Borsuk–Ulam for `n = 2`): for every continuous `f : S² → ℝ²` there
is `x ∈ S²` with `f(x) = f(-x)`. Mathlib v4.34.1 has no Borsuk–Ulam theorem.

The book's proof: if not, `g(x) = (f(x) - f(-x))/|f(x) - f(-x)|` is a continuous odd map
`S² → S¹`. On the equator it is odd, so of odd degree (`lem:odd-degree`), in particular not `0`.
But the equator bounds the upper hemisphere, a disc on which `g` is defined; so `g` on the
equator is null-homotopic, of degree `0`. Here the null-homotopy is written out: it shrinks the
equator through the upper hemisphere to the north pole, `(z, t) ↦ ((1 - t)z, √(1 - (1 - t)²))`,
which is `D²`'s straight-line contraction `z ↦ (1 - t)z` lifted to the hemisphere. -/
theorem borsuk_ulam_2 (f : S2 → ℝ × ℝ) (hf : Continuous f) : ∃ x, f x = f (-x) := by
  by_contra hno
  push Not at hno
  have hne : ∀ x, f x - f (-x) ≠ 0 := fun x => sub_ne_zero.mpr (hno x)
  -- Step 1. `g(x) = (f(x) - f(-x))/|f(x) - f(-x)|` is continuous (Analysis I, through the
  -- bridges) and odd.
  have hfM := mathlib_continuous_of_eq S2_toMathlib R2_toMathlib hf
  have hneg : _root_.Continuous (fun x : S2 => -x) :=
    (_root_.continuous_subtype_val.neg).subtype_mk _
  set g : S2 → S1 := fun x => nrm (f x - f (-x)) (hne x) with hgdef
  have hg : Continuous g :=
    continuous_nrm S2_toMathlib (v := fun x => f x - f (-x)) (hfM.sub (hfM.comp hneg)) hne
  have hgodd : ∀ x, g (-x) = -g x := fun x => by
    simp only [hgdef]
    rw [← nrm_neg _ (hne x) (neg_ne_zero.mpr (hne x))]
    apply Subtype.ext
    simp only [coe_nrm]
    rw [S2.neg_neg, neg_sub]
  -- Step 2. The equator `e : S¹ → S²`, `e(x, y) = (x, y, 0)`; it is odd, so `g ∘ e` is odd and
  -- has odd degree (`lem:odd-degree`): not `0`.
  set e : S1 → S2 := fun z => ⟨(z.1.1, z.1.2, 0), by
    simp only [S2, mem_ofPred_eq]; nlinarith [S1.sq_add_sq z]⟩ with hedef
  have he : Continuous e := continuous_of_mathlib_eq S1_toMathlib S2_toMathlib
    (by simp only [hedef]; fun_prop)
  have heodd : ∀ z, e (-z) = -e z := fun z => by
    apply Subtype.ext
    show ((-z.1.1, -z.1.2, (0 : ℝ)) : ℝ × ℝ × ℝ) = -((z.1.1, z.1.2, (0 : ℝ)) : ℝ × ℝ × ℝ)
    simp
  have hodd := degree_odd (hg.comp he) (fun z => by
    show g (e (-z)) = -g (e z); rw [heodd, hgodd])
  -- Step 3. The homotopy through the upper hemisphere: `E(z, t) = ((1 - t)z, √(1 - (1 - t)²))`.
  have hmem : ∀ w : S1 × I, ((1 - (w.2 : ℝ)) * w.1.1.1, (1 - (w.2 : ℝ)) * w.1.1.2,
      √(1 - (1 - (w.2 : ℝ)) ^ 2)) ∈ S2 := fun w => by
    have h0 : 0 ≤ (w.2 : ℝ) := w.2.2.1
    have h1 : (w.2 : ℝ) ≤ 1 := w.2.2.2
    simp only [S2, mem_ofPred_eq]
    rw [Real.sq_sqrt (by nlinarith)]
    linear_combination (1 - (w.2 : ℝ)) ^ 2 * S1.sq_add_sq w.1
  set E : S1 × I → S2 := fun w => ⟨_, hmem w⟩ with hEdef
  have hE : Continuous E := continuous_of_mathlib_eq S1I_toMathlib S2_toMathlib
    (by simp only [hEdef]; fun_prop)
  have d := degree_eq_of_homotopic (homotopic_ends (hg.comp hE))
  -- At `t = 0`, `E(z, 0) = (z, 0) = e(z)`; at `t = 1`, `E(z, 1) = (0, 0, 1)`, the north pole.
  have c0 : (fun z => (g ∘ E) (z, 0)) = g ∘ e := by
    funext z
    simp only [Function.comp_apply]
    congr 1
    apply Subtype.ext
    simp [hEdef, hedef]
  have c1 : (fun z => (g ∘ E) (z, 1)) = fun _ => g ⟨(0, 0, 1), by simp [S2]⟩ := by
    funext z
    simp only [Function.comp_apply]
    congr 1
    apply Subtype.ext
    simp [hEdef]
  rw [c0, c1, degree_const] at d
  -- Step 4. So `deg (g ∘ e) = 0`, which is not odd.
  rw [d] at hodd
  exact absurd hodd (by decide)

/-! ## The winding number (`def:winding-number`, `prop:winding`) -/

/-- The map `z ↦ (γ(z) - q)/|γ(z) - q|` of `S¹` to itself, for `γ : S¹ → ℝ²` and a point `q` that
`γ` misses (`hq : ∀ z, γ z ≠ q`). `def:winding-number`. -/
def windingMap (γ : S1 → ℝ × ℝ) (q : ℝ × ℝ) (hq : ∀ z, γ z ≠ q) (z : S1) : S1 :=
  nrm (γ z - q) (sub_ne_zero.mpr (hq z))

/-- **`def:winding-number`**: the winding number `w(γ, q) = deg (z ↦ (γ(z) - q)/|γ(z) - q|)` of
`γ : S¹ → ℝ²` about a point `q ∉ γ(S¹)`. Mathlib v4.34.1 has no winding number. -/
def winding (γ : S1 → ℝ × ℝ) (q : ℝ × ℝ) (hq : ∀ z, γ z ≠ q) : ℤ := degree (windingMap γ q hq)

/-- The winding number depends only on the point `q`, not on the proof that `γ` misses it. -/
theorem winding_congr {γ : S1 → ℝ × ℝ} {q q' : ℝ × ℝ} (e : q = q') (hq : ∀ z, γ z ≠ q)
    (hq' : ∀ z, γ z ≠ q') : winding γ q hq = winding γ q' hq' := by
  subst e; rfl

/-- **`prop:winding`**, first part: a homotopy `H` from `γ₀` to `γ₁` in `ℝ² ∖ {q}` (`hH`: it never
meets `q`) does not change the winding number about `q`. The book's proof: `prop:degree` (1),
applied to the normalised homotopy `(z, t) ↦ (H(z, t) - q)/|H(z, t) - q|`. -/
theorem winding_eq_of_homotopy {γ₀ γ₁ : S1 → ℝ × ℝ} {q : ℝ × ℝ} (H : Homotopy γ₀ γ₁)
    (hH : ∀ w, H.toFun w ≠ q) (h₀ : ∀ z, γ₀ z ≠ q) (h₁ : ∀ z, γ₁ z ≠ q) :
    winding γ₀ q h₀ = winding γ₁ q h₁ := by
  -- The normalised homotopy is continuous (`continuous_nrm`, through the bridges) …
  have hHM := mathlib_continuous_of_eq S1I_toMathlib R2_toMathlib H.continuous_toFun
  have hF := continuous_nrm S1I_toMathlib (v := fun w => H.toFun w - q)
    (hHM.sub _root_.continuous_const) (fun w => sub_ne_zero.mpr (hH w))
  -- … and runs from `windingMap γ₀` to `windingMap γ₁`; so they have the same degree.
  have d := degree_eq_of_homotopic (homotopic_ends hF)
  have c0 : (fun z => nrm (H.toFun (z, 0) - q) (sub_ne_zero.mpr (hH (z, 0)))) =
      windingMap γ₀ q h₀ := by
    funext z; apply Subtype.ext; simp [windingMap, H.zero']
  have c1 : (fun z => nrm (H.toFun (z, 1) - q) (sub_ne_zero.mpr (hH (z, 1)))) =
      windingMap γ₁ q h₁ := by
    funext z; apply Subtype.ext; simp [windingMap, H.one']
  rw [c0, c1] at d
  exact d

/-- **`prop:winding`**, second part, the book's proof: moving `q` along a path `c` that avoids
`γ(S¹)` (`hcγ`) is a homotopy of the normalised maps, `(z, t) ↦ (γ(z) - c(t))/|γ(z) - c(t)|`; so
`w(γ, c(0)) = w(γ, c(1))`. -/
theorem winding_eq_of_path {γ : S1 → ℝ × ℝ} (hγ : Continuous γ) {c : I → ℝ × ℝ}
    (hc : Continuous c) (hcγ : ∀ t z, γ z ≠ c t) :
    winding γ (c 0) (fun z => hcγ 0 z) = winding γ (c 1) (fun z => hcγ 1 z) := by
  have hγM := mathlib_continuous_of_eq S1_toMathlib R2_toMathlib hγ
  have hcM := mathlib_continuous_of_eq I_toMathlib R2_toMathlib hc
  have hF := continuous_nrm S1I_toMathlib (v := fun w : S1 × I => γ w.1 - c w.2)
    ((hγM.comp _root_.continuous_fst).sub (hcM.comp _root_.continuous_snd))
    (fun w => sub_ne_zero.mpr (hcγ w.2 w.1))
  exact degree_eq_of_homotopic (homotopic_ends hF)

/-- **`prop:winding`**, second part: the winding number is constant on every path-connected set
`A` of points that `γ` misses (`hAγ`), in particular on every path component of
`ℝ² ∖ γ(S¹)`. (Lean: `a b : A` are points of `A`, and `(a : ℝ × ℝ)` is `a` in the plane.) -/
theorem winding_eq_of_pathConnected {γ : S1 → ℝ × ℝ} (hγ : Continuous γ) {A : Set (ℝ × ℝ)}
    (hA : PathConnected A) (hAγ : ∀ a ∈ A, ∀ z, γ z ≠ a) (a b : A) :
    winding γ a (hAγ a a.2) = winding γ b (hAγ b b.2) := by
  -- A path `c` in `A` from `a` to `b`, seen in the plane, avoids `γ(S¹)`.
  obtain ⟨c⟩ := hA.2 a b
  have h := winding_eq_of_path hγ (c := fun t => (c t : ℝ × ℝ))
    (continuous_subtype_val.comp c.continuous) (fun t => hAγ _ (c t).2)
  simp only [Path.source, Path.target] at h
  exact h

/-- Analysis I: the circle `S¹` is compact (closed and bounded in the plane; Mathlib's
`Metric.isCompact_of_isClosed_isBounded`). -/
theorem isCompact_S1 : IsCompact S1 := by
  apply Metric.isCompact_of_isClosed_isBounded
  · exact isClosed_eq (by fun_prop) _root_.continuous_const
  · refine (isBounded_iff_forall_norm_le).mpr ⟨1, fun v hv => ?_⟩
    have hv' : v.1 ^ 2 + v.2 ^ 2 = 1 := hv
    rw [Prod.norm_def, max_le_iff, Real.norm_eq_abs, Real.norm_eq_abs, abs_le, abs_le]
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> nlinarith [sq_nonneg v.1, sq_nonneg v.2]

/-- **`prop:winding`**, second part: `w(γ, q)` is locally constant in `q`. If `γ` misses `q`,
there is `ε > 0` such that `γ` misses every `q'` with `dist(q, q') < ε` (in Mathlib's metric on
`ℝ × ℝ`, the larger of the two coordinate distances), and `w(γ, q') = w(γ, q)`. The proof: `γ(S¹)`
is compact, hence closed (Analysis I), so a ball about `q` misses it, and the segment from `q` to
`q'` stays in that ball (`winding_eq_of_path`). -/
theorem winding_locallyConstant {γ : S1 → ℝ × ℝ} (hγ : Continuous γ) {q : ℝ × ℝ}
    (hq : ∀ z, γ z ≠ q) : ∃ ε > 0, ∀ q' : ℝ × ℝ, dist q' q < ε →
      ∃ hq' : ∀ z, γ z ≠ q', winding γ q' hq' = winding γ q hq := by
  -- Step 1. `γ(S¹)` is compact, so closed (Analysis I), and `q` is outside it: a ball
  -- `B(q, ε)` misses it.
  have hγM := mathlib_continuous_of_eq S1_toMathlib R2_toMathlib hγ
  have hK : IsCompact (range γ) := by
    have : CompactSpace S1 := isCompact_iff_compactSpace.mp isCompact_S1
    exact isCompact_range hγM
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hK.isClosed.isOpen_compl q
    (by rintro ⟨z, hz⟩; exact hq z hz)
  refine ⟨ε, hε, fun q' hq' => ?_⟩
  -- Step 2. The segment `c(t) = q + t(q' - q)` stays in the ball: `|c(t) - q| = t|q' - q| < ε`.
  set c : I → ℝ × ℝ := fun t => q + (t : ℝ) • (q' - q) with hcdef
  have hcin : ∀ t z, γ z ≠ c t := by
    intro t z hz
    have hmem : c t ∈ Metric.ball q ε := by
      rw [Metric.mem_ball, dist_eq_norm, hcdef]
      simp only [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg t.2.1]
      rw [← dist_eq_norm]
      calc (t : ℝ) * dist q' q ≤ 1 * dist q' q :=
            mul_le_mul_of_nonneg_right t.2.2 dist_nonneg
        _ < ε := by rw [one_mul]; exact hq'
    exact hball hmem ⟨z, hz⟩
  have hc : Continuous c :=
    continuous_of_mathlib_eq I_toMathlib R2_toMathlib (by simp only [hcdef]; fun_prop)
  -- Step 3. So `w(γ, q') = w(γ, c(1)) = w(γ, c(0)) = w(γ, q)` (`winding_eq_of_path`).
  have h1 : c 1 = q' := by simp [hcdef]
  have h0 : c 0 = q := by simp [hcdef]
  -- (Lean: `h1 ▸ hcin 1 z` turns `γ z ≠ c 1` into `γ z ≠ q'` using `h1 : c 1 = q'`.)
  refine ⟨fun z => h1 ▸ hcin 1 z, ?_⟩
  rw [winding_congr h1.symm _ (fun z => hcin 1 z), ← winding_eq_of_path hγ hc hcin,
    winding_congr h0]

/-- **`prop:winding`**, third part: if `|q| > |γ(z)|` for every `z` (`q` beyond `max |γ|`), then
`w(γ, q) = 0`. The book's proof: `γ(z) - q` lies in the half-plane `⟨v, q⟩ < 0`, so the normalised
map misses the point `q/|q|` of `S¹` and has degree `0` (`prop:degree` (3)). That `ℝ² ∖ γ(S¹)`
has exactly one unbounded component, and `w = 0` on all of it, is below
(`exists_unique_unbounded_component`, `winding_eq_zero_of_unbounded`). -/
theorem winding_eq_zero_of_large {γ : S1 → ℝ × ℝ} (hγ : Continuous γ) {q : ℝ × ℝ}
    (hq : ∀ z, γ z ≠ q) (hbig : ∀ z, (γ z).1 ^ 2 + (γ z).2 ^ 2 < q.1 ^ 2 + q.2 ^ 2) :
    winding γ q hq = 0 := by
  -- `q ≠ 0`, since `|q|² > |γ(1)|² ≥ 0`.
  have hq0 : q ≠ 0 := by
    intro h
    have := hbig 1
    rw [h] at this
    simp only [Prod.fst_zero, Prod.snd_zero] at this
    nlinarith [sq_nonneg (γ 1).1, sq_nonneg (γ 1).2]
  -- The normalised map is continuous (`continuous_nrm`).
  have hγM := mathlib_continuous_of_eq S1_toMathlib R2_toMathlib hγ
  have hcont : Continuous (windingMap γ q hq) :=
    continuous_nrm S1_toMathlib (v := fun z => γ z - q) (hγM.sub _root_.continuous_const)
      (fun z => sub_ne_zero.mpr (hq z))
  -- It misses `q/|q|`, and `prop:degree` (3) gives degree `0`.
  refine degree_eq_zero_of_not_mem hcont (w := nrm q hq0) (fun z hz => ?_)
  -- Suppose `v/|v| = q/|q|` for `v = γ(z) - q`. Then `v |q| = q |v|`, coordinate by coordinate …
  set v := γ z - q with hvdef
  have hNv : 0 < √(v.1 ^ 2 + v.2 ^ 2) :=
    Real.sqrt_pos.mpr (by
      simpa using Brouwer.dist_sq_pos (x := v) (y := 0) (sub_ne_zero.mpr (hq z)))
  have hNq : 0 < √(q.1 ^ 2 + q.2 ^ 2) :=
    Real.sqrt_pos.mpr (by simpa using Brouwer.dist_sq_pos hq0)
  have e1 := congrArg (fun u : S1 => u.1.1) hz
  have e2 := congrArg (fun u : S1 => u.1.2) hz
  simp only [windingMap, coe_nrm, Brouwer.dir, Prod.fst_zero, Prod.snd_zero, sub_zero,
    ← hvdef] at e1 e2
  rw [div_eq_div_iff hNv.ne' hNq.ne'] at e1 e2
  -- … so `⟨v, q⟩ |q| = |v| |q|² > 0`, and `⟨v, q⟩ > 0`.
  have hpos : 0 < (v.1 * q.1 + v.2 * q.2) * √(q.1 ^ 2 + q.2 ^ 2) := by
    have : (v.1 * q.1 + v.2 * q.2) * √(q.1 ^ 2 + q.2 ^ 2) =
        √(v.1 ^ 2 + v.2 ^ 2) * (q.1 ^ 2 + q.2 ^ 2) := by linear_combination q.1 * e1 + q.2 * e2
    rw [this]
    have : 0 < q.1 ^ 2 + q.2 ^ 2 := by simpa using Brouwer.dist_sq_pos hq0
    positivity
  have hvq : 0 < v.1 * q.1 + v.2 * q.2 := pos_of_mul_pos_left hpos hNq.le
  -- But `⟨v, q⟩ = ⟨γ(z), q⟩ - |q|² < 0`, since `2⟨γ(z), q⟩ ≤ |γ(z)|² + |q|² < 2|q|²`.
  have hv1 : v.1 = (γ z).1 - q.1 := rfl
  have hv2 : v.2 = (γ z).2 - q.2 := rfl
  rw [hv1, hv2] at hvq
  nlinarith [sq_nonneg ((γ z).1 - q.1), sq_nonneg ((γ z).2 - q.2), hbig z]

/-! ## The unbounded component (`prop:winding`, third part) -/

/-- `q` and `q'` lie in the same path component of `ℝ² ∖ γ(S¹)`: a path `c` in the plane runs from
`q` to `q'` and never meets `γ(S¹)`. -/
def JoinedOff (γ : S1 → ℝ × ℝ) (q q' : ℝ × ℝ) : Prop :=
  ∃ c : Path q q', ∀ t z, γ z ≠ c t

/-- A point off `γ(S¹)` is joined to itself, by the constant path. -/
theorem JoinedOff.refl {γ : S1 → ℝ × ℝ} {q : ℝ × ℝ} (hq : ∀ z, γ z ≠ q) : JoinedOff γ q q :=
  ⟨Path.refl q, fun _ z => hq z⟩

/-- Joined is symmetric: run the path backwards, `c̄(t) = c(1 - t)`. -/
theorem JoinedOff.symm {γ : S1 → ℝ × ℝ} {q q' : ℝ × ℝ} (h : JoinedOff γ q q') :
    JoinedOff γ q' q := by
  obtain ⟨c, hc⟩ := h
  exact ⟨c.symm, fun t z => by rw [Path.symm_apply]; exact hc _ z⟩

/-- Joined is transitive: the product `c · c'` takes only values of `c` and of `c'`. -/
theorem JoinedOff.trans {γ : S1 → ℝ × ℝ} {q q' q'' : ℝ × ℝ} (h : JoinedOff γ q q')
    (h' : JoinedOff γ q' q'') : JoinedOff γ q q'' := by
  obtain ⟨c, hc⟩ := h
  obtain ⟨c', hc'⟩ := h'
  refine ⟨c.trans c', fun t z => ?_⟩
  by_cases ht : (t : ℝ) ≤ 1 / 2
  · rw [Path.trans_apply_of_le _ _ _ ht]; exact hc _ z
  · rw [Path.trans_apply_of_ge _ _ _ (le_of_lt (not_le.mp ht))]; exact hc' _ z

/-- **`prop:winding`**, second part, for components: points `q`, `q'` in the same path component
of `ℝ² ∖ γ(S¹)` have the same winding number (`winding_eq_of_path`, along the joining path). -/
theorem winding_eq_of_joinedOff {γ : S1 → ℝ × ℝ} (hγ : Continuous γ) {q q' : ℝ × ℝ}
    (h : JoinedOff γ q q') (hq : ∀ z, γ z ≠ q) (hq' : ∀ z, γ z ≠ q') :
    winding γ q hq = winding γ q' hq' := by
  obtain ⟨c, hc⟩ := h
  have e := winding_eq_of_path hγ c.continuous hc
  rw [winding_congr c.source.symm hq (fun z => hc 0 z), e, winding_congr c.target]

/-- Analysis I: `γ(S¹)` is bounded, `‖γ(z)‖ ≤ M` for some `M ≥ 0` (a continuous image of the
compact `S¹`; Mathlib's norm on `ℝ × ℝ` is the larger of `|q₁|`, `|q₂|`). -/
theorem exists_norm_le_of_loop {γ : S1 → ℝ × ℝ} (hγ : Continuous γ) :
    ∃ M, 0 ≤ M ∧ ∀ z, ‖γ z‖ ≤ M := by
  have hγM := mathlib_continuous_of_eq S1_toMathlib R2_toMathlib hγ
  have : CompactSpace S1 := isCompact_iff_compactSpace.mp isCompact_S1
  obtain ⟨M, hM⟩ := isBounded_iff_forall_norm_le.mp (isCompact_range hγM).isBounded
  exact ⟨max M 0, le_max_right _ _, fun z => (hM _ ⟨z, rfl⟩).trans (le_max_left _ _)⟩

/-- Analysis I: for `ρ ≥ 0` the outside `{q : ‖q‖ > ρ}` of a square is path-connected ("`ℝ²` has
one end"). It is the image of `(ρ, ∞) × {u : ‖u‖ = 1}` under `(r, u) ↦ r u`, and both factors are
path-connected (Mathlib's `isPathConnected_sphere`: the unit sphere of a normed space of
dimension at least `2`). -/
theorem isPathConnected_outside {ρ : ℝ} (hρ : 0 ≤ ρ) :
    IsPathConnected {q : ℝ × ℝ | ρ < ‖q‖} := by
  have hrank : 1 < Module.rank ℝ (ℝ × ℝ) :=
    Module.one_lt_rank_of_one_lt_finrank (by simp)
  have hS := isPathConnected_sphere hrank (0 : ℝ × ℝ) zero_le_one
  have hP := ((convex_Ioi ρ).isPathConnected nonempty_Ioi).prod hS
  have e : {q : ℝ × ℝ | ρ < ‖q‖} = (fun w : ℝ × (ℝ × ℝ) => w.1 • w.2) '' (Ioi ρ ×ˢ
      Metric.sphere (0 : ℝ × ℝ) 1) := by
    ext q
    constructor
    · intro hq
      have hq0 : ‖q‖ ≠ 0 := (lt_of_le_of_lt hρ hq).ne'
      refine ⟨(‖q‖, ‖q‖⁻¹ • q), ⟨hq, ?_⟩, ?_⟩
      · simp [norm_smul, hq0]
      · simp [smul_smul, hq0]
    · rintro ⟨⟨r, u⟩, ⟨hr, hu⟩, rfl⟩
      have hr' : ρ < r := hr
      have hu' : ‖u‖ = 1 := by simpa using hu
      show ρ < ‖r • u‖
      rw [norm_smul, hu', mul_one, Real.norm_eq_abs, abs_of_pos (lt_of_le_of_lt hρ hr')]
      exact hr'
  rw [e]
  exact hP.image (by fun_prop)

/-- Two points beyond `max ‖γ‖` are joined outside `γ(S¹)`: by `isPathConnected_outside`, a path
runs between them outside the square of side `2ρ`, where `γ` never goes. -/
theorem joinedOff_of_far {γ : S1 → ℝ × ℝ} {ρ : ℝ} (hρ : 0 ≤ ρ) (hγρ : ∀ z, ‖γ z‖ ≤ ρ)
    {q q' : ℝ × ℝ} (hq : ρ < ‖q‖) (hq' : ρ < ‖q'‖) : JoinedOff γ q q' := by
  -- Mathlib gives a path `c` in the outside; it is a path of the course (the bridges).
  have hJ := (isPathConnected_outside hρ).joinedIn q hq q' hq'
  let c : Path q q' :=
    { toFun := fun t => hJ.somePath t
      continuous_toFun := continuous_of_mathlib_eq I_toMathlib R2_toMathlib
        (hJ.somePath.continuous)
      source' := hJ.somePath.source
      target' := hJ.somePath.target }
  refine ⟨c, fun t z hz => ?_⟩
  -- `c(t)` is outside the square, `γ(z)` inside.
  have h1 : ρ < ‖c t‖ := hJ.somePath_mem t
  rw [← hz] at h1
  exact absurd (hγρ z) (not_le.mpr h1)

/-- **`prop:winding`**, third part: `ℝ² ∖ γ(S¹)` has exactly one unbounded path component. There
is a point `a` whose component `{q : q joined to a}` is unbounded, and every point `b` whose
component is unbounded is joined to `a`. The book's proof ("`ℝ²` has one end"): beyond
`ρ = max ‖γ‖` the plane is path-connected (`isPathConnected_outside`) and misses `γ(S¹)`, so it
lies in one component; an unbounded component has a point beyond `ρ`, so it is that one. -/
theorem exists_unique_unbounded_component {γ : S1 → ℝ × ℝ} (hγ : Continuous γ) :
    ∃ a : ℝ × ℝ, ¬ Bornology.IsBounded {q | JoinedOff γ a q} ∧
      ∀ b : ℝ × ℝ, ¬ Bornology.IsBounded {q | JoinedOff γ b q} → JoinedOff γ b a := by
  obtain ⟨ρ, hρ, hγρ⟩ := exists_norm_le_of_loop hγ
  -- The point `a = (ρ + 1, 0)` is beyond `ρ`; so is `(R, 0)` for every `R > ρ`.
  have hfar : ∀ R, ρ < R → ρ < ‖((R, 0) : ℝ × ℝ)‖ := fun R hR => by
    rw [Prod.norm_def, norm_zero, Real.norm_eq_abs, abs_of_pos (lt_of_le_of_lt hρ hR)]
    exact lt_max_of_lt_left hR
  set a : ℝ × ℝ := (ρ + 1, 0)
  have ha : ρ < ‖a‖ := hfar _ (by linarith)
  refine ⟨a, fun hb => ?_, fun b hb => ?_⟩
  · -- `a`'s component contains every `(R, 0)` with `R > ρ`, so it is not bounded.
    obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.mp hb
    set R := max C ρ + 1
    have hR : ρ < R := by have := le_max_right C ρ; linarith
    have h := hC _ (joinedOff_of_far hρ hγρ ha (hfar R hR))
    have : ‖((R, 0) : ℝ × ℝ)‖ = R := by
      rw [Prod.norm_def, norm_zero, Real.norm_eq_abs,
        abs_of_pos (lt_of_le_of_lt hρ hR), max_eq_left (lt_of_le_of_lt hρ hR).le]
    rw [this] at h
    have := le_max_left C ρ
    linarith
  · -- `b`'s component, being unbounded, has a point `q` beyond `ρ`; and `q` is joined to `a`.
    obtain ⟨q, hbq, hq⟩ : ∃ q, JoinedOff γ b q ∧ ρ < ‖q‖ := by
      by_contra hno
      simp only [not_exists, not_and, not_lt] at hno
      exact hb (isBounded_iff_forall_norm_le.mpr ⟨ρ, fun q hq => hno q hq⟩)
    exact hbq.trans (joinedOff_of_far hρ hγρ hq ha)

/-- **`prop:winding`**, third part: `w(γ, q) = 0` on the unbounded component. If `q`'s component
is unbounded, it has a point `q'` with `‖q'‖ > 2ρ + 1`, where `ρ = max ‖γ‖`; there
`|q'| > |γ(z)|`, so `w(γ, q') = 0` (`winding_eq_zero_of_large`), and `w(γ, q) = w(γ, q')`
(`winding_eq_of_joinedOff`). -/
theorem winding_eq_zero_of_unbounded {γ : S1 → ℝ × ℝ} (hγ : Continuous γ) {q : ℝ × ℝ}
    (hq : ∀ z, γ z ≠ q) (hunb : ¬ Bornology.IsBounded {q' | JoinedOff γ q q'}) :
    winding γ q hq = 0 := by
  obtain ⟨ρ, hρ, hγρ⟩ := exists_norm_le_of_loop hγ
  -- A point `q'` of the component beyond `2ρ + 1`.
  obtain ⟨q', hqq', hq'⟩ : ∃ q', JoinedOff γ q q' ∧ 2 * ρ + 1 < ‖q'‖ := by
    by_contra hno
    simp only [not_exists, not_and, not_lt] at hno
    exact hunb (isBounded_iff_forall_norm_le.mpr ⟨2 * ρ + 1, fun q' h => hno q' h⟩)
  have hq'γ : ∀ z, γ z ≠ q' := fun z hz => by
    have := hγρ z; rw [hz] at this; linarith
  rw [winding_eq_of_joinedOff hγ hqq' hq hq'γ]
  apply winding_eq_zero_of_large hγ hq'γ
  -- `|γ(z)|² ≤ 2ρ² < (2ρ + 1)² < |q'|²`, coordinate by coordinate.
  intro z
  have h1 : |(γ z).1| ≤ ρ := (norm_fst_le (γ z)).trans (hγρ z)
  have h2 : |(γ z).2| ≤ ρ := (norm_snd_le (γ z)).trans (hγρ z)
  rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs, lt_max_iff] at hq'
  have s1 : (γ z).1 ^ 2 ≤ ρ ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h1 2
  have s2 : (γ z).2 ^ 2 ≤ ρ ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h2 2
  rcases hq' with h | h
  · have : (2 * ρ + 1) ^ 2 < q'.1 ^ 2 := by
      rw [← sq_abs q'.1]; exact pow_lt_pow_left₀ h (by linarith) two_ne_zero
    nlinarith [sq_nonneg q'.2]
  · have : (2 * ρ + 1) ^ 2 < q'.2 ^ 2 := by
      rw [← sq_abs q'.2]; exact pow_lt_pow_left₀ h (by linarith) two_ne_zero
    nlinarith [sq_nonneg q'.1]

end

end Course
