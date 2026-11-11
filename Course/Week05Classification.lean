/-
Machine-generated (Claude, Aristotle), no line written by a person. Copyleft: GPL-3.0-or-later.

# Week 5: the combinatorial half of the classification, in part

The proof of `thm:classification-I` (week 5 of the book) turns any surface presentation into
a standard one, `aa⁻¹` (the sphere), `a₁b₁a₁⁻¹b₁⁻¹ ⋯ a_gb_ga_g⁻¹b_g⁻¹` (`#_g T²`) or
`a₁a₁ ⋯ a_ka_k` (`#_k RP²`), in six steps. This file does four of them on the words: step 1
(paste two words along a shared symbol), step 2 (fold away the adjacent pairs `ee⁻¹`), step 5
(turn an interleaved quadruple `a ⋯ b ⋯ a⁻¹ ⋯ b⁻¹` into a handle `aba⁻¹b⁻¹`) and step 6 (a
product of blocks `aa` and `aba⁻¹b⁻¹` is standard, by `lem:torus-rp2`). It begins with what the
Euler characteristic says about the standard words (`prop:chi-invariant`, `prop:chi-standard`):
no two of them on the list are equivalent, except possibly `#_g T²` and `#_{2g} RP²`, which `χ`
alone cannot separate (`rem:classification-II-owed`).

Departures from the book:
* Only the word calculus: that elementary transformations do not change the realisation
  (`prop:elementary-homeo`) is not formalised here, so the statements are about equivalence of
  presentations, not homeomorphism of surfaces.
* Steps 3 (a single vertex class) and 4 (every twisted pair adjacent) are not done, and the
  steps are not yet chained into one theorem. Each step is proved in the form the book uses it:
  step 1 for one pair of words, step 5 for one quadruple, step 2 and step 6 in full.
* The book renames a symbol when it likes; here a renaming is a move (`Move.rename`), and
  renaming by any injective map is proved to be a chain of moves (`rename_inj`).
* Mathlib (v4.34.1) has no surface presentations and no classification of surfaces, so no
  declaration here has a Mathlib counterpart.

How letters, words, presentations and moves are written in Lean, and what `P ~ Q` (`Equiv P Q`)
means, is explained in the header of `Course/Week05.lean`; this file uses them as there. One more
notation: `U ++ x :: V` is the word `UxV`, and `x.inv` is `x⁻¹`.

New to Lean? Read `Course/README.md` first.
-/
import Course.Week05

namespace Course

namespace Surface

/-! ## What `χ` separates (`prop:chi-invariant`, `prop:chi-standard`) -/

/-- The sphere is not equivalent to `#_g T²`, `g ≥ 1`: `χ = 2` against `2 − 2g`. -/
theorem not_equiv_sphere_torus {g : ℕ} (hg : 1 ≤ g) : ¬ Equiv sphere [torusWord g] := by
  -- Suppose `aa⁻¹ ~ #_g T²` (`h`). Then they have the same `χ` (`prop:chi-invariant`), that is
  -- `2 = 2 − 2g` (`prop:chi-standard`), which is false for `g ≥ 1`. (Lean: `omega` does routine
  -- arithmetic with whole numbers, here `2 = 2 − 2g` and `g ≥ 1` contradict each other.)
  intro h
  have := chi_equiv h
  rw [chi_sphere, chi_torus hg] at this
  omega

/-- The sphere is not equivalent to `#_k RP²`, `k ≥ 1`: `χ = 2` against `2 − k`. -/
theorem not_equiv_sphere_cross {k : ℕ} (hk : 1 ≤ k) : ¬ Equiv sphere [crossWord k] := by
  -- Equal `χ` would give `2 = 2 − k`, false for `k ≥ 1`.
  intro h
  have := chi_equiv h
  rw [chi_sphere, chi_cross hk] at this
  omega

/-- Within the orientable family, `χ = 2 − 2g` separates: `#_g T² ~ #_{g'} T²` only if `g = g'`. -/
theorem torus_equiv_torus_iff {g g' : ℕ} (hg : 1 ≤ g) (hg' : 1 ≤ g') :
    Equiv [torusWord g] [torusWord g'] ↔ g = g' := by
  constructor
  -- If they are equivalent, `2 − 2g = 2 − 2g'`, so `g = g'`.
  · intro h
    have := chi_equiv h
    rw [chi_torus hg, chi_torus hg'] at this
    omega
  -- If `g = g'`, the two words are the same. (Lean: `rintro rfl` takes the hypothesis
  -- `g = g'` and replaces `g'` by `g` everywhere.)
  · rintro rfl; exact Equiv.refl _

/-- Within the non-orientable family, `χ = 2 − k` separates: `#_k RP² ~ #_{k'} RP²` only if
`k = k'`. -/
theorem cross_equiv_cross_iff {k k' : ℕ} (hk : 1 ≤ k) (hk' : 1 ≤ k') :
    Equiv [crossWord k] [crossWord k'] ↔ k = k' := by
  constructor
  -- If they are equivalent, `2 − k = 2 − k'`, so `k = k'`; the converse is clear.
  · intro h
    have := chi_equiv h
    rw [chi_cross hk, chi_cross hk'] at this
    omega
  · rintro rfl; exact Equiv.refl _

/-- Across the two families `χ` separates `#_g T²` from `#_k RP²` unless `k = 2g`. That case
(`χ` equal, orientability different) `χ` alone does not decide; `rem:classification-II-owed`
leaves it to week 9. -/
theorem not_equiv_torus_cross {g k : ℕ} (hg : 1 ≤ g) (hk : 1 ≤ k) (hgk : k ≠ 2 * g) :
    ¬ Equiv [torusWord g] [crossWord k] := by
  -- Equal `χ` would give `2 − 2g = 2 − k`, that is `k = 2g`, which `hgk` excludes.
  intro h
  have := chi_equiv h
  rw [chi_torus hg, chi_cross hk] at this
  omega

/-! ## Step 1 of `thm:classification-I`: pasting two words along a shared symbol -/

section Paste

variable {α : Type*} [DecidableEq α]

/-- Step 1 of `thm:classification-I`, a complementary pair in two words: rotate so that `x` ends
the first word and `x⁻¹` begins the second, and paste: `⟨UxV, U'x⁻¹V'⟩ ~ ⟨VUV'U'⟩`. The other
words `Q` are carried along. Hypotheses: `h₁`, `h₂`, the book's length conditions for the cut
that the paste undoes (`VU` and `V'U'` have at least two letters each); `h`, the symbol of `x`
occurs nowhere else. Mathlib: none. -/
theorem paste_complementary (U V U' V' : Word α) (x : Letter α) (Q : Presentation α)
    (h₁ : 2 ≤ (V ++ U).length) (h₂ : 2 ≤ (V' ++ U').length)
    (h : x.sym ∉ syms ((V ++ U ++ (V' ++ U')) :: Q)) :
    Equiv ((U ++ x :: V) :: (U' ++ x.inv :: V') :: Q) ((V ++ U ++ (V' ++ U')) :: Q) := by
  -- Rotate the first word, `UxV ~ VUx`.
  have r₁ := Equiv.rotate (U ++ [x]) V ((U' ++ x.inv :: V') :: Q)
  -- Rotate the second word, `U'x⁻¹V' ~ x⁻¹V'U'`.
  have r₂ := Equiv.second (w₁ := V ++ U ++ [x])
    (Equiv.rotate U' (x.inv :: V') ((V ++ U ++ [x]) :: Q))
  -- Paste along `x`: cutting `VUV'U'` between `VU` and `V'U'` along a new edge `x` gives
  -- `⟨VUx, x⁻¹V'U'⟩`, so pasting (the cut read backwards) goes the other way.
  have p := (Move.cut (V ++ U) (V' ++ U') x Q h₁ h₂ h).equiv_symm
  -- Write the words in one form, and chain the three steps. (Lean: `simp only […] at r₁ r₂ p ⊢`
  -- simplifies the hypotheses `r₁`, `r₂`, `p` and the goal, written `⊢`.)
  simp only [List.cons_append, List.append_assoc, List.singleton_append] at r₁ r₂ p ⊢
  exact r₁.trans (r₂.trans p)

/-- Step 1 of `thm:classification-I`, a twisted pair in two words: reflect the second word first,
then paste: `⟨UxV, U'xV'⟩ ~ ⟨VUU'⁻¹V'⁻¹⟩`. Here `U'⁻¹` is the formal inverse `Word.inv U'` of
`def:elementary`, the word read backwards with every letter inverted. Mathlib: none. -/
theorem paste_twisted (U V U' V' : Word α) (x : Letter α) (Q : Presentation α)
    (h₁ : 2 ≤ (V ++ U).length) (h₂ : 2 ≤ (V' ++ U').length)
    (h : x.sym ∉ syms ((V ++ U ++ (Word.inv U' ++ Word.inv V')) :: Q)) :
    Equiv ((U ++ x :: V) :: (U' ++ x :: V') :: Q)
      ((V ++ U ++ (Word.inv U' ++ Word.inv V')) :: Q) := by
  -- Reflect the second word: `U'xV' ~ (U'xV')⁻¹ = V'⁻¹x⁻¹U'⁻¹`. Now `x` is complementary.
  have r := Equiv.second (w₁ := U ++ x :: V)
    (Equiv.reflect (U' ++ x :: V') ((U ++ x :: V) :: Q))
  -- Paste as in `paste_complementary`, with `V'⁻¹` and `U'⁻¹` in place of `U'` and `V'`.
  have p := paste_complementary U V (Word.inv V') (Word.inv U') x Q h₁
    (by simpa [Nat.add_comm] using h₂) h
  simp only [Word.inv_append, Word.inv_cons, List.append_assoc, List.singleton_append] at r p ⊢
  exact r.trans p

end Paste

/-! ## Step 2 of `thm:classification-I`: folding adjacent complementary pairs -/

section Fold

variable {α : Type*} [DecidableEq α]

/-- In a presentation of one word `W`, the number of occurrences of `a` is the number of letters
of `W` with symbol `a`. -/
theorem occ_single (W : Word α) (a : α) : occ [W] a = W.countP (fun x => x.sym = a) := by
  simp [occ]

/-- A one-word presentation `⟨W⟩` is a surface presentation exactly when the symbol of every
letter of `W` occurs exactly twice in `W`. -/
theorem isSurface_single {W : Word α} :
    IsSurface [W] ↔ ∀ x ∈ W, W.countP (fun y => y.sym = x.sym) = 2 := by
  simp [IsSurface, occ_single]

/-- Folding an adjacent complementary pair anywhere in the first word: `Xee⁻¹Y ~ XY`, by rotating
`ee⁻¹` to the end, folding (`def:elementary`) and rotating back. Hypotheses: `h`, the book's
length condition for folding; `he`, the symbol of `e` occurs nowhere else. Mathlib: none. -/
theorem fold_inside (X Y : Word α) (e : Letter α) (Q : Presentation α)
    (h : 3 ≤ (X ++ Y).length ∨ ((X ++ Y).length = 2 ∧ Q = []))
    (he : e.sym ∉ syms ((X ++ Y) :: Q)) :
    Equiv ((X ++ e :: e.inv :: Y) :: Q) ((X ++ Y) :: Q) := by
  -- Rotate twice: `Xee⁻¹Y ~ ee⁻¹YX ~ YXee⁻¹`.
  have h₁ := Equiv.rotate X (e :: e.inv :: Y) Q
  have h₂ := Equiv.rotate [e, e.inv] (Y ++ X) Q
  -- The symbol of `e` is not in `YX` either: `YX` has the letters of `XY`.
  have he' : e.sym ∉ syms ((Y ++ X) :: Q) := by
    simp only [mem_syms, List.mem_cons, not_exists, not_and] at he ⊢
    rintro w (rfl | hw) y hy
    · exact he _ (Or.inl rfl) y (List.mem_append.2 (List.mem_append.1 hy).symm)
    · exact he w (Or.inr hw) y hy
  -- Fold: `YXee⁻¹ ~ YX`.
  have h₃ := (Move.fold (Y ++ X) e Q (by simpa [Nat.add_comm] using h) he').equiv
  -- Rotate back: `YX ~ XY`.
  have h₄ := Equiv.rotate Y X Q
  simp only [List.cons_append, List.nil_append, List.append_assoc] at h₁ h₂ h₃ ⊢
  exact h₁.trans (h₂.trans (h₃.trans h₄))

/-- In a one-word surface presentation an adjacent complementary pair `ee⁻¹` is the only
occurrence of its symbol, and removing it leaves a surface presentation. -/
theorem isSurface_of_fold {X Y : Word α} {e : Letter α}
    (h : IsSurface [X ++ e :: e.inv :: Y]) :
    (∀ y ∈ X ++ Y, y.sym ≠ e.sym) ∧ IsSurface [X ++ Y] := by
  rw [isSurface_single] at h
  -- The symbol of `e` occurs twice in `Xee⁻¹Y`, and `e`, `e⁻¹` are two occurrences; so it
  -- occurs `0` times in `X` and `0` times in `Y`.
  have he := h e (by simp)
  simp only [List.countP_append, List.countP_cons, Letter.inv_sym, decide_true, ite_true] at he
  have hX : X.countP (fun y => y.sym = e.sym) = 0 := by omega
  have hY : Y.countP (fun y => y.sym = e.sym) = 0 := by omega
  rw [List.countP_eq_zero] at hX hY
  have hne : ∀ y ∈ X ++ Y, y.sym ≠ e.sym := by
    intro y hy
    rcases List.mem_append.1 hy with hy | hy
    · simpa using hX y hy
    · simpa using hY y hy
  -- Every other symbol `x` of `XY` occurs twice in `Xee⁻¹Y`, and not as `e` or `e⁻¹`; so it
  -- occurs twice in `XY`.
  refine ⟨hne, isSurface_single.2 fun x hx => ?_⟩
  have := h x (by rcases List.mem_append.1 hx with hx | hx <;> simp [hx])
  have hxe : e.sym ≠ x.sym := (hne x hx).symm
  simpa [List.countP_append, List.countP_cons, hxe] using this

/-- A word has no adjacent complementary pair `ee⁻¹`, cyclically: none inside, and the last letter
is not the inverse of the first. -/
def NoCancel (W : Word α) : Prop :=
  (¬ ∃ X Y : Word α, ∃ e : Letter α, W = X ++ e :: e.inv :: Y) ∧
    (¬ ∃ x : Letter α, ∃ Z : Word α, W = x :: (Z ++ [x.inv]))

/-- Rearranging the letters of a one-word surface presentation (`W.Perm W'`: `W'` has the same
letters as `W`, in another order) gives a surface presentation: the counts are the same. -/
theorem isSurface_of_perm {W W' : Word α} (hp : W.Perm W') (h : IsSurface [W]) :
    IsSurface [W'] := by
  rw [isSurface_single] at h ⊢
  intro x hx
  rw [← hp.countP_eq]
  exact h x (hp.mem_iff.2 hx)

/-- Step 2 of `thm:classification-I`: in a one-word surface presentation `⟨W⟩` with at least two
letters, fold away each adjacent complementary pair `ee⁻¹` (cyclically). The result `W'` is
either `ee⁻¹` itself, the sphere, or a surface word of length at least `2` with no adjacent
complementary pair. The induction is on the length of the word. Mathlib: none. -/
theorem step2_fold (W : Word α) (hS : IsSurface [W]) (hW : 2 ≤ W.length) :
    ∃ W' : Word α, Equiv [W] [W'] ∧ IsSurface [W'] ∧
      ((∃ e : Letter α, W' = [e, e.inv]) ∨ (2 ≤ W'.length ∧ NoCancel W')) := by
  -- Strong induction on the length `n` of `W`: assume the claim for all shorter words (`ih`).
  induction hn : W.length using Nat.strong_induction_on generalizing W with
  | _ n ih =>
    -- The inner case: if `W ~ Xee⁻¹Y`, a surface word of length `n`, the claim holds for `W`.
    have inner : ∀ (X Y : Word α) (e : Letter α), (X ++ e :: e.inv :: Y).length = n →
        IsSurface [X ++ e :: e.inv :: Y] → Equiv [W] [X ++ e :: e.inv :: Y] →
        ∃ W' : Word α, Equiv [W] [W'] ∧ IsSurface [W'] ∧
          ((∃ e : Letter α, W' = [e, e.inv]) ∨ (2 ≤ W'.length ∧ NoCancel W')) := by
      intro X Y e hlen hS₀ hE₀
      -- `e` occurs only in the pair, and `XY` is again a surface word (`isSurface_of_fold`).
      obtain ⟨hne, hS₁⟩ := isSurface_of_fold hS₀
      simp only [List.length_append, List.length_cons] at hlen
      rcases Nat.lt_or_ge (X ++ Y).length 2 with hl | hl
      -- If `XY` has fewer than two letters, it is empty: one letter would be a symbol
      -- occurring once. So the word is `ee⁻¹`, the sphere, and we stop.
      · rcases List.length_eq_zero_iff.mp (show (X ++ Y).length = 0 by
          rcases Nat.lt_or_ge (X ++ Y).length 1 with h0 | h1
          · omega
          · exfalso
            obtain ⟨y, hy⟩ : ∃ y, X ++ Y = [y] :=
              List.length_eq_one_iff.mp (by omega)
            rw [isSurface_single, hy] at hS₁
            have := hS₁ y (by simp)
            simp at this) with h0
        obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.mp h0
        exact ⟨_, hE₀, hS₀, Or.inl ⟨e, rfl⟩⟩
      -- Otherwise fold: `Xee⁻¹Y ~ XY` (`fold_inside`; the length condition holds since
      -- `XY` has at least two letters and the presentation one word), and `XY` is shorter, so
      -- the induction hypothesis applies to it.
      · have hf := fold_inside X Y e [] (by
          rcases Nat.lt_or_ge (X ++ Y).length 3 with h | h
          · exact Or.inr ⟨by omega, rfl⟩
          · exact Or.inl h) (by
          intro hm
          obtain ⟨w, hw, y, hy, hye⟩ := mem_syms.1 hm
          rw [List.mem_singleton] at hw; subst hw
          exact hne y hy hye)
        obtain ⟨W', h₁, h₂, h₃⟩ :=
          ih (X ++ Y).length (by simp at hl ⊢; omega) (X ++ Y) hS₁ hl rfl
        exact ⟨W', hE₀.trans (hf.trans h₁), h₂, h₃⟩
    -- Case 1: `W = Xee⁻¹Y` has a pair inside: the inner case with `W` itself.
    by_cases hi : ∃ X Y : Word α, ∃ e : Letter α, W = X ++ e :: e.inv :: Y
    · obtain ⟨X, Y, e, rfl⟩ := hi
      exact inner X Y e hn hS (Equiv.refl _)
    -- Case 2: `W = xZx⁻¹`, a pair around the corner: rotate to `Zx⁻¹x`, which is `Zee⁻¹` with
    -- `e = x⁻¹`, a surface word (same letters as `W`), and use the inner case.
    by_cases hc : ∃ x : Letter α, ∃ Z : Word α, W = x :: (Z ++ [x.inv])
    · obtain ⟨x, Z, rfl⟩ := hc
      have hr := Equiv.rotate [x] (Z ++ [x.inv]) []
      have e₁ : Z ++ [x.inv] ++ [x] = Z ++ x.inv :: x.inv.inv :: [] := by simp
      rw [e₁] at hr
      refine inner Z [] x.inv (by rw [← hn]; simp) (isSurface_of_perm ?_ hS) (by simpa using hr)
      rw [← e₁]
      exact (List.perm_append_singleton _ _).symm
    -- Case 3: no pair at all: `W` itself will do.
    · exact ⟨W, Equiv.refl _, hS, Or.inr ⟨hW, hi, hc⟩⟩

end Fold

/-! ## Step 5 of `thm:classification-I`: complementary pairs into handles -/

section Handle

variable {α : Type*} [DecidableEq α]

/-- One cut and one paste along a complementary pair `x … x⁻¹`:
`P₁xP₂Q₁x⁻¹Q₂ ~ xP₁Q₂x⁻¹Q₁P₂`. Cut between `P₂` and `Q₁` along a new edge `e`, rotate both
pieces, paste along `x`, rename `e` as `x` and rotate. This is the move of step 5 of
`thm:classification-I`, done twice in `handle_form`. Hypotheses: `hP`, `hQ`, the words `P₁P₂`
and `Q₁Q₂` are not empty (so that the cut and the paste satisfy the book's length conditions);
`h`, the symbol of `x` occurs nowhere else. `[Infinite α]`: there are infinitely many symbols,
so a new one can be found. Mathlib: none. -/
theorem cut_paste [Infinite α] (P₁ P₂ Q₁ Q₂ : Word α) (x : Letter α) (Q : Presentation α)
    (hP : P₁ ++ P₂ ≠ []) (hQ : Q₁ ++ Q₂ ≠ [])
    (h : x.sym ∉ syms ((P₁ ++ P₂ ++ Q₁ ++ Q₂) :: Q)) :
    Equiv ((P₁ ++ x :: P₂ ++ Q₁ ++ x.inv :: Q₂) :: Q)
      ((x :: (P₁ ++ Q₂) ++ x.inv :: (Q₁ ++ P₂)) :: Q) := by
  -- The symbol of `x` occurs in none of `P₁`, `P₂`, `Q₁`, `Q₂`, `Q` (one fact for each).
  simp only [mem_syms, List.mem_cons, not_exists, not_and] at h
  have xP₁ : ∀ y ∈ P₁, y.sym ≠ x.sym := fun y hy => h _ (Or.inl rfl) y (by simp [hy])
  have xP₂ : ∀ y ∈ P₂, y.sym ≠ x.sym := fun y hy => h _ (Or.inl rfl) y (by simp [hy])
  have xQ₁ : ∀ y ∈ Q₁, y.sym ≠ x.sym := fun y hy => h _ (Or.inl rfl) y (by simp [hy])
  have xQ₂ : ∀ y ∈ Q₂, y.sym ≠ x.sym := fun y hy => h _ (Or.inl rfl) y (by simp [hy])
  have xQ : ∀ w ∈ Q, ∀ y ∈ w, y.sym ≠ x.sym := fun w hw y hy => h w (Or.inr hw) y hy
  -- Choose a new symbol `e`: not `x`'s, and not in the presentation (there are infinitely many
  -- symbols and only finitely many are used), and record that it is in none of the pieces.
  obtain ⟨e, he⟩ :=
    Infinite.exists_notMem_finset (insert x.sym (syms ((P₁ ++ P₂ ++ Q₁ ++ Q₂) :: Q)))
  simp only [Finset.mem_insert, mem_syms, List.mem_cons, List.mem_append, not_or, not_exists,
    not_and] at he
  obtain ⟨hex, he⟩ := he
  have eP₁ : ∀ y ∈ P₁, y.sym ≠ e := fun y hy => he _ (Or.inl rfl) y (by simp [hy])
  have eP₂ : ∀ y ∈ P₂, y.sym ≠ e := fun y hy => he _ (Or.inl rfl) y (by simp [hy])
  have eQ₁ : ∀ y ∈ Q₁, y.sym ≠ e := fun y hy => he _ (Or.inl rfl) y (by simp [hy])
  have eQ₂ : ∀ y ∈ Q₂, y.sym ≠ e := fun y hy => he _ (Or.inl rfl) y (by simp [hy])
  have eQ : ∀ w ∈ Q, ∀ y ∈ w, y.sym ≠ e := fun w hw y hy => he w (Or.inr hw) y hy
  -- The new edge `E` is `e`, with the direction of `x`. (Lean: `set` names an expression.)
  set E : Letter α := ⟨e, x.dir⟩ with hE
  have hEx : E.sym ≠ x.sym := hex
  -- Step 1. Cut between `P₂` and `Q₁` along `E`: `⟨P₁xP₂E, E⁻¹Q₁x⁻¹Q₂⟩`.
  have h₁ := Move.cut (P₁ ++ x :: P₂) (Q₁ ++ x.inv :: Q₂) E Q
    (by have := List.length_pos_iff.mpr hP; simp at this ⊢; omega)
    (by have := List.length_pos_iff.mpr hQ; simp at this ⊢; omega)
    (by surface_fresh)
  -- Step 2. Rotate the pieces to `P₂EP₁x` and `x⁻¹Q₂E⁻¹Q₁`.
  have h₂ := Equiv.rotate (P₁ ++ [x]) (P₂ ++ [E]) ((E.inv :: (Q₁ ++ x.inv :: Q₂)) :: Q)
  have h₃ := Equiv.second (w₁ := P₂ ++ [E] ++ (P₁ ++ [x]))
    (Equiv.rotate (E.inv :: Q₁) (x.inv :: Q₂) ((P₂ ++ [E] ++ (P₁ ++ [x])) :: Q))
  -- Step 3. Paste along `x` (the cut of `P₂EP₁ · Q₂E⁻¹Q₁` along `x`, read backwards):
  -- `P₂EP₁Q₂E⁻¹Q₁`.
  have h₄ := (Move.cut (P₂ ++ [E] ++ P₁) (Q₂ ++ E.inv :: Q₁) x Q
    (by have := List.length_pos_iff.mpr hP; simp at this ⊢; omega)
    (by have := List.length_pos_iff.mpr hQ; simp at this ⊢; omega) (by surface_fresh)).equiv_symm
  -- Step 4. Rename by the transposition of `e` and the symbol of `x` (`Move.rename`; Lean's
  -- `_root_.Equiv.swap e x.sym` is that bijection of the symbols, not the course's `Equiv` of
  -- presentations). Since `x` no longer occurs, this renames `E` as `x`: `P₂xP₁Q₂x⁻¹Q₁`.
  have h₅ := (Move.rename (_root_.Equiv.swap e x.sym)
    ((P₂ ++ [E] ++ P₁ ++ (Q₂ ++ E.inv :: Q₁)) :: Q)).equiv
  -- The transposition fixes every other symbol, since none is `e` or `x`'s.
  have hfix : ∀ y ∈ P₂ ++ P₁ ++ Q₂ ++ Q₁, _root_.Equiv.swap e x.sym y.sym = y.sym := by
    intro y hy
    simp only [List.mem_append] at hy
    have h1 : y.sym ≠ e ∧ y.sym ≠ x.sym := by
      rcases hy with ((hy | hy) | hy) | hy
      · exact ⟨eP₂ y hy, xP₂ y hy⟩
      · exact ⟨eP₁ y hy, xP₁ y hy⟩
      · exact ⟨eQ₂ y hy, xQ₂ y hy⟩
      · exact ⟨eQ₁ y hy, xQ₁ y hy⟩
    exact _root_.Equiv.swap_apply_of_ne_of_ne h1.1 h1.2
  -- So it leaves `P₁`, `P₂`, `Q₁`, `Q₂` and the other words `Q` unchanged.
  have fP₁ := map_relabel_of_fix (π := _root_.Equiv.swap e x.sym) (w := P₁)
    (fun y hy => hfix y (by simp [hy]))
  have fP₂ := map_relabel_of_fix (π := _root_.Equiv.swap e x.sym) (w := P₂)
    (fun y hy => hfix y (by simp [hy]))
  have fQ₁ := map_relabel_of_fix (π := _root_.Equiv.swap e x.sym) (w := Q₁)
    (fun y hy => hfix y (by simp [hy]))
  have fQ₂ := map_relabel_of_fix (π := _root_.Equiv.swap e x.sym) (w := Q₂)
    (fun y hy => hfix y (by simp [hy]))
  rw [relabel_cons, relabel_of_fix (fun w hw y hy =>
    _root_.Equiv.swap_apply_of_ne_of_ne (eQ w hw y hy) (xQ w hw y hy))] at h₅
  simp only [List.map_append, List.map_cons, List.map_nil, fP₁, fP₂, fQ₁, fQ₂, hE, Letter.inv,
    _root_.Equiv.swap_apply_left] at h₅
  -- Step 5. Rotate `P₂` to the end: `xP₁Q₂x⁻¹Q₁P₂`.
  have h₆ := Equiv.rotate P₂ (x :: (P₁ ++ (Q₂ ++ x.inv :: Q₁))) Q
  -- Chain the six steps.
  simp only [List.append_assoc, List.cons_append, List.singleton_append, List.nil_append,
    hE, Letter.inv] at h₁ h₂ h₃ h₄ h₅ h₆ ⊢
  exact h₁.equiv.trans (h₂.trans (h₃.trans (h₄.trans (h₅.trans h₆))))

/-- Step 5 of `thm:classification-I`, one handle: an interleaved quadruple of complementary pairs
`aBbCa⁻¹Db⁻¹E` becomes the block `aba⁻¹b⁻¹` followed by `DCBE`, by two cuts and two pastes
(`cut_paste`, first along `b`, then along `a`); the words between move as wholes, so blocks
already formed stay blocks. When `D` and `E` are empty one cut and paste along `a` and an
interchange of `b` and `b⁻¹` do it. Compare Munkres, Lemma 77.3 (three cuttings and pastings).
Hypotheses: `a` and `b` are different symbols (`hab`), and neither occurs in `B`, `C`, `D`, `E`
or the other words (`ha`, `hb`). Mathlib: none. -/
theorem handle_form [Infinite α] (a b : Letter α) (B C D E : Word α) (Q : Presentation α)
    (hab : a.sym ≠ b.sym) (ha : a.sym ∉ syms ((B ++ C ++ D ++ E) :: Q))
    (hb : b.sym ∉ syms ((B ++ C ++ D ++ E) :: Q)) :
    Equiv ((a :: B ++ b :: C ++ a.inv :: D ++ b.inv :: E) :: Q)
      ((a :: b :: a.inv :: b.inv :: (D ++ C ++ B ++ E)) :: Q) := by
  -- Unpack: `a` is not in `B`, `C`, `D`, `E`, `Q` (`aB`, …, `aQ`), and the same for `b`.
  simp only [notMem_syms_iff, List.forall_mem_cons, List.forall_mem_append] at ha hb
  obtain ⟨⟨⟨⟨aB, aC⟩, aD⟩, aE⟩, aQ⟩ := ha
  obtain ⟨⟨⟨⟨bB, bC⟩, bD⟩, bE⟩, bQ⟩ := hb
  have hba : b.sym ≠ a.sym := hab.symm
  rcases eq_or_ne (D ++ E) [] with hDE | hDE
  · -- Case `D`, `E` empty: the word is `aBbCa⁻¹b⁻¹`.
    obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.mp hDE
    -- One cut and paste along `a` (`cut_paste` with `P₁` empty, `Q₂ = b⁻¹`):
    -- `aBbCa⁻¹b⁻¹ ~ ab⁻¹a⁻¹bCB`. (If `B` is empty, take `P₂ = bC` and `Q₁` empty instead.)
    have h₁ : Equiv ((a :: B ++ b :: C ++ [a.inv, b.inv]) :: Q)
        ((a :: b.inv :: a.inv :: b :: (C ++ B)) :: Q) := by
      rcases eq_or_ne B [] with rfl | hB
      · exact (cut_paste [] (b :: C) [] [b.inv] a Q (by simp) (by simp)
          (by surface_fresh)).of_eq (by simp) (by simp)
      · exact (cut_paste [] B (b :: C) [b.inv] a Q (by simpa using hB) (by simp)
          (by surface_fresh)).of_eq (by simp) (by simp)
    -- Interchange `b` and `b⁻¹` throughout (`Move.flip`): `ab⁻¹a⁻¹bCB ~ aba⁻¹b⁻¹CB`. The other
    -- letters do not contain `b` and are unchanged.
    have h₂ := (Move.flip b.sym ((a :: b.inv :: a.inv :: b :: (C ++ B)) :: Q)).equiv
    have hf : flipSym b.sym ((a :: b.inv :: a.inv :: b :: (C ++ B)) :: Q) =
        (a :: b :: a.inv :: b.inv :: (C ++ B)) :: Q := by
      rw [flipSym_cons, flipSym_of_fix bQ]
      simp only [List.map_cons, List.map_append, map_flip_of_fix bB, map_flip_of_fix bC]
      simp [hab, Letter.inv]
    rw [hf] at h₂
    exact (h₁.trans h₂).of_eq (by simp) (by simp)
  · -- The general case.
    -- Cut and paste along `b` (`P₁ = aB`, `P₂ = Ca⁻¹`, `Q₁ = D`, `Q₂ = E`):
    -- `aBbCa⁻¹Db⁻¹E ~ baBEb⁻¹DCa⁻¹`.
    have h₁ := cut_paste (a :: B) (C ++ [a.inv]) D E b Q (by simp) hDE (by surface_fresh)
    -- Cut and paste along `a` (`P₁ = b`, `P₂ = BE`, `Q₁ = b⁻¹DC`, `Q₂` empty):
    -- `baBEb⁻¹DCa⁻¹ ~ aba⁻¹b⁻¹DCBE`.
    have h₂ := cut_paste [b] (B ++ E) (b.inv :: (D ++ C)) [] a Q (by simp) (by simp)
      (by surface_fresh)
    simp only [List.cons_append, List.append_assoc, List.nil_append, List.singleton_append,
      List.append_nil] at h₁ h₂ ⊢
    exact h₁.trans h₂

end Handle

/-! ## Relabelling by an injective map

The book renames symbols freely ("relabel", `def:elementary`). Here a move renames by a
bijection of all the symbols (`Move.rename`); this section shows that renaming the symbols of a
word by any map `f : ℕ → ℕ` that is injective on them is a chain of such moves (`rename_inj`).
The symbols are natural numbers from here on, as in the standard words. -/

/-- Rename the symbols of a word by a function: the letter `aᵈ` becomes `f(a)ᵈ`, with the same
direction. -/
def renameW (f : ℕ → ℕ) (W : Word ℕ) : Word ℕ := W.map fun x => ⟨f x.sym, x.dir⟩

/-- The symbols of a one-word presentation `⟨W⟩` are those of the letters of `W`. -/
theorem mem_syms_single {W : Word ℕ} {u : ℕ} : u ∈ syms [W] ↔ ∃ x ∈ W, x.sym = u := by
  simp [mem_syms]

/-- Renaming by `f`, then by `g`, is renaming by `g ∘ f`. -/
theorem renameW_renameW (f g : ℕ → ℕ) (W : Word ℕ) :
    renameW g (renameW f W) = renameW (g ∘ f) W := by
  simp [renameW, Function.comp_def]

/-- Two renamings that agree on the symbols of `W` give the same word. -/
theorem renameW_congr {f g : ℕ → ℕ} {W : Word ℕ} (h : ∀ x ∈ W, f x.sym = g x.sym) :
    renameW f W = renameW g W :=
  List.map_congr_left fun x hx => by rw [h x hx]

/-- A renaming that fixes every symbol of `W` leaves `W` unchanged. -/
theorem renameW_id {f : ℕ → ℕ} {W : Word ℕ} (h : ∀ x ∈ W, f x.sym = x.sym) : renameW f W = W := by
  conv_rhs => rw [← List.map_id W]
  exact List.map_congr_left fun x hx => by rw [h x hx]; rfl

/-- The symbols of the renamed word are the images `f(v)` of the symbols `v` of `W`. -/
theorem mem_syms_renameW {f : ℕ → ℕ} {W : Word ℕ} {u : ℕ} :
    u ∈ syms [renameW f W] ↔ ∃ v ∈ syms [W], f v = u := by
  simp only [mem_syms_single, renameW, List.mem_map]
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩; exact ⟨x.sym, ⟨x, hx, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩; exact ⟨_, ⟨x, hx, rfl⟩, rfl⟩

/-- Renaming one symbol `s` as a new symbol `t` (`ht`: `t` does not occur in `W`) is a
relabelling: `Move.rename` by the transposition of `s` and `t`. -/
theorem rename_one (W : Word ℕ) (s t : ℕ) (ht : t ∉ syms [W]) :
    Equiv [W] [renameW (fun u => if u = s then t else u) W] := by
  -- Relabel by the transposition `(s t)`; it remains to see that it renames `W` as claimed.
  have h := (Move.rename (_root_.Equiv.swap s t) [W]).equiv
  rw [relabel_cons] at h
  refine h.of_eq rfl ?_
  simp only [relabel, List.map_nil, List.cons.injEq, and_true]
  -- Letter by letter: `(s t)` sends `s` to `t` and fixes every other symbol of `W`, since no
  -- symbol of `W` is `t`.
  refine List.map_congr_left fun x hx => ?_
  have hxt : x.sym ≠ t := fun h' => ht (mem_syms_single.2 ⟨x, hx, h'⟩)
  rw [_root_.Equiv.swap_apply_def]
  split_ifs <;> simp_all

/-- Renaming by a map `f` that is injective on the symbols and sends each symbol to itself or to a
new symbol: one symbol at a time (`rename_one`). Hypotheses: the symbols that `f` moves lie in the
list `L`; `f` is injective on the symbols of `W`; and each symbol `u` has `f(u) = u` or `f(u)` new.
-/
theorem rename_fresh (L : List ℕ) : ∀ (W : Word ℕ) (f : ℕ → ℕ),
    (∀ u ∈ syms [W], f u ≠ u → u ∈ L) →
    (∀ u ∈ syms [W], ∀ v ∈ syms [W], f u = f v → u = v) →
    (∀ u ∈ syms [W], f u = u ∨ f u ∉ syms [W]) → Equiv [W] [renameW f W] := by
  -- Induction on the list `L` of symbols that may move.
  induction L with
  | nil =>
    -- `L` empty: `f` moves no symbol, so the renamed word is `W` itself.
    intro W f hL _ _
    rw [renameW_id (f := f) (W := W) fun x hx => by
      by_contra h
      simpa using hL _ (mem_syms_single.2 ⟨x, hx, rfl⟩) h]
  | cons s L ih =>
    intro W f hL hinj hfr
    by_cases hs : s ∈ syms [W] ∧ f s ≠ s
    · -- `f` moves the symbol `s` of `W`, to a new symbol `f(s)`. First rename `s` alone as
      -- `f(s)` (`g`, by `rename_one`); then rename the result by `f'`, which agrees with `f`
      -- except that it fixes `f(s)`. `f'` moves only symbols of `L`, so the induction
      -- hypothesis applies; and `f' ∘ g = f` on the symbols of `W`.
      obtain ⟨hsW, hfs⟩ := hs
      have hfsW : f s ∉ syms [W] := (hfr s hsW).resolve_left hfs
      set g : ℕ → ℕ := fun u => if u = s then f s else u with hg
      set f' : ℕ → ℕ := fun u => if u = f s then f s else f u with hf'
      have h₁ := rename_one W s (f s) hfsW
      -- The symbols of the renamed word: `f(s)`, and those of `W` other than `s`.
      have hW' : ∀ u, u ∈ syms [renameW g W] ↔ u = f s ∨ (u ∈ syms [W] ∧ u ≠ s) := by
        intro u
        rw [mem_syms_renameW]
        constructor
        · rintro ⟨v, hv, rfl⟩
          by_cases hvs : v = s
          · left; simp [hg, hvs]
          · right; simp only [hg, hvs, ite_false]; exact ⟨hv, hvs⟩
        · rintro (rfl | ⟨hu, hus⟩)
          · exact ⟨s, hsW, by simp [hg]⟩
          · exact ⟨u, hu, by simp [hg, hus]⟩
      have hne : ∀ u ∈ syms [W], u ≠ f s := fun u hu h => hfsW (h ▸ hu)
      -- The three hypotheses for `f'` on the renamed word, then the induction hypothesis.
      have h₂ := ih (renameW g W) f' (by
          -- `f'` moves only symbols of `L`.
          intro u hu hfu
          rcases (hW' u).1 hu with rfl | ⟨hu, hus⟩
          · simp [hf'] at hfu
          · have : f u ≠ u := by simpa [hf', hne u hu] using hfu
            rcases List.mem_cons.1 (hL u hu this) with h | h
            · exact absurd h hus
            · exact h)
        (by
          -- `f'` is injective on the new symbols, because `f` is injective on the old ones.
          intro u hu v hv huv
          rcases (hW' u).1 hu with rfl | ⟨hu, hus⟩ <;> rcases (hW' v).1 hv with rfl | ⟨hv, hvs⟩
          · rfl
          · simp only [hf', ite_true, hne v hv, ite_false] at huv
            exact absurd (hinj s hsW v hv huv) (Ne.symm hvs)
          · simp only [hf', ite_true, hne u hu, ite_false] at huv
            exact absurd (hinj u hu s hsW huv) hus
          · simp only [hf', hne u hu, hne v hv, ite_false] at huv
            exact hinj u hu v hv huv)
        (by
          -- `f'` fixes each symbol or sends it to a new one.
          intro u hu
          rcases (hW' u).1 hu with rfl | ⟨hu, hus⟩
          · left; simp [hf']
          · simp only [hf', hne u hu, ite_false]
            rcases hfr u hu with h | h
            · left; exact h
            · right
              rw [hW']
              rintro (h' | ⟨h', _⟩)
              · exact hus (hinj u hu s hsW h')
              · exact h h')
      -- Chain: `W ~ g(W) ~ f'(g(W)) = f(W)`.
      refine h₁.trans (h₂.trans (Equiv.of_eq (Equiv.refl _) rfl ?_))
      rw [renameW_renameW]
      refine congrArg (fun w => [w]) (renameW_congr fun x hx => ?_)
      by_cases hxs : x.sym = s
      · simp [hf', hg, hxs]
      · simp [hf', hg, hxs, hne x.sym (mem_syms_single.2 ⟨x, hx, rfl⟩)]
    · -- `f` does not move `s` (or `s` is not in `W`): the induction hypothesis applies to `L`.
      refine ih W f (fun u hu hfu => ?_) hinj hfr
      rcases List.mem_cons.1 (hL u hu hfu) with rfl | h
      · exact absurd ⟨hu, hfu⟩ hs
      · exact h

/-- There is a bound `M` above every symbol of `W` and every image `f(u)` of one. -/
theorem exists_bound (W : Word ℕ) (f : ℕ → ℕ) : ∃ M, ∀ x ∈ W, x.sym < M ∧ f x.sym < M := by
  -- Induction on `W`: for `yW`, add `y` and `f(y)` to the bound for `W`.
  induction W with
  | nil => exact ⟨0, by simp⟩
  | cons y W ih =>
    obtain ⟨M, hM⟩ := ih
    refine ⟨M + y.sym + f y.sym + 1, fun x hx => ?_⟩
    rcases List.mem_cons.1 hx with rfl | hx
    · omega
    · have := hM x hx; omega

/-- Relabelling by any map `f` injective on the symbols (`hinj`) is a chain of elementary
transformations: move every symbol to a new one beyond all of them, then to its target.
Mathlib: none. -/
theorem rename_inj (W : Word ℕ) (f : ℕ → ℕ)
    (hinj : ∀ u ∈ syms [W], ∀ v ∈ syms [W], f u = f v → u = v) :
    Equiv [W] [renameW f W] := by
  -- Take `M` above all the symbols `u` of `W` and their images `f(u)`.
  obtain ⟨M, hM⟩ := exists_bound W f
  have hMs : ∀ u ∈ syms [W], u < M ∧ f u < M := by
    intro u hu
    obtain ⟨x, hx, rfl⟩ := mem_syms_single.1 hu
    exact hM x hx
  -- Step 1. Move every symbol `u` to `M + u` (`rename_fresh`): injective, and each `M + u` is
  -- new, since all symbols are `< M`.
  have h₁ := rename_fresh (W.map Letter.sym) W (fun u => M + u)
    (fun u hu _ => by
      obtain ⟨x, hx, rfl⟩ := mem_syms_single.1 hu
      exact List.mem_map_of_mem hx)
    (fun u _ v _ h => by omega)
    (fun u hu => Or.inr fun h => by have := (hMs _ h).1; omega)
  -- Step 2. Move `M + u` to `f(u)`: injective because `f` is, and each `f(u) < M` is new, since
  -- the symbols are now all `≥ M`.
  have h₂ := rename_fresh ((renameW (fun u => M + u) W).map Letter.sym)
    (renameW (fun u => M + u) W) (fun v => f (v - M))
    (fun u hu _ => by
      obtain ⟨x, hx, rfl⟩ := mem_syms_single.1 hu
      exact List.mem_map_of_mem hx)
    (fun u hu v hv h => by
      obtain ⟨u', hu', rfl⟩ := mem_syms_renameW.1 hu
      obtain ⟨v', hv', rfl⟩ := mem_syms_renameW.1 hv
      simp only [Nat.add_sub_cancel_left] at h
      rw [hinj u' hu' v' hv' h])
    (fun u hu => Or.inr fun h => by
      obtain ⟨u', hu', rfl⟩ := mem_syms_renameW.1 hu
      obtain ⟨v', hv', hv⟩ := mem_syms_renameW.1 h
      simp only [Nat.add_sub_cancel_left] at hv
      have := (hMs _ hu').2
      omega)
  -- The two renamings compose to `u ↦ f((M + u) − M) = f(u)`.
  refine (h₁.trans h₂).of_eq rfl ?_
  rw [renameW_renameW]
  congr 2
  funext u
  simp

/-! ## Step 6 of `thm:classification-I`: trading handles for cross-caps -/

/-- The handle block `aba⁻¹b⁻¹` on the symbols `a = s`, `b = s + 1`. -/
def hblock (s : ℕ) : Word ℕ := [⟨s, true⟩, ⟨s + 1, true⟩, ⟨s, false⟩, ⟨s + 1, false⟩]

/-- `g` handle blocks on the symbols `s, s + 1, …, s + 2g − 1`, in order. (A definition by
recursion on `g`: none for `g = 0`; for `g + 1`, a block on `s, s + 1`, then `g` blocks from
`s + 2`.) -/
def handlesFrom : ℕ → ℕ → Word ℕ
  | _, 0 => []
  | s, g + 1 => hblock s ++ handlesFrom (s + 2) g

/-- The word `a₁a₁ ⋯ a_ka_k` followed by `g` handles on the next `2g` symbols: the words that
step 6 of `thm:classification-I` starts from, labelled in order. -/
def mixedWord (k g : ℕ) : Word ℕ := crossWord k ++ handlesFrom k g

/-- The last handle can be split off at the end: `g + 1` handles from `s` are `g` handles, then
a block on `s + 2g`, `s + 2g + 1`. -/
theorem handlesFrom_succ (s g : ℕ) :
    handlesFrom s (g + 1) = handlesFrom s g ++ hblock (s + 2 * g) := by
  -- Induction on `g`, for every starting symbol `s`.
  induction g generalizing s with
  | zero => simp [handlesFrom]
  | succ g ih =>
    rw [handlesFrom, ih (s + 2), handlesFrom]
    simp only [List.append_assoc]
    congr 3
    omega

/-- The standard orientable word is the handles from `0`. -/
theorem torusWord_eq_handlesFrom (g : ℕ) : torusWord g = handlesFrom 0 g := by
  -- Both add the `g`-th handle on `2g`, `2g + 1` at the end.
  induction g with
  | zero => rfl
  | succ g ih =>
    rw [torusWord, handlesFrom_succ, ih]
    simp [handle, hblock]

/-- The symbols of `a₁a₁ ⋯ a_ka_k` are `0, …, k − 1`. -/
theorem sym_lt_of_mem_crossWord {k : ℕ} {x : Letter ℕ} (h : x ∈ crossWord k) : x.sym < k :=
  mem_syms_cross.1 (mem_syms.2 ⟨_, List.mem_singleton_self _, x, h, rfl⟩)

/-- The symbols of `g` handles from `s` are `s, …, s + 2g − 1`. -/
theorem sym_of_mem_handlesFrom {s g : ℕ} {x : Letter ℕ} (h : x ∈ handlesFrom s g) :
    s ≤ x.sym ∧ x.sym < s + 2 * g := by
  induction g generalizing s with
  | zero => simp [handlesFrom] at h
  | succ g ih =>
    rw [handlesFrom, List.mem_append] at h
    rcases h with h | h
    · simp only [hblock, List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl | rfl | rfl <;> simp <;> omega
    · have := ih h; omega

/-- Step 6 of `thm:classification-I`: with at least one cross-cap, every handle can be traded for
two more cross-caps (`lem:torus-rp2`), so `k` cross-caps and `g` handles are `#_{k+2g} RP²`.
The book rotates a block `cc` in front of a block `aba⁻¹b⁻¹` and applies `lem:torus-rp2` with
`W` the rest of the word, until no handle remains. Mathlib: none. -/
theorem mixedWord_equiv_crossWord {k : ℕ} (g : ℕ) (hk : 1 ≤ k) :
    Equiv [mixedWord k g] [crossWord (k + 2 * g)] := by
  -- Induction on the number `g` of handles, for every `k ≥ 1`.
  induction g generalizing k with
  -- No handle: the word is already `a₁a₁ ⋯ a_ka_k`.
  | zero => simp [mixedWord, handlesFrom]; exact Equiv.refl _
  | succ g ih =>
    -- Write the number of cross-caps as `k + 1`. The word is `a₀a₀ ⋯ a_{k−1}a_{k−1} · cc ·
    -- aba⁻¹b⁻¹ · (g handles)`, with `c = k`, `a = k + 1`, `b = k + 2`; let `W` be the
    -- `g` handles followed by the first `k` cross-caps.
    obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    set W := handlesFrom (k + 3) g ++ crossWord k with hW
    -- The symbols of `W` are `< k` or `≥ k + 3`, so `k`, `k + 1`, `k + 2` are new for `W`.
    have hWs : ∀ x ∈ W, x.sym < k ∨ k + 3 ≤ x.sym := by
      intro x hx
      rw [hW, List.mem_append] at hx
      rcases hx with hx | hx
      · exact Or.inr (sym_of_mem_handlesFrom hx).1
      · exact Or.inl (sym_lt_of_mem_crossWord hx)
    have fresh : ∀ c, k ≤ c → c < k + 3 → c ∉ syms ([W] : Presentation ℕ) := by
      intro c h1 h2 hc
      obtain ⟨w, hw, x, hx, rfl⟩ := mem_syms.1 hc
      rw [List.mem_singleton] at hw
      subst hw
      rcases hWs x hx with h | h <;> omega
    -- Step 1. Rotate the cross-caps but the last to the end: `cc aba⁻¹b⁻¹ W`.
    have h₁ := Equiv.rotate (crossWord k)
      (crosscap k ++ hblock (k + 1) ++ handlesFrom (k + 3) g) []
    -- Step 2. `lem:torus-rp2`: `ccaba⁻¹b⁻¹W ~ W ccaabb`, which is `g` handles from `k + 3`
    -- followed by `k + 3` cross-caps.
    have h₂ := torus_rp2 (k + 1) (k + 2) k W [] (by omega) (by omega) (by omega)
      (fresh _ (by omega) (by omega)) (fresh _ (by omega) (by omega)) (fresh _ le_rfl (by omega))
    -- Step 3. Rotate back: `mixedWord (k + 3) g`, with one handle fewer.
    have h₃ := Equiv.rotate (handlesFrom (k + 3) g) (crossWord (k + 3)) []
    -- Step 4. By induction it is `#_{k+3+2g} RP²`, and `k + 3 + 2g = (k + 1) + 2(g + 1)`.
    have h₄ := ih (k := k + 3) (by omega)
    -- The equations `e₁`, `e₂`, `e₃` say that the words above are what was claimed.
    have e₁ : mixedWord (k + 1) (g + 1) =
        crossWord k ++ (crosscap k ++ hblock (k + 1) ++ handlesFrom (k + 3) g) := by
      simp [mixedWord, crossWord, handlesFrom, List.append_assoc]
    have e₂ : crosscap k ++ hblock (k + 1) ++ handlesFrom (k + 3) g ++ crossWord k =
        ⟨k, true⟩ :: ⟨k, true⟩ :: ⟨k + 1, true⟩ :: ⟨k + 2, true⟩ :: ⟨k + 1, false⟩ ::
          ⟨k + 2, false⟩ :: W := by
      simp [hW, crosscap, hblock]
    have e₃ : W ++ [⟨k, true⟩, ⟨k, true⟩, ⟨k + 1, true⟩, ⟨k + 1, true⟩, ⟨k + 2, true⟩,
        ⟨k + 2, true⟩] = handlesFrom (k + 3) g ++ crossWord (k + 3) := by
      simp [hW, crossWord, crosscap]
    rw [e₁]
    rw [e₂] at h₁
    rw [e₃] at h₂
    rw [show k + 1 + 2 * (g + 1) = k + 3 + 2 * g by omega]
    exact h₁.trans (h₂.trans (h₃.trans h₄))

/-- Step 6 of `thm:classification-I`, the standard form: a word of `k` blocks `aa` followed by `g`
blocks `aba⁻¹b⁻¹` is `#_g T²` if `k = 0` and `#_{k+2g} RP²` if `k ≥ 1`. Mathlib: none. -/
theorem mixedWord_standard (k g : ℕ) :
    (k = 0 ∧ [mixedWord k g] = [torusWord g]) ∨
      (1 ≤ k ∧ Equiv [mixedWord k g] [crossWord (k + 2 * g)]) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  -- `k = 0`: the word is the `g` handles from `0`, the standard word of `#_g T²`.
  · left; simp [mixedWord, crossWord, torusWord_eq_handlesFrom]
  -- `k ≥ 1`: `mixedWord_equiv_crossWord`.
  · right; exact ⟨hk, mixedWord_equiv_crossWord g hk⟩

/-! ### Step 6 for blocks in any order and with any labels

In the book, the word at step 6 is a product of blocks `aa` and `aba⁻¹b⁻¹` in any order and on
any symbols. A list of blocks (`Block`) records such a word; the proof trades handles one at a
time (`trade`) and at the end relabels the symbols in order (`equiv_std`). -/

/-- A block of the word at step 6 of `thm:classification-I`: a cross-cap `aa` or a handle
`aba⁻¹b⁻¹`. (A block `a⁻¹a⁻¹` or `a⁻¹b⁻¹ab` is one of these after interchanging `a` and `a⁻¹`,
`Move.flip`.)

Lean: an `inductive` type lists the ways to build its elements, one `|` each: a block is either
`cap a` or `hand a b`, for natural numbers `a`, `b`. -/
inductive Block
  /-- The cross-cap `aa` on the symbol `a`. -/
  | cap (a : ℕ)
  /-- The handle `aba⁻¹b⁻¹` on the symbols `a`, `b`. -/
  | hand (a b : ℕ)

namespace Block

/-- The letters of a block. (A definition by cases on the block, one line each.) -/
def word : Block → Word ℕ
  | cap a => [⟨a, true⟩, ⟨a, true⟩]
  | hand a b => [⟨a, true⟩, ⟨b, true⟩, ⟨a, false⟩, ⟨b, false⟩]

/-- The symbols of a block. -/
def syms : Block → List ℕ
  | cap a => [a]
  | hand a b => [a, b]

/-- Rename the symbols of a block. -/
def map (f : ℕ → ℕ) : Block → Block
  | cap a => cap (f a)
  | hand a b => hand (f a) (f b)

/-- Is the block a cross-cap? (`Bool`: the answer `true` or `false`.) -/
def isCap : Block → Bool
  | cap _ => true
  | hand _ _ => false

/-- Two renamings that agree on the symbols of a block rename it alike. -/
theorem map_congr {f g : ℕ → ℕ} {b : Block} (h : ∀ u ∈ b.syms, f u = g u) : b.map f = b.map g := by
  cases b <;> simp_all [syms, map]

end Block

/-- The word of a list of blocks: their letters, one block after another. -/
def blocksWord (bs : List Block) : Word ℕ := bs.flatMap Block.word

/-- The symbols of a list of blocks, in order. -/
def blockSyms (bs : List Block) : List ℕ := bs.flatMap Block.syms

/-- The number of cross-caps. -/
def ncap (bs : List Block) : ℕ := bs.countP Block.isCap

/-- The number of handles. -/
def nhand (bs : List Block) : ℕ := bs.countP fun b => !b.isCap

/-- The word of `L₁L₂` is the word of `L₁` followed by that of `L₂`. -/
theorem blocksWord_append (L₁ L₂ : List Block) :
    blocksWord (L₁ ++ L₂) = blocksWord L₁ ++ blocksWord L₂ := by
  simp [blocksWord]

/-- Renaming the blocks renames their word. -/
theorem blocksWord_map (f : ℕ → ℕ) (bs : List Block) :
    blocksWord (bs.map (Block.map f)) = renameW f (blocksWord bs) := by
  -- Induction on the list, and for the first block the two cases `cap`, `hand`.
  induction bs with
  | nil => rfl
  | cons b t ih =>
    simp only [blocksWord, List.map_cons, List.flatMap_cons] at ih ⊢
    rw [ih]
    cases b <;> simp [Block.map, Block.word, renameW]

/-- The symbols of the word of a list of blocks are the symbols of its blocks. -/
theorem mem_syms_blocksWord {bs : List Block} {u : ℕ} :
    u ∈ syms [blocksWord bs] ↔ u ∈ blockSyms bs := by
  rw [mem_syms_single]
  simp only [blocksWord, blockSyms, List.mem_flatMap]
  constructor
  -- A letter of the word lies in some block `b`; its symbol is a symbol of `b`.
  · rintro ⟨x, ⟨b, hb, hx⟩, rfl⟩
    refine ⟨b, hb, ?_⟩
    cases b with
    | cap a =>
      simp [Block.word, Block.syms] at hx ⊢
      rcases hx with rfl | rfl <;> rfl
    | hand a c =>
      simp [Block.word, Block.syms] at hx ⊢
      rcases hx with rfl | rfl | rfl | rfl <;> simp
  -- Conversely, a symbol `u` of a block is the symbol of the letter `u` of that block.
  · rintro ⟨b, hb, hu⟩
    cases b with
    | cap a =>
      simp only [Block.syms, List.mem_singleton] at hu
      exact ⟨⟨a, true⟩, ⟨_, hb, by simp [Block.word]⟩, hu.symm⟩
    | hand a c =>
      simp only [Block.syms, List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl | rfl
      · exact ⟨⟨u, true⟩, ⟨_, hb, by simp [Block.word]⟩, rfl⟩
      · exact ⟨⟨u, true⟩, ⟨_, hb, by simp [Block.word]⟩, rfl⟩

/-- The blocks relabelled with consecutive symbols from `n` on: a cross-cap takes the next
symbol, a handle the next two. -/
def std : ℕ → List Block → List Block
  | _, [] => []
  | n, Block.cap _ :: t => Block.cap n :: std (n + 1) t
  | n, Block.hand _ _ :: t => Block.hand n (n + 1) :: std (n + 2) t

/-- The position of the first occurrence of `u` in a list (counting from `0`). -/
def pos : List ℕ → ℕ → ℕ
  | [], _ => 0
  | s :: L, u => if u = s then 0 else pos L u + 1

/-- Different elements of a list have different positions. -/
theorem pos_inj {L : List ℕ} {u v : ℕ} (hu : u ∈ L) (hv : v ∈ L) (h : pos L u = pos L v) :
    u = v := by
  -- Induction on the list: if neither `u` nor `v` is the first element `s`, their positions
  -- are one more than in the rest of the list.
  induction L with
  | nil => simp at hu
  | cons s L ih =>
    by_cases hus : u = s <;> by_cases hvs : v = s
    · rw [hus, hvs]
    · simp [pos, hus, hvs] at h
    · simp [pos, hus, hvs] at h
    · simp only [pos, hus, hvs, ite_false, Nat.add_right_cancel_iff] at h
      exact ih (List.mem_of_ne_of_mem hus hu) (List.mem_of_ne_of_mem hvs hv) h

/-- If the symbols of the blocks are distinct (`hnd`; `Nodup`: no repetitions), renaming each
symbol `u` as `n` plus its position is the consecutive relabelling `std n`. -/
theorem map_pos (bs : List Block) (n : ℕ) (hnd : (blockSyms bs).Nodup) :
    bs.map (Block.map fun u => n + pos (blockSyms bs) u) = std n bs := by
  -- Induction on the list of blocks, for every `n`. For the first block, its symbols have
  -- positions `0` (and `1`); every later symbol is different from them, so its position is
  -- `1` (or `2`) more than in the rest.
  induction bs generalizing n with
  | nil => rfl
  | cons b t ih =>
    cases b with
    | cap a =>
      have hnd' : (a :: blockSyms t).Nodup := by simpa [blockSyms, Block.syms] using hnd
      rw [List.nodup_cons] at hnd'
      simp only [List.map_cons, std, Block.map]
      refine congr (congrArg _ (by simp [blockSyms, Block.syms, pos])) ?_
      rw [← ih (n + 1) hnd'.2]
      refine List.map_congr_left fun c hc => Block.map_congr fun u hu => ?_
      have hut : u ∈ blockSyms t := List.mem_flatMap.2 ⟨c, hc, hu⟩
      have hua : u ≠ a := fun h => hnd'.1 (h ▸ hut)
      simp [blockSyms, Block.syms, pos, hua]
      omega
    | hand a b =>
      have hnd' : (a :: b :: blockSyms t).Nodup := by simpa [blockSyms, Block.syms] using hnd
      simp only [List.nodup_cons, List.mem_cons, not_or] at hnd'
      simp only [List.map_cons, std, Block.map]
      have hba : b ≠ a := Ne.symm hnd'.1.1
      refine congr (congrArg _ (by simp [blockSyms, Block.syms, pos, hba])) ?_
      rw [← ih (n + 2) hnd'.2.2]
      refine List.map_congr_left fun c hc => Block.map_congr fun u hu => ?_
      have hut : u ∈ blockSyms t := List.mem_flatMap.2 ⟨c, hc, hu⟩
      have hua : u ≠ a := fun h => hnd'.1.2 (h ▸ hut)
      have hub : u ≠ b := fun h => hnd'.2.1 (h ▸ hut)
      simp [blockSyms, Block.syms, pos, hua, hub]
      omega

/-- Relabel a list of blocks with consecutive symbols from `0`: if the symbols are distinct,
the word is equivalent to that of `std 0 bs`. -/
theorem equiv_std (bs : List Block) (hnd : (blockSyms bs).Nodup) :
    Equiv [blocksWord bs] [blocksWord (std 0 bs)] := by
  -- Rename each symbol by its position (`rename_inj`, injective by `pos_inj`); by `map_pos`
  -- that is `std 0`.
  have h := rename_inj (blocksWord bs) (fun u => 0 + pos (blockSyms bs) u) (fun u hu v hv huv =>
    pos_inj (mem_syms_blocksWord.1 hu) (mem_syms_blocksWord.1 hv) (by simpa using huv))
  rwa [← blocksWord_map, map_pos bs 0 hnd] at h

/-- `k` cross-caps on the symbols `n, …, n + k − 1`, in order. -/
def capsFrom : ℕ → ℕ → Word ℕ
  | _, 0 => []
  | n, k + 1 => crosscap n ++ capsFrom (n + 1) k

/-- The last cross-cap can be split off at the end. -/
theorem capsFrom_succ (n k : ℕ) : capsFrom n (k + 1) = capsFrom n k ++ crosscap (n + k) := by
  induction k generalizing n with
  | zero => simp [capsFrom]
  | succ k ih =>
    rw [capsFrom, ih (n + 1), capsFrom]
    simp only [List.append_assoc]
    congr 3
    omega

/-- The standard non-orientable word is the cross-caps from `0`. -/
theorem crossWord_eq_capsFrom (k : ℕ) : crossWord k = capsFrom 0 k := by
  induction k with
  | zero => rfl
  | succ k ih => rw [crossWord, capsFrom_succ, ih, Nat.zero_add]

/-- If every block is a cross-cap, relabelling them in order from `n` gives `capsFrom n`. -/
theorem blocksWord_std_caps (bs : List Block) (n : ℕ) (h : ∀ b ∈ bs, b.isCap = true) :
    blocksWord (std n bs) = capsFrom n bs.length := by
  induction bs generalizing n with
  | nil => rfl
  | cons b t ih =>
    cases b with
    | cap a =>
      simp only [std, blocksWord, List.flatMap_cons, List.length_cons, capsFrom] at ih ⊢
      rw [ih (n + 1) (fun c hc => h c (List.mem_cons_of_mem _ hc))]
      rfl
    | hand a c => simp [Block.isCap] at h

/-- If every block is a handle, relabelling them in order from `n` gives `handlesFrom n`. -/
theorem blocksWord_std_hands (bs : List Block) (n : ℕ) (h : ∀ b ∈ bs, b.isCap = false) :
    blocksWord (std n bs) = handlesFrom n bs.length := by
  induction bs generalizing n with
  | nil => rfl
  | cons b t ih =>
    cases b with
    | cap a => simp [Block.isCap] at h
    | hand a c =>
      simp only [std, blocksWord, List.flatMap_cons, List.length_cons, handlesFrom] at ih ⊢
      rw [ih (n + 2) (fun c hc => h c (List.mem_cons_of_mem _ hc))]
      rfl

/-- Cyclically, some cross-cap is followed by a handle, if both occur: either the list is
`L₁ (cap c) (hand a b) L₂`, or it begins with a handle and ends with a cross-cap. -/
theorem cap_hand_or (l : List Block) (hc : ∃ c, Block.cap c ∈ l) (hh : ∃ a b, Block.hand a b ∈ l) :
    (∃ L₁ c a b L₂, l = L₁ ++ Block.cap c :: Block.hand a b :: L₂) ∨
      (∃ a b M c, l = Block.hand a b :: (M ++ [Block.cap c])) := by
  -- Induction on the list, by the kind of its first block.
  induction l with
  | nil => simp at hc
  | cons x t ih =>
    cases x with
    | cap c =>
      -- First block `cap c`. If the next block is a handle, we are done; if it is a cross-cap,
      -- use the induction hypothesis on the rest (which begins with a cross-cap, so the second
      -- alternative cannot occur there).
      obtain ⟨a, b, hab⟩ := hh
      rcases t with _ | ⟨y, t'⟩
      · simp at hab
      cases y with
      | hand a' b' => exact Or.inl ⟨[], c, a', b', t', rfl⟩
      | cap c' =>
        have hab' : Block.hand a b ∈ Block.cap c' :: t' := by simpa using hab
        rcases ih ⟨c', by simp⟩ ⟨a, b, hab'⟩ with ⟨L₁, c'', a'', b'', L₂, hL⟩ | ⟨_, _, _, _, hL⟩
        · exact Or.inl ⟨Block.cap c :: L₁, c'', a'', b'', L₂, by rw [hL]; rfl⟩
        · simp at hL
    | hand a b =>
      -- First block `hand a b`. If the rest has a handle too, use the induction hypothesis;
      -- otherwise the rest is all cross-caps, and it ends with one.
      obtain ⟨c, hc⟩ := hc
      have hct : Block.cap c ∈ t := by simpa using hc
      by_cases hh' : ∃ a b, Block.hand a b ∈ t
      · rcases ih ⟨c, hct⟩ hh' with ⟨L₁, c', a', b', L₂, hL⟩ | ⟨a', b', M, c', hL⟩
        · exact Or.inl ⟨Block.hand a b :: L₁, c', a', b', L₂, by rw [hL]; rfl⟩
        · exact Or.inr ⟨a, b, Block.hand a' b' :: M, c', by rw [hL]; rfl⟩
      · rcases List.eq_nil_or_concat t with rfl | ⟨M, y, rfl⟩
        · simp at hct
        cases y with
        | cap c' => exact Or.inr ⟨a, b, M, c', by simp⟩
        | hand a' b' => exact absurd ⟨a', b', by simp⟩ hh'

/-- Step 6 of `thm:classification-I`, one trade: if the blocks include a cross-cap and a handle,
rotate so that a block `cc` is followed by a block `aba⁻¹b⁻¹` and apply `lem:torus-rp2` with `W`
the rest of the word: one handle fewer, two cross-caps more. The new list of blocks `bs'` again
has distinct symbols. -/
theorem trade (bs : List Block) (hnd : (blockSyms bs).Nodup) (hc : ∃ c, Block.cap c ∈ bs)
    (hh : ∃ a b, Block.hand a b ∈ bs) :
    ∃ bs', Equiv [blocksWord bs] [blocksWord bs'] ∧ (blockSyms bs').Nodup ∧
      nhand bs' + 1 = nhand bs ∧ ncap bs' = ncap bs + 2 := by
  -- Split `bs = L₁L₂` so that `L₂L₁` (a rotation) begins with `cap c, hand a b`, followed by
  -- the rest `R` (`cap_hand_or`).
  obtain ⟨L₁, L₂, c, a, b, R, hbs, hrot⟩ : ∃ L₁ L₂ c a b R, bs = L₁ ++ L₂ ∧
      L₂ ++ L₁ = Block.cap c :: Block.hand a b :: R := by
    rcases cap_hand_or bs hc hh with ⟨L₁, c, a, b, L₂, hL⟩ | ⟨a, b, M, c, hL⟩
    · exact ⟨L₁, _, c, a, b, L₂ ++ L₁, hL, by simp⟩
    · exact ⟨Block.hand a b :: M, [Block.cap c], c, a, b, M, by rw [hL]; rfl, by simp⟩
  -- The symbols `c`, `a`, `b` are distinct and do not occur in `R`.
  have hperm : (L₂ ++ L₁).Perm bs := hbs ▸ List.perm_append_comm
  have hnd' : (blockSyms (L₂ ++ L₁)).Nodup :=
    (List.Perm.flatMap_right _ hperm).nodup_iff.2 hnd
  rw [hrot] at hnd'
  simp only [blockSyms, List.flatMap_cons, Block.syms, List.cons_append, List.nil_append,
    List.nodup_cons, List.mem_cons, not_or] at hnd'
  obtain ⟨⟨hca, hcb, hcR⟩, ⟨hab, haR⟩, hbR, hR⟩ := hnd'
  have fresh : ∀ s, s ∉ blockSyms R → s ∉ syms ([blocksWord R] : Presentation ℕ) :=
    fun s hs h => hs (mem_syms_blocksWord.1 h)
  -- The new blocks: `R`, then the cross-caps `cc`, `aa`, `bb`.
  refine ⟨R ++ [Block.cap c, Block.cap a, Block.cap b], ?_, ?_, ?_, ?_⟩
  -- The word: rotate `L₁L₂` to `L₂L₁ = cc aba⁻¹b⁻¹ R`, then `lem:torus-rp2` gives `R ccaabb`.
  · have h₁ := Equiv.rotate (blocksWord L₁) (blocksWord L₂) []
    rw [← blocksWord_append, ← blocksWord_append, ← hbs, hrot] at h₁
    have h₂ := torus_rp2 a b c (blocksWord R) [] hab (Ne.symm hca) (Ne.symm hcb)
      (fresh a haR) (fresh b hbR) (fresh c hcR)
    refine h₁.trans (h₂.of_eq ?_ ?_)
    · simp [blocksWord, Block.word]
    · simp [blocksWord, Block.word]
  -- The symbols of `R c a b` are distinct.
  · simp only [blockSyms, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, Block.syms,
      List.append_nil, List.singleton_append]
    rw [List.nodup_append]
    refine ⟨hR, by simp [hca, hcb, hab], ?_⟩
    intro u hu v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl <;> rintro rfl <;> simp_all [blockSyms]
  -- One handle fewer: the rotation keeps the counts, and `hand a b` is gone.
  · have := hperm.countP_eq (fun b => !b.isCap)
    rw [hrot] at this
    simp only [nhand]; rw [← this]
    simp [List.countP_append, List.countP_cons, Block.isCap]
  -- Two cross-caps more: `cap c` stays, `cap a` and `cap b` are new.
  · have := hperm.countP_eq Block.isCap
    rw [hrot] at this
    simp only [ncap]; rw [← this]
    simp [List.countP_append, List.countP_cons, Block.isCap]

/-- Step 6 of `thm:classification-I`: a word that is a product of blocks `aa` and `aba⁻¹b⁻¹`, in
any order and on distinct symbols, is `#_g T²` (`g` handles) if it has no block of the first kind,
and otherwise `#_k RP²` with `k` the number of cross-caps plus twice the number of handles. The
induction is on the number of handles; each trade is `lem:torus-rp2`. Mathlib: none. -/
theorem step6 (bs : List Block) (hnd : (blockSyms bs).Nodup) :
    (ncap bs = 0 ∧ Equiv [blocksWord bs] [torusWord (nhand bs)]) ∨
      (1 ≤ ncap bs ∧ Equiv [blocksWord bs] [crossWord (ncap bs + 2 * nhand bs)]) := by
  -- Strong induction on the number `n` of handles.
  induction hn : nhand bs using Nat.strong_induction_on generalizing bs with
  | _ n ih =>
    rcases Nat.eq_zero_or_pos (ncap bs) with h0 | hpos
    · -- No cross-cap: all blocks are handles, and relabelling them in order gives the
      -- standard word `#_g T²` (`equiv_std`).
      left
      have hall : ∀ b ∈ bs, b.isCap = false := by
        intro b hb
        have := List.countP_eq_zero.1 h0 b hb
        simpa using this
      have hlen : nhand bs = bs.length :=
        List.countP_eq_length.2 fun b hb => by simp [hall b hb]
      refine ⟨h0, ?_⟩
      rw [← hn, hlen, torusWord_eq_handlesFrom, ← blocksWord_std_hands bs 0 hall]
      exact equiv_std bs hnd
    · right
      refine ⟨hpos, ?_⟩
      rcases Nat.eq_zero_or_pos n with rfl | hnpos
      · -- No handle: all blocks are cross-caps, and relabelling them in order gives the
        -- standard word `#_k RP²`.
        have hall : ∀ b ∈ bs, b.isCap = true := by
          intro b hb
          have := List.countP_eq_zero.1 hn b hb
          simpa using this
        have hlen : ncap bs = bs.length := List.countP_eq_length.2 fun b hb => hall b hb
        rw [Nat.mul_zero, Nat.add_zero, hlen, crossWord_eq_capsFrom,
          ← blocksWord_std_caps bs 0 hall]
        exact equiv_std bs hnd
      · -- Both kinds: find a cross-cap `c` and a handle `a, b`, trade the handle for two
        -- cross-caps (`trade`), and apply the induction hypothesis to the new blocks, which
        -- have one handle fewer. The count `k + 2g` does not change: `(k + 2) + 2(g − 1)`.
        obtain ⟨c, hc⟩ : ∃ c, Block.cap c ∈ bs := by
          obtain ⟨b, hb, hb'⟩ := List.countP_pos_iff.1 hpos
          cases b with
          | cap c => exact ⟨c, hb⟩
          | hand _ _ => simp [Block.isCap] at hb'
        obtain ⟨a, b, hab⟩ : ∃ a b, Block.hand a b ∈ bs := by
          obtain ⟨x, hx, hx'⟩ := List.countP_pos_iff.1 (hn ▸ hnpos)
          cases x with
          | cap _ => simp [Block.isCap] at hx'
          | hand a b => exact ⟨a, b, hx⟩
        obtain ⟨bs', h₁, hnd', hh', hc'⟩ := trade bs hnd ⟨c, hc⟩ ⟨a, b, hab⟩
        rcases ih (nhand bs') (by omega) bs' hnd' rfl with ⟨h0', _⟩ | ⟨_, h₂⟩
        · omega
        · have e : ncap bs' + 2 * nhand bs' = ncap bs + 2 * n := by omega
          rw [e] at h₂
          exact h₁.trans h₂

end Surface

end Course
