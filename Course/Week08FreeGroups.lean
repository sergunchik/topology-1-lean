/-
Machine-generated (Claude, Aristotle), no line written by a person. Copyleft: GPL-3.0-or-later.

# Week 8: free groups and presentations

This file proves statements of week 8 of the book. `FreeGroup S` is the free group
`F(S)`, and `FreeAbelianGroup S` is by definition its abelianisation `F(S)^ab`.

* `F(S)^ab ≅ ℤ^S` for a finite set `S` (`def:free-abelian`, `abEquiv`), by the book's argument:
  the homomorphisms `F(S)^ab → ℤ^S`, `s ↦ e_s`, and `ℤ^S → F(S)^ab`, `f ↦ ∑ f(s) s`, compose
  both ways to maps that fix the generators, so to the identity, by the uniqueness half of each
  universal property.
* The rank of a free abelian group is well defined (`prop:rank`): `ℤ^m ≅ ℤ^n` implies `m = n`
  (`rank_unique`), by the book's count mod 2: an isomorphism `A ≅ B` induces `A/2A ≅ B/2B`
  (`quot_twice`), and `ℤ^m/2ℤ^m` has `2^m` elements (`card_quot_twice`).
* Free groups on finite sets of different sizes are not isomorphic (`exr-8-free-rank`, its first
  half, `free_rank`): an isomorphism `F(S) ≅ F(T)` induces `F(S)^ab ≅ F(T)^ab`, that is
  `ℤ^S ≅ ℤ^T`, so `|S| = |T|` by `prop:rank`.
* A free group is abelian only on at most one generator (`exr-8-free-rank`, its second half,
  `subsingleton_of_comm`): by the book's reduced words, `ab` and `ba` are reduced words
  (`FreeGroup.toWord`), and distinct reduced words are distinct elements
  (`prop:free-group-exists`), so `ab = ba` forces `a = b`.
* Familiar presentations (`ex:familiar-presentations`): `⟨a ∣ aⁿ⟩ ≅ ℤ/n` (`cyc_equiv`; for
  `n = 0` it is `⟨a ∣ ⟩ ≅ ℤ`, since `ZMod 0` is `ℤ`) and `⟨a, b ∣ aba⁻¹b⁻¹⟩ ≅ ℤ²` (`tor_equiv`),
  by the book's route: the map given on the generators kills the relators, so it is defined on
  the presented group; the map back exists because the generators satisfy the relations (`aⁿ = 1`;
  `a` and `b` commute); and the two compose both ways to maps fixing the generators, so to the
  identity.
* In `⟨a, b ∣ a², b²⟩` the element `ab` has infinite order (`ab_infinite_order`), by the book's
  action on `ℤ`: `a` acts by `x ↦ -x` and `b` by `x ↦ 1 - x`, both involutions, so the action is
  one of the presented group (`dihAct`); there `ab` is the translation `x ↦ x - 1` (`dihAct_ab`),
  and `(ab)ⁿ` moves `0` to `-n`.
* The ping-pong sets (`exr-8-pingpong`, its first claim, `pingpong`): for `A = [[1, 2], [0, 1]]`,
  `B = [[1, 0], [2, 1]]`, `X = {|x| > |y|}` and `Y = {|x| < |y|}`, `Aⁿ(Y) ⊆ X` and `Bⁿ(X) ⊆ Y`
  for `n ≠ 0`: `Aⁿ = [[1, 2n], [0, 1]]` (`upper_shear_pow`), and if `|x| < |y|` and `|t| ≥ 2`,
  then `|x + ty| ≥ |t||y| - |x| > |y|` (`abs_shear_expands`); `B` is the transpose. The
  exercise's deductions, down to the free subgroup of `SL(2, ℤ)`, are not formalised here.

The proofs of `card_quot_twice`, `quot_twice`, `subsingleton_of_comm`, `cyc_equiv`, `tor_equiv`
and `pingpong` (with the lemmas before each) were found by a computer program, the automated
prover Aleph Prover, and Lean checks them like every proof here. Its proof that `ab` has
infinite order went through Mathlib's `DihedralGroup 0`; it is replaced here by the book's
action on `ℤ`. The rest is assembled from them by the book's route.
Whether each Lean statement says what the book's statement says is still to be compared.
-/
import Mathlib

namespace Week08FreeGroups

/-! ## The rank of a free abelian group (`prop:rank`) -/

/-- `2A`, the subgroup of doubles of an abelian group `A`. -/
abbrev twice (A : Type*) [AddCommGroup A] : AddSubgroup A :=
  (zsmulAddGroupHom (2 : ℤ) : A →+ A).range

/-- `ℤ^m/2ℤ^m` has `2^m` elements: coordinatewise, `ℤ^m/2ℤ^m ≅ (ℤ/2)^m`, and `ℤ/2` has two
elements. -/
theorem card_quot_twice (m : ℕ) : Nat.card ((Fin m → ℤ) ⧸ twice (Fin m → ℤ)) = 2 ^ m := by
  have h : (zsmulAddGroupHom (2 : ℤ) : (Fin m → ℤ) →+ (Fin m → ℤ)) =
      nsmulAddMonoidHom 2 := by
    ext x i
    simp [zsmulAddGroupHom_apply, nsmulAddMonoidHom_apply]
  have hc : Nat.card (ℤ ⧸ (nsmulAddMonoidHom 2 : ℤ →+ ℤ).range) = 2 := by
    rw [Int.range_nsmulAddMonoidHom]
    exact (Nat.card_congr (Int.quotientZMultiplesNatEquivZMod 2).toEquiv).trans
      (by simp)
  change Nat.card ((Fin m → ℤ) ⧸
    (zsmulAddGroupHom (2 : ℤ) : (Fin m → ℤ) →+ (Fin m → ℤ)).range) = _
  rw [h, Nat.card_congr
    (QuotientAddGroup.addEquivPiModRangeNSMulAddMonoidHom (fun _ : Fin m => ℤ) 2).toEquiv]
  rw [Nat.card_fun, hc]
  simp

/-- An isomorphism `A ≅ B` induces an isomorphism `A/2A ≅ B/2B`, since it maps `2A` onto `2B`:
`e (2x) = 2 e(x)`. -/
theorem quot_twice {A B : Type*} [AddCommGroup A] [AddCommGroup B] (e : A ≃+ B) :
    Nonempty ((A ⧸ twice A) ≃+ (B ⧸ twice B)) := by
  have htwice : (twice A).map e.toAddMonoidHom = twice B := by
    ext b
    simp only [AddSubgroup.mem_map]
    constructor
    · rintro ⟨a, ha, hab⟩
      obtain ⟨x, hx⟩ := ha
      change (2 : ℤ) • x = a at hx
      refine ⟨e x, ?_⟩
      change (2 : ℤ) • e x = b
      rw [← map_zsmul, hx]
      exact hab
    · rintro ⟨y, hy⟩
      change (2 : ℤ) • y = b at hy
      refine ⟨(2 : ℤ) • e.symm y, ⟨e.symm y, rfl⟩, ?_⟩
      change e ((2 : ℤ) • e.symm y) = b
      rw [map_zsmul, e.apply_symm_apply]
      exact hy
  exact ⟨QuotientAddGroup.congr (twice A) (twice B) e htwice⟩

/-- `ℤ^m ≅ ℤ^n` implies `m = n` (`prop:rank`), by the book's count mod 2: `ℤ^m/2ℤ^m ≅ ℤ^n/2ℤ^n`,
and these have `2^m` and `2^n` elements. -/
theorem rank_unique {m n : ℕ} (e : (Fin m → ℤ) ≃+ (Fin n → ℤ)) : m = n := by
  obtain ⟨f⟩ := quot_twice e
  have h := Nat.card_congr f.toEquiv
  rw [card_quot_twice, card_quot_twice] at h
  exact Nat.pow_right_injective le_rfl h

/-! ## The free abelian group (`def:free-abelian`) -/

/-- From `F(S)^ab` to `ℤ^S`: the homomorphism the universal property gives to `s ↦ e_s`. -/
noncomputable def abToFun (S : Type*) [DecidableEq S] : FreeAbelianGroup S →+ (S → ℤ) :=
  FreeAbelianGroup.lift fun s => Pi.single s 1

/-- From `ℤ^S` to `F(S)^ab`, `f ↦ ∑ f(s) s`. -/
noncomputable def funToAb (S : Type*) [Fintype S] : (S → ℤ) →+ FreeAbelianGroup S where
  toFun f := ∑ s, f s • FreeAbelianGroup.of s
  map_zero' := by simp
  map_add' f g := by simp [add_smul, Finset.sum_add_distrib]

/-- `F(S)^ab ≅ ℤ^S` for a finite set `S` (`def:free-abelian`), by the book's argument: both
composites fix the generators, so they are the identity by the uniqueness half of each universal
property. -/
noncomputable def abEquiv (S : Type*) [Fintype S] [DecidableEq S] :
    FreeAbelianGroup S ≃+ (S → ℤ) :=
  AddMonoidHom.toAddEquiv (abToFun S) (funToAb S)
    (FreeAbelianGroup.lift_ext _ _ fun t => by
      simp [abToFun, funToAb, Pi.single_apply])
    (AddMonoidHom.functions_ext _ _ _ fun t x => by
      ext s; by_cases h : s = t <;> simp [abToFun, funToAb, Pi.single_apply, h])

/-! ## Free groups of different ranks (`exr-8-free-rank`) -/

/-- `F(S) ≅ F(T)` only if `|S| = |T|` (`exr-8-free-rank`, first half), by the book's route: the
isomorphism induces `F(S)^ab ≅ F(T)^ab`, that is `ℤ^S ≅ ℤ^T`, and `prop:rank` applies. -/
theorem free_rank {S T : Type*} [Fintype S] [Fintype T] (e : FreeGroup S ≃* FreeGroup T) :
    Fintype.card S = Fintype.card T := by
  classical
  have a : FreeAbelianGroup S ≃+ FreeAbelianGroup T :=
    MulEquiv.toAdditive (MulEquiv.abelianizationCongr e)
  exact rank_unique
    (((LinearEquiv.funCongrLeft ℤ ℤ (Fintype.equivFin S)).toAddEquiv.trans (abEquiv S).symm).trans
      (a.trans ((abEquiv T).trans (LinearEquiv.funCongrLeft ℤ ℤ (Fintype.equivFin T)).symm.toAddEquiv)))

/-- `F(S)` is abelian only if `S` has at most one element (`exr-8-free-rank`, second half): the
reduced words of `ab` and `ba` are `ab` and `ba`, so `ab = ba` forces `a = b`. -/
theorem subsingleton_of_comm {S : Type*} (h : ∀ x y : FreeGroup S, x * y = y * x) :
    Subsingleton S := by
  classical
  constructor
  intro a b
  have hab := congrArg FreeGroup.toWord (h (FreeGroup.of a) (FreeGroup.of b))
  simp only [FreeGroup.toWord_mul, FreeGroup.toWord_of, List.singleton_append,
    FreeGroup.reduce.cons, FreeGroup.reduce_nil, Bool.not_true,
    Bool.true_eq_false, and_false, ite_false, List.cons.injEq, Prod.mk.injEq,
    and_true] at hab
  exact hab.1

/-! ## Familiar presentations (`ex:familiar-presentations`) -/

namespace Presentations

/-- `⟨a ∣ aⁿ⟩`: one generator `a = of ()`, one relator `aⁿ`; for `n = 0` it is `⟨a ∣ ⟩`. -/
abbrev Cyc (n : ℕ) := PresentedGroup ({FreeGroup.of () ^ n} : Set (FreeGroup Unit))

/-- `a ↦ 1` kills `aⁿ`, so it defines `⟨a ∣ aⁿ⟩ → ℤ/n`. -/
theorem cyc_to_zmod (n : ℕ) :
    ∃ f : Cyc n →* Multiplicative (ZMod n), f (PresentedGroup.of ()) = Multiplicative.ofAdd 1 := by
  let f : Cyc n →* Multiplicative (ZMod n) := PresentedGroup.toGroup
    (f := fun _ : Unit => Multiplicative.ofAdd (1 : ZMod n)) (by
      intro r hr
      obtain rfl : r = FreeGroup.of () ^ n := Set.mem_singleton_iff.mp hr
      simp only [map_pow, FreeGroup.lift_apply_of]
      apply Multiplicative.toAdd.injective
      change n • (1 : ZMod n) = 0
      simp)
  exact ⟨f, PresentedGroup.toGroup.of _⟩

/-- `aⁿ = 1` in `⟨a ∣ aⁿ⟩`. -/
theorem of_pow (n : ℕ) : (PresentedGroup.of () : Cyc n) ^ n = 1 := by
  simpa only [map_pow, PresentedGroup.of] using
    (PresentedGroup.one_of_mem (rels := ({FreeGroup.of () ^ n} : Set (FreeGroup Unit)))
      (Set.mem_singleton (FreeGroup.of () ^ n)))

/-- If `gⁿ = 1`, then `k ↦ gᵏ` is a well-defined homomorphism `ℤ/n → G`. -/
theorem zmod_lift (n : ℕ) {G : Type*} [Group G] (g : G) (hg : g ^ n = 1) :
    ∃ h : Multiplicative (ZMod n) →* G, h (Multiplicative.ofAdd 1) = g := by
  let F : ℤ →+ Additive G := zmultiplesHom (Additive G) (Additive.ofMul g)
  have hF : F (n : ℤ) = 0 := by
    change (n : ℤ) • Additive.ofMul g = 0
    rw [natCast_zsmul]
    exact congrArg Additive.ofMul hg
  let H : ZMod n →+ Additive G := ZMod.lift n ⟨F, hF⟩
  refine ⟨H.toMultiplicativeLeft, ?_⟩
  have hH := ZMod.lift_coe n ⟨F, hF⟩ (1 : ℤ)
  change H (1 : ZMod n) = Additive.ofMul g
  simpa only [H, F, Int.cast_one, zmultiplesHom_apply, one_zsmul] using hH

/-- `⟨a ∣ aⁿ⟩ ≅ ℤ/n`, `a ↦ 1` (`ex:familiar-presentations`): the maps `a ↦ 1` and `k ↦ aᵏ`
compose both ways to maps fixing the generators, so to the identity. -/
theorem cyc_equiv (n : ℕ) :
    ∃ e : Cyc n ≃* Multiplicative (ZMod n), e (PresentedGroup.of ()) = Multiplicative.ofAdd 1 := by
  obtain ⟨f, hf⟩ := cyc_to_zmod n
  obtain ⟨g, hg⟩ := zmod_lift n (PresentedGroup.of () : Cyc n) (of_pow n)
  have hleft : g.comp f = MonoidHom.id (Cyc n) := by
    apply PresentedGroup.ext
    intro u
    cases u
    simp only [MonoidHom.comp_apply, MonoidHom.id_apply, hf, hg]
  have hright : f.comp g = MonoidHom.id (Multiplicative (ZMod n)) := by
    apply MonoidHom.ext
    intro x
    obtain ⟨k, hk⟩ := ZMod.intCast_surjective x.toAdd
    have hx : x = Multiplicative.ofAdd (k : ZMod n) := by
      change x.toAdd = (k : ZMod n)
      exact hk.symm
    rw [hx]
    have hkpow : Multiplicative.ofAdd (k : ZMod n) = (Multiplicative.ofAdd (1 : ZMod n)) ^ k := by
      rw [← ofAdd_zsmul]
      simp only [zsmul_eq_mul, mul_one]
    simp only [MonoidHom.comp_apply, MonoidHom.id_apply, hkpow, map_zpow, hg, hf]
  exact ⟨MonoidHom.toMulEquiv f g hleft hright, hf⟩

/-- `⟨a, b ∣ aba⁻¹b⁻¹⟩`, with `a = of 0` and `b = of 1`. -/
abbrev Tor := PresentedGroup
  ({FreeGroup.of 0 * FreeGroup.of 1 * (FreeGroup.of 0)⁻¹ * (FreeGroup.of 1)⁻¹} :
    Set (FreeGroup (Fin 2)))

/-- `a ↦ (1,0)`, `b ↦ (0,1)` kills `aba⁻¹b⁻¹`, since `ℤ²` is abelian. -/
theorem tor_to_prod : ∃ f : Tor →* Multiplicative (ℤ × ℤ),
    f (PresentedGroup.of 0) = Multiplicative.ofAdd (1, 0) ∧
    f (PresentedGroup.of 1) = Multiplicative.ofAdd (0, 1) := by
  let c : Fin 2 → Multiplicative (ℤ × ℤ) := fun i =>
    if i = 0 then Multiplicative.ofAdd (1, 0) else Multiplicative.ofAdd (0, 1)
  have h : ∀ r ∈ ({FreeGroup.of 0 * FreeGroup.of 1 *
      (FreeGroup.of 0)⁻¹ * (FreeGroup.of 1)⁻¹} : Set (FreeGroup (Fin 2))),
      FreeGroup.lift c r = 1 := by
    intro r hr
    rcases Set.mem_singleton_iff.mp hr with rfl
    simp only [map_mul, map_inv, FreeGroup.lift_apply_of]
    simp [mul_assoc]
  refine ⟨PresentedGroup.toGroup h, ?_, ?_⟩ <;> simp [PresentedGroup.toGroup.of, c]

/-- `a` and `b` commute in `⟨a, b ∣ aba⁻¹b⁻¹⟩`. -/
theorem tor_commute :
    Commute (PresentedGroup.of (0 : Fin 2) : Tor) (PresentedGroup.of (1 : Fin 2) : Tor) := by
  have h := PresentedGroup.one_of_mem
    (rels := {FreeGroup.of (0 : Fin 2) * FreeGroup.of 1 *
      (FreeGroup.of 0)⁻¹ * (FreeGroup.of 1)⁻¹})
    (Set.mem_singleton _)
  change (PresentedGroup.of (0 : Fin 2) : Tor) * PresentedGroup.of 1 =
    PresentedGroup.of 1 * PresentedGroup.of 0
  have hc : (PresentedGroup.of (0 : Fin 2) : Tor) * PresentedGroup.of 1 *
      (PresentedGroup.of 0)⁻¹ * (PresentedGroup.of 1)⁻¹ = 1 := by
    simpa only [map_mul, map_inv, PresentedGroup.of] using h
  calc
    _ = ((PresentedGroup.of (0 : Fin 2) : Tor) * PresentedGroup.of 1 *
        (PresentedGroup.of 0)⁻¹ * (PresentedGroup.of 1)⁻¹) *
        (PresentedGroup.of 1 * PresentedGroup.of 0) := by simp [mul_assoc]
    _ = _ := by rw [hc, one_mul]

/-- `(m, n) ↦ aᵐbⁿ` is a homomorphism `ℤ² → ⟨a, b ∣ aba⁻¹b⁻¹⟩`, since `a` and `b` commute. -/
theorem prod_to_tor : ∃ g : Multiplicative (ℤ × ℤ) →* Tor, ∀ z : Multiplicative (ℤ × ℤ),
    g z = (PresentedGroup.of 0 : Tor) ^ z.toAdd.1 * (PresentedGroup.of 1 : Tor) ^ z.toAdd.2 := by
  refine ⟨{
    toFun := fun z => (PresentedGroup.of 0 : Tor) ^ z.toAdd.1 *
      (PresentedGroup.of 1 : Tor) ^ z.toAdd.2
    map_one' := by simp
    map_mul' := by
      intro x y
      change (PresentedGroup.of 0 : Tor) ^ (x.toAdd.1 + y.toAdd.1) *
          (PresentedGroup.of 1 : Tor) ^ (x.toAdd.2 + y.toAdd.2) =
        ((PresentedGroup.of 0 : Tor) ^ x.toAdd.1 * (PresentedGroup.of 1 : Tor) ^ x.toAdd.2) *
          ((PresentedGroup.of 0 : Tor) ^ y.toAdd.1 * (PresentedGroup.of 1 : Tor) ^ y.toAdd.2)
      rw [zpow_add, zpow_add]
      have h := (tor_commute.symm.zpow_zpow x.toAdd.2 y.toAdd.1).eq
      simp only [mul_assoc]
      rw [← mul_assoc ((PresentedGroup.of 0 : Tor) ^ y.toAdd.1), ← h]
      simp only [mul_assoc] }, fun z => rfl⟩

/-- `⟨a, b ∣ aba⁻¹b⁻¹⟩ ≅ ℤ²`, `a ↦ (1,0)`, `b ↦ (0,1)` (`ex:familiar-presentations`): the two
maps above compose both ways to maps fixing the generators, so to the identity. -/
theorem tor_equiv : ∃ e : Tor ≃* Multiplicative (ℤ × ℤ),
    e (PresentedGroup.of 0) = Multiplicative.ofAdd (1, 0) ∧
    e (PresentedGroup.of 1) = Multiplicative.ofAdd (0, 1) := by
  obtain ⟨f, hf0, hf1⟩ := tor_to_prod
  obtain ⟨g, hg⟩ := prod_to_tor
  have hleft : g.comp f = MonoidHom.id Tor := by
    apply PresentedGroup.ext
    intro i
    fin_cases i <;> simp [MonoidHom.comp_apply, hf0, hf1, hg]
  have hright : f.comp g = MonoidHom.id (Multiplicative (ℤ × ℤ)) := by
    apply MonoidHom.ext
    intro z
    rw [MonoidHom.comp_apply, hg, map_mul, map_zpow, map_zpow, hf0, hf1]
    change Multiplicative.ofAdd (1, 0) ^ z.toAdd.1 * Multiplicative.ofAdd (0, 1) ^ z.toAdd.2 = z
    apply Multiplicative.toAdd.injective
    ext <;> simp
  exact ⟨MonoidHom.toMulEquiv f g hleft hright, hf0, hf1⟩

/-- `⟨a, b ∣ a², b²⟩`, with `a = of 0` and `b = of 1`: the infinite dihedral group. -/
abbrev Dih := PresentedGroup ({FreeGroup.of 0 ^ 2, FreeGroup.of 1 ^ 2} : Set (FreeGroup (Fin 2)))

/-- The book's action on `ℤ`: `a` acts by `x ↦ -x`, `b` by `x ↦ 1 - x`. -/
def act : Fin 2 → Equiv.Perm ℤ := ![Equiv.neg ℤ, Equiv.subLeft 1]

/-- Both reflections are involutions, so the action is one of `⟨a, b ∣ a², b²⟩`. -/
noncomputable def dihAct : Dih →* Equiv.Perm ℤ :=
  PresentedGroup.toGroup (f := act) (by
    intro r hr
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hr
    rcases hr with rfl | rfl <;> ext x <;> simp [act, pow_two])

/-- `ab` acts as the translation `x ↦ x - 1`. -/
theorem dihAct_ab : dihAct (PresentedGroup.of 0 * PresentedGroup.of 1) = Equiv.addRight (-1) := by
  ext x
  simp [dihAct, act, PresentedGroup.toGroup.of]
  ring

/-- The translation `x ↦ x - 1`, applied `n` times, is `x ↦ x - n`. -/
theorem translate_zpow (n : ℤ) : ∀ x : ℤ, ((Equiv.addRight (-1 : ℤ)) ^ n) x = x - n := by
  refine Int.induction_on n ?_ ?_ ?_
  · intro x; simp
  · intro k ih x
    rw [zpow_add_one, Equiv.Perm.mul_apply, ih]
    simp only [Equiv.coe_addRight]
    ring
  · intro k ih x
    rw [zpow_sub_one, Equiv.Perm.mul_apply, ih]
    simp [Equiv.Perm.inv_def]
    ring

/-- In `⟨a, b ∣ a², b²⟩` the element `ab` has infinite order (`ex:familiar-presentations`), by the
book's route: in the action on `ℤ` it is the translation `x ↦ x - 1`, so `(ab)ⁿ` moves `0` to `-n`. -/
theorem ab_infinite_order (n : ℤ) (hn : n ≠ 0) :
    (PresentedGroup.of 0 * PresentedGroup.of 1 : Dih) ^ n ≠ 1 := by
  intro h
  have h0 := congrArg (fun g => dihAct g 0) h
  simp only [map_zpow, dihAct_ab, map_one, translate_zpow, Equiv.Perm.one_apply] at h0
  apply hn
  linarith

end Presentations

/-! ## The ping-pong sets (`exr-8-pingpong`, its first claim) -/

namespace PingPong

/-- `X = {(x, y) : |x| > |y|}`. -/
def X : Set (Fin 2 → ℝ) := {v | |v 1| < |v 0|}

/-- `Y = {(x, y) : |x| < |y|}`. -/
def Y : Set (Fin 2 → ℝ) := {v | |v 0| < |v 1|}

open Matrix

/-- If `|x| < |y|` and `|t| ≥ 2`, then `|x + ty| > |y|`, since
`|x + ty| ≥ |t||y| - |x| ≥ 2|y| - |x| > |y|`. -/
theorem abs_shear_expands (x y t : ℝ) (hxy : |x| < |y|) (ht : 2 ≤ |t|) :
    |y| < |x + t * y| := by
  have hrev := abs_sub_abs_le_abs_add (t * y) x
  rw [abs_mul, add_comm (t * y) x] at hrev
  have hmul := mul_le_mul_of_nonneg_right ht (abs_nonneg y)
  linarith

/-- `[[1, a], [0, 1]]ⁿ = [[1, na], [0, 1]]`, by induction on `n`. -/
theorem upper_shear_pow (a : ℝ) (n : ℕ) :
    (!![1, a; 0, 1] ^ n : Matrix (Fin 2) (Fin 2) ℝ) =
      !![1, (n : ℝ) * a; 0, 1] := by
  induction n with
  | zero =>
      ext i j
      fin_cases i <;> fin_cases j <;> simp
  | succ n ih =>
      rw [pow_succ, ih, Matrix.mul_fin_two]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Nat.cast_add, Nat.cast_one]
      ring

/-- `[[1, 0], [a, 1]]ⁿ = [[1, 0], [na, 1]]`: transpose the last. -/
theorem lower_shear_pow (a : ℝ) (n : ℕ) :
    (!![1, 0; a, 1] ^ n : Matrix (Fin 2) (Fin 2) ℝ) =
      !![1, 0; (n : ℝ) * a, 1] := by
  have ht (b : ℝ) : ( (!![1, b; 0, 1] : Matrix (Fin 2) (Fin 2) ℝ))ᵀ =
      !![1, 0; b, 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have h := congrArg Matrix.transpose (upper_shear_pow a n)
  simpa only [Matrix.transpose_pow, ht] using h

/-- `Aⁿ(Y) ⊆ X` and `Bⁿ(X) ⊆ Y` for every `n ≠ 0` (`exr-8-pingpong`, its first claim), for
`A = [[1, 2], [0, 1]]` and `B = [[1, 0], [2, 1]]`, stated for the powers `n ≥ 1` of `A`, `A⁻¹`,
`B` and `B⁻¹`: `Aⁿ` sends `(x, y)` to `(x + 2ny, y)`, and if `|x| < |y|`, then `|x + 2ny| > |y|`;
the same for `B` with the coordinates exchanged. -/
theorem pingpong (n : ℕ) (hn : 1 ≤ n) :
    (∀ v ∈ Y, (!![1, 2; 0, 1] ^ n : Matrix (Fin 2) (Fin 2) ℝ) *ᵥ v ∈ X) ∧
    (∀ v ∈ Y, (!![1, -2; 0, 1] ^ n : Matrix (Fin 2) (Fin 2) ℝ) *ᵥ v ∈ X) ∧
    (∀ v ∈ X, (!![1, 0; 2, 1] ^ n : Matrix (Fin 2) (Fin 2) ℝ) *ᵥ v ∈ Y) ∧
    (∀ v ∈ X, (!![1, 0; -2, 1] ^ n : Matrix (Fin 2) (Fin 2) ℝ) *ᵥ v ∈ Y) := by
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hplus : 2 ≤ |(n : ℝ) * 2| := by
    rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg n)]
    norm_num
    linarith
  have hminus : 2 ≤ |(n : ℝ) * (-2)| := by
    rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg n)]
    norm_num
    linarith
  dsimp [X, Y]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro v hv
    rw [upper_shear_pow]
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using
      (abs_shear_expands (v 0) (v 1) ((n : ℝ) * 2) hv hplus)
  · intro v hv
    rw [upper_shear_pow]
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using
      (abs_shear_expands (v 0) (v 1) ((n : ℝ) * (-2)) hv hminus)
  · intro v hv
    rw [lower_shear_pow]
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two, add_comm] using
      (abs_shear_expands (v 1) (v 0) ((n : ℝ) * 2) hv hplus)
  · intro v hv
    rw [lower_shear_pow]
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two, add_comm] using
      (abs_shear_expands (v 1) (v 0) ((n : ℝ) * (-2)) hv hminus)

end PingPong

end Week08FreeGroups
