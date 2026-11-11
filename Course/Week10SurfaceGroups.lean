/-
Machine-generated (Claude, Aristotle), no line written by a person. Copyleft: GPL-3.0-or-later.

# Week 10: the abelianised group of a closed surface

This file proves a statement of week 10 of the book, both halves.

* `π₁(#_g T²)^ab ≅ ℤ^{2g}` (`cor:surface-abelian`, its first half, `surface_ab`), for the group
  `⟨a₁, b₁, …, a_g, b_g ∣ [a₁, b₁] ⋯ [a_g, b_g]⟩` that `thm:surface-groups` gives as
  `π₁(#_g T²)`, by the book's route: a homomorphism from a presented group to an abelian group is
  a map on the generators that kills each relator read additively, and a product of commutators
  reads as `0`. So the abelianised presented group is the abelianised free group
  (`ab_map_surjective`, `presented_ab_injective`, `relator_map_eq_one`), which is `ℤ^{2g}` by
  week 8 (`def:free-abelian`, `Week08FreeGroups.abEquiv`). That `π₁(#_g T²)` has this
  presentation (`thm:surface-groups`) is not formalised here.
* `π₁(#_k ℝP²)^ab ≅ ℤ^{k-1} ⊕ ℤ/2` (`cor:surface-abelian`, its second half, `Crosscap.crosscap_ab`),
  for `k + 1` projective planes, with group `⟨a₁, …, a_{k+1} ∣ a₁² ⋯ a_{k+1}²⟩`, by the same kind of
  route: maps out of the abelianised presented group are the maps on the generators with
  `2 (f a₁ + ⋯ + f a_{k+1}) = 0` (`crosscap_lift`), which are also the maps out of the model
  `ℤ^k ⊕ ℤ/2` (`crosscap_model_lift`), so the two are isomorphic. The two halves are now proved.

The proofs of both halves were found by computer programs (automated provers; the first half by
Aleph Prover), and Lean checks them like every proof here. The last step of the first half uses
week 8's `abEquiv` in place of Mathlib's `FreeAbelianGroup.equivFinsupp`. AI models compared the
Lean statement of the first half with the book's and found that it says the same (9 November 2026).
-/
import Course.Week08FreeGroups

namespace Week10SurfaceGroups

/-- `[a₁, b₁] ⋯ [a_g, b_g]` in the free group on `a₁, …, a_g, b₁, …, b_g`, where
`aᵢ = of (inl i)`, `bᵢ = of (inr i)` and `[a, b] = a b a⁻¹ b⁻¹`. -/
def relator (g : ℕ) : FreeGroup (Fin g ⊕ Fin g) :=
  (List.ofFn fun i : Fin g =>
    FreeGroup.of (Sum.inl i) * FreeGroup.of (Sum.inr i) * (FreeGroup.of (Sum.inl i))⁻¹ *
      (FreeGroup.of (Sum.inr i))⁻¹).prod

/-- A surjective homomorphism induces a surjective one on abelianisations. -/
theorem ab_map_surjective {G H : Type*} [Group G] [Group H] (f : G →* H) (hf : Function.Surjective f) : Function.Surjective (Abelianization.map f) := by
  intro x
  induction x using QuotientGroup.induction_on with
  | H h =>
    obtain ⟨g, rfl⟩ := hf h
    exact ⟨Abelianization.of g, Abelianization.map_of f g⟩

/-- If every relator dies in `F(S)^ab`, the map `F(S)^ab → ⟨S ∣ R⟩^ab` is injective: the map
back, from `⟨S ∣ R⟩` to `F(S)^ab`, exists because the relators die there, and the composite fixes
the generators. -/
theorem presented_ab_injective {α : Type*} (rels : Set (FreeGroup α)) (h : ∀ r ∈ rels, (Abelianization.of r : Abelianization (FreeGroup α)) = 1) : Function.Injective (Abelianization.map (PresentedGroup.mk rels)) := by
  let p : FreeGroup α →* Abelianization (FreeGroup α) := Abelianization.of
  have hker : Subgroup.normalClosure rels ≤ p.ker := by
    apply Subgroup.normalClosure_le_normal
    intro r hr
    exact MonoidHom.mem_ker.mpr (h r hr)
  let b : PresentedGroup rels →* Abelianization (FreeGroup α) :=
    QuotientGroup.lift _ p (fun x hx => MonoidHom.mem_ker.mp (hker hx))
  let r : Abelianization (PresentedGroup rels) →* Abelianization (FreeGroup α) :=
    Abelianization.lift b
  have hr : r.comp (Abelianization.map (PresentedGroup.mk rels)) = MonoidHom.id _ := by
    apply Abelianization.hom_ext
    apply MonoidHom.ext
    intro x
    rfl
  intro x y hxy
  have hxy' := congrArg r hxy
  change (r.comp (Abelianization.map (PresentedGroup.mk rels))) x =
    (r.comp (Abelianization.map (PresentedGroup.mk rels))) y at hxy'
  simpa only [hr, MonoidHom.id_apply] using hxy'

/-- A homomorphism from `F(S)` to an abelian group kills `[a₁, b₁] ⋯ [a_g, b_g]`: read additively,
each commutator is `0`. -/
theorem relator_map_eq_one (g : ℕ) {A : Type*} [CommGroup A] (f : FreeGroup (Fin g ⊕ Fin g) →* A) : f (relator g) = 1 := by
  unfold relator
  simp [map_list_prod, List.map_ofFn, Function.comp_def, mul_assoc]

/-- `π₁(#_g T²)^ab ≅ ℤ^{2g}` (`cor:surface-abelian`, its first half), for the presentation
`⟨a₁, b₁, …, a_g, b_g ∣ [a₁, b₁] ⋯ [a_g, b_g]⟩` of `thm:surface-groups`. -/
theorem surface_ab (g : ℕ) :
    Nonempty (Additive (Abelianization (PresentedGroup {relator g})) ≃+ (Fin g ⊕ Fin g → ℤ)) := by
  classical
  let α := Fin g ⊕ Fin g
  let rels : Set (FreeGroup α) := {relator g}
  let F := Abelianization.map (PresentedGroup.mk rels)
  have hsurj : Function.Surjective F :=
    ab_map_surjective (PresentedGroup.mk rels)
      (PresentedGroup.mk_surjective rels)
  have hinj : Function.Injective F := by
    apply presented_ab_injective rels
    intro r hr
    have hr' : r = relator g := Set.mem_singleton_iff.mp hr
    subst r
    exact relator_map_eq_one g
      (Abelianization.of : FreeGroup α →* Abelianization (FreeGroup α))
  let e := MulEquiv.ofBijective F ⟨hinj, hsurj⟩
  exact ⟨(MulEquiv.toAdditive e.symm).trans (Week08FreeGroups.abEquiv α)⟩

/-! ### The non-orientable half: `k + 1` projective planes -/

namespace Crosscap

/-- `a₁² ⋯ a_m²` with `m = k + 1`. -/
def relator (k : ℕ) : FreeGroup (Fin (k + 1)) :=
  (List.ofFn fun i : Fin (k + 1) => FreeGroup.of i ^ 2).prod

abbrev crosscapAb (k : ℕ) := Additive (Abelianization (PresentedGroup {relator k}))

def crosscapGen (k : ℕ) (i : Fin (k + 1)) : crosscapAb k := Additive.ofMul (Abelianization.of (PresentedGroup.of (rels := {relator k}) i))

def crosscapModelGen (k : ℕ) : Fin (k + 1) → (Fin k → ℤ) × ZMod 2 := Fin.cases ((fun _ : Fin k => (-1 : ℤ)), (1 : ZMod 2)) (fun i => (Pi.single i (1 : ℤ), (0 : ZMod 2)))

theorem crosscap_hom_ext (k : ℕ) {A : Type*} [AddCommGroup A] (F G : crosscapAb k →+ A) (h : ∀ i, F (crosscapGen k i) = G (crosscapGen k i)) : F = G := by
  have hm : F.toMultiplicativeRight = G.toMultiplicativeRight := by
    apply Abelianization.hom_ext
    apply PresentedGroup.ext
    intro i
    exact congrArg Multiplicative.ofAdd (h i)
  exact AddMonoidHom.toMultiplicativeRight.injective hm

theorem crosscap_lift (k : ℕ) {A : Type*} [AddCommGroup A] (f : Fin (k + 1) → A) (hf : (2 : ℕ) • (∑ i, f i) = 0) : ∃ F : crosscapAb k →+ A, ∀ i, F (crosscapGen k i) = f i := by
  let g : Fin (k + 1) → Multiplicative A := fun i => Multiplicative.ofAdd (f i)
  have hrel : FreeGroup.lift g (relator k) = 1 := by
    simp only [relator, map_list_prod, List.map_ofFn, List.prod_ofFn]
    simpa [g, Finset.prod_pow, ← ofAdd_sum] using congrArg Multiplicative.ofAdd hf
  have h : ∀ r ∈ ({relator k} : Set (FreeGroup (Fin (k + 1)))), FreeGroup.lift g r = 1 := by
    rintro r hr
    rw [Set.mem_singleton_iff] at hr
    subst r
    exact hrel
  let p : PresentedGroup {relator k} →* Multiplicative A := PresentedGroup.toGroup h
  refine ⟨(Abelianization.lift p).toAdditiveLeft, ?_⟩
  intro i
  simp [crosscapGen, p, g]

theorem crosscap_model_sum (k : ℕ) : (∑ i : Fin (k + 1), crosscapModelGen k i) = ((0 : Fin k → ℤ), (1 : ZMod 2)) := by
  classical
  rw [Fin.sum_univ_succ]
  ext j <;> simp [crosscapModelGen, Prod.fst_sum, Prod.snd_sum,
    Finset.sum_apply, Pi.single_apply]

theorem crosscap_model_lift (k : ℕ) {A : Type*} [AddCommGroup A] (f : Fin (k + 1) → A) (hf : (2 : ℕ) • (∑ i, f i) = 0) : ∃! G : ((Fin k → ℤ) × ZMod 2) →+ A, ∀ i, G (crosscapModelGen k i) = f i := by
  classical
  let t : A := ∑ i, f i
  have ht : (2 : ℕ) • t = 0 := hf
  have ht' : (zmultiplesAddHom A t) (2 : ℤ) = 0 := by
    change ((2 : ℕ) : ℤ) • t = 0
    rw [natCast_zsmul]
    exact ht
  let q : ZMod 2 →+ A := ZMod.lift 2 ⟨zmultiplesAddHom A t, ht'⟩
  let L : (Fin k → ℤ) →+ A :=
    { toFun := fun x => ∑ j, x j • f j.succ
      map_zero' := by simp only [Pi.zero_apply, zero_zsmul, Finset.sum_const_zero]
      map_add' := by
        intro x y
        simp only [Pi.add_apply, add_zsmul, Finset.sum_add_distrib] }
  let G : ((Fin k → ℤ) × ZMod 2) →+ A := L.coprod q
  have hq : q 1 = t := by
    simpa [q] using ZMod.lift_coe 2 ⟨zmultiplesAddHom A t, ht'⟩ (1 : ℤ)
  have hG : ∀ i, G (crosscapModelGen k i) = f i := by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [crosscapModelGen, Fin.cases_zero]
      change (∑ j : Fin k, (-1 : ℤ) • f j.succ) + q 1 = f 0
      rw [hq]
      dsimp [t]
      rw [Fin.sum_univ_succ]
      simp only [neg_one_zsmul, Finset.sum_neg_distrib]
      abel
    · simp [crosscapModelGen, G, L]
  refine ⟨G, hG, ?_⟩
  intro H hH
  have hHone : H (0, 1) = t := by
    rw [← crosscap_model_sum k, map_sum]
    simp only [hH]
    rfl
  apply AddMonoidHom.ext
  intro p
  rcases p with ⟨x, z⟩
  have hx : (x, (0 : ZMod 2)) = ∑ j : Fin k, x j • crosscapModelGen k j.succ := by
    ext a
    · simp [crosscapModelGen, Prod.fst_sum, Finset.sum_apply, Pi.single_apply]
    · simp [crosscapModelGen, Prod.snd_sum]
  have hHx : H (x, 0) = L x := by
    rw [hx, map_sum]
    simp only [map_zsmul, hH]
    rfl
  have hHz : H (0, z) = q z := by
    fin_cases z
    · change H (0 : (Fin k → ℤ) × ZMod 2) = q 0
      rw [map_zero, map_zero]
    · change H (0, 1) = q 1
      rw [hHone, hq]
  have hp : (x, z) = (x, (0 : ZMod 2)) + (0, z) := by simp
  rw [hp, map_add, hHx, hHz]
  simp [G]

theorem crosscap_relation (k : ℕ) : (2 : ℕ) • (∑ i : Fin (k + 1), crosscapGen k i) = 0 := by
  let f : FreeGroup (Fin (k + 1)) →* Abelianization (PresentedGroup {relator k}) :=
    Abelianization.of.comp (PresentedGroup.mk {relator k})
  have h : f (relator k) = 1 := by
    change Abelianization.of ((PresentedGroup.mk {relator k}) (relator k)) = 1
    rw [PresentedGroup.one_of_mem (Set.mem_singleton (relator k)), map_one]
  change f (List.ofFn (fun i : Fin (k + 1) => FreeGroup.of i ^ 2)).prod = 1 at h
  rw [f.map_list_prod, List.map_ofFn, List.prod_ofFn] at h
  have hh := congrArg Additive.ofMul h
  simpa only [Function.comp_apply, map_pow, ofMul_prod, ofMul_pow,
    ← Finset.smul_sum, f, MonoidHom.comp_apply, crosscapGen,
    PresentedGroup.of, ofMul_one] using hh


/-- `π₁(#_k ℝP²)^ab ≅ ℤ^{k-1} ⊕ ℤ/2` (`cor:surface-abelian`, its second half), for the connected
sum of `m = k + 1` projective planes, whose group is `⟨a₁, …, a_m ∣ a₁² ⋯ a_m²⟩`
(`thm:surface-groups`). The book's route: a homomorphism from the presented group to an abelian
group is a map on the generators with `2 (f a₁ + ⋯ + f a_m) = 0`; the model `ℤ^k ⊕ ℤ/2` has the
generators `(-1, …, -1; 1)` and `(eᵢ; 0)`, which satisfy it, and both composites of the two maps
fix the generators. -/
theorem crosscap_ab (k : ℕ) :
    Nonempty (Additive (Abelianization (PresentedGroup {relator k})) ≃+ (Fin k → ℤ) × ZMod 2) := by
  classical
  have hm : (2 : ℕ) • (∑ i : Fin (k + 1), crosscapModelGen k i) = 0 := by
    rw [crosscap_model_sum]
    norm_num
    decide
  obtain ⟨F, hF⟩ := crosscap_lift k (crosscapModelGen k) hm
  obtain ⟨G, hG, hGuniq⟩ := crosscap_model_lift k (crosscapGen k) (crosscap_relation k)
  have hGF : G.comp F = AddMonoidHom.id (crosscapAb k) := by
    apply crosscap_hom_ext k
    intro i
    change G (F (crosscapGen k i)) = crosscapGen k i
    rw [hF, hG]
  obtain ⟨H, hH, hHuniq⟩ := crosscap_model_lift k (crosscapModelGen k) hm
  have hFG : F.comp G = AddMonoidHom.id ((Fin k → ℤ) × ZMod 2) := by
    have hcomp : F.comp G = H := hHuniq (F.comp G) (by
      intro i
      change F (G (crosscapModelGen k i)) = crosscapModelGen k i
      rw [hG, hF])
    have hid : AddMonoidHom.id ((Fin k → ℤ) × ZMod 2) = H :=
      hHuniq (AddMonoidHom.id _) (by intro i; rfl)
    exact hcomp.trans hid.symm
  refine ⟨{ toFun := F, invFun := G, left_inv := ?_, right_inv := ?_, map_add' := F.map_add }⟩
  · intro x
    exact congrArg (fun f : crosscapAb k →+ crosscapAb k => f x) hGF
  · intro x
    exact congrArg (fun f : ((Fin k → ℤ) × ZMod 2) →+ ((Fin k → ℤ) × ZMod 2) => f x) hFG

end Crosscap

end Week10SurfaceGroups
