/-
Machine-generated (Claude, Aristotle), no line written by a person. Copyleft: GPL-3.0-or-later.

# Week 12: the automorphisms of a transitive right `G`-set

This file proves the algebraic core of a statement of week 12 of the book.

* `Aut(p) ≅ N(H)/H` (`thm:deck-group`, `deck_group`): the automorphisms of a transitive right
  `G`-set `X`, whose point `x₀` has stabiliser `H`, form a group isomorphic to `N(H)/H`. A right
  action is an action of `Gᵐᵒᵖ`; an automorphism is a permutation of `X` that commutes with every
  `x ↦ x · g`, that is, an element of the centraliser of those permutations. The book's route:
  an automorphism `φ` is determined by `φ(x₀) = x₀ · g`, since `φ(x₀ · g') = φ(x₀) · g'`
  (`deck_centralizer_iff`, `deck_orbit_eq_iff`); for a given `g`, the rule `x₀ · g' ↦ x₀ · g g'`
  is well defined and bijective exactly when `g ∈ N(H)` (`deck_centralizer_representative_normalizes`,
  `deck_translation_exists`); sending `g` to it is a homomorphism from `N(H)` onto the
  automorphisms, with kernel `H` (`deck_normalizer_hom_exists`, `deck_group`). That the fibre of a
  covering is such a right `π₁`-set, with `H = p_* π₁(X̃, e)` (`thm:monodromy-action`), and that a
  deck transformation is an automorphism of it (`thm:fibre-functor-ff`) are not formalised here.

The proof was found by a computer program (an automated prover), and Lean checks it like every
proof here.
-/
import Mathlib

namespace Week12Deck

/-- A permutation commutes with every `x ↦ x · g` exactly when it is in the centraliser. -/
theorem deck_centralizer_iff {G X : Type*} [Group G] [MulAction Gᵐᵒᵖ X]
    (p : Equiv.Perm X) :
    p ∈ Subgroup.centralizer (Set.range (MulAction.toPermHom Gᵐᵒᵖ X)) ↔
      ∀ (g : G) (x : X), p (MulOpposite.op g • x) = MulOpposite.op g • p x := by
  rw [Subgroup.mem_centralizer_iff]
  constructor
  · intro h g x
    have he := h (MulAction.toPermHom Gᵐᵒᵖ X (MulOpposite.op g))
      (Set.mem_range_self (MulOpposite.op g))
    exact (congrArg (fun q : Equiv.Perm X => q x) he).symm
  · intro h q hq
    rcases hq with ⟨g, rfl⟩
    ext x
    exact (h g.unop x).symm

/-- `x₀ · a = x₀ · b` exactly when `a b⁻¹ ∈ H`, `H` being the stabiliser of `x₀`. -/
theorem deck_orbit_eq_iff {G X : Type*} [Group G] [MulAction Gᵐᵒᵖ X]
    (x₀ : X) (H : Subgroup G)
    (hH : ∀ g : G, g ∈ H ↔ MulOpposite.op g • x₀ = x₀)
    (a b : G) :
    MulOpposite.op a • x₀ = MulOpposite.op b • x₀ ↔ a * b⁻¹ ∈ H := by
  rw [hH]
  constructor
  · intro h
    have h' := congrArg (fun x : X => MulOpposite.op (b⁻¹) • x) h
    simpa only [← mul_smul, ← MulOpposite.op_mul, mul_inv_cancel,
      MulOpposite.op_one, one_smul] using h'
  · intro h
    have h' := congrArg (fun x : X => MulOpposite.op b • x) h
    simpa only [← mul_smul, ← MulOpposite.op_mul, mul_assoc,
      inv_mul_cancel, mul_one] using h'

/-- If an automorphism sends `x₀` to `x₀ · n`, then `n ∈ N(H)` (`φ` is well defined and injective). -/
theorem deck_centralizer_representative_normalizes {G X : Type*} [Group G] [MulAction Gᵐᵒᵖ X]
    (x₀ : X) (H : Subgroup G)
    (hH : ∀ g : G, g ∈ H ↔ MulOpposite.op g • x₀ = x₀)
    (p : Subgroup.centralizer (Set.range (MulAction.toPermHom Gᵐᵒᵖ X)))
    (n : G) (hn : (p : Equiv.Perm X) x₀ = MulOpposite.op n • x₀) :
    n ∈ Subgroup.normalizer (H : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  have hp := (deck_centralizer_iff (p : Equiv.Perm X)).mp p.property
  have heq : (MulOpposite.op h • (MulOpposite.op n • x₀)) =
      MulOpposite.op (n * h) • x₀ := by
    rw [← mul_smul]
    rfl
  have hh : h ∈ H ↔ n * h * n⁻¹ ∈ H := by
    rw [hH h, ← (p : Equiv.Perm X).injective.eq_iff, hp h x₀, hn, heq]
    exact deck_orbit_eq_iff x₀ H hH (n * h) n
  exact hh

/-- For `n ∈ N(H)`, the rule `x₀ · a ↦ x₀ · n a` is a well-defined permutation of `X`. -/
theorem deck_translation_exists {G X : Type*} [Group G] [MulAction Gᵐᵒᵖ X]
    [MulAction.IsPretransitive Gᵐᵒᵖ X]
    (x₀ : X) (H : Subgroup G)
    (hH : ∀ g : G, g ∈ H ↔ MulOpposite.op g • x₀ = x₀)
    (n : G) (hn : n ∈ Subgroup.normalizer (H : Set G)) :
    ∃ p : Equiv.Perm X, ∀ a : G,
      p (MulOpposite.op a • x₀) = MulOpposite.op (n * a) • x₀ := by
  classical
  have hreps : ∀ x : X, ∃ a : G, MulOpposite.op a • x₀ = x := by
    intro x
    obtain ⟨a, ha⟩ := MulAction.exists_smul_eq Gᵐᵒᵖ x₀ x
    exact ⟨MulOpposite.unop a, ha⟩
  choose r hr using hreps
  have hnormal := Subgroup.mem_normalizer_iff.mp hn
  have hfiber : ∀ a b : G,
      MulOpposite.op a • x₀ = MulOpposite.op b • x₀ ↔
      MulOpposite.op (n * a) • x₀ = MulOpposite.op (n * b) • x₀ := by
    intro a b
    rw [deck_orbit_eq_iff x₀ H hH, deck_orbit_eq_iff x₀ H hH]
    have heq : (n * a) * (n * b)⁻¹ = n * (a * b⁻¹) * n⁻¹ := by group
    rw [heq]
    exact hnormal (a * b⁻¹)
  let f : X → X := fun x => MulOpposite.op (n * r x) • x₀
  have hf : ∀ a : G, f (MulOpposite.op a • x₀) = MulOpposite.op (n * a) • x₀ := by
    intro a
    exact (hfiber (r (MulOpposite.op a • x₀)) a).mp (hr _)
  have hinj : Function.Injective f := by
    intro x y h
    have hxy := (hfiber (r x) (r y)).mpr h
    simpa only [hr] using hxy
  have hsurj : Function.Surjective f := by
    intro y
    refine ⟨MulOpposite.op (n⁻¹ * r y) • x₀, ?_⟩
    rw [hf]
    simpa only [mul_inv_cancel_left] using hr y
  exact ⟨Equiv.ofBijective f ⟨hinj, hsurj⟩, hf⟩

/-- `n ↦ (x₀ · a ↦ x₀ · n a)` is a homomorphism from `N(H)` to the automorphisms. -/
theorem deck_normalizer_hom_exists {G X : Type*} [Group G] [MulAction Gᵐᵒᵖ X]
    [MulAction.IsPretransitive Gᵐᵒᵖ X]
    (x₀ : X) (H : Subgroup G)
    (hH : ∀ g : G, g ∈ H ↔ MulOpposite.op g • x₀ = x₀) :
    ∃ ρ : Subgroup.normalizer (H : Set G) →*
      Subgroup.centralizer (Set.range (MulAction.toPermHom Gᵐᵒᵖ X)),
      ∀ n : Subgroup.normalizer (H : Set G),
        ((ρ n : Subgroup.centralizer (Set.range (MulAction.toPermHom Gᵐᵒᵖ X))) : Equiv.Perm X) x₀ =
          MulOpposite.op (n : G) • x₀ := by
  classical
  let N := Subgroup.normalizer (H : Set G)
  let C := Subgroup.centralizer (Set.range (MulAction.toPermHom Gᵐᵒᵖ X))
  choose p hp using fun n : N => deck_translation_exists x₀ H hH (n : G) n.property
  have hex : ∀ x : X, ∃ a : G, MulOpposite.op a • x₀ = x := by
    intro x
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Gᵐᵒᵖ x₀ x
    exact ⟨MulOpposite.unop g, hg⟩
  have hact (a g : G) : MulOpposite.op g • (MulOpposite.op a • x₀) =
      MulOpposite.op (a * g) • x₀ := by
    rw [← mul_smul]
    rfl
  have hc (n : N) : p n ∈ C := by
    apply (deck_centralizer_iff (p n)).2
    intro g x
    obtain ⟨a, rfl⟩ := hex x
    rw [hact, hp, hp, hact, mul_assoc]
  let f : N → C := fun n => ⟨p n, hc n⟩
  have hf (n : N) (a : G) : (f n : Equiv.Perm X) (MulOpposite.op a • x₀) =
      MulOpposite.op ((n : G) * a) • x₀ := hp n a
  refine ⟨{ toFun := f, map_one' := ?_, map_mul' := ?_ }, ?_⟩
  · apply Subtype.ext
    apply Equiv.ext
    intro x
    obtain ⟨a, rfl⟩ := hex x
    change (f 1 : Equiv.Perm X) (MulOpposite.op a • x₀) = MulOpposite.op a • x₀
    rw [hf]
    simp only [Subgroup.coe_one, one_mul]
  · intro n m
    apply Subtype.ext
    apply Equiv.ext
    intro x
    obtain ⟨a, rfl⟩ := hex x
    change (f (n * m) : Equiv.Perm X) (MulOpposite.op a • x₀) =
      (f n : Equiv.Perm X) ((f m : Equiv.Perm X) (MulOpposite.op a • x₀))
    rw [hf, hf, hf]
    simp only [Subgroup.coe_mul, mul_assoc]
  · intro n
    change (f n : Equiv.Perm X) x₀ = MulOpposite.op (n : G) • x₀
    have h := hf n 1
    simpa only [MulOpposite.op_one, one_smul, mul_one] using h


/-- `Aut(p) ≅ N(H)/H` (`thm:deck-group`), for a transitive right `G`-set with the point `x₀` of
stabiliser `H`: the automorphisms (the centraliser of the permutations `x ↦ x · g`) are isomorphic
to the normaliser of `H` modulo `H`. The book's route: `N(H) → Aut`, `g ↦ (x₀ g' ↦ x₀ g g')`, is
a surjective homomorphism with kernel `H`. -/
theorem deck_group {G X : Type*} [Group G] [MulAction Gᵐᵒᵖ X]
    [MulAction.IsPretransitive Gᵐᵒᵖ X] (x₀ : X) (H : Subgroup G)
    (hH : ∀ g : G, g ∈ H ↔ MulOpposite.op g • x₀ = x₀) :
    Nonempty (Subgroup.centralizer (Set.range (MulAction.toPermHom Gᵐᵒᵖ X)) ≃*
      (Subgroup.normalizer (H : Set G) ⧸ H.subgroupOf (Subgroup.normalizer (H : Set G)))) := by
  classical
  obtain ⟨ρ, hρ⟩ := deck_normalizer_hom_exists x₀ H hH
  let N := Subgroup.normalizer (H : Set G)
  let K := H.subgroupOf N
  let C := Subgroup.centralizer (Set.range (MulAction.toPermHom Gᵐᵒᵖ X))
  have hext (p q : C) (hpq : (p : Equiv.Perm X) x₀ = (q : Equiv.Perm X) x₀) : p = q := by
    apply Subtype.ext
    ext x
    obtain ⟨a, rfl⟩ := MulAction.exists_smul_eq Gᵐᵒᵖ x₀ x
    have hp := (deck_centralizer_iff (p : Equiv.Perm X)).mp p.property a.unop x₀
    have hq := (deck_centralizer_iff (q : Equiv.Perm X)).mp q.property a.unop x₀
    simpa only [MulOpposite.op_unop] using
      hp.trans ((congrArg (fun y : X => MulOpposite.op a.unop • y) hpq).trans hq.symm)
  have hsurj : Function.Surjective ρ := by
    intro p
    obtain ⟨n, hn⟩ := MulAction.exists_smul_eq Gᵐᵒᵖ x₀ ((p : Equiv.Perm X) x₀)
    have hnN := deck_centralizer_representative_normalizes x₀ H hH p n.unop hn.symm
    refine ⟨⟨n.unop, hnN⟩, ?_⟩
    apply hext
    exact (hρ ⟨n.unop, hnN⟩).trans hn
  have hker : ρ.ker = K := by
    ext n
    change ρ n = 1 ↔ (n : G) ∈ H
    constructor
    · intro hn
      apply (hH (n : G)).mpr
      rw [← hρ n, hn]
      rfl
    · intro hn
      apply hext
      exact (hρ n).trans ((hH (n : G)).mp hn)
  exact ⟨(QuotientGroup.quotientKerEquivOfSurjective ρ hsurj).symm.trans
    (QuotientGroup.quotientMulEquivOfEq hker)⟩

end Week12Deck
