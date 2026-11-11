/-
Machine-generated (Claude, Aristotle), no line written by a person. Copyleft: GPL-3.0-or-later.

# Week 9: homology, the algebra

This file proves statements of week 9 of the book. Over a ring `R`, take maps
of modules `A --d₁--> B --d₀--> C` with `d₀ ∘ d₁ = 0`.

* Boundaries are cycles: `im d₁ ⊆ ker d₀` (`lem:boundaries-are-cycles`), since `d₀ (d₁ a) = 0`.
* A chain map induces one and only one map on homology, the one sending the class `[z]` of a cycle
  to the class of its image (`lem:chain-map-homology`). The homology at `B` is `H d₁ d₀`, the
  cycles `ker d₀` modulo the boundaries `im d₁`; `cls d₁ d₀ z` is the class `[z]`.
* The map induced by a composite is the composite of the induced maps, `(gf)_* = g_* f_*`
  (`functoriality`, also `lem:chain-map-homology`).
* Chain homotopic chain maps induce the same map on homology (`lem:chain-homotopy`): for a
  cycle `z`, `f z - g z = ∂ (P z)` is a boundary (`homotopic_maps_agree`).
* The boundary of ordered simplicial chains squares to zero (`lem:dd`): in `∂ ∂ σ` the terms
  `σ ∘ δ i ∘ δ j` cancel in pairs, by `δ j.castSucc ∘ δ i = δ i.succ ∘ δ j` for `j ≤ i`
  (`delete_comm`, the face identity `lem:face-identity`), where `δ i = Fin.succAbove i`
  misses `i`.
* The boundary of singular chains squares to zero (`lem:dd`, `Singular.bd_bd`), by the book's
  route: the face maps `dⁱ` of the standard simplex satisfy the face identity
  (`lem:face-identity`, `Singular.face_comp`), and the terms of `∂ ∂ σ` cancel in pairs as for
  ordered chains (`alternating_sum_cancel`).
* The cone formula on ordered chains (`prop:cone-construction`): with `v · σ` the simplex `σ`
  with the vertex `v` put in front, `∂ (v · c) = c - v · ∂ c` for every chain `c` of degree at
  least `1` (`cone_boundary`), by the book's comparison of faces.
* The ordered chain complex of all simplices on a nonempty `V` has no homology in degrees at
  least `1` (`acyclic`, the last step of `prop:cone-construction`): a cycle `z` is the boundary
  of its cone. On one vertex this is the point (`prop:homology-point`, `point_acyclic`), by the
  cone rather than by the book's explicit complex.
* `H₀ ≅ ℤ` on a nonempty `V`, through the augmentation `ε (∑ m_k x_k) = ∑ m_k` (`prop:H0`,
  `H0_equiv_int`), by the book's route: `ε` is onto and kills the boundaries, and a chain with
  `ε = 0` is the boundary of `∑ m_k (v, x_k)`, the edges `(v, x_k)` playing the book's paths. On
  one vertex this is the point's `H₀` (`point_H0`, `prop:homology-point`).
* For singular chains, `H₀ ≅ ℤ` on a path-connected space, through the augmentation
  (`prop:H0`, `Singular.H0_equiv_int`), by the book's route: a path from `x` to `σ`, read on
  `Δ¹`, is a singular `1`-simplex with boundary `σ - x` (`Singular.single_sub_single_mem_range`).
* (This item describes a homework's solution; it appears here after 12 November 2026.)


* For a finite graph, `b₁ = |E| - |V| + c` (`exr-9-graph`), by rank-nullity from `b₀ = c`
  (`b1_eq_edges_sub_vertices_add_components`).
* (This item describes a homework's solution; it appears here after 12 November 2026.)


* (This item describes a homework's solution; it appears here after 12 November 2026.)


* (This item describes a homework's solution; it appears here after 12 November 2026.)




The proofs were found by a computer program, the automated prover Aleph Prover, and Lean checks
them like every proof here.
Whether each Lean statement says what the book's statement says is still to be compared.
-/
import Mathlib

namespace Week09Homology

/-! ## Boundaries are cycles (`lem:boundaries-are-cycles`) -/

theorem range_le_ker {R A B C : Type*} [Ring R]
    [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B] [AddCommGroup C] [Module R C]
    (d₁ : A →ₗ[R] B) (d₀ : B →ₗ[R] C) (h : d₀ ∘ₗ d₁ = 0) :
    LinearMap.range d₁ ≤ LinearMap.ker d₀ := by
  intro b hb
  rcases hb with ⟨a, rfl⟩
  change d₀ (d₁ a) = 0
  have ha := LinearMap.congr_fun h a
  exact ha

/-! ## The map on homology (`lem:chain-map-homology`) -/

/-- The homology at `B` of `A --d₁--> B --d₀--> C`: the cycles `ker d₀` modulo the
boundaries `im d₁`, taken inside `ker d₀`. -/
abbrev H {R A B C : Type*} [Ring R] [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B] [AddCommGroup C] [Module R C]
    (d₁ : A →ₗ[R] B) (d₀ : B →ₗ[R] C) : Type _ :=
  ↥(LinearMap.ker d₀) ⧸ (LinearMap.range d₁).comap (LinearMap.ker d₀).subtype

/-- The class `[z]` of a cycle `z`. -/
abbrev cls {R A B C : Type*} [Ring R] [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B] [AddCommGroup C] [Module R C]
    (d₁ : A →ₗ[R] B) (d₀ : B →ₗ[R] C) (z : LinearMap.ker d₀) : H d₁ d₀ :=
  Submodule.Quotient.mk z

theorem induced_map_exists_unique {R A B C A' B' C' : Type*} [Ring R]
    [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B] [AddCommGroup C] [Module R C]
    [AddCommGroup A'] [Module R A'] [AddCommGroup B'] [Module R B'] [AddCommGroup C'] [Module R C']
    (d₁ : A →ₗ[R] B) (d₀ : B →ₗ[R] C) (hd : d₀ ∘ₗ d₁ = 0)
    (d₁' : A' →ₗ[R] B') (d₀' : B' →ₗ[R] C') (hd' : d₀' ∘ₗ d₁' = 0)
    (f₂ : A →ₗ[R] A') (f₁ : B →ₗ[R] B') (f₀ : C →ₗ[R] C')
    (sqf₁ : d₁' ∘ₗ f₂ = f₁ ∘ₗ d₁) (sqf₀ : d₀' ∘ₗ f₁ = f₀ ∘ₗ d₀) :
    ∃! φ : H d₁ d₀ →ₗ[R] H d₁' d₀',
      ∀ (z : LinearMap.ker d₀) (z' : LinearMap.ker d₀'),
        (z' : B') = f₁ z → φ (cls d₁ d₀ z) = cls d₁' d₀' z' := by
  let F : LinearMap.ker d₀ →ₗ[R] LinearMap.ker d₀' :=
    { toFun := fun z => ⟨f₁ z, by
        have h := congrArg (fun k : B →ₗ[R] C' => k z) sqf₀
        change d₀' (f₁ z) = f₀ (d₀ z) at h
        change d₀' (f₁ z) = 0
        rw [LinearMap.mem_ker.mp z.property, map_zero] at h
        exact h⟩
      map_add' := by
        intro x y
        apply Subtype.ext
        exact f₁.map_add x y
      map_smul' := by
        intro r x
        apply Subtype.ext
        exact f₁.map_smul r x }
  let P := (LinearMap.range d₁).comap (LinearMap.ker d₀).subtype
  let P' := (LinearMap.range d₁').comap (LinearMap.ker d₀').subtype
  have hF : P ≤ P'.comap F := by
    intro z hz
    change (f₁ z : B') ∈ LinearMap.range d₁'
    change (z : B) ∈ LinearMap.range d₁ at hz
    rcases hz with ⟨a, ha⟩
    refine ⟨f₂ a, ?_⟩
    have h := congrArg (fun k : A →ₗ[R] B' => k a) sqf₁
    change d₁' (f₂ a) = f₁ (d₁ a) at h
    exact h.trans (congrArg f₁ ha)
  refine ⟨P.mapQ P' F hF, ?_, ?_⟩
  · intro z z' hz'
    have heq : F z = z' := Subtype.ext hz'.symm
    change Submodule.Quotient.mk (F z) = Submodule.Quotient.mk z'
    rw [heq]
  · intro ψ hψ
    apply LinearMap.ext
    intro x
    induction x using Submodule.Quotient.induction_on with
    | _ z => exact hψ z (F z) rfl

/-- The map induced by a composite of chain maps is the composite of the induced maps,
`(gf)_* = g_* f_*` (`lem:chain-map-homology`): `φ`, `ψ`, `χ` are the maps that
`induced_map_exists_unique` gives for `f`, `g` and `gf`. -/
theorem functoriality {R A B C A' B' C' A'' B'' C'' : Type*} [Ring R]
    [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B] [AddCommGroup C] [Module R C]
    [AddCommGroup A'] [Module R A'] [AddCommGroup B'] [Module R B'] [AddCommGroup C'] [Module R C']
    [AddCommGroup A''] [Module R A''] [AddCommGroup B''] [Module R B''] [AddCommGroup C''] [Module R C'']
    (d₁ : A →ₗ[R] B) (d₀ : B →ₗ[R] C) (hd : d₀ ∘ₗ d₁ = 0)
    (d₁' : A' →ₗ[R] B') (d₀' : B' →ₗ[R] C') (hd' : d₀' ∘ₗ d₁' = 0)
    (d₁'' : A'' →ₗ[R] B'') (d₀'' : B'' →ₗ[R] C'') (hd'' : d₀'' ∘ₗ d₁'' = 0)
    (f₂ : A →ₗ[R] A') (f₁ : B →ₗ[R] B') (f₀ : C →ₗ[R] C')
    (sqf₁ : d₁' ∘ₗ f₂ = f₁ ∘ₗ d₁) (sqf₀ : d₀' ∘ₗ f₁ = f₀ ∘ₗ d₀)
    (g₂ : A' →ₗ[R] A'') (g₁ : B' →ₗ[R] B'') (g₀ : C' →ₗ[R] C'')
    (sqg₁ : d₁'' ∘ₗ g₂ = g₁ ∘ₗ d₁') (sqg₀ : d₀'' ∘ₗ g₁ = g₀ ∘ₗ d₀')
    (φ : H d₁ d₀ →ₗ[R] H d₁' d₀') (ψ : H d₁' d₀' →ₗ[R] H d₁'' d₀'')
    (χ : H d₁ d₀ →ₗ[R] H d₁'' d₀'')
    (hφ : ∀ (z : LinearMap.ker d₀) (z' : LinearMap.ker d₀'),
      (z' : B') = f₁ z → φ (cls d₁ d₀ z) = cls d₁' d₀' z')
    (hψ : ∀ (z' : LinearMap.ker d₀') (z'' : LinearMap.ker d₀''),
      (z'' : B'') = g₁ z' → ψ (cls d₁' d₀' z') = cls d₁'' d₀'' z'')
    (hχ : ∀ (z : LinearMap.ker d₀) (z'' : LinearMap.ker d₀''),
      (z'' : B'') = g₁ (f₁ z) → χ (cls d₁ d₀ z) = cls d₁'' d₀'' z'') :
    χ = ψ ∘ₗ φ := by
  apply LinearMap.ext
  intro x
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  let z' : LinearMap.ker d₀' := ⟨f₁ z, by
    change d₀' (f₁ z) = 0
    rw [← LinearMap.comp_apply, sqf₀, LinearMap.comp_apply]
    simp only [LinearMap.mem_ker.mp z.property, map_zero]⟩
  let z'' : LinearMap.ker d₀'' := ⟨g₁ z', by
    change d₀'' (g₁ z') = 0
    rw [← LinearMap.comp_apply, sqg₀, LinearMap.comp_apply]
    simp only [LinearMap.mem_ker.mp z'.property, map_zero]⟩
  change χ (cls d₁ d₀ z) = ψ (φ (cls d₁ d₀ z))
  rw [hφ z z' rfl, hψ z' z'' rfl, hχ z z'' rfl]

/-! ## Chain homotopic maps agree on homology (`lem:chain-homotopy`) -/

/-- Chain homotopic chain maps induce the same map on homology (`lem:chain-homotopy`). The
homotopy is `hB : B → A'` and `hC : C → B'` with `f₁ - g₁ = d₁' ∘ hB + hC ∘ d₀`; `φ` and `γ`
are the maps that `induced_map_exists_unique` gives for `f` and `g`. For a cycle `z`,
`f₁ z - g₁ z = d₁' (hB z) + hC (d₀ z) = d₁' (hB z)` is a boundary, so `[f₁ z] = [g₁ z]`. -/
theorem homotopic_maps_agree {R A B C A' B' C' : Type*} [Ring R]
    [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B] [AddCommGroup C] [Module R C]
    [AddCommGroup A'] [Module R A'] [AddCommGroup B'] [Module R B'] [AddCommGroup C'] [Module R C']
    (d₁ : A →ₗ[R] B) (d₀ : B →ₗ[R] C) (hd : d₀ ∘ₗ d₁ = 0)
    (d₁' : A' →ₗ[R] B') (d₀' : B' →ₗ[R] C') (hd' : d₀' ∘ₗ d₁' = 0)
    (f₂ : A →ₗ[R] A') (f₁ : B →ₗ[R] B') (f₀ : C →ₗ[R] C')
    (sqf₁ : d₁' ∘ₗ f₂ = f₁ ∘ₗ d₁) (sqf₀ : d₀' ∘ₗ f₁ = f₀ ∘ₗ d₀)
    (g₂ : A →ₗ[R] A') (g₁ : B →ₗ[R] B') (g₀ : C →ₗ[R] C')
    (sqg₁ : d₁' ∘ₗ g₂ = g₁ ∘ₗ d₁) (sqg₀ : d₀' ∘ₗ g₁ = g₀ ∘ₗ d₀)
    (hB : B →ₗ[R] A') (hC : C →ₗ[R] B') (hom : f₁ - g₁ = d₁' ∘ₗ hB + hC ∘ₗ d₀)
    (φ γ : H d₁ d₀ →ₗ[R] H d₁' d₀')
    (hφ : ∀ (z : LinearMap.ker d₀) (z' : LinearMap.ker d₀'),
      (z' : B') = f₁ z → φ (cls d₁ d₀ z) = cls d₁' d₀' z')
    (hγ : ∀ (z : LinearMap.ker d₀) (z' : LinearMap.ker d₀'),
      (z' : B') = g₁ z → γ (cls d₁ d₀ z) = cls d₁' d₀' z') :
    φ = γ := by
  apply LinearMap.ext
  intro x
  rcases Submodule.Quotient.mk_surjective _ x with ⟨z, rfl⟩
  have hf : d₀' (f₁ z) = 0 := by
    have hs := LinearMap.congr_fun sqf₀ z
    simpa only [LinearMap.comp_apply, LinearMap.mem_ker.mp z.property, map_zero] using hs
  have hg : d₀' (g₁ z) = 0 := by
    have hs := LinearMap.congr_fun sqg₀ z
    simpa only [LinearMap.comp_apply, LinearMap.mem_ker.mp z.property, map_zero] using hs
  rw [hφ z ⟨f₁ z, hf⟩ rfl, hγ z ⟨g₁ z, hg⟩ rfl]
  apply (Submodule.Quotient.eq _).mpr
  change (⟨f₁ z, hf⟩ : LinearMap.ker d₀') - ⟨g₁ z, hg⟩ ∈ _
  have hh := LinearMap.congr_fun hom z
  simp only [LinearMap.sub_apply, LinearMap.add_apply, LinearMap.comp_apply,
    LinearMap.mem_ker.mp z.property, map_zero, add_zero] at hh
  exact ⟨hB z, hh.symm⟩

/-! ## The boundary squares to zero (`lem:dd`) -/

/-- `∂ : C (n+1) → C n` on ordered simplices `σ : Fin (n+2) → V`:
`∂ σ = ∑ i, (-1)^i (σ ∘ δ i)`, where `δ i = Fin.succAbove i` misses `i`. -/
noncomputable def bd (V : Type*) (n : ℕ) :
    ((Fin (n + 2) → V) →₀ ℤ) →ₗ[ℤ] ((Fin (n + 1) → V) →₀ ℤ) :=
  Finsupp.linearCombination ℤ fun σ =>
    ∑ i : Fin (n + 2), ((-1 : ℤ) ^ (i : ℕ)) • Finsupp.single (σ ∘ Fin.succAbove i) (1 : ℤ)

theorem alternating_sum_cancel {M : Type*} [AddCommGroup M] (m : ℕ) (f : Fin (m + 2) → Fin (m + 1) → M) (h : ∀ i j : Fin (m + 1), j ≤ i → f j.castSucc i = f i.succ j) : (∑ i : Fin (m + 2), ∑ j : Fin (m + 1), ((-1 : ℤ) ^ (i : ℕ) * (-1 : ℤ) ^ (j : ℕ)) • f i j) = 0 := by
  classical
  let P := Fin (m + 1) × Fin (m + 2)
  let S : Finset P := Finset.univ.filter (fun ij => ij.2.val ≤ ij.1.val)
  rw [Finset.sum_comm, ← Finset.sum_product', Finset.univ_product_univ]
  rw [← Finset.sum_add_sum_compl S, ← eq_neg_iff_add_eq_zero, ← Finset.sum_neg_distrib]
  let φ : ∀ ij : P, ij ∈ S → P := fun ij hij =>
    (Fin.castLT ij.2 (lt_of_le_of_lt (Finset.mem_filter.mp hij).2 ij.1.is_lt), ij.1.succ)
  apply Finset.sum_bij φ
  · intro ij hij
    simp only [S, φ, Finset.mem_compl, Finset.mem_filter, Finset.mem_univ,
      true_and, Fin.val_succ, Fin.val_castLT]
    have hij' := (Finset.mem_filter.mp hij).2
    omega
  · intro a ha b hb hab
    apply Prod.ext
    · apply Fin.ext
      have hh := congrArg (fun p : P => p.2.val) hab
      change a.1.val + 1 = b.1.val + 1 at hh
      omega
    · apply Fin.ext
      exact congrArg (fun p : P => p.1.val) hab
  · intro ij hij
    have hij' : ij.1.val < ij.2.val := by
      simpa only [S, Finset.mem_compl, Finset.mem_filter, Finset.mem_univ,
        true_and, not_le] using hij
    have hne : ij.2 ≠ 0 := by
      intro hz
      simp only [hz, Fin.val_zero] at hij'
      omega
    refine ⟨(ij.2.pred hne, ij.1.castSucc), ?_, ?_⟩
    · simp only [S, Finset.mem_filter, Finset.mem_univ, true_and,
        Fin.val_castSucc, Fin.val_pred]
      omega
    · apply Prod.ext
      · simp only [φ, Fin.castLT_castSucc]
      · simp only [φ, Fin.succ_pred]
  · intro ij hij
    have hij' := (Finset.mem_filter.mp hij).2
    have heq := h ij.1 (Fin.castLT ij.2 (lt_of_le_of_lt hij' ij.1.is_lt))
      (by simpa only [Fin.le_iff_val_le_val, Fin.val_castLT] using hij')
    simp only [Fin.castSucc_castLT] at heq
    simp only [φ, Fin.val_castLT, Fin.val_succ, pow_succ, heq,
      mul_neg, neg_mul, one_mul, neg_smul, neg_neg, mul_comm]

theorem bd_single (V : Type*) (n : ℕ) (σ : Fin (n + 2) → V) : bd V n (Finsupp.single σ (1 : ℤ)) = ∑ i : Fin (n + 2), ((-1 : ℤ) ^ (i : ℕ)) • Finsupp.single (σ ∘ Fin.succAbove i) (1 : ℤ) := by
  simp only [bd, Finsupp.linearCombination_single, one_smul]

/-- The face identity (`lem:face-identity`), with `δ k = Fin.succAbove k` in the place of
the book's `d^k`: the book's `d^j d^i = d^i d^(j-1)` for `i < j` is this equation with the
book's `i` for `j` here and the book's `j` for `i + 1` here. -/
theorem delete_comm (m : ℕ) (i j : Fin (m + 1)) (h : j ≤ i) : (Fin.succAbove j.castSucc) ∘ (Fin.succAbove i) = (Fin.succAbove i.succ) ∘ (Fin.succAbove j) := by
  funext k
  simpa only [Function.comp_apply, Fin.succAbove_castSucc_of_le _ _ h,
    Fin.predAbove_castSucc_of_le _ _ h] using
    (Fin.succAbove_succAbove_succAbove_predAbove j.castSucc i k).symm

theorem bd_bd (V : Type*) (n : ℕ) : bd V n ∘ₗ bd V (n + 1) = 0 := by
  classical
  apply Finsupp.lhom_ext'
  intro σ
  apply LinearMap.ext_ring
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, LinearMap.zero_apply,
    bd_single, map_sum, map_smul, Finset.smul_sum, smul_smul]
  apply alternating_sum_cancel (n + 1)
  intro i j hij
  simpa only [Function.comp_assoc] using
    congrArg (fun g => Finsupp.single (σ ∘ g) (1 : ℤ))
      (delete_comm (n + 1) i j hij)

/-! ## Singular chains: the boundary squares to zero (`lem:dd`)

The book's `lem:dd` is about singular chains. The face maps `dⁱ` of the standard simplex satisfy
the face identity (`lem:face-identity`, `Singular.face_comp`), and the terms of `∂ ∂ σ` cancel in
pairs exactly as for ordered chains (`alternating_sum_cancel`). -/

namespace Singular

/-- The standard `n`-simplex `Δⁿ = {t ∈ ℝ^{n+1} : tᵢ ≥ 0, ∑ tᵢ = 1}` (`def:standard-simplex`). -/
def Simplex (n : ℕ) : Set (Fin (n + 1) → ℝ) := {t | (∀ i, 0 ≤ t i) ∧ ∑ i, t i = 1}

/-- The face map `dⁱ : Δⁿ → Δⁿ⁺¹`, inserting a zero at position `i`: it includes `Δⁿ` as the
face opposite the vertex `eᵢ`. -/
def face (n : ℕ) (i : Fin (n + 2)) : C(Simplex n, Simplex (n + 1)) where
  toFun t := ⟨Fin.insertNth i 0 t.1, fun k => by
      induction k using Fin.succAboveCases i with
      | x => simp
      | p j => simpa using t.2.1 j,
    by rw [Fin.sum_univ_succAbove _ i]; simpa using t.2.2⟩
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ _
    exact Continuous.finInsertNth i continuous_const continuous_subtype_val

/-- The boundary `∂ : C_{n+1}(X) → C_n(X)` of singular chains (`def:boundary`):
`∂ σ = ∑ i, (-1)^i (σ ∘ dⁱ)` on a singular simplex `σ : Δⁿ⁺¹ → X`. -/
noncomputable def bd (X : Type*) [TopologicalSpace X] (n : ℕ) :
    (C(Simplex (n + 1), X) →₀ ℤ) →ₗ[ℤ] (C(Simplex n, X) →₀ ℤ) :=
  Finsupp.linearCombination ℤ fun σ =>
    ∑ i : Fin (n + 2), ((-1 : ℤ) ^ (i : ℕ)) • Finsupp.single (σ.comp (face n i)) (1 : ℤ)

theorem bd_single (X : Type*) [TopologicalSpace X] (n : ℕ) (σ : C(Simplex (n + 1), X)) :
    bd X n (Finsupp.single σ (1 : ℤ)) =
      ∑ i : Fin (n + 2), ((-1 : ℤ) ^ (i : ℕ)) • Finsupp.single (σ.comp (face n i)) (1 : ℤ) := by
  simp only [bd, Finsupp.linearCombination_single, one_smul]

/-- The face identity (`lem:face-identity`): the book's `d^j d^i = d^i d^(j-1)` for `i < j` is
this equation with the book's `i` for `j` here and the book's `j` for `i + 1` here. Both sides
insert zeros in the same two positions, compared coordinate by coordinate. -/
theorem face_comp (n : ℕ) (i j : Fin (n + 2)) (h : j ≤ i) :
    (face (n + 1) j.castSucc).comp (face n i) =
      (face (n + 1) i.succ).comp (face n j) := by
  ext t : 1
  apply Subtype.ext
  change Fin.insertNth (α := fun _ => ℝ) j.castSucc 0
      (Fin.insertNth (α := fun _ => ℝ) i 0 t.val) =
    Fin.insertNth (α := fun _ => ℝ) i.succ 0
      (Fin.insertNth (α := fun _ => ℝ) j 0 t.val)
  have hij : i.succ.succAbove j = j.castSucc := Fin.succAbove_succ_of_le i j h
  have hji : j.castSucc.succAbove i = i.succ := Fin.succAbove_castSucc_of_le j i h
  have hp : i.predAbove j.castSucc = j := Fin.predAbove_castSucc_of_le i j h
  ext k
  refine Fin.succAboveCases j.castSucc ?_ (fun k => ?_) k
  · rw [Fin.insertNth_apply_same, ← hij, Fin.insertNth_apply_succAbove,
      Fin.insertNth_apply_same]
  · refine Fin.succAboveCases i ?_ (fun l => ?_) k
    · rw [Fin.insertNth_apply_succAbove, Fin.insertNth_apply_same, hji,
        Fin.insertNth_apply_same]
    · rw [Fin.insertNth_apply_succAbove, Fin.insertNth_apply_succAbove]
      rw [← Fin.succAbove_succAbove_succAbove_predAbove j.castSucc i l, hji, hp]
      rw [Fin.insertNth_apply_succAbove, Fin.insertNth_apply_succAbove]

/-- **The boundary of singular chains squares to zero** (`lem:dd`), by the book's route: expand
`∂ ∂ σ` as the double sum of `± σ dʲ dⁱ`, and the face identity (`face_comp`) pairs the terms
off with opposite signs (`alternating_sum_cancel`). -/
theorem bd_bd (X : Type*) [TopologicalSpace X] (n : ℕ) : bd X n ∘ₗ bd X (n + 1) = 0 := by
  classical
  apply Finsupp.lhom_ext'
  intro σ
  apply LinearMap.ext_ring
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, LinearMap.zero_apply,
    bd_single, map_sum, map_smul, Finset.smul_sum, smul_smul]
  apply alternating_sum_cancel (n + 1)
  intro i j hij
  simpa only [ContinuousMap.comp_assoc] using
    congrArg (fun g => Finsupp.single (σ.comp g) (1 : ℤ)) (face_comp n i j hij)

end Singular


/-! ## The cone construction (`prop:cone-construction`)

On ordered simplices the cone puts the vertex `v` in front, `v · σ = Fin.cons v σ`. Its faces are
the book's: `(v · σ) δ 0 = σ`, and `(v · σ) δ (i + 1) = v · (σ δ i)`. So the book's computation
`∂ (v · σ) = σ - v · ∂ σ` goes through as written. The book's singular cone on a star-shaped set
has the same faces, and its continuity is not formalised here. -/

/-- The cone `v · σ = Fin.cons v σ` on ordered `k`-simplices, extended linearly to chains. -/
noncomputable def cone {V : Type*} (v : V) (k : ℕ) :
    ((Fin (k + 1) → V) →₀ ℤ) →ₗ[ℤ] ((Fin (k + 2) → V) →₀ ℤ) :=
  Finsupp.lmapDomain ℤ ℤ fun σ => (Fin.cons v σ : Fin (k + 2) → V)

/-- The boundary of a cone on one simplex, face by face: the face missing `v` is `σ`, and the
face missing the vertex `i + 1` is `v · (σ δ i)`. -/
theorem cone_boundary_simplex {V : Type*} (v : V) (n : ℕ) (σ : Fin (n + 2) → V) :
    bd V (n + 1) (Finsupp.single (Fin.cons v σ) (1 : ℤ)) =
      Finsupp.single σ (1 : ℤ) -
        ∑ i : Fin (n + 2), ((-1 : ℤ) ^ (i : ℕ)) •
          Finsupp.single (Fin.cons v (σ ∘ Fin.succAbove i)) (1 : ℤ) := by
  classical
  unfold bd
  rw [Finsupp.linearCombination_single]
  simp only [one_smul]
  rw [Fin.sum_univ_succ]
  simp only [Fin.succAbove_zero, Fin.cons_comp_succ, Fin.val_zero, pow_zero,
    one_smul, Fin.cons_comp_succ_succAbove, Fin.val_succ,
    pow_succ, mul_neg, mul_one, neg_smul, Finset.sum_neg_distrib]
  rw [sub_eq_add_neg]
  rfl

/-- The cone formula `∂ (v · c) = c - v · ∂ c` for every chain `c` of degree at least `1`
(`prop:cone-construction`): on one simplex by `cone_boundary_simplex`, then by linearity. -/
theorem cone_boundary {V : Type*} (v : V) (n : ℕ)
    (c : (Fin (n + 2) → V) →₀ ℤ) :
    bd V (n + 1) (cone v (n + 1) c) = c - cone v n (bd V n c) := by
  classical
  have hs (σ : Fin (n + 2) → V) :
      bd V (n + 1) (cone v (n + 1) (Finsupp.single σ 1)) =
        Finsupp.single σ 1 - cone v n (bd V n (Finsupp.single σ 1)) := by
    rw [show cone v (n + 1) (Finsupp.single σ 1) =
      Finsupp.single (Fin.cons v σ) 1 by
        simp only [cone, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]]
    rw [cone_boundary_simplex]
    congr 1
    simp only [bd, Finsupp.linearCombination_single, one_smul,
      map_sum, map_smul, cone, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]
  induction c using Finsupp.induction_linear with
  | zero => simp only [map_zero, sub_zero]
  | add c d hc hd =>
      simp only [map_add, hc, hd]
      abel
  | single σ a =>
      have he : Finsupp.single σ a = a • Finsupp.single σ (1 : ℤ) := by
        simp only [Finsupp.smul_single, smul_eq_mul, mul_one]
      rw [he]
      simp only [map_smul, hs, smul_sub]

/-- The ordered chain complex of all simplices on a nonempty `V` has no homology in degrees at
least `1`, by the last step of `prop:cone-construction`: a cycle `z` of degree at least `1` is
the boundary of its cone, `∂ (v · z) = z - v · ∂ z = z` (`cone_boundary`). -/
theorem acyclic {V : Type*} (v : V) (n : ℕ) : Subsingleton (H (bd V (n + 1)) (bd V n)) := by
  classical
  change Subsingleton ((LinearMap.ker (bd V n)) ⧸
    (LinearMap.range (bd V (n + 1))).comap (LinearMap.ker (bd V n)).subtype)
  apply Submodule.Quotient.subsingleton_iff.mpr
  apply eq_top_iff.mpr
  intro z _
  change (z : (Fin (n + 2) → V) →₀ ℤ) ∈ LinearMap.range (bd V (n + 1))
  refine LinearMap.mem_range.mpr ⟨cone v (n + 1) z.val, ?_⟩
  have hz0 : bd V n z.val = 0 := z.property
  simpa only [hz0, map_zero, sub_zero] using cone_boundary v n z.val

/-- The point in degrees at least `1` (`prop:homology-point`): on one vertex there is exactly one
ordered simplex in each degree, as in the book's singular complex of a point, and the homology
vanishes. By the cone (`acyclic`), not by the book's explicit complex. -/
theorem point_acyclic (n : ℕ) : Subsingleton (H (bd Unit (n + 1)) (bd Unit n)) :=
  acyclic () n

/-! ## `H₀` through the augmentation (`prop:H0`) -/

/-- The augmentation `ε : C₀ → ℤ`, `ε (∑ m_k x_k) = ∑ m_k` (`prop:H0`). -/
noncomputable def aug (V : Type*) : ((Fin 1 → V) →₀ ℤ) →ₗ[ℤ] ℤ :=
  Finsupp.linearCombination ℤ fun _ => (1 : ℤ)

/-- On an edge, `∂ (m · (a, b)) = m · b - m · a`. -/
theorem bd_zero_single {V : Type*} (σ : Fin 2 → V) (m : ℤ) :
    bd V 0 (Finsupp.single σ m) =
      Finsupp.single (fun _ : Fin 1 => σ 1) m - Finsupp.single (fun _ : Fin 1 => σ 0) m := by
  classical
  have h0 : σ ∘ Fin.succ = (fun _ : Fin 1 => σ 1) := by
    funext j
    fin_cases j
    rfl
  have h1 : σ ∘ Fin.succAbove 1 = (fun _ : Fin 1 => σ 0) := by
    funext j
    fin_cases j
    simp
  simpa [bd, Finsupp.linearCombination_single, Fin.sum_univ_two, h0, h1, sub_eq_add_neg]

/-- The augmentation kills the boundaries: `ε (∂ (a, b)) = ε (b - a) = 0`. -/
theorem aug_comp_bd (V : Type*) : (aug V).comp (bd V 0) = 0 := by
  apply Finsupp.lhom_ext
  intro σ m
  simp [LinearMap.comp_apply, bd_zero_single, aug]

/-- With a vertex `v` fixed, `c - ε(c) · v` is a boundary: `m · x - m · v = ∂ (m · (v, x))`, the
edge `(v, x)` playing the book's path from `v` to `x`. -/
theorem sub_aug_mem_range {V : Type*} (v : V) (c : (Fin 1 → V) →₀ ℤ) :
    c - Finsupp.single (fun _ : Fin 1 => v) (aug V c) ∈ LinearMap.range (bd V 0) := by
  classical
  induction c using Finsupp.induction_linear with
  | zero =>
      simp only [map_zero, Finsupp.single_zero, sub_zero]
      exact Submodule.zero_mem _
  | add c d hc hd =>
      have h := (LinearMap.range (bd V 0)).add_mem hc hd
      simpa only [map_add, Finsupp.single_add, sub_add_sub_comm] using h
  | single σ m =>
      have haug : aug V (Finsupp.single σ m) = m := by
        simp [aug, Finsupp.linearCombination_single]
      rw [haug]
      let τ : Fin 2 → V := fun i => if i = 0 then v else σ 0
      refine ⟨Finsupp.single τ m, ?_⟩
      rw [bd_zero_single]
      have hσ : (fun _ : Fin 1 => σ 0) = σ := by
        funext j
        fin_cases j
        rfl
      have h10 : (1 : Fin 2) ≠ 0 := by decide
      simp only [τ, h10, if_false, if_true, hσ]

/-- `H₀ ≅ ℤ` through the augmentation on a nonempty `V` (`prop:H0`), by the book's route. Every
`0`-chain is a cycle, so `H₀ = C₀ / im ∂`. The augmentation is onto, it kills the boundaries
(`aug_comp_bd`), and its kernel is the boundaries, since
`∑ m_k x_k - (∑ m_k) v = ∂ (∑ m_k (v, x_k))` (`sub_aug_mem_range`): the edges `(v, x_k)` play the
book's paths `γ_k` from `v` to `x_k`. -/
theorem H0_equiv_int {V : Type*} (v : V) :
    ∃ e : (((Fin 1 → V) →₀ ℤ) ⧸ LinearMap.range (bd V 0)) ≃ₗ[ℤ] ℤ,
      ∀ c, e (Submodule.Quotient.mk c) = aug V c := by
  have hker : LinearMap.range (bd V 0) = LinearMap.ker (aug V) := by
    apply le_antisymm
    · exact LinearMap.range_le_ker_iff.mpr (aug_comp_bd V)
    · intro c hc
      have hc0 : aug V c = 0 := LinearMap.mem_ker.mp hc
      simpa only [hc0, Finsupp.single_zero, sub_zero] using sub_aug_mem_range v c
  have hs : Function.Surjective (aug V) := by
    intro z
    refine ⟨Finsupp.single (fun _ : Fin 1 => v) z, ?_⟩
    simp [aug, Finsupp.linearCombination_single]
  refine ⟨(Submodule.quotEquivOfEq _ _ hker).trans
    ((aug V).quotKerEquivOfSurjective hs), ?_⟩
  intro c
  simp

/-- The point's `H₀ ≅ ℤ` (`prop:homology-point`), the case of one vertex. -/
theorem point_H0 :
    ∃ e : (((Fin 1 → Unit) →₀ ℤ) ⧸ LinearMap.range (bd Unit 0)) ≃ₗ[ℤ] ℤ,
      ∀ c, e (Submodule.Quotient.mk c) = aug Unit c :=
  H0_equiv_int ()

/-! ## Singular `H₀` of a path-connected space (`prop:H0`)

The book's `prop:H0` is about singular chains. Its route: the augmentation is onto and kills the
boundaries, and a path from `x` to `σ`, read on `Δ¹`, is a singular `1`-simplex with boundary
`σ - x` (`Singular.single_sub_single_mem_range`). -/

namespace Singular

/-- The augmentation `ε : C₀(X) → ℤ`, `ε (∑ m_k σ_k) = ∑ m_k` (`prop:H0`), on singular
`0`-chains. -/
noncomputable def aug (X : Type*) [TopologicalSpace X] : (C(Simplex 0, X) →₀ ℤ) →ₗ[ℤ] ℤ :=
  Finsupp.linearCombination ℤ fun _ => (1 : ℤ)

/-- The augmentation kills the boundaries: `ε (∂ η) = ε (η ∘ d⁰ - η ∘ d¹) = 1 - 1 = 0`. -/
theorem aug_comp_bd (X : Type*) [TopologicalSpace X] : (aug X).comp (bd X 0) = 0 := by
  apply Finsupp.lhom_ext
  intro σ a
  simp [bd, aug, Finsupp.linearCombination_single, Fin.sum_univ_two]

/-- The standard `0`-simplex is a point. -/
theorem simplex_zero_eq (s t : Simplex 0) : s = t := by
  have hs : s.val 0 = 1 := by simpa using s.property.2
  have ht : t.val 0 = 1 := by simpa using t.property.2
  apply Subtype.ext
  funext i
  fin_cases i
  exact hs.trans ht.symm

/-- In a path-connected space two points differ by a boundary, by the book's `∂ γ = γ(1) - γ(0)`:
a path `p` from `τ` to `σ`, read on `Δ¹` through the second coordinate `t ↦ t₁`, is a singular
`1`-simplex `η` with `η ∘ d⁰ = σ` and `η ∘ d¹ = τ`, so `∂ η = σ - τ`. -/
theorem single_sub_single_mem_range (X : Type*) [TopologicalSpace X] [PathConnectedSpace X]
    (σ τ : C(Simplex 0, X)) :
    Finsupp.single σ (1 : ℤ) - Finsupp.single τ (1 : ℤ) ∈ LinearMap.range (bd X 0) := by
  classical
  let v : Simplex 0 := ⟨fun _ => 1, by simp [Simplex]⟩
  let p : Path (τ v) (σ v) := PathConnectedSpace.somePath (τ v) (σ v)
  let q : C(Simplex 1, Set.Icc (0 : ℝ) 1) :=
    { toFun := fun t => ⟨t.val 1, by
        constructor
        · exact t.property.1 1
        · have h := t.property.2
          change (∑ i : Fin 2, t.val i) = 1 at h
          rw [Fin.sum_univ_two] at h
          have h0 := t.property.1 0
          linarith⟩
      continuous_toFun := by
        apply Continuous.subtype_mk
        exact (continuous_apply 1).comp continuous_subtype_val }
  let η : C(Simplex 1, X) := p.toContinuousMap.comp q
  have h₀ : η.comp (face 0 0) = σ := by
    ext t
    have ht : t = v := simplex_zero_eq t v
    subst t
    simp [η, q, v, face]
  have h₁ : η.comp (face 0 1) = τ := by
    ext t
    have ht : t = v := simplex_zero_eq t v
    subst t
    simp [η, q, v, face, Fin.insertNth]
  refine ⟨Finsupp.single η (1 : ℤ), ?_⟩
  simp [bd, Finsupp.linearCombination_single, Fin.sum_univ_two, h₀, h₁, sub_eq_add_neg]

/-- `c - ε(c) τ` is a boundary for every singular `0`-chain `c`, the book's
`∂ (∑ m_k γ_k) = ∑ m_k x_k - (∑ m_k) x`: by linearity from `single_sub_single_mem_range`. -/
theorem sub_aug_mem_range (X : Type*) [TopologicalSpace X] [PathConnectedSpace X]
    (c : C(Simplex 0, X) →₀ ℤ) (τ : C(Simplex 0, X)) :
    c - (aug X c) • Finsupp.single τ (1 : ℤ) ∈ LinearMap.range (bd X 0) := by
  classical
  induction c using Finsupp.induction_linear with
  | zero =>
      simpa only [map_zero, zero_smul, sub_zero] using
        (LinearMap.range (bd X 0)).zero_mem
  | add f g hf hg =>
      simpa only [map_add, add_smul, sub_add_sub_comm] using
        (LinearMap.range (bd X 0)).add_mem hf hg
  | single σ a =>
      have h := (LinearMap.range (bd X 0)).smul_mem a
        (single_sub_single_mem_range X σ τ)
      simpa [aug, Finsupp.linearCombination_single, smul_sub,
        Finsupp.smul_single] using h

/-- **`H₀ ≅ ℤ` for a path-connected space** (`prop:H0`), through the augmentation, by the book's
route. Every `0`-chain is a cycle, so `H₀ = C₀ / im ∂`. The augmentation is onto, a point `x` being
a singular `0`-simplex; it kills the boundaries (`aug_comp_bd`); and its kernel is the boundaries
(`sub_aug_mem_range`). Mathlib's `PathConnectedSpace` includes `Nonempty`, the book's `X ≠ ∅`. The
proposition's last sentence, `H₀` free on the path components, is not formalised here. -/
theorem H0_equiv_int (X : Type*) [TopologicalSpace X] [PathConnectedSpace X] :
    ∃ e : ((C(Simplex 0, X) →₀ ℤ) ⧸ LinearMap.range (bd X 0)) ≃ₗ[ℤ] ℤ,
      ∀ c, e (Submodule.Quotient.mk c) = aug X c := by
  classical
  let x : X := Classical.choice (inferInstance : Nonempty X)
  let τ : C(Simplex 0, X) := ContinuousMap.const _ x
  have hsurj : Function.Surjective (aug X) := by
    intro a
    refine ⟨Finsupp.single τ a, ?_⟩
    simp [aug, Finsupp.linearCombination_single]
  have hker : LinearMap.range (bd X 0) = LinearMap.ker (aug X) := by
    ext c
    constructor
    · rintro ⟨d, rfl⟩
      change aug X (bd X 0 d) = 0
      have h := LinearMap.congr_fun (aug_comp_bd X) d
      simpa only [LinearMap.comp_apply, LinearMap.zero_apply] using h
    · intro hc
      have hc0 : aug X c = 0 := hc
      have h := sub_aug_mem_range X c τ
      simpa only [hc0, zero_smul, sub_zero] using h
  let e := (Submodule.quotEquivOfEq _ _ hker).trans
    ((aug X).quotKerEquivOfSurjective hsurj)
  refine ⟨e, ?_⟩
  intro c
  simp [e]

end Singular

/-! ## `b₀` of a graph is its number of components (`ex:graph-cycles`) -/

/-- The boundary `∂ : ℚ^E → ℚ^V` of a finite graph with tail and head maps `s t : E → V`:
`∂ e = t e - s e` (`ex:graph-cycles`, with coefficients in `ℚ`). -/
noncomputable def graphBd {V E : Type*} [Fintype E] [DecidableEq V] (s t : E → V) :
    (E → ℚ) →ₗ[ℚ] (V → ℚ) :=
  ∑ e : E, (LinearMap.proj e : (E → ℚ) →ₗ[ℚ] ℚ).smulRight
    ((Pi.single (t e) (1 : ℚ) - Pi.single (s e) (1 : ℚ) : V → ℚ))

theorem graphBd_single {V E : Type*} [Fintype E] [DecidableEq V] [DecidableEq E]
    (s t : E → V) (e : E) :
    graphBd s t (Pi.single e (1 : ℚ)) =
      Pi.single (t e) (1 : ℚ) - Pi.single (s e) (1 : ℚ) := by
  classical
  simp [graphBd, LinearMap.sum_apply, LinearMap.smulRight_apply, Pi.single_apply]

-- (part of a homework solution; it appears here after 12 November 2026)






















-- (part of a homework solution; it appears here after 12 November 2026)












-- (part of a homework solution; it appears here after 12 November 2026)



































/-- `b₀ = c` (Example 9.18, `ex:graph-cycles`). Its proof appears here after 12 November 2026, when
the homework is due.


-/
theorem b0_eq_components {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (s t : E → V) :
    Module.finrank ℚ ((V → ℚ) ⧸ LinearMap.range (graphBd s t)) =
      Nat.card (Quot (fun a b : V => ∃ e, s e = a ∧ t e = b)) := by sorry -- the proof appears here after 12 November 2026, when the homework is due


























/-! ## `b₁` of a graph (`ex:graph-cycles`, `exr-9-graph`) -/

/-- Two vertices joined by a chain of edges differ by a boundary: `v - u ∈ im ∂`. -/
theorem graphBd_eqvGen_mem_range {V E : Type*} [Fintype E] [DecidableEq V]
    (s t : E → V) {u v : V}
    (h : Relation.EqvGen (fun a b => ∃ e, s e = a ∧ t e = b) u v) :
    Pi.single v (1 : ℚ) - Pi.single u (1 : ℚ) ∈ LinearMap.range (graphBd s t) := by
  classical
  induction h with
  | rel a b hab =>
      rcases hab with ⟨e, rfl, rfl⟩
      exact ⟨Pi.single e (1 : ℚ), graphBd_single s t e⟩
  | refl a =>
      simpa only [sub_self] using (LinearMap.range (graphBd s t)).zero_mem
  | symm a b hab ih =>
      simpa only [neg_sub] using (LinearMap.range (graphBd s t)).neg_mem ih
  | trans a b c hab hbc ihab ihbc =>
      have hsum := (LinearMap.range (graphBd s t)).add_mem ihbc ihab
      convert hsum using 1 <;> abel

/-- The augmentation `ε : ℚ^V → ℚ`, the sum of the coefficients (`exr-9-reduced`). -/
noncomputable def vertexSum (V : Type*) [Fintype V] : (V → ℚ) →ₗ[ℚ] ℚ :=
  ∑ v : V, (LinearMap.proj v : (V → ℚ) →ₗ[ℚ] ℚ)

/-- For a connected graph, `im ∂ = ker ε`: every `f` with `ε f = 0` is `∑ f v (v - r)`. -/
theorem graphBd_range_eq_ker_vertexSum {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (s t : E → V) (r : V)
    (hconn : ∀ u v : V, Relation.EqvGen (fun a b => ∃ e, s e = a ∧ t e = b) u v) :
    LinearMap.range (graphBd s t) = LinearMap.ker (vertexSum V) := by
  classical
  have hsum (f : V → ℚ) : vertexSum V f = ∑ v, f v := by
    simp [vertexSum, LinearMap.sum_apply]
  have hsingle (v : V) : vertexSum V (Pi.single v (1 : ℚ)) = 1 := by
    rw [hsum]
    simp
  apply le_antisymm
  · rintro f ⟨x, rfl⟩
    rw [LinearMap.mem_ker]
    change vertexSum V ((graphBd s t) x) = 0
    simp [graphBd, LinearMap.sum_apply, LinearMap.smulRight_apply,
      LinearMap.proj_apply, map_sum, map_smul, map_sub, hsingle]
  · intro f hf
    have hfzero : ∑ v, f v = 0 := by
      simpa only [LinearMap.mem_ker, hsum] using hf
    have hmem : (∑ v : V, f v • (Pi.single v (1 : ℚ) - Pi.single r (1 : ℚ))) ∈
        LinearMap.range (graphBd s t) := by
      apply Submodule.sum_mem
      intro v hv
      exact Submodule.smul_mem _ _ (graphBd_eqvGen_mem_range s t (hconn r v))
    have heq : (∑ v : V, f v • (Pi.single v (1 : ℚ) - Pi.single r (1 : ℚ))) = f := by
      rw [Finset.sum_congr rfl (fun v _ => smul_sub (f v) _ _), Finset.sum_sub_distrib,
        ← Finset.sum_smul, hfzero, zero_smul, sub_zero]
      ext w
      simp [Pi.single_apply]
    rw [heq] at hmem
    exact hmem

/-- `ε` is onto, so `dim ker ε = |V| - 1`. -/
theorem vertexSum_ker_finrank (V : Type*) [Fintype V] [DecidableEq V] (r : V) :
    Module.finrank ℚ (LinearMap.ker (vertexSum V)) + 1 = Fintype.card V := by
  have hsurj : Function.Surjective (vertexSum V) := by
    intro q
    refine ⟨Pi.single r q, ?_⟩
    simp [vertexSum, LinearMap.sum_apply, LinearMap.proj_apply]
  have hrange : LinearMap.range (vertexSum V) = ⊤ :=
    LinearMap.range_eq_top.mpr hsurj
  have hdim := LinearMap.finrank_range_add_finrank_ker (vertexSum V)
  rw [hrange] at hdim
  simpa [Module.finrank_fintype_fun_eq_card, Nat.add_comm] using hdim

/-- `b₁ = |E| - |V| + 1` for a non-empty connected finite graph (`ex:graph-cycles`, its last
display with `c = 1`), with coefficients in `ℚ` (`def:betti-euler`). The route differs a little
from the book's: here `im ∂` is shown to be the kernel of the augmentation `ε`, since any two
vertices are joined by a chain of edges, so `dim im ∂ = |V| - 1`, and rank-nullity gives `b₁`.
The book gets `rank im ∂ = |V| - c` from `b₀ = c` instead, as in
`b1_eq_edges_sub_vertices_add_components`. -/
theorem b1_eq_edges_sub_vertices_add_one {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (s t : E → V) [Nonempty V]
    (hconn : ∀ u v : V, Relation.EqvGen (fun a b => ∃ e, s e = a ∧ t e = b) u v) :
    (Module.finrank ℚ (LinearMap.ker (graphBd s t)) : ℤ) =
      Fintype.card E - Fintype.card V + 1 := by
  classical
  let r : V := Classical.choice (inferInstance : Nonempty V)
  have hdim := LinearMap.finrank_range_add_finrank_ker (graphBd s t)
  rw [Module.finrank_fintype_fun_eq_card,
    graphBd_range_eq_ker_vertexSum s t r hconn] at hdim
  have hsum := vertexSum_ker_finrank V r
  have hdimZ : (Module.finrank ℚ (LinearMap.ker (vertexSum V)) : ℤ) +
      (Module.finrank ℚ (LinearMap.ker (graphBd s t)) : ℤ) = (Fintype.card E : ℤ) := by
    exact_mod_cast hdim
  have hsumZ : (Module.finrank ℚ (LinearMap.ker (vertexSum V)) : ℤ) + 1 =
      (Fintype.card V : ℤ) := by
    exact_mod_cast hsum
  omega

/-- `b₁ = |E| - |V| + c` for a finite graph with `c` components (`exr-9-graph`), with
coefficients in `ℚ` (`def:betti-euler`), by the book's route (`ex:graph-cycles`): rank-nullity
for `∂ : ℚ^E → ℚ^V` and for the quotient `H₀ = ℚ^V / im ∂`, with `b₀ = c`
(`b0_eq_components`). That `ker ∂` is free over `ℤ` is not formalised here. -/
theorem b1_eq_edges_sub_vertices_add_components {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq V] (s t : E → V) :
    (Module.finrank ℚ (LinearMap.ker (graphBd s t)) : ℤ) =
      Fintype.card E - Fintype.card V +
        Nat.card (Quot (fun a b : V => ∃ e, s e = a ∧ t e = b)) := by
  have h1 := LinearMap.finrank_range_add_finrank_ker (graphBd s t)
  have h2 := Submodule.finrank_quotient_add_finrank (LinearMap.range (graphBd s t))
  rw [Module.finrank_fintype_fun_eq_card] at h1 h2
  rw [b0_eq_components] at h2
  omega

/-! ## A graph's `H₀` over `ℤ` (`exr-9-graph`)

`coker ∂ ≅ ℤ^c` for a graph, compared with `prop:H0`: a vertex goes to its component, and the class
of a vertex depends only on its component, since the ends of an edge `e` differ by `∂ e`. -/

namespace GraphZ

/-- The boundary `∂ : ℤ[E] → ℤ[V]` of a graph with source and target maps `s t : E → V`,
`∂ e = t e - s e`, over `ℤ`. -/
noncomputable def graphBd {V E : Type*} (s t : E → V) : (E →₀ ℤ) →ₗ[ℤ] (V →₀ ℤ) :=
  Finsupp.linearCombination ℤ fun e => Finsupp.single (t e) (1 : ℤ) - Finsupp.single (s e) 1

/-- `a` and `b` are the ends of an edge from `a` to `b`. The quotient `Quot (adj s t)` identifies
the ends of every edge: its points are the components of the graph. -/
def adj {V E : Type*} (s t : E → V) (a b : V) : Prop := ∃ e, s e = a ∧ t e = b

/-- **A graph's `H₀ = coker ∂` is free abelian on its components** (Exercise 9.E1, `exr-9-graph`;
Homework 9.H10, `hw-9-10`). Its proof appears here after 12 November 2026, when the homework is
due.

-/
theorem H0_equiv {V E : Type*} (s t : E → V) :
    ∃ e : ((V →₀ ℤ) ⧸ LinearMap.range (graphBd s t)) ≃ₗ[ℤ] (Quot (adj s t) →₀ ℤ),
      ∀ v, e (Submodule.Quotient.mk (Finsupp.single v 1)) = Finsupp.single (Quot.mk _ v) 1 := by sorry -- the proof appears here after 12 November 2026, when the homework is due
















































end GraphZ

/-! ## The Euler number from the chain groups (`rem:euler-chain-groups`, `hw-9-9`) -/

/-- The cycles of `K 0 ← K 1 ← K 2 ← ⋯`, with `d n : K (n + 1) → K n`: `Z 0 = K 0` and
`Z (n + 1) = ker (d n)`. -/
def natCycles {F : Type*} [Field F] {K : ℕ → Type*} [∀ n, AddCommGroup (K n)]
    [∀ n, Module F (K n)] (d : ∀ n, K (n + 1) →ₗ[F] K n) : ∀ p, Submodule F (K p)
  | 0 => ⊤
  | n + 1 => LinearMap.ker (d n)

/-- The homology `H p = Z p / B p` of such a complex, the boundaries `B p = im (d p)` taken
inside `Z p`. -/
abbrev natHomology {F : Type*} [Field F] {K : ℕ → Type*} [∀ n, AddCommGroup (K n)]
    [∀ n, Module F (K n)] (d : ∀ n, K (n + 1) →ₗ[F] K n) (p : ℕ) : Type _ :=
  ↥(natCycles d p) ⧸ (LinearMap.range (d p)).comap (natCycles d p).subtype

-- (part of a homework solution; it appears here after 12 November 2026)
















-- (part of a homework solution; it appears here after 12 November 2026)























/-- **The Euler number is computed from the chain groups** (Definition 9.15, `def:betti-euler`;
Homework 9.H9, `hw-9-9`; Remark 9.16, `rem:euler-chain-groups`). Its proof appears here after
12 November 2026, when the homework is due.




-/
theorem euler_number_eq_alternating_dim {F : Type*} [Field F] {K : ℕ → Type*}
    [∀ n, AddCommGroup (K n)] [∀ n, Module F (K n)] [∀ n, FiniteDimensional F (K n)]
    (d : ∀ n, K (n + 1) →ₗ[F] K n) (hd : ∀ n, d n ∘ₗ d (n + 1) = 0)
    (N : ℕ) (hN : ∀ p, N < p → Subsingleton (K p)) :
    ∑ p ∈ Finset.range (N + 1), (-1 : ℤ) ^ p * (Module.finrank F (K p) : ℤ) =
      ∑ p ∈ Finset.range (N + 1), (-1 : ℤ) ^ p * (Module.finrank F (natHomology d p) : ℤ) := by sorry -- the proof appears here after 12 November 2026, when the homework is due






































/-! ## The zigzag lemma: the connecting map (`hw-9-4`)

Chain complexes indexed by `ℤ`, with `dA n : A (n + 1) → A n`; degrees are written `n + 1 + 1`
rather than `n + 2`, so that the types agree by definition. -/

-- (part of a homework solution; it appears here after 12 November 2026)





































-- (part of a homework solution; it appears here after 12 November 2026)



































-- (part of a homework solution; it appears here after 12 November 2026)












































/-- **The connecting map of the zigzag lemma** (Homework 9.H4, `hw-9-4`). Its proof appears here
after 12 November 2026, when the homework is due.





-/
theorem connecting_map_exists_unique {R : Type*} [Ring R] {A B C : ℤ → Type*}
    [∀ n, AddCommGroup (A n)] [∀ n, Module R (A n)]
    [∀ n, AddCommGroup (B n)] [∀ n, Module R (B n)]
    [∀ n, AddCommGroup (C n)] [∀ n, Module R (C n)]
    (dA : ∀ n, A (n + 1) →ₗ[R] A n) (dB : ∀ n, B (n + 1) →ₗ[R] B n)
    (dC : ∀ n, C (n + 1) →ₗ[R] C n)
    (hdA : ∀ n, dA n ∘ₗ dA (n + 1) = 0) (hdB : ∀ n, dB n ∘ₗ dB (n + 1) = 0)
    (hdC : ∀ n, dC n ∘ₗ dC (n + 1) = 0)
    (i : ∀ n, A n →ₗ[R] B n) (j : ∀ n, B n →ₗ[R] C n)
    (hi : ∀ n, dB n ∘ₗ i (n + 1) = i n ∘ₗ dA n)
    (hj : ∀ n, dC n ∘ₗ j (n + 1) = j n ∘ₗ dB n)
    (hinj : ∀ n, Function.Injective (i n))
    (hex : ∀ n, LinearMap.range (i n) = LinearMap.ker (j n))
    (hsurj : ∀ n, Function.Surjective (j n)) (n : ℤ) :
    ∃! δ : H (dC (n + 1 + 1)) (dC (n + 1)) →ₗ[R] H (dA (n + 1)) (dA n),
      ∀ (z : LinearMap.ker (dC (n + 1))) (b : B (n + 1 + 1)) (a : LinearMap.ker (dA n)),
        j (n + 1 + 1) b = z → i (n + 1) a = dB (n + 1) b →
          δ (cls (dC (n + 1 + 1)) (dC (n + 1)) z) = cls (dA (n + 1)) (dA n) a := by sorry -- the proof appears here after 12 November 2026, when the homework is due







































/-! ## The zigzag lemma: exactness (`hw-9-4`) -/

-- (part of a homework solution; it appears here after 12 November 2026)





-- (part of a homework solution; it appears here after 12 November 2026)




-- (part of a homework solution; it appears here after 12 November 2026)



















-- (part of a homework solution; it appears here after 12 November 2026)






















/-- **The zigzag lemma** (Homework 9.H4, `hw-9-4`). Its proof appears here after 12 November 2026,
when the homework is due.







-/
theorem zigzag_exact {R : Type*} [Ring R] {A B C : ℤ → Type*}
    [∀ n, AddCommGroup (A n)] [∀ n, Module R (A n)]
    [∀ n, AddCommGroup (B n)] [∀ n, Module R (B n)]
    [∀ n, AddCommGroup (C n)] [∀ n, Module R (C n)]
    (dA : ∀ n, A (n + 1) →ₗ[R] A n) (dB : ∀ n, B (n + 1) →ₗ[R] B n)
    (dC : ∀ n, C (n + 1) →ₗ[R] C n)
    (hdA : ∀ n, dA n ∘ₗ dA (n + 1) = 0) (hdB : ∀ n, dB n ∘ₗ dB (n + 1) = 0)
    (hdC : ∀ n, dC n ∘ₗ dC (n + 1) = 0)
    (i : ∀ n, A n →ₗ[R] B n) (j : ∀ n, B n →ₗ[R] C n)
    (hi : ∀ n, dB n ∘ₗ i (n + 1) = i n ∘ₗ dA n)
    (hj : ∀ n, dC n ∘ₗ j (n + 1) = j n ∘ₗ dB n)
    (hinj : ∀ n, Function.Injective (i n))
    (hex : ∀ n, LinearMap.range (i n) = LinearMap.ker (j n))
    (hsurj : ∀ n, Function.Surjective (j n)) (n : ℤ)
    (iₛ₂ : H (dA (n + 1 + 1)) (dA (n + 1)) →ₗ[R] H (dB (n + 1 + 1)) (dB (n + 1)))
    (jₛ₂ : H (dB (n + 1 + 1)) (dB (n + 1)) →ₗ[R] H (dC (n + 1 + 1)) (dC (n + 1)))
    (δ : H (dC (n + 1 + 1)) (dC (n + 1)) →ₗ[R] H (dA (n + 1)) (dA n))
    (iₛ₁ : H (dA (n + 1)) (dA n) →ₗ[R] H (dB (n + 1)) (dB n))
    (hi₂ : ∀ (x : LinearMap.ker (dA (n + 1))) (y : LinearMap.ker (dB (n + 1))),
      (y : B (n + 1 + 1)) = i (n + 1 + 1) x →
        iₛ₂ (cls (dA (n + 1 + 1)) (dA (n + 1)) x) = cls (dB (n + 1 + 1)) (dB (n + 1)) y)
    (hj₂ : ∀ (y : LinearMap.ker (dB (n + 1))) (z : LinearMap.ker (dC (n + 1))),
      (z : C (n + 1 + 1)) = j (n + 1 + 1) y →
        jₛ₂ (cls (dB (n + 1 + 1)) (dB (n + 1)) y) = cls (dC (n + 1 + 1)) (dC (n + 1)) z)
    (hδ : ∀ (z : LinearMap.ker (dC (n + 1))) (b : B (n + 1 + 1)) (a : LinearMap.ker (dA n)),
      j (n + 1 + 1) b = z → i (n + 1) a = dB (n + 1) b →
        δ (cls (dC (n + 1 + 1)) (dC (n + 1)) z) = cls (dA (n + 1)) (dA n) a)
    (hi₁ : ∀ (x : LinearMap.ker (dA n)) (y : LinearMap.ker (dB n)),
      (y : B (n + 1)) = i (n + 1) x →
        iₛ₁ (cls (dA (n + 1)) (dA n) x) = cls (dB (n + 1)) (dB n) y) :
    LinearMap.range iₛ₂ = LinearMap.ker jₛ₂ ∧ LinearMap.range jₛ₂ = LinearMap.ker δ ∧
      LinearMap.range δ = LinearMap.ker iₛ₁ := by sorry -- the proof appears here after 12 November 2026, when the homework is due






































































































end Week09Homology
