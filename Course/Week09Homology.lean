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
* For a finite graph, `dim (ℚ^V / im ∂)` is the number of components, `b₀ = c`
  (`ex:graph-cycles`): the functionals that kill `im ∂` are the functions constant along
  edges, that is, the functions on the components (`b0_eq_components`).
* For a finite graph, `b₁ = |E| - |V| + c` (`exr-9-graph`), by rank-nullity from `b₀ = c`
  (`b1_eq_edges_sub_vertices_add_components`).
* For any graph, over `ℤ`, `H₀ = coker ∂` is free abelian on the components, `ℤ^c`
  (`exr-9-graph`, `GraphZ.H0_equiv`), by the route of `prop:H0` one component at a time: a vertex
  goes to its component, and the ends of an edge `e` differ by `∂ e`.
* The Euler number is computed from the chain groups (`rem:euler-chain-groups`, `hw-9-9`): for a
  bounded complex of finite-dimensional vector spaces, `∑ (-1)^p dim K p = ∑ (-1)^p dim H p`
  (`euler_number_eq_alternating_dim`).
* The zigzag lemma's connecting map (`hw-9-4`): for chain maps `0 → A → B → C → 0`, short exact
  in each degree, there is exactly one linear `δ : H_{n+2}(C) → H_{n+1}(A)` with `δ [z] = [a]`
  whenever `j b = z` and `i a = ∂ b` (`connecting_map_exists_unique`); with it,
  `H_{n+2}(A) → H_{n+2}(B) → H_{n+2}(C) → H_{n+1}(A) → H_{n+1}(B)` is exact (`zigzag_exact`).

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

/-- A functional on `ℚ^V` kills `im ∂` if and only if it takes the same value at the two ends of
every edge. -/
theorem graphBd_annihilator_iff {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (s t : E → V) (φ : Module.Dual ℚ (V → ℚ)) :
    φ ∈ (LinearMap.range (graphBd s t)).dualAnnihilator ↔
      ∀ e, φ (Pi.single (s e) (1 : ℚ)) = φ (Pi.single (t e) (1 : ℚ)) := by
  classical
  rw [Submodule.mem_dualAnnihilator]
  constructor
  · intro h e
    have he := h (graphBd s t (Pi.single e (1 : ℚ))) ⟨_, rfl⟩
    rw [graphBd_single, map_sub] at he
    exact (sub_eq_zero.mp he).symm
  · intro h y hy
    rcases hy with ⟨x, rfl⟩
    have hcomp : φ.comp (graphBd s t) = 0 := by
      apply (Pi.basisFun ℚ E).ext
      intro e
      simp only [LinearMap.comp_apply, Pi.basisFun_apply, graphBd_single,
        map_sub, h e, sub_self, LinearMap.zero_apply]
    have hx := congrArg (fun f : (E → ℚ) →ₗ[ℚ] ℚ => f x) hcomp
    exact hx

/-- The functions on `V` that take the same value at the two ends of every edge. -/
def edgeConstant {V E : Type*} (s t : E → V) : Submodule ℚ (V → ℚ) where
  carrier := {f | ∀ e, f (s e) = f (t e)}
  zero_mem' := by intro e; rfl
  add_mem' := by
    intro f g hf hg e
    change f (s e) + g (s e) = f (t e) + g (t e)
    rw [hf e, hg e]
  smul_mem' := by
    intro c f hf e
    change c • f (s e) = c • f (t e)
    rw [hf e]

/-- They are the functions on the components, so their dimension is the number of components.
For the relation `r a b`, "an edge runs from `a` to `b`", the quotient `Quot r` is the set of
classes of the equivalence relation that `r` generates: the components. -/
theorem edgeConstant_finrank {V E : Type*} [Fintype V] [Fintype E] (s t : E → V) :
    Module.finrank ℚ (edgeConstant s t) =
      Nat.card (Quot (fun a b : V => ∃ e, s e = a ∧ t e = b)) := by
  classical
  let r : V → V → Prop := fun a b => ∃ e, s e = a ∧ t e = b
  let C := Quot r
  letI : Fintype C := Fintype.ofFinite C
  let equiv : (C → ℚ) ≃ₗ[ℚ] edgeConstant s t :=
    { toFun := fun f => ⟨fun v => f (Quot.mk r v), by
        intro e
        exact congrArg f (Quot.sound ⟨e, rfl, rfl⟩)⟩
      invFun := fun f => Quot.lift f.val (by
        rintro a b ⟨e, ha, hb⟩
        subst a
        subst b
        exact f.property e)
      left_inv := by
        intro f
        funext q
        induction q using Quot.inductionOn
        rfl
      right_inv := by
        intro f
        apply Subtype.ext
        rfl
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  calc
    Module.finrank ℚ (edgeConstant s t) = Module.finrank ℚ (C → ℚ) :=
      equiv.finrank_eq.symm
    _ = Fintype.card C := Module.finrank_fintype_fun_eq_card ℚ
    _ = Nat.card C := (Nat.card_eq_fintype_card).symm

/-- `b₀ = c` (`ex:graph-cycles`): for a finite graph, `dim (ℚ^V / im ∂)` is the number of its
components. The route is dual to the book's: the dual of `ℚ^V / im ∂` is the annihilator of
`im ∂`, which consists of the functions constant along edges (`graphBd_annihilator_iff`), that is,
the functions on the components (`edgeConstant_finrank`). The book maps `H₀` onto `ℤ^c` instead,
and leaves injectivity to `hw-9-10`. -/
theorem b0_eq_components {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (s t : E → V) :
    Module.finrank ℚ ((V → ℚ) ⧸ LinearMap.range (graphBd s t)) =
      Nat.card (Quot (fun a b : V => ∃ e, s e = a ∧ t e = b)) := by
  classical
  let W := LinearMap.range (graphBd s t)
  let e := LinearEquiv.piRing ℚ ℚ V ℚ
  have hm (φ : Module.Dual ℚ (V → ℚ)) :
      φ ∈ W.dualAnnihilator ↔ e φ ∈ edgeConstant s t := by
    change φ ∈ W.dualAnnihilator ↔ ∀ a, (e φ) (s a) = (e φ) (t a)
    simpa only [e, LinearEquiv.piRing_apply] using graphBd_annihilator_iff s t φ
  have hmap : W.dualAnnihilator.map e.toLinearMap = edgeConstant s t := by
    ext f
    constructor
    · rintro ⟨φ, hφ, rfl⟩
      exact (hm φ).mp hφ
    · intro hf
      refine ⟨e.symm f, (hm _).mpr ?_, e.apply_symm_apply f⟩
      simpa only [e.apply_symm_apply] using hf
  let er := e.ofSubmodules W.dualAnnihilator (edgeConstant s t) hmap
  calc
    Module.finrank ℚ ((V → ℚ) ⧸ W) =
        Module.finrank ℚ (Module.Dual ℚ ((V → ℚ) ⧸ W)) := by
      symm
      exact Subspace.dual_finrank_eq
    _ = Module.finrank ℚ W.dualAnnihilator :=
      W.dualQuotEquivDualAnnihilator.finrank_eq
    _ = Module.finrank ℚ (edgeConstant s t) := er.finrank_eq
    _ = _ := edgeConstant_finrank s t

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

/-- **A graph's `H₀ = coker ∂` is free abelian on its components** (`exr-9-graph`, `hw-9-10`,
`coker ∂ ≅ ℤ^c`), by the route of `prop:H0`, one component at a time: sending each vertex to its
component kills the boundaries, since both ends of an edge lie in one component; conversely the
class of a vertex depends only on its component, since `t e - s e = ∂ e`; and the two maps are
inverse. -/
theorem H0_equiv {V E : Type*} (s t : E → V) :
    ∃ e : ((V →₀ ℤ) ⧸ LinearMap.range (graphBd s t)) ≃ₗ[ℤ] (Quot (adj s t) →₀ ℤ),
      ∀ v, e (Submodule.Quotient.mk (Finsupp.single v 1)) = Finsupp.single (Quot.mk _ v) 1 := by
  classical
  let P := LinearMap.range (graphBd s t)
  let f : (V →₀ ℤ) →ₗ[ℤ] (Quot (adj s t) →₀ ℤ) :=
    Finsupp.linearCombination ℤ (fun v => Finsupp.single (Quot.mk (adj s t) v) 1)
  have hf : f.comp (graphBd s t) = 0 := by
    apply Finsupp.lhom_ext
    intro e z
    have he : Quot.mk (adj s t) (s e) = Quot.mk (adj s t) (t e) :=
      Quot.sound ⟨e, rfl, rfl⟩
    simp [f, graphBd, he]
  have hker : P ≤ LinearMap.ker f := by
    rintro y ⟨x, rfl⟩
    change f (graphBd s t x) = 0
    exact LinearMap.congr_fun hf x
  let F : ((V →₀ ℤ) ⧸ P) →ₗ[ℤ] (Quot (adj s t) →₀ ℤ) := P.liftQ f hker
  let j : Quot (adj s t) → ((V →₀ ℤ) ⧸ P) :=
    Quot.lift (fun v => Submodule.Quotient.mk (Finsupp.single v (1 : ℤ))) (by
      intro a b hab
      rcases hab with ⟨e, rfl, rfl⟩
      apply Eq.symm
      apply (Submodule.Quotient.eq P).2
      refine ⟨Finsupp.single e 1, ?_⟩
      simp [graphBd])
  let G : (Quot (adj s t) →₀ ℤ) →ₗ[ℤ] ((V →₀ ℤ) ⧸ P) :=
    Finsupp.linearCombination ℤ j
  have hFG : F.comp G = LinearMap.id := by
    apply Finsupp.lhom_ext
    intro c z
    induction c using Quot.inductionOn with
    | h v =>
      simp [G, j, F, f]
  have hGF : G.comp F = LinearMap.id := by
    have h : G.comp f = P.mkQ := by
      apply Finsupp.lhom_ext
      intro v z
      simp [G, j, f]
      change z • P.mkQ (Finsupp.single v 1) = P.mkQ (Finsupp.single v z)
      rw [← map_smul]
      simp
    apply LinearMap.ext
    intro q
    induction q using Submodule.Quotient.induction_on with
    | _ x =>
      exact LinearMap.congr_fun h x
  refine ⟨LinearEquiv.ofLinearMap F G hFG hGF, ?_⟩
  intro v
  simp [F, f, LinearEquiv.ofLinearMap]

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

/-- If `c p = h p + b p + b (p - 1)`, with `b (-1) = 0`, the alternating sums of `c` and `h`
up to `N` differ by `(-1)^N b N`: the terms `b p` cancel in pairs. -/
theorem alternating_sum_telescope (c h b : ℕ → ℤ)
    (hzero : c 0 = h 0 + b 0)
    (hsucc : ∀ p, c (p + 1) = h (p + 1) + b (p + 1) + b p)
    (N : ℕ) :
    (∑ p ∈ Finset.range (N + 1), (-1 : ℤ) ^ p * c p) =
      (∑ p ∈ Finset.range (N + 1), (-1 : ℤ) ^ p * h p) + (-1 : ℤ) ^ N * b N := by
  induction N with
  | zero =>
      simpa only [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, one_mul,
        zero_add, add_zero] using hzero
  | succ N ih =>
      rw [Finset.sum_range_succ _ (N + 1), ih,
        Finset.sum_range_succ _ (N + 1), hsucc N, pow_succ]
      ring

/-- `dim H p + dim B p = dim Z p`, where `B p = im (d p) ⊆ Z p`. -/
theorem finrank_natHomology_add_finrank_range {F : Type*} [Field F] {K : ℕ → Type*}
    [∀ n, AddCommGroup (K n)] [∀ n, Module F (K n)] [∀ n, FiniteDimensional F (K n)]
    (d : ∀ n, K (n + 1) →ₗ[F] K n) (hd : ∀ n, d n ∘ₗ d (n + 1) = 0)
    (p : ℕ) :
    Module.finrank F (natHomology d p) + Module.finrank F (LinearMap.range (d p)) =
      Module.finrank F (natCycles d p) := by
  have hle : LinearMap.range (d p) ≤ natCycles d p := by
    cases p with
    | zero => simp [natCycles]
    | succ n =>
      change LinearMap.range (d (n + 1)) ≤ LinearMap.ker (d n)
      exact LinearMap.range_le_ker_iff.mpr (hd n)
  let S := natCycles d p
  let B := (LinearMap.range (d p)).comap S.subtype
  have hB : Module.finrank F B = Module.finrank F (LinearMap.range (d p)) := by
    rw [← Submodule.finrank_map_subtype_eq S B]
    dsimp [B]
    rw [Submodule.map_comap_subtype, inf_eq_right.mpr hle]
  change Module.finrank F (S ⧸ B) + Module.finrank F (LinearMap.range (d p)) =
    Module.finrank F S
  rw [← hB]
  exact Submodule.finrank_quotient_add_finrank B

/-- **The Euler number is computed from the chain groups** (`rem:euler-chain-groups`,
`hw-9-9`, `def:betti-euler`): for a complex of finite-dimensional vector spaces with `K p = 0`
for `p > N`, `∑ (-1)^p dim K p = ∑ (-1)^p dim H p`.

The route: in each degree, rank-nullity for `d (p - 1)` and the quotient `H p = Z p / B p` give
`dim K p = b p + dim B p + dim B (p - 1)`; in the alternating sum the `dim B p` cancel in pairs,
leaving `(-1)^N dim B N`, which is `0` because `K (N + 1) = 0`. The book's hint starts from
`n = 1`, the two-term case of the same count. -/
theorem euler_number_eq_alternating_dim {F : Type*} [Field F] {K : ℕ → Type*}
    [∀ n, AddCommGroup (K n)] [∀ n, Module F (K n)] [∀ n, FiniteDimensional F (K n)]
    (d : ∀ n, K (n + 1) →ₗ[F] K n) (hd : ∀ n, d n ∘ₗ d (n + 1) = 0)
    (N : ℕ) (hN : ∀ p, N < p → Subsingleton (K p)) :
    ∑ p ∈ Finset.range (N + 1), (-1 : ℤ) ^ p * (Module.finrank F (K p) : ℤ) =
      ∑ p ∈ Finset.range (N + 1), (-1 : ℤ) ^ p * (Module.finrank F (natHomology d p) : ℤ) := by
  classical
  have hzero : (Module.finrank F (K 0) : ℤ) =
      (Module.finrank F (natHomology d 0) : ℤ) +
        (Module.finrank F (LinearMap.range (d 0)) : ℤ) := by
    have h := finrank_natHomology_add_finrank_range d hd 0
    change Module.finrank F (natHomology d 0) +
      Module.finrank F (LinearMap.range (d 0)) =
        Module.finrank F (⊤ : Submodule F (K 0)) at h
    rw [finrank_top] at h
    exact_mod_cast h.symm
  have hsucc (p : ℕ) : (Module.finrank F (K (p + 1)) : ℤ) =
      (Module.finrank F (natHomology d (p + 1)) : ℤ) +
        (Module.finrank F (LinearMap.range (d (p + 1))) : ℤ) +
        (Module.finrank F (LinearMap.range (d p)) : ℤ) := by
    have h := LinearMap.finrank_range_add_finrank_ker (d p)
    have hz := finrank_natHomology_add_finrank_range d hd (p + 1)
    change Module.finrank F (natHomology d (p + 1)) +
      Module.finrank F (LinearMap.range (d (p + 1))) =
        Module.finrank F (LinearMap.ker (d p)) at hz
    have hn : Module.finrank F (K (p + 1)) =
        Module.finrank F (natHomology d (p + 1)) +
        Module.finrank F (LinearMap.range (d (p + 1))) +
        Module.finrank F (LinearMap.range (d p)) := by omega
    exact_mod_cast hn
  have hsum := alternating_sum_telescope
    (fun p => (Module.finrank F (K p) : ℤ))
    (fun p => (Module.finrank F (natHomology d p) : ℤ))
    (fun p => (Module.finrank F (LinearMap.range (d p)) : ℤ))
    hzero hsucc N
  have htop : Module.finrank F (LinearMap.range (d N)) = 0 := by
    letI : Subsingleton (K (N + 1)) := hN (N + 1) (by omega)
    have hdN : d N = 0 := by
      ext x
      rw [Subsingleton.elim x 0, map_zero]
      rfl
    rw [hdN, LinearMap.range_zero, finrank_bot]
  simpa only [htop, Int.natCast_zero, mul_zero, add_zero] using hsum

/-! ## The zigzag lemma: the connecting map (`hw-9-4`)

Chain complexes indexed by `ℤ`, with `dA n : A (n + 1) → A n`; degrees are written `n + 1 + 1`
rather than `n + 2`, so that the types agree by definition. -/

/-- Every cycle `z` of `C` lifts: there are `b` with `j b = z` and a cycle `a` of `A` with
`i a = ∂ b`. Since `j (∂ b) = ∂ z = 0`, `∂ b` lies in `ker j = im i`; and `i (∂ a) = ∂ ∂ b = 0`
with `i` injective gives `∂ a = 0`. -/
theorem zigzag_lift_exists {R : Type*} [Ring R] {A B C : ℤ → Type*}
    [∀ n, AddCommGroup (A n)] [∀ n, Module R (A n)]
    [∀ n, AddCommGroup (B n)] [∀ n, Module R (B n)]
    [∀ n, AddCommGroup (C n)] [∀ n, Module R (C n)]
    (dA : ∀ n, A (n + 1) →ₗ[R] A n) (dB : ∀ n, B (n + 1) →ₗ[R] B n)
    (dC : ∀ n, C (n + 1) →ₗ[R] C n)
    (hdB : ∀ n, dB n ∘ₗ dB (n + 1) = 0)
    (i : ∀ n, A n →ₗ[R] B n) (j : ∀ n, B n →ₗ[R] C n)
    (hi : ∀ n, dB n ∘ₗ i (n + 1) = i n ∘ₗ dA n)
    (hj : ∀ n, dC n ∘ₗ j (n + 1) = j n ∘ₗ dB n)
    (hinj : ∀ n, Function.Injective (i n))
    (hex : ∀ n, LinearMap.range (i n) = LinearMap.ker (j n))
    (hsurj : ∀ n, Function.Surjective (j n)) (n : ℤ)
    (z : LinearMap.ker (dC (n + 1))) :
    ∃ (b : B (n + 1 + 1)) (a : LinearMap.ker (dA n)),
      j (n + 1 + 1) b = z ∧ i (n + 1) a = dB (n + 1) b := by
  rcases hsurj (n + 1 + 1) z with ⟨b, hb⟩
  have hcycle : j (n + 1) (dB (n + 1) b) = 0 := by
    have h := LinearMap.congr_fun (hj (n + 1)) b
    simp only [LinearMap.comp_apply] at h
    rw [hb] at h
    exact h.symm.trans z.property
  have hrange : dB (n + 1) b ∈ LinearMap.range (i (n + 1)) := by
    rw [hex (n + 1)]
    exact hcycle
  rcases hrange with ⟨a0, ha0⟩
  have hacycle : dA n a0 = 0 := by
    apply hinj n
    have h := LinearMap.congr_fun (hi n) a0
    have hsq := LinearMap.congr_fun (hdB n) b
    simp only [LinearMap.comp_apply, LinearMap.zero_apply] at h hsq
    rw [ha0] at h
    simpa only [map_zero] using h.symm.trans hsq
  exact ⟨b, ⟨a0, hacycle⟩, hb, ha0⟩

/-- The class `[a]` does not depend on the lift: if `j b = j b'`, then `b - b' = i c`, and
`a - a' = ∂ c` because `i` is injective and `i (a - a') = ∂ (b - b') = i (∂ c)`. -/
theorem zigzag_class_independent {R : Type*} [Ring R] {A B C : ℤ → Type*}
    [∀ n, AddCommGroup (A n)] [∀ n, Module R (A n)]
    [∀ n, AddCommGroup (B n)] [∀ n, Module R (B n)]
    [∀ n, AddCommGroup (C n)] [∀ n, Module R (C n)]
    (dA : ∀ n, A (n + 1) →ₗ[R] A n) (dB : ∀ n, B (n + 1) →ₗ[R] B n)
    (i : ∀ n, A n →ₗ[R] B n) (j : ∀ n, B n →ₗ[R] C n)
    (hi : ∀ n, dB n ∘ₗ i (n + 1) = i n ∘ₗ dA n)
    (hinj : ∀ n, Function.Injective (i n))
    (hex : ∀ n, LinearMap.range (i n) = LinearMap.ker (j n)) (n : ℤ)
    (b b' : B (n + 1 + 1)) (a a' : LinearMap.ker (dA n))
    (hb : j (n + 1 + 1) b = j (n + 1 + 1) b')
    (ha : i (n + 1) a = dB (n + 1) b)
    (ha' : i (n + 1) a' = dB (n + 1) b') :
    cls (dA (n + 1)) (dA n) a = cls (dA (n + 1)) (dA n) a' := by
  have hmem : b - b' ∈ LinearMap.range (i (n + 1 + 1)) := by
    rw [hex]
    change j (n + 1 + 1) (b - b') = 0
    rw [map_sub, hb, sub_self]
  obtain ⟨c, hc⟩ := hmem
  have hac : (a : A (n + 1)) - (a' : A (n + 1)) = dA (n + 1) c := by
    apply hinj (n + 1)
    rw [map_sub, ha, ha']
    have hcomm := LinearMap.congr_fun (hi (n + 1)) c
    change dB (n + 1) (i (n + 1 + 1) c) = i (n + 1) (dA (n + 1) c) at hcomm
    rw [hc, map_sub] at hcomm
    exact hcomm
  let p := (LinearMap.range (dA (n + 1))).comap (LinearMap.ker (dA n)).subtype
  have hz : p.mkQ (a - a') = 0 := by
    apply (Submodule.Quotient.mk_eq_zero p).mpr
    change (a : A (n + 1)) - (a' : A (n + 1)) ∈ LinearMap.range (dA (n + 1))
    exact ⟨c, hac.symm⟩
  rw [map_sub] at hz
  exact sub_eq_zero.mp hz

/-- The rule `z ↦ [a]` is a linear map on the cycles of `C`: the sum (or a multiple) of
lifts is a lift of the sum (or the multiple). -/
theorem zigzag_cycle_map_exists {R : Type*} [Ring R] {A B C : ℤ → Type*}
    [∀ n, AddCommGroup (A n)] [∀ n, Module R (A n)]
    [∀ n, AddCommGroup (B n)] [∀ n, Module R (B n)]
    [∀ n, AddCommGroup (C n)] [∀ n, Module R (C n)]
    (dA : ∀ n, A (n + 1) →ₗ[R] A n) (dB : ∀ n, B (n + 1) →ₗ[R] B n)
    (dC : ∀ n, C (n + 1) →ₗ[R] C n)
    (hdB : ∀ n, dB n ∘ₗ dB (n + 1) = 0)
    (i : ∀ n, A n →ₗ[R] B n) (j : ∀ n, B n →ₗ[R] C n)
    (hi : ∀ n, dB n ∘ₗ i (n + 1) = i n ∘ₗ dA n)
    (hj : ∀ n, dC n ∘ₗ j (n + 1) = j n ∘ₗ dB n)
    (hinj : ∀ n, Function.Injective (i n))
    (hex : ∀ n, LinearMap.range (i n) = LinearMap.ker (j n))
    (hsurj : ∀ n, Function.Surjective (j n)) (n : ℤ) :
    ∃ f : LinearMap.ker (dC (n + 1)) →ₗ[R] H (dA (n + 1)) (dA n),
      ∀ (z : LinearMap.ker (dC (n + 1))) (b : B (n + 1 + 1)) (a : LinearMap.ker (dA n)),
        j (n + 1 + 1) b = z → i (n + 1) a = dB (n + 1) b →
          f z = cls (dA (n + 1)) (dA n) a := by
  classical
  choose b a hb ha using
    (fun z : LinearMap.ker (dC (n + 1)) =>
      zigzag_lift_exists dA dB dC hdB i j hi hj hinj hex hsurj n z)
  let f0 : LinearMap.ker (dC (n + 1)) → H (dA (n + 1)) (dA n) :=
    fun z => cls (dA (n + 1)) (dA n) (a z)
  have hf0 : ∀ (z : LinearMap.ker (dC (n + 1)))
      (b0 : B (n + 1 + 1)) (a0 : LinearMap.ker (dA n)),
      j (n + 1 + 1) b0 = z → i (n + 1) a0 = dB (n + 1) b0 →
      f0 z = cls (dA (n + 1)) (dA n) a0 := by
    intro z b0 a0 hb0 ha0
    exact zigzag_class_independent dA dB i j hi hinj hex n
      (b z) b0 (a z) a0 ((hb z).trans hb0.symm) (ha z) ha0
  refine ⟨{ toFun := f0, map_add' := ?_, map_smul' := ?_ }, ?_⟩
  · intro x y
    have h := hf0 (x + y) (b x + b y) (a x + a y)
      (by simp only [map_add, hb, Submodule.coe_add])
      (by simp only [Submodule.coe_add, map_add, ha])
    exact h.trans (by rfl)
  · intro r x
    have h := hf0 (r • x) (r • b x) (r • a x)
      (by simp only [map_smul, hb, Submodule.coe_smul])
      (by simp only [Submodule.coe_smul, map_smul, ha])
    exact h.trans (by rfl)
  · exact hf0

/-- **The connecting map of the zigzag lemma** (`hw-9-4`). For chain maps
`0 → A → B → C → 0`, short exact in each degree, there is exactly one linear
`δ : H_{n+2}(C) → H_{n+1}(A)` with `δ [z] = [a]` whenever `j b = z` and `i a = ∂ b`.

The route is the usual diagram chase, which the book leaves to the homework: the rule
`z ↦ [a]` is well defined and linear on cycles (`zigzag_cycle_map_exists`); it kills a
boundary `z = ∂ c`, since `c = j b'` gives the lift `b = ∂ b'` with `a = 0`; so it factors
through `H(C)`; and it is unique because every class `[z]` has a lift. -/
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
          δ (cls (dC (n + 1 + 1)) (dC (n + 1)) z) = cls (dA (n + 1)) (dA n) a := by
  classical
  obtain ⟨f, hf⟩ := zigzag_cycle_map_exists dA dB dC hdB i j hi hj hinj hex hsurj n
  let p := (LinearMap.range (dC (n + 1 + 1))).comap
    (LinearMap.ker (dC (n + 1))).subtype
  have hp : p ≤ LinearMap.ker f := by
    intro z hz
    change (z : C (n + 1 + 1)) ∈ LinearMap.range (dC (n + 1 + 1)) at hz
    obtain ⟨c, hc⟩ := hz
    obtain ⟨b', hb'⟩ := hsurj (n + 1 + 1 + 1) c
    have hb : j (n + 1 + 1) (dB (n + 1 + 1) b') = z := by
      calc
        j (n + 1 + 1) (dB (n + 1 + 1) b') =
            dC (n + 1 + 1) (j (n + 1 + 1 + 1) b') :=
          (LinearMap.congr_fun (hj (n + 1 + 1)) b').symm
        _ = z := by rw [hb', hc]
    have ha : i (n + 1) (0 : LinearMap.ker (dA n)) =
        dB (n + 1) (dB (n + 1 + 1) b') := by
      simpa only [ZeroMemClass.coe_zero, map_zero, LinearMap.comp_apply,
        LinearMap.zero_apply] using (LinearMap.congr_fun (hdB (n + 1)) b').symm
    have hz0 := hf z (dB (n + 1 + 1) b') 0 hb ha
    change f z = 0
    simpa only [cls, Submodule.Quotient.mk_zero] using hz0
  let δ := p.liftQ f hp
  have hδ : ∀ (z : LinearMap.ker (dC (n + 1))) (b : B (n + 1 + 1))
      (a : LinearMap.ker (dA n)), j (n + 1 + 1) b = z →
      i (n + 1) a = dB (n + 1) b →
      δ (cls (dC (n + 1 + 1)) (dC (n + 1)) z) =
        cls (dA (n + 1)) (dA n) a := by
    intro z b a hb ha
    change f z = _
    exact hf z b a hb ha
  refine ⟨δ, hδ, ?_⟩
  intro δ' hδ'
  apply LinearMap.ext
  intro q
  obtain ⟨z, rfl⟩ := p.mkQ_surjective q
  obtain ⟨b, a, hb, ha⟩ := zigzag_lift_exists dA dB dC hdB i j hi hj hinj hex hsurj n z
  exact (hδ' z b a hb ha).trans (hδ z b a hb ha).symm

/-! ## The zigzag lemma: exactness (`hw-9-4`) -/

/-- Two cycles have the same class exactly when their difference is a boundary. -/
theorem zigzag_cls_eq_iff {R U V W : Type*} [Ring R] [AddCommGroup U] [Module R U] [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W] (d₁ : U →ₗ[R] V) (d₀ : V →ₗ[R] W) (x y : LinearMap.ker d₀) : cls d₁ d₀ x = cls d₁ d₀ y ↔ ∃ u : U, d₁ u = (x : V) - (y : V) := by
  unfold cls
  rw [Submodule.Quotient.eq]
  rfl

/-- Every class is the class of a cycle. -/
theorem zigzag_cls_surjective {R U V W : Type*} [Ring R] [AddCommGroup U] [Module R U] [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W] (d₁ : U →ₗ[R] V) (d₀ : V →ₗ[R] W) : Function.Surjective (cls d₁ d₀) := by
  unfold cls H
  exact Submodule.Quotient.mk_surjective _

/-- The lift of `zigzag_lift_exists`, stated for one square of the diagram: a cycle `z` of `C`
is `j b`, and `∂ b = i a` for a cycle `a` of `A`. -/
theorem zigzag_connecting_representative {R A₀ A₁ B₀ B₁ B₂ C₁ C₂ : Type*} [Ring R] [AddCommGroup A₀] [Module R A₀] [AddCommGroup A₁] [Module R A₁] [AddCommGroup B₀] [Module R B₀] [AddCommGroup B₁] [Module R B₁] [AddCommGroup B₂] [Module R B₂] [AddCommGroup C₁] [Module R C₁] [AddCommGroup C₂] [Module R C₂] (dA : A₁ →ₗ[R] A₀) (dB : B₁ →ₗ[R] B₀) (dB' : B₂ →ₗ[R] B₁) (dC : C₂ →ₗ[R] C₁) (i₀ : A₀ →ₗ[R] B₀) (i₁ : A₁ →ₗ[R] B₁) (j₁ : B₁ →ₗ[R] C₁) (j₂ : B₂ →ₗ[R] C₂) (hdB : dB ∘ₗ dB' = 0) (hi : dB ∘ₗ i₁ = i₀ ∘ₗ dA) (hj : dC ∘ₗ j₂ = j₁ ∘ₗ dB') (hinj : Function.Injective i₀) (hex : LinearMap.range i₁ = LinearMap.ker j₁) (hsurj : Function.Surjective j₂) (z : LinearMap.ker dC) : ∃ b : B₂, ∃ a : LinearMap.ker dA, j₂ b = (z : C₂) ∧ i₁ a = dB' b := by
  obtain ⟨b, hb⟩ := hsurj (z : C₂)
  have hcycle : j₁ (dB' b) = 0 := by
    have h := congrArg (fun f : B₂ →ₗ[R] C₁ => f b) hj
    simpa only [LinearMap.comp_apply, hb, LinearMap.mem_ker.mp z.property] using h.symm
  have hrange : dB' b ∈ LinearMap.range i₁ := by
    rw [hex]
    exact hcycle
  obtain ⟨a₀, ha₀⟩ := hrange
  have ha : dA a₀ = 0 := by
    apply hinj
    have hcomm := congrArg (fun f : A₁ →ₗ[R] B₀ => f a₀) hi
    have hzero := congrArg (fun f : B₂ →ₗ[R] B₀ => f b) hdB
    simp only [LinearMap.comp_apply, ha₀] at hcomm
    simp only [LinearMap.comp_apply, LinearMap.zero_apply] at hzero
    simpa only [map_zero] using hcomm.symm.trans hzero
  exact ⟨b, ⟨a₀, ha⟩, hb, ha₀⟩

/-- A cycle `y` of `B` whose image `j y` is a boundary `∂ c` is `i x` up to a boundary, for a
cycle `x` of `A`: write `c = j b`; then `j (y - ∂ b) = 0`, so `y - ∂ b = i x`, and `x` is a
cycle because `i` is injective. -/
theorem zigzag_cycle_preimage_mod_boundary {R A₀ A₁ B₀ B₁ B₂ C₁ C₂ : Type*} [Ring R] [AddCommGroup A₀] [Module R A₀] [AddCommGroup A₁] [Module R A₁] [AddCommGroup B₀] [Module R B₀] [AddCommGroup B₁] [Module R B₁] [AddCommGroup B₂] [Module R B₂] [AddCommGroup C₁] [Module R C₁] [AddCommGroup C₂] [Module R C₂] (dA : A₁ →ₗ[R] A₀) (dB : B₁ →ₗ[R] B₀) (dB' : B₂ →ₗ[R] B₁) (dC : C₂ →ₗ[R] C₁) (i₀ : A₀ →ₗ[R] B₀) (i₁ : A₁ →ₗ[R] B₁) (j₁ : B₁ →ₗ[R] C₁) (j₂ : B₂ →ₗ[R] C₂) (hdB : dB ∘ₗ dB' = 0) (hi : dB ∘ₗ i₁ = i₀ ∘ₗ dA) (hj : dC ∘ₗ j₂ = j₁ ∘ₗ dB') (hinj : Function.Injective i₀) (hex : LinearMap.range i₁ = LinearMap.ker j₁) (hsurj : Function.Surjective j₂) (y : LinearMap.ker dB) (hy : j₁ y ∈ LinearMap.range dC) : ∃ x : LinearMap.ker dA, ∃ b : B₂, i₁ x = (y : B₁) - dB' b := by
  rcases hy with ⟨c, hc⟩
  rcases hsurj c with ⟨b, hb⟩
  have hjb := DFunLike.congr_fun hj b
  simp only [LinearMap.comp_apply] at hjb
  have hz : y.val - dB' b ∈ LinearMap.ker j₁ := by
    change j₁ (y.val - dB' b) = 0
    rw [map_sub, ← hjb, hb, hc, sub_self]
  rw [← hex] at hz
  rcases hz with ⟨x₀, hx₀⟩
  have hdb := DFunLike.congr_fun hdB b
  simp only [LinearMap.comp_apply, LinearMap.zero_apply] at hdb
  have hix := DFunLike.congr_fun hi x₀
  simp only [LinearMap.comp_apply] at hix
  have hx : dA x₀ = 0 := by
    apply hinj
    rw [map_zero, ← hix, hx₀, map_sub, hdb, sub_zero]
    exact y.property
  exact ⟨⟨x₀, hx⟩, b, hx₀⟩

/-- **The zigzag lemma** (`hw-9-4`). With `i_*`, `j_*` and `δ` given by their values on classes,
`H_{n+2}(A) → H_{n+2}(B) → H_{n+2}(C) → H_{n+1}(A) → H_{n+1}(B)` is exact at its three middle
terms.

The route is the usual diagram chase, which the book leaves to the homework. The composites
vanish: `j i = 0`; `δ [j y] = [0]`, lifting `j y` by the cycle `y`; and `i_* δ [z] = [∂ b] = 0`.
Each kernel lies in the image: if `j_* [y] = 0`, then `[y] = [i x]`
(`zigzag_cycle_preimage_mod_boundary`); if `δ [z] = [a] = 0`, then `a = ∂ a₂`, and `b - i a₂` is a
cycle with image `z`; if `i_* [a] = 0`, then `i a = ∂ b`, and `z = j b` is a cycle with
`δ [z] = [a]`. -/
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
      LinearMap.range δ = LinearMap.ker iₛ₁ := by
  classical
  have hzA (a : LinearMap.ker (dA n)) :
      cls (dA (n + 1)) (dA n) a = 0 ↔ ∃ t, dA (n + 1) t = (a : A (n + 1)) := by
    simpa only [cls, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap,
      Submodule.subtype_apply, LinearMap.mem_range]
  have hzB (m : ℤ) (a : LinearMap.ker (dB m)) :
      cls (dB (m + 1)) (dB m) a = 0 ↔ ∃ t, dB (m + 1) t = (a : B (m + 1)) := by
    simp only [cls, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap,
      Submodule.subtype_apply, LinearMap.mem_range]
  have hzC (z : LinearMap.ker (dC (n + 1))) :
      cls (dC (n + 1 + 1)) (dC (n + 1)) z = 0 ↔
        ∃ t, dC (n + 1 + 1) t = (z : C (n + 1 + 1)) := by
    simp only [cls, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap,
      Submodule.subtype_apply, LinearMap.mem_range]
  have ci (m : ℤ) (x : A (m + 1)) : dB m (i (m + 1) x) = i m (dA m x) :=
    DFunLike.congr_fun (hi m) x
  have cj (m : ℤ) (x : B (m + 1)) : dC m (j (m + 1) x) = j m (dB m x) :=
    DFunLike.congr_fun (hj m) x
  have ji (m : ℤ) (x : A m) : j m (i m x) = 0 := by
    have h : i m x ∈ LinearMap.ker (j m) := by
      rw [← hex m]
      exact ⟨x, rfl⟩
    exact h
  let ic (m : ℤ) (x : LinearMap.ker (dA m)) : LinearMap.ker (dB m) :=
    ⟨i (m + 1) x, by rw [LinearMap.mem_ker, ci, x.property, map_zero]⟩
  let jc (m : ℤ) (x : LinearMap.ker (dB m)) : LinearMap.ker (dC m) :=
    ⟨j (m + 1) x, by rw [LinearMap.mem_ker, cj, x.property, map_zero]⟩
  constructor
  · ext x
    simp only [LinearMap.mem_range, LinearMap.mem_ker]
    constructor
    · rintro ⟨a, rfl⟩
      obtain ⟨a, rfl⟩ := zigzag_cls_surjective (dA (n + 1 + 1)) (dA (n + 1)) a
      rw [hi₂ a (ic (n + 1) a) rfl,
        hj₂ (ic (n + 1) a) (jc (n + 1) (ic (n + 1) a)) rfl]
      apply (hzC _).2
      exact ⟨0, by simpa only [jc, ic, map_zero] using (ji (n + 1 + 1) a).symm⟩
    · intro hx
      obtain ⟨y, rfl⟩ := zigzag_cls_surjective (dB (n + 1 + 1)) (dB (n + 1)) x
      rw [hj₂ y (jc (n + 1) y) rfl] at hx
      have hy : j (n + 1 + 1) y ∈ LinearMap.range (dC (n + 1 + 1)) :=
        (hzC _).1 hx
      obtain ⟨a, b, ha⟩ := zigzag_cycle_preimage_mod_boundary
        (dA (n + 1)) (dB (n + 1)) (dB (n + 1 + 1)) (dC (n + 1 + 1))
        (i (n + 1)) (i (n + 1 + 1)) (j (n + 1 + 1)) (j (n + 1 + 1 + 1))
        (hdB (n + 1)) (hi (n + 1)) (hj (n + 1 + 1)) (hinj (n + 1))
        (hex (n + 1 + 1)) (hsurj (n + 1 + 1 + 1)) y hy
      refine ⟨cls _ _ a, ?_⟩
      rw [hi₂ a (ic (n + 1) a) rfl]
      apply (zigzag_cls_eq_iff _ _ _ _).2
      refine ⟨-b, ?_⟩
      change dB (n + 1 + 1) (-b) = i (n + 1 + 1) a - y
      rw [map_neg, ha]
      abel
  · constructor
    · ext x
      simp only [LinearMap.mem_range, LinearMap.mem_ker]
      constructor
      · rintro ⟨y, rfl⟩
        obtain ⟨y, rfl⟩ := zigzag_cls_surjective (dB (n + 1 + 1)) (dB (n + 1)) y
        rw [hj₂ y (jc (n + 1) y) rfl]
        rw [hδ (jc (n + 1) y) y 0 rfl (by
          simpa only [Submodule.coe_zero, map_zero] using y.property.symm)]
        rfl
      · intro hx
        obtain ⟨z, rfl⟩ := zigzag_cls_surjective (dC (n + 1 + 1)) (dC (n + 1)) x
        obtain ⟨b, a, hb, ha⟩ := zigzag_connecting_representative
          (dA n) (dB n) (dB (n + 1)) (dC (n + 1))
          (i n) (i (n + 1)) (j (n + 1)) (j (n + 1 + 1))
          (hdB n) (hi n) (hj (n + 1)) (hinj n) (hex (n + 1))
          (hsurj (n + 1 + 1)) z
        rw [hδ z b a hb ha] at hx
        obtain ⟨a₂, ha₂⟩ := (hzA a).1 hx
        let y : LinearMap.ker (dB (n + 1)) :=
          ⟨b - i (n + 1 + 1) a₂, by
            rw [LinearMap.mem_ker, map_sub, ci, ha₂, ← ha, sub_self]⟩
        refine ⟨cls _ _ y, ?_⟩
        apply hj₂ y z
        change (z : C (n + 1 + 1)) = j (n + 1 + 1) (b - i (n + 1 + 1) a₂)
        rw [map_sub, ji, sub_zero, hb]
    · ext x
      simp only [LinearMap.mem_range, LinearMap.mem_ker]
      constructor
      · rintro ⟨z, rfl⟩
        obtain ⟨z, rfl⟩ := zigzag_cls_surjective (dC (n + 1 + 1)) (dC (n + 1)) z
        obtain ⟨b, a, hb, ha⟩ := zigzag_connecting_representative
          (dA n) (dB n) (dB (n + 1)) (dC (n + 1))
          (i n) (i (n + 1)) (j (n + 1)) (j (n + 1 + 1))
          (hdB n) (hi n) (hj (n + 1)) (hinj n) (hex (n + 1))
          (hsurj (n + 1 + 1)) z
        rw [hδ z b a hb ha, hi₁ a (ic n a) rfl]
        exact (hzB n _).2 ⟨b, ha.symm⟩
      · intro hx
        obtain ⟨a, rfl⟩ := zigzag_cls_surjective (dA (n + 1)) (dA n) x
        rw [hi₁ a (ic n a) rfl] at hx
        obtain ⟨b, hb⟩ := (hzB n _).1 hx
        let z : LinearMap.ker (dC (n + 1)) :=
          ⟨j (n + 1 + 1) b, by
            rw [LinearMap.mem_ker, cj, hb]
            exact ji (n + 1) a⟩
        exact ⟨cls _ _ z, hδ z b a rfl hb.symm⟩

end Week09Homology
