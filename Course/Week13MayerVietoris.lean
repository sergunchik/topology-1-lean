/-
Machine-generated (Claude, Aristotle), no line written by a person. Copyleft: GPL-3.0-or-later.

# Week 13: the short exact sequence of Mayer–Vietoris

This file proves a statement of week 13 of the book.

* For subsets `A, B` of a set `S`, with `ℤ[T]` the finite integer combinations of points of `T`
  (`Finsupp.supported ℤ ℤ T`), the sequence `0 → ℤ[A ∩ B] → ℤ[A] ⊕ ℤ[B] → ℤ[A ∪ B] → 0`, with
  `φ(c) = (c, -c)` and `ψ(a, b) = a + b`, is exact (`mv_ses`). With `S` the singular
  `n`-simplices of `X`, and `A`, `B` those in `U` and in `V`, it is the exactness in `lem:mv-ses`,
  by the book's route: `ψ` is onto, since a chain of simplices each in `U` or in `V` is a chain
  in `U` plus one in `V` (`chain_decomposition`); and if `a + b = 0` then `a = -b`, so each
  simplex of `a` lies in `U` and in `V` (`cycle_supported`). That `φ` and `ψ` are chain maps is
  not formalised here.

The proof was found by a computer program, the automated prover Aleph Prover, and Lean checks it
like every proof here. AI models compared the Lean statement with the book's and found that it
says the same (9 November 2026).
-/
import Mathlib

namespace Week13MayerVietoris

open Finsupp

variable {S : Type*} (A B : Set S)

/-- `φ(c) = (c, -c)`. -/
noncomputable def φ : supported ℤ ℤ (A ∩ B) →ₗ[ℤ] supported ℤ ℤ A × supported ℤ ℤ B :=
  (Submodule.inclusion (supported_mono Set.inter_subset_left)).prod
    (-Submodule.inclusion (supported_mono Set.inter_subset_right))

/-- `ψ(a, b) = a + b`. -/
noncomputable def ψ : supported ℤ ℤ A × supported ℤ ℤ B →ₗ[ℤ] supported ℤ ℤ (A ∪ B) :=
  (Submodule.inclusion (supported_mono Set.subset_union_left)).coprod
    (Submodule.inclusion (supported_mono Set.subset_union_right))

/-- A chain on `A ∪ B` is a chain on `A` plus a chain on `B`: so `ψ` is onto. -/
theorem chain_decomposition {S : Type*} (A B : Set S) (c : Finsupp.supported ℤ ℤ (A ∪ B)) : ∃ (a : Finsupp.supported ℤ ℤ A) (b : Finsupp.supported ℤ ℤ B), (a : S →₀ ℤ) + (b : S →₀ ℤ) = (c : S →₀ ℤ) := by
  have hc : (c : S →₀ ℤ) ∈ Finsupp.supported ℤ ℤ A ⊔ Finsupp.supported ℤ ℤ B := by
    simpa only [Finsupp.supported_union] using c.property
  exact Submodule.mem_sup'.mp hc

/-- If `a + b = 0`, with `a` on `A` and `b` on `B`, then `a = -b` lies on `A` and on `B`, so on
`A ∩ B`. -/
theorem cycle_supported {S : Type*} (A B : Set S) (a : Finsupp.supported ℤ ℤ A) (b : Finsupp.supported ℤ ℤ B) (h : (a : S →₀ ℤ) + (b : S →₀ ℤ) = 0) : (a : S →₀ ℤ) ∈ Finsupp.supported ℤ ℤ (A ∩ B) := by
  have ha : (a : S →₀ ℤ) = -(b : S →₀ ℤ) := eq_neg_of_add_eq_zero_left h
  rw [Finsupp.supported_inter]
  exact ⟨a.property, ha ▸ (Finsupp.supported ℤ ℤ B).neg_mem b.property⟩

/-- `0 → ℤ[A ∩ B] → ℤ[A] ⊕ ℤ[B] → ℤ[A ∪ B] → 0` is exact (`lem:mv-ses`, its exactness, with `S`
the singular `n`-simplices of `X`, and `A`, `B` those in `U` and in `V`). -/
theorem mv_ses {S : Type*} (A B : Set S) :
    Function.Injective (φ A B) ∧ LinearMap.range (φ A B) = LinearMap.ker (ψ A B) ∧
      Function.Surjective (ψ A B) := by
  constructor
  · intro c d h
    apply Subtype.ext
    have hfst := congrArg Prod.fst h
    exact congrArg (fun z : Finsupp.supported ℤ ℤ A => (z : S →₀ ℤ)) hfst
  · constructor
    · ext p
      simp only [LinearMap.mem_range, LinearMap.mem_ker]
      constructor
      · rintro ⟨c, rfl⟩
        apply Subtype.ext
        change (c : S →₀ ℤ) + -(c : S →₀ ℤ) = 0
        exact add_neg_cancel _
      · intro hp
        rcases p with ⟨a, b⟩
        have hp' := congrArg (fun z : Finsupp.supported ℤ ℤ (A ∪ B) => (z : S →₀ ℤ)) hp
        change (a : S →₀ ℤ) + (b : S →₀ ℤ) = 0 at hp'
        let c : Finsupp.supported ℤ ℤ (A ∩ B) :=
          ⟨(a : S →₀ ℤ), cycle_supported A B a b hp'⟩
        refine ⟨c, ?_⟩
        apply Prod.ext
        · apply Subtype.ext
          rfl
        · apply Subtype.ext
          change -(a : S →₀ ℤ) = (b : S →₀ ℤ)
          calc
            -(a : S →₀ ℤ) = -(a : S →₀ ℤ) + ((a : S →₀ ℤ) + (b : S →₀ ℤ)) := by rw [hp', add_zero]
            _ = (b : S →₀ ℤ) := by simp only [← add_assoc, neg_add_cancel, zero_add]
    · intro c
      obtain ⟨a, b, hab⟩ := chain_decomposition A B c
      refine ⟨(a, b), ?_⟩
      apply Subtype.ext
      change (a : S →₀ ℤ) + (b : S →₀ ℤ) = (c : S →₀ ℤ)
      exact hab

end Week13MayerVietoris
