import GMZP0.ObservationFiniteDimension
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition

/-! Finitely many actual subgroup evaluations determine a finite-dimensional
observation, when evaluations on the whole subgroup already separate it. -/
noncomputable section
open Module
namespace GMZP0
variable {G : Type*} [Group G]

/-- Actual point evaluation as a real linear functional on V. -/
def observationEvaluation (V : ObservationModule G) (g : G) : V.space →ₗ[ℝ] ℝ :=
  (LinearMap.proj g).comp V.space.subtype

/-- The evaluation functional reads the original function at the stated point. -/
@[simp] theorem observationEvaluation_apply (V : ObservationModule G) (g : G) (P : V.space) :
    observationEvaluation V g P = P g := rfl

/-- At most dim(V) actual subgroup points suffice; the chosen points retain their original provenance. -/
theorem observation_finite_determining_points (V : ObservationModule G)
    [FiniteDimensional ℝ V.space] (Gamma : Subgroup G)
    (hsep : ∀ P : V.space, (∀ gamma : Gamma, P gamma = 0) → P = 0) :
    ∃ n : ℕ, n ≤ Module.finrank ℝ V.space ∧ ∃ gamma : Fin n → Gamma,
      ∀ P : V.space, (∀ i, P (gamma i) = 0) → P = 0 := by
  classical
  let ev : Gamma → (V.space →ₗ[ℝ] ℝ) := fun g => observationEvaluation V g
  let U := Submodule.span ℝ (Set.range ev)
  obtain ⟨f, hf, hspan, _⟩ := Submodule.exists_fun_fin_finrank_span_eq ℝ (Set.range ev)
  choose gamma hgamma using hf
  refine ⟨Module.finrank ℝ U, ?_, gamma, ?_⟩
  · simpa only [Subspace.dual_finrank_eq] using Submodule.finrank_le U
  · intro P hP
    apply hsep P
    intro g
    let atP : (V.space →ₗ[ℝ] ℝ) →ₗ[ℝ] ℝ := LinearMap.applyₗ P
    have hker : Submodule.span ℝ (Set.range f) ≤ LinearMap.ker atP := by
      apply Submodule.span_le.mpr
      rintro _ ⟨i, rfl⟩
      change f i P = 0
      rw [← hgamma i]
      exact hP i
    rw [hspan] at hker
    exact hker (Submodule.subset_span ⟨g, rfl⟩)

end GMZP0
