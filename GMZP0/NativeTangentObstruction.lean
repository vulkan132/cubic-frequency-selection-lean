import Mathlib.Analysis.Calculus.Deriv.Abs

/-! An exact obstruction to replacing a derivative proposition by the
value of a totalized derivative. This is not a P0 counterexample. -/
namespace GMZP0

/-- Absolute value has totalized derivative zero at zero but no actual
zero derivative there. Tangent specifications must retain differentiability. -/
theorem totalized_derivative_tangent_obstruction :
    deriv (abs : ℝ → ℝ) 0 = 0 ∧ ¬ HasDerivAt (abs : ℝ → ℝ) 0 0 := by
  exact ⟨deriv_abs_zero, fun h => not_differentiableAt_abs_zero h.differentiableAt⟩

end GMZP0
