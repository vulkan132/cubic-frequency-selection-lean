import GMZP0.PolynomialValueSpan
import Mathlib.Tactic.NormNum

/-! Exact obstruction to recovering coefficients from a restricted coordinate image. -/
noncomputable section
namespace GMZP0

/-- A nonzero linear polynomial vanishes on the coordinate image {0}; its coefficient survives. -/
theorem polynomial_restricted_parameter_obstruction :
    let P : MvPolynomial Unit ℝ := MvPolynomial.X ()
    (∀ x : Unit → ℝ, x () = 0 → MvPolynomial.eval x P = 0) ∧
      MvPolynomial.coeff (Finsupp.single () 1) P = 1 := by
  constructor
  · intro x hx
    simpa using hx
  · simp [MvPolynomial.X, MvPolynomial.coeff_monomial]

end GMZP0
