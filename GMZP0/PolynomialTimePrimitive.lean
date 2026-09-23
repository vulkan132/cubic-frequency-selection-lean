import GMZP0.FiniteDerivativeTower
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Algebra.Algebra.Rat

/-! Exact polynomial integration in the real time variable. Coefficients
may themselves be rational polynomials in all original tangent variables. -/
noncomputable section
namespace GMZP0

/-- The polynomial primitive with zero constant term, over any rational algebra. -/
def polynomialTimePrimitive {A : Type*} [CommRing A] [Algebra ℚ A]
    (p : Polynomial A) : Polynomial A :=
  ∑ n ∈ p.support, Polynomial.monomial (n + 1)
    (algebraMap ℚ A ((n + 1 : ℚ)⁻¹) * p.coeff n)

/-- Formal differentiation recovers every coefficient exactly. -/
theorem polynomial_time_primitive_derivative {A : Type*} [CommRing A] [Algebra ℚ A]
    (p : Polynomial A) : (polynomialTimePrimitive p).derivative = p := by
  classical
  rw [polynomialTimePrimitive, Polynomial.derivative_sum]
  have hterm (n : ℕ) :
      (Polynomial.monomial (n + 1)
        (algebraMap ℚ A ((n + 1 : ℚ)⁻¹) * p.coeff n)).derivative =
        Polynomial.monomial n (p.coeff n) := by
    rw [Polynomial.derivative_monomial_succ]
    have hn : (n + 1 : ℚ) ≠ 0 := by positivity
    have hmul : algebraMap ℚ A ((n + 1 : ℚ)⁻¹) * (n + 1 : A) = 1 := by
      calc
        _ = algebraMap ℚ A ((n + 1 : ℚ)⁻¹ * (n + 1)) := by simp
        _ = 1 := by rw [inv_mul_cancel₀ hn, map_one]
    congr 1
    calc
      _ = (algebraMap ℚ A ((n + 1 : ℚ)⁻¹) * (n + 1 : A)) * p.coeff n := by ring
      _ = p.coeff n := by rw [hmul, one_mul]
  simp_rw [hterm]
  exact p.sum_monomial_eq

/-- The primitive starts at zero after every coefficient specialization. -/
theorem polynomial_time_primitive_eval_zero
    {A B : Type*} [CommRing A] [Algebra ℚ A] [CommRing B]
    (f : A →+* B) (p : Polynomial A) :
    (polynomialTimePrimitive p).eval₂ f 0 = 0 := by
  classical
  simp [polynomialTimePrimitive, Polynomial.eval₂_finsetSum]

set_option backward.isDefEq.respectTransparency false in
/-- Any real specialization of the same algebraic primitive has the
required derivative at every real time. -/
theorem polynomial_time_primitive_hasDerivAt
    {A : Type*} [CommRing A] [Algebra ℚ A]
    (f : A →+* ℝ) (p : Polynomial A) (t : ℝ) :
    HasDerivAt (fun s => (polynomialTimePrimitive p).eval₂ f s) (p.eval₂ f t) t := by
  have h := ((polynomialTimePrimitive p).map f).hasDerivAt t
  simpa only [Polynomial.eval_map, Polynomial.derivative_map,
    polynomial_time_primitive_derivative] using h

end GMZP0
