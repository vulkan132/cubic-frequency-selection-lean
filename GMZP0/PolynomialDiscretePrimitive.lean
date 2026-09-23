import Mathlib.NumberTheory.BernoulliPolynomials
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Data.Real.Basic

/-! Exact discrete integration with rational coefficients. Its forward
difference is the original polynomial at every point, not merely on a
finite grid; coefficients may retain every original group coordinate. -/
noncomputable section
namespace GMZP0

/-- The zero-initial-value discrete primitive of a time monomial. -/
def rationalDiscreteMonomial (n : ℕ) : Polynomial ℚ :=
  Polynomial.C ((n + 1 : ℚ)⁻¹) *
    (Polynomial.bernoulli (n + 1) - Polynomial.C ((Polynomial.bernoulli (n + 1)).eval 0))

/-- The prescribed discrete primitive has zero initial value. -/
theorem rational_discrete_monomial_zero (n : ℕ) : (rationalDiscreteMonomial n).eval 0 = 0 := by
  simp [rationalDiscreteMonomial]

/-- Its forward difference is exactly the original monomial. -/
theorem rational_discrete_monomial_step (n : ℕ) :
    (rationalDiscreteMonomial n).comp (1 + Polynomial.X) - rationalDiscreteMonomial n =
      Polynomial.X ^ n := by
  have hn : (n + 1 : ℚ) ≠ 0 := by positivity
  simp only [rationalDiscreteMonomial, Polynomial.mul_comp, Polynomial.C_comp,
    Polynomial.sub_comp, Polynomial.bernoulli_comp_one_add_X, Nat.add_sub_cancel]
  have hfactor : Polynomial.C ((n + 1 : ℚ)⁻¹) * (n + 1 : Polynomial ℚ) = 1 := by
    calc
      _ = Polynomial.C ((n + 1 : ℚ)⁻¹ * (n + 1)) := by simp
      _ = 1 := by rw [inv_mul_cancel₀ hn, Polynomial.C_1]
  rw [nsmul_eq_mul]
  calc
    _ = (Polynomial.C ((n + 1 : ℚ)⁻¹) * (n + 1 : Polynomial ℚ)) * Polynomial.X ^ n := by push_cast; ring
    _ = Polynomial.X ^ n := by rw [hfactor, one_mul]

/-- Coefficientwise discrete integration over every rational algebra. -/
def polynomialDiscretePrimitive {A : Type*} [CommRing A] [Algebra ℚ A]
    (p : Polynomial A) : Polynomial A :=
  ∑ n ∈ p.support, Polynomial.C (p.coeff n) *
    (rationalDiscreteMonomial n).map (algebraMap ℚ A)

/-- Every coefficient specialization preserves the zero initial value. -/
theorem polynomial_discrete_primitive_eval_zero
    {A B : Type*} [CommRing A] [Algebra ℚ A] [CommRing B]
    (f : A →+* B) (p : Polynomial A) :
    (polynomialDiscretePrimitive p).eval₂ f 0 = 0 := by
  classical
  simp only [polynomialDiscretePrimitive, Polynomial.eval₂_finsetSum,
    Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_map]
  apply Finset.sum_eq_zero
  intro n _
  rw [Polynomial.eval₂_at_zero]
  have hz : (rationalDiscreteMonomial n).coeff 0 = 0 := by
    rw [Polynomial.coeff_zero_eq_eval_zero]
    exact rational_discrete_monomial_zero n
  rw [hz, map_zero, mul_zero]

/-- The whole discrete primitive has the original polynomial as its
exact forward difference, over the unchanged coefficient algebra. -/
theorem polynomial_discrete_primitive_step
    {A : Type*} [CommRing A] [Algebra ℚ A] (p : Polynomial A) :
    (polynomialDiscretePrimitive p).comp (1 + Polynomial.X) - polynomialDiscretePrimitive p = p := by
  classical
  simp only [polynomialDiscretePrimitive, Polynomial.sum_comp, ← Finset.sum_sub_distrib]
  have hterm (n : ℕ) :
      (Polynomial.C (p.coeff n) * (rationalDiscreteMonomial n).map (algebraMap ℚ A)).comp
          (1 + Polynomial.X) -
        Polynomial.C (p.coeff n) * (rationalDiscreteMonomial n).map (algebraMap ℚ A) =
        Polynomial.monomial n (p.coeff n) := by
    have hd := congrArg (Polynomial.map (algebraMap ℚ A)) (rational_discrete_monomial_step n)
    simp only [Polynomial.map_sub, Polynomial.map_comp, Polynomial.map_add,
      Polynomial.map_one, Polynomial.map_X, Polynomial.map_pow] at hd
    rw [Polynomial.mul_comp, Polynomial.C_comp, ← mul_sub, hd, Polynomial.C_mul_X_pow_eq_monomial]
  simp_rw [hterm]
  exact p.sum_monomial_eq

/-- The same forward-difference identity holds after every real
specialization, for all real times. -/
theorem polynomial_discrete_primitive_eval_step
    {A : Type*} [CommRing A] [Algebra ℚ A]
    (f : A →+* ℝ) (p : Polynomial A) (t : ℝ) :
    (polynomialDiscretePrimitive p).eval₂ f (t + 1) -
      (polynomialDiscretePrimitive p).eval₂ f t = p.eval₂ f t := by
  have h := congrArg (Polynomial.eval₂ f t) (polynomial_discrete_primitive_step p)
  simpa only [Polynomial.eval₂_sub, Polynomial.eval₂_comp, Polynomial.eval₂_add,
    Polynomial.eval₂_one, Polynomial.eval₂_X, add_comm 1 t] using h

end GMZP0
