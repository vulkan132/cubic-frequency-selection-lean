import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.RingTheory.Nilpotent.Basic
import Mathlib.Tactic.Abel

/-! The finite fiber polynomial in the proposed observation exponential
has a fixed rational polynomial inverse whenever the generator has a
fixed nilpotency bound. Identifying this polynomial with the actual Lie
exponential is a separate obligation. -/
noncomputable section
open scoped BigOperators
namespace GMZP0
variable {A : Type*} [Ring A] [Algebra ℚ A]

/-- The finite fiber sum, with its zero-th identity term retained. -/
def nilpotentFiberMatrix (K : ℕ) (D : A) : A :=
  ∑ j ∈ Finset.range (K + 1), (((j + 1).factorial : ℚ)⁻¹) • D ^ j

/-- Factoring the positive-degree part leaves this finite polynomial. -/
def nilpotentFiberTail (K : ℕ) (D : A) : A :=
  ∑ j ∈ Finset.range K, (((j + 2).factorial : ℚ)⁻¹) • D ^ j

/-- A bounded geometric sum provides the two-sided inverse. -/
def nilpotentFiberInverse (K : ℕ) (D : A) : A :=
  ∑ j ∈ Finset.range K, (1 - nilpotentFiberMatrix K D) ^ j

/-- The exact fiber sum is the identity plus a multiple of the generator. -/
theorem nilpotent_fiber_matrix_factor (K : ℕ) (D : A) :
    nilpotentFiberMatrix K D = 1 + D * nilpotentFiberTail K D := by
  classical
  rw [nilpotentFiberMatrix, Finset.sum_range_succ']
  simp only [Nat.zero_add, Nat.factorial_one, Nat.cast_one, inv_one, pow_zero, one_smul]
  rw [add_comm]
  congr 1
  rw [nilpotentFiberTail, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [mul_smul_comm, ← pow_succ']

/-- The fiber correction has the same uniform nilpotency exponent. -/
theorem nilpotent_fiber_correction_pow_zero (K : ℕ) (D : A) (hD : D ^ K = 0) :
    (1 - nilpotentFiberMatrix K D) ^ K = 0 := by
  have hc : Commute D (nilpotentFiberTail K D) := by
    apply Commute.sum_right
    intro j _
    exact (Commute.self_pow D j).smul_right _
  have he : 1 - nilpotentFiberMatrix K D = -(D * nilpotentFiberTail K D) := by
    rw [nilpotent_fiber_matrix_factor]
    abel
  rw [he, neg_pow, hc.mul_pow, hD, zero_mul, mul_zero]

/-- The explicitly bounded polynomial inverse works in both orders,
including noncommutative endomorphism algebras. -/
theorem nilpotent_fiber_inverse_two_sided (K : ℕ) (D : A) (hD : D ^ K = 0) :
    nilpotentFiberInverse K D * nilpotentFiberMatrix K D = 1 ∧
      nilpotentFiberMatrix K D * nilpotentFiberInverse K D = 1 := by
  have hB := nilpotent_fiber_correction_pow_zero K D hD
  constructor
  · simpa only [sub_sub_cancel, hB, sub_zero, nilpotentFiberInverse] using
      (geom_sum_mul_neg (1 - nilpotentFiberMatrix K D) K)
  · simpa only [sub_sub_cancel, hB, sub_zero, nilpotentFiberInverse] using
      (mul_neg_geom_sum (1 - nilpotentFiberMatrix K D) K)

/-- A fixed rational polynomial for the fiber map, independent of D. -/
def nilpotentFiberPolynomial (K : ℕ) : Polynomial ℚ :=
  ∑ j ∈ Finset.range (K + 1), Polynomial.C (((j + 1).factorial : ℚ)⁻¹) * Polynomial.X ^ j

/-- A fixed rational polynomial for its inverse, with the same K. -/
def nilpotentFiberInversePolynomial (K : ℕ) : Polynomial ℚ :=
  ∑ j ∈ Finset.range K, (1 - nilpotentFiberPolynomial K) ^ j

/-- Evaluation of the fixed rational polynomial gives the actual finite sum. -/
theorem nilpotent_fiber_polynomial_eval (K : ℕ) (D : A) :
    Polynomial.aeval D (nilpotentFiberPolynomial K) = nilpotentFiberMatrix K D := by
  simp [nilpotentFiberPolynomial, nilpotentFiberMatrix, Algebra.smul_def]

/-- The inverse also has one literal rational polynomial before every D. -/
theorem nilpotent_fiber_inverse_polynomial_eval (K : ℕ) (D : A) :
    Polynomial.aeval D (nilpotentFiberInversePolynomial K) = nilpotentFiberInverse K D := by
  simp [nilpotentFiberInversePolynomial, nilpotentFiberInverse, nilpotent_fiber_polynomial_eval]

/-- One pair of rational polynomials works for every generator killed
by the fixed power K, with no coefficient bound on that generator. -/
theorem uniform_nilpotent_fiber_polynomial_inverse (K : ℕ) :
    ∃ p q : Polynomial ℚ, ∀ D : A, D ^ K = 0 →
      Polynomial.aeval D p = nilpotentFiberMatrix K D ∧
      Polynomial.aeval D q * Polynomial.aeval D p = 1 ∧
      Polynomial.aeval D p * Polynomial.aeval D q = 1 := by
  refine ⟨nilpotentFiberPolynomial K, nilpotentFiberInversePolynomial K, ?_⟩
  intro D hD
  rw [nilpotent_fiber_polynomial_eval, nilpotent_fiber_inverse_polynomial_eval]
  exact ⟨rfl, nilpotent_fiber_inverse_two_sided K D hD⟩

end GMZP0
