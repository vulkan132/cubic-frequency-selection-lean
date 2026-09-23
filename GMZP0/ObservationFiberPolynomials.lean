import GMZP0.ObservationInfinitesimal
import GMZP0.RationalObservationInverse

/-! Literal rational polynomial arrays for a polynomial in the actual
observation differential, retaining every original fiber coefficient. -/
noncomputable section
open Module MvPolynomial
namespace GMZP0
variable {sigma iota : Type*} [Fintype sigma] [Fintype iota]

/-- The actual differential matrix, with all tangent variables retained. -/
def differentialMatrixPolynomial (A : iota → iota → sigma → ℚ) (i j : iota) :
    MvPolynomial (sigma ⊕ iota) ℚ :=
  ∑ s, C (A i j s) * X (Sum.inl s)

/-- Apply the same differential n times to the original fiber variables. -/
def iteratedDifferentialPolynomial (A : iota → iota → sigma → ℚ) :
    ℕ → iota → MvPolynomial (sigma ⊕ iota) ℚ
  | 0, i => X (Sum.inr i)
  | n + 1, i => ∑ j, differentialMatrixPolynomial A i j *
      iteratedDifferentialPolynomial A n j

/-- A fixed rational operator polynomial gives one fixed full-coordinate array. -/
def fiberOperatorPolynomial (A : iota → iota → sigma → ℚ)
    (E : Polynomial ℚ) (i : iota) : MvPolynomial (sigma ⊕ iota) ℚ :=
  ∑ n ∈ Finset.range (E.natDegree + 1), C (E.coeff n) * iteratedDifferentialPolynomial A n i

omit [Fintype iota] in
/-- The literal matrix evaluates to the original tangent-linear matrix. -/
theorem differential_matrix_polynomial_eval (A : iota → iota → sigma → ℚ)
    (v : sigma → ℝ) (w : iota → ℝ) (i j : iota) :
    aeval (Sum.elim v w) (differentialMatrixPolynomial A i j) =
      ∑ s, (A i j s : ℝ) * v s := by
  simp [differentialMatrixPolynomial]

/-- Every iterated array evaluates to the actual endomorphism power. -/
theorem iterated_differential_polynomial_eval {G : Type*} [Group G]
    (V : ObservationModule G) (b : Basis iota ℝ V.space)
    (A : iota → iota → sigma → ℚ) (v : sigma → ℝ) (Q : V.space)
    (n : ℕ) (i : iota) :
    aeval (Sum.elim v (b.equivFun Q)) (iteratedDifferentialPolynomial A n i) =
      b.equivFun (((observationCoordinateDifferential V b A v) ^ n) Q) i := by
  induction n generalizing i with
  | zero => simp [iteratedDifferentialPolynomial]
  | succ n ih =>
    rw [pow_succ']
    change _ = b.equivFun (observationCoordinateDifferential V b A v
      (((observationCoordinateDifferential V b A v) ^ n) Q)) i
    rw [observation_coordinate_differential_repr]
    simp only [iteratedDifferentialPolynomial, map_sum, map_mul,
      differential_matrix_polynomial_eval, ih]

/-- Rational polynomial evaluation on a real endomorphism uses the same
real scalar coefficients after restriction of scalars. -/
theorem rational_endomorphism_polynomial_apply {W : Type*}
    [AddCommGroup W] [Module ℝ W] (D : Module.End ℝ W) (E : Polynomial ℚ) (Q : W) :
    letI := Algebra.restrictScalars ℚ ℝ (Module.End ℝ W)
    Polynomial.aeval D E Q =
      ∑ n ∈ Finset.range (E.natDegree + 1), (E.coeff n : ℝ) • ((D ^ n) Q) := by
  let := Algebra.restrictScalars ℚ ℝ (Module.End ℝ W)
  rw [Polynomial.aeval_eq_sum_range]
  simp only [LinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro n _
  rfl

/-- The full literal fiber array equals the original polynomial operator
on every unrestricted original tangent and observation. -/
theorem fiber_operator_polynomial_eval {G : Type*} [Group G]
    (V : ObservationModule G) (b : Basis iota ℝ V.space)
    (A : iota → iota → sigma → ℚ) (E : Polynomial ℚ)
    (v : sigma → ℝ) (Q : V.space) (i : iota) :
    letI := Algebra.restrictScalars ℚ ℝ (Module.End ℝ V.space)
    aeval (Sum.elim v (b.equivFun Q)) (fiberOperatorPolynomial A E i) =
      b.equivFun (Polynomial.aeval (observationCoordinateDifferential V b A v) E Q) i := by
  let := Algebra.restrictScalars ℚ ℝ (Module.End ℝ V.space)
  rw [rational_endomorphism_polynomial_apply]
  simp only [fiberOperatorPolynomial, map_sum, map_mul, aeval_C,
    iterated_differential_polynomial_eval, map_smul, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul]
  simp

end GMZP0
