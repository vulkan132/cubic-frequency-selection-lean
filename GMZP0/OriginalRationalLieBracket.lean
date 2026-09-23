import GMZP0.OriginalLeftInvariantCoordinates
import GMZP0.OriginalChartLieBracket

/-! The original multiplication gives rational structure coefficients
for the actual Mathlib Lie bracket in the original tangent basis. -/
noncomputable section
open Module MvPolynomial
open scoped Manifold
namespace GMZP0
variable {sigma : Type*} [Fintype sigma]

/-- Rational coefficients from the actual left-invariant coordinate fields. -/
def originalRationalLieCoefficient (p : sigma → MvPolynomial (sigma ⊕ sigma) ℚ)
    (c : sigma → ℚ) (i j k : sigma) : ℚ :=
  eval c (pderiv i (originalLeftBasisPolynomial p c j k)) -
    eval c (pderiv j (originalLeftBasisPolynomial p c i k))

/-- The genuine tangent-space basis whose coordinates are the standard
vectors in the original global chart. -/
def originalTangentBasis {G : Type*} [Group G] [TopologicalSpace G]
    (coord : G ≃ₜ (sigma → ℝ)) :
    letI := coord.isOpenEmbedding.singletonChartedSpace
    Basis sigma ℝ (GroupLieAlgebra 𝓘(ℝ, sigma → ℝ) G) := by
  let := coord.isOpenEmbedding.singletonChartedSpace
  exact Pi.basisFun ℝ sigma

set_option backward.isDefEq.respectTransparency false in
/-- The actual bracket of the original coordinate tangent basis has
rational coefficients computed from the original group law. -/
theorem original_lie_bracket_rational_coordinates
    {G : Type*} [Group G] [TopologicalSpace G] [DecidableEq sigma]
    (coord : G ≃ₜ (sigma → ℝ))
    (p : sigma → MvPolynomial (sigma ⊕ sigma) ℚ)
    (hmul : ∀ g h k, coord (g * h) k = aeval (Sum.elim (coord g) (coord h)) (p k))
    (c : sigma → ℚ) (hc : coord 1 = fun s => (c s : ℝ)) (i j k : sigma) :
    letI := coord.isOpenEmbedding.singletonChartedSpace
    (show sigma → ℝ from
      @Bracket.bracket (GroupLieAlgebra 𝓘(ℝ, sigma → ℝ) G)
        (GroupLieAlgebra 𝓘(ℝ, sigma → ℝ) G) inferInstance
        (Pi.single i 1) (Pi.single j 1)) k =
      (originalRationalLieCoefficient p c i j k : ℝ) := by
  let := coord.isOpenEmbedding.singletonChartedSpace
  have hfields (j : sigma) :
      (mulInvariantVectorField (I := 𝓘(ℝ, sigma → ℝ)) (G := G) (Pi.single j 1)) ∘ coord.symm =
        fun x k => aeval x (originalLeftBasisPolynomial p c j k) := by
    funext x k
    simpa only [Function.comp_apply, coord.apply_symm_apply] using
      original_left_invariant_basis_coordinates coord p hmul c hc (coord.symm x) j k
  have hidentity (j : sigma) :
      (fun k => aeval (coord 1) (originalLeftBasisPolynomial p c j k)) = Pi.single j 1 := by
    funext k
    rw [← original_left_invariant_basis_coordinates coord p hmul c hc 1 j k]
    change (mfderiv 𝓘(ℝ, sigma → ℝ) 𝓘(ℝ, sigma → ℝ) (fun x : G => 1 * x) 1 (Pi.single j 1) : sigma → ℝ) k = _
    rw [show (fun x : G => 1 * x) = id from funext one_mul, mfderiv_id]
    rfl
  change (VectorField.mlieBracket 𝓘(ℝ, sigma → ℝ)
    (mulInvariantVectorField (I := 𝓘(ℝ, sigma → ℝ)) (G := G) (Pi.single i 1))
    (mulInvariantVectorField (I := 𝓘(ℝ, sigma → ℝ)) (G := G) (Pi.single j 1)) (1 : G) : sigma → ℝ) k = _
  rw [original_chart_lie_bracket coord, hfields, hfields]
  change (fderiv ℝ (fun x k => aeval x (originalLeftBasisPolynomial p c j k)) (coord 1)
    (fun k => aeval (coord 1) (originalLeftBasisPolynomial p c i k))) k -
    (fderiv ℝ (fun x k => aeval x (originalLeftBasisPolynomial p c i k)) (coord 1)
    (fun k => aeval (coord 1) (originalLeftBasisPolynomial p c j k))) k = _
  rw [hidentity, hidentity, rational_polynomial_array_fderiv_apply,
    rational_polynomial_array_fderiv_apply]
  simp [Pi.single_apply, hc, ← rational_polynomial_eval_cast, originalRationalLieCoefficient]

set_option backward.isDefEq.respectTransparency false in
/-- The actual Lie bracket is rational in the same original tangent basis. -/
theorem original_tangent_basis_rational
    {G : Type*} [Group G] [TopologicalSpace G]
    (coord : G ≃ₜ (sigma → ℝ))
    (p : sigma → MvPolynomial (sigma ⊕ sigma) ℚ)
    (hmul : ∀ g h k, coord (g * h) k = aeval (Sum.elim (coord g) (coord h)) (p k))
    (c : sigma → ℚ) (hc : coord 1 = fun s => (c s : ℝ)) (i j k : sigma) :
    letI := coord.isOpenEmbedding.singletonChartedSpace
    (originalTangentBasis coord).repr
      (@Bracket.bracket (GroupLieAlgebra 𝓘(ℝ, sigma → ℝ) G)
        (GroupLieAlgebra 𝓘(ℝ, sigma → ℝ) G) inferInstance
        (originalTangentBasis coord i) (originalTangentBasis coord j)) k =
        (originalRationalLieCoefficient p c i j k : ℝ) := by
  classical
  let := coord.isOpenEmbedding.singletonChartedSpace
  have hi : originalTangentBasis coord i = (Pi.single i 1 : sigma → ℝ) := Pi.basisFun_apply ℝ sigma i
  have hj : originalTangentBasis coord j = (Pi.single j 1 : sigma → ℝ) := Pi.basisFun_apply ℝ sigma j
  have hrepr (v : GroupLieAlgebra 𝓘(ℝ, sigma → ℝ) G) :
      (originalTangentBasis coord).repr v k = (show sigma → ℝ from v) k := Pi.basisFun_repr ℝ sigma v k
  rw [hrepr, hi, hj]
  exact original_lie_bracket_rational_coordinates coord p hmul c hc i j k

end GMZP0
