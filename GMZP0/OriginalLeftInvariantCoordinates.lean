import GMZP0.OriginalChartDifferential
import GMZP0.RationalCoordinateDifferential

/-! Rational polynomial coordinates of the actual left-invariant basis
fields used by Mathlib's Lie algebra, from the original multiplication. -/
noncomputable section
open Module MvPolynomial
open scoped Manifold
namespace GMZP0
variable {sigma : Type*} [Fintype sigma]

/-- Differentiate the second input of the original multiplication and
substitute the actual rational identity there. -/
def originalLeftBasisPolynomial (p : sigma → MvPolynomial (sigma ⊕ sigma) ℚ)
    (c : sigma → ℚ) (j k : sigma) : MvPolynomial sigma ℚ :=
  aeval (Sum.elim X (fun s => C (c s))) (pderiv (Sum.inr j) (p k))

omit [Fintype sigma] in
/-- The literal rational array evaluates to the correct second-input partial. -/
theorem original_left_basis_polynomial_eval
    (p : sigma → MvPolynomial (sigma ⊕ sigma) ℚ) (c : sigma → ℚ)
    (x : sigma → ℝ) (j k : sigma) :
    aeval x (originalLeftBasisPolynomial p c j k) =
      aeval (Sum.elim x (fun s => (c s : ℝ))) (pderiv (Sum.inr j) (p k)) := by
  rw [originalLeftBasisPolynomial, comp_aeval_apply]
  apply congrArg (fun z : (sigma ⊕ sigma) → ℝ => aeval z (pderiv (Sum.inr j) (p k)))
  funext s
  cases s <;> simp

set_option backward.isDefEq.respectTransparency false in
/-- The actual standard left-invariant basis vector field has the
constructed rational coordinates. This is an identity in the original
manifold tangent space, not a substituted abstract Lie algebra. -/
theorem original_left_invariant_basis_coordinates
    {G : Type*} [Group G] [TopologicalSpace G] [DecidableEq sigma]
    (coord : G ≃ₜ (sigma → ℝ))
    (p : sigma → MvPolynomial (sigma ⊕ sigma) ℚ)
    (hmul : ∀ g h k, coord (g * h) k = aeval (Sum.elim (coord g) (coord h)) (p k))
    (c : sigma → ℚ) (hc : coord 1 = fun s => (c s : ℝ)) (g : G) (j k : sigma) :
    letI := coord.isOpenEmbedding.singletonChartedSpace
    mulInvariantVectorField (I := 𝓘(ℝ, sigma → ℝ)) (G := G) (Pi.single j 1) g k =
      aeval (coord g) (originalLeftBasisPolynomial p c j k) := by
  let := coord.isOpenEmbedding.singletonChartedSpace
  let f : (sigma → ℝ) → sigma → ℝ := coord ∘ (fun h => g * h) ∘ coord.symm
  have hfval : f = fun y k => aeval (Sum.elim (coord g) y) (p k) := by
    funext y k
    simp only [f, Function.comp_apply, hmul, coord.apply_symm_apply]
  have hf : DifferentiableAt ℝ f (coord 1) := by
    rw [hfval]
    apply differentiableAt_pi.mpr
    intro k
    apply (rational_coordinate_polynomial_contDiff 1 (p k)
      (fun y => Sum.elim (coord g) y) ?_).differentiable_one (coord 1)
    intro s
    cases s with
    | inl s => exact contDiff_const
    | inr s => exact contDiff_apply ℝ ℝ s
  have hd : fderiv ℝ f (coord 1) (Pi.single j 1) =
      fun k => aeval (coord g) (originalLeftBasisPolynomial p c j k) := by
    apply coordinate_line_fderiv_apply _ _ _ _ hf
    apply hasDerivAt_pi.mpr
    intro k
    rw [hfval]
    have hh := rational_polynomial_hasDerivAt (p k)
      (fun t : ℝ => Sum.elim (coord g) (coord 1 + t • Pi.single j 1))
      (Sum.elim (fun _ => 0) (Pi.single j 1)) 0 (by
        intro s
        cases s with
        | inl s => exact hasDerivAt_const 0 _
        | inr s =>
          simpa using ((hasDerivAt_id (0 : ℝ)).mul_const ((Pi.single j 1 : sigma → ℝ) s)).const_add (coord 1 s))
    simpa [hc, original_left_basis_polynomial_eval, Fintype.sum_sum_type,
      Pi.single_apply] using hh
  rw [mulInvariantVectorField, original_mfderiv coord (fun h => g * h) 1 hf]
  exact congrFun hd k

end GMZP0
