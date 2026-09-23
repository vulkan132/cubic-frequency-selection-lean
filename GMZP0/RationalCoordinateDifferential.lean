import GMZP0.RationalCoordinateLieGroup
import GMZP0.RationalPolynomialDerivative

/-! Actual Fréchet derivatives of rational polynomial arrays, including
their values on the original coordinate tangent vectors. -/
noncomputable section
open MvPolynomial
namespace GMZP0

/-- The derivative along a genuine coordinate line is the Fréchet
derivative applied to its tangent; the line is not asserted to be a subgroup. -/
theorem coordinate_line_fderiv_apply {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E → F) (x v : E) (w : F) (hf : DifferentiableAt ℝ f x)
    (hline : HasDerivAt (fun t : ℝ => f (x + t • v)) w 0) :
    fderiv ℝ f x v = w := by
  have hv : HasDerivAt (fun t : ℝ => x + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add x
  have hd := hf.hasFDerivAt.comp_hasDerivAt_of_eq 0 hv (by simp)
  exact hd.unique hline

/-- The original rational partial derivatives compute every actual
directional Fréchet derivative, without a supplied derivative formula. -/
theorem rational_polynomial_fderiv_apply {sigma : Type*} [Fintype sigma]
    (p : MvPolynomial sigma ℚ) (x v : sigma → ℝ) :
    fderiv ℝ (fun y => aeval y p) x v = ∑ i, aeval x (pderiv i p) * v i := by
  have hf : DifferentiableAt ℝ (fun y : sigma → ℝ => aeval y p) x :=
    (rational_coordinate_polynomial_contDiff 1 p (fun y => y)
      (fun i => contDiff_apply ℝ ℝ i)).differentiable_one x
  apply coordinate_line_fderiv_apply _ x v _ hf
  have hd := rational_polynomial_hasDerivAt p (fun t : ℝ => x + t • v) v 0 (by
    intro i
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (v i)).const_add (x i))
  simpa only [zero_smul, add_zero] using hd

/-- A rational polynomial array has the literal partial-derivative matrix
on every original coordinate tangent. -/
theorem rational_polynomial_array_fderiv_apply {sigma tau : Type*}
    [Fintype sigma] [Fintype tau] (P : tau → MvPolynomial sigma ℚ)
    (x v : sigma → ℝ) (j : tau) :
    fderiv ℝ (fun y => fun i => aeval y (P i)) x v j =
      ∑ i, aeval x (pderiv i (P j)) * v i := by
  have hf : DifferentiableAt ℝ (fun y : sigma → ℝ => fun i => aeval y (P i)) x := by
    apply differentiableAt_pi.mpr
    intro i
    exact (rational_coordinate_polynomial_contDiff 1 (P i) (fun y => y)
      (fun j => contDiff_apply ℝ ℝ j)).differentiable_one x
  have hd := coordinate_line_fderiv_apply (fun y : sigma → ℝ => fun i => aeval y (P i))
    x v (fun j => ∑ i, aeval x (pderiv i (P j)) * v i) hf (by
      apply hasDerivAt_pi.mpr
      intro j
      have hh := rational_polynomial_hasDerivAt (P j) (fun t : ℝ => x + t • v) v 0 (by
        intro i
        simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (v i)).const_add (x i))
      simpa only [zero_smul, add_zero] using hh)
  exact congrFun hd j

end GMZP0
