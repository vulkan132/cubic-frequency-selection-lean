import GMZP0.RationalObservationTranslation
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.LinearAlgebra.Matrix.ToLin

/-! Analytic derivatives of the original rational polynomial coordinates.
The formula holds along every differentiable actual coordinate curve; no
coordinate curve is silently declared to be a Lie exponential. -/
noncomputable section
open Module MvPolynomial
namespace GMZP0

set_option backward.isDefEq.respectTransparency false in
/-- The formal rational partial derivatives give the actual analytic
derivative along every differentiable real coordinate curve. -/
theorem rational_polynomial_hasDerivAt {sigma : Type*} [Fintype sigma]
    (p : MvPolynomial sigma ℚ) (x : ℝ → sigma → ℝ) (v : sigma → ℝ) (t : ℝ)
    (hx : ∀ i, HasDerivAt (fun s => x s i) (v i) t) :
    HasDerivAt (fun s => MvPolynomial.aeval (x s) p)
      (∑ i, MvPolynomial.aeval (x t) (MvPolynomial.pderiv i p) * v i) t := by
  classical
  induction p using MvPolynomial.induction_on with
  | C a => simpa [MvPolynomial.pderiv_C] using (hasDerivAt_const t (a : ℝ))
  | add p q hp hq =>
    convert! hp.add hq using 1
    · funext s
      simp
    · simp [add_mul, Finset.sum_add_distrib]
  | mul_X p j hp =>
    convert! hp.mul (hx j) using 1
    · funext s
      simp
    · simp only [MvPolynomial.pderiv_mul, map_add, map_mul, MvPolynomial.aeval_X,
        MvPolynomial.pderiv_X, Pi.single_apply]
      simp only [add_mul, Finset.sum_add_distrib, mul_assoc, mul_comm (x t j),
        ← Finset.mul_sum]
      simp [mul_comm, mul_assoc, Finset.mul_sum]

/-- At rational original coordinates, the derivative coefficients are
rational; one fixed rational matrix acts linearly on every real tangent. -/
theorem rational_polynomial_derivative_at_rational {sigma : Type*} [Fintype sigma]
    (p : MvPolynomial sigma ℚ) (x : ℝ → sigma → ℝ) (c : sigma → ℚ)
    (v : sigma → ℝ) (t : ℝ) (hc : x t = fun i => (c i : ℝ))
    (hx : ∀ i, HasDerivAt (fun s => x s i) (v i) t) :
    HasDerivAt (fun s => MvPolynomial.aeval (x s) p)
      (∑ i, (MvPolynomial.eval c (MvPolynomial.pderiv i p) : ℝ) * v i) t := by
  have h := rational_polynomial_hasDerivAt p x v t hx
  simpa only [hc, ← rational_polynomial_eval_cast] using h

/-- A rational polynomial matrix which is the identity at zero need not
be a translation representation. Actual group-action identities matter
when identifying its derivative with an exponential generator. -/
theorem polynomial_identity_at_zero_not_translation_action :
    (1 + (0 : ℝ) = 1) ∧
      ¬ (∀ s t : ℝ, 1 + (s + t) = (1 + t) * (1 + s)) := by
  constructor
  · norm_num
  · intro h
    have h11 := h 1 1
    norm_num at h11

end GMZP0
