import GMZP0.OneParameterTranslation
import GMZP0.NilpotentFiberPolynomial
import Mathlib.Algebra.Algebra.RestrictScalars

/-! The original finite fiber path is an actual cocycle along a genuine
base one-parameter subgroup, with the correct right semidirect order.
Its time-one value is the exact finite polynomial from the manuscript. -/
noncomputable section
open Module
namespace GMZP0

/-- Integrate the finite translation series with zero initial value. -/
def nilpotentFiberPath {E : Type*} [AddCommGroup E] [Module ℝ E]
    (K : ℕ) (D : Module.End ℝ E) (t : ℝ) : Module.End ℝ E :=
  ∑ j ∈ Finset.range K, (t ^ (j + 1) / ((j + 1).factorial : ℝ)) • D ^ j

/-- The actual fiber starts at zero, for every original vector. -/
theorem nilpotent_fiber_path_zero {E : Type*} [AddCommGroup E] [Module ℝ E]
    (K : ℕ) (D : Module.End ℝ E) : nilpotentFiberPath K D 0 = 0 := by
  simp [nilpotentFiberPath]

variable {G : Type*} [Group G]

/-- Literal evaluation of the finite fiber path retains every original
function value and every real time. -/
theorem nilpotent_fiber_path_eval
    (V : ObservationModule G) (K : ℕ) (D : Module.End ℝ V.space)
    (t : ℝ) (Q : V.space) (u : G) :
    nilpotentFiberPath K D t Q u =
      ∑ j ∈ Finset.range K, (t ^ (j + 1) / ((j + 1).factorial : ℝ)) * (D ^ j) Q u := by
  change observationEvaluation V u ((nilpotentFiberPath K D t) Q) = _
  simp only [nilpotentFiberPath, LinearMap.sum_apply, LinearMap.smul_apply,
    map_sum, map_smul, smul_eq_mul, observationEvaluation_apply]

set_option backward.isDefEq.respectTransparency false in
/-- The derivative of the actual finite fiber path is the original
translated observation at every original group point and real time. -/
theorem nilpotent_fiber_path_hasDerivAt
    (V : ObservationModule G) (gamma : ℝ → G)
    (hadd : ∀ s t, gamma (s + t) = gamma s * gamma t)
    (D : Module.End ℝ V.space) (K : ℕ) (hD : D ^ K = 0)
    (hder : ∀ (F : V.space) (u : G),
      HasDerivAt (fun t => F (gamma t * u)) (D F u) 0)
    (Q : V.space) (u : G) (t : ℝ) :
    HasDerivAt (fun s => nilpotentFiberPath K D s Q u) (Q (gamma t * u)) t := by
  classical
  have hh := HasDerivAt.fun_sum (u := Finset.range K) fun j _ =>
    (factorial_power_hasDerivAt j t).mul_const ((D ^ j) Q u)
  convert! hh using 1
  · funext s
    exact nilpotent_fiber_path_eval V K D s Q u
  · have he := congrArg (fun L : Module.End ℝ V.space => observationEvaluation V u (L Q))
      (one_parameter_translation_finite_series V gamma hadd D K hD hder t)
    simpa only [LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul,
      smul_eq_mul, observationEvaluation_apply, observationTranslate_apply] using he

set_option backward.isDefEq.respectTransparency false in
/-- The finite fiber satisfies the actual right semidirect cocycle
identity. This proves the group law for the lifted one-parameter path. -/
theorem nilpotent_fiber_path_cocycle
    (V : ObservationModule G) (gamma : ℝ → G)
    (hadd : ∀ s t, gamma (s + t) = gamma s * gamma t)
    (D : Module.End ℝ V.space) (K : ℕ) (hD : D ^ K = 0)
    (hder : ∀ (F : V.space) (u : G),
      HasDerivAt (fun t => F (gamma t * u)) (D F u) 0)
    (Q : V.space) (s t : ℝ) :
    nilpotentFiberPath K D (s + t) Q =
      observationTranslate V (gamma t) (nilpotentFiberPath K D s Q) + nilpotentFiberPath K D t Q := by
  apply Subtype.ext
  funext u
  let f : ℝ → ℝ := fun r => nilpotentFiberPath K D (r + t) Q u
  let g : ℝ → ℝ := fun r =>
    nilpotentFiberPath K D r Q (gamma t * u) + nilpotentFiberPath K D t Q u
  let d : ℝ → ℝ := fun r => Q (gamma (r + t) * u)
  have hf : ∀ r, HasDerivAt f (d r) r := by
    intro r
    exact (nilpotent_fiber_path_hasDerivAt V gamma hadd D K hD hder Q u (r + t)).comp_add_const r t
  have hg : ∀ r, HasDerivAt g (d r) r := by
    intro r
    have hh := (nilpotent_fiber_path_hasDerivAt V gamma hadd D K hD hder Q (gamma t * u) r).add_const
      (nilpotentFiberPath K D t Q u)
    convert! hh using 1
    dsimp [d]
    rw [hadd, mul_assoc]
  have hzero : f 0 = g 0 := by simp [f, g, nilpotent_fiber_path_zero]
  exact real_functions_eq_of_derivative_and_initial f g d hf hg hzero s

/-- At time one the actual finite fiber is exactly the manuscript's
factorial polynomial. The last included term vanishes by the same K. -/
theorem nilpotent_fiber_path_one {E : Type*} [AddCommGroup E] [Module ℝ E]
    (K : ℕ) (D : Module.End ℝ E) (hD : D ^ K = 0) :
    letI := Algebra.restrictScalars ℚ ℝ (Module.End ℝ E)
    nilpotentFiberPath K D 1 = nilpotentFiberMatrix K D := by
  let := Algebra.restrictScalars ℚ ℝ (Module.End ℝ E)
  simp only [nilpotentFiberPath, one_pow, one_div, nilpotentFiberMatrix,
    Finset.sum_range_succ, hD, smul_zero, add_zero]
  apply Finset.sum_congr rfl
  intro j _
  change (((j + 1).factorial : ℝ)⁻¹) • D ^ j =
    (((((j + 1).factorial : ℚ)⁻¹) : ℚ) : ℝ) • D ^ j
  simp

end GMZP0
