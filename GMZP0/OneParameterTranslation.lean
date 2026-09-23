import GMZP0.FiniteDerivativeTower
import GMZP0.InfinitesimalNilpotent

/-! Actual one-parameter base subgroups turn the original infinitesimal
translation into its exact finite exponential series. The base subgroup
law is explicit and is never inferred from an arbitrary coordinate curve. -/
noncomputable section
open Module
namespace GMZP0
variable {G : Type*} [Group G]

/-- The full real parameter composition law forces the original
identity at zero; it is not an independent initial-value assumption. -/
theorem one_parameter_zero (gamma : ℝ → G)
    (hadd : ∀ s t, gamma (s + t) = gamma s * gamma t) : gamma 0 = 1 := by
  have h : gamma 0 * 1 = gamma 0 * gamma 0 := by simpa using hadd 0 0
  exact (mul_left_cancel h).symm

set_option backward.isDefEq.respectTransparency false in
/-- Translate the actual derivative at zero to every real time using
the original subgroup law, with the original pullback order intact. -/
theorem one_parameter_translation_hasDerivAt
    (V : ObservationModule G) (gamma : ℝ → G)
    (hadd : ∀ s t, gamma (s + t) = gamma s * gamma t)
    (D : Module.End ℝ V.space)
    (hder : ∀ (F : V.space) (u : G),
      HasDerivAt (fun t => F (gamma t * u)) (D F u) 0)
    (F : V.space) (u : G) (t : ℝ) :
    HasDerivAt (fun s => F (gamma s * u)) (D F (gamma t * u)) t := by
  have hz : HasDerivAt (fun s => F (gamma s * (gamma t * u)))
      (D F (gamma t * u)) (t - t) := by simpa only [sub_self] using hder F (gamma t * u)
  have hh := hz.comp_sub_const t t
  convert! hh using 1
  funext s
  rw [← mul_assoc, ← hadd, sub_add_cancel]

/-- Every actual original translation along the subgroup is the finite
nilpotent exponential. Equality holds as an endomorphism of the entire
original observation space at every real time. -/
theorem one_parameter_translation_finite_series
    (V : ObservationModule G) (gamma : ℝ → G)
    (hadd : ∀ s t, gamma (s + t) = gamma s * gamma t)
    (D : Module.End ℝ V.space) (K : ℕ) (hD : D ^ K = 0)
    (hder : ∀ (F : V.space) (u : G),
      HasDerivAt (fun t => F (gamma t * u)) (D F u) 0)
    (t : ℝ) :
    observationTranslate V (gamma t) =
      ∑ j ∈ Finset.range K, (t ^ j / (j.factorial : ℝ)) • D ^ j := by
  apply LinearMap.ext
  intro F
  apply Subtype.ext
  funext u
  let f : ℕ → ℝ → ℝ := fun j s => (D ^ j) F (gamma s * u)
  have hf : ∀ j s, HasDerivAt (f j) (f (j + 1) s) s := by
    intro j s
    simpa only [f, pow_succ', Module.End.mul_apply] using
      one_parameter_translation_hasDerivAt V gamma hadd D hder ((D ^ j) F) u s
  have hz : ∀ s, f K s = 0 := by
    intro s
    simp [f, hD]
  have he := finite_derivative_tower_exact K f hf hz t
  change F (gamma t * u) = observationEvaluation V u
    ((∑ j ∈ Finset.range K, (t ^ j / (j.factorial : ℝ)) • D ^ j) F)
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, smul_eq_mul]
  simpa only [finiteDerivativeTaylor, f, pow_zero, Module.End.one_apply,
    one_parameter_zero gamma hadd, one_mul, observationEvaluation_apply] using he

end GMZP0
