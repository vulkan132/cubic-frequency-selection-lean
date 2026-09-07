import GMZP0.CircleCharacter
import GMZP0.LagGeometry

/-! The actual product of original horizontal kernel entries has the manuscript's double phase. -/

noncomputable section
open scoped BigOperators ComplexConjugate
namespace GMZP0

/-- The N^(-4) kernel product and its circle phase are exact at a shared original target. -/
theorem double_kernel_original_phase {N : ℕ} (p : Base N → Frequency)
    (x x' : Fin N) (hx : x ≠ x') (y t v : Fin (N ^ 2))
    (r s r' s' : Fin N)
    (he : endpointIndex (x, y) r = endpointIndex (x', v) s)
    (he' : endpointIndex (x, t) r' = endpointIndex (x', v) s') :
    horizontalKernel N p x x' y v * conj (horizontalKernel N p x x' t v) =
      circleCharacter (doublePhaseCoefficient (p (x, y)) (p (x, t)) (p (x', v))
        (horizontalGap x x') ((label r : ℤ) - (label r' : ℤ)) (label r')) / (N : ℂ) ^ 4 := by
  have hg := double_collision_coordinates x x' y t v r s r' s' he he'
  rw [horizontalKernel_of_collision p x x' hx y v r s he,
    horizontalKernel_of_collision p x x' hx t v r' s' he']
  simp only [cubicPhase_integer, map_div₀, map_pow, map_natCast]
  rw [div_mul_div_comm]
  have hr : (label r : ℤ) = (label r' : ℤ) + ((label r : ℤ) - (label r' : ℤ)) := by ring
  have hphase := double_phase_character (p (x, y)) (p (x, t)) (p (x', v))
    (horizontalGap x x') ((label r : ℤ) - (label r' : ℤ)) (label r')
  have hnum : (integerCubicPhase (p (x, y)) (label r) *
      conj (integerCubicPhase (p (x', v)) (label s))) *
      conj (integerCubicPhase (p (x, t)) (label r') *
        conj (integerCubicPhase (p (x', v)) (label s'))) =
      circleCharacter (doublePhaseCoefficient (p (x, y)) (p (x, t)) (p (x', v))
        (horizontalGap x x') ((label r : ℤ) - (label r' : ℤ)) (label r')) := by
    rw [← hr] at hphase
    rw [hg.1, hg.2.1]
    exact hphase
  rw [hnum]
  congr 1
  ring

/-- Multiplying by the original weights gives the exact signed summand, including its scale. -/
theorem double_kernel_original_weighted_phase {N : ℕ} (p : Base N → Frequency)
    (σ : Base N → ℝ) (lam : Base N → ℂ)
    (x x' : Fin N) (hx : x ≠ x') (y t v : Fin (N ^ 2))
    (r s r' s' : Fin N)
    (he : endpointIndex (x, y) r = endpointIndex (x', v) s)
    (he' : endpointIndex (x, t) r' = endpointIndex (x', v) s') :
    (horizontalKernel N p x x' y v * conj (horizontalKernel N p x x' t v) *
      alignedWeightVector σ lam (x, t) * conj (alignedWeightVector σ lam (x, y))).re =
      (σ (x, y) * σ (x, t) *
        (lam (x, y) * conj (lam (x, t)) *
          circleCharacter (doublePhaseCoefficient (p (x, y)) (p (x, t)) (p (x', v))
            (horizontalGap x x') ((label r : ℤ) - (label r' : ℤ)) (label r'))).re) / (N : ℝ) ^ 4 := by
  rw [double_kernel_original_phase p x x' hx y t v r s r' s' he he']
  simp only [alignedWeightVector, map_mul, Complex.conj_ofReal, starRingEnd_self_apply]
  have hscalar (A : ℂ) :
      A / (N : ℂ) ^ 4 * ((σ (x, t) : ℂ) * conj (lam (x, t))) *
        ((σ (x, y) : ℂ) * lam (x, y)) =
      ((σ (x, y) * σ (x, t) : ℝ) : ℂ) * (lam (x, y) * conj (lam (x, t)) * A) / (N : ℂ) ^ 4 := by
    push_cast
    ring
  rw [hscalar]
  have hcast : (N : ℂ) ^ 4 = ((N : ℝ) ^ 4 : ℝ) := by norm_cast
  rw [hcast, Complex.div_ofReal_re, Complex.re_ofReal_mul]

end GMZP0
