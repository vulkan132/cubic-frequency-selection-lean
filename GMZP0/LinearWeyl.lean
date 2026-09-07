import GMZP0.MeanAlgebra
import GMZP0.RerootedBounds
import Mathlib.Algebra.Ring.GeomSum

/-! Quantitative linear exponential sums on the circle, including all affine intercepts. -/

noncomputable section
open scoped BigOperators
namespace GMZP0

theorem circleCharacter_nsmul (a : Frequency) (n : ℕ) :
    circleCharacter (n • a) = circleCharacter a ^ n := by
  induction n with
  | zero => simp [circleCharacter]
  | succ n ih => rw [succ_nsmul, circleCharacter_add, ih, pow_succ]

/-- The inverse chord estimate uses a nearest representative, with both signs retained. -/
theorem circle_norm_le_chord (a : Frequency) :
    4 * ‖a‖ ≤ ‖circleCharacter a - 1‖ := by
  obtain ⟨t, ht, hn⟩ := exists_nearest_frequency_lift a
  have htbound : |t| ≤ (1 : ℝ) / 2 := by
    rw [hn]
    simpa using AddCircle.norm_le_half_period (1 : ℝ) (x := a) one_ne_zero
  have harg : |Real.pi * t| ≤ Real.pi / 2 := by
    rw [abs_mul, abs_of_pos Real.pi_pos]
    nlinarith [Real.pi_pos]
  have hs := Real.mul_abs_le_abs_sin harg
  rw [abs_mul, abs_of_pos Real.pi_pos] at hs
  have hs' : 2 * |t| ≤ |Real.sin (Real.pi * t)| := by
    convert hs using 1; field_simp
  rw [← ht, circleCharacter_real, mul_comm _ Complex.I,
    Complex.norm_exp_I_mul_ofReal_sub_one]
  have heq : 2 * Real.pi * t / 2 = Real.pi * t := by ring
  rw [heq, Real.norm_eq_abs, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  rw [← ht] at hn
  nlinarith

def linearPhaseMean (N : ℕ) (a b : Frequency) : ℂ :=
  complexUniformMean (fun r : Fin N => circleCharacter (label r • a + b))

/-- An affine intercept and the shift from 0,...,N-1 to 1,...,N are unit factors. -/
theorem linearPhaseMean_geometric (N : ℕ) (a b : Frequency) :
    linearPhaseMean N a b = circleCharacter (a + b) *
      (∑ r ∈ Finset.range N, circleCharacter a ^ r) / (N : ℂ) := by
  simp only [linearPhaseMean, complexUniformMean, label, succ_nsmul,
    circleCharacter_add, circleCharacter_nsmul, Fintype.card_fin]
  rw [← Finset.sum_mul, ← Finset.sum_mul]
  rw [← Finset.sum_range]
  ring

/-- The undivided estimate remains valid even when a=0 on the circle. -/
theorem linearPhaseMean_chord_bound (N : ℕ) (a b : Frequency) :
    (N : ℝ) * ‖linearPhaseMean N a b‖ * ‖circleCharacter a - 1‖ ≤ 2 := by
  by_cases hN : N = 0
  · simp [hN]
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast hN
  rw [linearPhaseMean_geometric, norm_div, norm_mul, norm_circleCharacter,
    one_mul, Complex.norm_natCast, mul_div_cancel₀ _ hn]
  rw [← norm_mul, geom_sum_mul]
  calc
    ‖circleCharacter a ^ N - 1‖ ≤ ‖circleCharacter a ^ N‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
    _ = 2 := by norm_num [norm_pow, norm_circleCharacter]

/-- A large linear sum gives scale N⁻¹ control, uniformly in its affine intercept. -/
theorem linear_weyl_inverse {N : ℕ} (hN : 0 < N) (a b : Frequency)
    {ρ : ℝ} (hρ : 0 < ρ) (hlarge : ρ ≤ ‖linearPhaseMean N a b‖) :
    ‖a‖ ≤ 1 / (2 * ρ * (N : ℝ)) := by
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
  have hchord := circle_norm_le_chord a
  have hbound := linearPhaseMean_chord_bound N a b
  have h1 := mul_le_mul_of_nonneg_left hchord
    (mul_nonneg hNreal.le (norm_nonneg (linearPhaseMean N a b)))
  have h2 := mul_le_mul_of_nonneg_right hlarge
    (mul_nonneg hNreal.le (norm_nonneg a))
  apply (le_div_iff₀ (by positivity : 0 < 2 * ρ * (N : ℝ))).2
  nlinarith

end GMZP0
