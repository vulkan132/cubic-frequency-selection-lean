import GMZP0.CubicWeyl
import Mathlib.Data.Nat.Factorial.Basic

/-! A single positive denominator is chosen before the scale and every polynomial coefficient. -/

noncomputable section
namespace GMZP0

theorem uniform_cubic_common_denominator (ρ : ℝ) (hρ : 0 < ρ) :
    ∃ D : ℕ, ∃ E : ℝ, 0 < D ∧ 0 < E ∧
      ∀ N : ℕ, 0 < N → ∀ a₃ a₂ a₁ a₀ : Frequency,
        ρ ≤ ‖integerIntervalMean N (fun t => circleCharacter (cubicCirclePolynomial a₃ a₂ a₁ a₀ t))‖ →
        ‖D • a₃‖ ≤ E / (N : ℝ) ^ 3 := by
  obtain ⟨Q, E, _, hE, hw⟩ := uniform_cubic_weyl ρ hρ
  have hD : (0 : ℝ) < Q.factorial := by exact_mod_cast Nat.factorial_pos Q
  refine ⟨Q.factorial, (Q.factorial : ℝ) * E, Nat.factorial_pos Q, by positivity, ?_⟩
  intro N hN a₃ a₂ a₁ a₀ hlarge
  obtain ⟨q, hq, hqQ, hb⟩ := hw N hN a₃ a₂ a₁ a₀ hlarge
  have hdvd : q ∣ Q.factorial := Nat.dvd_factorial hq hqQ
  have heq : Q.factorial • a₃ = (Q.factorial / q) • (q • a₃) := by
    rw [← mul_nsmul, Nat.mul_div_cancel' hdvd]
  have hm : ((Q.factorial / q : ℕ) : ℝ) ≤ (Q.factorial : ℝ) := by
    exact_mod_cast Nat.div_le_self Q.factorial q
  rw [heq]
  calc
    ‖(Q.factorial / q) • (q • a₃)‖ ≤ ((Q.factorial / q : ℕ) : ℝ) * ‖q • a₃‖ := norm_nsmul_le
    _ ≤ ((Q.factorial / q : ℕ) : ℝ) * (E / (N : ℝ) ^ 3) :=
      mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg _)
    _ ≤ (Q.factorial : ℝ) * (E / (N : ℝ) ^ 3) :=
      mul_le_mul_of_nonneg_right hm (by positivity)
    _ = _ := by ring

end GMZP0
