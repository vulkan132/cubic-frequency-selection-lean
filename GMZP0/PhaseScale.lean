import GMZP0.CubicMetric
import Mathlib.Analysis.Normed.Group.AddCircle
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-! The natural N⁻³ scale on the circle and the complete cubic-label metric. -/

noncomputable section
open scoped BigOperators
namespace GMZP0

/-- An actual real representative attaining the circle norm; no root is discarded. -/
theorem exists_nearest_frequency_lift (a : Frequency) :
    ∃ t : ℝ, (t : Frequency) = a ∧ |t| = ‖a‖ := by
  induction a using QuotientAddGroup.induction_on
  rename_i x
  refine ⟨x - (round x : ℝ), ?_, ?_⟩
  · have hz : (((round x : ℤ) : ℝ) : Frequency) = 0 := by
      apply (AddCircle.coe_eq_zero_iff (1 : ℝ)).2
      exact ⟨round x, by simp⟩
    rw [AddCircle.coe_sub, hz, sub_zero]
  · rw [UnitAddCircle.norm_eq]

theorem cubicPhase_add {N : ℕ} (a b : Frequency) (r : Fin N) :
    cubicPhase (a + b) r = cubicPhase a r * cubicPhase b r := by
  simp only [cubicPhase, nsmul_add, AddCircle.toCircle_add, Circle.coe_mul]

@[simp] theorem cubicPhase_zero {N : ℕ} (r : Fin N) : cubicPhase 0 r = 1 := by
  simp [cubicPhase]

theorem norm_cubicPhase_sub {N : ℕ} (a b : Frequency) (r : Fin N) :
    ‖cubicPhase a r - cubicPhase b r‖ = ‖cubicPhase (a - b) r - 1‖ := by
  have hchar : cubicPhase a r = cubicPhase (a - b) r * cubicPhase b r := by
    rw [← cubicPhase_add, sub_add_cancel]
  calc
    ‖cubicPhase a r - cubicPhase b r‖ =
        ‖(cubicPhase (a - b) r - 1) * cubicPhase b r‖ := by rw [hchar]; congr 1; ring
    _ = ‖cubicPhase (a - b) r - 1‖ := by rw [norm_mul, norm_cubicPhase, mul_one]

/-- The chord bound for a real cubic phase, valid for arbitrary real t. -/
theorem real_cubicPhase_chord_le {N : ℕ} (t : ℝ) (r : Fin N) :
    ‖cubicPhase (t : Frequency) r - 1‖ ≤ 2 * Real.pi * (label r : ℝ) ^ 3 * |t| := by
  rw [cubicPhase_coe_real]
  have h := Real.norm_exp_I_mul_ofReal_sub_one_le (x := 2 * Real.pi * t * (label r : ℝ) ^ 3)
  rw [mul_comm Complex.I] at h
  apply h.trans_eq
  simp only [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_pos (by norm_num : (0 : ℝ) < 2),
    abs_of_pos Real.pi_pos, abs_of_nonneg (Nat.cast_nonneg (label r) : (0 : ℝ) ≤ label r)]
  ring

/-- A circle displacement controls each original cubic label at its exact scale. -/
theorem cubicPhase_chord_le {N : ℕ} (a b : Frequency) (r : Fin N) :
    ‖cubicPhase a r - cubicPhase b r‖ ≤ 2 * Real.pi * (label r : ℝ) ^ 3 * ‖a - b‖ := by
  obtain ⟨t, ht, hnorm⟩ := exists_nearest_frequency_lift (a - b)
  rw [norm_cubicPhase_sub]
  simpa only [ht, hnorm] using real_cubicPhase_chord_le t r

/-- The manuscript's full-label bound d_(3,N)(a,b) <= 2 pi N³ ||a-b||_T. -/
theorem cubicDistance_le_circle_scale {N : ℕ} (hN : 0 < N) (a b : Frequency) :
    cubicDistance N a b ≤ 2 * Real.pi * (N : ℝ) ^ 3 * ‖a - b‖ := by
  apply cubicDistance_le_of_label_bound hN a b _ (by positivity)
  intro r
  apply (cubicPhase_chord_le a b r).trans
  have hr : (label r : ℝ) ≤ N := by exact_mod_cast Nat.succ_le_of_lt r.isLt
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg _) hr 3) (by positivity))
    (norm_nonneg _)

/-- A circle error at scale epsilon/(2 pi N³) gives the requested full-label accuracy. -/
theorem cubicDistance_le_of_scaled_circle_error {N : ℕ} (hN : 0 < N)
    (a b : Frequency) (ε : ℝ)
    (hclose : ‖a - b‖ ≤ ε / (2 * Real.pi * (N : ℝ) ^ 3)) :
    cubicDistance N a b ≤ ε := by
  have hscale : 0 < 2 * Real.pi * (N : ℝ) ^ 3 := by positivity
  apply (cubicDistance_le_circle_scale hN a b).trans
  simpa only [mul_comm] using (le_div_iff₀ hscale).mp hclose

end GMZP0
