import GMZP0.OriginalBlockSchur

/-! The direction and size condition of parent-child minor-arc transfer are explicit. -/
noncomputable section
namespace GMZP0

/-- Nearby control cannot be omitted when transferring a child's major-arc witness. -/
theorem majorArc_transfer_without_closeness_obstruction :
    ∃ a b : Frequency, MajorArc 1 4 b ∧ ¬ MajorArc 2 4 a := by
  have hnq : ‖((1 / 4 : ℝ) : Frequency)‖ = (1 / 4 : ℝ) := by
    have h := (AddCircle.norm_coe_eq_abs_iff (p := (1 : ℝ)) (x := (1 / 4 : ℝ)) (by norm_num)).2 (by norm_num)
    simpa using h
  have hnh : ‖((1 / 2 : ℝ) : Frequency)‖ = (1 / 2 : ℝ) := by
    have h := (AddCircle.norm_coe_eq_abs_iff (p := (1 : ℝ)) (x := (1 / 2 : ℝ)) (by norm_num)).2 (by norm_num)
    simpa using h
  have hd : (2 : ℕ) • ((1 / 4 : ℝ) : Frequency) = ((1 / 2 : ℝ) : Frequency) := by
    rw [← AddCircle.coe_nsmul]
    congr 1
    norm_num
  refine ⟨((1 / 4 : ℝ) : Frequency), 0, ⟨1, le_rfl, le_rfl, by norm_num⟩, ?_⟩
  rintro ⟨q, hq, hq2, hn⟩
  have hc : q = 1 ∨ q = 2 := by omega
  rcases hc with rfl | rfl
  · norm_num [hnq] at hn
  · norm_num [hd, hnh] at hn

/-- A sufficiently accurate child major-arc witness is also a parent major-arc witness. -/
theorem majorArc_nearby_transfer {N : ℕ} (hN : 0 < N) (Q Q' : ℕ)
    (hQ : 2 * Q' ≤ Q) (a b : Frequency)
    (hclose : ‖a - b‖ ≤ 1 / (N : ℝ) ^ 3) (hb : MajorArc Q' N b) : MajorArc Q N a := by
  obtain ⟨q, hq, hqQ', hqb⟩ := hb
  refine ⟨q, hq, by omega, ?_⟩
  have hqR : (q : ℝ) ≤ Q' := by exact_mod_cast hqQ'
  have hQR : 2 * (Q' : ℝ) ≤ Q := by exact_mod_cast hQ
  have hden : 0 ≤ (N : ℝ) ^ 3 := by positivity
  calc
    ‖q • a‖ = ‖q • (a - b) + q • b‖ := by rw [← nsmul_add, sub_add_cancel]
    _ ≤ ‖q • (a - b)‖ + ‖q • b‖ := norm_add_le _ _
    _ ≤ (q : ℝ) * ‖a - b‖ + (Q' : ℝ) / (N : ℝ) ^ 3 := add_le_add norm_nsmul_le hqb
    _ ≤ (q : ℝ) * (1 / (N : ℝ) ^ 3) + (Q' : ℝ) / (N : ℝ) ^ 3 := by
      gcongr
    _ ≤ (Q' : ℝ) * (1 / (N : ℝ) ^ 3) + (Q' : ℝ) / (N : ℝ) ^ 3 := by
      gcongr
    _ = (2 * (Q' : ℝ)) / (N : ℝ) ^ 3 := by ring
    _ ≤ (Q : ℝ) / (N : ℝ) ^ 3 := div_le_div_of_nonneg_right hQR hden

/-- The usable direction is parent minor implies chosen nearby child minor. -/
theorem minorArc_nearby_transfer {N : ℕ} (hN : 0 < N) (Q Q' : ℕ)
    (hQ : 2 * Q' ≤ Q) (a b : Frequency)
    (hclose : ‖a - b‖ ≤ 1 / (N : ℝ) ^ 3) (ha : ¬ MajorArc Q N a) :
    ¬ MajorArc Q' N b := fun hb => ha (majorArc_nearby_transfer hN Q Q' hQ a b hclose hb)

/-- The manuscript restricts s to at most one, which also secures major-arc transfer. -/
theorem freezing_circle_error_le_unit_scale {N : ℕ} (hN : 0 < N)
    (s : ℝ) (hs : s ≤ 1) :
    (s / 12) / (2 * Real.pi * (N : ℝ) ^ 3) ≤ 1 / (N : ℝ) ^ 3 := by
  have hn : (0 : ℝ) < (N : ℝ) ^ 3 := by positivity
  have hp : (s / 12) / (2 * Real.pi) ≤ 1 := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * Real.pi)).2
    linarith [Real.two_le_pi]
  simpa only [div_div, mul_assoc] using div_le_div_of_nonneg_right hp hn.le

/-- The paper's a0=s/(12*pi) circle error is exactly the scale used by the operator proof. -/
theorem freezing_manuscript_circle_scale (N : ℕ) (s : ℝ) :
    (s / (12 * Real.pi)) / (2 * (N : ℝ) ^ 3) =
      (s / 12) / (2 * Real.pi * (N : ℝ) ^ 3) := by
  simp only [div_div]
  congr 1
  ring

end GMZP0
