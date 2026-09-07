import GMZP0.LiftRounding

/-! All 57 allowed choices obey the same grid, size and circle-error bounds. -/

noncomputable section
namespace GMZP0

abbrev LiftChoice := smoothingShiftLabels 9 × smoothingShiftLabels 1

theorem card_liftChoice : Fintype.card LiftChoice = 57 := by
  simp [LiftChoice, card_smoothingShiftLabels]

def liftChoiceValue (M : ℕ) (a : Frequency) (c : LiftChoice) : ℝ :=
  ((liftRound M a : ℝ) + (c.1.val : ℝ)) / M + (c.2.val : ℝ)

theorem liftChoice_bounds (c : LiftChoice) : |(c.1.val : ℝ)| ≤ 9 ∧ |(c.2.val : ℝ)| ≤ 1 := by
  have hu := c.1.property
  have hv := c.2.property
  simp only [smoothingShiftLabels, Finset.mem_Icc] at hu hv
  constructor <;> apply abs_le.mpr <;> exact_mod_cast (by omega)

theorem liftChoiceValue_grid {M : ℕ} (hM : 0 < M) (a : Frequency) (c : LiftChoice) :
    ∃ k : ℤ, liftChoiceValue M a c = (k : ℝ) / M := by
  refine ⟨liftRound M a + c.1.val + (M : ℤ) * c.2.val, ?_⟩
  have hm : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
  unfold liftChoiceValue
  push_cast
  field_simp

theorem liftChoiceValue_abs_le {M : ℕ} (hM : 9 ≤ M) (a : Frequency) (c : LiftChoice) :
    |liftChoiceValue M a c| ≤ 3 := by
  have hm : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hm9 : (9 : ℝ) ≤ M := by exact_mod_cast hM
  have hn := liftRound_bounds M a
  have hn0 : (0 : ℝ) ≤ liftRound M a := by exact_mod_cast hn.1
  have hnM : (liftRound M a : ℝ) ≤ M := by exact_mod_cast hn.2
  have hc := liftChoice_bounds c
  unfold liftChoiceValue
  calc
    _ ≤ |(liftRound M a : ℝ) + (c.1.val : ℝ)| / M + |(c.2.val : ℝ)| := by
      simpa only [abs_div, abs_of_pos hm] using abs_add_le
        (((liftRound M a : ℝ) + (c.1.val : ℝ)) / M) (c.2.val : ℝ)
    _ ≤ ((M : ℝ) + 9) / M + 1 := by
      apply add_le_add _ hc.2
      apply div_le_div_of_nonneg_right _ hm.le
      exact (abs_add_le _ _).trans (by rw [abs_of_nonneg hn0]; linarith)
    _ ≤ 3 := by
      have hd : ((M : ℝ) + 9) / M ≤ 2 := (div_le_iff₀ hm).mpr (by linarith)
      linarith

theorem liftChoiceValue_circle_error {M : ℕ} (hM : 0 < M) (a : Frequency) (c : LiftChoice) :
    ‖((liftChoiceValue M a c : ℝ) : Frequency) - a‖ ≤ 19 / (2 * (M : ℝ)) := by
  have hm : (0 : ℝ) < M := by exact_mod_cast hM
  have hc := liftChoice_bounds c
  have he : ((liftChoiceValue M a c : ℝ) : Frequency) - a =
      ((((liftRound M a : ℝ) / M - frequencyUnitRep a) + (c.1.val : ℝ) / M : ℝ) : Frequency) := by
    unfold liftChoiceValue
    rw [AddCircle.coe_add, integer_cast_frequency, add_zero]
    conv_lhs => rhs; rw [← frequencyUnitRep_coe a]
    rw [← AddCircle.coe_sub]
    congr 1
    ring
  rw [he]
  calc
    _ ≤ |((liftRound M a : ℝ) / M - frequencyUnitRep a) + (c.1.val : ℝ) / M| :=
      QuotientAddGroup.norm_mk_le_norm
    _ ≤ |(liftRound M a : ℝ) / M - frequencyUnitRep a| + |(c.1.val : ℝ) / M| := abs_add_le _ _
    _ ≤ 1 / (2 * (M : ℝ)) + 9 / M := by
      apply add_le_add (liftRound_div_error hM a)
      rw [abs_div, abs_of_pos hm]
      exact div_le_div_of_nonneg_right hc.1 hm.le
    _ = _ := by ring

end GMZP0
