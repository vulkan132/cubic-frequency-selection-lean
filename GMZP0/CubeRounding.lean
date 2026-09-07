import GMZP0.LiftChoices
import GMZP0.CubeSignCounts

/-! The same sixteen rounded values yield a bounded integer branch and bounded remainder. -/

noncomputable section
open scoped BigOperators
namespace GMZP0

theorem frequency_coe_sum {I : Type*} (s : Finset I) (f : I → ℝ) :
    ((∑ i ∈ s, f i : ℝ) : Frequency) = ∑ i ∈ s, (f i : Frequency) :=
  map_sum (QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℝ))) f s

def cubeRoundedSum (M : ℕ) (a : (Fin 4 → Bool) → Frequency) : ℤ :=
  ∑ ω, cubeSign 4 ω * liftRound M (a ω)

theorem cubeRoundedSum_abs_le (M : ℕ) (a : (Fin 4 → Bool) → Frequency) :
    |cubeRoundedSum M a| ≤ 8 * (M : ℤ) :=
  bounded_integer_cube_sum M (fun ω => liftRound M (a ω)) (fun ω => liftRound_bounds M (a ω))

theorem cubeRoundedSum_real_error {M : ℕ} (hM : 0 < M) (a : (Fin 4 → Bool) → Frequency) :
    |(cubeRoundedSum M a : ℝ) / M - ∑ ω, (cubeSign 4 ω : ℝ) * frequencyUnitRep (a ω)| ≤
      8 / (M : ℝ) := by
  have he : (cubeRoundedSum M a : ℝ) / M - ∑ ω, (cubeSign 4 ω : ℝ) * frequencyUnitRep (a ω) =
      ∑ ω, (cubeSign 4 ω : ℝ) * ((liftRound M (a ω) : ℝ) / M - frequencyUnitRep (a ω)) := by
    simp only [cubeRoundedSum, Int.cast_sum, Int.cast_mul, div_eq_mul_inv, Finset.sum_mul,
      mul_sub, Finset.sum_sub_distrib, mul_assoc]
  rw [he]
  calc
    _ ≤ ∑ ω, |(cubeSign 4 ω : ℝ) * ((liftRound M (a ω) : ℝ) / M - frequencyUnitRep (a ω))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _ω : Fin 4 → Bool, 1 / (2 * (M : ℝ)) := by
      apply Finset.sum_le_sum
      intro ω _
      have hs : |(cubeSign 4 ω : ℝ)| = 1 := by exact_mod_cast cubeSign_abs 4 ω
      rw [abs_mul, hs, one_mul]
      exact liftRound_div_error hM (a ω)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, card_booleanVertices, nsmul_eq_mul]; ring

theorem cubeUnitRep_sum_coe (a : (Fin 4 → Bool) → Frequency) :
    ((∑ ω, (cubeSign 4 ω : ℝ) * frequencyUnitRep (a ω) : ℝ) : Frequency) =
      ∑ ω, cubeSign 4 ω • a ω := by
  rw [frequency_coe_sum]
  apply Finset.sum_congr rfl
  intro ω _
  rw [← zsmul_eq_mul, AddCircle.coe_zsmul, frequencyUnitRep_coe]

theorem cubeRoundedSum_circle_norm {M : ℕ} (hM : 0 < M)
    (a : (Fin 4 → Bool) → Frequency) (ε : ℝ)
    (hnear : ‖∑ ω, cubeSign 4 ω • a ω‖ ≤ ε) :
    ‖(((cubeRoundedSum M a : ℝ) / M : ℝ) : Frequency)‖ ≤ ε + 8 / (M : ℝ) := by
  let T : ℝ := ∑ ω, (cubeSign 4 ω : ℝ) * frequencyUnitRep (a ω)
  have he : (((cubeRoundedSum M a : ℝ) / M : ℝ) : Frequency) =
      ((T : ℝ) : Frequency) + (((cubeRoundedSum M a : ℝ) / M - T : ℝ) : Frequency) := by
    rw [← AddCircle.coe_add, add_sub_cancel]
  rw [he]
  apply (norm_add_le _ _).trans
  apply add_le_add
  · simpa only [T, cubeUnitRep_sum_coe] using hnear
  · exact (QuotientAddGroup.norm_mk_le_norm).trans (cubeRoundedSum_real_error hM a)

theorem cube_rounding_branch {M : ℕ} (hM : 0 < M)
    (a : (Fin 4 → Bool) → Frequency) (ε : ℝ) (hscale : (M : ℝ) * ε ≤ 1)
    (hnear : ‖∑ ω, cubeSign 4 ω • a ω‖ ≤ ε) :
    ∃ l r : ℤ, cubeRoundedSum M a = l * (M : ℤ) + r ∧ |l| ≤ 8 ∧ |r| ≤ 9 := by
  have hm : (0 : ℝ) < M := by exact_mod_cast hM
  let S : ℤ := cubeRoundedSum M a
  let l : ℤ := round ((S : ℝ) / M)
  let r : ℤ := S - l * (M : ℤ)
  have hS : |(S : ℝ)| ≤ 8 * (M : ℝ) := by exact_mod_cast cubeRoundedSum_abs_le M a
  have ht : |(S : ℝ) / M| ≤ 8 := by
    rw [abs_div, abs_of_pos hm]
    exact (div_le_iff₀ hm).mpr hS
  have hl : |l| ≤ 8 := by
    have hb := round_between_integers (-8) 8 ((S : ℝ) / M) (by simpa using abs_le.mp ht)
    exact abs_le.mpr hb
  have hn := cubeRoundedSum_circle_norm hM a ε hnear
  rw [UnitAddCircle.norm_eq] at hn
  have hr : |(r : ℝ)| ≤ 9 := by
    have he : (r : ℝ) = ((S : ℝ) / M - (l : ℝ)) * M := by
      dsimp only [r]
      push_cast
      field_simp
    rw [he, abs_mul, abs_of_pos hm]
    have hb := mul_le_mul_of_nonneg_right hn hm.le
    have hcalc : (ε + 8 / (M : ℝ)) * M = (M : ℝ) * ε + 8 := by field_simp
    rw [hcalc] at hb
    exact hb.trans (by linarith)
  exact ⟨l, r, by dsimp [r, S]; ring, hl, by exact_mod_cast hr⟩

end GMZP0
