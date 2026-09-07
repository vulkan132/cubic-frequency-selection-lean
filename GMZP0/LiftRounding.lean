import GMZP0.CubeSignSymmetry
import GMZP0.CircleRoots

/-! One fixed [0,1) representative and its actual nearest grid integer. -/

noncomputable section
namespace GMZP0

def frequencyUnitRep (a : Frequency) : ℝ := (AddCircle.equivIco (1 : ℝ) 0 a).val

theorem frequencyUnitRep_bounds (a : Frequency) :
    0 ≤ frequencyUnitRep a ∧ frequencyUnitRep a < 1 := by
  simpa only [frequencyUnitRep, zero_add, Set.mem_Ico] using (AddCircle.equivIco (1 : ℝ) 0 a).property

theorem frequencyUnitRep_coe (a : Frequency) : ((frequencyUnitRep a : ℝ) : Frequency) = a :=
  AddCircle.coe_equivIco

theorem round_monotone_real : Monotone (fun t : ℝ => round t) := by
  intro s t hst
  simp only [round_eq]
  exact Int.floor_mono (by linarith)

def liftRound (M : ℕ) (a : Frequency) : ℤ := round ((M : ℝ) * frequencyUnitRep a)

theorem round_between_integers (L U : ℤ) (t : ℝ) (ht : (L : ℝ) ≤ t ∧ t ≤ (U : ℝ)) :
    L ≤ round t ∧ round t ≤ U := by
  exact ⟨by simpa only [round_intCast] using round_monotone_real ht.1,
    by simpa only [round_intCast] using round_monotone_real ht.2⟩

theorem liftRound_bounds (M : ℕ) (a : Frequency) : 0 ≤ liftRound M a ∧ liftRound M a ≤ M := by
  have hb := frequencyUnitRep_bounds a
  have h0 : (0 : ℝ) ≤ (M : ℝ) * frequencyUnitRep a := mul_nonneg (Nat.cast_nonneg _) hb.1
  have hM : (M : ℝ) * frequencyUnitRep a ≤ M := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hb.2.le (Nat.cast_nonneg M : (0 : ℝ) ≤ M)
  exact ⟨by simpa only [liftRound, round_zero] using round_monotone_real h0,
    by simpa only [liftRound, round_natCast] using round_monotone_real hM⟩

theorem liftRound_error (M : ℕ) (a : Frequency) :
    |(liftRound M a : ℝ) - (M : ℝ) * frequencyUnitRep a| ≤ 1 / 2 := by
  simpa only [liftRound, abs_sub_comm] using abs_sub_round ((M : ℝ) * frequencyUnitRep a)

theorem liftRound_div_error {M : ℕ} (hM : 0 < M) (a : Frequency) :
    |(liftRound M a : ℝ) / M - frequencyUnitRep a| ≤ 1 / (2 * (M : ℝ)) := by
  have hm : (0 : ℝ) < M := by exact_mod_cast hM
  have he : (liftRound M a : ℝ) / M - frequencyUnitRep a =
      ((liftRound M a : ℝ) - (M : ℝ) * frequencyUnitRep a) / M := by field_simp
  rw [he, abs_div, abs_of_pos hm]
  calc
    _ ≤ (1 / 2 : ℝ) / M := div_le_div_of_nonneg_right (liftRound_error M a) hm.le
    _ = _ := by ring

end GMZP0
