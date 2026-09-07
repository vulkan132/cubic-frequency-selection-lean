import GMZP0.LinearWeyl
import GMZP0.CircleRoots

/-! Complete finite character averages, including the exact non-aliasing condition. -/

noncomputable section
open scoped BigOperators
namespace GMZP0

theorem circleCharacter_eq_one_iff (a : Frequency) : circleCharacter a = 1 ↔ a = 0 := by
  constructor
  · intro h
    have hc := circle_norm_le_chord a
    rw [h, sub_self, norm_zero] at hc
    exact norm_eq_zero.mp (by linarith [norm_nonneg a])
  · rintro rfl
    simp [circleCharacter]

def completeCharacterMean (B : ℕ) (a : Frequency) : ℂ :=
  complexUniformMean (fun j : Fin B => circleCharacter (j.val • a))

theorem completeCharacterMean_torsion {B : ℕ} (hB : 0 < B) (a : Frequency) (ha : B • a = 0) :
    completeCharacterMean B a = if a = 0 then 1 else 0 := by
  let : Nonempty (Fin B) := ⟨⟨0, hB⟩⟩
  by_cases hz : a = 0
  · simp [completeCharacterMean, hz, circleCharacter, complexUniformMean_const]
  · rw [if_neg hz]
    have hc : circleCharacter a - 1 ≠ 0 := by
      intro he
      exact hz ((circleCharacter_eq_one_iff a).mp (sub_eq_zero.mp he))
    have hp : circleCharacter a ^ B = 1 := by
      rw [← circleCharacter_nsmul, ha]
      simp [circleCharacter]
    have hs := geom_sum_mul (circleCharacter a) B
    rw [hp, sub_self] at hs
    have hzero : (∑ j ∈ Finset.range B, circleCharacter a ^ j) = 0 :=
      (mul_eq_zero.mp hs).resolve_right hc
    unfold completeCharacterMean complexUniformMean
    simp only [circleCharacter_nsmul, Fintype.card_fin]
    rw [← Finset.sum_range, hzero, zero_div]

theorem short_rational_frequency_zero_iff {B : ℕ} (hB : 0 < B) (k : ℤ) (hk : |k| < (B : ℤ)) :
    (((k : ℝ) / B : ℝ) : Frequency) = 0 ↔ k = 0 := by
  constructor
  · intro he
    obtain ⟨l, hl⟩ := (AddCircle.coe_eq_zero_iff (1 : ℝ)).mp he
    simp only [zsmul_eq_mul, mul_one] at hl
    have hb : (0 : ℝ) < B := by exact_mod_cast hB
    have hkr : |(k : ℝ)| < B := by exact_mod_cast hk
    have hlt : |(l : ℝ)| < 1 := by
      rw [hl, abs_div, abs_of_pos hb]
      exact (div_lt_iff₀ hb).mpr (by simpa using hkr)
    have hlz : |l| < 1 := by exact_mod_cast hlt
    have hl0 : l = 0 := by have hb := abs_lt.mp hlz; omega
    rw [hl0, Int.cast_zero] at hl
    have hk0 : (k : ℝ) = 0 := (div_eq_zero_iff.mp hl.symm).resolve_right hb.ne'
    exact_mod_cast hk0
  · rintro rfl
    simp

theorem rational_character_orthogonality {B : ℕ} (hB : 0 < B) (k : ℤ) (hk : |k| < (B : ℤ)) :
    complexUniformMean (fun j : Fin B =>
      circleCharacter ((((j.val : ℝ) * (k : ℝ) / B : ℝ)) : Frequency)) =
        if k = 0 then 1 else 0 := by
  have hb : (B : ℝ) ≠ 0 := by exact_mod_cast hB.ne'
  let a : Frequency := (((k : ℝ) / B : ℝ) : Frequency)
  have ht : B • a = 0 := by
    change B • (((k : ℝ) / B : ℝ) : Frequency) = 0
    rw [← AddCircle.coe_nsmul, nsmul_eq_mul]
    have he : (B : ℝ) * ((k : ℝ) / B) = k := by field_simp
    rw [he, integer_cast_frequency]
  have he (j : Fin B) : ((((j.val : ℝ) * (k : ℝ) / B : ℝ)) : Frequency) = j.val • a := by
    change _ = j.val • (((k : ℝ) / B : ℝ) : Frequency)
    rw [← AddCircle.coe_nsmul, nsmul_eq_mul]
    congr 1
    ring
  simp only [he]
  change completeCharacterMean B a = _
  rw [completeCharacterMean_torsion hB a ht]
  simp only [a, short_rational_frequency_zero_iff hB k hk]

end GMZP0
