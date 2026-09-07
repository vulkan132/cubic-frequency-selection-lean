import GMZP0.IntervalWeyl

/-! Actual interval length and original-N normalization when passing to complete shorter sums. -/

noncomputable section
open scoped BigOperators
namespace GMZP0

theorem interval_length_card (L U : ℤ) :
    (Finset.Icc L U).card = (U - L + 1).toNat := by
  rw [Int.card_Icc]
  congr 1
  ring

theorem interval_mean_rescale (N : ℕ) (L U : ℤ) (F : ℤ → ℂ) :
    (∑ t ∈ Finset.Icc L U, F t) / (N : ℂ) =
      (((U - L + 1).toNat : ℂ) / (N : ℂ)) *
        integerIntervalMean (U - L + 1).toNat (fun t => F (L - 1 + t)) := by
  rw [sum_Icc_as_fin, integerIntervalMean_eq_fin, complexUniformMean, Fintype.card_fin]
  by_cases hM : (U - L + 1).toNat = 0
  · have hz : (∑ r : Fin ((U - L + 1).toNat), F (L - 1 + (label r : ℤ))) = 0 := by
      apply Finset.sum_eq_zero
      intro r _
      have hr := r.isLt
      omega
    rw [hz]
    simp [hM]
  · have hm : ((U - L + 1).toNat : ℂ) ≠ 0 := by exact_mod_cast hM
    field_simp

/-- A large N-normalized sum has a long actual interval and a large complete shorter mean. -/
theorem interval_large_rescaling {N : ℕ} (hN : 0 < N) (L U : ℤ) (F : ℤ → ℂ)
    (hF : ∀ t, ‖F t‖ ≤ 1) (hMN : (U - L + 1).toNat ≤ N)
    {ρ : ℝ} (hρ : 0 < ρ)
    (hlarge : ρ ≤ ‖(∑ t ∈ Finset.Icc L U, F t) / (N : ℂ)‖) :
    0 < (U - L + 1).toNat ∧ ρ * (N : ℝ) ≤ ((U - L + 1).toNat : ℝ) ∧
      ρ ≤ ‖integerIntervalMean (U - L + 1).toNat (fun t => F (L - 1 + t))‖ := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hsum := norm_sum_bounded (Finset.Icc L U) F hF
  rw [interval_length_card] at hsum
  have hl := hlarge
  rw [norm_div, Complex.norm_natCast, le_div_iff₀ hNR] at hl
  have hlen : ρ * (N : ℝ) ≤ ((U - L + 1).toNat : ℝ) := hl.trans hsum
  have hMR : (0 : ℝ) < (U - L + 1).toNat := (mul_pos hρ hNR).trans_le hlen
  have hM : 0 < (U - L + 1).toNat := by exact_mod_cast hMR
  refine ⟨hM, hlen, ?_⟩
  rw [interval_mean_rescale, norm_mul, norm_div, Complex.norm_natCast, Complex.norm_natCast] at hlarge
  have hratio : ((U - L + 1).toNat : ℝ) / (N : ℝ) ≤ 1 := by
    apply (div_le_one hNR).2
    exact_mod_cast hMN
  have hh := mul_le_mul_of_nonneg_right hratio
    (norm_nonneg (integerIntervalMean (U - L + 1).toNat (fun t => F (L - 1 + t))))
  exact hlarge.trans (by simpa only [one_mul] using hh)

end GMZP0
