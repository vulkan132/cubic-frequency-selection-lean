import GMZP0.WideGram
import GMZP0.ZeroLagBounds

/-! The phase-based large-block upper bound from complete sums, with original finite boundaries retained. -/
noncomputable section
open scoped BigOperators
namespace GMZP0

/-- The complete exponential sum on exactly I_h intersect (I_h-k). -/
def wideLagSum {N : ℕ} (P : Fin N → ℤ → Frequency) (x x' : Fin N) (y k : ℤ) : ℂ :=
  ∑ r ∈ lagLabels N (horizontalGap x x') k, circleCharacter (wideDoublePhase P x x' y k r)

/-- The zero-lag phase is identically zero before any absolute value is taken. -/
theorem wideDoublePhase_zero_lag {N : ℕ} (P : Fin N → ℤ → Frequency)
    (x x' : Fin N) (y r : ℤ) : wideDoublePhase P x x' y 0 r = 0 := by
  simp [wideDoublePhase, doublePhaseCoefficient]

/-- The complete zero-lag sum counts the original block labels exactly. -/
theorem wideLagSum_zero {N : ℕ} (P : Fin N → ℤ → Frequency)
    (x x' : Fin N) (y : ℤ) :
    wideLagSum P x x' y 0 = ((blockLabels N (horizontalGap x x')).card : ℂ) := by
  simp [wideLagSum, lagLabels_zero, wideDoublePhase_zero_lag, circleCharacter]

/-- Every complete lag sum is bounded by the number of original labels, hence by N. -/
theorem wideLagSum_norm_le {N : ℕ} (P : Fin N → ℤ → Frequency)
    (x x' : Fin N) (y k : ℤ) : ‖wideLagSum P x x' y k‖ ≤ N := by
  calc
    _ ≤ ∑ r ∈ lagLabels N (horizontalGap x x') k, ‖circleCharacter (wideDoublePhase P x x' y k r)‖ :=
      norm_sum_le _ _
    _ = ((lagLabels N (horizontalGap x x') k).card : ℝ) := by simp [norm_circleCharacter]
    _ ≤ ((blockLabels N (horizontalGap x x')).card : ℝ) := by
      exact_mod_cast Finset.card_le_card (Finset.filter_subset (fun r => r + k ∈ blockLabels N (horizontalGap x x')) _)
    _ ≤ N := by exact_mod_cast blockLabels_card_le N (horizontalGap x x')

/-- A fixed integer target coordinate is attained by at most one original vertical point. -/
theorem original_vertical_single_fiber_sum_le (N : ℕ) (c : ℤ) (a : ℝ) (ha : 0 ≤ a) :
    (∑ t : Fin (N ^ 2), if (label t : ℤ) = c then a else 0) ≤ a := by
  classical
  by_cases he : ∃ t : Fin (N ^ 2), (label t : ℤ) = c
  · obtain ⟨t, ht⟩ := he
    have hi (v : Fin (N ^ 2)) : (label v : ℤ) = c ↔ v = t := by
      rw [← ht]
      constructor
      · intro h
        apply Fin.ext
        simp only [label, Nat.cast_add, Nat.cast_one] at h
        omega
      · rintro rfl
        rfl
    simp_rw [hi]
    simp
  · have hn (t : Fin (N ^ 2)) : (label t : ℤ) ≠ c := fun ht => he ⟨t, ht⟩
    simpa only [hn, if_false, Finset.sum_const_zero] using ha

/-- The widened Gram row is bounded by complete lag sums, not arbitrary truncated inner sums. -/
theorem wideHorizontalKernel_gram_row_le {N : ℕ} (P : Fin N → ℤ → Frequency)
    (x x' : Fin N) (y : Fin (N ^ 2)) :
    (∑ t, ‖gramKernel (wideHorizontalKernel P x x') y t‖) ≤
      (∑ k ∈ Finset.Icc (-(N : ℤ)) N, ‖wideLagSum P x x' (label y) k‖) / (N : ℝ) ^ 4 := by
  have hp (t : Fin (N ^ 2)) : ‖gramKernel (wideHorizontalKernel P x x') y t‖ ≤
      (∑ k ∈ Finset.Icc (-(N : ℤ)) N,
        if (label t : ℤ) = (label y : ℤ) + 2 * horizontalGap x x' * k then
          ‖wideLagSum P x x' (label y) k‖ else 0) / (N : ℝ) ^ 4 := by
    rw [wideHorizontalKernel_gram_lags, norm_div, norm_pow, Complex.norm_natCast]
    apply div_le_div_of_nonneg_right _ (by positivity)
    simpa only [apply_ite norm, norm_zero, wideLagSum] using
      norm_sum_le (Finset.Icc (-(N : ℤ)) N) (fun k =>
        if (label t : ℤ) = (label y : ℤ) + 2 * horizontalGap x x' * k then
          wideLagSum P x x' (label y) k else 0)
  calc
    _ ≤ ∑ t : Fin (N ^ 2), (∑ k ∈ Finset.Icc (-(N : ℤ)) N,
        if (label t : ℤ) = (label y : ℤ) + 2 * horizontalGap x x' * k then
          ‖wideLagSum P x x' (label y) k‖ else 0) / (N : ℝ) ^ 4 :=
      Finset.sum_le_sum (fun t _ => hp t)
    _ = (∑ k ∈ Finset.Icc (-(N : ℤ)) N, ∑ t : Fin (N ^ 2),
        if (label t : ℤ) = (label y : ℤ) + 2 * horizontalGap x x' * k then
          ‖wideLagSum P x x' (label y) k‖ else 0) / (N : ℝ) ^ 4 := by
      simp only [div_eq_mul_inv]
      rw [← Finset.sum_mul, Finset.sum_comm]
    _ ≤ _ := div_le_div_of_nonneg_right (Finset.sum_le_sum (fun k _ =>
      original_vertical_single_fiber_sum_le N _ _ (norm_nonneg _))) (by positivity)

/-- The zero lag costs at most N; every nonzero lag retains its supplied complete-sum bound. -/
theorem wide_lag_total_bound {N : ℕ} (P : Fin N → ℤ → Frequency)
    (x x' : Fin N) (y : ℤ) (M : ℤ → ℝ)
    (hM : ∀ k ∈ Finset.Icc (-(N : ℤ)) N, k ≠ 0 → ‖wideLagSum P x x' y k‖ ≤ M k) :
    (∑ k ∈ Finset.Icc (-(N : ℤ)) N, ‖wideLagSum P x x' y k‖) ≤
      (N : ℝ) + ∑ k ∈ Finset.Icc (-(N : ℤ)) N, if k ≠ 0 then M k else 0 := by
  have hz : (0 : ℤ) ∈ Finset.Icc (-(N : ℤ)) N := by simp
  have hp (k : ℤ) (hk : k ∈ Finset.Icc (-(N : ℤ)) N) : ‖wideLagSum P x x' y k‖ ≤
      (if k = 0 then (N : ℝ) else 0) + (if k ≠ 0 then M k else 0) := by
    by_cases h : k = 0
    · subst k
      simpa using wideLagSum_norm_le P x x' y 0
    · simpa only [h, if_false, ne_eq, not_false_eq_true, if_true, zero_add] using hM k hk h
  have hs := Finset.sum_le_sum hp
  simpa only [Finset.sum_add_distrib, Finset.sum_ite_eq', hz, if_true] using hs

/-- A pointwise envelope of complete lag sums gives the paper's N^(-4) widened-block estimate. -/
theorem wide_block_energy_of_lag_bounds {N : ℕ} (P : Fin N → ℤ → Frequency)
    (x x' : Fin N) (M : ℤ → ℝ) (hM0 : ∀ k, 0 ≤ M k)
    (hM : ∀ y : Fin (N ^ 2), ∀ k ∈ Finset.Icc (-(N : ℤ)) N, k ≠ 0 →
      ‖wideLagSum P x x' (label y) k‖ ≤ M k) (g : WideVertical N → ℂ) :
    finiteEnergy (kernelAction (wideHorizontalKernel P x x') g) ≤
      (((N : ℝ) + ∑ k ∈ Finset.Icc (-(N : ℤ)) N, if k ≠ 0 then M k else 0) / (N : ℝ) ^ 4) *
        finiteEnergy g := by
  apply kernel_action_energy_of_gram_rows
  · apply div_nonneg
    · exact add_nonneg (Nat.cast_nonneg _) (Finset.sum_nonneg (fun k _ => ite_nonneg (hM0 k) le_rfl))
    · positivity
  · intro y
    exact (wideHorizontalKernel_gram_row_le P x x' y).trans
      (div_le_div_of_nonneg_right (wide_lag_total_bound P x x' (label y) M (hM y)) (by positivity))

end GMZP0
