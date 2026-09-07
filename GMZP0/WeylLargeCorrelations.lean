import GMZP0.WeylDifferencing

/-! Many nonzero correlations above an explicit scale threshold; small-scale obstruction. -/

noncomputable section
open scoped BigOperators
namespace GMZP0

theorem sum_le_large_card_add {I : Type*} (s : Finset I) (v : I → ℝ)
    {τ : ℝ} (hτ : 0 ≤ τ) (hv : ∀ i ∈ s, v i ≤ 1) :
    (∑ i ∈ s, v i) ≤ ((s.filter (fun i => τ ≤ v i)).card : ℝ) + (s.card : ℝ) * τ := by
  classical
  calc
    (∑ i ∈ s, v i) ≤ ∑ i ∈ s, ((if τ ≤ v i then 1 else 0) + τ) := by
      apply Finset.sum_le_sum
      intro i hi
      split_ifs with h
      · linarith [hv i hi]
      · have := le_of_lt (lt_of_not_ge h)
        linarith
    _ = _ := by simp [Finset.sum_add_distrib]

def largeWeylShifts (N : ℕ) (F : ℤ → ℂ) (τ : ℝ) : Finset ℤ :=
  (horizontalShiftLabels N).filter fun h => τ ≤ ‖weylCorrelation N F h‖

/-- Both signs are retained. The necessary threshold N*rho²>=2 is a hypothesis. -/
theorem many_large_weyl_correlations {N : ℕ} (hN : 0 < N) (F : ℤ → ℂ)
    (hF : ∀ r, ‖F r‖ ≤ 1) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hlarge : ρ ≤ ‖integerIntervalMean N F‖) (hscale : 2 ≤ (N : ℝ) * ρ ^ 2) :
    (N : ℝ) * ρ ^ 2 / 4 ≤ (largeWeylShifts N F (ρ ^ 2 / 8)).card := by
  have h1 := weyl_nonzero_correlation_lower hN F hF
  have h2 := sum_le_large_card_add (horizontalShiftLabels N)
    (fun h => ‖weylCorrelation N F h‖) (τ := ρ ^ 2 / 8) (by positivity)
    (fun h _ => weylCorrelation_norm_le hN F hF h)
  rw [horizontalShiftLabels_card, Nat.cast_mul, Nat.cast_ofNat] at h2
  have hs := pow_le_pow_left₀ hρ hlarge 2
  have h3 := mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
  change (N : ℝ) * ρ ^ 2 / 4 ≤
    (((horizontalShiftLabels N).filter (fun h => ρ ^ 2 / 8 ≤ ‖weylCorrelation N F h‖)).card : ℝ)
  nlinarith

theorem largeWeylShifts_mem {N : ℕ} {F : ℤ → ℂ} {τ : ℝ} {h : ℤ}
    (hh : h ∈ largeWeylShifts N F τ) :
    h ≠ 0 ∧ -(N : ℤ) ≤ h ∧ h ≤ N ∧ τ ≤ ‖weylCorrelation N F h‖ := by
  simpa only [largeWeylShifts, horizontalShiftLabels, Finset.mem_filter,
    Finset.mem_erase, Finset.mem_Icc, and_assoc] using hh

/-- At N=1 a full mean can have norm one while every nonzero correlation vanishes. -/
theorem weyl_small_scale_obstruction :
    ∃ F : ℤ → ℂ, (∀ r, ‖F r‖ ≤ 1) ∧ ‖integerIntervalMean 1 F‖ = 1 ∧
      ∀ h : ℤ, h ≠ 0 → weylCorrelation 1 F h = 0 := by
  refine ⟨fun _ => 1, by simp, ?_, ?_⟩
  · norm_num [integerIntervalMean]
  · intro h hh
    have hn : 1 + h ∉ Finset.Icc (1 : ℤ) 1 := by
      simp only [Finset.mem_Icc]
      omega
    norm_num [weylCorrelation, hn, hh]

end GMZP0
