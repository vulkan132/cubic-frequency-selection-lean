import GMZP0.ZeroLag

/-! Direct original-weight bound on the reinserted lag diagonal. -/

noncomputable section
open scoped BigOperators
namespace GMZP0

theorem lagLabels_zero (N : ℕ) (h : ℤ) : lagLabels N h 0 = blockLabels N h := by
  ext r
  simp [lagLabels]

theorem blockLabels_card_le (N : ℕ) (h : ℤ) : (blockLabels N h).card ≤ N := by
  calc
    (blockLabels N h).card = (blockFinLabels N h).card := by
      simpa only [Fintype.card_coe] using (Fintype.card_congr (blockLabelEquiv N h)).symm
    _ ≤ N := by simpa only [Fintype.card_fin] using Finset.card_le_univ (blockFinLabels N h)

theorem zero_lag_row_le (N : ℕ) (p : Base N → Frequency) (σ : Base N → ℝ)
    (lam : Base N → ℂ) (x x' : Fin N) (y : Fin (N ^ 2))
    (hσ : 0 ≤ σ (x, y) ∧ σ (x, y) ≤ 1) (hlam : ‖lam (x, y)‖ = 1) :
    (∑ r ∈ lagLabels N (horizontalGap x x') 0, originalLagSummand N p σ lam x x' y 0 r) ≤
      (N : ℝ) * σ (x, y) := by
  simp only [lagLabels_zero, originalLagSummand_zero_lag, hlam, one_pow, mul_one,
    Finset.sum_const, nsmul_eq_mul]
  have hc : ((blockLabels N (horizontalGap x x')).card : ℝ) ≤ N := by
    exact_mod_cast blockLabels_card_le N (horizontalGap x x')
  calc
    ((blockLabels N (horizontalGap x x')).card : ℝ) * σ (x, y) ^ 2 ≤
        (N : ℝ) * σ (x, y) ^ 2 := mul_le_mul_of_nonneg_right hc (sq_nonneg _)
    _ ≤ (N : ℝ) * σ (x, y) := mul_le_mul_of_nonneg_left
      (by nlinarith only [hσ.1, hσ.2]) (Nat.cast_nonneg _)

theorem zeroLagNumerator_le (N : ℕ) (p : Base N → Frequency) (X : Finset (Fin N))
    (σ : Base N → ℝ) (lam : Base N → ℂ)
    (hσ : ∀ z, 0 ≤ σ z ∧ σ z ≤ 1) (hlam : ∀ z, ‖lam z‖ = 1) :
    zeroLagNumerator N p X σ lam ≤ (N : ℝ) ^ 2 * ∑ z : Base N, σ z := by
  calc
    zeroLagNumerator N p X σ lam ≤
        ∑ x : Fin N, ∑ _x' : Fin N, ∑ y : Fin (N ^ 2), (N : ℝ) * σ (x, y) := by
      apply Finset.sum_le_sum
      intro x _
      apply Finset.sum_le_sum
      intro x' _
      split_ifs
      · exact Finset.sum_le_sum fun y _ => zero_lag_row_le N p σ lam x x' y (hσ _) (hlam _)
      · exact Finset.sum_nonneg fun y _ => mul_nonneg (Nat.cast_nonneg _) (hσ _).1
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        Fintype.sum_prod_type, Finset.mul_sum, pow_two, mul_assoc]

theorem lagDiagonalStatistic_le {N : ℕ} (hN : 0 < N) (p : Base N → Frequency)
    (X : Finset (Fin N)) (σ : Base N → ℝ) (lam : Base N → ℂ)
    (hσ : ∀ z, 0 ≤ σ z ∧ σ z ≤ 1) (hlam : ∀ z, ‖lam z‖ = 1) :
    lagDiagonalStatistic N p X σ lam ≤ (∑ z : Base N, σ z) / (N : ℝ) ^ 4 := by
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  calc
    lagDiagonalStatistic N p X σ lam ≤
        ((N : ℝ) ^ 2 * ∑ z : Base N, σ z) / (N : ℝ) ^ 6 :=
      div_le_div_of_nonneg_right (zeroLagNumerator_le N p X σ lam hσ hlam) (pow_nonneg (Nat.cast_nonneg _) 6)
    _ = _ := by field_simp

/-- The actual k=0 sum costs at most mu(D)/N and is distinct from the excluded h=0 error. -/
theorem original_window_lag_diagonal_le {N : ℕ} (hN : 0 < N) (p : Base N → Frequency)
    (X : Finset (Fin N)) (μ : Base N → ℝ) (D : Finset (Base N)) (lam : Base N → ℂ)
    (hμ : ∀ z, 0 ≤ μ z ∧ μ z ≤ (N : ℝ)⁻¹ ^ 3) (hlam : ∀ z, ‖lam z‖ = 1) :
    lagDiagonalStatistic N p X (originalScaledWeight N μ D) lam ≤
      (∑ z ∈ D, μ z) / (N : ℝ) := by
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hm := (div_eq_iff (pow_ne_zero 3 hNr)).1 (originalScaledWeight_mass hN μ D)
  calc
    lagDiagonalStatistic N p X (originalScaledWeight N μ D) lam ≤
        (∑ z : Base N, originalScaledWeight N μ D z) / (N : ℝ) ^ 4 :=
      lagDiagonalStatistic_le hN p X (originalScaledWeight N μ D) lam
        (originalScaledWeight_bounds hN μ D hμ) hlam
    _ = _ := by rw [hm]; field_simp

end GMZP0
