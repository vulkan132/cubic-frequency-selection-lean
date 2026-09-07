import GMZP0.LagStatistic

/-! Reinsert the actual nonnegative k=0 contribution before rerooting and averaging. -/

noncomputable section
open scoped BigOperators ComplexConjugate
namespace GMZP0

theorem originalLagSummand_zero_lag (N : ℕ) (p : Base N → Frequency) (σ : Base N → ℝ)
    (lam : Base N → ℂ) (x x' : Fin N) (y : Fin (N ^ 2)) (r : ℤ) :
    originalLagSummand N p σ lam x x' y 0 r = σ (x, y) ^ 2 * ‖lam (x, y)‖ ^ 2 := by
  have hσ := originalFieldExtension_base N σ 0 (x, y)
  have hl := originalFieldExtension_base N lam 1 (x, y)
  have hp := originalFieldExtension_base N p 0 (x, y)
  have hz : circleCharacter (0 : Frequency) = 1 := by simp [circleCharacter]
  dsimp only [basePoint] at hσ hl hp
  dsimp only [originalLagSummand]
  simp only [mul_zero, add_zero, hσ, hl, hp, doublePhaseCoefficient,
    sub_self, zero_zsmul, hz, mul_one, Complex.mul_conj',
    ← Complex.ofReal_pow, Complex.ofReal_re]
  ring

theorem originalLagSummand_zero_nonneg (N : ℕ) (p : Base N → Frequency) (σ : Base N → ℝ)
    (lam : Base N → ℂ) (x x' : Fin N) (y : Fin (N ^ 2)) (r : ℤ) :
    0 ≤ originalLagSummand N p σ lam x x' y 0 r := by
  rw [originalLagSummand_zero_lag]
  exact mul_nonneg (sq_nonneg _) (sq_nonneg _)

theorem lag_sum_split_zero (N : ℕ) (h : ℤ) (F : ℤ → ℤ → ℝ) :
    (∑ k ∈ Finset.Icc (-(N : ℤ)) N, ∑ r ∈ lagLabels N h k, F k r) =
      (∑ k ∈ Finset.Icc (-(N : ℤ)) N, ∑ r ∈ lagLabels N h k,
        if k ≠ 0 then F k r else 0) + ∑ r ∈ lagLabels N h 0, F 0 r := by
  classical
  have ht : ∀ k : ℤ, (∑ r ∈ lagLabels N h k, F k r) =
      (∑ r ∈ lagLabels N h k, if k ≠ 0 then F k r else 0) +
        (if k = 0 then ∑ r ∈ lagLabels N h 0, F 0 r else 0) := by
    intro k
    by_cases hk : k = 0
    · subst k
      simp
    · simp [hk]
  conv_lhs => arg 2; ext k; rw [ht k]
  rw [Finset.sum_add_distrib]
  simp

def zeroLagNumerator (N : ℕ) (p : Base N → Frequency) (X : Finset (Fin N))
    (σ : Base N → ℝ) (lam : Base N → ℂ) : ℝ :=
  ∑ x : Fin N, ∑ x' : Fin N, if x ∈ X ∧ x' ∈ X ∧ x' ≠ x then
    ∑ y : Fin (N ^ 2), ∑ r ∈ lagLabels N (horizontalGap x x') 0,
      originalLagSummand N p σ lam x x' y 0 r else 0

def fullLagNumerator (N : ℕ) (p : Base N → Frequency) (X : Finset (Fin N))
    (σ : Base N → ℝ) (lam : Base N → ℂ) : ℝ :=
  ∑ x : Fin N, ∑ x' : Fin N, if x ∈ X ∧ x' ∈ X ∧ x' ≠ x then
    ∑ y : Fin (N ^ 2), ∑ k ∈ Finset.Icc (-(N : ℤ)) N,
      ∑ r ∈ lagLabels N (horizontalGap x x') k,
        originalLagSummand N p σ lam x x' y k r else 0

def lagDiagonalStatistic (N : ℕ) (p : Base N → Frequency) (X : Finset (Fin N))
    (σ : Base N → ℝ) (lam : Base N → ℂ) : ℝ := zeroLagNumerator N p X σ lam / (N : ℝ) ^ 6

def fullLagStatistic (N : ℕ) (p : Base N → Frequency) (X : Finset (Fin N))
    (σ : Base N → ℝ) (lam : Base N → ℂ) : ℝ := fullLagNumerator N p X σ lam / (N : ℝ) ^ 6

theorem fullLagNumerator_split (N : ℕ) (p : Base N → Frequency) (X : Finset (Fin N))
    (σ : Base N → ℝ) (lam : Base N → ℂ) :
    fullLagNumerator N p X σ lam = lagSignedNumerator N p X σ lam + zeroLagNumerator N p X σ lam := by
  unfold fullLagNumerator lagSignedNumerator zeroLagNumerator
  simp only [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro x' _
  split_ifs
  · rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro y _
    exact lag_sum_split_zero N (horizontalGap x x') (originalLagSummand N p σ lam x x' y)
  · simp only [add_zero]

theorem fullLagStatistic_split (N : ℕ) (p : Base N → Frequency) (X : Finset (Fin N))
    (σ : Base N → ℝ) (lam : Base N → ℂ) :
    fullLagStatistic N p X σ lam = lagSignedDoubleStatistic N p X σ lam + lagDiagonalStatistic N p X σ lam := by
  rw [fullLagStatistic, fullLagNumerator_split, add_div]
  rfl

theorem lagDiagonalStatistic_nonneg (N : ℕ) (p : Base N → Frequency) (X : Finset (Fin N))
    (σ : Base N → ℝ) (lam : Base N → ℂ) : 0 ≤ lagDiagonalStatistic N p X σ lam := by
  apply div_nonneg _ (pow_nonneg (Nat.cast_nonneg _) 6)
  apply Finset.sum_nonneg
  intro x _
  apply Finset.sum_nonneg
  intro x' _
  apply ite_nonneg _ le_rfl
  exact Finset.sum_nonneg fun y _ => Finset.sum_nonneg fun r _ =>
    originalLagSummand_zero_nonneg N p σ lam x x' y r

theorem lagSigned_le_full (N : ℕ) (p : Base N → Frequency) (X : Finset (Fin N))
    (σ : Base N → ℝ) (lam : Base N → ℂ) :
    lagSignedDoubleStatistic N p X σ lam ≤ fullLagStatistic N p X σ lam := by
  rw [fullLagStatistic_split]
  exact le_add_of_nonneg_right (lagDiagonalStatistic_nonneg N p X σ lam)

end GMZP0
