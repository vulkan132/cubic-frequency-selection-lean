import GMZP0.DoubleBlockFormula
import GMZP0.LagReindexing
import GMZP0.OriginalFieldExtension
import GMZP0.SecondStatistic

/-! Exact lag-indexed signed statistic on the original fields. -/

noncomputable section
open scoped BigOperators ComplexConjugate
namespace GMZP0

def originalLagSummand (N : ℕ) (p : Base N → Frequency) (σ : Base N → ℝ)
    (lam : Base N → ℂ) (x x' : Fin N) (y : Fin (N ^ 2)) (k r : ℤ) : ℝ :=
  let h := horizontalGap x x'
  let z := ((x.val : ℤ) + 1, (y.val : ℤ) + 1 + 2 * h * k)
  let v := ((x'.val : ℤ) + 1, (y.val : ℤ) + 1 + 2 * h * (r + k) - h ^ 2)
  σ (x, y) * originalFieldExtension N σ 0 z *
    (lam (x, y) * conj (originalFieldExtension N lam 1 z) *
      circleCharacter (doublePhaseCoefficient (p (x, y))
        (originalFieldExtension N p 0 z) (originalFieldExtension N p 0 v) h k r)).re

theorem originalLagSummand_labels {N : ℕ} (H : ℕ) (p : Base N → Frequency)
    (σ : Base N → ℝ) (lam : Base N → ℂ) (x x' : Fin N) (y : Fin (N ^ 2))
    (hy : SafeVertical (N : ℤ) H ((y.val : ℤ) + 1)) (hh : |horizontalGap x x'| ≤ H)
    (hHN : H ≤ N) (r s : Fin N) :
    originalLagSummand N p σ lam x x' y ((label r : ℤ) - (label s : ℤ)) (label s) =
      σ (x, y) * σ (x, lagSource H y hy (horizontalGap x x') hh r s) *
        (lam (x, y) * conj (lam (x, lagSource H y hy (horizontalGap x x') hh r s)) *
          circleCharacter (doublePhaseCoefficient (p (x, y))
            (p (x, lagSource H y hy (horizontalGap x x') hh r s))
            (p (x', blockTarget H y hy (horizontalGap x x') hh hHN r))
            (horizontalGap x x') ((label r : ℤ) - (label s : ℤ)) (label s))).re := by
  have hr : (label s : ℤ) + ((label r : ℤ) - (label s : ℤ)) = (label r : ℤ) := by ring
  dsimp only [originalLagSummand]
  rw [hr, originalFieldExtension_lagSource H σ 0 x y hy _ hh r s,
    originalFieldExtension_lagSource H lam 1 x y hy _ hh r s,
    originalFieldExtension_lagSource H p 0 x y hy _ hh r s,
    originalFieldExtension_blockTarget H p 0 x' y hy _ hh hHN r]

/-- Complete equality with the integer lag sum, including the exact N^(-4) row scale. -/
theorem horizontalGram_offDiagonal_lag {N : ℕ} (H : ℕ) (p : Base N → Frequency)
    (σ : Base N → ℝ) (lam : Base N → ℂ)
    (x x' : Fin N) (hx : x ≠ x') (y : Fin (N ^ 2))
    (hy : SafeVertical (N : ℤ) H ((y.val : ℤ) + 1)) (hh : |horizontalGap x x'| ≤ H)
    (hHN : H ≤ N) :
    (∑ t : Fin (N ^ 2), if t ≠ y then
      (gramKernel (horizontalKernel N p x x') y t * alignedWeightVector σ lam (x, t) *
        conj (alignedWeightVector σ lam (x, y))).re else 0) =
      (∑ k ∈ Finset.Icc (-(N : ℤ)) N, ∑ r ∈ lagLabels N (horizontalGap x x') k,
        if k ≠ 0 then originalLagSummand N p σ lam x x' y k r else 0) / (N : ℝ) ^ 4 := by
  rw [horizontalGram_offDiagonal_original_phase H p σ lam x x' hx y hy hh hHN,
    ← distinct_label_pair_sum N (horizontalGap x x') (originalLagSummand N p σ lam x x' y)]
  simp only [div_eq_mul_inv, Finset.sum_mul, ite_mul, zero_mul]
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro s _
  split_ifs
  · rw [originalLagSummand_labels H p σ lam x x' y hy hh hHN r.val s.val]
  · rfl

def lagSignedNumerator (N : ℕ) (p : Base N → Frequency) (X : Finset (Fin N))
    (σ : Base N → ℝ) (lam : Base N → ℂ) : ℝ :=
  ∑ x : Fin N, ∑ x' : Fin N, if x ∈ X ∧ x' ∈ X ∧ x' ≠ x then
    ∑ y : Fin (N ^ 2), ∑ k ∈ Finset.Icc (-(N : ℤ)) N,
      ∑ r ∈ lagLabels N (horizontalGap x x') k,
        if k ≠ 0 then originalLagSummand N p σ lam x x' y k r else 0
    else 0

def lagSignedDoubleStatistic (N : ℕ) (p : Base N → Frequency) (X : Finset (Fin N))
    (σ : Base N → ℝ) (lam : Base N → ℂ) : ℝ := lagSignedNumerator N p X σ lam / (N : ℝ) ^ 6

/-- Safe support and horizontal diameter justify every term in the full sum reindexing. -/
theorem secondOffDiagonalEnergy_lag {N : ℕ} (H : ℕ) (p : Base N → Frequency)
    (X : Finset (Fin N)) (σ : Base N → ℝ) (lam : Base N → ℂ) (hHN : H ≤ N)
    (hX : ∀ x ∈ X, ∀ x' ∈ X, |horizontalGap x x'| ≤ H)
    (hσ : ∀ x y, σ (x, y) ≠ 0 → SafeVertical (N : ℤ) H ((y.val : ℤ) + 1)) :
    secondOffDiagonalEnergy N p X (alignedWeightVector σ lam) =
      lagSignedNumerator N p X σ lam / (N : ℝ) ^ 4 := by
  classical
  unfold secondOffDiagonalEnergy lagSignedNumerator
  simp only [div_eq_mul_inv, Finset.sum_mul, ite_mul, zero_mul]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro x' _
  split_ifs with hp
  · apply Finset.sum_congr rfl
    intro y _
    by_cases hs : σ (x, y) = 0
    · simp only [alignedWeightVector, hs, Complex.ofReal_zero, zero_mul, map_zero,
        mul_zero, Complex.zero_re, ite_self, Finset.sum_const_zero, originalLagSummand]
    · simpa only [div_eq_mul_inv, Finset.sum_mul, ite_mul, zero_mul] using
        horizontalGram_offDiagonal_lag H p σ lam x x' (Ne.symm hp.2.2) y
          (hσ x y hs) (hX x hp.1 x' hp.2.1) hHN
  · rfl

/-- The original finite statistic equals the complete lag statistic, with total normalization N^(-6). -/
theorem finiteSignedDoubleStatistic_eq_lag {N : ℕ} (H : ℕ) (p : Base N → Frequency)
    (X : Finset (Fin N)) (σ : Base N → ℝ) (lam : Base N → ℂ) (hHN : H ≤ N)
    (hX : ∀ x ∈ X, ∀ x' ∈ X, |horizontalGap x x'| ≤ H)
    (hσ : ∀ x y, σ (x, y) ≠ 0 → SafeVertical (N : ℤ) H ((y.val : ℤ) + 1)) :
    finiteSignedDoubleStatistic N p X (alignedWeightVector σ lam) =
      lagSignedDoubleStatistic N p X σ lam := by
  rw [finiteSignedDoubleStatistic, secondOffDiagonalEnergy_lag H p X σ lam hHN hX hσ,
    lagSignedDoubleStatistic, div_div]
  congr 1
  ring

end GMZP0
