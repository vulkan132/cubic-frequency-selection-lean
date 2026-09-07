import GMZP0.SecondAdjoint
import GMZP0.BlockRowEnergy
import GMZP0.GramEnergy

/-! Exact second Gram statistics on the original finite box.
The subsequent identification with the manuscript's lag-indexed statistic is a separate task. -/

noncomputable section
open scoped BigOperators ComplexConjugate
namespace GMZP0

def secondDiagonalEnergy (N : ℕ) (p : Base N → Frequency) (X : Finset (Fin N)) (b : Base N → ℂ) : ℝ :=
  ∑ x : Fin N, ∑ x' : Fin N, if x ∈ X ∧ x' ∈ X ∧ x' ≠ x then
    ∑ y : Fin (N ^ 2), finiteEnergy (horizontalKernel N p x x' y) * ‖b (x, y)‖ ^ 2 else 0

def secondOffDiagonalEnergy (N : ℕ) (p : Base N → Frequency) (X : Finset (Fin N)) (b : Base N → ℂ) : ℝ :=
  ∑ x : Fin N, ∑ x' : Fin N, if x ∈ X ∧ x' ∈ X ∧ x' ≠ x then
    ∑ y : Fin (N ^ 2), ∑ t : Fin (N ^ 2), if t ≠ y then
      (gramKernel (horizontalKernel N p x x') y t * b (x, t) * conj (b (x, y))).re
        else 0 else 0

def finiteSignedDoubleStatistic (N : ℕ) (p : Base N → Frequency)
    (X : Finset (Fin N)) (b : Base N → ℂ) : ℝ := secondOffDiagonalEnergy N p X b / (N : ℝ) ^ 2

/-- The signed statistic carries sigma_z*sigma_w and lam_z*conj(lam_w), with the original field p. -/
theorem finite_signed_original_weights (N : ℕ) (p : Base N → Frequency)
    (X : Finset (Fin N)) (σ : Base N → ℝ) (lam : Base N → ℂ) :
    finiteSignedDoubleStatistic N p X (alignedWeightVector σ lam) =
      (∑ x : Fin N, ∑ x' : Fin N, if x ∈ X ∧ x' ∈ X ∧ x' ≠ x then
        ∑ y : Fin (N ^ 2), ∑ t : Fin (N ^ 2), if t ≠ y then
          σ (x, y) * σ (x, t) *
            (lam (x, y) * conj (lam (x, t)) * gramKernel (horizontalKernel N p x x') y t).re
          else 0 else 0) / (N : ℝ) ^ 2 := by
  unfold finiteSignedDoubleStatistic secondOffDiagonalEnergy
  have hterm : ∀ x x' : Fin N, ∀ y t : Fin (N ^ 2),
      (gramKernel (horizontalKernel N p x x') y t * alignedWeightVector σ lam (x, t) *
        conj (alignedWeightVector σ lam (x, y))).re =
      σ (x, y) * σ (x, t) *
        (lam (x, y) * conj (lam (x, t)) * gramKernel (horizontalKernel N p x x') y t).re := by
    intro x x' y t
    exact gram_interaction_original_weights (horizontalKernel N p x x')
      (fun y => σ (x, y)) (fun y => lam (x, y)) y t
  simp_rw [hterm]

theorem secondDiagonalEnergy_nonneg (N : ℕ) (p : Base N → Frequency)
    (X : Finset (Fin N)) (b : Base N → ℂ) :
    0 ≤ secondDiagonalEnergy N p X b := by
  apply Finset.sum_nonneg
  intro x _
  apply Finset.sum_nonneg
  intro x' _
  apply ite_nonneg _ le_rfl
  exact Finset.sum_nonneg fun y _ => mul_nonneg (finiteEnergy_nonneg _) (sq_nonneg _)

/-- The vertical diagonal is removed only after the h=0 horizontal diagonal was excluded. -/
theorem secondAdjointEnergy_split (N : ℕ) (p : Base N → Frequency)
    (X : Finset (Fin N)) (b : Base N → ℂ) :
    secondAdjointEnergy N p X b = secondDiagonalEnergy N p X b + secondOffDiagonalEnergy N p X b := by
  simp only [secondAdjointEnergy, secondDiagonalEnergy, secondOffDiagonalEnergy,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro x' _
  split_ifs
  · exact kernelAdjoint_energy_split (horizontalKernel N p x x') (fun y => b (x, y))
  · simp

/-- The second diagonal costs at most sum(sigma)/N² before normalizing the statistic. -/
theorem secondDiagonalEnergy_le {N : ℕ} (hN : 0 < N)
    (p : Base N → Frequency) (X : Finset (Fin N)) (σ : Base N → ℝ) (lam : Base N → ℂ)
    (hσ : ∀ z, 0 ≤ σ z ∧ σ z ≤ 1) (hlam : ∀ z, ‖lam z‖ = 1) :
    secondDiagonalEnergy N p X (alignedWeightVector σ lam) ≤ (∑ z : Base N, σ z) / (N : ℝ) ^ 2 := by
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hrow : ∀ x x' : Fin N,
      (if x ∈ X ∧ x' ∈ X ∧ x' ≠ x then ∑ y : Fin (N ^ 2),
        finiteEnergy (horizontalKernel N p x x' y) * ‖alignedWeightVector σ lam (x, y)‖ ^ 2 else 0) ≤
      (N : ℝ)⁻¹ ^ 3 * finiteEnergy (fun y => alignedWeightVector σ lam (x, y)) := by
    intro x x'
    by_cases hx : x ∈ X ∧ x' ∈ X ∧ x' ≠ x
    · rw [if_pos hx, finiteEnergy, Finset.mul_sum]
      apply Finset.sum_le_sum
      intro y _
      exact mul_le_mul_of_nonneg_right (horizontalKernel_row_energy_le hN p x x' hx.2.2.symm y)
        (sq_nonneg _)
    · rw [if_neg hx]
      exact mul_nonneg (pow_nonneg (inv_nonneg.mpr (Nat.cast_nonneg N)) 3) (finiteEnergy_nonneg _)
  calc
    secondDiagonalEnergy N p X (alignedWeightVector σ lam) ≤
        ∑ x : Fin N, ∑ _x' : Fin N,
          (N : ℝ)⁻¹ ^ 3 * finiteEnergy (fun y => alignedWeightVector σ lam (x, y)) :=
      Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun x' _ => hrow x x'
    _ = ((N : ℝ) * (N : ℝ)⁻¹ ^ 3) * finiteEnergy (alignedWeightVector σ lam) := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        finiteEnergy, Fintype.sum_prod_type, Finset.mul_sum, mul_assoc]
    _ = (N : ℝ)⁻¹ ^ 2 * finiteEnergy (alignedWeightVector σ lam) := by
      congr 1
      field_simp
    _ ≤ (N : ℝ)⁻¹ ^ 2 * (∑ z : Base N, σ z) :=
      mul_le_mul_of_nonneg_left (alignedWeightVector_energy_le σ lam hσ hlam) (sq_nonneg _)
    _ = (∑ z : Base N, σ z) / (N : ℝ) ^ 2 := by rw [div_eq_mul_inv, inv_pow]; ring

/-- For the actual original window, the normalized second diagonal is at most mu(D)/N. -/
theorem original_window_second_diagonal {N : ℕ} (hN : 0 < N)
    (p : Base N → Frequency) (μ : Base N → ℝ) (D : Finset (Base N))
    (X : Finset (Fin N))
    (lam : Base N → ℂ) (hlam : ∀ z, ‖lam z‖ = 1)
    (hμ : ∀ z, 0 ≤ μ z ∧ μ z ≤ (N : ℝ)⁻¹ ^ 3) :
    secondDiagonalEnergy N p X (alignedWeightVector (originalScaledWeight N μ D) lam) /
      (N : ℝ) ^ 2 ≤ (∑ z ∈ D, μ z) / (N : ℝ) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have h := div_le_div_of_nonneg_right
    (secondDiagonalEnergy_le hN p X (originalScaledWeight N μ D) lam
      (originalScaledWeight_bounds hN μ D hμ) hlam) (sq_nonneg (N : ℝ))
  have hmass := (div_eq_iff (pow_ne_zero 3 hNr.ne')).1 (originalScaledWeight_mass hN μ D)
  have heq : ((∑ z : Base N, originalScaledWeight N μ D z) / (N : ℝ) ^ 2) / (N : ℝ) ^ 2 =
      (∑ z ∈ D, μ z) / (N : ℝ) := by
    rw [hmass]
    field_simp
  rwa [heq] at h

/-- The signed lower bound on the exact finite statistic; no lag reindexing is assumed here. -/
theorem original_window_finite_signed_lower {N : ℕ} (hN : 0 < N)
    (f : ℤ × ℤ → ℂ) (hf : ∀ v, ‖f v‖ ≤ 1)
    (p : Base N → Frequency) (μ : Base N → ℝ) (D : Finset (Base N))
    (X : Finset (Fin N)) (hD : ∀ z ∈ D, z.1 ∈ X)
    (lam : Base N → ℂ) (hlam : ∀ z, ‖lam z‖ = 1)
    (hμ : ∀ z, 0 ≤ μ z ∧ μ z ≤ (N : ℝ)⁻¹ ^ 3) :
    max (‖weightedOriginalResponse N f p (originalScaledWeight N μ D) lam‖ ^ 2 / 4 -
        (∑ z ∈ D, μ z) / (N : ℝ)) 0 ^ 2 ≤
      finiteSignedDoubleStatistic N p X (alignedWeightVector (originalScaledWeight N μ D) lam) +
        (∑ z ∈ D, μ z) / (N : ℝ) := by
  have he := original_window_second_adjoint hN f hf p μ D X hD lam hlam hμ
  rw [secondAdjointEnergy_split, add_div] at he
  have hd := original_window_second_diagonal hN p μ D X lam hlam hμ
  unfold finiteSignedDoubleStatistic
  linarith only [he, hd]

end GMZP0
