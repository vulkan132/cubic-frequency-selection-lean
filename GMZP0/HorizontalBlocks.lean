import GMZP0.DiagonalEnergy
import GMZP0.OriginalWeights

/-! Group the first Gram expansion by horizontal fibers before taking absolute values. -/

noncomputable section
open scoped BigOperators ComplexConjugate
namespace GMZP0

def horizontalKernel (N : ℕ) (p : Base N → Frequency) (x x' : Fin N)
    (y v : Fin (N ^ 2)) : ℂ := gramKernel (responseKernel N p) (x, y) (x', v)

def horizontalPairing (N : ℕ) (p : Base N → Frequency) (b : Base N → ℂ)
    (x x' : Fin N) : ℂ :=
  finitePairing (kernelAction (horizontalKernel N p x x') (fun v => b (x', v)))
    (fun y => b (x, y))

def offBlockNormSum (N : ℕ) (p : Base N → Frequency) (b : Base N → ℂ) : ℝ :=
  ∑ x : Fin N, ∑ x' : Fin N, if x' ≠ x then ‖horizontalPairing N p b x x'‖ else 0

/-- This grouping keeps each complete horizontal block intact. -/
theorem offHorizontalEnergy_blocks (N : ℕ) (p : Base N → Frequency) (b : Base N → ℂ) :
    offHorizontalEnergy N p b =
      ∑ x : Fin N, ∑ x' : Fin N, if x' ≠ x then (horizontalPairing N p b x x').re else 0 := by
  classical
  simp only [offHorizontalEnergy, Fintype.sum_prod_type, horizontalPairing,
    finitePairing, kernelAction, Finset.sum_mul, Complex.re_sum, horizontalKernel,
    gramInteraction]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x' _
  by_cases hx : x' ≠ x <;> simp [hx]

theorem offBlockNormSum_nonneg (N : ℕ) (p : Base N → Frequency) (b : Base N → ℂ) :
    0 ≤ offBlockNormSum N p b := by
  apply Finset.sum_nonneg
  intro x _
  apply Finset.sum_nonneg
  intro x' _
  exact ite_nonneg (norm_nonneg _) le_rfl

theorem offHorizontalEnergy_le_blocks (N : ℕ) (p : Base N → Frequency) (b : Base N → ℂ) :
    offHorizontalEnergy N p b ≤ offBlockNormSum N p b := by
  classical
  rw [offHorizontalEnergy_blocks]
  apply Finset.sum_le_sum
  intro x _
  apply Finset.sum_le_sum
  intro x' _
  split_ifs
  · exact Complex.re_le_norm _
  · exact le_rfl

/-- The positive part is taken only after the complete off-horizontal block pairings. -/
theorem weighted_first_tt_lower {N : ℕ} (hN : 0 < N)
    (f : ℤ × ℤ → ℂ) (hf : ∀ v, ‖f v‖ ≤ 1)
    (p : Base N → Frequency) (σ : Base N → ℝ) (lam : Base N → ℂ)
    (hσ : ∀ z, 0 ≤ σ z ∧ σ z ≤ 1) (hlam : ∀ z, ‖lam z‖ = 1) :
    max (‖weightedOriginalResponse N f p σ lam‖ ^ 2 * (N : ℝ) ^ 3 / 4 -
        (∑ z : Base N, σ z) / (N : ℝ)) 0 ≤
      offBlockNormSum N p (alignedWeightVector σ lam) := by
  exact max_le ((weighted_offHorizontal_lower hN f hf p σ lam hσ hlam).trans
    (offHorizontalEnergy_le_blocks N p _)) (offBlockNormSum_nonneg N p _)

/-- The manuscript's first TT* bound with the exact original window mass. -/
theorem original_window_first_tt {N : ℕ} (hN : 0 < N)
    (f : ℤ × ℤ → ℂ) (hf : ∀ v, ‖f v‖ ≤ 1)
    (p : Base N → Frequency) (μ : Base N → ℝ) (D : Finset (Base N))
    (lam : Base N → ℂ) (hlam : ∀ z, ‖lam z‖ = 1)
    (hμ : ∀ z, 0 ≤ μ z ∧ μ z ≤ (N : ℝ)⁻¹ ^ 3) :
    (N : ℝ) ^ 3 * max
      (‖weightedOriginalResponse N f p (originalScaledWeight N μ D) lam‖ ^ 2 / 4 -
        (∑ z ∈ D, μ z) / (N : ℝ)) 0 ≤
      offBlockNormSum N p (alignedWeightVector (originalScaledWeight N μ D) lam) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have h := weighted_first_tt_lower hN f hf p (originalScaledWeight N μ D) lam
    (originalScaledWeight_bounds hN μ D hμ) hlam
  have hmass := (div_eq_iff (pow_ne_zero 3 hNr.ne')).1 (originalScaledWeight_mass hN μ D)
  rw [mul_max_of_nonneg _ _ (pow_nonneg hNr.le 3), mul_zero]
  have heq : (N : ℝ) ^ 3 *
      (‖weightedOriginalResponse N f p (originalScaledWeight N μ D) lam‖ ^ 2 / 4 -
        (∑ z ∈ D, μ z) / (N : ℝ)) =
      ‖weightedOriginalResponse N f p (originalScaledWeight N μ D) lam‖ ^ 2 * (N : ℝ) ^ 3 / 4 -
        (∑ z : Base N, originalScaledWeight N μ D z) / (N : ℝ) := by
    rw [hmass]
    ring
  rwa [heq]

/-- First use of the second adjoint, keeping the complete horizontal input fiber. -/
theorem horizontalPairing_adjoint_bound (N : ℕ) (p : Base N → Frequency)
    (σ : Base N → ℝ) (lam : Base N → ℂ)
    (hσ : ∀ z, 0 ≤ σ z ∧ σ z ≤ 1) (hlam : ∀ z, ‖lam z‖ = 1) (x x' : Fin N) :
    ‖horizontalPairing N p (alignedWeightVector σ lam) x x'‖ ^ 2 ≤
      (N : ℝ) ^ 2 * finiteEnergy
        (kernelAdjoint (horizontalKernel N p x x') (fun y => alignedWeightVector σ lam (x, y))) := by
  have hfiber : finiteEnergy (fun v => alignedWeightVector σ lam (x', v)) ≤ (N : ℝ) ^ 2 := by
    apply (alignedWeightVector_energy_le (fun v => σ (x', v)) (fun v => lam (x', v))
      (fun v => hσ (x', v)) (fun v => hlam (x', v))).trans
    calc
      (∑ v : Fin (N ^ 2), σ (x', v)) ≤ ∑ _v : Fin (N ^ 2), (1 : ℝ) :=
        Finset.sum_le_sum fun v _ => (hσ (x', v)).2
      _ = (N : ℝ) ^ 2 := by simp
  rw [horizontalPairing, kernel_adjoint_identity]
  exact (finitePairing_norm_sq_le _ _).trans
    (mul_le_mul_of_nonneg_right hfiber (finiteEnergy_nonneg _))

end GMZP0
