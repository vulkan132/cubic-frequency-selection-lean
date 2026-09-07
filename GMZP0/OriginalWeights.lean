import GMZP0.WeightedAdjoint

/-! Restricting and rescaling the actual original weight, without replacing its response. -/

noncomputable section
open scoped BigOperators ComplexConjugate
namespace GMZP0

def originalScaledWeight (N : ℕ) (μ : Base N → ℝ) (D : Finset (Base N))
    (z : Base N) : ℝ := if z ∈ D then (N : ℝ) ^ 3 * μ z else 0

theorem originalScaledWeight_bounds {N : ℕ} (hN : 0 < N)
    (μ : Base N → ℝ) (D : Finset (Base N))
    (hμ : ∀ z, 0 ≤ μ z ∧ μ z ≤ (N : ℝ)⁻¹ ^ 3) :
    ∀ z, 0 ≤ originalScaledWeight N μ D z ∧ originalScaledWeight N μ D z ≤ 1 := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  intro z
  by_cases hz : z ∈ D
  · rw [originalScaledWeight, if_pos hz]
    refine ⟨mul_nonneg (pow_nonneg hNr.le 3) (hμ z).1, ?_⟩
    have hup := mul_le_mul_of_nonneg_left (hμ z).2 (pow_nonneg hNr.le 3)
    have heq : (N : ℝ) ^ 3 * (N : ℝ)⁻¹ ^ 3 = 1 := by field_simp
    rwa [heq] at hup
  · simp [originalScaledWeight, hz]

theorem originalScaledWeight_mass {N : ℕ} (hN : 0 < N)
    (μ : Base N → ℝ) (D : Finset (Base N)) :
    (∑ z : Base N, originalScaledWeight N μ D z) / (N : ℝ) ^ 3 = ∑ z ∈ D, μ z := by
  classical
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hs : (∑ z : Base N, originalScaledWeight N μ D z) =
      (N : ℝ) ^ 3 * ∑ z ∈ D, μ z := by
    simp [originalScaledWeight, Finset.mul_sum]
  rw [hs]
  field_simp

theorem originalScaledWeight_support {N : ℕ} (μ : Base N → ℝ)
    (D : Finset (Base N)) (z : Base N) (hz : originalScaledWeight N μ D z ≠ 0) :
    z ∈ D ∧ μ z ≠ 0 := by
  by_cases hD : z ∈ D
  · refine ⟨hD, ?_⟩
    intro hzero
    exact hz (by simp [originalScaledWeight, hzero])
  · exact False.elim (hz (by simp [originalScaledWeight, hD]))

/-- Retaining D keeps the original pointwise aligned response on the entire retained support. -/
theorem originalScaledWeight_response {N : ℕ} (μ : Base N → ℝ) (D : Finset (Base N))
    (f : ℤ × ℤ → ℂ) (p : Base N → Frequency) (lam : Base N → ℂ) (η : ℝ)
    (hresponse : ∀ z, μ z ≠ 0 → η ≤ (lam z * response N f z (p z)).re) :
    ∀ z, originalScaledWeight N μ D z ≠ 0 →
      η ≤ (lam z * response N f z (p z)).re := by
  intro z hz
  exact hresponse z (originalScaledWeight_support μ D z hz).2

/-- The normalized response lower bound uses exactly the mass of the original weight on D. -/
theorem original_window_response_lower {N : ℕ} (hN : 0 < N)
    (μ : Base N → ℝ) (D : Finset (Base N))
    (hμ : ∀ z, 0 ≤ μ z ∧ μ z ≤ (N : ℝ)⁻¹ ^ 3)
    (f : ℤ × ℤ → ℂ) (p : Base N → Frequency) (lam : Base N → ℂ) (η : ℝ)
    (hresponse : ∀ z, μ z ≠ 0 → η ≤ (lam z * response N f z (p z)).re) :
    η * (∑ z ∈ D, μ z) ≤
      ‖weightedOriginalResponse N f p (originalScaledWeight N μ D) lam‖ := by
  have h := weighted_original_response_lower hN f p (originalScaledWeight N μ D) lam η
    (fun z => (originalScaledWeight_bounds hN μ D hμ z).1)
    (originalScaledWeight_response μ D f p lam η hresponse)
  rwa [originalScaledWeight_mass hN] at h

end GMZP0
