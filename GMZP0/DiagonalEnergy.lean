import GMZP0.WeightedAdjoint

/-! Exact removal of the h=0 contribution in the first original Gram expansion. -/

noncomputable section
open scoped BigOperators ComplexConjugate
namespace GMZP0

def gramInteraction (N : ℕ) (p : Base N → Frequency) (b : Base N → ℂ)
    (z w : Base N) : ℂ := gramKernel (responseKernel N p) z w * b w * conj (b z)

/-- This is the signed off-horizontal interaction; no absolute value is inserted into it. -/
def offHorizontalEnergy (N : ℕ) (p : Base N → Frequency) (b : Base N → ℂ) : ℝ :=
  ∑ z : Base N, ∑ w : Base N,
    if w.1 ≠ z.1 then (gramInteraction N p b z w).re else 0

/-- The h=0 interaction is exactly the input vector's squared norm divided by N. -/
theorem gram_same_horizontal_energy {N : ℕ} (hN : 0 < N)
    (p : Base N → Frequency) (b : Base N → ℂ) :
    (∑ z : Base N, ∑ w : Base N,
      if w.1 = z.1 then gramInteraction N p b z w else 0) =
        ((finiteEnergy b / (N : ℝ) : ℝ) : ℂ) := by
  classical
  have hinner : ∀ z : Base N,
      (∑ w : Base N, if w.1 = z.1 then gramInteraction N p b z w else 0) =
        (b z / (N : ℂ)) * conj (b z) := by
    intro z
    rw [← responseKernel_horizontal_block hN p b z]
    simp only [gramInteraction, Finset.sum_mul, ite_mul, zero_mul]
  simp_rw [hinner]
  rw [Complex.ofReal_div, Complex.ofReal_natCast]
  simp only [finiteEnergy, Complex.ofReal_sum,
    Complex.ofReal_pow, div_eq_mul_inv, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro z _
  rw [← Complex.mul_conj']
  ring

/-- The signed off-horizontal part plus its exact diagonal recovers all adjoint energy. -/
theorem finiteAdjoint_energy_split {N : ℕ} (hN : 0 < N)
    (p : Base N → Frequency) (b : Base N → ℂ) :
    finiteEnergy (finiteAdjoint N p b) = finiteEnergy b / (N : ℝ) +
      offHorizontalEnergy N p b := by
  classical
  have htotal := congrArg Complex.re (finiteAdjoint_energy_gram N p b)
  have hdiag := congrArg Complex.re (gram_same_horizontal_energy hN p b)
  simp only [Complex.ofReal_re, Complex.re_sum] at htotal
  simp only [Complex.ofReal_re, Complex.re_sum, apply_ite, Complex.zero_re] at hdiag
  rw [← hdiag, offHorizontalEnergy, ← Finset.sum_add_distrib]
  rw [htotal]
  apply Finset.sum_congr rfl
  intro z _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro w _
  by_cases hx : w.1 = z.1 <;> simp [hx, gramInteraction]

/-- The exact first off-horizontal lower bound, still carrying the actual weight vector. -/
theorem weighted_offHorizontal_lower {N : ℕ} (hN : 0 < N)
    (f : ℤ × ℤ → ℂ) (hf : ∀ v, ‖f v‖ ≤ 1)
    (p : Base N → Frequency) (σ : Base N → ℝ) (lam : Base N → ℂ)
    (hσ : ∀ z, 0 ≤ σ z ∧ σ z ≤ 1) (hlam : ∀ z, ‖lam z‖ = 1) :
    ‖weightedOriginalResponse N f p σ lam‖ ^ 2 * (N : ℝ) ^ 3 / 4 -
        (∑ z : Base N, σ z) / (N : ℝ) ≤
      offHorizontalEnergy N p (alignedWeightVector σ lam) := by
  have hfirst := weighted_original_adjoint_lower hN f hf p σ lam
  rw [finiteAdjoint_energy_split hN] at hfirst
  have hdiag := div_le_div_of_nonneg_right (alignedWeightVector_energy_le σ lam hσ hlam)
    (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
  linarith only [hfirst, hdiag]

end GMZP0
