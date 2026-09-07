import GMZP0.FiniteAdjoint

/-! The first adjoint estimate with the original function and original aligned weights. -/

noncomputable section
open scoped BigOperators ComplexConjugate
namespace GMZP0

def finiteEnergy {Z : Type*} [Fintype Z] (a : Z → ℂ) : ℝ := ∑ z, ‖a z‖ ^ 2

theorem finiteEnergy_nonneg {Z : Type*} [Fintype Z] (a : Z → ℂ) :
    0 ≤ finiteEnergy a := Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem finitePairing_self {Z : Type*} [Fintype Z] (a : Z → ℂ) :
    finitePairing a a = (finiteEnergy a : ℂ) := by
  simp only [finitePairing, finiteEnergy, Complex.mul_conj', Complex.ofReal_sum,
    Complex.ofReal_pow]

/-- Finite complex Cauchy--Schwarz in the linear-first pairing convention. -/
theorem finitePairing_norm_sq_le {Z : Type*} [Fintype Z] (a b : Z → ℂ) :
    ‖finitePairing a b‖ ^ 2 ≤ finiteEnergy a * finiteEnergy b := by
  have hnorm : ‖finitePairing a b‖ ≤ ∑ z, ‖a z‖ * ‖b z‖ := by
    simpa only [finitePairing, norm_mul, Complex.norm_conj] using
      norm_sum_le Finset.univ (fun z => a z * conj (b z))
  exact (pow_le_pow_left₀ (norm_nonneg _) hnorm 2).trans
    (Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun z => ‖a z‖) (fun z => ‖b z‖))

def alignedWeightVector {Z : Type*} (σ : Z → ℝ) (lam : Z → ℂ) (z : Z) : ℂ :=
  (σ z : ℂ) * conj (lam z)

/-- This is exactly the normalized original response with its supplied aligned weights. -/
def weightedOriginalResponse (N : ℕ) (f : ℤ × ℤ → ℂ) (p : Base N → Frequency)
    (σ : Base N → ℝ) (lam : Base N → ℂ) : ℂ :=
  (∑ z : Base N, (σ z : ℂ) * lam z * response N f z (p z)) / (N : ℂ) ^ 3

theorem weighted_original_pairing (N : ℕ) (f : ℤ × ℤ → ℂ)
    (p : Base N → Frequency) (σ : Base N → ℝ) (lam : Base N → ℂ) :
    finitePairing (fun z => response N f z (p z)) (alignedWeightVector σ lam) =
      ∑ z : Base N, (σ z : ℂ) * lam z * response N f z (p z) := by
  simp only [finitePairing, alignedWeightVector, map_mul, Complex.conj_ofReal,
    starRingEnd_self_apply]
  apply Finset.sum_congr rfl
  intro z _
  ring

/-- No replacement function occurs in the first adjoint Cauchy--Schwarz bound. -/
theorem weighted_original_adjoint_sq_le (N : ℕ) (f : ℤ × ℤ → ℂ)
    (hf : ∀ w, ‖f w‖ ≤ 1) (p : Base N → Frequency)
    (σ : Base N → ℝ) (lam : Base N → ℂ) :
    ‖∑ z : Base N, (σ z : ℂ) * lam z * response N f z (p z)‖ ^ 2 ≤
      4 * (N : ℝ) ^ 3 * finiteEnergy (finiteAdjoint N p (alignedWeightVector σ lam)) := by
  rw [← weighted_original_pairing]
  have hresponse : (fun z => response N f z (p z)) =
      finiteResponse N p (fun u => f (inputPoint u)) := by
    funext z
    exact (finiteResponse_original N p f z).symm
  rw [hresponse, finiteResponse_adjoint_identity]
  exact (finitePairing_norm_sq_le _ _).trans
    (mul_le_mul_of_nonneg_right (inputEnergy_le N f hf) (finiteEnergy_nonneg _))

/-- The normalized lower bound has the manuscript's precise N³/4 factor. -/
theorem weighted_original_adjoint_lower {N : ℕ} (hN : 0 < N)
    (f : ℤ × ℤ → ℂ) (hf : ∀ w, ‖f w‖ ≤ 1)
    (p : Base N → Frequency) (σ : Base N → ℝ) (lam : Base N → ℂ) :
    ‖weightedOriginalResponse N f p σ lam‖ ^ 2 * (N : ℝ) ^ 3 / 4 ≤
      finiteEnergy (finiteAdjoint N p (alignedWeightVector σ lam)) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have h := weighted_original_adjoint_sq_le N f hf p σ lam
  rw [weightedOriginalResponse, norm_div, norm_pow, Complex.norm_natCast, div_pow]
  apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 4)).2
  have heq : ‖∑ z : Base N, (σ z : ℂ) * lam z * response N f z (p z)‖ ^ 2 /
      ((N : ℝ) ^ 3) ^ 2 * (N : ℝ) ^ 3 =
      ‖∑ z : Base N, (σ z : ℂ) * lam z * response N f z (p z)‖ ^ 2 / (N : ℝ) ^ 3 := by
    field_simp
  rw [heq]
  apply (div_le_iff₀ (pow_pos hNr 3)).2
  nlinarith only [h]

/-- Bounded original scaled weights bound the squared norm of b by their mass. -/
theorem alignedWeightVector_energy_le {Z : Type*} [Fintype Z]
    (σ : Z → ℝ) (lam : Z → ℂ) (hσ : ∀ z, 0 ≤ σ z ∧ σ z ≤ 1)
    (hlam : ∀ z, ‖lam z‖ = 1) : finiteEnergy (alignedWeightVector σ lam) ≤ ∑ z, σ z := by
  apply Finset.sum_le_sum
  intro z _
  simp only [alignedWeightVector, norm_mul, Complex.norm_conj, hlam, mul_one,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hσ z).1]
  nlinarith [(hσ z).1, (hσ z).2]

/-- The whole Gram interaction sum is exactly the squared adjoint norm. -/
theorem finiteAdjoint_energy_gram (N : ℕ) (p : Base N → Frequency) (b : Base N → ℂ) :
    (finiteEnergy (finiteAdjoint N p b) : ℂ) =
      ∑ z : Base N, ∑ w : Base N,
        gramKernel (responseKernel N p) z w * b w * conj (b z) := by
  rw [← finitePairing_self]
  change finitePairing (kernelAdjoint (responseKernel N p) b)
    (kernelAdjoint (responseKernel N p) b) = _
  rw [← kernel_adjoint_identity]
  simp_rw [finitePairing, kernel_comp_adjoint]
  simp only [kernelAction, Finset.sum_mul]

/-- Positivity is needed only where the original scaled weight is nonzero. -/
theorem weighted_original_response_lower {N : ℕ} (hN : 0 < N)
    (f : ℤ × ℤ → ℂ) (p : Base N → Frequency)
    (σ : Base N → ℝ) (lam : Base N → ℂ) (η : ℝ)
    (hσ : ∀ z, 0 ≤ σ z)
    (hresponse : ∀ z, σ z ≠ 0 → η ≤ (lam z * response N f z (p z)).re) :
    η * ((∑ z : Base N, σ z) / (N : ℝ) ^ 3) ≤
      ‖weightedOriginalResponse N f p σ lam‖ := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hsum : η * (∑ z : Base N, σ z) ≤
      (∑ z : Base N, (σ z : ℂ) * lam z * response N f z (p z)).re := by
    rw [Finset.mul_sum, Complex.re_sum]
    apply Finset.sum_le_sum
    intro z _
    by_cases hz : σ z = 0
    · simp [hz]
    · have hp := mul_le_mul_of_nonneg_left (hresponse z hz) (hσ z)
      rw [mul_assoc, Complex.re_ofReal_mul]
      simpa only [mul_comm] using hp
  rw [weightedOriginalResponse, norm_div, norm_pow, Complex.norm_natCast,
    ← mul_div_assoc]
  exact div_le_div_of_nonneg_right (hsum.trans (Complex.re_le_norm _)) (pow_nonneg hNr.le 3)

end GMZP0
