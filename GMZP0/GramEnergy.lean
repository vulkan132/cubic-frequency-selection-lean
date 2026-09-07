import GMZP0.WeightedAdjoint

/-! Generic finite Gram energy and its exact diagonal/off-diagonal split. -/

noncomputable section
open scoped BigOperators ComplexConjugate
namespace GMZP0

theorem kernelAdjoint_energy_gram {Z U : Type*} [Fintype Z] [Fintype U]
    (K : Z → U → ℂ) (b : Z → ℂ) :
    (finiteEnergy (kernelAdjoint K b) : ℂ) =
      ∑ z, ∑ w, gramKernel K z w * b w * conj (b z) := by
  rw [← finitePairing_self, ← kernel_adjoint_identity]
  simp_rw [finitePairing, kernel_comp_adjoint]
  simp only [kernelAction, Finset.sum_mul]

theorem gram_diagonal_interaction {Z U : Type*} [Fintype U]
    (K : Z → U → ℂ) (b : Z → ℂ) (z : Z) :
    (gramKernel K z z * b z * conj (b z)).re = finiteEnergy (K z) * ‖b z‖ ^ 2 := by
  have hdiag : gramKernel K z z = (finiteEnergy (K z) : ℂ) := finitePairing_self (K z)
  rw [hdiag, mul_assoc, Complex.mul_conj']
  simp only [← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.ofReal_re]

/-- The two original scaled weights and the original alignment phases are retained exactly. -/
theorem gram_interaction_original_weights {Z U : Type*} [Fintype U]
    (K : Z → U → ℂ) (σ : Z → ℝ) (lam : Z → ℂ) (z w : Z) :
    (gramKernel K z w * alignedWeightVector σ lam w * conj (alignedWeightVector σ lam z)).re =
      σ z * σ w * (lam z * conj (lam w) * gramKernel K z w).re := by
  have heq : gramKernel K z w * alignedWeightVector σ lam w * conj (alignedWeightVector σ lam z) =
      ((σ z * σ w : ℝ) : ℂ) * (lam z * conj (lam w) * gramKernel K z w) := by
    simp only [alignedWeightVector, map_mul, Complex.conj_ofReal,
      starRingEnd_self_apply, Complex.ofReal_mul]
    ring
  rw [heq, Complex.re_ofReal_mul]

/-- A zero input pairing cannot justify dropping its nonzero adjoint energy. -/
theorem zero_pairing_nonzero_adjoint :
    ∃ K : Unit → Unit → ℂ, ∃ g b : Unit → ℂ,
      (∀ u, g u = 0) ∧ finitePairing (kernelAction K g) b = 0 ∧
        finiteEnergy (kernelAdjoint K b) = 1 := by
  refine ⟨fun _ _ => 1, fun _ => 0, fun _ => 1, fun _ => rfl, ?_, ?_⟩
  · simp [finitePairing, kernelAction]
  · simp [finiteEnergy, kernelAdjoint]

/-- Both components are exact, even when the signed off-diagonal term is negative. -/
theorem kernelAdjoint_energy_split {Z U : Type*} [Fintype Z] [Fintype U] [DecidableEq Z]
    (K : Z → U → ℂ) (b : Z → ℂ) :
    finiteEnergy (kernelAdjoint K b) =
      (∑ z, finiteEnergy (K z) * ‖b z‖ ^ 2) +
        ∑ z, ∑ w, if w ≠ z then (gramKernel K z w * b w * conj (b z)).re else 0 := by
  have htotal := congrArg Complex.re (kernelAdjoint_energy_gram K b)
  simp only [Complex.ofReal_re, Complex.re_sum] at htotal
  rw [htotal, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro z _
  rw [← gram_diagonal_interaction K b z]
  have hterm : ∀ w, (gramKernel K z w * b w * conj (b z)).re =
      (if w = z then (gramKernel K z z * b z * conj (b z)).re else 0) +
      (if w ≠ z then (gramKernel K z w * b w * conj (b z)).re else 0) := by
    intro w
    by_cases hw : w = z <;> simp [hw]
  conv_lhs => arg 2; ext w; rw [hterm w]
  rw [Finset.sum_add_distrib]
  simp only [Fintype.sum_ite_eq']

end GMZP0
