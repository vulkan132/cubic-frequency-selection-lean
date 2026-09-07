import GMZP0.HorizontalBlocks

/-! Cauchy--Schwarz across complete horizontal blocks, before expanding the second Gram kernel. -/

noncomputable section
open scoped BigOperators ComplexConjugate
namespace GMZP0

def secondAdjointEnergy (N : ℕ) (p : Base N → Frequency) (X : Finset (Fin N)) (b : Base N → ℂ) : ℝ :=
  ∑ x : Fin N, ∑ x' : Fin N, if x ∈ X ∧ x' ∈ X ∧ x' ≠ x then
    finiteEnergy (kernelAdjoint (horizontalKernel N p x x') (fun y => b (x, y))) else 0

def restrictedBlockNormSum (N : ℕ) (p : Base N → Frequency) (X : Finset (Fin N))
    (b : Base N → ℂ) : ℝ :=
  ∑ x : Fin N, ∑ x' : Fin N, if x ∈ X ∧ x' ∈ X ∧ x' ≠ x then
    ‖horizontalPairing N p b x x'‖ else 0

theorem horizontalPairing_zero_left {N : ℕ} (p : Base N → Frequency) (b : Base N → ℂ)
    (x x' : Fin N) (hb : ∀ y, b (x, y) = 0) : horizontalPairing N p b x x' = 0 := by
  simp only [horizontalPairing, finitePairing, hb, map_zero, mul_zero, Finset.sum_const_zero]

theorem horizontalPairing_zero_right {N : ℕ} (p : Base N → Frequency) (b : Base N → ℂ)
    (x x' : Fin N) (hb : ∀ y, b (x', y) = 0) : horizontalPairing N p b x x' = 0 := by
  simp only [horizontalPairing, finitePairing, kernelAction, hb, mul_zero,
    Finset.sum_const_zero, zero_mul]

/-- Support removes outside fibers from the pairings, before the second adjoint is taken. -/
theorem offBlockNormSum_restrict {N : ℕ} (p : Base N → Frequency) (X : Finset (Fin N))
    (b : Base N → ℂ) (hb : ∀ z, z.1 ∉ X → b z = 0) :
    offBlockNormSum N p b = restrictedBlockNormSum N p X b := by
  simp only [offBlockNormSum, restrictedBlockNormSum]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro x' _
  by_cases hx : x ∈ X
  · by_cases hx' : x' ∈ X
    · simp [hx, hx']
    · rw [horizontalPairing_zero_right p b x x' (fun y => hb (x', y) hx')]
      simp [hx']
  · rw [horizontalPairing_zero_left p b x x' (fun y => hb (x, y) hx)]
    simp [hx]

theorem secondAdjointEnergy_nonneg (N : ℕ) (p : Base N → Frequency)
    (X : Finset (Fin N)) (b : Base N → ℂ) :
    0 ≤ secondAdjointEnergy N p X b := by
  apply Finset.sum_nonneg
  intro x _
  apply Finset.sum_nonneg
  intro x' _
  exact ite_nonneg (finiteEnergy_nonneg _) le_rfl

/-- There are at most N² horizontal pairs, independently of the number of base points. -/
theorem offBlockNormSum_sq_le (N : ℕ) (p : Base N → Frequency)
    (X : Finset (Fin N)) (b : Base N → ℂ) :
    restrictedBlockNormSum N p X b ^ 2 ≤ (N : ℝ) ^ 2 *
      ∑ x : Fin N, ∑ x' : Fin N, if x ∈ X ∧ x' ∈ X ∧ x' ≠ x then
        ‖horizontalPairing N p b x x'‖ ^ 2 else 0 := by
  classical
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun _ : Fin N × Fin N => (1 : ℝ))
    (fun q : Fin N × Fin N => if q.1 ∈ X ∧ q.2 ∈ X ∧ q.2 ≠ q.1 then
      ‖horizontalPairing N p b q.1 q.2‖ else 0)
  simpa only [one_mul, one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_prod,
    Fintype.card_fin, nsmul_eq_mul, mul_one, Nat.cast_mul, Fintype.sum_prod_type,
    ite_pow, zero_pow (by decide : 2 ≠ 0), restrictedBlockNormSum, pow_two] using hcs

/-- Combining the complete-fiber and horizontal-pair Cauchy--Schwarz inequalities. -/
theorem offBlockNormSum_second_adjoint (N : ℕ) (p : Base N → Frequency) (X : Finset (Fin N))
    (σ : Base N → ℝ) (lam : Base N → ℂ)
    (hσ : ∀ z, 0 ≤ σ z ∧ σ z ≤ 1) (hlam : ∀ z, ‖lam z‖ = 1)
    (hsupport : ∀ z, z.1 ∉ X → σ z = 0) :
    offBlockNormSum N p (alignedWeightVector σ lam) ^ 2 ≤
      (N : ℝ) ^ 4 * secondAdjointEnergy N p X (alignedWeightVector σ lam) := by
  have hb : ∀ z, z.1 ∉ X → alignedWeightVector σ lam z = 0 := by
    intro z hz
    simp [alignedWeightVector, hsupport z hz]
  rw [offBlockNormSum_restrict p X _ hb]
  have hsum : (∑ x : Fin N, ∑ x' : Fin N,
      if x ∈ X ∧ x' ∈ X ∧ x' ≠ x then
        ‖horizontalPairing N p (alignedWeightVector σ lam) x x'‖ ^ 2 else 0) ≤
        (N : ℝ) ^ 2 * secondAdjointEnergy N p X (alignedWeightVector σ lam) := by
    simp only [secondAdjointEnergy, Finset.mul_sum, mul_ite, mul_zero]
    apply Finset.sum_le_sum
    intro x _
    apply Finset.sum_le_sum
    intro x' _
    split_ifs
    · exact horizontalPairing_adjoint_bound N p σ lam hσ hlam x x'
    · exact le_rfl
  calc
    restrictedBlockNormSum N p X (alignedWeightVector σ lam) ^ 2 ≤ _ := offBlockNormSum_sq_le N p X _
    _ ≤ (N : ℝ) ^ 2 * ((N : ℝ) ^ 2 * secondAdjointEnergy N p X (alignedWeightVector σ lam)) :=
      mul_le_mul_of_nonneg_left hsum (sq_nonneg _)
    _ = _ := by ring

/-- The second energy lower bound retains the same R_D and exact original mass mu(D). -/
theorem original_window_second_adjoint {N : ℕ} (hN : 0 < N)
    (f : ℤ × ℤ → ℂ) (hf : ∀ v, ‖f v‖ ≤ 1)
    (p : Base N → Frequency) (μ : Base N → ℝ) (D : Finset (Base N))
    (X : Finset (Fin N)) (hD : ∀ z ∈ D, z.1 ∈ X)
    (lam : Base N → ℂ) (hlam : ∀ z, ‖lam z‖ = 1)
    (hμ : ∀ z, 0 ≤ μ z ∧ μ z ≤ (N : ℝ)⁻¹ ^ 3) :
    max (‖weightedOriginalResponse N f p (originalScaledWeight N μ D) lam‖ ^ 2 / 4 -
        (∑ z ∈ D, μ z) / (N : ℝ)) 0 ^ 2 ≤
      secondAdjointEnergy N p X (alignedWeightVector (originalScaledWeight N μ D) lam) /
        (N : ℝ) ^ 2 := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hfirst := original_window_first_tt hN f hf p μ D lam hlam hμ
  have hsupport : ∀ z : Base N, z.1 ∉ X → originalScaledWeight N μ D z = 0 := by
    intro z hz
    have hzD : z ∉ D := fun he => hz (hD z he)
    simp [originalScaledWeight, hzD]
  have hsecond := offBlockNormSum_second_adjoint N p X (originalScaledWeight N μ D) lam
    (originalScaledWeight_bounds hN μ D hμ) hlam hsupport
  have hsquare := (pow_le_pow_left₀
    (mul_nonneg (pow_nonneg hNr.le 3) (le_max_right _ _)) hfirst 2).trans hsecond
  apply (le_div_iff₀ (sq_pos_of_pos hNr)).2
  apply (mul_le_mul_iff_right₀ (pow_pos hNr 4)).1
  nlinarith only [hsquare]

end GMZP0
