import GMZP0.FewLargeBlocks
import GMZP0.BlockRowEnergy

/-! Exact original parabola blocks, arbitrary output masks, and the finite minor-arc criterion.
Only the displayed count of large compressed blocks is assumed in the final implications. -/

noncomputable section
open scoped BigOperators ComplexConjugate
namespace GMZP0

/-- Actual nonparallel collision counts give row norm sum at most 1/N. -/
theorem horizontalKernel_row_norm_sum {N : ℕ} (hN : 0 < N)
    (p : Base N → Frequency) (x x' : Fin N) (hx : x ≠ x') (y : Fin (N ^ 2)) :
    ∑ v, ‖horizontalKernel N p x x' y v‖ ≤ (N : ℝ)⁻¹ := by
  classical
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hcount : ((Finset.univ.filter (fun v : Fin (N ^ 2) =>
      ∃ r s : Fin N, endpointIndex (x, y) r = endpointIndex (x', v) s)).card : ℝ) ≤ N := by
    exact_mod_cast horizontal_collision_count x x' y
  simp only [horizontalKernel_norm p x x' hx]
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul]
  calc
    _ ≤ (N : ℝ) * (N : ℝ)⁻¹ ^ 2 := mul_le_mul_of_nonneg_right hcount (sq_nonneg _)
    _ = (N : ℝ)⁻¹ := by field_simp

/-- Conjugate symmetry transfers the original row bound to every column. -/
theorem horizontalKernel_column_norm_sum {N : ℕ} (hN : 0 < N)
    (p : Base N → Frequency) (x x' : Fin N) (hx : x ≠ x') (v : Fin (N ^ 2)) :
    ∑ y, ‖horizontalKernel N p x x' y v‖ ≤ (N : ℝ)⁻¹ := by
  have he (y : Fin (N ^ 2)) : ‖horizontalKernel N p x x' y v‖ =
      ‖horizontalKernel N p x' x v y‖ := by
    rw [horizontalKernel, horizontalKernel, ← gramKernel_conjugate, Complex.norm_conj]
  simpa only [he] using horizontalKernel_row_norm_sum hN p x' x hx.symm v

/-- Every actual horizontal Gram block has norm at most 1/N, including the diagonal. -/
theorem original_horizontal_block_bound {N : ℕ} (hN : 0 < N)
    (p : Base N → Frequency) (x x' : Fin N) :
    KernelEnergyBound (blockGramKernel (responseKernel N p) x x') (N : ℝ)⁻¹ := by
  classical
  change KernelEnergyBound (horizontalKernel N p x x') (N : ℝ)⁻¹
  by_cases hx : x = x'
  · subst x'
    have hk (y v : Fin (N ^ 2)) : horizontalKernel N p x x y v =
        if y = v then (N : ℂ)⁻¹ else 0 := by
      simpa only [horizontalKernel, Prod.mk.injEq, true_and] using
        responseKernel_gram_same_horizontal hN p (x, y) (x, v) rfl
    intro g
    have he : kernelAction (horizontalKernel N p x x) g = fun y => (N : ℂ)⁻¹ * g y := by
      funext y
      simp [kernelAction, hk]
    rw [he]
    simp only [finiteEnergy, norm_mul, norm_inv, Complex.norm_natCast, mul_pow, Finset.mul_sum]
    exact le_rfl
  · intro g
    simpa only [pow_two] using kernel_action_energy_of_rows_columns
      (horizontalKernel N p x x') (N : ℝ)⁻¹ (N : ℝ)⁻¹ (by positivity) (by positivity)
      (horizontalKernel_row_norm_sum hN p x x' hx)
      (horizontalKernel_column_norm_sum hN p x x' hx) g

/-- Arbitrary pointwise contractions preserve the complete vertical block bound. -/
theorem masked_original_horizontal_block_bound {N : ℕ} (hN : 0 < N)
    (p : Base N → Frequency) (m : Base N → ℂ) (hm : ∀ z, ‖m z‖ ≤ 1) (x x' : Fin N) :
    KernelEnergyBound (blockGramKernel (outputMaskedKernel (responseKernel N p) m) x x')
      (N : ℝ)⁻¹ :=
  blockGramKernel_mask_bound _ m hm x x' _ (original_horizontal_block_bound hN p x x')

/-- A count on the compressed blocks controls the complete original finite response. -/
theorem masked_original_energy_of_few_large_blocks {N : ℕ} (hN : 0 < N)
    (p : Base N → Frequency) (m : Base N → ℂ) (H : Finset (Fin N))
    (hm : ∀ z, ‖m z‖ ≤ 1) (hsupport : ∀ z, z.1 ∉ H → m z = 0)
    (v ρ : ℝ) (hv : 0 ≤ v) (hρ : 0 ≤ ρ)
    (hcount : ∀ x ∈ H,
      ((largeBlockNeighbors (outputMaskedKernel (responseKernel N p) m) H v x).card : ℝ) ≤ ρ * N)
    (g : InputBox N → ℂ) :
    finiteEnergy (fun z => m z * finiteResponse N p g z) ≤
      (ρ + v + (N : ℝ)⁻¹) * finiteEnergy g := by
  have hs : ∀ x, x ∉ H → ∀ y u, outputMaskedKernel (responseKernel N p) m (x, y) u = 0 := by
    intro x hx y u
    simp [outputMaskedKernel, hsupport (x, y) hx]
  have h := kernel_energy_of_few_large_blocks hN (outputMaskedKernel (responseKernel N p) m)
    H v ρ hv hρ hs (masked_original_horizontal_block_bound hN p m hm) hcount g
  simpa only [finiteEnergy, outputMaskedKernel_action, responseKernel_action] using h

/-- The same original f and every original label remain after the operator estimate. -/
theorem masked_original_response_energy {N : ℕ} (hN : 0 < N)
    (p : Base N → Frequency) (m : Base N → ℂ) (H : Finset (Fin N))
    (hm : ∀ z, ‖m z‖ ≤ 1) (hsupport : ∀ z, z.1 ∉ H → m z = 0)
    (v ρ : ℝ) (hv : 0 ≤ v) (hρ : 0 ≤ ρ)
    (hcount : ∀ x ∈ H,
      ((largeBlockNeighbors (outputMaskedKernel (responseKernel N p) m) H v x).card : ℝ) ≤ ρ * N)
    (f : ℤ × ℤ → ℂ) (hf : ∀ w, ‖f w‖ ≤ 1) :
    (∑ z : Base N, ‖m z * response N f z (p z)‖ ^ 2) ≤
      4 * (N : ℝ) ^ 3 * (ρ + v + (N : ℝ)⁻¹) := by
  have h := masked_original_energy_of_few_large_blocks hN p m H hm hsupport v ρ hv hρ hcount
    (fun u => f (inputPoint u))
  simp only [finiteEnergy, finiteResponse_original] at h
  have he := mul_le_mul_of_nonneg_left (inputEnergy_le N f hf)
    (show 0 ≤ ρ + v + (N : ℝ)⁻¹ by positivity)
  change (ρ + v + (N : ℝ)⁻¹) * (∑ u : InputBox N, ‖f (inputPoint u)‖ ^ 2) ≤ _ at he
  exact h.trans (he.trans_eq (by ring))

/-- The actual pointwise minor-arc mask, with no regularity assumption. -/
def minorOutputMask (Q N : ℕ) (p : Base N → Frequency) : Base N → ℂ := by
  classical
  exact fun z => if MajorArc Q N (p z) then 0 else 1

/-- The actual pointwise minor-arc indicator is a contraction. -/
theorem minorOutputMask_bound (Q N : ℕ) (p : Base N → Frequency) (z : Base N) :
    ‖minorOutputMask Q N p z‖ ≤ 1 := by
  unfold minorOutputMask
  split_ifs <;> norm_num

/-- Masked finite energy is exactly the existing original minor-arc energy sum. -/
theorem minorOutputMask_energy (Q N : ℕ) (p : Base N → Frequency) (g : InputBox N → ℂ) :
    finiteEnergy (fun z => minorOutputMask Q N p z * finiteResponse N p g z) =
      (by
        classical
        exact ∑ z : Base N, if MajorArc Q N (p z) then 0 else ‖finiteResponse N p g z‖ ^ 2) := by
  classical
  apply Finset.sum_congr rfl
  intro z _
  by_cases hz : MajorArc Q N (p z) <;> simp [minorOutputMask, hz]

/-- An explicit block-count criterion for the pre-existing finite minor-arc interface. -/
theorem finiteMinorEstimate_of_few_large_compressed_blocks {N : ℕ} (hN : 0 < N)
    (Q : ℕ) (p : Base N → Frequency) (v ρ : ℝ) (hv : 0 ≤ v) (hρ : 0 ≤ ρ)
    (hcount : ∀ x : Fin N,
      ((largeBlockNeighbors (outputMaskedKernel (responseKernel N p) (minorOutputMask Q N p))
        Finset.univ v x).card : ℝ) ≤ ρ * N) :
    FiniteMinorEstimate Q N (Real.sqrt (ρ + v + (N : ℝ)⁻¹)) p := by
  classical
  intro g
  have h := masked_original_energy_of_few_large_blocks hN p (minorOutputMask Q N p) Finset.univ
    (minorOutputMask_bound Q N p) (by simp) v ρ hv hρ (fun x _ => hcount x) g
  rw [minorOutputMask_energy] at h
  simpa only [Real.sq_sqrt (show 0 ≤ ρ + v + (N : ℝ)⁻¹ by positivity), finiteEnergy] using h

/-- The error parameters and size threshold are chosen before N and all original data. -/
theorem uniform_compressed_block_error_budget (s : ℝ) (hs : 0 < s) :
    ∃ ρ v : ℝ, 0 < ρ ∧ 0 < v ∧ ∃ N₀ : ℕ, 0 < N₀ ∧
      ∀ N : ℕ, N₀ ≤ N → ρ + v + (N : ℝ)⁻¹ ≤ s ^ 2 := by
  obtain ⟨B, hB⟩ := exists_nat_gt (2 / s ^ 2)
  refine ⟨s ^ 2 / 4, s ^ 2 / 4, by positivity, by positivity, B + 1, by omega, ?_⟩
  intro N hN
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hBN : (B : ℝ) ≤ N := by exact_mod_cast (show B ≤ N by omega)
  have hbig := (div_lt_iff₀ (sq_pos_of_pos hs)).mp (hB.trans_le hBN)
  have hi : (N : ℝ)⁻¹ ≤ s ^ 2 / 2 := by
    rw [inv_eq_one_div]
    apply (div_le_iff₀ hn).2
    nlinarith
  linarith

/-- A uniform target error precedes N,Q,p in the conditional compressed-block criterion. -/
theorem uniform_finiteMinorEstimate_of_compressed_counts (s : ℝ) (hs : 0 < s) :
    ∃ ρ v : ℝ, 0 < ρ ∧ 0 < v ∧ ∃ N₀ : ℕ, 0 < N₀ ∧
      ∀ N : ℕ, N₀ ≤ N → ∀ Q : ℕ, ∀ p : Base N → Frequency,
        (∀ x : Fin N,
          ((largeBlockNeighbors (outputMaskedKernel (responseKernel N p) (minorOutputMask Q N p))
            Finset.univ v x).card : ℝ) ≤ ρ * N) →
        FiniteMinorEstimate Q N s p := by
  classical
  obtain ⟨ρ, v, hρ, hv, N₀, hN₀, hbudget⟩ := uniform_compressed_block_error_budget s hs
  refine ⟨ρ, v, hρ, hv, N₀, hN₀, ?_⟩
  intro N hN Q p hcount g
  have hn : 0 < N := lt_of_lt_of_le hN₀ hN
  have h := finiteMinorEstimate_of_few_large_compressed_blocks hn Q p v ρ hv.le hρ.le hcount g
  rw [Real.sq_sqrt (show 0 ≤ ρ + v + (N : ℝ)⁻¹ by positivity)] at h
  exact h.trans (mul_le_mul_of_nonneg_right (hbudget N hN) (finiteEnergy_nonneg g))

end GMZP0
