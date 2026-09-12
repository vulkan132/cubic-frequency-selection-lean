import GMZP0.ConstantGramPhase

/-! Actual scalar Gram-entry counts imply the original degree-zero minor estimate.
The uniform count remains an explicit core premise. -/
noncomputable section
open scoped BigOperators ComplexConjugate
namespace GMZP0

def largeHorizontalEntries {N : ℕ} {U : Type*} [Fintype U]
    (K : Fin N → U → ℂ) (v : ℝ) (x : Fin N) : Finset (Fin N) := by
  classical
  exact Finset.univ.filter (fun x' => x' ≠ x ∧ v / N < ‖gramKernel K x x'‖)

/-- Count the actual large entries, with separate diagonal and small-entry budgets. -/
theorem gram_row_of_few_large_entries {N : ℕ} (hN : 0 < N) {U : Type*} [Fintype U]
    (K : Fin N → U → ℂ) (v ρ : ℝ) (hv : 0 ≤ v) (x : Fin N)
    (htrivial : ∀ x', ‖gramKernel K x x'‖ ≤ (N : ℝ)⁻¹)
    (hcount : ((largeHorizontalEntries K v x).card : ℝ) ≤ ρ * N) :
    ∑ x', ‖gramKernel K x x'‖ ≤ ρ + v + (N : ℝ)⁻¹ := by
  classical
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hp (x' : Fin N) : ‖gramKernel K x x'‖ ≤
      (if x' = x then (N : ℝ)⁻¹ else 0) +
      (if x' ∈ largeHorizontalEntries K v x then (N : ℝ)⁻¹ else 0) + v / N := by
    by_cases he : x' = x
    · subst x'
      have hn : x ∉ largeHorizontalEntries K v x := by simp [largeHorizontalEntries]
      simp only [if_true, hn, if_false, add_zero]
      exact (htrivial x).trans (le_add_of_nonneg_right (by positivity))
    · by_cases hl : x' ∈ largeHorizontalEntries K v x
      · simp only [he, if_false, hl, if_true, zero_add]
        exact (htrivial x').trans (le_add_of_nonneg_right (by positivity))
      · have hsmall : ‖gramKernel K x x'‖ ≤ v / N := by
          apply le_of_not_gt
          intro hb
          exact hl (Finset.mem_filter.mpr ⟨Finset.mem_univ _, he, hb⟩)
        simpa only [he, hl, if_false, zero_add] using hsmall
  have hc : (∑ x' : Fin N, if x' ∈ largeHorizontalEntries K v x then (N : ℝ)⁻¹ else 0) =
      ((largeHorizontalEntries K v x).card : ℝ) / N := by
    rw [← Finset.sum_filter]
    simp [div_eq_mul_inv]
  have hcard : ((largeHorizontalEntries K v x).card : ℝ) / N ≤ ρ :=
    (div_le_iff₀ hNr).2 hcount
  have hs := Finset.sum_le_sum (fun x' (_ : x' ∈ (Finset.univ : Finset (Fin N))) => hp x')
  simp only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ,
    if_true, hc, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hs
  have he : (N : ℝ) * (v / N) = v := by field_simp
  rw [he] at hs
  linarith

theorem outputMaskedKernel_gram_norm_le {Z U : Type*} [Fintype U]
    (K : Z → U → ℂ) (m : Z → ℂ) (hm : ∀ z, ‖m z‖ ≤ 1) (z w : Z) :
    ‖gramKernel (outputMaskedKernel K m) z w‖ ≤ ‖gramKernel K z w‖ := by
  rw [outputMaskedKernel_gram, norm_mul, norm_mul, Complex.norm_conj]
  calc
    _ ≤ (1 * ‖gramKernel K z w‖) * 1 :=
      mul_le_mul (mul_le_mul_of_nonneg_right (hm z) (norm_nonneg _)) (hm w)
        (norm_nonneg _) (by positivity)
    _ = _ := by ring

/-- Supported horizontal masks preserve the scalar Schur bound from actual unmasked row counts. -/
theorem masked_energy_of_few_horizontal_entries {N : ℕ} (hN : 0 < N)
    {U : Type*} [Fintype U] (K : Fin N → U → ℂ) (P : Fin N → Prop)
    (m : Fin N → ℂ) (hm : ∀ x, ‖m x‖ ≤ 1) (hsupport : ∀ x, ¬ P x → m x = 0)
    (v ρ : ℝ) (hv : 0 ≤ v) (hρ : 0 ≤ ρ)
    (htrivial : ∀ x x', ‖gramKernel K x x'‖ ≤ (N : ℝ)⁻¹)
    (hcount : ∀ x, P x → ((largeHorizontalEntries K v x).card : ℝ) ≤ ρ * N)
    (u : U → ℂ) :
    finiteEnergy (fun x => m x * kernelAction K u x) ≤
      (ρ + v + (N : ℝ)⁻¹) * finiteEnergy u := by
  have hrow (x : Fin N) : ∑ x', ‖gramKernel (outputMaskedKernel K m) x x'‖ ≤
      ρ + v + (N : ℝ)⁻¹ := by
    by_cases hx : P x
    · exact (Finset.sum_le_sum (fun x' _ => outputMaskedKernel_gram_norm_le K m hm x x')).trans
        (gram_row_of_few_large_entries hN K v ρ hv x (htrivial x) (hcount x hx))
    · simp only [outputMaskedKernel_gram, hsupport x hx, zero_mul, norm_zero, Finset.sum_const_zero]
      positivity
  simpa only [finiteEnergy, outputMaskedKernel_action] using
    kernel_action_energy_of_gram_rows (outputMaskedKernel K m) (ρ + v + (N : ℝ)⁻¹)
      (by positivity) hrow u

theorem horizontalMinorMask_bound {N : ℕ} (Q : ℕ) (φ : Fin N → Frequency) (x : Fin N) :
    ‖horizontalMinorMask Q φ x‖ ≤ 1 := by
  unfold horizontalMinorMask
  split_ifs <;> simp

/-- Actual off-diagonal Fourier Gram counts give the minor-row squared-energy estimate. -/
theorem horizontal_minor_energy_of_counts {N : ℕ} (hN : 0 < N)
    (Q : ℕ) (φ : Fin N → Frequency) (ξ : Frequency) (v ρ : ℝ) (hv : 0 ≤ v) (hρ : 0 ≤ ρ)
    (hcount : ∀ x : Fin N, ¬ MajorArc Q N (φ x) →
      ((largeHorizontalEntries (horizontalCubicKernel N φ ξ) v x).card : ℝ) ≤ ρ * N)
    (u : Fin (2 * N) → ℂ) :
    (∑ x, ‖horizontalMinorMask Q φ x * horizontalCubicResponse N φ ξ u x‖ ^ 2) ≤
      (ρ + v + (N : ℝ)⁻¹) * ∑ t, ‖u t‖ ^ 2 := by
  classical
  have hsupport (x : Fin N) (hx : ¬ ¬ MajorArc Q N (φ x)) : horizontalMinorMask Q φ x = 0 := by
    simp [horizontalMinorMask, not_not.mp hx]
  simpa only [horizontalCubicKernel_action, finiteEnergy] using
    masked_energy_of_few_horizontal_entries hN (horizontalCubicKernel N φ ξ)
      (fun x => ¬ MajorArc Q N (φ x)) (horizontalMinorMask Q φ) (horizontalMinorMask_bound Q φ)
      hsupport v ρ hv hρ (horizontalCubicKernel_gram_norm_le hN φ ξ) hcount u

/-- The scalar Fourier counts and budget imply the original complete finite minor estimate. -/
theorem constant_finiteMinorEstimate_of_counts {N : ℕ} (hN : 0 < N)
    (Q : ℕ) (s v ρ : ℝ) (hv : 0 ≤ v) (hρ : 0 ≤ ρ)
    (hbudget : ρ + v + (N : ℝ)⁻¹ ≤ s ^ 2) (φ : Fin N → Frequency)
    (hcount : ∀ (ξ : Frequency) (x : Fin N), ¬ MajorArc Q N (φ x) →
      ((largeHorizontalEntries (horizontalCubicKernel N φ ξ) v x).card : ℝ) ≤ ρ * N) :
    FiniteMinorEstimate Q N s (fun z : Base N => φ z.1) := by
  apply finiteMinorEstimate_of_horizontal
  intro ξ u
  exact (horizontal_minor_energy_of_counts hN Q φ ξ v ρ hv hρ (hcount ξ) u).trans
    (mul_le_mul_of_nonneg_right hbudget (Finset.sum_nonneg (fun _ _ => sq_nonneg _)))

/-- Numerical parameters precede N,Q,phi and all Fourier parameters in the scalar criterion. -/
theorem uniform_constant_estimate_of_counts (s : ℝ) (hs : 0 < s) :
    ∃ ρ v : ℝ, 0 < ρ ∧ 0 < v ∧ ∃ N₀ : ℕ, 0 < N₀ ∧
      ∀ N : ℕ, N₀ ≤ N → ∀ Q : ℕ, ∀ φ : Fin N → Frequency,
        (∀ (ξ : Frequency) (x : Fin N), ¬ MajorArc Q N (φ x) →
          ((largeHorizontalEntries (horizontalCubicKernel N φ ξ) v x).card : ℝ) ≤ ρ * N) →
        FiniteMinorEstimate Q N s (fun z : Base N => φ z.1) := by
  obtain ⟨ρ, v, hρ, hv, N₀, hN₀, hbudget⟩ := uniform_compressed_block_error_budget s hs
  exact ⟨ρ, v, hρ, hv, N₀, hN₀, fun N hN Q φ hc =>
    constant_finiteMinorEstimate_of_counts (hN₀.trans_le hN) Q s v ρ hv.le hρ.le (hbudget N hN) φ hc⟩

end GMZP0
