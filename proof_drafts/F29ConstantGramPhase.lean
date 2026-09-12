import GMZP0.HorizontalCubicKernel

/-! Exact coefficients of the genuine horizontal Gram phase, with its full interval and scale. -/
noncomputable section
open scoped BigOperators ComplexConjugate
namespace GMZP0

def constantGramPhase (a b ξ : Frequency) (h r : ℤ) : Frequency :=
  r ^ 3 • a - (r - h) ^ 3 • b + (2 * h * r - h ^ 2) • ξ

theorem horizontalFourierPhase_product (a b ξ : Frequency) (h r : ℤ) :
    horizontalFourierPhase a ξ r * conj (horizontalFourierPhase b ξ (r - h)) =
      circleCharacter (constantGramPhase a b ξ h r) := by
  rw [horizontalFourierPhase, horizontalFourierPhase, ← circleCharacter_sub]
  congr 1
  unfold constantGramPhase
  module

/-- The quadratic coefficient is 3*h*b, even when the cubic difference a-b vanishes. -/
theorem constantGramPhase_coefficients (a b ξ : Frequency) (h r : ℤ) :
    constantGramPhase a b ξ h r =
      cubicCirclePolynomial (a - b) ((3 * h) • b)
        ((-3 * h ^ 2) • b + (2 * h) • ξ) (h ^ 3 • b - h ^ 2 • ξ) r := by
  unfold constantGramPhase cubicCirclePolynomial
  module

/-- The finite Gram entry is exactly the complete original I_h exponential sum. -/
theorem horizontalCubicKernel_gram_integer (N : ℕ) (φ : Fin N → Frequency) (ξ : Frequency)
    (x x' : Fin N) :
    gramKernel (horizontalCubicKernel N φ ξ) x x' =
      (∑ r ∈ blockLabels N (horizontalGap x x'),
        circleCharacter (constantGramPhase (φ x) (φ x') ξ (horizontalGap x x') r)) / (N : ℂ) ^ 2 := by
  rw [horizontalCubicKernel_gram_labels]
  simp only [horizontalFourierPhase_product]
  have he := Equiv.sum_comp (blockLabelEquiv N (horizontalGap x x')).symm
    (fun r : blockFinLabels N (horizontalGap x x') =>
      circleCharacter (constantGramPhase (φ x) (φ x') ξ (horizontalGap x x') (label r.val)))
  simp only [blockLabelEquiv_symm_value] at he
  rw [← he]
  congr 1
  exact Finset.sum_coe_sort (blockLabels N (horizontalGap x x'))
    (fun r : ℤ => circleCharacter (constantGramPhase (φ x) (φ x') ξ (horizontalGap x x') r))

/-- The actual overlap is one integer interval, whose endpoints are not normalized away. -/
theorem blockLabels_eq_interval (N : ℕ) (h : ℤ) :
    blockLabels N h = Finset.Icc (max 1 (1 + h)) (min (N : ℤ) (N + h)) := by
  ext r
  simp only [mem_blockLabels_iff, Finset.mem_Icc, max_le_iff, le_min_iff]
  omega

/-- Every full horizontal Gram entry is at most 1/N, for all Fourier parameters. -/
theorem horizontalCubicKernel_gram_norm_le {N : ℕ} (hN : 0 < N)
    (φ : Fin N → Frequency) (ξ : Frequency) (x x' : Fin N) :
    ‖gramKernel (horizontalCubicKernel N φ ξ) x x'‖ ≤ (N : ℝ)⁻¹ := by
  rw [horizontalCubicKernel_gram_integer, norm_div, norm_pow, Complex.norm_natCast]
  have hs : ‖∑ r ∈ blockLabels N (horizontalGap x x'),
      circleCharacter (constantGramPhase (φ x) (φ x') ξ (horizontalGap x x') r)‖ ≤ N := by
    calc
      _ ≤ ∑ r ∈ blockLabels N (horizontalGap x x'),
          ‖circleCharacter (constantGramPhase (φ x) (φ x') ξ (horizontalGap x x') r)‖ := norm_sum_le _ _
      _ = ((blockLabels N (horizontalGap x x')).card : ℝ) := by
        simp only [circleCharacter, Circle.norm_coe, Finset.sum_const, nsmul_eq_mul, mul_one]
      _ ≤ N := by exact_mod_cast blockLabels_card_le N (horizontalGap x x')
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  calc
    _ ≤ (N : ℝ) / (N : ℝ) ^ 2 := div_le_div_of_nonneg_right hs (sq_nonneg _)
    _ = _ := by field_simp

/-- A large actual Gram entry gives a large original-N-normalized complete phase sum. -/
theorem horizontalCubicKernel_large_sum {N : ℕ} (hN : 0 < N)
    (φ : Fin N → Frequency) (ξ : Frequency) (x x' : Fin N) (v : ℝ)
    (hlarge : v / N < ‖gramKernel (horizontalCubicKernel N φ ξ) x x'‖) :
    v * (N : ℝ) < ‖∑ r ∈ blockLabels N (horizontalGap x x'),
      circleCharacter (constantGramPhase (φ x) (φ x') ξ (horizontalGap x x') r)‖ := by
  rw [horizontalCubicKernel_gram_integer, norm_div, norm_pow, Complex.norm_natCast] at hlarge
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have h := (lt_div_iff₀ (sq_pos_of_pos hNr)).mp hlarge
  have he : (v / N) * (N : ℝ) ^ 2 = v * N := by field_simp
  rwa [he] at h

/-- The current-row return requires both coefficients and retains the common multiplier. -/
theorem constant_two_coefficient_return {N : ℕ} (hN : 0 < N) (a b : Frequency)
    (h : ℤ) (hh : |h| ≤ N) (q : ℕ) (C : ℝ)
    (ha : ‖q • (a - b)‖ ≤ C / (N : ℝ) ^ 3)
    (hb : ‖q • ((3 * h) • b)‖ ≤ C / (N : ℝ) ^ 2) :
    ‖(3 * q) • (h • a)‖ ≤ (4 * C) / (N : ℝ) ^ 2 := by
  have hid : (3 * q) • (h • a) =
      (3 * h) • (q • (a - b)) + q • ((3 * h) • b) := by module
  rw [hid]
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hhR : |(h : ℝ)| ≤ N := by exact_mod_cast hh
  have hmult : ‖(3 * h) • (q • (a - b))‖ ≤ 3 * (N : ℝ) * (C / (N : ℝ) ^ 3) := by
    calc
      _ ≤ |((3 * h : ℤ) : ℝ)| * ‖q • (a - b)‖ := norm_zsmul_le ..
      _ ≤ (3 * (N : ℝ)) * (C / (N : ℝ) ^ 3) := by
        apply mul_le_mul _ ha (norm_nonneg _) (by positivity)
        simpa only [Int.cast_mul, Int.cast_ofNat, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 3)]
          using mul_le_mul_of_nonneg_left hhR (by norm_num : (0 : ℝ) ≤ 3)
  calc
    _ ≤ ‖(3 * h) • (q • (a - b))‖ + ‖q • ((3 * h) • b)‖ := norm_add_le _ _
    _ ≤ 3 * (N : ℝ) * (C / (N : ℝ) ^ 3) + C / (N : ℝ) ^ 2 := add_le_add hmult hb
    _ = _ := by field_simp; ring

/-- Zero cubic difference alone does not force a small current-row frequency. -/
theorem constant_leading_coefficient_obstruction :
    ∃ a b : Frequency, a - b = 0 ∧ ‖a‖ = (1 / 4 : ℝ) := by
  obtain ⟨a, b, _, _, ha⟩ := affine_direction_branch_obstruction
  exact ⟨a, a, sub_self a, ha⟩

end GMZP0
