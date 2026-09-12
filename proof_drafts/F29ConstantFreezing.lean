import GMZP0.HorizontalSchur

/-! Complete degree-zero and affine freezing conditional on an explicit external Weyl input.
Only this analytic input is assumed; the actual Gram counts and core arguments are proved. -/
noncomputable section
open scoped BigOperators
namespace GMZP0

/-- The two-coefficient specialization of the manuscript's external Weyl estimate.
It is stated in the project's circle/ordinary-coefficient convention, for actual
subintervals of [1,N] and with the original N normalization. It is not proved or
declared as an axiom. The conversion from an external library's theorem statement
must still be supplied if an unconditional library-backed theorem is desired. -/
def CubicTwoCoefficientWeylInput : Prop :=
  ∀ v : ℝ, 0 < v → ∃ D : ℕ, ∃ C : ℝ, ∃ N₀ : ℕ,
    0 < D ∧ 0 < C ∧ 0 < N₀ ∧
    ∀ N : ℕ, N₀ ≤ N → ∀ L U : ℤ, 1 ≤ L → U ≤ N →
    ∀ a₃ a₂ a₁ a₀ : Frequency,
      v * (N : ℝ) ≤ ‖∑ r ∈ Finset.Icc L U,
        circleCharacter (cubicCirclePolynomial a₃ a₂ a₁ a₀ r)‖ →
      ∃ q : ℕ, 0 < q ∧ q ≤ D ∧
        ‖q • a₃‖ ≤ C / (N : ℝ) ^ 3 ∧ ‖q • a₂‖ ≤ C / (N : ℝ) ^ 2

/-- The external coefficient input yields an actual current-row return from each large entry. -/
theorem uniform_constant_entry_return (hW : CubicTwoCoefficientWeylInput) (v : ℝ) (hv : 0 < v) :
    ∃ D : ℕ, ∃ C : ℝ, ∃ N₀ : ℕ, 0 < D ∧ 0 < C ∧ 0 < N₀ ∧
      ∀ N : ℕ, N₀ ≤ N → ∀ (φ : Fin N → Frequency) (ξ : Frequency) (x x' : Fin N),
      v / N < ‖gramKernel (horizontalCubicKernel N φ ξ) x x'‖ →
      ∃ q : ℕ, 0 < q ∧ q ≤ D ∧ ‖q • (horizontalGap x x' • φ x)‖ ≤ C / (N : ℝ) ^ 2 := by
  obtain ⟨D, C, N₀, hD, hC, hN₀, hw⟩ := hW v hv
  refine ⟨3 * D, 4 * C, N₀, by positivity, by positivity, hN₀, ?_⟩
  intro N hN φ ξ x x' hlarge
  have hn : 0 < N := hN₀.trans_le hN
  have hsum := (horizontalCubicKernel_large_sum hn φ ξ x x' v hlarge).le
  simp only [constantGramPhase_coefficients, blockLabels_eq_interval] at hsum
  obtain ⟨q, hq, hqD, h₃, h₂⟩ := hw N hN
    (max 1 (1 + horizontalGap x x')) (min (N : ℤ) (N + horizontalGap x x'))
    (le_max_left _ _) (min_le_left _ _) (φ x - φ x') ((3 * horizontalGap x x') • φ x')
    ((-3 * horizontalGap x x' ^ 2) • φ x' + (2 * horizontalGap x x') • ξ)
    (horizontalGap x x' ^ 3 • φ x' - horizontalGap x x' ^ 2 • ξ) hsum
  exact ⟨3 * q, by positivity, Nat.mul_le_mul_left 3 hqD,
    constant_two_coefficient_return hn (φ x) (φ x') (horizontalGap x x')
      (horizontalGap_bound x x').le q C h₃ h₂⟩

/-- Many actual off-diagonal entries force the original current-row frequency into a cubic major arc. -/
theorem uniform_constant_many_entries_majorArc (hW : CubicTwoCoefficientWeylInput)
    (v ρ : ℝ) (hv : 0 < v) (hρ : 0 < ρ) :
    ∃ Q N₀ : ℕ, 0 < Q ∧ 0 < N₀ ∧
      ∀ N : ℕ, N₀ ≤ N → ∀ (φ : Fin N → Frequency) (ξ : Frequency) (x : Fin N),
      ρ * (N : ℝ) ≤ (largeHorizontalEntries (horizontalCubicKernel N φ ξ) v x).card →
      MajorArc Q N (φ x) := by
  classical
  obtain ⟨D, C, N₁, hD, hC, hN₁, hb⟩ := uniform_constant_entry_return hW v hv
  obtain ⟨Q, E, N₂, hQ, _hE, hN₂, hr⟩ := uniform_bounded_multiplier_affine_returns ρ C hρ hC D hD
  let Q' := max Q (Nat.ceil E)
  have hQQ' : Q ≤ Q' := le_max_left _ _
  have hEQ' : E ≤ (Q' : ℝ) := (Nat.le_ceil E).trans (by exact_mod_cast le_max_right Q (Nat.ceil E))
  refine ⟨Q', max N₁ N₂, hQ.trans_le hQQ', hN₁.trans_le (le_max_left _ _), ?_⟩
  intro N hN φ ξ x hcount
  let S := largeHorizontalEntries (horizontalCubicKernel N φ ξ) v x
  let T := S.image (horizontalGap x)
  have hT : T ⊆ Finset.Icc (-(N : ℤ)) N := by
    intro h hh
    obtain ⟨x', _, rfl⟩ := Finset.mem_image.mp hh
    have hg := abs_lt.mp (horizontalGap_bound x x')
    exact Finset.mem_Icc.mpr ⟨hg.1.le, hg.2.le⟩
  have hcard : T.card = S.card := Finset.card_image_of_injective _ (horizontalGap_injective_right x)
  have hd : ρ * (N : ℝ) ≤ T.card := by rw [hcard]; exact hcount
  have hp : ∀ h ∈ T, ∃ d : ℕ, 0 < d ∧ d ≤ D ∧ ‖d • (h • φ x + 0)‖ ≤ C / (N : ℝ) ^ 2 := by
    intro h hh
    obtain ⟨x', hx', rfl⟩ := Finset.mem_image.mp hh
    have hx : x' ≠ x ∧ v / N < ‖gramKernel (horizontalCubicKernel N φ ξ) x x'‖ := by
      simpa only [S, largeHorizontalEntries, Finset.mem_filter, Finset.mem_univ, true_and] using hx'
    simpa only [add_zero] using hb N ((le_max_left _ _).trans hN) φ ξ x x' hx.2
  obtain ⟨q, hq, hqQ, he⟩ := hr 2 (by norm_num) N ((le_max_right _ _).trans hN) (φ x) 0 T hT hd hp
  refine ⟨q, hq, hqQ.trans hQQ', he.trans ?_⟩
  exact div_le_div_of_nonneg_right hEQ' (by positivity)

/-- The full horizontal core estimate, uniform in all Fourier parameters and original coefficient fields. -/
theorem uniform_horizontal_constant_freezing_of_weyl (hW : CubicTwoCoefficientWeylInput) :
    UniformHorizontalConstantFreezing := by
  intro s hs _hs1
  obtain ⟨ρ, v, hρ, hv, N₁, hN₁, hbudget⟩ := uniform_compressed_block_error_budget s hs
  obtain ⟨Q, N₂, hQ, hN₂, hmajor⟩ := uniform_constant_many_entries_majorArc hW v ρ hv hρ
  refine ⟨Q, max N₁ N₂, hQ, hN₁.trans_le (le_max_left _ _), ?_⟩
  intro N hN φ ξ u
  have hn : 0 < N := hN₁.trans_le ((le_max_left _ _).trans hN)
  have hc (x : Fin N) (hx : ¬ MajorArc Q N (φ x)) :
      ((largeHorizontalEntries (horizontalCubicKernel N φ ξ) v x).card : ℝ) ≤ ρ * N := by
    exact (lt_of_not_ge (fun h => hx (hmajor N ((le_max_right _ _).trans hN) φ ξ x h))).le
  exact (horizontal_minor_energy_of_counts hn Q φ ξ v ρ hv.le hρ.le hc u).trans
    (mul_le_mul_of_nonneg_right (hbudget N ((le_max_left _ _).trans hN))
      (Finset.sum_nonneg (fun _ _ => sq_nonneg _)))

/-- No degree-zero core estimate is assumed: only the declared external analytic input remains. -/
theorem uniform_constant_freezing_of_weyl (hW : CubicTwoCoefficientWeylInput) :
    UniformConstantFreezing :=
  uniform_constant_freezing_of_horizontal (uniform_horizontal_constant_freezing_of_weyl hW)

/-- Complete affine freezing with constructed children and counts, conditional on the external input. -/
theorem uniform_affine_freezing_of_weyl (hW : CubicTwoCoefficientWeylInput)
    (s : ℝ) (hs : 0 < s) (hs1 : s ≤ 1) :
    ∃ Q N₀ : ℕ, 0 < Q ∧ 0 < N₀ ∧
      ∀ N : ℕ, N₀ ≤ N → ∀ a b : Fin N → Frequency,
        FiniteMinorEstimate Q N s (affineOriginalProfile a b) :=
  uniform_affine_freezing_of_constant (uniform_constant_freezing_of_weyl hW) s hs hs1

end GMZP0
