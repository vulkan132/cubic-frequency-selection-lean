import GMZP0.OrdinaryPolynomialAlgebra

/-! Genuine full-integer ordinary polynomial profiles, exact original responses and phase coefficients. -/
noncomputable section
open scoped BigOperators
open Polynomial
namespace GMZP0

def ordinaryVerticalProfile {N : ℕ} (P : Fin N → ℝ[X]) (x : Fin N) (y : ℤ) : Frequency :=
  (((P x).eval (y : ℝ) : ℝ) : Frequency)

def ordinaryOriginalProfile {N : ℕ} (P : Fin N → ℝ[X]) (z : Base N) : Frequency :=
  ordinaryVerticalProfile P z.1 (label z.2)

/-- The full polynomial agrees on every original point, without choosing an arbitrary extension. -/
theorem ordinary_profile_agreement {N : ℕ} (P : Fin N → ℝ[X]) :
    WideProfileAgreement N (ordinaryVerticalProfile P) (ordinaryOriginalProfile P) := by
  intro x y
  rfl

/-- The polynomial profile uses the same input function and complete original response. -/
theorem ordinary_profile_original_response {N : ℕ} (P : Fin N → ℝ[X])
    (f : ℤ × ℤ → ℂ) (z : Base N) :
    finiteResponse N (ordinaryOriginalProfile P) (fun u => f (inputPoint u)) z =
      response N f z ((((P z.1).eval ((label z.2 : ℕ) : ℝ)) : ℝ) : Frequency) := by
  simpa only [ordinaryOriginalProfile, ordinaryVerticalProfile, Int.cast_natCast] using
    finiteResponse_original N (ordinaryOriginalProfile P) f z

/-- Exact equality of the actual full circle phase and the real polynomial evaluation. -/
theorem ordinary_wideDoublePhase {N : ℕ} (P : Fin N → ℝ[X])
    (x x' : Fin N) (y k r : ℤ) :
    wideDoublePhase (ordinaryVerticalProfile P) x x' y k r =
      (((ordinaryDoublePhasePolynomial (P x) (P x') (y : ℝ) (horizontalGap x x' : ℝ) (k : ℝ)).eval
        (r : ℝ) : ℝ) : Frequency) := by
  rw [ordinaryDoublePhasePolynomial_eval]
  simp only [wideDoublePhase, doublePhaseCoefficient, ordinaryVerticalProfile,
    ← AddCircle.coe_zsmul, ← AddCircle.coe_sub, zsmul_eq_mul,
    Int.cast_add, Int.cast_mul, Int.cast_sub, Int.cast_pow, Int.cast_ofNat]

/-- The actual complete lag sum is the corresponding ordinary polynomial exponential sum. -/
theorem ordinary_wideLagSum {N : ℕ} (P : Fin N → ℝ[X]) (x x' : Fin N) (y k : ℤ) :
    wideLagSum (ordinaryVerticalProfile P) x x' y k =
      ∑ r ∈ lagLabels N (horizontalGap x x') k,
        circleCharacter ((((ordinaryDoublePhasePolynomial (P x) (P x') (y : ℝ)
          (horizontalGap x x' : ℝ) (k : ℝ)).eval (r : ℝ)) : ℝ) : Frequency) := by
  simp only [wideLagSum, ordinary_wideDoublePhase]

/-- All original roots have the same degree-(D+2) circle coefficient. -/
theorem ordinary_wide_top_coefficient {N : ℕ} (P : Fin N → ℝ[X]) (D : ℕ) (hD : 2 ≤ D)
    (hP : ∀ x, (P x).natDegree ≤ D) (x x' : Fin N) (y k : ℤ) :
    (((ordinaryDoublePhasePolynomial (P x) (P x') (y : ℝ) (horizontalGap x x' : ℝ)
      (k : ℝ)).coeff (D + 2) : ℝ) : Frequency) =
      (-3 * k * (2 * horizontalGap x x') ^ D) • ((P x').coeff D : Frequency) := by
  rw [ordinaryDoublePhasePolynomial_top_coeff (P x) (P x') D hD (hP x')]
  rw [← AddCircle.coe_zsmul, zsmul_eq_mul]
  simp only [Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_ofNat]

/-- Reversing the actual pair reads the current original row's coefficient and retains the sign. -/
theorem ordinary_wide_top_coefficient_reverse {N : ℕ} (P : Fin N → ℝ[X]) (D : ℕ) (hD : 2 ≤ D)
    (hP : ∀ x, (P x).natDegree ≤ D) (x x' : Fin N) (y k : ℤ) :
    (((ordinaryDoublePhasePolynomial (P x') (P x) (y : ℝ) (horizontalGap x' x : ℝ)
      (k : ℝ)).coeff (D + 2) : ℝ) : Frequency) =
      (-3 * k * (-2 * horizontalGap x x') ^ D) • ((P x).coeff D : Frequency) := by
  rw [ordinary_wide_top_coefficient P D hD hP x' x y k]
  have he : 2 * horizontalGap x' x = -2 * horizontalGap x x' := by
    unfold horizontalGap
    ring
  rw [he]

def UniformOrdinaryFreezing (D : ℕ) : Prop :=
  ∀ s : ℝ, 0 < s → s ≤ 1 → ∃ Q N₀ : ℕ, 0 < Q ∧ 0 < N₀ ∧
    ∀ N : ℕ, N₀ ≤ N → ∀ P : Fin N → ℝ[X], (∀ x, (P x).natDegree ≤ D) →
      FiniteMinorEstimate Q N s (ordinaryOriginalProfile P)

theorem ordinary_profile_degree_zero {N : ℕ} (P : Fin N → ℝ[X])
    (hP : ∀ x, (P x).natDegree ≤ 0) :
    ordinaryOriginalProfile P = fun z : Base N => ((P z.1).coeff 0 : Frequency) := by
  funext z
  simp only [ordinaryOriginalProfile, ordinaryVerticalProfile, ordinary_eval_degree_zero (P z.1) (hP z.1)]

/-- Real degree-one polynomials agree with the already checked circle affine profiles everywhere. -/
theorem ordinary_profile_degree_one {N : ℕ} (P : Fin N → ℝ[X])
    (hP : ∀ x, (P x).natDegree ≤ 1) :
    ordinaryOriginalProfile P = affineOriginalProfile
      (fun x => ((P x).coeff 1 : Frequency)) (fun x => ((P x).coeff 0 : Frequency)) := by
  funext z
  rw [ordinaryOriginalProfile, ordinaryVerticalProfile, affineOriginalProfile,
    affineVerticalProfile_real_eval]
  rw [ordinary_eval_degree_one (P z.1) (hP z.1)]

/-- The exact ordinary degree-zero induction base follows from the explicit external input. -/
theorem uniform_ordinary_freezing_zero (hW : CubicTwoCoefficientWeylInput) :
    UniformOrdinaryFreezing 0 := by
  intro s hs hs1
  obtain ⟨Q, N₀, hQ, hN₀, hf⟩ := uniform_constant_freezing_of_weyl hW s hs hs1
  refine ⟨Q, N₀, hQ, hN₀, ?_⟩
  intro N hN P hP
  rw [ordinary_profile_degree_zero P hP]
  exact hf N hN (fun x => ((P x).coeff 0 : Frequency))

/-- The ordinary degree-one induction base has no remaining core premise besides the external input. -/
theorem uniform_ordinary_freezing_one (hW : CubicTwoCoefficientWeylInput) :
    UniformOrdinaryFreezing 1 := by
  intro s hs hs1
  obtain ⟨Q, N₀, hQ, hN₀, hf⟩ := uniform_affine_freezing_of_weyl hW s hs hs1
  refine ⟨Q, N₀, hQ, hN₀, ?_⟩
  intro N hN P hP
  rw [ordinary_profile_degree_one P hP]
  exact hf N hN (fun x => ((P x).coeff 1 : Frequency)) (fun x => ((P x).coeff 0 : Frequency))

end GMZP0
