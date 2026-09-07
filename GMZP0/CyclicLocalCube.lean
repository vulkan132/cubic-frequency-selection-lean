import GMZP0.LocalCubeNorm
import GMZP0.CyclicLiftValues
import GMZP0.WeightedFrequencyCube
import GMZP0.IndependentAssignments

/-! Actual cyclic local norms and the original weighted four-cube parameters. -/

noncomputable section
open scoped BigOperators
namespace GMZP0

def cyclicShiftMap (q ℓ : ℕ) (h : ℤ) (v : smoothingShiftLabels ℓ) : ZMod q :=
  ((2 * h * v.val : ℤ) : ZMod q)

theorem localBoxFunction_cyclic_vertex (q ℓ : ℕ) (H : ZMod q → ℂ)
    (h : ℤ) (Y : ZMod q) (u : CubeShiftPairs ℓ) (ω : Fin 4 → Bool) :
    localBoxFunction 3 H (cyclicShiftMap q ℓ h) Y (cubeVertex u ω) =
      H (cyclicCubeVertex q ℓ h Y u ω) := by
  unfold localBoxFunction cyclicShiftMap cyclicCubeVertex cubeShiftSum fourShiftSum
  rw [← Int.cast_sum, ← Finset.mul_sum]

theorem cyclicLocalMoment_expand (q ℓ : ℕ) [NeZero q] (H : ZMod q → ℂ) (h : ℤ) :
    localCubeMoment 3 H (cyclicShiftMap q ℓ h) =
      realUniformMean (fun Y : ZMod q => realUniformMean (fun u : CubeShiftPairs ℓ =>
        (∏ ω, cubeConj 4 ω (H (cyclicCubeVertex q ℓ h Y u ω))).re)) := by
  unfold localCubeMoment
  congr 1
  funext Y
  rw [boxMoment_eq_cubeMean_re, cubeMean, complexUniformMean_re]
  simp only [cubeProduct, localBoxFunction_cyclic_vertex]

def modulatedCyclicField (N q M : ℕ) (σ : Base N → ℝ) (F : Fin N → ZMod q → ℝ)
    (x : Fin N) (j : Fin (1024 * M)) (Y : ZMod q) : ℂ :=
  ((cyclicField N q σ 0 x Y : ℝ) : ℂ) * circleCharacter ((meshFrequency M j * F x Y : ℝ) : Frequency)

theorem modulatedCyclicField_norm (N q M : ℕ) (σ : Base N → ℝ) (F : Fin N → ZMod q → ℝ)
    (x : Fin N) (j : Fin (1024 * M)) (Y : ZMod q) :
    ‖modulatedCyclicField N q M σ F x j Y‖ = |cyclicField N q σ 0 x Y| := by
  simp only [modulatedCyclicField, norm_mul, norm_circleCharacter, mul_one,
    Complex.norm_real, Real.norm_eq_abs]

theorem modulatedCyclicField_norm_le (N q M : ℕ) (σ : Base N → ℝ) (F : Fin N → ZMod q → ℝ)
    (hσ : ∀ z, 0 ≤ σ z ∧ σ z ≤ 1) (x : Fin N) (j : Fin (1024 * M)) (Y : ZMod q) :
    ‖modulatedCyclicField N q M σ F x j Y‖ ≤ 1 := by
  rw [modulatedCyclicField_norm]
  have hs := cyclicField_property N q σ 0 (fun t : ℝ => 0 ≤ t ∧ t ≤ 1)
    hσ ⟨le_rfl, zero_le_one⟩ x Y
  rw [abs_of_nonneg hs.1]
  exact hs.2

theorem cyclic_weighted_frequency_cube {N q ℓ M : ℕ} (hM : 0 < M)
    (σ : Base N → ℝ) (F : Fin N → ZMod q → ℝ)
    (hgrid : ∀ x Y, ∃ k : ℤ, F x Y = (k : ℝ) / M) (hF : ∀ x Y, |F x Y| ≤ 3)
    (x : Fin N) (h : ℤ) (Y : ZMod q) (u : CubeShiftPairs ℓ) :
    realUniformMean (fun j : Fin (1024 * M) =>
      (∏ ω, cubeConj 4 ω (modulatedCyclicField N q M σ F x j (cyclicCubeVertex q ℓ h Y u ω))).re) =
        if cyclicRealCubeDifference q ℓ F x Y h u = 0
        then cyclicCubeWeight N q ℓ σ x Y h u else 0 := by
  exact weighted_frequency_cube_real (by decide : 4 ≤ 7) hM
    (fun ω => cyclicField N q σ 0 x (cyclicCubeVertex q ℓ h Y u ω))
    (fun ω => F x (cyclicCubeVertex q ℓ h Y u ω))
    (fun ω => hgrid x _) (fun ω => hF x _)

theorem cyclic_local_frequency_row {N q ℓ M : ℕ} [NeZero q] (hM : 0 < M)
    (σ : Base N → ℝ) (F : Fin N → ZMod q → ℝ)
    (hgrid : ∀ x Y, ∃ k : ℤ, F x Y = (k : ℝ) / M) (hF : ∀ x Y, |F x Y| ≤ 3)
    (x : Fin N) (h : ℤ) :
    realUniformMean (fun j : Fin (1024 * M) =>
      localCubeMoment 3 (modulatedCyclicField N q M σ F x j) (cyclicShiftMap q ℓ h)) =
        realUniformMean (fun Y : ZMod q => realUniformMean (fun u : CubeShiftPairs ℓ =>
          if cyclicRealCubeDifference q ℓ F x Y h u = 0
          then cyclicCubeWeight N q ℓ σ x Y h u else 0)) := by
  simp only [cyclicLocalMoment_expand]
  rw [realUniformMean_comm]
  congr 1
  funext Y
  rw [realUniformMean_comm]
  congr 1
  funext u
  exact cyclic_weighted_frequency_cube hM σ F hgrid hF x h Y u

end GMZP0
