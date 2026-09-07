import GMZP0.CubeLiftCorrection
import GMZP0.LiftGridScale
import GMZP0.UniformDistinctCubeCapture

/-! One pointwise assignment defines one cyclic real lift, with the original support unchanged. -/

noncomputable section
open scoped BigOperators
namespace GMZP0

abbrev CyclicLiftAssignments (N q : ℕ) := (Fin N × ZMod q) → LiftChoice

def cyclicLiftValue (N q M : ℕ) (p : Base N → Frequency) (σ : Base N → ℝ) (d : ℕ)
    (c : CyclicLiftAssignments N q) (x : Fin N) (Y : ZMod q) : ℝ :=
  if 0 < cyclicField N q σ 0 x Y then liftChoiceValue M (d • cyclicField N q p 0 x Y) (c (x, Y)) else 0

def cyclicRealCubeDifference {N : ℕ} (q ℓ : ℕ) (F : Fin N → ZMod q → ℝ)
    (x : Fin N) (Y : ZMod q) (h : ℤ) (u : CubeShiftPairs ℓ) : ℝ :=
  ∑ ω, (cubeSign 4 ω : ℝ) * F x (cyclicCubeVertex q ℓ h Y u ω)

def cyclicRealCubeMass (N q ℓ : ℕ) [NeZero q] (σ : Base N → ℝ) (F : Fin N → ZMod q → ℝ) : ℝ :=
  realUniformMean (fun z : PositiveCubeParameters N q ℓ =>
    if cyclicRealCubeDifference q ℓ F z.1 z.2.2.1 (label z.2.1) z.2.2.2 = 0
    then cyclicCubeWeight N q ℓ σ z.1 z.2.2.1 (label z.2.1) z.2.2.2 else 0)

theorem cyclicLiftValue_grid {N q M : ℕ} (hM : 0 < M) (p : Base N → Frequency)
    (σ : Base N → ℝ) (d : ℕ) (c : CyclicLiftAssignments N q) (x : Fin N) (Y : ZMod q) :
    ∃ k : ℤ, cyclicLiftValue N q M p σ d c x Y = (k : ℝ) / M := by
  unfold cyclicLiftValue
  split_ifs
  · exact liftChoiceValue_grid hM _ _
  · exact ⟨0, by simp⟩

theorem cyclicLiftValue_abs_le {N q M : ℕ} (hM : 9 ≤ M) (p : Base N → Frequency)
    (σ : Base N → ℝ) (d : ℕ) (c : CyclicLiftAssignments N q) (x : Fin N) (Y : ZMod q) :
    |cyclicLiftValue N q M p σ d c x Y| ≤ 3 := by
  unfold cyclicLiftValue
  split_ifs
  · exact liftChoiceValue_abs_le hM _ _
  · norm_num

theorem cyclicLiftValue_zero {N q M : ℕ} (p : Base N → Frequency)
    (σ : Base N → ℝ) (d : ℕ) (c : CyclicLiftAssignments N q) (x : Fin N) (Y : ZMod q)
    (hz : cyclicField N q σ 0 x Y = 0) : cyclicLiftValue N q M p σ d c x Y = 0 := by
  simp only [cyclicLiftValue, hz, lt_self_iff_false, if_false]

theorem cyclicLiftValue_circle_error {N q M : ℕ} (hM : 0 < M) (p : Base N → Frequency)
    (σ : Base N → ℝ) (d : ℕ) (c : CyclicLiftAssignments N q) (x : Fin N) (Y : ZMod q)
    (hs : 0 < cyclicField N q σ 0 x Y) :
    ‖((cyclicLiftValue N q M p σ d c x Y : ℝ) : Frequency) - d • cyclicField N q p 0 x Y‖ ≤
      19 / (2 * (M : ℝ)) := by
  rw [cyclicLiftValue, if_pos hs]
  exact liftChoiceValue_circle_error hM _ _

theorem cyclicLiftValue_original_error {N q M : ℕ} (hq : N ^ 2 < q) (hM : 0 < M)
    (p : Base N → Frequency) (σ : Base N → ℝ) (d : ℕ) (c : CyclicLiftAssignments N q)
    (z : Base N) (hz : 0 < σ z) :
    ‖((cyclicLiftValue N q M p σ d c z.1 (cyclicRow N q z.2) : ℝ) : Frequency) - d • p z‖ ≤
      19 / (2 * (M : ℝ)) := by
  have hs : 0 < cyclicField N q σ 0 z.1 (cyclicRow N q z.2) := by rwa [cyclicField_original hq]
  simpa only [cyclicField_original hq] using cyclicLiftValue_circle_error hM p σ d c z.1 _ hs

end GMZP0
