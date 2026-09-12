import GMZP0.LargeBlockLags
import GMZP0.PolynomialDifferencing
import Mathlib.Tactic.Module

/-! The exact cubic phase of a full affine vertical profile, on the original lag labels. -/
noncomputable section
open scoped BigOperators
namespace GMZP0

/-- A full integer affine profile with unrestricted circle slope and intercept. -/
def affineVerticalProfile {N : ℕ} (a b : Fin N → Frequency) (x : Fin N) (y : ℤ) : Frequency :=
  y • a x + b x

/-- Restriction uses exactly the original one-based vertical coordinate. -/
def affineOriginalProfile {N : ℕ} (a b : Fin N → Frequency) (z : Base N) : Frequency :=
  affineVerticalProfile a b z.1 (label z.2)

/-- The full affine formula agrees with the actual original profile everywhere in its box. -/
theorem affine_profile_agreement {N : ℕ} (a b : Fin N → Frequency) :
    WideProfileAgreement N (affineVerticalProfile a b) (affineOriginalProfile a b) := by
  intro x y
  rfl

/-- The leading coefficient is independent of the original root and both intercepts. -/
def affineBlockCubic (a c : Frequency) (h k : ℤ) : Frequency := (-2 * h * k) • (a + 3 • c)

def affineBlockQuadratic (a b c d : Frequency) (y h k : ℤ) : Frequency :=
  (3 * k) • (y • a + b) - (3 * k) • ((y + 2 * h * k - h ^ 2) • c + d) -
    (2 * h * (3 * k ^ 2 - 6 * k * h)) • c

def affineBlockLinear (a b c d : Frequency) (y h k : ℤ) : Frequency :=
  (3 * k ^ 2) • (y • a + b) - (3 * k ^ 2 - 6 * k * h) • ((y + 2 * h * k - h ^ 2) • c + d) -
    (2 * h * (k ^ 3 - 3 * k ^ 2 * h + 3 * k * h ^ 2)) • c

def affineBlockConstant (a b c d : Frequency) (y h k : ℤ) : Frequency :=
  k ^ 3 • (y • a + b) - (k ^ 3 - 3 * k ^ 2 * h + 3 * k * h ^ 2) •
    ((y + 2 * h * k - h ^ 2) • c + d)

/-- The complete circle phase is a cubic with all four coefficients explicit. -/
theorem affine_double_phase_polynomial (a b c d : Frequency) (y h k r : ℤ) :
    doublePhaseCoefficient (y • a + b) ((y + 2 * h * k) • a + b)
      ((y + 2 * h * (r + k) - h ^ 2) • c + d) h k r =
    cubicCirclePolynomial (affineBlockCubic a c h k) (affineBlockQuadratic a b c d y h k)
      (affineBlockLinear a b c d y h k) (affineBlockConstant a b c d y h k) r := by
  simp only [doublePhaseCoefficient, cubicCirclePolynomial, affineBlockCubic,
    affineBlockQuadratic, affineBlockLinear, affineBlockConstant]
  module

/-- Specialization of the actual widened phase, without an arbitrary outside-box extension. -/
theorem affine_wideDoublePhase {N : ℕ} (a b : Fin N → Frequency) (x x' : Fin N) (y k r : ℤ) :
    wideDoublePhase (affineVerticalProfile a b) x x' y k r =
      cubicCirclePolynomial (affineBlockCubic (a x) (a x') (horizontalGap x x') k)
        (affineBlockQuadratic (a x) (b x) (a x') (b x') y (horizontalGap x x') k)
        (affineBlockLinear (a x) (b x) (a x') (b x') y (horizontalGap x x') k)
        (affineBlockConstant (a x) (b x) (a x') (b x') y (horizontalGap x x') k) r := by
  exact affine_double_phase_polynomial (a x) (b x) (a x') (b x') y (horizontalGap x x') k r

/-- The true lag sum is the complete cubic sum on its actual overlap, before taking norms. -/
theorem affine_wideLagSum {N : ℕ} (a b : Fin N → Frequency) (x x' : Fin N) (y k : ℤ) :
    wideLagSum (affineVerticalProfile a b) x x' y k =
      ∑ r ∈ lagLabels N (horizontalGap x x') k,
        circleCharacter (cubicCirclePolynomial (affineBlockCubic (a x) (a x') (horizontalGap x x') k)
          (affineBlockQuadratic (a x) (b x) (a x') (b x') y (horizontalGap x x') k)
          (affineBlockLinear (a x) (b x) (a x') (b x') y (horizontalGap x x') k)
          (affineBlockConstant (a x) (b x) (a x') (b x') y (horizontalGap x x') k) r) := by
  simp only [wideLagSum, affine_wideDoublePhase]

/-- The reverse direction has cubic coefficient +2hk(3a+c), with its own lag k. -/
theorem affineBlockCubic_reverse (a c : Frequency) (h k : ℤ) :
    affineBlockCubic c a (-h) k = (2 * h * k) • (3 • a + c) := by
  simp only [affineBlockCubic]
  module

/-- Taking both independent directional relations leaves the exact integer multiplier eight. -/
theorem affine_two_direction_elimination (a c : Frequency) (h : ℤ) (n₁ n₂ : ℕ) :
    (3 * n₁) • (n₂ • (h • (3 • a + c))) - n₂ • (n₁ • (h • (a + 3 • c))) =
      (8 * n₁ * n₂) • (h • a) := by
  module

/-- Both directional combinations can vanish while the slope is nonzero; the factor 8 cannot be cancelled. -/
theorem affine_direction_branch_obstruction :
    ∃ a c : Frequency, a + 3 • c = 0 ∧ 3 • a + c = 0 ∧ ‖a‖ = (1 / 4 : ℝ) := by
  let a : Frequency := ((1 / 4 : ℝ) : Frequency)
  have hs : a + 3 • a = 0 := by
    change ((1 / 4 : ℝ) : Frequency) + 3 • ((1 / 4 : ℝ) : Frequency) = 0
    rw [← AddCircle.coe_nsmul, ← AddCircle.coe_add]
    norm_num [nsmul_eq_mul, AddCircle.coe_period]
  have hn : ‖a‖ = (1 / 4 : ℝ) := by
    have hh := (AddCircle.norm_coe_eq_abs_iff (p := (1 : ℝ)) (x := (1 / 4 : ℝ))
      (by norm_num)).2 (by norm_num)
    simpa [a] using hh
  exact ⟨a, a, hs, by simpa only [add_comm] using hs, hn⟩

end GMZP0
