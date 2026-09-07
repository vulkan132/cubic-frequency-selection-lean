import Mathlib.Tactic.Ring

/-!
Exact algebra from the manuscript's double-adjoint and lag phases.
These identities prove no analytic extraction or freezing estimate.
-/

namespace GMZP0

variable {R : Type*} [CommRing R]

/-- The second derivative factor in the reverse block; all three terms survive. -/
theorem cubic_lag_difference (t k : R) :
    t ^ 3 - (t - k) ^ 3 = 3 * k * t ^ 2 - 3 * k ^ 2 * t + k ^ 3 := by
  ring

/-- Exact rerooting of the other-source vertical coordinate. -/
theorem lag_target_coordinate (y h k t : R) :
    y + 2 * h * ((t - k + h) + k) - h ^ 2 = y + h ^ 2 + 2 * h * t := by
  ring

/-- Equation (double-phase) after r = t-k+h; the three frequencies are distinct. -/
theorem double_phase_reroot (a b c h k t : R) :
    a * ((t - k + h) + k) ^ 3 - b * (t - k + h) ^ 3 -
      c * ((((t - k + h) + k) - h) ^ 3 - ((t - k + h) - h) ^ 3) =
    a * (t + h) ^ 3 - b * (t + h - k) ^ 3 -
      (t ^ 3 - (t - k) ^ 3) * c := by
  ring

/-- Four additive differences, with the base vertex assigned positive sign. -/
def diff (f : R → R) (h : R) : R → R := fun t => f t - f (t + h)

/-- Four lag differences annihilate every polynomial of degree at most three. -/
theorem fourth_difference_cubic (a b c d h₁ h₂ h₃ h₄ t : R) :
    diff (diff (diff (diff (fun u => a * u ^ 3 + b * u ^ 2 + c * u + d)
      h₁) h₂) h₃) h₄ t = 0 := by
  simp only [diff]
  ring

/-- The two ordinary linear-profile directions must retain the multiplier eight. -/
theorem linear_collision_eight (a b : R) :
    3 * (a + 3 * b) - (3 * a + b) = 8 * b := by
  ring

end GMZP0
