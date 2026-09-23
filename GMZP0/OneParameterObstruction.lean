import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! The original right semidirect multiplication already forces a
quadratic fiber correction for affine observations on the real line.
These are exact identities, not finite tests of a general claim. -/
namespace GMZP0

/-- With Q(u)=u and left translations u -> t+u, the naive fiber t*Q
fails the original right semidirect one-parameter law. -/
theorem naive_linear_fiber_not_one_parameter :
    ¬ (∀ s t u : ℝ, (s + t) * u = s * (t + u) + t * u) := by
  intro h
  have h110 := h 1 1 0
  norm_num at h110

/-- The second-order term predicted by the manuscript gives the exact
original composition law in this basic nonconstant example. -/
theorem affine_quadratic_fiber_composition (s t u : ℝ) :
    (s + t) * u + (s + t) ^ 2 / 2 =
      (s * (t + u) + s ^ 2 / 2) + (t * u + t ^ 2 / 2) := by
  ring

end GMZP0
