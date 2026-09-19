import GMZP0.CompactCosetLifts

/-! Uniform local metric bounds globalize on a bounded actual range.
This will derive the original quotient projection constant rather than
inserting it as an additional assumption on the final cutoff. -/
noncomputable section
open Set Metric
namespace GMZP0

/-- A fixed local Lipschitz radius and a bounded actual image give one
global constant, including point pairs in different charts. -/
theorem lipschitz_of_uniform_local_bound {X Y : Type*}
    [PseudoMetricSpace X] [PseudoMetricSpace Y]
    (f : X → Y) (L r : ℝ) (hL : 0 ≤ L) (hr : 0 < r)
    (hlocal : ∀ x y, dist x y < r → dist (f x) (f y) ≤ L * dist x y)
    (hbounded : Bornology.IsBounded (Set.range f)) :
    LipschitzWith (Real.toNNReal (L + diam (Set.range f) / r)) f := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [Real.coe_toNNReal _ (by positivity)]
  by_cases hxy : dist x y < r
  · have h := hlocal x y hxy
    have hn : 0 ≤ diam (Set.range f) / r * dist x y := by positivity
    nlinarith
  · have h := dist_le_diam_of_mem hbounded (Set.mem_range_self x) (Set.mem_range_self y)
    have hd : diam (Set.range f) ≤ diam (Set.range f) / r * dist x y := by
      have hh := mul_le_mul_of_nonneg_left (le_of_not_gt hxy)
        (show 0 ≤ diam (Set.range f) / r by positivity)
      simpa only [div_mul_cancel₀ _ hr.ne'] using hh
    have hn : 0 ≤ L * dist x y := mul_nonneg hL dist_nonneg
    nlinarith

end GMZP0
