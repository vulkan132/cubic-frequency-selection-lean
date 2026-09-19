import GMZP0.MetricBoundaryCutoff
import Mathlib.Analysis.Complex.Basic

/-! Quantitative gluing of a unit observation across its actual boundary.
The local alternative concerns the unchanged observation, before any
cutoff scale is chosen. A Lipschitz cutoff alone is not enough. -/
noncomputable section
open Set Metric
open scoped NNReal
namespace GMZP0

/-- Product comparison retaining the small coefficient on a possible jump. -/
theorem unit_cutoff_product_difference (a b : ℝ) (ha : 0 ≤ a) (u v : ℂ)
    (hv : ‖v‖ = 1) :
    ‖(a : ℂ) * u - (b : ℂ) * v‖ ≤ a * ‖u - v‖ + |a - b| := by
  have he : (a : ℂ) * u - (b : ℂ) * v =
      (a : ℂ) * (u - v) + ((a - b : ℝ) : ℂ) * v := by push_cast; ring
  rw [he]
  apply (norm_add_le _ _).trans_eq
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ha, hv, mul_one]

/-- Near an actual boundary the cutoff itself is bounded by distance/t. -/
theorem boundary_cutoff_le_distance_div {X : Type*} [PseudoMetricSpace X]
    (S : Set X) (hS : S.Nonempty) {t : ℝ} (ht : 0 < t) (x : X) :
    boundaryCutoff S t x ≤ infDist x S / t := by
  by_cases hx : infDist x S ≤ t
  · rw [(boundary_cutoff_zero_near S ht x hS hx).2]
    exact div_nonneg infDist_nonneg ht.le
  · exact (boundary_cutoff_bounds S t x).2.2.2.trans ((one_le_div ht).mpr (le_of_not_ge hx))

/-- A scale-independent local alternative gives a uniform O(1/t) product
bound: either the original values are close, or the first base point is
within A times the pair distance of the actual boundary. -/
theorem boundary_cutoff_lipschitz_of_local_alternative
    {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    (pi : X → Y) (J : ℝ≥0) (hpi : LipschitzWith J pi)
    (S : Set Y) (psi : X → ℂ) (hunit : ∀ x, ‖psi x‖ = 1)
    (L A r : ℝ) (hL : 0 ≤ L) (hA : 0 ≤ A) (hr : 0 < r)
    (hpair : ∀ x y, dist x y < r →
      ‖psi x - psi y‖ ≤ L * dist x y ∨
        (S.Nonempty ∧ infDist (pi x) S ≤ A * dist x y))
    {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
    LipschitzWith (Real.toNNReal ((L + 2 * A + J + 2 / r) / t))
      (fun x => (boundaryCutoff S t (pi x) : ℂ) * psi x) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [Real.coe_toNNReal _ (by positivity), dist_eq_norm, div_mul_eq_mul_div]
  apply (le_div_iff₀ ht).mpr
  have hx0 := (boundary_cutoff_bounds S t (pi x)).2.2.1
  have hx1 := (boundary_cutoff_bounds S t (pi x)).2.2.2
  have hy0 := (boundary_cutoff_bounds S t (pi y)).2.2.1
  have hy1 := (boundary_cutoff_bounds S t (pi y)).2.2.2
  have hchi : |boundaryCutoff S t (pi x) - boundaryCutoff S t (pi y)| ≤
      (J : ℝ) / t * dist x y := by
    have h := ((boundary_cutoff_lipschitz S ht).comp hpi).dist_le_mul x y
    simpa only [Function.comp_apply, Real.dist_eq, NNReal.coe_mul, Real.coe_toNNReal _ (inv_nonneg.mpr ht.le),
      div_eq_mul_inv, mul_comm t⁻¹] using h
  have hd : ‖psi x - psi y‖ ≤ 2 := by
    simpa only [hunit, one_add_one_eq_two] using norm_sub_le (psi x) (psi y)
  have hprod := (unit_cutoff_product_difference _ (boundaryCutoff S t (pi y))
    hx0 (psi x) (psi y) (hunit y)).trans (add_le_add le_rfl hchi)
  have htd : 0 ≤ dist x y := dist_nonneg
  have hfrac : ((J : ℝ) / t * dist x y) * t = J * dist x y := by field_simp
  by_cases hclose : dist x y < r
  · rcases hpair x y hclose with hgood | ⟨hS, hnear⟩
    · have hb : boundaryCutoff S t (pi x) * ‖psi x - psi y‖ ≤ L * dist x y :=
        (mul_le_mul_of_nonneg_left hgood hx0).trans
          (by simpa using mul_le_mul_of_nonneg_right hx1 (mul_nonneg hL htd))
      have hh := mul_le_mul_of_nonneg_right (hprod.trans (add_le_add hb le_rfl)) ht.le
      have hLt := mul_le_mul_of_nonneg_left ht1 (mul_nonneg hL htd)
      have hrest : 0 ≤ (2 * A + 2 / r) * dist x y := by positivity
      rw [add_mul, hfrac] at hh
      nlinarith
    · have hc : boundaryCutoff S t (pi x) ≤ A * dist x y / t :=
        (boundary_cutoff_le_distance_div S hS ht _).trans (div_le_div_of_nonneg_right hnear ht.le)
      have hb : boundaryCutoff S t (pi x) * ‖psi x - psi y‖ ≤ 2 * (A * dist x y / t) :=
        (mul_le_mul_of_nonneg_left hd hx0).trans (by nlinarith)
      have hh := mul_le_mul_of_nonneg_right (hprod.trans (add_le_add hb le_rfl)) ht.le
      have hdiv : (2 * (A * dist x y / t)) * t = 2 * A * dist x y := by field_simp
      have hrest : 0 ≤ (L + 2 / r) * dist x y := by positivity
      rw [add_mul, hdiv, hfrac] at hh
      nlinarith
  · have hbound : ‖(boundaryCutoff S t (pi x) : ℂ) * psi x -
        (boundaryCutoff S t (pi y) : ℂ) * psi y‖ ≤ 2 := by
      have h := norm_sub_le ((boundaryCutoff S t (pi x) : ℂ) * psi x)
        ((boundaryCutoff S t (pi y) : ℂ) * psi y)
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hx0,
        abs_of_nonneg hy0, hunit, mul_one] at h
      linarith
    have hh := mul_le_mul_of_nonneg_right hbound ht.le
    have hfar : 2 ≤ (2 / r) * dist x y := by
      have h := (le_div_iff₀ hr).mpr (show 2 * r ≤ 2 * dist x y by linarith [le_of_not_gt hclose])
      simpa only [div_mul_eq_mul_div] using h
    have hrest : 0 ≤ (L + 2 * A + J) * dist x y := by positivity
    nlinarith

end GMZP0
