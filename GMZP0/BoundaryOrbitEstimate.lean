import GMZP0.MetricBoundaryCutoff
import GMZP0.MeanAlgebra
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! Quantitative testing and the actual finite-orbit boundary error.
Every original orbit point is retained. The metric and tube estimates are
explicit inputs; neither follows from a small boundary measure alone. -/
noncomputable section
open Set Metric MeasureTheory
open scoped NNReal
namespace GMZP0
variable {X Y I : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
  [Fintype I]

/-- Testing all bounded Lipschitz functions, with the sup-bound plus Lipschitz
constant convention. A finite interval is represented by its full subtype. -/
def LipschitzOrbitDiscrepancy (mu : Measure X) (u : I → X) (alpha : ℝ) : Prop :=
  ∀ (F : X → ℂ) (B : ℝ) (L : ℝ≥0), (∀ x, ‖F x‖ ≤ B) → LipschitzWith L F →
    ‖complexUniformMean (fun i => F (u i)) - ∫ x, F x ∂mu‖ ≤ alpha * (B + L)

/-- Complex testing controls the same real test with no loss of constants. -/
theorem orbit_discrepancy_real (mu : Measure X) (u : I → X) (alpha : ℝ)
    (h : LipschitzOrbitDiscrepancy mu u alpha) (f : X → ℝ) (B : ℝ) (L : ℝ≥0)
    (hf : ∀ x, |f x| ≤ B) (hL : LipschitzWith L f) :
    |realUniformMean (fun i => f (u i)) - ∫ x, f x ∂mu| ≤ alpha * (B + L) := by
  have hc : LipschitzWith L (fun x => (f x : ℂ)) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [Complex.isometry_ofReal.dist_eq]
    exact hL.dist_le_mul x y
  have hh := h (fun x => (f x : ℂ)) B L (fun x => by simpa using hf x) hc
  have he : complexUniformMean (fun i => (f (u i) : ℂ)) =
      (realUniformMean (fun i => f (u i)) : ℂ) := by
    simp [complexUniformMean, realUniformMean]
  simpa only [he, integral_complex_ofReal, ← Complex.ofReal_sub,
    Complex.norm_real, Real.norm_eq_abs] using hh

variable [PseudoMetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]

/-- Testing the actual pulled-back majorant bounds actual visits, using the
proved measure-preserving projection to the original base. -/
theorem orbit_boundary_majorant_mean_le (mu : Measure X) (nu : Measure Y) [IsFiniteMeasure nu]
    (pi : X → Y) (hp : MeasurePreserving pi mu nu) (J : ℝ≥0) (hJ : LipschitzWith J pi)
    (S : Set Y) {t : ℝ} (ht : 0 < t) (u : I → X) (alpha : ℝ)
    (heq : LipschitzOrbitDiscrepancy mu u alpha) :
    realUniformMean (fun i => boundaryMajorant S t (pi (u i))) ≤
      (nu (boundaryTube S (2 * t))).toReal + alpha * (1 + t⁻¹ * J) := by
  have hbm := (boundary_majorant_lipschitz S ht).continuous.measurable
  have hi : (∫ x, boundaryMajorant S t (pi x) ∂mu) =
      ∫ y, boundaryMajorant S t y ∂nu := by
    rw [← hp.map_eq]
    exact (integral_map hp.measurable.aemeasurable hbm.aestronglyMeasurable).symm
  have hd := orbit_discrepancy_real mu u alpha heq (fun x => boundaryMajorant S t (pi x)) 1
    (Real.toNNReal t⁻¹ * J)
    (fun x => by rw [abs_of_nonneg (boundary_cutoff_bounds S t (pi x)).1]
                 exact (boundary_cutoff_bounds S t (pi x)).2.1)
    ((boundary_majorant_lipschitz S ht).comp hJ)
  rw [hi, NNReal.coe_mul, Real.coe_toNNReal _ (inv_nonneg.mpr ht.le)] at hd
  have hmean := boundary_majorant_integral_le_tube nu S ht
  have hupper := (abs_le.mp hd).2
  linarith

omit [MeasurableSpace Y] [BorelSpace Y] in
/-- A cutoff of a unit-norm observation has error exactly the constructed
majorant; this is pointwise, including every boundary point. -/
theorem unit_observation_cutoff_error (S : Set Y) (t : ℝ) (y : Y) (z : ℂ)
    (hz : ‖z‖ = 1) :
    ‖z - (boundaryCutoff S t y : ℂ) * z‖ = boundaryMajorant S t y := by
  have he : z - (boundaryCutoff S t y : ℂ) * z = (boundaryMajorant S t y : ℂ) * z := by
    simp only [boundaryCutoff, Complex.ofReal_sub, Complex.ofReal_one]
    ring
  rw [he, norm_mul, hz, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (boundary_cutoff_bounds S t y).1]

/-- The precise orbit bound from the original observation, its zero-mean
cutoff, the actual metric projection, and the actual doubled-tube measure. -/
theorem boundary_orbit_observation_bound (mu : Measure X) (nu : Measure Y) [IsFiniteMeasure nu]
    (pi : X → Y) (hp : MeasurePreserving pi mu nu) (J : ℝ≥0) (hJ : LipschitzWith J pi)
    (S : Set Y) {t : ℝ} (ht : 0 < t) (psi : X → ℂ) (hpsi : ∀ x, ‖psi x‖ = 1)
    (K : ℝ≥0)
    (hK : LipschitzWith K (fun x => (boundaryCutoff S t (pi x) : ℂ) * psi x))
    (hzero : (∫ x, (boundaryCutoff S t (pi x) : ℂ) * psi x ∂mu) = 0)
    (u : I → X) (alpha : ℝ) (heq : LipschitzOrbitDiscrepancy mu u alpha) :
    ‖complexUniformMean (fun i => psi (u i))‖ ≤
      (nu (boundaryTube S (2 * t))).toReal + alpha * (2 + K + t⁻¹ * J) := by
  let F : X → ℂ := fun x => (boundaryCutoff S t (pi x) : ℂ) * psi x
  have hF : ∀ x, ‖F x‖ ≤ 1 := by
    intro x
    dsimp [F]
    rw [norm_mul, hpsi, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (boundary_cutoff_bounds S t (pi x)).2.2.1]
    exact (boundary_cutoff_bounds S t (pi x)).2.2.2
  have htest := heq F 1 K hF hK
  change ‖complexUniformMean (fun i => F (u i)) - ∫ x, F x ∂mu‖ ≤ _ at htest
  rw [show (∫ x, F x ∂mu) = 0 from hzero, sub_zero] at htest
  have herr : ‖complexUniformMean (fun i => psi (u i)) - complexUniformMean (fun i => F (u i))‖ ≤
      realUniformMean (fun i => boundaryMajorant S t (pi (u i))) := by
    rw [← complexUniformMean_sub]
    simpa only [F, unit_observation_cutoff_error S t _ _ (hpsi _)] using
      norm_complexUniformMean_le_mean_norm (fun i => psi (u i) - F (u i))
  have hb := orbit_boundary_majorant_mean_le mu nu pi hp J hJ S ht u alpha heq
  have htri := norm_le_norm_sub_add (complexUniformMean (fun i => psi (u i)))
    (complexUniformMean (fun i => F (u i)))
  linarith

/-- Choose the geometric scale first and the discrepancy tolerance second,
both before the orbit. The constants are uniform in all original coefficients. -/
theorem boundary_error_parameters (C D gamma : ℝ) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hg : 0 < gamma) :
    ∃ t alpha : ℝ, 0 < t ∧ t ≤ 1 ∧ 0 < alpha ∧
      C * t + alpha * (2 + D / t) ≤ gamma / 2 := by
  let t := min 1 (gamma / (4 * (C + 1)))
  have hden : 0 < 4 * (C + 1) := by positivity
  have ht : 0 < t := lt_min zero_lt_one (div_pos hg hden)
  have ht1 : t ≤ 1 := min_le_left _ _
  have ht' : t * (4 * (C + 1)) ≤ gamma :=
    (le_div_iff₀ hden).mp (min_le_right _ _)
  have hCt : C * t ≤ gamma / 4 := by nlinarith
  let alpha := gamma / (4 * (2 + D / t))
  have hden' : 0 < 2 + D / t := by positivity
  have ha : 0 < alpha := div_pos hg (mul_pos (by norm_num) hden')
  have he : alpha * (2 + D / t) = gamma / 4 := by
    dsimp [alpha]
    field_simp
  exact ⟨t, alpha, ht, ht1, ha, by rw [he]; linarith⟩

/-- Conditional quantitative non-equidistribution, with one t and alpha
chosen before every actual orbit. The two unproved geometric estimates
are visible as the tube bound and the original cutoff's Lipschitz bound. -/
theorem uniform_boundary_nonequidistribution (mu : Measure X) (nu : Measure Y) [IsFiniteMeasure nu]
    (pi : X → Y) (hp : MeasurePreserving pi mu nu) (J : ℝ≥0) (hJ : LipschitzWith J pi)
    (S : Set Y) (psi : X → ℂ) (hpsi : ∀ x, ‖psi x‖ = 1)
    (C A : ℝ) (hC : 0 ≤ C) (hA : 0 ≤ A)
    (hmass : ∀ t : ℝ, 0 < t → t ≤ 1 → (nu (boundaryTube S (2 * t))).toReal ≤ C * t)
    (hK : ∀ t : ℝ, 0 < t → t ≤ 1 →
      LipschitzWith (Real.toNNReal (A / t)) (fun x => (boundaryCutoff S t (pi x) : ℂ) * psi x))
    (hzero : ∀ t : ℝ, 0 < t → t ≤ 1 →
      (∫ x, (boundaryCutoff S t (pi x) : ℂ) * psi x ∂mu) = 0)
    (gamma : ℝ) (hg : 0 < gamma) :
    ∃ t alpha : ℝ, 0 < t ∧ t ≤ 1 ∧ 0 < alpha ∧
      ∀ (I : Type*) [Fintype I] (u : I → X), gamma < ‖complexUniformMean (fun i => psi (u i))‖ →
        ¬ LipschitzOrbitDiscrepancy mu u alpha := by
  obtain ⟨t, alpha, ht, ht1, ha, hbudget⟩ :=
    boundary_error_parameters C (A + J) gamma hC (add_nonneg hA J.coe_nonneg) hg
  refine ⟨t, alpha, ht, ht1, ha, ?_⟩
  intro I _ u hu heq
  have hbound := boundary_orbit_observation_bound mu nu pi hp J hJ S ht psi hpsi
    (Real.toNNReal (A / t)) (hK t ht ht1) (hzero t ht ht1) u alpha heq
  rw [Real.coe_toNNReal _ (div_nonneg hA ht.le)] at hbound
  have he : 2 + A / t + t⁻¹ * (J : ℝ) = 2 + (A + J) / t := by ring
  rw [he] at hbound
  have hm := hmass t ht ht1
  linarith

end GMZP0
