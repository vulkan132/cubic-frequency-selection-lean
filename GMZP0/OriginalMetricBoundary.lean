import GMZP0.QuotientBoundaryTube

/-! A genuine linear tube bound for the specified original invariant
probability, derived from exact coordinate data, the original coset-distance
formula and fixed local coordinate metric bounds. -/
noncomputable section
open Set Metric MeasureTheory MeasureTheory.Measure
namespace GMZP0

/-- For probability measures, a small-scale linear bound extends to all
positive scales with one explicitly controlled structural constant. -/
theorem local_probability_bound_global {X : Type*} [MeasurableSpace X]
    (mu : Measure X) [IsProbabilityMeasure mu] (A : ℝ → Set X)
    (C r : ℝ) (hC : 0 ≤ C) (hr : 0 < r)
    (hsmall : ∀ t : ℝ, 0 < t → t ≤ r → (mu (A t)).toReal ≤ C * t) :
    ∀ t : ℝ, 0 < t → (mu (A t)).toReal ≤ (C + r⁻¹) * t := by
  intro t ht
  by_cases htr : t ≤ r
  · have h := hsmall t ht htr
    have hnonneg : 0 ≤ r⁻¹ * t := mul_nonneg (inv_nonneg.mpr hr.le) ht.le
    nlinarith
  · have hp : mu (A t) ≤ 1 := prob_le_one
    have hp' : (mu (A t)).toReal ≤ 1 := by
      simpa using ENNReal.toReal_mono ENNReal.one_ne_top hp
    have hrt : 1 ≤ r⁻¹ * t := by
      have h := (one_le_div hr).mpr (lt_of_not_ge htr).le
      simpa only [div_eq_mul_inv, mul_comm] using h
    have hnonneg : 0 ≤ C * t := mul_nonneg hC ht.le
    nlinarith

variable {G : Type*} [Group G] [PseudoMetricSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G] {m : ℕ}
  (Gamma : Subgroup G) [DiscreteTopology Gamma] [PseudoMetricSpace (G ⧸ Gamma)]

local instance originalTubeMetricTopology : TopologicalSpace (G ⧸ Gamma) :=
  (inferInstance : PseudoMetricSpace (G ⧸ Gamma)).toUniformSpace.toTopologicalSpace

variable [BorelSpace (G ⧸ Gamma)]

/-- Uniform original quotient face-tube mass, with the explicit constant
2mL+1/r. The coordinate probability and the geometric strip cover are
proved internally; no tube-mass premise is supplied. -/
theorem original_quotient_face_tube_linear_bound (coord : G ≃ₜ (Fin m → ℝ))
    (q : G → Fin m → MvPolynomial (Fin m) ℝ)
    (hgroup : ∀ g u i, coord (g * u) i = coord u i + MvPolynomial.aeval (coord u) (q g i))
    (hlow : ∀ g i d, d ∈ (q g i).support → ∀ j ∈ d.support, j.val < i.val)
    (hint : ∀ gamma : Gamma, ∃ z : Fin m → ℤ, coord gamma = fun i => (z i : ℝ))
    (hcover : ∀ z : Fin m → ℤ, ∃ gamma : Gamma, coord gamma = fun i => (z i : ℝ))
    (a : Fin m → ℝ)
    (hdist : ∀ g h : G, dist (QuotientGroup.mk g : G ⧸ Gamma) (QuotientGroup.mk h) =
      originalCosetInfDist Gamma g h)
    (L r : ℝ) (hL : 0 ≤ L) (hr : 0 < r)
    (hmetric : ∀ g ∈ coordinateHalfOpenCell coord a, ∀ v : G, dist g v < r →
      dist (coord g) (coord v) ≤ L * dist g v)
    (mu : Measure (G ⧸ Gamma)) [IsProbabilityMeasure mu] [SMulInvariantMeasure G (G ⧸ Gamma) mu] :
    ∀ t : ℝ, 0 < t → (mu (boundaryTube (originalCellFaceImage Gamma coord a) t)).toReal ≤
      (2 * (m : ℝ) * L + r⁻¹) * t := by
  apply local_probability_bound_global mu _ (2 * (m : ℝ) * L) r (by positivity) hr
  intro t ht htr
  have huniq := triangular_coordinate_cell_correction Gamma coord coord.injective q hgroup hlow hint hcover a
  have h := coordinate_quotient_face_tube_measure_le Gamma coord a huniq hdist L r hL hmetric t htr
  rw [← coordinate_quotient_volume_identification Gamma coord q hgroup hlow hint hcover a mu] at h
  have he := ENNReal.toReal_mono ENNReal.ofReal_ne_top h
  rw [ENNReal.toReal_ofReal (by positivity)] at he
  convert he using 1
  ring

/-- A nonlinear coordinate change can destroy a uniform inverse metric
comparison even on a compact interval. Mere topological compatibility
cannot be substituted for the quantitative local coordinate hypothesis. -/
theorem cubic_coordinate_comparison_obstruction :
    ¬ ∃ L : ℝ, 0 ≤ L ∧ ∀ x ∈ Set.Icc (0 : ℝ) 1, |x| ≤ L * |x ^ 3| := by
  rintro ⟨L, hL, hbound⟩
  let x : ℝ := (L + 1)⁻¹
  have hden : 0 < L + 1 := by linarith
  have hx : 0 < x := inv_pos.mpr hden
  have hprod : (L + 1) * x = 1 := mul_inv_cancel₀ hden.ne'
  have hx1 : x ≤ 1 := by nlinarith [mul_nonneg hL hx.le]
  have hb := hbound x ⟨hx.le, hx1⟩
  rw [abs_of_pos hx, abs_of_nonneg (pow_nonneg hx.le 3)] at hb
  have hbig : 1 ≤ L * x ^ 2 := by
    by_contra h
    have hp := mul_pos hx (sub_pos.mpr (lt_of_not_ge h))
    nlinarith only [hb, hp]
  have hx2 : x ^ 2 ≤ x := by
    simpa only [pow_two, mul_one] using mul_le_mul_of_nonneg_left hx1 hx.le
  have hsmall : L * x ^ 2 ≤ L * x := mul_le_mul_of_nonneg_left hx2 hL
  nlinarith

end GMZP0
