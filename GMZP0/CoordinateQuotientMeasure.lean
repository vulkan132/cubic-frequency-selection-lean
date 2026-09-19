import GMZP0.CoordinateHaarMeasure
import GMZP0.QuotientProbabilityUnique

/-! Identify the original quotient probability with the pushforward of
actual coordinate volume on the proved strict half-open unit cell. -/
noncomputable section
open Set MeasureTheory MeasureTheory.Measure TopologicalSpace
namespace GMZP0
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G] {m : ℕ}

/-- The actual quotient map applied to original coordinate volume on its original cell. -/
def coordinateQuotientVolume (Gamma : Subgroup G) (coord : G ≃ₜ (Fin m → ℝ)) (a : Fin m → ℝ) :
    Measure (G ⧸ Gamma) :=
  ((coordinateVolume coord).restrict (coordinateHalfOpenCell coord a)).map QuotientGroup.mk

omit [IsTopologicalGroup G] in
/-- Unit coordinate volume gives an actual quotient probability without a normalization factor. -/
theorem coordinate_quotient_volume_probability (Gamma : Subgroup G)
    (coord : G ≃ₜ (Fin m → ℝ)) (a : Fin m → ℝ) :
    IsProbabilityMeasure (coordinateQuotientVolume Gamma coord a) := by
  constructor
  simp only [coordinateQuotientVolume, Measure.map_apply QuotientGroup.measurable_coe MeasurableSet.univ,
    Set.preimage_univ, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
    coordinate_cell_volume_one]

/-- Literal original triangular laws and the full original integer grid make
this precise coordinate quotient probability invariant under the whole group. -/
theorem coordinate_quotient_volume_invariant (Gamma : Subgroup G) [DiscreteTopology Gamma]
    (coord : G ≃ₜ (Fin m → ℝ))
    (q : G → Fin m → MvPolynomial (Fin m) ℝ)
    (hcoord : ∀ g u i, coord (g * u) i = coord u i + MvPolynomial.aeval (coord u) (q g i))
    (hlow : ∀ g i d, d ∈ (q g i).support → ∀ j ∈ d.support, j.val < i.val)
    (hint : ∀ gamma : Gamma, ∃ z : Fin m → ℤ, coord gamma = fun i => (z i : ℝ))
    (hcover : ∀ z : Fin m → ℤ, ∃ gamma : Gamma, coord gamma = fun i => (z i : ℝ))
    (a : Fin m → ℝ) :
    SMulInvariantMeasure G (G ⧸ Gamma) (coordinateQuotientVolume Gamma coord a) := by
  let : PolishSpace G := coord.isClosedEmbedding.polishSpace
  let : LocallyCompactSpace G := coord.isOpenEmbedding.locallyCompactSpace
  let : Countable Gamma := TopologicalSpace.separableSpace_iff_countable.mp inferInstance
  let : IsClosed (Gamma : Set G) := Subgroup.isClosed_of_discrete
  let : T2Space (G ⧸ Gamma) := inferInstance
  let D := coordinateHalfOpenCell coord a
  have hD := coordinate_half_open_cell_measurable coord coord.continuous a
  have huniq := triangular_coordinate_cell_correction Gamma coord coord.injective q hcoord hlow hint hcover a
  let : CompactSpace (G ⧸ Gamma) := quotient_compact_of_strict_cell Gamma D
    (coordinate_half_open_cell_compact_closure coord a) (fun g => (huniq g).exists)
  let nu := coordinateVolume coord
  let : IsHaarMeasure nu := coordinate_volume_isHaar coord q hcoord hlow
  let : IsMulRightInvariant nu := cocompact_lattice_haar_right_invariant Gamma nu
  have hfund := strict_right_domain_fundamental Gamma nu D hD huniq
  let : HasFundamentalDomain Gamma.op G nu := ⟨D, hfund⟩
  let : QuotientMeasureEqMeasurePreimage nu (coordinateQuotientVolume Gamma coord a) :=
    hfund.quotientMeasureEqMeasurePreimage_quotientMeasure
  exact QuotientMeasureEqMeasurePreimage.smulInvariantMeasure_quotient nu

/-- Every specified original invariant probability is exactly the coordinate-cell
pushforward. Coordinate-volume invariance is proved rather than assumed. -/
theorem coordinate_quotient_volume_identification (Gamma : Subgroup G) [DiscreteTopology Gamma]
    (coord : G ≃ₜ (Fin m → ℝ))
    (q : G → Fin m → MvPolynomial (Fin m) ℝ)
    (hcoord : ∀ g u i, coord (g * u) i = coord u i + MvPolynomial.aeval (coord u) (q g i))
    (hlow : ∀ g i d, d ∈ (q g i).support → ∀ j ∈ d.support, j.val < i.val)
    (hint : ∀ gamma : Gamma, ∃ z : Fin m → ℤ, coord gamma = fun i => (z i : ℝ))
    (hcover : ∀ z : Fin m → ℤ, ∃ gamma : Gamma, coord gamma = fun i => (z i : ℝ))
    (a : Fin m → ℝ) (mu : Measure (G ⧸ Gamma))
    [IsProbabilityMeasure mu] [SMulInvariantMeasure G (G ⧸ Gamma) mu] :
    mu = coordinateQuotientVolume Gamma coord a := by
  let : PolishSpace G := coord.isClosedEmbedding.polishSpace
  let : LocallyCompactSpace G := coord.isOpenEmbedding.locallyCompactSpace
  have huniq := triangular_coordinate_cell_correction Gamma coord coord.injective q hcoord hlow hint hcover a
  let : CompactSpace (G ⧸ Gamma) := quotient_compact_of_strict_cell Gamma _
    (coordinate_half_open_cell_compact_closure coord a) (fun g => (huniq g).exists)
  let := coordinate_quotient_volume_probability Gamma coord a
  let := coordinate_quotient_volume_invariant Gamma coord q hcoord hlow hint hcover a
  exact compact_quotient_invariant_probability_unique Gamma mu _

omit [IsTopologicalGroup G] in
/-- Coordinate coverings of actual quotient events give bounds for the exact
coordinate-cell pushforward, with no surrogate measure or orbit deletion. -/
theorem coordinate_quotient_event_bound (Gamma : Subgroup G)
    (coord : G ≃ₜ (Fin m → ℝ)) (a : Fin m → ℝ)
    (A : Set (G ⧸ Gamma)) (hA : MeasurableSet A) (B : Set (Fin m → ℝ)) (hB : MeasurableSet B)
    (hsub : ∀ g, g ∈ coordinateHalfOpenCell coord a → QuotientGroup.mk g ∈ A → coord g ∈ B) :
    coordinateQuotientVolume Gamma coord a A ≤ volume B := by
  rw [coordinateQuotientVolume, Measure.map_apply QuotientGroup.measurable_coe hA,
    Measure.restrict_apply (hA.preimage QuotientGroup.measurable_coe)]
  calc
    coordinateVolume coord ((QuotientGroup.mk ⁻¹' A) ∩ coordinateHalfOpenCell coord a) ≤
        coordinateVolume coord (coord ⁻¹' B) := measure_mono (fun g hg => hsub g hg.2 hg.1)
    _ = volume B := (coordinate_volume_preserving coord).measure_preimage hB.nullMeasurableSet

end GMZP0
