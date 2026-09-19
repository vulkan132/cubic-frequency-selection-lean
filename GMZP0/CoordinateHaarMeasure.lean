import GMZP0.TriangularVolume
import GMZP0.CanonicalCoordinateCell
import GMZP0.CompactQuotientMeasure

/-! The actual coordinate Lebesgue measure is Haar for literal strictly
triangular group laws. The coordinate homeomorphism and original group
law are used explicitly, rather than postulating volume invariance. -/
noncomputable section
open Set MeasureTheory MeasureTheory.Measure
namespace GMZP0
variable {G : Type*} [TopologicalSpace G] [MeasurableSpace G] [BorelSpace G] {m : ℕ}

/-- Push forward actual Euclidean volume by the inverse of the original coordinates. -/
def coordinateVolume (coord : G ≃ₜ (Fin m → ℝ)) : Measure G := volume.map coord.symm

/-- The original coordinate map preserves the explicitly constructed coordinate measure. -/
theorem coordinate_volume_preserving (coord : G ≃ₜ (Fin m → ℝ)) :
    MeasurePreserving coord (coordinateVolume coord) volume := by
  refine ⟨coord.continuous.measurable, ?_⟩
  rw [coordinateVolume, Measure.map_map coord.continuous.measurable coord.symm.continuous.measurable]
  simp only [Function.comp_def, coord.apply_symm_apply]
  exact Measure.map_id

/-- Original compact sets have finite coordinate volume. -/
theorem coordinate_volume_finite_compacts (coord : G ≃ₜ (Fin m → ℝ)) :
    IsFiniteMeasureOnCompacts (coordinateVolume coord) := by
  let : T2Space G := coord.symm.t2Space
  constructor
  intro K hK
  rw [coordinateVolume, Measure.map_apply coord.symm.continuous.measurable hK.measurableSet]
  exact (coord.symm.isClosedEmbedding.isCompact_preimage hK).measure_lt_top

/-- Every nonempty original open set has positive coordinate volume. -/
theorem coordinate_volume_open_positive (coord : G ≃ₜ (Fin m → ℝ)) :
    IsOpenPosMeasure (coordinateVolume coord) :=
  coord.symm.continuous.isOpenPosMeasure_map coord.symm.surjective

variable [Group G]

/-- Literal triangular left multiplication preserves the actual coordinate volume. -/
theorem coordinate_volume_left_invariant (coord : G ≃ₜ (Fin m → ℝ))
    (q : G → Fin m → MvPolynomial (Fin m) ℝ)
    (hcoord : ∀ g u i, coord (g * u) i = coord u i + MvPolynomial.aeval (coord u) (q g i))
    (hlow : ∀ g i d, d ∈ (q g i).support → ∀ j ∈ d.support, j.val < i.val) :
    IsMulLeftInvariant (coordinateVolume coord) := by
  constructor
  intro g
  have hc := coordinate_volume_preserving coord
  have hcinv := hc.symm coord.toMeasurableEquiv
  have ht := triangular_polynomial_volume (q g) (hlow g)
  have hp := hcinv.comp (ht.comp hc)
  change MeasurePreserving
    (coord.symm ∘ (fun (v : Fin m → ℝ) i => v i + MvPolynomial.aeval v (q g i)) ∘ coord)
    (coordinateVolume coord) (coordinateVolume coord) at hp
  have he : (coord.symm ∘ (fun (v : Fin m → ℝ) i => v i + MvPolynomial.aeval v (q g i)) ∘ coord) =
      (fun u => g * u) := by
    funext u
    apply coord.injective
    simp only [Function.comp_apply, coord.apply_symm_apply]
    funext i
    exact (hcoord g u i).symm
  rw [he] at hp
  exact hp.map_eq

/-- The coordinate measure is genuinely Haar under the original triangular laws. -/
theorem coordinate_volume_isHaar (coord : G ≃ₜ (Fin m → ℝ))
    (q : G → Fin m → MvPolynomial (Fin m) ℝ)
    (hcoord : ∀ g u i, coord (g * u) i = coord u i + MvPolynomial.aeval (coord u) (q g i))
    (hlow : ∀ g i d, d ∈ (q g i).support → ∀ j ∈ d.support, j.val < i.val) :
    IsHaarMeasure (coordinateVolume coord) where
  toIsMulLeftInvariant := coordinate_volume_left_invariant coord q hcoord hlow
  toIsFiniteMeasureOnCompacts := coordinate_volume_finite_compacts coord
  toIsOpenPosMeasure := coordinate_volume_open_positive coord

omit [Group G] in
/-- Every actual translated half-open unit coordinate cell has mass one. -/
theorem coordinate_cell_volume_one (coord : G ≃ₜ (Fin m → ℝ)) (a : Fin m → ℝ) :
    coordinateVolume coord (coordinateHalfOpenCell coord a) = 1 := by
  rw [coordinateVolume, Measure.map_apply coord.symm.continuous.measurable
    (coordinate_half_open_cell_measurable coord coord.continuous a)]
  have he : coord.symm ⁻¹' coordinateHalfOpenCell coord a =
      Set.pi Set.univ (fun i => Set.Ico (a i) (a i + 1)) := by
    ext u
    simp [coordinateHalfOpenCell, Set.mem_pi]
  rw [he, Real.volume_pi_Ico]
  simp

end GMZP0
