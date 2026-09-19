import GMZP0.CoordinateQuotientMeasure
import GMZP0.CoordinateBoundaryStrips
import GMZP0.CanonicalObservationSection

/-! Quantitative coordinate-strip mass for the specified original section
under the specified original invariant probability. Original quotient-metric
tubes require a further geometric covering argument. -/
noncomputable section
open Set MeasureTheory MeasureTheory.Measure
namespace GMZP0
variable {G : Type*} [Group G]

/-- Any specified section in the strict original domain fixes every point
of that domain, not merely almost every point. -/
theorem specified_section_fixes_strict_domain (Gamma : Subgroup G) (D : Set G)
    (huniq : ∀ g : G, ∃! gamma : Gamma, g * gamma ∈ D)
    (c : ObservationSection Gamma) (hc : Set.range c.representative ⊆ D)
    (g : G) (hg : g ∈ D) : c.representative g = g := by
  have hmem : g * observationCorrection c g ∈ D := by
    rw [observation_representative_eq]
    exact hc ⟨g, rfl⟩
  have he : observationCorrection c g = 1 := (huniq g).unique hmem (by simpa using hg)
  rw [← observation_representative_eq c g, he]
  simp

variable [TopologicalSpace G] [MeasurableSpace G] [BorelSpace G] {m : ℕ}

/-- An actual quotient event covered by original coordinate strips has the
explicit 2mt bound under the exact coordinate quotient measure. -/
theorem coordinate_quotient_strip_event_bound (Gamma : Subgroup G)
    (coord : G ≃ₜ (Fin m → ℝ)) (a : Fin m → ℝ) (t : ℝ)
    (A : Set (G ⧸ Gamma)) (hA : MeasurableSet A)
    (hsub : ∀ g, g ∈ coordinateHalfOpenCell coord a → QuotientGroup.mk g ∈ A →
      coord g ∈ coordinateBoundaryStrip a t) :
    coordinateQuotientVolume Gamma coord a A ≤ ENNReal.ofReal (2 * (m : ℝ) * t) :=
  (coordinate_quotient_event_bound Gamma coord a A hA _
    (coordinate_boundary_strip_measurable a t) hsub).trans (coordinate_boundary_strip_volume a t)

variable [IsTopologicalGroup G]

/-- The actual chosen representatives lie in coordinate boundary strips
with probability at most 2mt. The original invariant probability is
identified internally with the coordinate-cell measure; it is not replaced. -/
theorem original_section_boundary_strip_mass (Gamma : Subgroup G) [DiscreteTopology Gamma]
    (coord : G ≃ₜ (Fin m → ℝ))
    (q : G → Fin m → MvPolynomial (Fin m) ℝ)
    (hcoord : ∀ g u i, coord (g * u) i = coord u i + MvPolynomial.aeval (coord u) (q g i))
    (hlow : ∀ g i d, d ∈ (q g i).support → ∀ j ∈ d.support, j.val < i.val)
    (hint : ∀ gamma : Gamma, ∃ z : Fin m → ℤ, coord gamma = fun i => (z i : ℝ))
    (hcover : ∀ z : Fin m → ℤ, ∃ gamma : Gamma, coord gamma = fun i => (z i : ℝ))
    (a : Fin m → ℝ) (mu : Measure (G ⧸ Gamma))
    [IsProbabilityMeasure mu] [SMulInvariantMeasure G (G ⧸ Gamma) mu]
    (c : ObservationSection Gamma) (hc : Set.range c.representative ⊆ coordinateHalfOpenCell coord a)
    (t : ℝ) :
    mu {x | coord (observationQuotientSection c x) ∈ coordinateBoundaryStrip a t} ≤
      ENNReal.ofReal (2 * (m : ℝ) * t) := by
  let : PolishSpace G := coord.isClosedEmbedding.polishSpace
  have hcm := specified_canonical_coordinate_section_measurable Gamma coord q hcoord hlow hint hcover a c hc
  have hsm := observationQuotientSection_measurable c hcm
  have hA : MeasurableSet {x | coord (observationQuotientSection c x) ∈ coordinateBoundaryStrip a t} :=
    (coordinate_boundary_strip_measurable a t).preimage (coord.continuous.measurable.comp hsm)
  have huniq := triangular_coordinate_cell_correction Gamma coord coord.injective q hcoord hlow hint hcover a
  rw [coordinate_quotient_volume_identification Gamma coord q hcoord hlow hint hcover a mu]
  apply coordinate_quotient_strip_event_bound Gamma coord a t _ hA
  intro g hg hAg
  change coord (observationQuotientSection c (QuotientGroup.mk g)) ∈ coordinateBoundaryStrip a t at hAg
  rwa [observationQuotientSection_mk, specified_section_fixes_strict_domain Gamma _ huniq c hc g hg] at hAg

end GMZP0
