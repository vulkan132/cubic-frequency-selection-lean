import GMZP0.ObservationFiberIntegral
import GMZP0.ObservationFiberGeometry

/-! The actual rational presentation supplies all compact-fiber hypotheses
needed for a normalized Haar probability measure and genuine zero means. -/
noncomputable section
open Module MeasureTheory MeasureTheory.Measure
namespace GMZP0
variable {G sigma iota : Type*} [Group G] [Fintype iota]

/-- Construct normalized Haar on the original fiber from the actual rational presentation.
The conclusion applies to every original section and every original base representative. -/
theorem observation_fiber_haar_of_presentation (V : ObservationModule G) (Gamma : Subgroup G)
    (b : Basis iota ℝ V.space) (coord : G → sigma → ℝ)
    (hint : ∀ gamma : Gamma, ∃ z : sigma → ℤ, coord gamma = fun i => (z i : ℝ))
    (hcover : ∀ z : sigma → ℤ, ∃ gamma : Gamma, coord gamma = fun i => (z i : ℝ))
    (P : iota → MvPolynomial sigma ℚ)
    (hb : ∀ i g, b i g = MvPolynomial.aeval (coord g) (P i))
    (h1 : (fun _ : G => (1 : ℝ)) ∈ V.space) :
    T2Space (ObservationFiber V Gamma) ∧
    ∃ mu : Measure (ObservationFiber V Gamma), IsProbabilityMeasure mu ∧ IsAddHaarMeasure mu ∧
      ∀ (c : ObservationSection Gamma) (g : G) (a : ℂ),
        Integrable (fun x => a * quotientObservation V c (observationFiberPoint V Gamma g x)) mu ∧
        (∫ x, a * quotientObservation V c (observationFiberPoint V Gamma g x) ∂mu) = 0 := by
  let : FiniteDimensional ℝ V.space := b.finiteDimensional_of_finite
  let : DiscreteTopology (observationIntegerLattice V Gamma) :=
    (observation_integer_full_lattice V Gamma b coord hint hcover P hb).1
  have hsep := observation_integer_points_separate V Gamma coord hcover
    (observation_representatives_of_rational_basis V b coord P hb)
  have hfull := observation_integer_span_top V Gamma b coord hint P hb
  obtain ⟨d, ⟨bZ⟩⟩ := observation_integer_basis V Gamma hsep
  let : CompactSpace (ObservationFiber V Gamma) := observation_integer_quotient_compact V Gamma
    bZ (observationRealBasis V Gamma bZ hsep hfull) (observationRealBasis_apply V Gamma bZ hsep hfull)
  refine ⟨observationFiber_t2 V Gamma, observationFiberHaar V Gamma, inferInstance, inferInstance, ?_⟩
  exact fun c g a => quotient_observation_fiber_cutoff_mean_zero V h1 c g a

end GMZP0
