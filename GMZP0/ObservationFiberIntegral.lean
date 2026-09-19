import GMZP0.ObservationFiber
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Topology.Algebra.IsUniformGroup.Basic

/-! Normalized Haar measure and a genuine zero integral on the original
observation fiber. Integrability is proved separately, so no default value
for an undefined Bochner integral is used as mathematical evidence. -/
noncomputable section
open MeasureTheory MeasureTheory.Measure TopologicalSpace
namespace GMZP0
variable {G : Type*} [Group G]

/-- Use the Borel measurable structure of the actual quotient topology. -/
instance observationFiberMeasurableSpace (V : ObservationModule G) (Gamma : Subgroup G) :
    MeasurableSpace (ObservationFiber V Gamma) := borel _

instance observationFiberBorelSpace (V : ObservationModule G) (Gamma : Subgroup G) :
    BorelSpace (ObservationFiber V Gamma) := ⟨rfl⟩

/-- The actual discrete integer-valued subgroup is closed in the original observation space. -/
theorem observation_integer_lattice_closed (V : ObservationModule G) (Gamma : Subgroup G)
    [DiscreteTopology (observationIntegerLattice V Gamma)] :
    IsClosed (observationIntegerFunctions V Gamma : Set V.space) := by
  let : DiscreteTopology (observationIntegerFunctions V Gamma) := by
    change DiscreteTopology (observationIntegerLattice V Gamma)
    infer_instance
  exact AddSubgroup.isClosed_of_discrete

/-- A discrete original lattice makes its actual additive quotient Hausdorff. -/
theorem observationFiber_t2 (V : ObservationModule G) (Gamma : Subgroup G)
    [DiscreteTopology (observationIntegerLattice V Gamma)] : T2Space (ObservationFiber V Gamma) := by
  let : IsClosed (observationIntegerFunctions V Gamma : Set V.space) :=
    observation_integer_lattice_closed V Gamma
  infer_instance

/-- The continuous unit-modulus character is integrable for every finite Borel measure. -/
theorem observationFiberCharacter_integrable (V : ObservationModule G) (Gamma : Subgroup G)
    (gamma : Gamma) (mu : Measure (ObservationFiber V Gamma)) [IsFiniteMeasure mu] :
    Integrable (observationFiberCharacter V Gamma gamma) mu := by
  apply (integrable_const (1 : ℝ)).mono'
    (observationFiberCharacter_continuous V Gamma gamma).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun x => (observationFiberCharacter_norm V Gamma gamma x).le

/-- The original half-constant translation proves zero integral for any invariant measure. -/
theorem observationFiberCharacter_integral_zero (V : ObservationModule G) (Gamma : Subgroup G)
    (h1 : (fun _ : G => (1 : ℝ)) ∈ V.space) (gamma : Gamma)
    (mu : Measure (ObservationFiber V Gamma)) [IsAddLeftInvariant mu] :
    (∫ x, observationFiberCharacter V Gamma gamma x ∂mu) = 0 :=
  integral_eq_zero_of_add_left_eq_neg (observationFiberCharacter_half_translate V Gamma h1 gamma)

/-- Normalized Haar measure on the original compact additive fiber. -/
def observationFiberHaar (V : ObservationModule G) (Gamma : Subgroup G)
    [CompactSpace (ObservationFiber V Gamma)] : Measure (ObservationFiber V Gamma) :=
  addHaarMeasure ⊤
deriving IsAddHaarMeasure

instance observationFiberHaar_probability (V : ObservationModule G) (Gamma : Subgroup G)
    [CompactSpace (ObservationFiber V Gamma)] : IsProbabilityMeasure (observationFiberHaar V Gamma) :=
  IsProbabilityMeasure.mk addHaarMeasure_self

/-- At every base representative, the original quotient observation has a genuine zero fiber mean. -/
theorem quotient_observation_fiber_mean_zero (V : ObservationModule G) {Gamma : Subgroup G}
    [CompactSpace (ObservationFiber V Gamma)]
    (h1 : (fun _ : G => (1 : ℝ)) ∈ V.space) (c : ObservationSection Gamma) (g : G) :
    Integrable (fun x => quotientObservation V c (observationFiberPoint V Gamma g x))
      (observationFiberHaar V Gamma) ∧
    (∫ x, quotientObservation V c (observationFiberPoint V Gamma g x)
      ∂observationFiberHaar V Gamma) = 0 := by
  simp_rw [quotient_observation_fiber]
  exact ⟨observationFiberCharacter_integrable V Gamma _ _,
    observationFiberCharacter_integral_zero V Gamma h1 _ _⟩

/-- A base-dependent scalar cutoff preserves the zero fiber mean of the original observation. -/
theorem quotient_observation_fiber_cutoff_mean_zero (V : ObservationModule G) {Gamma : Subgroup G}
    [CompactSpace (ObservationFiber V Gamma)]
    (h1 : (fun _ : G => (1 : ℝ)) ∈ V.space) (c : ObservationSection Gamma) (g : G) (a : ℂ) :
    Integrable (fun x => a * quotientObservation V c (observationFiberPoint V Gamma g x))
      (observationFiberHaar V Gamma) ∧
    (∫ x, a * quotientObservation V c (observationFiberPoint V Gamma g x)
      ∂observationFiberHaar V Gamma) = 0 := by
  obtain ⟨hint, hz⟩ := quotient_observation_fiber_mean_zero V h1 c g
  refine ⟨hint.const_mul a, ?_⟩
  rw [integral_const_mul, hz, mul_zero]

end GMZP0
