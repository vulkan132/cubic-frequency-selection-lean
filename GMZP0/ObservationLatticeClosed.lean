import GMZP0.ObservationTopology
import Mathlib.Topology.Instances.Int

/-! Closedness of the original observation lattice follows directly from
its defining integer values. No discreteness, finite evaluation test or
replacement lattice is used in this closedness argument. -/
noncomputable section
open Set Module
namespace GMZP0
variable {G : Type*} [Group G]

/-- Every actual lattice evaluation is required to be an integer. This
defines a closed subset of the original pointwise function topology. -/
theorem observation_integer_functions_closed_by_values
    (V : ObservationModule G) (Gamma : Subgroup G) :
    IsClosed (observationIntegerFunctions V Gamma : Set V.space) := by
  have he : (observationIntegerFunctions V Gamma : Set V.space) =
      ⋂ gamma : Gamma, (fun P : V.space => P gamma) ⁻¹' Set.range (fun n : ℤ => (n : ℝ)) := by
    ext P
    simp only [Set.mem_iInter, Set.mem_preimage, Set.mem_range]
    change (∀ gamma : Gamma, ∃ n : ℤ, P gamma = n) ↔
      ∀ gamma : Gamma, ∃ n : ℤ, (n : ℝ) = P gamma
    simp only [eq_comm]
  rw [he]
  exact isClosed_iInter fun gamma => Real.isClosedEmbedding_intCast.isClosed_range.preimage
    ((continuous_apply (gamma : G)).comp continuous_subtype_val)

variable [TopologicalSpace G]

/-- Closedness of the original base lattice gives closedness of the
actual product lattice in the original observation group topology. -/
theorem observation_lattice_closed_by_values (V : ObservationModule G) (Gamma : Subgroup G)
    (hclosed : IsClosed (Gamma : Set G)) :
    IsClosed (observationLatticeSubgroup V Gamma : Set (ObservationGroup V)) := by
  change IsClosed ((fun a : ObservationGroup V => a.base) ⁻¹' (Gamma : Set G) ∩
    (fun a : ObservationGroup V => a.obs) ⁻¹' (observationIntegerFunctions V Gamma : Set V.space))
  exact (hclosed.preimage (observation_pair_coordinates_continuous V).fst).inter
    ((observation_integer_functions_closed_by_values V Gamma).preimage
      (observation_pair_coordinates_continuous V).snd)

end GMZP0
