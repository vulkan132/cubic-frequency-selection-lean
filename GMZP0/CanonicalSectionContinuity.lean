import GMZP0.CanonicalCoordinateCell
import GMZP0.ObservationTopology

/-! The specified original correction is locally constant above interior
representatives. This gives actual local continuity of the original section
and observation, without asserting quantitative Lipschitz or boundary estimates. -/
noncomputable section
open Set Filter Topology
namespace GMZP0
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- Inside a strict domain, the actual original lattice correction is locally constant. -/
theorem original_correction_locally_constant (Gamma : Subgroup G) (S : Set G)
    (hunique : ∀ g : G, ∃! gamma : Gamma, g * gamma ∈ S)
    (c : ObservationSection Gamma) (hc : Set.range c.representative ⊆ S)
    (g : G) (hg : c.representative g ∈ interior S) :
    (fun u => observationCorrection c u) =ᶠ[𝓝 g] (fun _ => observationCorrection c g) := by
  have hg' : g * observationCorrection c g ∈ interior S := by
    rwa [observation_representative_eq]
  have hnear := (continuous_mul_const (observationCorrection c g : G)).continuousAt.eventually
    (isOpen_interior.mem_nhds hg')
  filter_upwards [hnear] with u hu
  apply (hunique u).unique
  · rw [observation_representative_eq]
    exact hc ⟨u, rfl⟩
  · exact interior_subset hu

/-- The specified original section is continuous above interior representatives of its strict domain. -/
theorem original_section_continuousAt_interior (Gamma : Subgroup G) (S : Set G)
    (hunique : ∀ g : G, ∃! gamma : Gamma, g * gamma ∈ S)
    (c : ObservationSection Gamma) (hc : Set.range c.representative ⊆ S)
    (g : G) (hg : c.representative g ∈ interior S) : ContinuousAt c.representative g := by
  apply (continuous_mul_const (observationCorrection c g : G)).continuousAt.congr
  filter_upwards [original_correction_locally_constant Gamma S hunique c hc g hg] with u hu
  rw [← observation_representative_eq c u, hu]

omit [Group G] [IsTopologicalGroup G] in
/-- Strict coordinate inequalities put the original representative in the interior of its actual cell. -/
theorem coordinate_cell_interior_of_strict {m : ℕ} (coord : G → Fin m → ℝ)
    (hc : Continuous coord) (a : Fin m → ℝ) (g : G)
    (hg : ∀ i, coord g i ∈ Set.Ioo (a i) (a i + 1)) :
    g ∈ interior (coordinateHalfOpenCell coord a) := by
  have hopen : IsOpen {u : G | ∀ i, coord u i ∈ Set.Ioo (a i) (a i + 1)} := by
    convert isOpen_iInter_of_finite (fun i : Fin m =>
      (isOpen_Ioo : IsOpen (Set.Ioo (a i) (a i + 1))).preimage ((continuous_apply i).comp hc)) using 1
    ext u
    simp
  have hsub : {u : G | ∀ i, coord u i ∈ Set.Ioo (a i) (a i + 1)} ⊆ coordinateHalfOpenCell coord a := by
    intro u hu i
    exact ⟨(hu i).1.le, (hu i).2⟩
  exact (interior_maximal hsub hopen) hg

/-- The specified canonical section is locally continuous away from its actual coordinate faces. -/
theorem specified_coordinate_section_continuousAt (Gamma : Subgroup G) {m : ℕ}
    (coord : G → Fin m → ℝ) (hcont : Continuous coord) (hinj : Function.Injective coord)
    (q : G → Fin m → MvPolynomial (Fin m) ℝ)
    (hcoord : ∀ g u i, coord (g * u) i = coord u i + MvPolynomial.aeval (coord u) (q g i))
    (hlow : ∀ g i d, d ∈ (q g i).support → ∀ j ∈ d.support, j.val < i.val)
    (hint : ∀ gamma : Gamma, ∃ z : Fin m → ℤ, coord gamma = fun i => (z i : ℝ))
    (hcover : ∀ z : Fin m → ℤ, ∃ gamma : Gamma, coord gamma = fun i => (z i : ℝ))
    (a : Fin m → ℝ) (c : ObservationSection Gamma)
    (hc : Set.range c.representative ⊆ coordinateHalfOpenCell coord a) (g : G)
    (hg : ∀ i, coord (c.representative g) i ∈ Set.Ioo (a i) (a i + 1)) :
    ContinuousAt c.representative g :=
  original_section_continuousAt_interior Gamma _
    (triangular_coordinate_cell_correction Gamma coord hinj q hcoord hlow hint hcover a) c hc g
    (coordinate_cell_interior_of_strict coord hcont a _ hg)

/-- The actual original real phase is locally continuous wherever the chosen base representative is interior. -/
theorem original_observation_phase_continuousAt (V : ObservationModule G) (Gamma : Subgroup G)
    (S : Set G) (hunique : ∀ g : G, ∃! gamma : Gamma, g * gamma ∈ S)
    (c : ObservationSection Gamma) (hc : Set.range c.representative ⊆ S)
    (a : ObservationGroup V) (ha : c.representative a.base ∈ interior S) :
    ContinuousAt (observationRealPhase V c) a := by
  have hbase : ContinuousAt (fun b : ObservationGroup V => b.base) a :=
    (observation_pair_coordinates_continuous V).fst.continuousAt
  have hnear := (original_correction_locally_constant Gamma S hunique c hc a.base ha).comp_tendsto hbase
  have heval : Continuous (fun b : ObservationGroup V => b.obs (observationCorrection c a.base)) :=
    (continuous_apply (observationCorrection c a.base : G)).comp
      (continuous_subtype_val.comp (observation_pair_coordinates_continuous V).snd)
  apply heval.continuousAt.congr
  filter_upwards [hnear] with b hb
  change observationCorrection c b.base = observationCorrection c a.base at hb
  simp only [observationRealPhase, hb]

/-- The pullback of the original quotient observation is locally continuous off the actual base faces. -/
theorem original_quotient_observation_pullback_continuousAt (V : ObservationModule G) (Gamma : Subgroup G)
    (S : Set G) (hunique : ∀ g : G, ∃! gamma : Gamma, g * gamma ∈ S)
    (c : ObservationSection Gamma) (hc : Set.range c.representative ⊆ S)
    (a : ObservationGroup V) (ha : c.representative a.base ∈ interior S) :
    ContinuousAt (fun b : ObservationGroup V => quotientObservation V c (QuotientGroup.mk b)) a := by
  change ContinuousAt (fun b => circleCharacter (observationRealPhase V c b : Frequency)) a
  exact (continuous_subtype_val.comp AddCircle.continuous_toCircle).continuousAt.comp
    (QuotientAddGroup.continuous_mk.continuousAt.comp
      (original_observation_phase_continuousAt V Gamma S hunique c hc a ha))

end GMZP0
