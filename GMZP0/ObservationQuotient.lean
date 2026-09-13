import GMZP0.ObservationGroup
import GMZP0.CircleCharacter

/-! The fixed observation on the actual coset quotient. All lattice corrections
are retained; no coordinatewise fractional-part replacement is made. -/
noncomputable section
namespace GMZP0
variable {G : Type*} [Group G]

/-- Algebraic data of a chosen representative of each coset g Gamma.
Boundedness and regularity of the canonical domain are not asserted here. -/
structure ObservationSection (Gamma : Subgroup G) where
  representative : G → G
  right_invariant : ∀ (g : G) (gamma : Gamma), representative (g * gamma) = representative g
  correction_mem : ∀ g, g⁻¹ * representative g ∈ Gamma

/-- The unique right correction belonging to the chosen section. -/
def observationCorrection {Gamma : Subgroup G} (c : ObservationSection Gamma) (g : G) : Gamma :=
  ⟨g⁻¹ * c.representative g, c.correction_mem g⟩

/-- The representative is the original element times its actual right lattice correction. -/
theorem observation_representative_eq {Gamma : Subgroup G} (c : ObservationSection Gamma) (g : G) :
    g * observationCorrection c g = c.representative g := by
  simp [observationCorrection]

/-- Changing a representative on the right changes its correction on the left. -/
theorem observation_correction_mul {Gamma : Subgroup G} (c : ObservationSection Gamma)
    (g : G) (gamma : Gamma) :
    observationCorrection c (g * gamma) = gamma⁻¹ * observationCorrection c g := by
  apply Subtype.ext
  simp [observationCorrection, c.right_invariant, mul_assoc]

/-- The paper's real phase before passing to the circle. -/
def observationRealPhase (V : ObservationModule G) {Gamma : Subgroup G}
    (c : ObservationSection Gamma) (a : ObservationGroup V) : ℝ :=
  a.obs (observationCorrection c a.base)

/-- The exact change in phase is the integral fiber term at an actual lattice element. -/
theorem observation_phase_lattice_change (V : ObservationModule G) {Gamma : Subgroup G}
    (c : ObservationSection Gamma) (a : ObservationGroup V)
    (l : observationLatticeSubgroup V Gamma) :
    observationRealPhase V c (a * l) = observationRealPhase V c a +
      l.val.obs ((⟨l.val.base, l.property.1⟩ : Gamma)⁻¹ * observationCorrection c a.base) := by
  unfold observationRealPhase
  rw [observation_mul_base]
  change (a * l.val).obs (observationCorrection c (a.base *
    (⟨l.val.base, l.property.1⟩ : Gamma))) = _
  rw [observation_correction_mul]
  simp

/-- The observation phase is unchanged modulo one by every element of Gamma_H. -/
theorem observation_circle_lattice_invariant (V : ObservationModule G) {Gamma : Subgroup G}
    (c : ObservationSection Gamma) (a : ObservationGroup V)
    (l : observationLatticeSubgroup V Gamma) :
    (observationRealPhase V c (a * l) : Frequency) = (observationRealPhase V c a : Frequency) := by
  rw [observation_phase_lattice_change]
  obtain ⟨n, hn⟩ := l.property.2
    ((⟨l.val.base, l.property.1⟩ : Gamma)⁻¹ * observationCorrection c a.base)
  have he := congrArg (fun t : ℝ => ((observationRealPhase V c a + t : ℝ) : Frequency)) hn
  exact he.trans (by simp)

/-- A well-defined fixed observation on H/Gamma_H, without assuming Gamma_H normal. -/
def quotientObservation (V : ObservationModule G) {Gamma : Subgroup G}
    (c : ObservationSection Gamma) : (ObservationGroup V ⧸ observationLatticeSubgroup V Gamma) → ℂ :=
  Quotient.lift (fun a => circleCharacter (observationRealPhase V c a : Frequency)) (by
    intro a b hab
    have hl : a⁻¹ * b ∈ observationLatticeSubgroup V Gamma :=
      QuotientGroup.leftRel_apply.mp hab
    have he := observation_circle_lattice_invariant V c a ⟨a⁻¹ * b, hl⟩
    simpa using (congrArg circleCharacter he).symm)

/-- The quotient observation evaluates to the original formula on every representative. -/
theorem quotient_observation_mk (V : ObservationModule G) {Gamma : Subgroup G}
    (c : ObservationSection Gamma) (a : ObservationGroup V) :
    quotientObservation V c (Quotient.mk _ a) =
      circleCharacter (observationRealPhase V c a : Frequency) := rfl

/-- At a canonical representative the observation is evaluation at the identity. -/
theorem observation_at_canonical (V : ObservationModule G) {Gamma : Subgroup G}
    (c : ObservationSection Gamma) (a : ObservationGroup V)
    (ha : c.representative a.base = a.base) : observationRealPhase V c a = a.obs 1 := by
  simp [observationRealPhase, observationCorrection, ha]

/-- The fixed observation always has modulus one, including on section boundaries. -/
theorem quotient_observation_norm (V : ObservationModule G) {Gamma : Subgroup G}
    (c : ObservationSection Gamma) (a : ObservationGroup V ⧸ observationLatticeSubgroup V Gamma) :
    ‖quotientObservation V c a‖ = 1 := by
  induction a using Quotient.inductionOn with
  | h a => exact Circle.norm_coe _

end GMZP0
