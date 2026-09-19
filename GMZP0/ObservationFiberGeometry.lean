import GMZP0.ObservationFiber
import GMZP0.ObservationGroupCompact

/-! Identification of the actual fibers of H/Gamma_H -> G/Gamma.
The additive observation quotient parametrizes exactly one entire fiber,
with no assumption that either original lattice is normal. -/
noncomputable section
namespace GMZP0
variable {G : Type*} [Group G]

/-- Projection of the original observation quotient to the original base quotient. -/
def observationQuotientBaseProjection (V : ObservationModule G) (Gamma : Subgroup G) :
    (ObservationGroup V ⧸ observationLatticeSubgroup V Gamma) → G ⧸ Gamma :=
  Quotient.lift (fun a => QuotientGroup.mk a.base) (by
    intro a b hab
    apply QuotientGroup.eq.mpr
    exact (QuotientGroup.leftRel_apply.mp hab).1)

/-- Base projection keeps the original base coordinate. -/
@[simp] theorem observationQuotientBaseProjection_mk (V : ObservationModule G) (Gamma : Subgroup G)
    (a : ObservationGroup V) :
    observationQuotientBaseProjection V Gamma (QuotientGroup.mk a) = QuotientGroup.mk a.base := rfl

/-- The actual fiber parametrization projects to its original base coset. -/
theorem observationFiberPoint_projection (V : ObservationModule G) (Gamma : Subgroup G)
    (g : G) (x : ObservationFiber V Gamma) :
    observationQuotientBaseProjection V Gamma (observationFiberPoint V Gamma g x) = QuotientGroup.mk g := by
  induction x using Quotient.inductionOn with
  | h F => rfl

/-- No distinct points of V/V_Z are identified within a fixed original fiber. -/
theorem observationFiberPoint_injective (V : ObservationModule G) (Gamma : Subgroup G) (g : G) :
    Function.Injective (observationFiberPoint V Gamma g) := by
  intro x y h
  induction x using Quotient.inductionOn with
  | h F =>
    induction y using Quotient.inductionOn with
    | h Q =>
      have hlat := (QuotientGroup.eq.mp h).2
      apply QuotientAddGroup.eq.mpr
      have he : ((⟨g, F⟩ : ObservationGroup V)⁻¹ * ⟨g, Q⟩).obs = -F + Q := by
        apply Subtype.ext
        funext u
        simp
      rwa [he] at hlat

/-- Every point over g*Gamma comes from the actual observation fiber, with its required pullback. -/
theorem observationFiberPoint_range (V : ObservationModule G) (Gamma : Subgroup G) (g : G) :
    Set.range (observationFiberPoint V Gamma g) =
      {x | observationQuotientBaseProjection V Gamma x = QuotientGroup.mk g} := by
  ext x
  constructor
  · rintro ⟨z, rfl⟩
    exact observationFiberPoint_projection V Gamma g z
  · intro h
    induction x using Quotient.inductionOn with
    | h a =>
      have hgamma : a.base⁻¹ * g ∈ Gamma := QuotientGroup.eq.mp h
      let gamma : Gamma := ⟨a.base⁻¹ * g, hgamma⟩
      let l : observationLatticeSubgroup V Gamma :=
        ⟨⟨gamma, 0⟩, gamma.property, (observationIntegerFunctions V Gamma).zero_mem⟩
      refine ⟨QuotientAddGroup.mk (observationTranslate V gamma a.obs), ?_⟩
      have he : a * l.val = (⟨g, observationTranslate V gamma a.obs⟩ : ObservationGroup V) := by
        apply ObservationGroup.ext
        · change a.base * (a.base⁻¹ * g) = g
          simp
        · change observationTranslate V gamma a.obs + 0 = _
          exact add_zero _
      change QuotientGroup.mk (⟨g, observationTranslate V gamma a.obs⟩ : ObservationGroup V) = _
      rw [← he]
      exact QuotientGroup.mk_mul_of_mem a l.property

/-- The entire actual fiber parametrization is continuous in the original quotient topologies. -/
theorem observationFiberPoint_continuous [TopologicalSpace G]
    (V : ObservationModule G) (Gamma : Subgroup G) (g : G) :
    Continuous (observationFiberPoint V Gamma g) := by
  apply (QuotientAddGroup.isQuotientMap_mk (observationIntegerFunctions V Gamma)).continuous_iff.mpr
  exact QuotientGroup.continuous_mk.comp
    ((observationPairHomeomorph V).symm.continuous.comp (continuous_const.prodMk continuous_id))

end GMZP0
