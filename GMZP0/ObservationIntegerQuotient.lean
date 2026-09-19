import GMZP0.ObservationIntegerBasis
import GMZP0.ObservationProper
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.Algebra.Module.Projective

/-! The actual quotient V_Z / (W cap V_Z) embeds in the real quotient V/W.
Its torsion-freeness, finite integer basis and splitting are conclusions.
No bound on the height of the resulting basis is asserted. -/
noncomputable section
open Module
namespace GMZP0
variable {G : Type*} [Group G]

/-- The previously constructed integer intersection, with its canonical integer module structure. -/
def observationIntegerDifferenceModule (V : ObservationModule G) (Gamma : Subgroup G) :
    Submodule ℤ (observationIntegerLattice V Gamma) :=
  (observationIntegerDifference V Gamma).toIntSubmodule

/-- Membership refers to the original real difference space and original integer-valued function. -/
theorem observationIntegerDifferenceModule_mem (V : ObservationModule G) (Gamma : Subgroup G)
    (F : observationIntegerLattice V Gamma) :
    F ∈ observationIntegerDifferenceModule V Gamma ↔ F.val ∈ observationDifferenceSpace V := Iff.rfl

/-- The actual integer quotient, without replacing it by its real span. -/
abbrev ObservationIntegerQuotient (V : ObservationModule G) (Gamma : Subgroup G) :=
  observationIntegerLattice V Gamma ⧸ observationIntegerDifferenceModule V Gamma

/-- The real quotient map restricted to the original integer-valued subgroup. -/
def observationIntegerToRealQuotient (V : ObservationModule G) (Gamma : Subgroup G) :
    observationIntegerLattice V Gamma →ₗ[ℤ] (V.space ⧸ observationDifferenceSpace V) :=
  ((observationDifferenceSpace V).mkQ.restrictScalars ℤ).comp
    (observationIntegerLattice V Gamma).subtype

/-- Its kernel is exactly W cap V_Z, with no extra integer relations. -/
theorem observationIntegerToRealQuotient_ker (V : ObservationModule G) (Gamma : Subgroup G) :
    LinearMap.ker (observationIntegerToRealQuotient V Gamma) =
      observationIntegerDifferenceModule V Gamma := by
  ext F
  change (observationDifferenceSpace V).mkQ F.val = 0 ↔ F.val ∈ observationDifferenceSpace V
  exact Submodule.Quotient.mk_eq_zero _

/-- Passing to the actual integer quotient defines its map into the real quotient. -/
def observationIntegerQuotientEmbedding (V : ObservationModule G) (Gamma : Subgroup G) :
    ObservationIntegerQuotient V Gamma →ₗ[ℤ] (V.space ⧸ observationDifferenceSpace V) :=
  (observationIntegerDifferenceModule V Gamma).liftQ
    (observationIntegerToRealQuotient V Gamma)
    (observationIntegerToRealQuotient_ker V Gamma).ge

/-- The quotient embedding preserves the real class of every actual integer observation. -/
theorem observationIntegerQuotientEmbedding_mk (V : ObservationModule G) (Gamma : Subgroup G)
    (F : observationIntegerLattice V Gamma) :
    observationIntegerQuotientEmbedding V Gamma
      ((observationIntegerDifferenceModule V Gamma).mkQ F) =
      (observationDifferenceSpace V).mkQ F.val := rfl

/-- The map into V/W is injective, so no nonzero integer class has been discarded. -/
theorem observationIntegerQuotientEmbedding_injective (V : ObservationModule G) (Gamma : Subgroup G) :
    Function.Injective (observationIntegerQuotientEmbedding V Gamma) := by
  apply LinearMap.ker_eq_bot.mp
  exact Submodule.ker_liftQ_eq_bot _ _ _ (observationIntegerToRealQuotient_ker V Gamma).le

/-- The actual integer quotient is torsion-free because it embeds into a real vector space. -/
theorem observation_integer_quotient_torsionFree (V : ObservationModule G) (Gamma : Subgroup G) :
    Module.IsTorsionFree ℤ (ObservationIntegerQuotient V Gamma) := by
  let : IsAddTorsionFree (V.space ⧸ observationDifferenceSpace V) :=
    IsAddTorsionFree.of_isTorsionFree ℝ _
  exact (observationIntegerQuotientEmbedding_injective V Gamma).moduleIsTorsionFree
    (observationIntegerQuotientEmbedding V Gamma) (fun n F => map_smul _ n F)

/-- Finite dimension and separation on actual subgroup points prove finite generation over Z. -/
theorem observation_integer_module_finite (V : ObservationModule G) [FiniteDimensional ℝ V.space]
    (Gamma : Subgroup G)
    (hsep : ∀ F : V.space, (∀ gamma : Gamma, F gamma = 0) → F = 0) :
    Module.Finite ℤ (observationIntegerLattice V Gamma) := by
  obtain ⟨d, ⟨b⟩⟩ := observation_integer_basis V Gamma hsep
  exact Module.Finite.of_basis b

/-- The actual quotient has a finite integer basis, rather than a basis merely of its real span. -/
theorem observation_integer_quotient_basis (V : ObservationModule G) (Gamma : Subgroup G)
    [Module.Finite ℤ (observationIntegerLattice V Gamma)] :
    ∃ d : ℕ, Nonempty (Basis (Fin d) ℤ (ObservationIntegerQuotient V Gamma)) := by
  let : Module.IsTorsionFree ℤ (ObservationIntegerQuotient V Gamma) :=
    observation_integer_quotient_torsionFree V Gamma
  obtain ⟨d, b⟩ := Module.basisOfFiniteTypeTorsionFree'
    (R := ℤ) (M := ObservationIntegerQuotient V Gamma)
  exact ⟨d, ⟨b⟩⟩

/-- A genuine integer-linear section chooses all quotient representatives compatibly. -/
theorem observation_integer_quotient_section (V : ObservationModule G) (Gamma : Subgroup G)
    [Module.Finite ℤ (observationIntegerLattice V Gamma)] :
    ∃ s : ObservationIntegerQuotient V Gamma →ₗ[ℤ] observationIntegerLattice V Gamma,
      (observationIntegerDifferenceModule V Gamma).mkQ.comp s = LinearMap.id := by
  let : Module.IsTorsionFree ℤ (ObservationIntegerQuotient V Gamma) :=
    observation_integer_quotient_torsionFree V Gamma
  exact (observationIntegerDifferenceModule V Gamma).mkQ.exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr (observationIntegerDifferenceModule V Gamma).mkQ_surjective)

end GMZP0
