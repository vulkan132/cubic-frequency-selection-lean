import GMZP0.ObservationIntegerQuotient
import Mathlib.LinearAlgebra.Basis.Prod

/-! A section of the actual integer quotient gives a direct decomposition
and an integer basis adapted to W cap V_Z. All representatives remain in V_Z.
The construction is qualitative; bounds are a separate obligation. -/
noncomputable section
open Module
namespace GMZP0
variable {G : Type*} [Group G]

/-- Subtracting a section representative leaves exactly an element of the integer intersection. -/
theorem observation_integer_section_remainder (V : ObservationModule G) (Gamma : Subgroup G)
    (s : ObservationIntegerQuotient V Gamma →ₗ[ℤ] observationIntegerLattice V Gamma)
    (hs : (observationIntegerDifferenceModule V Gamma).mkQ.comp s = LinearMap.id)
    (F : observationIntegerLattice V Gamma) :
    F - s ((observationIntegerDifferenceModule V Gamma).mkQ F) ∈
      observationIntegerDifferenceModule V Gamma := by
  apply (Submodule.Quotient.mk_eq_zero _).mp
  change (observationIntegerDifferenceModule V Gamma).mkQ
    (F - s ((observationIntegerDifferenceModule V Gamma).mkQ F)) = 0
  rw [map_sub]
  have he := LinearMap.congr_fun hs ((observationIntegerDifferenceModule V Gamma).mkQ F)
  change (observationIntegerDifferenceModule V Gamma).mkQ
    (s ((observationIntegerDifferenceModule V Gamma).mkQ F)) =
    (observationIntegerDifferenceModule V Gamma).mkQ F at he
  rw [he, sub_self]

/-- The actual section gives an integer-linear product decomposition of the original V_Z. -/
def observationIntegerSplitEquiv (V : ObservationModule G) (Gamma : Subgroup G)
    (s : ObservationIntegerQuotient V Gamma →ₗ[ℤ] observationIntegerLattice V Gamma)
    (hs : (observationIntegerDifferenceModule V Gamma).mkQ.comp s = LinearMap.id) :
    (observationIntegerDifferenceModule V Gamma × ObservationIntegerQuotient V Gamma) ≃ₗ[ℤ]
      observationIntegerLattice V Gamma := by
  let I := observationIntegerDifferenceModule V Gamma
  let f : (I × ObservationIntegerQuotient V Gamma) →ₗ[ℤ] observationIntegerLattice V Gamma :=
    I.subtype.coprod s
  have hsq (q : ObservationIntegerQuotient V Gamma) : I.mkQ (s q) = q :=
    LinearMap.congr_fun hs q
  apply LinearEquiv.ofBijective f
  constructor
  · apply LinearMap.ker_eq_bot.mp
    apply eq_bot_iff.mpr
    intro x hx
    change f x = 0 at hx
    have hq := congrArg I.mkQ hx
    have hi : I.mkQ x.1.val = 0 := (Submodule.Quotient.mk_eq_zero _).mpr x.1.property
    change I.mkQ (x.1.val + s x.2) = I.mkQ 0 at hq
    rw [map_add, map_zero, hi, hsq, zero_add] at hq
    change x = 0
    apply Prod.ext
    · apply Subtype.ext
      change x.1.val = 0
      change x.1.val + s x.2 = 0 at hx
      simpa only [hq, map_zero, add_zero] using hx
    · exact hq
  · intro F
    refine ⟨(⟨F - s (I.mkQ F), observation_integer_section_remainder V Gamma s hs F⟩,
      I.mkQ F), ?_⟩
    change F - s (I.mkQ F) + s (I.mkQ F) = F
    exact sub_add_cancel _ _

/-- The splitting acts by the original inclusion plus the chosen actual representative. -/
theorem observationIntegerSplitEquiv_apply (V : ObservationModule G) (Gamma : Subgroup G)
    (s : ObservationIntegerQuotient V Gamma →ₗ[ℤ] observationIntegerLattice V Gamma)
    (hs : (observationIntegerDifferenceModule V Gamma).mkQ.comp s = LinearMap.id)
    (x : observationIntegerDifferenceModule V Gamma × ObservationIntegerQuotient V Gamma) :
    observationIntegerSplitEquiv V Gamma s hs x = x.1.val + s x.2 := rfl

/-- Both parts have finite integer bases, and their actual lifts form an adapted basis of V_Z. -/
theorem observation_integer_adapted_basis (V : ObservationModule G) (Gamma : Subgroup G)
    [Module.Finite ℤ (observationIntegerLattice V Gamma)] :
    ∃ p q : ℕ, ∃ bW : Basis (Fin p) ℤ (observationIntegerDifferenceModule V Gamma),
      ∃ bQ : Basis (Fin q) ℤ (ObservationIntegerQuotient V Gamma),
      ∃ b : Basis (Fin p ⊕ Fin q) ℤ (observationIntegerLattice V Gamma),
        (∀ i, b (Sum.inl i) = (bW i).val) ∧
        (∀ j, (observationIntegerDifferenceModule V Gamma).mkQ (b (Sum.inr j)) = bQ j) := by
  let : IsAddTorsionFree V.space := IsAddTorsionFree.of_isTorsionFree ℝ _
  obtain ⟨p, bW⟩ := Module.basisOfFiniteTypeTorsionFree'
    (R := ℤ) (M := observationIntegerDifferenceModule V Gamma)
  obtain ⟨q, ⟨bQ⟩⟩ := observation_integer_quotient_basis V Gamma
  obtain ⟨s, hs⟩ := observation_integer_quotient_section V Gamma
  let e := observationIntegerSplitEquiv V Gamma s hs
  refine ⟨p, q, bW, bQ, (bW.prod bQ).map e, ?_, ?_⟩
  · intro i
    simp only [Basis.map_apply, e, observationIntegerSplitEquiv_apply,
      Basis.prod_apply_inl_fst, Basis.prod_apply_inl_snd, map_zero, add_zero]
  · intro j
    simp only [Basis.map_apply, e, observationIntegerSplitEquiv_apply,
      Basis.prod_apply_inr_fst, Basis.prod_apply_inr_snd, Submodule.coe_zero, zero_add]
    exact LinearMap.congr_fun hs (bQ j)

/-- Quotient coefficients reconstruct every actual integer observation modulo the actual W. -/
theorem observation_integer_quotient_reconstruction (V : ObservationModule G) (Gamma : Subgroup G)
    {iota : Type*} [Fintype iota] (bQ : Basis iota ℤ (ObservationIntegerQuotient V Gamma))
    (B : iota → observationIntegerLattice V Gamma)
    (hB : ∀ i, (observationIntegerDifferenceModule V Gamma).mkQ (B i) = bQ i)
    (F : observationIntegerLattice V Gamma) :
    F - ∑ i, bQ.repr ((observationIntegerDifferenceModule V Gamma).mkQ F) i • B i ∈
      observationIntegerDifferenceModule V Gamma := by
  apply (Submodule.Quotient.mk_eq_zero _).mp
  change (observationIntegerDifferenceModule V Gamma).mkQ
    (F - ∑ i, bQ.repr ((observationIntegerDifferenceModule V Gamma).mkQ F) i • B i) = 0
  rw [map_sub, map_sum]
  simp_rw [map_smul, hB]
  rw [bQ.sum_repr, sub_self]

end GMZP0
