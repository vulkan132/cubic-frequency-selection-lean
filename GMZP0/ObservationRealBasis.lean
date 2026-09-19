import GMZP0.ObservationIntegerSplitting
import Mathlib.LinearAlgebra.LinearIndependent.BaseChange

/-! An integer basis of the actual observation lattice is a real basis of V.
Real independence is proved through actual integer evaluations, not inferred
from integer independence alone. -/
noncomputable section
open Module
namespace GMZP0
variable {G iota : Type*} [Group G]

/-- Finite actual subgroup evaluation, regarded as a real-linear map. -/
def observationFiniteRealEvaluation (V : ObservationModule G) (Gamma : Subgroup G)
    {n : ℕ} (gamma : Fin n → Gamma) : V.space →ₗ[ℝ] (Fin n → ℝ) :=
  LinearMap.pi fun i => observationEvaluation V (gamma i)

/-- On the actual integer subgroup, this real map is exactly the cast of integer evaluation. -/
theorem observationFiniteRealEvaluation_cast (V : ObservationModule G) (Gamma : Subgroup G)
    {n : ℕ} (gamma : Fin n → Gamma) (F : observationIntegerLattice V Gamma) (i : Fin n) :
    observationFiniteRealEvaluation V Gamma gamma F.val i =
      (observationIntegerEvaluation V Gamma gamma F i : ℝ) :=
  (observationIntegerEvaluation_cast V Gamma gamma F i).symm

/-- Integer independence of genuine integer-valued observations implies real independence
when a finite family of actual subgroup evaluations separates V. -/
theorem observation_integer_family_real_independent (V : ObservationModule G) (Gamma : Subgroup G)
    {n : ℕ} (gamma : Fin n → Gamma)
    (hsep : ∀ F : V.space, (∀ i, F (gamma i) = 0) → F = 0)
    (B : iota → observationIntegerLattice V Gamma) (hB : LinearIndependent ℤ B) :
    LinearIndependent ℝ (fun i => (B i).val) := by
  have hz := hB.map' (observationIntegerEvaluation V Gamma gamma)
    (LinearMap.ker_eq_bot.mpr (observationIntegerEvaluation_injective V Gamma gamma hsep))
  have hr := (linearIndependent_algebraMap_comp_iff (R := ℤ) (S := ℝ)).mpr hz
  have he : (fun i => algebraMap ℤ ℝ ∘
      ((observationIntegerEvaluation V Gamma gamma) ∘ B) i) =
      (observationFiniteRealEvaluation V Gamma gamma) ∘ (fun i => (B i).val) := by
    funext i j
    exact (observationFiniteRealEvaluation_cast V Gamma gamma (B i) j).symm
  rw [he] at hr
  exact hr.of_comp

/-- A finite integer basis spans over the reals exactly the real span of the original lattice. -/
theorem observation_integer_basis_real_span [Fintype iota]
    (V : ObservationModule G) (Gamma : Subgroup G)
    (b : Basis iota ℤ (observationIntegerLattice V Gamma)) :
    Submodule.span ℝ (Set.range (fun i => (b i).val)) =
      Submodule.span ℝ (observationIntegerLattice V Gamma : Set V.space) := by
  classical
  apply le_antisymm
  · apply Submodule.span_mono
    rintro _ ⟨i, rfl⟩
    exact (b i).property
  · apply Submodule.span_le.mpr
    intro F hF
    let L := observationIntegerLattice V Gamma
    let S := Submodule.span ℝ (Set.range (fun i => (b i).val))
    have he := congrArg L.subtype (b.sum_repr ⟨F, hF⟩)
    simp only [map_sum, map_smul, Submodule.subtype_apply] at he
    rw [← he]
    exact S.sum_mem fun i _ => (S.restrictScalars ℤ).smul_mem _
      (Submodule.subset_span ⟨i, rfl⟩)

/-- The original integer basis is a real basis once the original lattice has full real span. -/
def observationRealBasis [Fintype iota] (V : ObservationModule G) [FiniteDimensional ℝ V.space]
    (Gamma : Subgroup G) (b : Basis iota ℤ (observationIntegerLattice V Gamma))
    (hsep : ∀ F : V.space, (∀ gamma : Gamma, F gamma = 0) → F = 0)
    (hfull : Submodule.span ℝ (observationIntegerLattice V Gamma : Set V.space) = ⊤) :
    Basis iota ℝ V.space := by
  have hi : LinearIndependent ℝ (fun i => (b i).val) := by
    obtain ⟨n, _, gamma, hgamma⟩ := observation_finite_determining_points V Gamma hsep
    exact observation_integer_family_real_independent V Gamma gamma hgamma b b.linearIndependent
  exact Basis.mk hi ((observation_integer_basis_real_span V Gamma b).trans hfull).ge

/-- Extending scalars retains every original integer basis vector exactly. -/
theorem observationRealBasis_apply [Fintype iota] (V : ObservationModule G)
    [FiniteDimensional ℝ V.space] (Gamma : Subgroup G)
    (b : Basis iota ℤ (observationIntegerLattice V Gamma))
    (hsep : ∀ F : V.space, (∀ gamma : Gamma, F gamma = 0) → F = 0)
    (hfull : Submodule.span ℝ (observationIntegerLattice V Gamma : Set V.space) = ⊤) (i : iota) :
    observationRealBasis V Gamma b hsep hfull i = (b i).val := by
  simp only [observationRealBasis, Basis.coe_mk]

/-- The size of any finite integer basis equals the actual real dimension. -/
theorem observation_integer_basis_card [Fintype iota] (V : ObservationModule G)
    [FiniteDimensional ℝ V.space] (Gamma : Subgroup G)
    (b : Basis iota ℤ (observationIntegerLattice V Gamma))
    (hsep : ∀ F : V.space, (∀ gamma : Gamma, F gamma = 0) → F = 0)
    (hfull : Submodule.span ℝ (observationIntegerLattice V Gamma : Set V.space) = ⊤) :
    Fintype.card iota = Module.finrank ℝ V.space :=
  (Module.finrank_eq_card_basis (observationRealBasis V Gamma b hsep hfull)).symm

/-- Real coordinates of an original integer observation are exactly its original integer coordinates. -/
theorem observationRealBasis_repr_int [Fintype iota] (V : ObservationModule G)
    [FiniteDimensional ℝ V.space] (Gamma : Subgroup G)
    (b : Basis iota ℤ (observationIntegerLattice V Gamma))
    (hsep : ∀ F : V.space, (∀ gamma : Gamma, F gamma = 0) → F = 0)
    (hfull : Submodule.span ℝ (observationIntegerLattice V Gamma : Set V.space) = ⊤)
    (F : observationIntegerLattice V Gamma) (i : iota) :
    (observationRealBasis V Gamma b hsep hfull).repr F.val i = (b.repr F i : ℝ) := by
  classical
  let r := observationRealBasis V Gamma b hsep hfull
  have he := congrArg (observationIntegerLattice V Gamma).subtype (b.sum_repr F)
  simp only [map_sum, map_smul, Submodule.subtype_apply] at he
  change r.repr F.val i = _
  rw [← he]
  have hr (j : iota) : (b j).val = r j := (observationRealBasis_apply V Gamma b hsep hfull j).symm
  simp only [hr, map_sum, map_zsmul, Basis.repr_self]
  simp [Finsupp.single_apply]

end GMZP0
