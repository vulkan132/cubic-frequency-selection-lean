import GMZP0.ObservationRationalSpan
import GMZP0.RationalPolynomialDenominators
import Mathlib.LinearAlgebra.StdBasis

/-! Rational subspaces are spanned by logarithms of actual original
lattice points in the subspace. No additive closure of log(Gamma) is used. -/
noncomputable section
open Module
namespace GMZP0
variable {sigma tau : Type*} [Fintype sigma] [Fintype tau]

/-- Clear all denominators in a fixed finite rational vector family at once. -/
theorem rational_vector_family_integer_multiple (a : tau → sigma → ℚ) :
    ∃ k : ℕ, 0 < k ∧ ∃ z : tau → sigma → ℤ,
      ∀ j i, (k : ℝ) * (a j i : ℝ) = z j i := by
  obtain ⟨k, hk, h⟩ := rational_polynomial_array_integer_multiple
    (fun ji : tau × sigma => (MvPolynomial.C (a ji.1 ji.2) : MvPolynomial Empty ℚ))
  obtain ⟨z, hz⟩ := h (fun _ => 0)
  exact ⟨k, hk, fun j i => z (j, i), fun j i => by simpa using hz (j, i)⟩

/-- One positive integer scales the entire rational family to logarithms
of original lattice elements. The common scale precedes every family index. -/
theorem rational_vectors_original_lattice_realization
    {G : Type*} [Group G] (Gamma : Subgroup G) (logCoord : G ≃ (sigma → ℝ))
    (den : ℕ) (hden : 0 < den)
    (hgrid : ∀ z : sigma → ℤ, ∃ gamma : Gamma,
      ∀ i, logCoord gamma i = (den : ℝ) * (z i : ℝ))
    (a : tau → sigma → ℚ) :
    ∃ k : ℕ, 0 < k ∧ ∃ gamma : tau → Gamma,
      ∀ j, logCoord (gamma j) = (k : ℝ) • (fun i => (a j i : ℝ)) := by
  obtain ⟨k, hk, z, hz⟩ := rational_vector_family_integer_multiple a
  choose gamma hgamma using fun j => hgrid (z j)
  refine ⟨den * k, Nat.mul_pos hden hk, gamma, ?_⟩
  intro j
  funext i
  simp only [Pi.smul_apply, smul_eq_mul, Nat.cast_mul, hgamma, ← hz, mul_assoc]

/-- In the original standard tangent basis the rational vector is the
literal coordinate vector, including when the index type is empty. -/
theorem rational_standard_basis_vector (a : sigma → ℚ) :
    rationalBasisVector (Pi.basisFun ℝ sigma) a = (fun i => (a i : ℝ)) := by
  funext i
  simpa only [Pi.basisFun_repr] using rationalBasisVector_repr (Pi.basisFun ℝ sigma) a i

/-- A finite subset of the original lattice inside the exact subspace
has logarithms spanning it. Neither the log image nor its intersection
is replaced by an additive subgroup or a selected replacement lattice. -/
theorem rational_subspace_finite_original_lattice_span
    {G : Type*} [Group G] (Gamma : Subgroup G) (logCoord : G ≃ (sigma → ℝ))
    (den : ℕ) (hden : 0 < den)
    (hgrid : ∀ z : sigma → ℤ, ∃ gamma : Gamma,
      ∀ i, logCoord gamma i = (den : ℝ) * (z i : ℝ))
    (U : Submodule ℝ (sigma → ℝ)) (hU : RationalInBasis (Pi.basisFun ℝ sigma) U) :
    ∃ F : Finset G, (∀ g ∈ F, g ∈ Gamma ∧ logCoord g ∈ U) ∧
      Submodule.span ℝ (logCoord '' (F : Set G)) = U := by
  classical
  obtain ⟨S, hS⟩ := hU
  obtain ⟨k, hk, gamma, hgamma⟩ := rational_vectors_original_lattice_realization
    Gamma logCoord den hden hgrid (fun a : S => a.val)
  let F : Finset G := Finset.univ.image (fun a : S => (gamma a : G))
  have hmem (a : S) : (fun i => (a.val i : ℝ)) ∈ U := by
    rw [hS, ← rational_standard_basis_vector]
    exact Submodule.subset_span ⟨a.val, a.property, rfl⟩
  have hF : ∀ g ∈ F, g ∈ Gamma ∧ logCoord g ∈ U := by
    intro g hg
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hg
    exact ⟨(gamma a).property, hgamma a ▸ U.smul_mem (k : ℝ) (hmem a)⟩
  refine ⟨F, hF, le_antisymm ?_ ?_⟩
  · apply Submodule.span_le.mpr
    rintro _ ⟨g, hg, rfl⟩
    exact (hF g hg).2
  · rw [hS]
    apply Submodule.span_le.mpr
    rintro _ ⟨a, ha, rfl⟩
    rw [rational_standard_basis_vector]
    apply (Submodule.smul_mem_iff (Submodule.span ℝ (logCoord '' (F : Set G)))
      (show (k : ℝ) ≠ 0 by exact_mod_cast (ne_of_gt hk))).mp
    rw [← hgamma ⟨a, ha⟩]
    exact Submodule.subset_span ⟨gamma ⟨a, ha⟩,
      Finset.mem_image.mpr ⟨⟨a, ha⟩, Finset.mem_univ _, rfl⟩, rfl⟩

/-- The entire original lattice intersection therefore has exactly the
required real logarithmic span; no cocompactness is claimed here. -/
theorem rational_subspace_original_lattice_span
    {G : Type*} [Group G] (Gamma : Subgroup G) (logCoord : G ≃ (sigma → ℝ))
    (den : ℕ) (hden : 0 < den)
    (hgrid : ∀ z : sigma → ℤ, ∃ gamma : Gamma,
      ∀ i, logCoord gamma i = (den : ℝ) * (z i : ℝ))
    (U : Submodule ℝ (sigma → ℝ)) (hU : RationalInBasis (Pi.basisFun ℝ sigma) U) :
    Submodule.span ℝ (logCoord '' {g | g ∈ Gamma ∧ logCoord g ∈ U}) = U := by
  obtain ⟨F, hF, hspan⟩ := rational_subspace_finite_original_lattice_span
    Gamma logCoord den hden hgrid U hU
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨g, hg, rfl⟩
    exact hg.2
  · calc
      U = Submodule.span ℝ (logCoord '' (F : Set G)) := hspan.symm
      _ ≤ _ := Submodule.span_mono (Set.image_mono hF)

end GMZP0
