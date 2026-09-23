import GMZP0.LieBasisBracketSpan
import GMZP0.ObservationRationalSpan
import GMZP0.RationalHeightFinite

/-! Rational coordinates for actual brackets in a fixed original real
basis, and the exact rational generator transformation for one step. -/
noncomputable section
open Module
namespace GMZP0
variable {L iota : Type*} [LieRing L] [LieAlgebra ℝ L] [Fintype iota]

/-- Fixed rational coordinates for bracketing on the left by a basis vector. -/
def rationalBasisBracketCoordinates (C : iota → iota → iota → ℚ)
    (i : iota) (a : iota → ℚ) : iota → ℚ := fun k => ∑ j, a j * C i j k

/-- Rational coordinate contraction computes the original Lie bracket,
using its actual structure coefficients. -/
theorem rational_basis_bracket_vector (b : Basis iota ℝ L)
    (C : iota → iota → iota → ℚ)
    (hC : ∀ i j k, b.repr ⁅b i, b j⁆ k = (C i j k : ℝ))
    (i : iota) (a : iota → ℚ) :
    ⁅b i, rationalBasisVector b a⁆ = rationalBasisVector b (rationalBasisBracketCoordinates C i a) := by
  apply b.repr.injective
  ext k
  rw [rationalBasisVector_repr]
  change b.repr ⁅b i, ∑ j, (a j : ℝ) • b j⁆ k = _
  simp [lie_sum, lie_smul, hC, rationalBasisBracketCoordinates]

/-- The whole rational generator list after an actual lower-central step. -/
def rationalBasisBracketStep (C : iota → iota → iota → ℚ)
    (S : Finset (iota → ℚ)) : Finset (iota → ℚ) := by
  classical
  exact (Finset.univ.product S).image (fun z => rationalBasisBracketCoordinates C z.1 z.2)

/-- The new rational generators have exactly the original basis-bracket
image, without enlarging or replacing the real subspace. -/
theorem rational_basis_bracket_step_image (b : Basis iota ℝ L)
    (C : iota → iota → iota → ℚ)
    (hC : ∀ i j k, b.repr ⁅b i, b j⁆ k = (C i j k : ℝ))
    (S : Finset (iota → ℚ)) :
    rationalBasisVector b '' (rationalBasisBracketStep C S : Set (iota → ℚ)) =
      {z | ∃ i, ∃ v ∈ rationalBasisVector b '' (S : Set (iota → ℚ)), z = ⁅b i, v⁆} := by
  classical
  ext z
  constructor
  · rintro ⟨a, ha, rfl⟩
    obtain ⟨⟨i, q⟩, hiq, rfl⟩ := Finset.mem_image.mp ha
    exact ⟨i, rationalBasisVector b q, ⟨q, (Finset.mem_product.mp hiq).2, rfl⟩,
      (rational_basis_bracket_vector b C hC i q).symm⟩
  · rintro ⟨i, v, ⟨a, ha, rfl⟩, rfl⟩
    refine ⟨rationalBasisBracketCoordinates C i a, ?_, (rational_basis_bracket_vector b C hC i a).symm⟩
    exact Finset.mem_image.mpr ⟨(i, a), Finset.mem_product.mpr ⟨Finset.mem_univ _, ha⟩, rfl⟩

/-- The actual lower-central step inherits a finite rational presentation
in the same original basis. -/
theorem rational_lie_ideal_step (b : Basis iota ℝ L)
    (C : iota → iota → iota → ℚ)
    (hC : ∀ i j k, b.repr ⁅b i, b j⁆ k = (C i j k : ℝ))
    (N : LieIdeal ℝ L) (S : Finset (iota → ℚ))
    (hN : N.toSubmodule = Submodule.span ℝ (rationalBasisVector b '' (S : Set (iota → ℚ)))) :
    (⁅(⊤ : LieIdeal ℝ L), N⁆ : LieIdeal ℝ L).toSubmodule =
      Submodule.span ℝ (rationalBasisVector b '' (rationalBasisBracketStep C S : Set (iota → ℚ))) := by
  rw [rational_basis_bracket_step_image b C hC]
  exact lie_ideal_basis_bracket_span b N _ hN

end GMZP0
