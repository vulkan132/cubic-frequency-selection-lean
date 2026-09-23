import GMZP0.RationalHeightFinite
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.Algebra.Module.Submodule.Ker
import Mathlib.Data.Real.Basic

/-! Finite families of actual linear kernels in a fixed original real
basis. Being a linear kernel alone does not assert a Lie subgroup. -/
noncomputable section
open Module
namespace GMZP0
variable {iota E : Type*} [Fintype iota] [AddCommGroup E] [Module ℝ E]

/-- A rational covector acts on the actual original real basis coordinates. -/
def rationalBasisFunctional (b : Basis iota ℝ E) (a : iota → ℚ) : E →ₗ[ℝ] ℝ :=
  ∑ i, (a i : ℝ) • b.coord i

/-- Evaluation on a basis vector recovers the unchanged rational coefficient. -/
theorem rational_basis_functional_basis (b : Basis iota ℝ E) (a : iota → ℚ) (i : iota) :
    rationalBasisFunctional b a (b i) = (a i : ℝ) := by
  classical
  simp [rationalBasisFunctional, Basis.coord_apply, Basis.repr_self, Finsupp.single_apply]

/-- A nonzero rational covector gives a proper kernel in the original space. -/
theorem rational_basis_kernel_proper (b : Basis iota ℝ E) (a : iota → ℚ) (ha : a ≠ 0) :
    LinearMap.ker (rationalBasisFunctional b a) ≠ ⊤ := by
  intro hk
  have hf := LinearMap.ker_eq_top.mp hk
  apply ha
  funext i
  have hi := LinearMap.congr_fun hf (b i)
  rw [rational_basis_functional_basis] at hi
  change (a i : ℝ) = 0 at hi
  change a i = 0
  exact_mod_cast hi

/-- All height-bounded rational covectors yield only finitely many actual
linear kernels in a fixed original basis, with no choice of new bases. -/
theorem bounded_rational_kernel_family_finite (b : Basis iota ℝ E) (H : ℕ) :
    {W : Submodule ℝ E | ∃ a : iota → ℚ, (∀ i, rationalHeight (a i) ≤ H) ∧
      LinearMap.ker (rationalBasisFunctional b a) = W}.Finite := by
  apply ((bounded_rational_vectors_finite (iota := iota) H).image
    (fun a => LinearMap.ker (rationalBasisFunctional b a))).subset
  rintro W ⟨a, ha, he⟩
  exact ⟨a, ha, he⟩

end GMZP0
