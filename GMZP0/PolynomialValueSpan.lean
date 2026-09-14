import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Algebra.BigOperators.Module
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.CharZero.Infinite

/-! A vector-valued polynomial has the same real span of values and coefficients.
The proof uses all real parameter values; an arbitrary restricted parameter
set need not determine the coefficient span. -/
noncomputable section
open MvPolynomial
namespace GMZP0
variable {sigma E : Type*} [AddCommGroup E] [Module ℝ E]

/-- Evaluate an actual finite family of vector coefficients at real coordinates. -/
def vectorPolynomialValue (S : Finset (sigma →₀ ℕ)) (v : (sigma →₀ ℕ) → E)
    (x : sigma → ℝ) : E := ∑ d ∈ S, (d.prod fun i n => x i ^ n) • v d

/-- Applying a real linear functional gives exactly the scalar coefficient polynomial. -/
theorem vectorPolynomialValue_linear (S : Finset (sigma →₀ ℕ)) (v : (sigma →₀ ℕ) → E)
    (ell : E →ₗ[ℝ] ℝ) (x : sigma → ℝ) :
    ell (vectorPolynomialValue S v x) =
      MvPolynomial.eval x (∑ d ∈ S, MvPolynomial.monomial d (ell (v d))) := by
  simp only [vectorPolynomialValue, map_sum, map_smul, smul_eq_mul, eval_monomial]
  apply Finset.sum_congr rfl
  intro d hd
  exact mul_comm _ _

/-- A subspace containing every real polynomial value contains every actual coefficient. -/
theorem vectorPolynomial_coefficient_mem (S : Finset (sigma →₀ ℕ)) (v : (sigma →₀ ℕ) → E)
    (U : Submodule ℝ E) (hvalues : ∀ x, vectorPolynomialValue S v x ∈ U)
    (d : sigma →₀ ℕ) (hd : d ∈ S) : v d ∈ U := by
  classical
  by_contra h
  obtain ⟨ell, hne, hker⟩ := Submodule.exists_le_ker_of_notMem h
  have hz : (∑ e ∈ S, MvPolynomial.monomial e (ell (v e))) = (0 : MvPolynomial sigma ℝ) := by
    apply MvPolynomial.funext
    intro x
    rw [← vectorPolynomialValue_linear]
    exact hker (hvalues x)
  have hc := congrArg (MvPolynomial.coeff d) hz
  have he : ell (v d) = 0 := by simpa [MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial, hd] using hc
  exact hne he

/-- Exact equality of the real span of all values and the real span of the finite coefficient family. -/
theorem vectorPolynomial_span_values (S : Finset (sigma →₀ ℕ)) (v : (sigma →₀ ℕ) → E) :
    Submodule.span ℝ (Set.range (vectorPolynomialValue S v)) =
      Submodule.span ℝ (v '' (S : Set (sigma →₀ ℕ))) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨x, rfl⟩
    apply Submodule.sum_mem
    intro d hd
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨d, hd, rfl⟩)
  · apply Submodule.span_le.mpr
    rintro _ ⟨d, hd, rfl⟩
    exact vectorPolynomial_coefficient_mem S v (Submodule.span ℝ (Set.range (vectorPolynomialValue S v)))
      (fun x => Submodule.subset_span ⟨x, rfl⟩) d hd

end GMZP0
