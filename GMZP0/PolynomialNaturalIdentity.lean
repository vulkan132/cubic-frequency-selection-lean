import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Real.Basic

/-! Exact polynomial identities from the entire natural grid. This is
an infinite-grid theorem, not a finite sampling test. -/
noncomputable section
namespace GMZP0

/-- Two real polynomials agreeing at every natural number are identical. -/
theorem polynomial_eq_of_nat_evaluations (p q : Polynomial ℝ)
    (h : ∀ n : ℕ, p.eval (n : ℝ) = q.eval (n : ℝ)) : p = q := by
  apply p.eq_of_infinite_eval_eq q
  apply (Set.infinite_range_of_injective (Nat.cast_injective (R := ℝ))).mono
  rintro x ⟨n, rfl⟩
  exact h n

end GMZP0
