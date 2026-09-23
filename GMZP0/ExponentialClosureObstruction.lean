import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum

/-! Exact coordinate obstruction: the Heisenberg multiplication law and
its exponential/logarithm polynomials do not preserve an arbitrary plane.
This does not refute closure for Lie subalgebras or ideals. -/
namespace GMZP0

/-- The exponential image of the horizontal linear plane fails closure
under the actual Heisenberg coordinate multiplication formula. -/
theorem heisenberg_exponential_plane_closure_obstruction :
    let mul : (ℝ × ℝ × ℝ) → (ℝ × ℝ × ℝ) → (ℝ × ℝ × ℝ) :=
      fun a b => (a.1 + b.1, a.2.1 + b.2.1, a.2.2 + b.2.2 + a.1 * b.2.1)
    let exp : (ℝ × ℝ × ℝ) → (ℝ × ℝ × ℝ) :=
      fun v => (v.1, v.2.1, v.2.2 + v.1 * v.2.1 / 2)
    let log : (ℝ × ℝ × ℝ) → (ℝ × ℝ × ℝ) :=
      fun a => (a.1, a.2.1, a.2.2 - a.1 * a.2.1 / 2)
    ∃ v w, v.2.2 = 0 ∧ w.2.2 = 0 ∧ (log (mul (exp v) (exp w))).2.2 = 1 / 2 ∧
      (log (mul (exp v) (exp w))).2.2 ≠ 0 := by
  refine ⟨(1, 0, 0), (0, 1, 0), ?_⟩
  norm_num

end GMZP0
