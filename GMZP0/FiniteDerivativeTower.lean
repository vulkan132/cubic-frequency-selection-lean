import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Tactic.FieldSimp

/-! Exact finite Taylor formulas for a derivative tower that vanishes
at a fixed level. No analytic remainder or approximate integration is
used; all initial values are those of the original functions. -/
noncomputable section
namespace GMZP0

/-- The finite Taylor sum with the unchanged initial derivatives. -/
def finiteDerivativeTaylor (K : ℕ) (a : ℕ → ℝ) (t : ℝ) : ℝ :=
  ∑ j ∈ Finset.range K, t ^ j / (j.factorial : ℝ) * a j

set_option backward.isDefEq.respectTransparency false in
/-- Differentiation of the factorial-normalized monomial preserves the
exact next factorial coefficient, at every real point. -/
theorem factorial_power_hasDerivAt (j : ℕ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => s ^ (j + 1) / ((j + 1).factorial : ℝ))
      (t ^ j / (j.factorial : ℝ)) t := by
  convert! (hasDerivAt_pow (j + 1) t).div_const ((j + 1).factorial : ℝ) using 1
  rw [Nat.add_sub_cancel, Nat.factorial_succ, Nat.cast_mul]
  have hj : ((j + 1 : ℕ) : ℝ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero j
  field_simp

/-- The finite Taylor sum with its constant term has its prescribed
initial value, including a tower of height one. -/
theorem finite_derivative_taylor_zero (K : ℕ) (a : ℕ → ℝ) :
    finiteDerivativeTaylor (K + 1) a 0 = a 0 := by
  simp [finiteDerivativeTaylor, Finset.sum_range_succ', pow_succ]

set_option backward.isDefEq.respectTransparency false in
/-- The derivative of a finite Taylor sum is the shifted shorter sum. -/
theorem finite_derivative_taylor_hasDerivAt (K : ℕ) (a : ℕ → ℝ) (t : ℝ) :
    HasDerivAt (finiteDerivativeTaylor (K + 1) a)
      (finiteDerivativeTaylor K (fun j => a (j + 1)) t) t := by
  classical
  have hh := (HasDerivAt.fun_sum (u := Finset.range K) fun j _ =>
    (factorial_power_hasDerivAt j t).mul_const (a (j + 1))).add_const (a 0)
  convert! hh using 1
  · funext s
    simp [finiteDerivativeTaylor, Finset.sum_range_succ']

set_option backward.isDefEq.respectTransparency false in
/-- Equality of the actual derivatives everywhere and the actual value
at zero determines the entire real function. -/
theorem real_functions_eq_of_derivative_and_initial
    (f g d : ℝ → ℝ)
    (hf : ∀ t, HasDerivAt f (d t) t) (hg : ∀ t, HasDerivAt g (d t) t)
    (hzero : f 0 = g 0) : ∀ t, f t = g t := by
  have hd (t : ℝ) : HasDerivAt (fun s => f s - g s) 0 t := by
    convert! (hf t).sub (hg t) using 1
    simp
  intro t
  have he := is_const_of_deriv_eq_zero (fun t => (hd t).differentiableAt)
    (fun t => (hd t).deriv) t 0
  simpa only [hzero, sub_self, sub_eq_zero] using he

/-- A genuine derivative tower killed at level K equals its exact
finite Taylor sum, for all real times, with the original initial values. -/
theorem finite_derivative_tower_exact (K : ℕ) (f : ℕ → ℝ → ℝ)
    (hd : ∀ j t, HasDerivAt (f j) (f (j + 1) t) t)
    (hzero : ∀ t, f K t = 0) :
    ∀ t, f 0 t = finiteDerivativeTaylor K (fun j => f j 0) t := by
  induction K generalizing f with
  | zero =>
    intro t
    simpa [finiteDerivativeTaylor] using hzero t
  | succ K ih =>
    have hs := ih (fun j => f (j + 1)) (fun j t => hd (j + 1) t) hzero
    apply real_functions_eq_of_derivative_and_initial (f 0)
      (finiteDerivativeTaylor (K + 1) (fun j => f j 0)) (f 1)
    · exact hd 0
    · intro t
      rw [hs t]
      exact finite_derivative_taylor_hasDerivAt K (fun j => f j 0) t
    · exact (finite_derivative_taylor_zero K (fun j => f j 0)).symm

end GMZP0
