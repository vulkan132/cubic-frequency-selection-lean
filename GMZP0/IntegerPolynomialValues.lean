import GMZP0.ObservationPolynomialMatrix
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-! Integer values of actual rational coordinate polynomials, and polynomial
uniqueness on the whole integer coordinate lattice. -/
noncomputable section
open Module MvPolynomial
namespace GMZP0
variable {sigma : Type*}

/-- One positive integer clears a rational polynomial's values at every integer coordinate vector. -/
theorem rational_polynomial_integer_multiple (P : MvPolynomial sigma ℚ) :
    ∃ k : ℕ, 0 < k ∧ ∀ z : sigma → ℤ, ∃ n : ℤ,
      (k : ℝ) * MvPolynomial.aeval (fun i => (z i : ℝ)) P = n := by
  induction P using MvPolynomial.induction_on with
  | C q =>
    refine ⟨q.den, q.den_pos, fun z => ⟨q.num, ?_⟩⟩
    rw [MvPolynomial.aeval_C]
    change (q.den : ℝ) * (q : ℝ) = (q.num : ℝ)
    rw [Rat.cast_def]
    have hd : (q.den : ℝ) ≠ 0 := by exact_mod_cast q.den_ne_zero
    field_simp
  | add P Q hP hQ =>
    obtain ⟨a, ha, hPa⟩ := hP
    obtain ⟨b, hb, hQb⟩ := hQ
    refine ⟨a * b, Nat.mul_pos ha hb, ?_⟩
    intro z
    obtain ⟨m, hm⟩ := hPa z
    obtain ⟨n, hn⟩ := hQb z
    refine ⟨(b : ℤ) * m + (a : ℤ) * n, ?_⟩
    rw [map_add, Nat.cast_mul, Int.cast_add, Int.cast_mul, Int.cast_mul,
      Int.cast_natCast, Int.cast_natCast, ← hm, ← hn]
    ring
  | mul_X P i hP =>
    obtain ⟨k, hk, hPk⟩ := hP
    refine ⟨k, hk, ?_⟩
    intro z
    obtain ⟨n, hn⟩ := hPk z
    refine ⟨n * z i, ?_⟩
    rw [map_mul, MvPolynomial.aeval_X, ← mul_assoc, hn, Int.cast_mul]

/-- Vanishing at every integer coordinate vector forces the actual real polynomial to be zero. -/
theorem real_polynomial_zero_of_integer_values (P : MvPolynomial sigma ℝ)
    (hP : ∀ z : sigma → ℤ, MvPolynomial.eval (fun i => (z i : ℝ)) P = 0) : P = 0 := by
  classical
  apply MvPolynomial.funext_set (fun _ : sigma => Set.range (Int.cast : ℤ → ℝ))
    (fun _ => Set.infinite_range_of_injective Int.cast_injective)
  intro x hx
  choose z hz using fun i => hx i (Set.mem_univ _)
  have he : x = fun i => (z i : ℝ) := funext fun i => (hz i).symm
  rw [he]
  simpa using hP z

end GMZP0
