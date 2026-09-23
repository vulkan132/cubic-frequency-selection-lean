import GMZP0.IntegerPolynomialValues
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-! Clear input and output denominators of fixed rational coordinate
polynomials before all real data and integer points. Integral values at
the origin are required for an integral scaled-input image. -/
noncomputable section
open MvPolynomial
namespace GMZP0
variable {sigma tau : Type*}

/-- A fixed rational polynomial has integral increments from the origin
on some full scaled integer grid. The constant term is not discarded. -/
theorem rational_polynomial_scaled_integer_increment (P : MvPolynomial sigma ℚ) :
    ∃ k : ℕ, 0 < k ∧ ∀ z : sigma → ℤ, ∃ n : ℤ,
      MvPolynomial.aeval (fun i => (k : ℝ) * (z i : ℝ)) P -
        MvPolynomial.aeval (fun _ => (0 : ℝ)) P = n := by
  induction P using MvPolynomial.induction_on with
  | C a =>
    exact ⟨1, Nat.one_pos, fun _ => ⟨0, by simp⟩⟩
  | add P Q hP hQ =>
    obtain ⟨a, ha, hPa⟩ := hP
    obtain ⟨b, hb, hQb⟩ := hQ
    refine ⟨a * b, Nat.mul_pos ha hb, ?_⟩
    intro z
    obtain ⟨u, hu⟩ := hPa (fun i => (b : ℤ) * z i)
    obtain ⟨v, hv⟩ := hQb (fun i => (a : ℤ) * z i)
    have hp : (fun i => (a : ℝ) * (((b : ℤ) * z i : ℤ) : ℝ)) =
        fun i => ((a * b : ℕ) : ℝ) * (z i : ℝ) := by funext i; push_cast; ring
    have hq : (fun i => (b : ℝ) * (((a : ℤ) * z i : ℤ) : ℝ)) =
        fun i => ((a * b : ℕ) : ℝ) * (z i : ℝ) := by funext i; push_cast; ring
    rw [hp] at hu
    rw [hq] at hv
    refine ⟨u + v, ?_⟩
    rw [map_add, map_add, Int.cast_add, ← hu, ← hv]
    ring
  | mul_X P i _ =>
    obtain ⟨k, hk, hPk⟩ := rational_polynomial_integer_multiple P
    refine ⟨k, hk, ?_⟩
    intro z
    obtain ⟨n, hn⟩ := hPk (fun j => (k : ℤ) * z j)
    have he : (fun j => (((k : ℤ) * z j : ℤ) : ℝ)) = fun j => (k : ℝ) * (z j : ℝ) := by
      funext j
      push_cast
      rfl
    rw [he] at hn
    refine ⟨n * z i, ?_⟩
    simp only [map_mul, MvPolynomial.aeval_X, mul_zero, sub_zero, Int.cast_mul]
    rw [← hn]
    ring

/-- If the original constant value is integral, one scaled full integer
grid maps entirely to integer values, uniformly before all input points. -/
theorem rational_polynomial_scaled_integer_values (P : MvPolynomial sigma ℚ)
    (hzero : ∃ c : ℤ, MvPolynomial.aeval (fun _ => (0 : ℝ)) P = c) :
    ∃ k : ℕ, 0 < k ∧ ∀ z : sigma → ℤ, ∃ n : ℤ,
      MvPolynomial.aeval (fun i => (k : ℝ) * (z i : ℝ)) P = n := by
  obtain ⟨c, hc⟩ := hzero
  obtain ⟨k, hk, hv⟩ := rational_polynomial_scaled_integer_increment P
  refine ⟨k, hk, ?_⟩
  intro z
  obtain ⟨n, hn⟩ := hv z
  refine ⟨n + c, ?_⟩
  rw [hc] at hn
  rw [Int.cast_add, ← hn]
  ring

/-- A single positive multiplier clears every output coordinate of a
fixed finite rational polynomial array at every original integer point. -/
theorem rational_polynomial_array_integer_multiple [Fintype tau]
    (P : tau → MvPolynomial sigma ℚ) :
    ∃ k : ℕ, 0 < k ∧ ∀ z : sigma → ℤ, ∃ n : tau → ℤ, ∀ j,
      (k : ℝ) * MvPolynomial.aeval (fun i => (z i : ℝ)) (P j) = n j := by
  classical
  choose k hk hv using fun j => rational_polynomial_integer_multiple (P j)
  let K := ∏ j, k j
  have hK : 0 < K := Finset.prod_pos fun j _ => hk j
  refine ⟨K, hK, ?_⟩
  intro z
  suffices ∀ j, ∃ n : ℤ, (K : ℝ) * MvPolynomial.aeval (fun i => (z i : ℝ)) (P j) = n by
    choose n hn using this
    exact ⟨n, hn⟩
  intro j
  obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem k (Finset.mem_univ j)
  obtain ⟨n, hn⟩ := hv j z
  refine ⟨(c : ℤ) * n, ?_⟩
  change ((∏ j, k j : ℕ) : ℝ) * _ = _
  rw [hc, Nat.cast_mul, Int.cast_mul, Int.cast_natCast, ← hn]
  ring

/-- A single scaled integer grid makes all coordinates of a fixed
rational array integral when their original constant values are integral. -/
theorem rational_polynomial_array_scaled_integer_values [Fintype tau]
    (P : tau → MvPolynomial sigma ℚ)
    (hzero : ∀ j, ∃ c : ℤ, MvPolynomial.aeval (fun _ => (0 : ℝ)) (P j) = c) :
    ∃ k : ℕ, 0 < k ∧ ∀ z : sigma → ℤ, ∃ n : tau → ℤ, ∀ j,
      MvPolynomial.aeval (fun i => (k : ℝ) * (z i : ℝ)) (P j) = n j := by
  classical
  choose k hk hv using fun j => rational_polynomial_scaled_integer_values (P j) (hzero j)
  let K := ∏ j, k j
  have hK : 0 < K := Finset.prod_pos fun j _ => hk j
  refine ⟨K, hK, ?_⟩
  intro z
  suffices ∀ j, ∃ n : ℤ, MvPolynomial.aeval (fun i => (K : ℝ) * (z i : ℝ)) (P j) = n by
    choose n hn using this
    exact ⟨n, hn⟩
  intro j
  obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem k (Finset.mem_univ j)
  obtain ⟨n, hn⟩ := hv j (fun i => (c : ℤ) * z i)
  refine ⟨n, ?_⟩
  have he : (fun i => (k j : ℝ) * (((c : ℤ) * z i : ℤ) : ℝ)) =
      fun i => (K : ℝ) * (z i : ℝ) := by
    funext i
    dsimp [K]
    rw [hc]
    push_cast
    ring
  rw [he] at hn
  exact hn

end GMZP0
