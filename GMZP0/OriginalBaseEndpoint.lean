import GMZP0.OriginalBaseOneParameter
import GMZP0.PolynomialNaturalIdentity

/-! The time-one map is injective because the actual original subgroup
coordinates are polynomials. Uniqueness of paths with a given initial
tangent alone is not used as an endpoint injectivity theorem. -/
noncomputable section
namespace GMZP0

/-- Natural times of an actual subgroup are the powers of its time-one
value, with the original multiplication and identity. -/
theorem one_parameter_nat {G : Type*} [Group G] (gamma : ℝ → G)
    (hadd : ∀ s t, gamma (s + t) = gamma s * gamma t) (n : ℕ) :
    gamma (n : ℝ) = gamma 1 ^ n := by
  induction n with
  | zero => simpa using one_parameter_zero gamma hadd
  | succ n ih => simp only [Nat.cast_add, Nat.cast_one, hadd, ih, pow_succ]

/-- The actual original subgroup coordinate as a real time polynomial. -/
def originalBaseTimePolynomial {m : ℕ}
    (p : Fin m → MvPolynomial (Fin m ⊕ Fin m) ℚ) (c : Fin m → ℚ)
    (v : Fin m → ℝ) (i : Fin m) : Polynomial ℝ :=
  (rationalTriangularFlowPolynomial (originalVelocityPolynomial p c) c i).map
    (MvPolynomial.aeval v).toRingHom

/-- This polynomial evaluates to the same original group coordinate
at every real time, including all natural times. -/
theorem original_base_time_polynomial_eval
    {G : Type*} {m : ℕ} (coord : G ≃ (Fin m → ℝ))
    (p : Fin m → MvPolynomial (Fin m ⊕ Fin m) ℚ) (c : Fin m → ℚ)
    (v : Fin m → ℝ) (t : ℝ) (i : Fin m) :
    (originalBaseTimePolynomial p c v i).eval t =
      coord (originalBaseOneParameter coord p c v t) i := by
  simp only [originalBaseTimePolynomial, Polynomial.eval_map,
    originalBaseOneParameter, Equiv.apply_symm_apply, rationalTriangularFlow]
  rfl

/-- Equal actual time-one values imply equality of every original
initial tangent coordinate. The proof uses all natural powers and
polynomial identity, not finite tests or a supplied inverse. -/
theorem original_base_time_one_injective
    {G : Type*} [Group G] {m : ℕ} (coord : G ≃ (Fin m → ℝ))
    (p : Fin m → MvPolynomial (Fin m ⊕ Fin m) ℚ)
    (hjoint : ∀ g h i, coord (g * h) i = MvPolynomial.aeval (Sum.elim (coord g) (coord h)) (p i))
    (q : G → Fin m → MvPolynomial (Fin m) ℝ)
    (htri : ∀ g u i, coord (g * u) i = coord u i + MvPolynomial.aeval (coord u) (q g i))
    (hlow : ∀ g i d, d ∈ (q g i).support → ∀ j ∈ d.support, j.val < i.val)
    (c : Fin m → ℚ) (hc : coord 1 = fun j => (c j : ℝ)) :
    Function.Injective (fun v => originalBaseOneParameter coord p c v 1) := by
  intro v w he
  change originalBaseOneParameter coord p c v 1 = originalBaseOneParameter coord p c w 1 at he
  have hpoly (i : Fin m) : originalBaseTimePolynomial p c v i = originalBaseTimePolynomial p c w i := by
    apply polynomial_eq_of_nat_evaluations
    intro n
    rw [original_base_time_polynomial_eval coord, original_base_time_polynomial_eval coord,
      one_parameter_nat _ (original_base_one_parameter_add coord p hjoint q htri hlow c hc v),
      one_parameter_nat _ (original_base_one_parameter_add coord p hjoint q htri hlow c hc w), he]
  funext i
  have hfun : (fun t => coord (originalBaseOneParameter coord p c v t) i) =
      (fun t => coord (originalBaseOneParameter coord p c w t) i) := by
    funext t
    rw [← original_base_time_polynomial_eval coord, ← original_base_time_polynomial_eval coord, hpoly i]
  have hd := original_base_one_parameter_tangent coord p hjoint q htri hlow c hc v i
  rw [hfun] at hd
  exact hd.unique (original_base_one_parameter_tangent coord p hjoint q htri hlow c hc w i)

end GMZP0
