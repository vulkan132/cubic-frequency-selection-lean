import GMZP0.RationalPolynomialDenominators

/-! The two weak lattice inclusions from actual rational coordinate maps.
One positive denominator precedes all original lattice points. No additive
closure of the image of the lattice under a nonlinear map is used. -/
noncomputable section
open MvPolynomial
namespace GMZP0
variable {sigma tau : Type*} [Fintype sigma] [Fintype tau]

/-- Rational forward and left-inverse coordinate maps, with integral
forward value at zero, place their actual integer-grid image between q*Z
and q^-1*Z for one fixed positive q. -/
theorem rational_coordinate_integer_image_sandwich
    (E : sigma → MvPolynomial tau ℚ) (L : tau → MvPolynomial sigma ℚ)
    (hLE : ∀ x : tau → ℝ, ∀ j,
      MvPolynomial.aeval (fun i => MvPolynomial.aeval x (E i)) (L j) = x j)
    (hzero : ∀ i, ∃ c : ℤ, MvPolynomial.aeval (fun _ => (0 : ℝ)) (E i) = c) :
    ∃ q : ℕ, 0 < q ∧
      (∀ z : tau → ℤ, ∃ w : sigma → ℤ, ∀ j,
        MvPolynomial.aeval (fun i => (w i : ℝ)) (L j) = (q : ℝ) * (z j : ℝ)) ∧
      (∀ w : sigma → ℤ, ∃ z : tau → ℤ, ∀ j,
        (q : ℝ) * MvPolynomial.aeval (fun i => (w i : ℝ)) (L j) = z j) := by
  obtain ⟨a, ha, hE⟩ := rational_polynomial_array_scaled_integer_values E hzero
  obtain ⟨b, hb, hL⟩ := rational_polynomial_array_integer_multiple L
  refine ⟨a * b, Nat.mul_pos ha hb, ?_, ?_⟩
  · intro z
    obtain ⟨w, hw⟩ := hE (fun j => (b : ℤ) * z j)
    have hx : (fun j => (a : ℝ) * (((b : ℤ) * z j : ℤ) : ℝ)) =
        fun j => ((a * b : ℕ) : ℝ) * (z j : ℝ) := by
      funext j
      push_cast
      ring
    rw [hx] at hw
    refine ⟨w, ?_⟩
    intro j
    have he := hLE (fun j => ((a * b : ℕ) : ℝ) * (z j : ℝ)) j
    simpa only [hw] using he
  · intro w
    obtain ⟨z, hz⟩ := hL w
    refine ⟨fun j => (a : ℤ) * z j, ?_⟩
    intro j
    rw [Nat.cast_mul, mul_assoc, hz, Int.cast_mul, Int.cast_natCast]

/-- For the actual original lattice and a specified rational logarithmic
coordinate equivalence, clearing both coordinate directions supplies the
weak-basis inclusions. The log/exp polynomial identities remain explicit
until proved for the intended Lie exponential. -/
theorem original_logarithmic_lattice_sandwich
    {H : Type*} [Group H] (Gamma : Subgroup H)
    (coord : H ≃ (sigma → ℝ)) (logCoord : H ≃ (tau → ℝ))
    (hint : ∀ gamma : Gamma, ∃ z : sigma → ℤ, coord gamma = fun i => (z i : ℝ))
    (hcover : ∀ z : sigma → ℤ, ∃ gamma : Gamma, coord gamma = fun i => (z i : ℝ))
    (E : sigma → MvPolynomial tau ℚ) (L : tau → MvPolynomial sigma ℚ)
    (hE : ∀ x : tau → ℝ, ∀ i, coord (logCoord.symm x) i = MvPolynomial.aeval x (E i))
    (hL : ∀ g : H, ∀ j, logCoord g j = MvPolynomial.aeval (coord g) (L j))
    (hzero : logCoord 1 = 0) :
    ∃ q : ℕ, 0 < q ∧
      (∀ z : tau → ℤ, ∃ gamma : Gamma, ∀ j, logCoord gamma j = (q : ℝ) * (z j : ℝ)) ∧
      (∀ gamma : Gamma, ∃ z : tau → ℤ, ∀ j, (q : ℝ) * logCoord gamma j = z j) := by
  have hLE (x : tau → ℝ) (j : tau) :
      MvPolynomial.aeval (fun i => MvPolynomial.aeval x (E i)) (L j) = x j := by
    have he := congrFun (logCoord.apply_symm_apply x) j
    rw [hL] at he
    have hx : coord (logCoord.symm x) = fun i => MvPolynomial.aeval x (E i) := funext (hE x)
    rw [hx] at he
    exact he
  have horigin : logCoord.symm (0 : tau → ℝ) = 1 := by
    apply logCoord.injective
    rw [logCoord.apply_symm_apply, hzero]
  obtain ⟨c, hc⟩ := hint ⟨1, Gamma.one_mem⟩
  have hEzero (i : sigma) : ∃ c : ℤ, MvPolynomial.aeval (fun _ => (0 : ℝ)) (E i) = c := by
    refine ⟨c i, ?_⟩
    rw [← hE]
    change coord (logCoord.symm (0 : tau → ℝ)) i = (c i : ℝ)
    rw [horigin]
    exact congrFun hc i
  obtain ⟨q, hq, hleft, hright⟩ := rational_coordinate_integer_image_sandwich E L hLE hEzero
  refine ⟨q, hq, ?_, ?_⟩
  · intro z
    obtain ⟨w, hw⟩ := hleft z
    obtain ⟨gamma, hgamma⟩ := hcover w
    refine ⟨gamma, ?_⟩
    intro j
    rw [hL, hgamma]
    exact hw j
  · intro gamma
    obtain ⟨w, hw⟩ := hint gamma
    obtain ⟨z, hz⟩ := hright w
    refine ⟨z, ?_⟩
    intro j
    rw [hL, hw]
    exact hz j

end GMZP0
