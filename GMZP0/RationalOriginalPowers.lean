import GMZP0.PolynomialDiscretePrimitive
import GMZP0.RationalTriangularFlow
import GMZP0.TriangularIntegerCell

/-! A fixed rational polynomial in the original element coordinates
and time agrees with all of that element's natural powers. Exact
discrete integration follows the original strict triangular law. -/
noncomputable section
namespace GMZP0

/-- Construct the original power coordinates by discrete integration,
retaining the actual rational identity and every element coordinate. -/
def originalPowerCoordinatePolynomial {m : ℕ}
    (p : Fin m → MvPolynomial (Fin m ⊕ Fin m) ℚ) (c : Fin m → ℚ)
    (i : Fin m) : Polynomial (MvPolynomial (Fin m) ℚ) :=
  Polynomial.C (MvPolynomial.C (c i)) + polynomialDiscretePrimitive
    (MvPolynomial.aeval (Sum.elim (fun j => Polynomial.C (MvPolynomial.X j))
      (fun j => if _h : j.val < i.val then originalPowerCoordinatePolynomial p c j else 0)) (p i))
termination_by i.val

/-- The real specialization of the same fixed power-coordinate array. -/
def rationalPowerCoordinates {m : ℕ}
    (p : Fin m → MvPolynomial (Fin m ⊕ Fin m) ℚ) (c : Fin m → ℚ)
    (x : Fin m → ℝ) (t : ℝ) (i : Fin m) : ℝ :=
  rationalTimeEvaluation x t (originalPowerCoordinatePolynomial p c i)

/-- Every specialization starts at the same original identity vector. -/
theorem rational_power_coordinates_zero {m : ℕ}
    (p : Fin m → MvPolynomial (Fin m ⊕ Fin m) ℚ) (c : Fin m → ℚ)
    (x : Fin m → ℝ) : rationalPowerCoordinates p c x 0 = fun i => (c i : ℝ) := by
  funext i
  rw [rationalPowerCoordinates, originalPowerCoordinatePolynomial, map_add]
  have hz (P : Polynomial (MvPolynomial (Fin m) ℚ)) :
      rationalTimeEvaluation x 0 (polynomialDiscretePrimitive P) = 0 := by
    convert! polynomial_discrete_primitive_eval_zero
      (MvPolynomial.aeval x : MvPolynomial (Fin m) ℚ →ₐ[ℚ] ℝ).toRingHom P using 1
  rw [hz, add_zero]
  simp [rationalTimeEvaluation]

/-- The recursively constructed array satisfies its exact forward
recurrence at every real time, before using any group-power identity. -/
theorem rational_power_coordinates_step {m : ℕ}
    (p : Fin m → MvPolynomial (Fin m ⊕ Fin m) ℚ) (c : Fin m → ℚ)
    (x : Fin m → ℝ) (t : ℝ) (i : Fin m) :
    rationalPowerCoordinates p c x (t + 1) i - rationalPowerCoordinates p c x t i =
      MvPolynomial.aeval (Sum.elim x (fun j =>
        if j.val < i.val then rationalPowerCoordinates p c x t j else 0)) (p i) := by
  let a : Fin m → Polynomial (MvPolynomial (Fin m) ℚ) := fun j =>
    if _h : j.val < i.val then originalPowerCoordinatePolynomial p c j else 0
  let P := MvPolynomial.aeval
    (Sum.elim (fun j => Polynomial.C (MvPolynomial.X j)) a) (p i)
  have hc (s : ℝ) : rationalPowerCoordinates p c x s i =
      (c i : ℝ) + rationalTimeEvaluation x s (polynomialDiscretePrimitive P) := by
    rw [rationalPowerCoordinates, originalPowerCoordinatePolynomial, map_add]
    congr 1
    simp [rationalTimeEvaluation]
  rw [hc (t + 1), hc t]
  calc
    _ = rationalTimeEvaluation x (t + 1) (polynomialDiscretePrimitive P) -
        rationalTimeEvaluation x t (polynomialDiscretePrimitive P) := by ring
    _ = rationalTimeEvaluation x t P := by
      convert! polynomial_discrete_primitive_eval_step
        (MvPolynomial.aeval x : MvPolynomial (Fin m) ℚ →ₐ[ℚ] ℝ).toRingHom P t using 1
    _ = _ := by
      rw [show P = MvPolynomial.aeval
        (Sum.elim (fun j => Polynomial.C (MvPolynomial.X j)) a) (p i) from rfl,
        rational_time_substitution]
      apply congrArg (fun z : Fin m ⊕ Fin m → ℝ => MvPolynomial.aeval z (p i))
      funext j
      cases j with
      | inl j => rfl
      | inr j =>
        by_cases hj : j.val < i.val
        · simp only [Sum.elim_inr, a, dif_pos hj, if_pos hj, rationalPowerCoordinates]
        · simp only [Sum.elim_inr, a, dif_neg hj, if_neg hj, map_zero]

/-- Every natural-time value is the actual original group power.
The induction keeps all original element coordinates and multiplication. -/
theorem rational_power_coordinates_nat
    {G : Type*} [Group G] {m : ℕ} (coord : G ≃ (Fin m → ℝ))
    (p : Fin m → MvPolynomial (Fin m ⊕ Fin m) ℚ)
    (hjoint : ∀ g h i, coord (g * h) i = MvPolynomial.aeval (Sum.elim (coord g) (coord h)) (p i))
    (q : G → Fin m → MvPolynomial (Fin m) ℝ)
    (htri : ∀ g u i, coord (g * u) i = coord u i + MvPolynomial.aeval (coord u) (q g i))
    (hlow : ∀ g i d, d ∈ (q g i).support → ∀ j ∈ d.support, j.val < i.val)
    (c : Fin m → ℚ) (hc : coord 1 = fun j => (c j : ℝ)) (g : G) (n : ℕ) :
    rationalPowerCoordinates p c (coord g) (n : ℝ) = coord (g ^ n) := by
  induction n with
  | zero => simpa only [Nat.cast_zero, pow_zero, hc] using rational_power_coordinates_zero p c (coord g)
  | succ n ih =>
    funext i
    let y : Fin m → ℝ := fun j => if j.val < i.val then coord (g ^ n) j else 0
    have hprefix : MvPolynomial.aeval y (q g i) = MvPolynomial.aeval (coord (g ^ n)) (q g i) :=
      polynomial_eval_eq_of_prefix i (q g i) (hlow g i) y (coord (g ^ n))
        (fun j hj => if_pos hj)
    have hp := hjoint g (coord.symm y) i
    rw [htri, Equiv.apply_symm_apply,
      show y i = 0 from if_neg (lt_irrefl _), zero_add, hprefix] at hp
    have hs := rational_power_coordinates_step p c (coord g) (n : ℝ) i
    rw [ih] at hs
    change rationalPowerCoordinates p c (coord g) ((n : ℝ) + 1) i - coord (g ^ n) i =
      MvPolynomial.aeval (Sum.elim (coord g) y) (p i) at hs
    rw [← hp] at hs
    rw [Nat.cast_add, Nat.cast_one, pow_succ', htri]
    linarith only [hs]

/-- Interpret the same polynomial power coordinates in the original group. -/
def originalPowerPath {G : Type*} {m : ℕ} (coord : G ≃ (Fin m → ℝ))
    (p : Fin m → MvPolynomial (Fin m ⊕ Fin m) ℚ) (c : Fin m → ℚ)
    (g : G) (t : ℝ) : G := coord.symm (rationalPowerCoordinates p c (coord g) t)

/-- The original power path agrees with all original natural powers. -/
theorem original_power_path_nat
    {G : Type*} [Group G] {m : ℕ} (coord : G ≃ (Fin m → ℝ))
    (p : Fin m → MvPolynomial (Fin m ⊕ Fin m) ℚ)
    (hjoint : ∀ g h i, coord (g * h) i = MvPolynomial.aeval (Sum.elim (coord g) (coord h)) (p i))
    (q : G → Fin m → MvPolynomial (Fin m) ℝ)
    (htri : ∀ g u i, coord (g * u) i = coord u i + MvPolynomial.aeval (coord u) (q g i))
    (hlow : ∀ g i d, d ∈ (q g i).support → ∀ j ∈ d.support, j.val < i.val)
    (c : Fin m → ℚ) (hc : coord 1 = fun j => (c j : ℝ)) (g : G) (n : ℕ) :
    originalPowerPath coord p c g (n : ℝ) = g ^ n := by
  apply coord.injective
  simpa only [originalPowerPath, Equiv.apply_symm_apply] using
    rational_power_coordinates_nat coord p hjoint q htri hlow c hc g n

/-- Each actual power-path coordinate is a real time polynomial. -/
theorem original_power_path_polynomial_eval
    {G : Type*} {m : ℕ} (coord : G ≃ (Fin m → ℝ))
    (p : Fin m → MvPolynomial (Fin m ⊕ Fin m) ℚ) (c : Fin m → ℚ)
    (g : G) (t : ℝ) (i : Fin m) :
    coord (originalPowerPath coord p c g t) i =
      ((originalPowerCoordinatePolynomial p c i).map (MvPolynomial.aeval (coord g)).toRingHom).eval t := by
  simp only [originalPowerPath, Equiv.apply_symm_apply, rationalPowerCoordinates, Polynomial.eval_map]
  rfl

end GMZP0
