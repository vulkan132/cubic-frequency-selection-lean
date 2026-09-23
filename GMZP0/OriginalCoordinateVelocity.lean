import GMZP0.RationalPolynomialDerivative
import GMZP0.TriangularIntegerCell

/-! The actual coordinate velocity of left multiplication, derived from
the original joint group law. Associativity gives right-translation
invariance; the original strict triangular law gives prefix dependence. -/
noncomputable section
open MvPolynomial
namespace GMZP0

/-- The derivative of the original multiplication in its first input.
All first-input tangent coordinates are retained. -/
def coordinateRightDifferential {m : ℕ}
    (p : Fin m → MvPolynomial (Fin m ⊕ Fin m) ℚ)
    (x y v : Fin m → ℝ) (i : Fin m) : ℝ :=
  ∑ j, MvPolynomial.aeval (Sum.elim x y) (MvPolynomial.pderiv (Sum.inl j) (p i)) * v j

/-- The original left-generated velocity at every coordinate point. -/
def originalCoordinateVelocity {m : ℕ}
    (p : Fin m → MvPolynomial (Fin m ⊕ Fin m) ℚ)
    (c v x : Fin m → ℝ) : Fin m → ℝ := coordinateRightDifferential p c x v

set_option backward.isDefEq.respectTransparency false in
/-- Differentiate an actual original right translate of any coordinate
curve, without assuming that curve is a subgroup. -/
theorem original_right_translate_hasDerivAt
    {G : Type*} [Group G] {m : ℕ} (coord : G → Fin m → ℝ)
    (p : Fin m → MvPolynomial (Fin m ⊕ Fin m) ℚ)
    (hjoint : ∀ g h i, coord (g * h) i = MvPolynomial.aeval (Sum.elim (coord g) (coord h)) (p i))
    (gamma : ℝ → G) (v : Fin m → ℝ) (t : ℝ)
    (hv : ∀ i, HasDerivAt (fun s => coord (gamma s) i) (v i) t)
    (u : G) (i : Fin m) :
    HasDerivAt (fun s => coord (gamma s * u) i)
      (coordinateRightDifferential p (coord (gamma t)) (coord u) v i) t := by
  have hx : ∀ j : Fin m ⊕ Fin m,
      HasDerivAt (fun s => Sum.elim (coord (gamma s)) (coord u) j)
        (Sum.elim v (fun _ => 0) j) t := by
    intro j
    cases j with
    | inl j => exact hv j
    | inr j => exact hasDerivAt_const t _
  have hd := rational_polynomial_hasDerivAt (p i)
    (fun s => Sum.elim (coord (gamma s)) (coord u)) (Sum.elim v (fun _ => 0)) t hx
  simpa only [hjoint, coordinateRightDifferential, Fintype.sum_sum_type,
    Sum.elim_inl, Sum.elim_inr, mul_zero, Finset.sum_const_zero, add_zero] using hd

/-- A coordinate tangent line has the prescribed original initial
derivative. It is not asserted to have any subgroup law. -/
theorem original_coordinate_tangent_line
    {G : Type*} [Group G] {m : ℕ} (coord : G ≃ (Fin m → ℝ))
    (c v : Fin m → ℝ) (hc : coord 1 = c) :
    (coord.symm (fun i => c i + (0 : ℝ) * v i) = 1) ∧
      ∀ i, HasDerivAt (fun t => coord (coord.symm (fun j => c j + t * v j)) i) (v i) 0 := by
  constructor
  · apply coord.injective
    simp [hc]
  · intro i
    simp only [Equiv.apply_symm_apply]
    convert! ((hasDerivAt_id (0 : ℝ)).mul_const (v i)).const_add (c i) using 1
    simp

/-- The velocity at the actual identity is the unchanged original
coordinate tangent, even when that identity coordinate is nonzero. -/
theorem original_coordinate_velocity_identity
    {G : Type*} [Group G] {m : ℕ} (coord : G ≃ (Fin m → ℝ))
    (p : Fin m → MvPolynomial (Fin m ⊕ Fin m) ℚ)
    (hjoint : ∀ g h i, coord (g * h) i = MvPolynomial.aeval (Sum.elim (coord g) (coord h)) (p i))
    (c v : Fin m → ℝ) (hc : coord 1 = c) : originalCoordinateVelocity p c v c = v := by
  let a : ℝ → G := fun t => coord.symm (fun j => c j + t * v j)
  obtain ⟨ha, hv⟩ := original_coordinate_tangent_line coord c v hc
  have ha0 : a 0 = 1 := ha
  funext i
  have hd := original_right_translate_hasDerivAt coord p hjoint a v 0 hv 1 i
  simp only [ha0, hc, mul_one] at hd
  exact hd.unique (hv i)

set_option backward.isDefEq.respectTransparency false in
/-- Associativity of the original group gives the exact covariance of
its velocity under every actual original right translation. -/
theorem original_coordinate_velocity_right_translate
    {G : Type*} [Group G] {m : ℕ} (coord : G ≃ (Fin m → ℝ))
    (p : Fin m → MvPolynomial (Fin m ⊕ Fin m) ℚ)
    (hjoint : ∀ g h i, coord (g * h) i = MvPolynomial.aeval (Sum.elim (coord g) (coord h)) (p i))
    (c v : Fin m → ℝ) (hc : coord 1 = c) (g u : G) (i : Fin m) :
    coordinateRightDifferential p (coord g) (coord u)
      (originalCoordinateVelocity p c v (coord g)) i =
      originalCoordinateVelocity p c v (coord (g * u)) i := by
  let a : ℝ → G := fun t => coord.symm (fun j => c j + t * v j)
  obtain ⟨ha, hv⟩ := original_coordinate_tangent_line coord c v hc
  have ha0 : a 0 = 1 := ha
  have hdg (j : Fin m) : HasDerivAt (fun s => coord (a s * g) j)
      (originalCoordinateVelocity p c v (coord g) j) 0 := by
    simpa only [ha0, hc, originalCoordinateVelocity] using
      original_right_translate_hasDerivAt coord p hjoint a v 0 hv g j
  have htwo := original_right_translate_hasDerivAt coord p hjoint
    (fun s => a s * g) (originalCoordinateVelocity p c v (coord g)) 0 hdg u i
  have hone := original_right_translate_hasDerivAt coord p hjoint a v 0 hv (g * u) i
  simp only [ha0, hc, one_mul, mul_assoc] at htwo hone
  exact htwo.unique hone

set_option backward.isDefEq.respectTransparency false in
/-- Differentiating the original strict triangular translation law
preserves prefix dependence. No tangent components are discarded. -/
theorem original_coordinate_velocity_prefix
    {G : Type*} [Group G] {m : ℕ} (coord : G ≃ (Fin m → ℝ))
    (p : Fin m → MvPolynomial (Fin m ⊕ Fin m) ℚ)
    (hjoint : ∀ g h i, coord (g * h) i = MvPolynomial.aeval (Sum.elim (coord g) (coord h)) (p i))
    (q : G → Fin m → MvPolynomial (Fin m) ℝ)
    (htri : ∀ g u i, coord (g * u) i = coord u i + MvPolynomial.aeval (coord u) (q g i))
    (hlow : ∀ g i d, d ∈ (q g i).support → ∀ j ∈ d.support, j.val < i.val)
    (c v : Fin m → ℝ) (hc : coord 1 = c)
    (i : Fin m) (x y : Fin m → ℝ) (hxy : ∀ j, j.val < i.val → x j = y j) :
    originalCoordinateVelocity p c v x i = originalCoordinateVelocity p c v y i := by
  let a : ℝ → G := fun t => coord.symm (fun j => c j + t * v j)
  obtain ⟨ha, hv⟩ := original_coordinate_tangent_line coord c v hc
  have ha0 : a 0 = 1 := ha
  have hd (z : Fin m → ℝ) :
      HasDerivAt (fun t => coord (a t * coord.symm z) i - z i)
        (originalCoordinateVelocity p c v z i) 0 := by
    have h := (original_right_translate_hasDerivAt coord p hjoint a v 0 hv (coord.symm z) i).sub_const (z i)
    convert! h using 1
    simp only [ha0, hc, Equiv.apply_symm_apply, originalCoordinateVelocity]
  have he : (fun t => coord (a t * coord.symm x) i - x i) =
      (fun t => coord (a t * coord.symm y) i - y i) := by
    funext t
    simp only [htri, Equiv.apply_symm_apply, add_sub_cancel_left]
    exact polynomial_eval_eq_of_prefix i (q (a t) i) (hlow (a t) i) x y hxy
  have hx := hd x
  rw [he] at hx
  exact hx.unique (hd y)

/-- One rational polynomial array simultaneously represents every real
tangent and every original coordinate point. -/
def originalVelocityPolynomial {m : ℕ}
    (p : Fin m → MvPolynomial (Fin m ⊕ Fin m) ℚ) (c : Fin m → ℚ)
    (i : Fin m) : MvPolynomial (Fin m ⊕ Fin m) ℚ :=
  ∑ j, MvPolynomial.aeval
    (Sum.elim (fun k => C (c k)) (fun k => X (Sum.inr k)))
    (MvPolynomial.pderiv (Sum.inl j) (p i)) * X (Sum.inl j)

/-- Evaluation of the fixed rational array is the actual original
velocity, with every tangent component and original value retained. -/
theorem original_velocity_polynomial_eval {m : ℕ}
    (p : Fin m → MvPolynomial (Fin m ⊕ Fin m) ℚ) (c : Fin m → ℚ)
    (v x : Fin m → ℝ) (i : Fin m) :
    MvPolynomial.aeval (Sum.elim v x) (originalVelocityPolynomial p c i) =
      originalCoordinateVelocity p (fun j => (c j : ℝ)) v x i := by
  classical
  simp only [originalVelocityPolynomial, map_sum, map_mul,
    MvPolynomial.aeval_X, Sum.elim_inl, MvPolynomial.comp_aeval_apply,
    originalCoordinateVelocity, coordinateRightDifferential]
  apply Finset.sum_congr rfl
  intro j _
  congr 2
  congr 1
  funext k
  cases k <;> simp

end GMZP0
