import GMZP0.OriginalCoordinateVelocity
import GMZP0.RationalTriangularFlow
import GMZP0.OneParameterTranslation

/-! Construct the actual original base subgroup for every coordinate
tangent. The original group law follows from its strictly triangular
differential equation and associativity, not from the word exponential. -/
noncomputable section
namespace GMZP0

/-- The fixed rational polynomial flow interpreted in the original group. -/
def originalBaseOneParameter {G : Type*} {m : ℕ} (coord : G ≃ (Fin m → ℝ))
    (p : Fin m → MvPolynomial (Fin m ⊕ Fin m) ℚ) (c : Fin m → ℚ)
    (v : Fin m → ℝ) (t : ℝ) : G :=
  coord.symm (rationalTriangularFlow (originalVelocityPolynomial p c) c v t)

section
variable {G : Type*} [Group G] {m : ℕ} (coord : G ≃ (Fin m → ℝ))
    (p : Fin m → MvPolynomial (Fin m ⊕ Fin m) ℚ)
    (hjoint : ∀ g h i, coord (g * h) i = MvPolynomial.aeval (Sum.elim (coord g) (coord h)) (p i))
    (q : G → Fin m → MvPolynomial (Fin m) ℝ)
    (htri : ∀ g u i, coord (g * u) i = coord u i + MvPolynomial.aeval (coord u) (q g i))
    (hlow : ∀ g i d, d ∈ (q g i).support → ∀ j ∈ d.support, j.val < i.val)
    (c : Fin m → ℚ) (hc : coord 1 = fun j => (c j : ℝ))

include hc in
/-- The constructed path starts at the actual original identity. -/
theorem original_base_one_parameter_zero (v : Fin m → ℝ) :
    originalBaseOneParameter coord p c v 0 = 1 := by
  apply coord.injective
  simpa only [originalBaseOneParameter, Equiv.apply_symm_apply, hc] using
    rational_triangular_flow_zero (originalVelocityPolynomial p c) c v

include hjoint htri hlow hc in
/-- The original strict triangular law supplies the prefix condition
for the same rational velocity polynomial, uniformly in all tangents. -/
theorem original_velocity_polynomial_prefix (v : Fin m → ℝ)
    (i : Fin m) (x y : Fin m → ℝ) (hxy : ∀ j, j.val < i.val → x j = y j) :
    MvPolynomial.aeval (Sum.elim v x) (originalVelocityPolynomial p c i) =
      MvPolynomial.aeval (Sum.elim v y) (originalVelocityPolynomial p c i) := by
  rw [original_velocity_polynomial_eval, original_velocity_polynomial_eval]
  exact original_coordinate_velocity_prefix coord p hjoint q htri hlow _ v hc i x y hxy

include hjoint htri hlow hc in
/-- The constructed path solves the actual original coordinate equation
for every real tangent and every real time. -/
theorem original_base_one_parameter_hasDerivAt (v : Fin m → ℝ) (t : ℝ) (i : Fin m) :
    HasDerivAt (fun s => coord (originalBaseOneParameter coord p c v s) i)
      (originalCoordinateVelocity p (fun j => (c j : ℝ)) v
        (coord (originalBaseOneParameter coord p c v t)) i) t := by
  simp only [originalBaseOneParameter, Equiv.apply_symm_apply]
  rw [← original_velocity_polynomial_eval]
  exact rational_triangular_flow_hasDerivAt (originalVelocityPolynomial p c) c
    (original_velocity_polynomial_prefix coord p hjoint q htri hlow c hc) v t i

include hjoint htri hlow hc in
/-- Its initial derivative is every specified original coordinate
tangent, rather than a supplied path-existence hypothesis. -/
theorem original_base_one_parameter_tangent (v : Fin m → ℝ) (i : Fin m) :
    HasDerivAt (fun s => coord (originalBaseOneParameter coord p c v s) i) (v i) 0 := by
  have hd := original_base_one_parameter_hasDerivAt coord p hjoint q htri hlow c hc v 0 i
  rw [original_base_one_parameter_zero coord p c hc v, hc,
    original_coordinate_velocity_identity coord p hjoint _ v hc] at hd
  exact hd

include hjoint htri hlow hc in
set_option backward.isDefEq.respectTransparency false in
/-- Uniqueness of the actual triangular differential equation proves
the original subgroup law at every pair of real times. -/
theorem original_base_one_parameter_add (v : Fin m → ℝ) (s t : ℝ) :
    originalBaseOneParameter coord p c v (s + t) =
      originalBaseOneParameter coord p c v s * originalBaseOneParameter coord p c v t := by
  let gamma := originalBaseOneParameter coord p c v
  let F := originalCoordinateVelocity p (fun j => (c j : ℝ)) v
  have hd (a : ℝ) (i : Fin m) : HasDerivAt (fun b => coord (gamma b) i) (F (coord (gamma a)) i) a :=
    original_base_one_parameter_hasDerivAt coord p hjoint q htri hlow c hc v a i
  have hshift (a : ℝ) (i : Fin m) :
      HasDerivAt (fun b => coord (gamma (b + t)) i) (F (coord (gamma (a + t))) i) a :=
    (hd (a + t) i).comp_add_const a t
  have hright (a : ℝ) (i : Fin m) :
      HasDerivAt (fun b => coord (gamma b * gamma t) i) (F (coord (gamma a * gamma t)) i) a := by
    have hr := original_right_translate_hasDerivAt coord p hjoint gamma
      (F (coord (gamma a))) a (hd a) (gamma t) i
    rw [original_coordinate_velocity_right_translate coord p hjoint _ v hc] at hr
    exact hr
  have hz : (fun b => coord (gamma (b + t))) 0 = (fun b => coord (gamma b * gamma t)) 0 := by
    simp only [zero_add]
    rw [show gamma 0 = 1 from original_base_one_parameter_zero coord p c hc v, one_mul]
  have he := triangular_differential_solution_unique F
    (fun i x y hxy => original_coordinate_velocity_prefix coord p hjoint q htri hlow _ v hc i x y hxy)
    (fun b => coord (gamma (b + t))) (fun b => coord (gamma b * gamma t)) hshift hright hz s
  exact coord.injective he

include hjoint hc in
set_option backward.isDefEq.respectTransparency false in
/-- Every actual base subgroup with the specified initial coordinate
tangent satisfies the same original equation at all real times. -/
theorem original_base_subgroup_hasDerivAt
    (eta : ℝ → G) (hadd : ∀ s t, eta (s + t) = eta s * eta t)
    (v : Fin m → ℝ) (hv : ∀ i, HasDerivAt (fun t => coord (eta t) i) (v i) 0)
    (t : ℝ) (i : Fin m) :
    HasDerivAt (fun s => coord (eta s) i)
      (originalCoordinateVelocity p (fun j => (c j : ℝ)) v (coord (eta t)) i) t := by
  have hd := original_right_translate_hasDerivAt coord p hjoint eta v 0 hv (eta t) i
  rw [one_parameter_zero eta hadd, hc] at hd
  have hz : HasDerivAt (fun s => coord (eta s * eta t) i)
      (originalCoordinateVelocity p (fun j => (c j : ℝ)) v (coord (eta t)) i) (t - t) := by
    simpa only [sub_self, originalCoordinateVelocity] using hd
  have hs := hz.comp_sub_const t t
  convert! hs using 1
  funext s
  rw [← hadd, sub_add_cancel]

include hjoint htri hlow hc in
/-- The constructed path is unique among all actual original subgroup
paths with that initial tangent; the base path is no longer an input. -/
theorem original_base_one_parameter_unique
    (v : Fin m → ℝ) (eta : ℝ → G)
    (hadd : ∀ s t, eta (s + t) = eta s * eta t)
    (hv : ∀ i, HasDerivAt (fun t => coord (eta t) i) (v i) 0) :
    ∀ t, eta t = originalBaseOneParameter coord p c v t := by
  have he := triangular_differential_solution_unique
    (originalCoordinateVelocity p (fun j => (c j : ℝ)) v)
    (fun i x y hxy => original_coordinate_velocity_prefix coord p hjoint q htri hlow _ v hc i x y hxy)
    (fun t => coord (eta t)) (fun t => coord (originalBaseOneParameter coord p c v t))
    (original_base_subgroup_hasDerivAt coord p hjoint c hc eta hadd v hv)
    (original_base_one_parameter_hasDerivAt coord p hjoint q htri hlow c hc v)
    (by rw [one_parameter_zero eta hadd, original_base_one_parameter_zero coord p c hc v])
  exact fun t => coord.injective (he t)

include hjoint htri hlow hc in
set_option backward.isDefEq.respectTransparency false in
/-- Rescaling the full original tangent is exactly rescaling real time
in its unique actual subgroup, including zero and negative scalars. -/
theorem original_base_one_parameter_smul (a : ℝ) (v : Fin m → ℝ) (t : ℝ) :
    originalBaseOneParameter coord p c (a • v) t =
      originalBaseOneParameter coord p c v (a * t) := by
  let eta : ℝ → G := fun s => originalBaseOneParameter coord p c v (a * s)
  have hadd (s u : ℝ) : eta (s + u) = eta s * eta u := by
    dsimp only [eta]
    rw [mul_add]
    exact original_base_one_parameter_add coord p hjoint q htri hlow c hc v (a * s) (a * u)
  have hv (i : Fin m) : HasDerivAt (fun s => coord (eta s) i) ((a • v) i) 0 := by
    have hs : HasDerivAt (fun s => coord (originalBaseOneParameter coord p c v s) i)
        (v i) (a * 0) := by
      simpa only [mul_zero] using original_base_one_parameter_tangent coord p hjoint q htri hlow c hc v i
    have ha : HasDerivAt (fun s : ℝ => a * s) a 0 := by
      convert! (hasDerivAt_id (0 : ℝ)).const_mul a using 1
      simp
    convert! hs.comp 0 ha using 1
    simp only [Pi.smul_apply, smul_eq_mul, mul_comm]
  exact (original_base_one_parameter_unique coord p hjoint q htri hlow c hc (a • v) eta hadd hv t).symm

omit [Group G] in
/-- One rational array fixed before all real tangents gives the
time-one value. Surjectivity and a logarithmic inverse are separate. -/
theorem original_base_one_parameter_one (v : Fin m → ℝ) (i : Fin m) :
    coord (originalBaseOneParameter coord p c v 1) i =
      MvPolynomial.aeval v
        ((rationalTriangularFlowPolynomial (originalVelocityPolynomial p c) c i).eval 1) := by
  simpa only [originalBaseOneParameter, Equiv.apply_symm_apply] using
    rational_triangular_flow_one (originalVelocityPolynomial p c) c v i

end
end GMZP0
