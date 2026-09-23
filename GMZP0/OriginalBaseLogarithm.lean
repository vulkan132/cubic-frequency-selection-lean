import GMZP0.RationalOriginalPowers
import GMZP0.PolynomialSubgroupExtension
import GMZP0.OriginalBaseEndpoint

/-! A global rational inverse of the actual original time-one map.
The inverse is the initial derivative of the constructed polynomial
power path; neither global surjectivity nor an inverse is supplied. -/
noncomputable section
namespace GMZP0

/-- The rational logarithmic coordinate is the original power-path
coefficient of t, i.e. its derivative at zero. -/
def originalBaseLogPolynomial {m : ℕ}
    (p : Fin m → MvPolynomial (Fin m ⊕ Fin m) ℚ) (c : Fin m → ℚ)
    (i : Fin m) : MvPolynomial (Fin m) ℚ := (originalPowerCoordinatePolynomial p c i).coeff 1

/-- The candidate inverse uses every original element coordinate and
the same fixed rational polynomial array. -/
def originalBaseLogarithm {G : Type*} {m : ℕ} (coord : G ≃ (Fin m → ℝ))
    (p : Fin m → MvPolynomial (Fin m ⊕ Fin m) ℚ) (c : Fin m → ℚ)
    (g : G) (i : Fin m) : ℝ := MvPolynomial.aeval (coord g) (originalBaseLogPolynomial p c i)

set_option backward.isDefEq.respectTransparency false in
/-- The candidate logarithm is exactly the actual power path's
initial original coordinate derivative. -/
theorem original_power_path_tangent
    {G : Type*} {m : ℕ} (coord : G ≃ (Fin m → ℝ))
    (p : Fin m → MvPolynomial (Fin m ⊕ Fin m) ℚ) (c : Fin m → ℚ)
    (g : G) (i : Fin m) :
    HasDerivAt (fun t => coord (originalPowerPath coord p c g t) i)
      (originalBaseLogarithm coord p c g i) 0 := by
  have hd := ((originalPowerCoordinatePolynomial p c i).map
    (MvPolynomial.aeval (coord g)).toRingHom).hasDerivAt 0
  convert! hd using 1
  · funext t
    exact original_power_path_polynomial_eval coord p c g t i
  · simp [originalBaseLogarithm, originalBaseLogPolynomial,
      ← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_derivative]

section
variable {G : Type*} [Group G] {m : ℕ} (coord : G ≃ (Fin m → ℝ))
    (p : Fin m → MvPolynomial (Fin m ⊕ Fin m) ℚ)
    (hjoint : ∀ g h i, coord (g * h) i = MvPolynomial.aeval (Sum.elim (coord g) (coord h)) (p i))
    (q : G → Fin m → MvPolynomial (Fin m) ℝ)
    (htri : ∀ g u i, coord (g * u) i = coord u i + MvPolynomial.aeval (coord u) (q g i))
    (hlow : ∀ g i d, d ∈ (q g i).support → ∀ j ∈ d.support, j.val < i.val)
    (c : Fin m → ℚ) (hc : coord 1 = fun j => (c j : ℝ))

include hjoint htri hlow hc in
/-- The polynomial power path of each original element satisfies
the actual subgroup law for all real parameters. -/
theorem original_power_path_add (g : G) :
    ∀ s t, originalPowerPath coord p c g (s + t) =
      originalPowerPath coord p c g s * originalPowerPath coord p c g t := by
  exact polynomial_curve_subgroup_of_nat_powers coord coord.injective p hjoint
    (originalPowerPath coord p c g) g
    (fun i => (originalPowerCoordinatePolynomial p c i).map (MvPolynomial.aeval (coord g)).toRingHom)
    (original_power_path_polynomial_eval coord p c g)
    (original_power_path_nat coord p hjoint q htri hlow c hc g)

include hjoint htri hlow hc in
/-- Every original group element is recovered from the constructed
logarithmic tangent by the actual time-one map. -/
theorem original_base_time_one_logarithm (g : G) :
    originalBaseOneParameter coord p c (originalBaseLogarithm coord p c g) 1 = g := by
  have hu := original_base_one_parameter_unique coord p hjoint q htri hlow c hc
    (originalBaseLogarithm coord p c g) (originalPowerPath coord p c g)
    (original_power_path_add coord p hjoint q htri hlow c hc g)
    (original_power_path_tangent coord p c g) 1
  have h1 : originalPowerPath coord p c g 1 = g := by
    simpa only [Nat.cast_one, pow_one] using
      original_power_path_nat coord p hjoint q htri hlow c hc g 1
  exact hu.symm.trans h1

include hjoint htri hlow hc in
/-- The same rational logarithm recovers every unrestricted original
tangent from its time-one value; this is the other inverse identity. -/
theorem original_base_logarithm_time_one (v : Fin m → ℝ) :
    originalBaseLogarithm coord p c (originalBaseOneParameter coord p c v 1) = v := by
  apply original_base_time_one_injective coord p hjoint q htri hlow c hc
  exact original_base_time_one_logarithm coord p hjoint q htri hlow c hc _

include hjoint htri hlow hc in
/-- The actual original time-one map is globally bijective. -/
theorem original_base_time_one_bijective :
    Function.Bijective (fun v => originalBaseOneParameter coord p c v 1) := by
  refine ⟨original_base_time_one_injective coord p hjoint q htri hlow c hc, ?_⟩
  exact fun g => ⟨originalBaseLogarithm coord p c g,
    original_base_time_one_logarithm coord p hjoint q htri hlow c hc g⟩

include hjoint htri hlow hc in
/-- The zero tangent has the actual identity as its time-one value. -/
theorem original_base_time_one_zero : originalBaseOneParameter coord p c 0 1 = 1 := by
  have hu := original_base_one_parameter_unique coord p hjoint q htri hlow c hc
    0 (fun _ => (1 : G)) (fun _ _ => (one_mul _).symm)
    (fun i => hasDerivAt_const 0 (coord 1 i)) 1
  exact hu.symm

include hjoint htri hlow hc in
/-- The same fixed rational arrays give a global equivalence between
all original coordinate tangents and the original group, with the
correct identity and the actual subgroup at every real time. -/
theorem original_rational_base_time_one_equiv :
    ∃ E L : Fin m → MvPolynomial (Fin m) ℚ, ∃ e : (Fin m → ℝ) ≃ G,
      (∀ v, e v = originalBaseOneParameter coord p c v 1) ∧
      (∀ g, e.symm g = originalBaseLogarithm coord p c g) ∧
      (∀ v i, coord (e v) i = MvPolynomial.aeval v (E i)) ∧
      (∀ g i, e.symm g i = MvPolynomial.aeval (coord g) (L i)) ∧
      e 0 = 1 ∧ (∀ v t, e (t • v) = originalBaseOneParameter coord p c v t) := by
  let e : (Fin m → ℝ) ≃ G :=
    { toFun := fun v => originalBaseOneParameter coord p c v 1
      invFun := originalBaseLogarithm coord p c
      left_inv := original_base_logarithm_time_one coord p hjoint q htri hlow c hc
      right_inv := original_base_time_one_logarithm coord p hjoint q htri hlow c hc }
  refine ⟨fun i => (rationalTriangularFlowPolynomial (originalVelocityPolynomial p c) c i).eval 1,
    originalBaseLogPolynomial p c, e, fun _ => rfl, fun _ => rfl, ?_, fun _ _ => rfl, ?_, ?_⟩
  · exact original_base_one_parameter_one coord p c
  · exact original_base_time_one_zero coord p hjoint q htri hlow c hc
  · intro v t
    change originalBaseOneParameter coord p c (t • v) 1 = originalBaseOneParameter coord p c v t
    simpa only [mul_one] using original_base_one_parameter_smul coord p hjoint q htri hlow c hc t v 1

end
end GMZP0
