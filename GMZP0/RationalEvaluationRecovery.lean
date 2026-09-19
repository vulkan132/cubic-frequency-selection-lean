import GMZP0.ObservationRealBasis
import GMZP0.ObservationCoefficientRecovery
import GMZP0.ObservationTopology

/-! Rational recovery of actual observation coefficients from determining
original integer points. Real observations and their coefficients remain
unrestricted; rationality belongs to the fixed recovery matrix only. -/
noncomputable section
open Module MvPolynomial
namespace GMZP0

/-- Rational evaluation followed by the real embedding equals evaluation
at the same embedded rational coordinates. -/
theorem rational_polynomial_eval_cast {sigma : Type*}
    (P : MvPolynomial sigma ℚ) (z : sigma → ℚ) :
    (MvPolynomial.eval z P : ℝ) = MvPolynomial.aeval (fun i => (z i : ℝ)) P := by
  induction P using MvPolynomial.induction_on with
  | C q => simp
  | add P Q hP hQ => simp only [map_add, Rat.cast_add, hP, hQ]
  | mul_X P i hP => simp only [map_mul, MvPolynomial.eval_X, Rat.cast_mul,
      MvPolynomial.aeval_X, hP]

variable {G iota : Type*} [Group G] [Fintype iota]

/-- Rational values of the actual basis at determining actual points give
one rational recovery matrix for every original real observation. -/
theorem observation_rational_recovery_of_values
    (V : ObservationModule G) (b : Basis iota ℝ V.space)
    {n : ℕ} (u : Fin n → G) (B : Fin n → iota → ℚ)
    (hB : ∀ k j, b j (u k) = (B k j : ℝ))
    (hsep : ∀ F : V.space, (∀ k, F (u k) = 0) → F = 0) :
    ∃ A : iota → Fin n → ℚ, ∀ F : V.space, ∀ i,
      b.equivFun F i = ∑ k, (A i k : ℝ) * F (u k) := by
  classical
  let ER : V.space →ₗ[ℝ] (Fin n → ℝ) := LinearMap.pi fun k => observationEvaluation V (u k)
  have hER : LinearMap.ker ER = ⊥ := by
    apply LinearMap.ker_eq_bot.mpr
    intro F Q he
    apply sub_eq_zero.mp
    apply hsep
    intro k
    exact sub_eq_zero.mpr (congrFun he k)
  have hr := b.linearIndependent.map' ER hER
  have he : ER ∘ b = fun j => algebraMap ℚ ℝ ∘ (fun k => B k j) := by
    funext j k
    exact hB k j
  rw [he] at hr
  have hq : LinearIndependent ℚ (fun j k => B k j) :=
    (linearIndependent_algebraMap_comp_iff (R := ℚ) (S := ℝ)).mp hr
  let E := Fintype.linearCombination ℚ (fun j k => B k j)
  have hE : LinearMap.ker E = ⊥ :=
    LinearMap.ker_eq_bot.mpr hq.fintypeLinearCombination_injective
  let L := E.leftInverse
  let A : iota → Fin n → ℚ := fun i k => L (Pi.single k 1) i
  have hL (v : Fin n → ℚ) (i : iota) : L v i = ∑ k, A i k * v k := by
    have hv : v = ∑ k, v k • Pi.single k (1 : ℚ) := by
      ext k
      simp [Pi.single_apply]
    conv_lhs => rw [hv]
    simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  have hAB (i j : iota) : ∑ k, A i k * B k j = if i = j then 1 else 0 := by
    have hj := congrFun (LinearMap.leftInverse_apply_of_inj hE (Pi.single j 1)) i
    change L (E (Pi.single j 1)) i = _ at hj
    rw [hL] at hj
    simpa [E, Fintype.linearCombination_apply_single, Pi.single_apply, eq_comm] using hj
  have hABR (i j : iota) : ∑ k, (A i k : ℝ) * (B k j : ℝ) = if i = j then 1 else 0 := by
    have h := congrArg (fun x : ℚ => (x : ℝ)) (hAB i j)
    simpa only [Rat.cast_sum, Rat.cast_mul, apply_ite, Rat.cast_one, Rat.cast_zero] using h
  refine ⟨A, ?_⟩
  intro F i
  simp_rw [observation_evaluation_basis V b F, hB, Finset.mul_sum]
  rw [Finset.sum_comm]
  calc
    b.equivFun F i = ∑ j, b.equivFun F j * (if i = j then (1 : ℝ) else 0) := by simp
    _ = ∑ j, ∑ k, (A i k : ℝ) * (b.equivFun F j * (B k j : ℝ)) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [← hABR, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      ring

/-- A rational polynomial basis and the full original integer coordinate
grid produce actual integer points and a rational recovery matrix before
all unrestricted real observation coefficients. -/
theorem observation_rational_recovery_on_integer_points
    {sigma : Type*} (V : ObservationModule G) (Gamma : Subgroup G)
    (b : Basis iota ℝ V.space) (coord : G → sigma → ℝ)
    (hint : ∀ gamma : Gamma, ∃ z : sigma → ℤ, coord gamma = fun i => (z i : ℝ))
    (hcover : ∀ z : sigma → ℤ, ∃ gamma : Gamma, coord gamma = fun i => (z i : ℝ))
    (P : iota → MvPolynomial sigma ℚ)
    (hP : ∀ j g, b j g = MvPolynomial.aeval (coord g) (P j)) :
    ∃ n : ℕ, n ≤ Module.finrank ℝ V.space ∧ ∃ u : Fin n → Gamma,
      ∃ z : Fin n → sigma → ℤ, (∀ k, coord (u k) = fun s => (z k s : ℝ)) ∧
      ∃ A : iota → Fin n → ℚ, ∀ F : V.space, ∀ i,
        b.equivFun F i = ∑ k, (A i k : ℝ) * F (u k) := by
  let : FiniteDimensional ℝ V.space := b.finiteDimensional_of_finite
  have hsep := observation_integer_points_separate V Gamma coord hcover
    (observation_representatives_of_rational_basis V b coord P hP)
  obtain ⟨n, hn, u, hu⟩ := observation_finite_determining_points V Gamma hsep
  choose z hz using fun k => hint (u k)
  let B : Fin n → iota → ℚ := fun k j => MvPolynomial.eval (fun s => (z k s : ℚ)) (P j)
  have hB (k : Fin n) (j : iota) : b j (u k) = (B k j : ℝ) := by
    rw [hP, hz]
    simp only [B, rational_polynomial_eval_cast, Rat.cast_intCast]
  obtain ⟨A, hA⟩ := observation_rational_recovery_of_values V b (fun k => u k) B hB hu
  exact ⟨n, hn, u, z, hz, A, hA⟩

end GMZP0
