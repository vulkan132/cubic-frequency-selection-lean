import GMZP0.ObservationInfinitesimal
import GMZP0.RationalObservationFlag

/-! A single finite nilpotency exponent for the actual translation
differentials, constructed before every real tangent and every original
observation. -/
noncomputable section
open Module MvPolynomial
namespace GMZP0

/-- Strict lowering of a finite original flag kills the actual K-th
power of an endomorphism, not merely the induced quotient operators. -/
theorem linear_operator_pow_zero_of_flag
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (flag : ℕ → Submodule ℝ E) (K : ℕ)
    (hzero : flag 0 = ⊥) (htop : ∀ F : E, F ∈ flag K)
    (D : Module.End ℝ E)
    (hdrop : ∀ n (F : E), F ∈ flag (n + 1) → D F ∈ flag n) :
    D ^ K = 0 := by
  have hpow : ∀ n (F : E), F ∈ flag n → (D ^ n) F = 0 := by
    intro n
    induction n with
    | zero =>
      intro F hF
      rw [hzero] at hF
      have hF0 : F = 0 := hF
      simp [hF0]
    | succ n ih =>
      intro F hF
      rw [pow_succ, Module.End.mul_apply]
      exact ih (D F) (hdrop n F hF)
  exact LinearMap.ext fun F => hpow K F (htop F)

/-- The original fixed rational data derive a rational tangent matrix
and one nilpotency exponent, with an actual pointwise derivative identity
for every differentiable original curve through the identity. Neither the
matrix nor its nilpotence is supplied as a premise. -/
theorem original_rational_infinitesimal_translation
    {G iota : Type*} [Group G] [Fintype iota] {m : ℕ}
    (V : ObservationModule G) (Gamma : Subgroup G)
    (coord : G ≃ (Fin m → ℝ)) (b : Basis iota ℝ V.space)
    (hint : ∀ gamma : Gamma, ∃ z : Fin m → ℤ, coord gamma = fun i => (z i : ℝ))
    (hcover : ∀ z : Fin m → ℤ, ∃ gamma : Gamma, coord gamma = fun i => (z i : ℝ))
    (p : Fin m → MvPolynomial (Fin m ⊕ Fin m) ℚ)
    (hjoint : ∀ g h i, coord (g * h) i = MvPolynomial.aeval (Sum.elim (coord g) (coord h)) (p i))
    (q : G → Fin m → MvPolynomial (Fin m) ℝ)
    (htri : ∀ g u i, coord (g * u) i = coord u i + MvPolynomial.aeval (coord u) (q g i))
    (hlow : ∀ g i d, d ∈ (q g i).support → ∀ j ∈ d.support, j.val < i.val)
    (P : iota → MvPolynomial (Fin m) ℚ)
    (hP : ∀ j g, b j g = MvPolynomial.aeval (coord g) (P j)) :
    ∃ K : ℕ, 0 < K ∧ ∃ A : iota → iota → Fin m → ℚ,
      (∀ v : Fin m → ℝ, (observationCoordinateDifferential V b A v) ^ K = 0) ∧
      (∀ (gamma : ℝ → G) (v : Fin m → ℝ), gamma 0 = 1 →
        (∀ s, HasDerivAt (fun t => coord (gamma t) s) (v s) 0) →
        ∀ (F : V.space) (u : G), HasDerivAt (fun t => F (gamma t * u))
          (observationCoordinateDifferential V b A v F u) 0) := by
  obtain ⟨T, hT⟩ := observation_rational_translation_matrix V Gamma b coord hint hcover p hjoint P hP
  obtain ⟨z, hz⟩ := hint ⟨1, Gamma.one_mem⟩
  let c : Fin m → ℚ := fun s => z s
  have hc : coord 1 = fun s => (c s : ℝ) := by simpa [c] using hz
  obtain ⟨K, hK, flag, hzero, htop, hdrop⟩ :=
    original_rational_observation_flag V b coord p hjoint q htri hlow P hP
  refine ⟨K, hK, (fun i j s => MvPolynomial.eval c (MvPolynomial.pderiv s (T i j))), ?_, ?_⟩
  · intro v
    apply linear_operator_pow_zero_of_flag flag K hzero htop
    intro n F hF
    exact observation_coordinate_differential_lowers V b coord T hT c hc
      (flag (n + 1)) (flag n) (hdrop n) v F hF
  · intro gamma v hg hv F u
    exact original_translation_pointwise_hasDerivAt V b coord T hT c gamma v
      (by rw [hg]; exact hc) hv F u

end GMZP0
