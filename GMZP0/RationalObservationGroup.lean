import GMZP0.RationalObservationTranslation
import GMZP0.ObservationFullCoordinates

/-! The actual semidirect observation group has a rational joint
polynomial law, derived from the original rational group and basis data. -/
noncomputable section
open Module MvPolynomial
namespace GMZP0
variable {sigma iota : Type*} [Fintype iota]

/-- Rational polynomials for the actual base and fiber multiplication.
The translating base is the second factor, not the first. -/
def rationalObservationProductPolynomial
    (p : sigma → MvPolynomial (sigma ⊕ sigma) ℚ)
    (T : iota → iota → MvPolynomial sigma ℚ) (s : sigma ⊕ iota) :
    MvPolynomial ((sigma ⊕ iota) ⊕ (sigma ⊕ iota)) ℚ :=
  match s with
  | Sum.inl s => MvPolynomial.aeval
      (Sum.elim (fun j => X (Sum.inl (Sum.inl j))) (fun j => X (Sum.inr (Sum.inl j)))) (p s)
  | Sum.inr i => X (Sum.inr (Sum.inr i)) + ∑ j, X (Sum.inl (Sum.inr j)) *
      MvPolynomial.aeval (fun s => X (Sum.inr (Sum.inl s))) (T i j)

variable {G : Type*} [Group G] [TopologicalSpace G]

/-- The displayed rational formula is the original multiplication on all
original elements, with unrestricted real fiber coefficients. -/
theorem rational_observation_product_polynomial_eval
    (V : ObservationModule G) (coord : G ≃ₜ (sigma → ℝ)) (b : Basis iota ℝ V.space)
    (p : sigma → MvPolynomial (sigma ⊕ sigma) ℚ)
    (hgroup : ∀ g h s, coord (g * h) s = MvPolynomial.aeval (Sum.elim (coord g) (coord h)) (p s))
    (T : iota → iota → MvPolynomial sigma ℚ)
    (hT : ∀ g j i, b.equivFun (observationTranslate V g (b j)) i = MvPolynomial.aeval (coord g) (T i j))
    (a e : ObservationGroup V) (s : sigma ⊕ iota) :
    observationFullCoordinates V coord b (a * e) s =
      MvPolynomial.aeval (Sum.elim (observationFullCoordinates V coord b a)
        (observationFullCoordinates V coord b e)) (rationalObservationProductPolynomial p T s) := by
  classical
  cases s with
  | inl s =>
    change coord (a.base * e.base) s = _
    rw [hgroup]
    simp only [rationalObservationProductPolynomial, MvPolynomial.comp_aeval_apply]
    apply congrArg (fun v : (sigma ⊕ sigma) → ℝ => MvPolynomial.aeval v (p s))
    funext j
    cases j <;> simp [observation_full_coordinates_base]
  | inr i =>
    have hlin : b.equivFun (observationTranslate V e.base a.obs) i =
        ∑ j, b.equivFun a.obs j * MvPolynomial.aeval (coord e.base) (T i j) := by
      have he := congrArg (fun F => b.equivFun (observationTranslate V e.base F) i)
        (b.sum_equivFun a.obs)
      simpa only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hT] using he.symm
    change b.equivFun (observationTranslate V e.base a.obs + e.obs) i = _
    simp only [map_add, Pi.add_apply, hlin, rationalObservationProductPolynomial,
      map_sum, map_mul, MvPolynomial.aeval_X, MvPolynomial.comp_aeval_apply,
      Sum.elim_inl, Sum.elim_inr, observation_full_coordinates_base, observation_full_coordinates_fiber]
    rw [add_comm]

/-- A single rational polynomial array represents actual H multiplication
from original base and basis data. Rationality of H is not an extra premise. -/
theorem observation_group_rational_polynomial_presentation
    (V : ObservationModule G) (Gamma : Subgroup G)
    (coord : G ≃ₜ (sigma → ℝ)) (b : Basis iota ℝ V.space)
    (hint : ∀ gamma : Gamma, ∃ z : sigma → ℤ, coord gamma = fun i => (z i : ℝ))
    (hcover : ∀ z : sigma → ℤ, ∃ gamma : Gamma, coord gamma = fun i => (z i : ℝ))
    (p : sigma → MvPolynomial (sigma ⊕ sigma) ℚ)
    (hgroup : ∀ g h s, coord (g * h) s = MvPolynomial.aeval (Sum.elim (coord g) (coord h)) (p s))
    (P : iota → MvPolynomial sigma ℚ)
    (hP : ∀ j g, b j g = MvPolynomial.aeval (coord g) (P j)) :
    ∃ Q : (sigma ⊕ iota) → MvPolynomial ((sigma ⊕ iota) ⊕ (sigma ⊕ iota)) ℚ,
      ∀ a e : ObservationGroup V, ∀ s,
        observationFullCoordinates V coord b (a * e) s =
          MvPolynomial.aeval (Sum.elim (observationFullCoordinates V coord b a)
            (observationFullCoordinates V coord b e)) (Q s) := by
  obtain ⟨T, hT⟩ := observation_rational_translation_matrix V Gamma b coord hint hcover p hgroup P hP
  exact ⟨rationalObservationProductPolynomial p T,
    rational_observation_product_polynomial_eval V coord b p hgroup T hT⟩

end GMZP0
