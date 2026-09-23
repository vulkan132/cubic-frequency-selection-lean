import GMZP0.RationalTriangularInverse
import GMZP0.RationalObservationLatticeCoordinates

/-! Rational coordinate formulas for the actual observation inverse,
using the original convention (g,F)^-1=(g^-1,-F composed with L_(g^-1)). -/
noncomputable section
open Module MvPolynomial
namespace GMZP0
variable {sigma iota : Type*} [Fintype iota]

/-- Substitute the original base inverse in the actual translation
matrix and keep the original negative fiber pullback. -/
def rationalObservationInversePolynomial
    (r : sigma → MvPolynomial sigma ℚ) (T : iota → iota → MvPolynomial sigma ℚ)
    (s : sigma ⊕ iota) : MvPolynomial (sigma ⊕ iota) ℚ :=
  match s with
  | Sum.inl s => MvPolynomial.aeval (fun j => X (Sum.inl j)) (r s)
  | Sum.inr i => -(∑ j, X (Sum.inr j) * MvPolynomial.aeval
      (fun s => MvPolynomial.aeval (fun k => X (Sum.inl k)) (r s)) (T i j))

variable {G : Type*} [Group G] [TopologicalSpace G]

/-- The rational formula gives the actual H inverse for every original
group point and every unrestricted real observation. -/
theorem rational_observation_inverse_polynomial_eval
    (V : ObservationModule G) (coord : G ≃ₜ (sigma → ℝ)) (b : Basis iota ℝ V.space)
    (r : sigma → MvPolynomial sigma ℚ)
    (hr : ∀ g s, coord g⁻¹ s = MvPolynomial.aeval (coord g) (r s))
    (T : iota → iota → MvPolynomial sigma ℚ)
    (hT : ∀ g j i, b.equivFun (observationTranslate V g (b j)) i = MvPolynomial.aeval (coord g) (T i j))
    (a : ObservationGroup V) (s : sigma ⊕ iota) :
    observationFullCoordinates V coord b a⁻¹ s =
      MvPolynomial.aeval (observationFullCoordinates V coord b a)
        (rationalObservationInversePolynomial r T s) := by
  classical
  cases s with
  | inl s =>
    change coord a.base⁻¹ s = _
    rw [hr]
    simp only [rationalObservationInversePolynomial, MvPolynomial.comp_aeval_apply,
      MvPolynomial.aeval_X, observation_full_coordinates_base]
  | inr i =>
    have hlin : b.equivFun (observationTranslate V a.base⁻¹ a.obs) i =
        ∑ j, b.equivFun a.obs j * MvPolynomial.aeval (coord a.base⁻¹) (T i j) := by
      have he := congrArg (fun F => b.equivFun (observationTranslate V a.base⁻¹ F) i)
        (b.sum_equivFun a.obs)
      simpa only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hT] using he.symm
    change b.equivFun (-observationTranslate V a.base⁻¹ a.obs) i = _
    simp only [map_neg, Pi.neg_apply, hlin, rationalObservationInversePolynomial,
      map_sum, map_mul, MvPolynomial.aeval_X, MvPolynomial.comp_aeval_apply,
      observation_full_coordinates_base, observation_full_coordinates_fiber]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    congr 1
    apply congrArg (fun v : sigma → ℝ => MvPolynomial.aeval v (T i j))
    funext s
    exact hr a.base s

/-- From the original rational joint law, strict triangular left law and
integer grid, construct the rational inverse formula on the original H. -/
theorem observation_group_rational_inverse_presentation
    {m : ℕ} (V : ObservationModule G) (Gamma : Subgroup G)
    (coord : G ≃ₜ (Fin m → ℝ)) (b : Basis iota ℝ V.space)
    (hint : ∀ gamma : Gamma, ∃ z : Fin m → ℤ, coord gamma = fun i => (z i : ℝ))
    (hcover : ∀ z : Fin m → ℤ, ∃ gamma : Gamma, coord gamma = fun i => (z i : ℝ))
    (p : Fin m → MvPolynomial (Fin m ⊕ Fin m) ℚ)
    (hjoint : ∀ g h s, coord (g * h) s = MvPolynomial.aeval (Sum.elim (coord g) (coord h)) (p s))
    (q : G → Fin m → MvPolynomial (Fin m) ℝ)
    (htri : ∀ g u s, coord (g * u) s = coord u s + MvPolynomial.aeval (coord u) (q g s))
    (hlow : ∀ g s d, d ∈ (q g s).support → ∀ j ∈ d.support, j.val < s.val)
    (P : iota → MvPolynomial (Fin m) ℚ)
    (hP : ∀ j g, b j g = MvPolynomial.aeval (coord g) (P j)) :
    ∃ R : (Fin m ⊕ iota) → MvPolynomial (Fin m ⊕ iota) ℚ, ∀ a : ObservationGroup V, ∀ s,
      observationFullCoordinates V coord b a⁻¹ s =
        MvPolynomial.aeval (observationFullCoordinates V coord b a) (R s) := by
  obtain ⟨r, hr⟩ := original_group_rational_inverse_polynomials coord.toEquiv Gamma hint p hjoint q htri hlow
  obtain ⟨T, hT⟩ := observation_rational_translation_matrix V Gamma b coord hint hcover p hjoint P hP
  exact ⟨rationalObservationInversePolynomial r T,
    rational_observation_inverse_polynomial_eval V coord b r hr T hT⟩

end GMZP0
