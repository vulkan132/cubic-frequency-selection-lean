import GMZP0.RationalObservationOperations
import Mathlib.Geometry.Manifold.Algebra.LieGroup
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Analysis.Convex.Contractible

/-! Construct a genuine smooth Lie group in the actual global coordinate
chart from literal rational multiplication and inverse polynomials. The
underlying group and topology are unchanged. -/
noncomputable section
open Module MvPolynomial
open scoped Manifold ContDiff
namespace GMZP0

/-- Rational multivariate polynomial evaluation preserves arbitrary
orders of smoothness of its actual scalar coordinate functions. -/
theorem rational_coordinate_polynomial_contDiff {sigma E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (n : ℕ∞ω)
    (p : MvPolynomial sigma ℚ) (v : E → sigma → ℝ)
    (hv : ∀ i, ContDiff ℝ n (fun x => v x i)) :
    ContDiff ℝ n (fun x => MvPolynomial.aeval (v x) p) := by
  induction p using MvPolynomial.induction_on with
  | C a => simpa using (contDiff_const : ContDiff ℝ n (fun _ : E => (a : ℝ)))
  | add p q hp hq => simpa using hp.add hq
  | mul_X p i hp => simpa using hp.mul (hv i)

/-- The actual single global chart gives a smooth Lie structure whenever
the actual multiplication and inverse have literal rational polynomials. -/
theorem rational_coordinate_lie_group {G sigma : Type*} [Group G]
    [TopologicalSpace G] [Fintype sigma] (coord : G ≃ₜ (sigma → ℝ))
    (p : sigma → MvPolynomial (sigma ⊕ sigma) ℚ)
    (hmul : ∀ g h i, coord (g * h) i = MvPolynomial.aeval (Sum.elim (coord g) (coord h)) (p i))
    (r : sigma → MvPolynomial sigma ℚ)
    (hinv : ∀ g i, coord g⁻¹ i = MvPolynomial.aeval (coord g) (r i)) :
    letI := coord.isOpenEmbedding.singletonChartedSpace
    LieGroup 𝓘(ℝ, sigma → ℝ) ∞ G := by
  let := coord.isOpenEmbedding.singletonChartedSpace
  have hm : IsManifold 𝓘(ℝ, sigma → ℝ) ∞ G := coord.isOpenEmbedding.isManifold_singleton
  have := hm
  have hc : ContMDiff 𝓘(ℝ, sigma → ℝ) 𝓘(ℝ, sigma → ℝ) ∞ coord :=
    contMDiff_isOpenEmbedding coord.isOpenEmbedding
  have hp : ContDiff ℝ ∞ (fun z : (sigma → ℝ) × (sigma → ℝ) =>
      fun i => MvPolynomial.aeval (Sum.elim z.1 z.2) (p i)) := by
    apply contDiff_pi.mpr
    intro i
    apply rational_coordinate_polynomial_contDiff
    intro j
    cases j with
    | inl j => exact (contDiff_apply ℝ ℝ j).comp contDiff_fst
    | inr j => exact (contDiff_apply ℝ ℝ j).comp contDiff_snd
  have hr : ContDiff ℝ ∞ (fun x : sigma → ℝ => fun i => MvPolynomial.aeval x (r i)) := by
    apply contDiff_pi.mpr
    intro i
    apply rational_coordinate_polynomial_contDiff
    intro j
    exact contDiff_apply ℝ ℝ j
  have hmul' : ContMDiff (𝓘(ℝ, sigma → ℝ).prod 𝓘(ℝ, sigma → ℝ))
      𝓘(ℝ, sigma → ℝ) ∞ (fun z : G × G => z.1 * z.2) := by
    apply ContMDiff.of_comp_isOpenEmbedding coord.isOpenEmbedding
    have hh := hp.comp_contMDiff ((hc.comp contMDiff_fst).prodMk_space (hc.comp contMDiff_snd))
    have heq : (coord ∘ fun z : G × G => z.1 * z.2) =
        (fun z : (sigma → ℝ) × (sigma → ℝ) =>
          fun i => MvPolynomial.aeval (Sum.elim z.1 z.2) (p i)) ∘
            (fun z : G × G => (coord z.1, coord z.2)) := by
      funext z i
      exact hmul z.1 z.2 i
    rw [heq]
    exact hh
  have hinv' : ContMDiff 𝓘(ℝ, sigma → ℝ) 𝓘(ℝ, sigma → ℝ) ∞ (fun g : G => g⁻¹) := by
    apply ContMDiff.of_comp_isOpenEmbedding coord.isOpenEmbedding
    have hh := hr.comp_contMDiff hc
    have heq : (coord ∘ fun g : G => g⁻¹) =
        (fun x : sigma → ℝ => fun i => MvPolynomial.aeval x (r i)) ∘ coord := by
      funext g i
      exact hinv g i
    rw [heq]
    exact hh
  exact { toContMDiffMul := { toIsManifold := hm, contMDiff_mul := hmul' }, contMDiff_inv := hinv' }

/-- The actual coordinate homeomorphism also proves contractibility of
the original space, without a replacement underlying group or topology. -/
theorem coordinate_group_contractible {G sigma : Type*} [TopologicalSpace G]
    [Fintype sigma] (coord : G ≃ₜ (sigma → ℝ)) : ContractibleSpace G :=
  coord.contractibleSpace

/-- The original rational base/basis data and strict triangular law
construct a genuine smooth Lie group on the actual observation group. -/
theorem original_observation_coordinate_lie_group
    {G iota : Type*} [Group G] [TopologicalSpace G] [Fintype iota] {m : ℕ}
    (V : ObservationModule G) (Gamma : Subgroup G)
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
    letI := (observationFullCoordinates V coord b).isOpenEmbedding.singletonChartedSpace
    LieGroup 𝓘(ℝ, (Fin m ⊕ iota) → ℝ) ∞ (ObservationGroup V) := by
  obtain ⟨M, hM⟩ := observation_group_rational_polynomial_presentation V Gamma coord b hint hcover p hjoint P hP
  obtain ⟨R, hR⟩ := observation_group_rational_inverse_presentation V Gamma coord b hint hcover p hjoint q htri hlow P hP
  exact rational_coordinate_lie_group (observationFullCoordinates V coord b) M hM R hR

end GMZP0
