import GMZP0.FiniteObservationEvaluations
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-! Recover the original basis coefficients from finitely many actual
group evaluations. This is exact linear recovery, not a finite test of a
general theorem or a replacement for the original observation functions. -/
noncomputable section
open Module
namespace GMZP0
variable {G iota : Type*} [Group G] [Fintype iota]

/-- One finite family of actual points and one coefficient matrix recover
every original observation, before any unrestricted real coefficients. -/
theorem observation_coefficients_from_finite_values
    (V : ObservationModule G) (b : Basis iota ℝ V.space) :
    ∃ n : ℕ, n ≤ Module.finrank ℝ V.space ∧ ∃ u : Fin n → G,
      ∃ A : iota → Fin n → ℝ, ∀ F : V.space, ∀ i,
        b.equivFun F i = ∑ k, A i k * F (u k) := by
  classical
  let : FiniteDimensional ℝ V.space := b.finiteDimensional_of_finite
  have hsep : ∀ F : V.space, (∀ g : (⊤ : Subgroup G), F g = 0) → F = 0 := by
    intro F hF
    apply Subtype.ext
    funext g
    exact hF ⟨g, trivial⟩
  obtain ⟨n, hn, gamma, hg⟩ := observation_finite_determining_points V ⊤ hsep
  let u : Fin n → G := fun k => gamma k
  let E : V.space →ₗ[ℝ] (Fin n → ℝ) := LinearMap.pi fun k => observationEvaluation V (u k)
  have hE : LinearMap.ker E = ⊥ := by
    apply LinearMap.ker_eq_bot.mpr
    intro F Q he
    apply sub_eq_zero.mp
    apply hg
    intro k
    have hk := congrFun he k
    change F (u k) - Q (u k) = 0
    exact sub_eq_zero.mpr hk
  let L : (Fin n → ℝ) →ₗ[ℝ] (iota → ℝ) := b.equivFun.toLinearMap.comp E.leftInverse
  refine ⟨n, hn, u, fun i k => L (Pi.single k 1) i, ?_⟩
  intro F i
  have hr : L (E F) = b.equivFun F := by
    change b.equivFun (E.leftInverse (E F)) = b.equivFun F
    rw [LinearMap.leftInverse_apply_of_inj hE]
  have he : E F = ∑ k, F (u k) • Pi.single k (1 : ℝ) := by
    ext k
    simp [E, observationEvaluation, Pi.single_apply]
  rw [← hr, he]
  simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro k _
  exact mul_comm _ _

end GMZP0
