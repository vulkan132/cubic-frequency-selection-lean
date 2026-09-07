import GMZP0.MajorArcGrid

/-! Finite energy and mass estimates, always using the given original weight. -/

noncomputable section
open scoped BigOperators
namespace GMZP0

/-- A lower response threshold converts weighted energy into a mass bound. -/
theorem weighted_mass_le_energy {Z : Type*} (A : Finset Z) (μ R : Z → ℝ)
    (τ E : ℝ) (hτ : 0 < τ) (hμ : ∀ z ∈ A, 0 ≤ μ z)
    (hresponse : ∀ z ∈ A, τ ≤ R z) (henergy : (∑ z ∈ A, μ z * R z ^ 2) ≤ E) :
    (∑ z ∈ A, μ z) ≤ E / τ ^ 2 := by
  apply (le_div_iff₀ (sq_pos_of_pos hτ)).2
  calc
    (∑ z ∈ A, μ z) * τ ^ 2 = ∑ z ∈ A, μ z * τ ^ 2 := Finset.sum_mul ..
    _ ≤ ∑ z ∈ A, μ z * R z ^ 2 := by
      apply Finset.sum_le_sum
      intro z hz
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hτ.le (hresponse z hz) 2) (hμ z hz)
    _ ≤ E := henergy

/-- Partitioning a fixed original weight subtracts only the mass of the rejected points. -/
theorem retained_mass_from_energy {Z : Type*} (A : Finset Z) (μ R : Z → ℝ)
    (P : Z → Prop) [DecidablePred P] (τ E c : ℝ) (hτ : 0 < τ)
    (hμ : ∀ z ∈ A, 0 ≤ μ z) (hmass : c ≤ ∑ z ∈ A, μ z)
    (hresponse : ∀ z ∈ A.filter (fun z => ¬P z), τ ≤ R z)
    (henergy : (∑ z ∈ A.filter (fun z => ¬P z), μ z * R z ^ 2) ≤ E) :
    c - E / τ ^ 2 ≤ ∑ z ∈ A.filter P, μ z := by
  have hminor := weighted_mass_le_energy (A.filter (fun z => ¬P z)) μ R τ E hτ
    (fun z hz => hμ z (Finset.mem_filter.mp hz).1) hresponse henergy
  have hpartition : (∑ z ∈ A.filter P, μ z) +
      (∑ z ∈ A.filter (fun z => ¬P z), μ z) = ∑ z ∈ A, μ z := by
    simp only [Finset.sum_filter, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro z _
    by_cases hz : P z <;> simp [hz]
  linarith

/-- Finite arbitrary pointwise assignment costs at most the number of profiles in energy. -/
theorem assigned_weighted_energy {Z J : Type*} [Fintype Z] [Fintype J]
    (A : Finset Z) (μ : Z → ℝ) (R : Z → J → ℝ) (j : Z → J)
    (w E : ℝ) (hw : 0 ≤ w) (hμ : ∀ z ∈ A, μ z ≤ w)
    (hR : ∀ z i, 0 ≤ R z i) (hprofiles : ∀ i, (∑ z, R z i) ≤ E) :
    (∑ z ∈ A, μ z * R z (j z)) ≤ w * ((Fintype.card J : ℝ) * E) := by
  classical
  calc
    (∑ z ∈ A, μ z * R z (j z)) ≤ ∑ z ∈ A, w * ∑ i, R z i := by
      apply Finset.sum_le_sum
      intro z hz
      exact (mul_le_mul_of_nonneg_right (hμ z hz) (hR z (j z))).trans
        (mul_le_mul_of_nonneg_left
          (Finset.single_le_sum (fun i _ => hR z i) (Finset.mem_univ (j z))) hw)
    _ = w * ∑ z ∈ A, ∑ i, R z i := (Finset.mul_sum ..).symm
    _ ≤ w * ∑ z, ∑ i, R z i := by
      apply mul_le_mul_of_nonneg_left _ hw
      exact Finset.sum_le_univ_sum_of_nonneg (fun z => Finset.sum_nonneg (fun i _ => hR z i))
    _ = w * ∑ i, ∑ z, R z i := by rw [Finset.sum_comm]
    _ ≤ w * ∑ _i : J, E := mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ => hprofiles i)) hw
    _ = w * ((Fintype.card J : ℝ) * E) := by simp

def majorPoints (Q N : ℕ) (p : Base N → Frequency) (A : Finset (Base N)) : Finset (Base N) := by
  classical
  exact A.filter (fun z => MajorArc Q N (p z))

def minorPoints (Q N : ℕ) (p : Base N → Frequency) (A : Finset (Base N)) : Finset (Base N) := by
  classical
  exact A.filter (fun z => ¬MajorArc Q N (p z))

/-- Unweighted squared original-function response, with the output minor-arc mask. -/
def profileMinorEnergy (Q N : ℕ) (f : ℤ × ℤ → ℂ) (p : Base N → Frequency) : ℝ := by
  classical
  exact ∑ z : Base N, if MajorArc Q N (p z) then 0 else ‖response N f z (p z)‖ ^ 2

/-- Per-profile squared operator estimates imply the assigned original-weight energy bound. -/
theorem assigned_minor_energy {N J : ℕ} (hN : 0 < N) (Q : ℕ) (s : ℝ)
    (f : ℤ × ℤ → ℂ) (p : Fin J → Base N → Frequency) (j : Base N → Fin J)
    (A : Finset (Base N)) (μ : Base N → ℝ)
    (hμ : ∀ z ∈ A, μ z ≤ (N : ℝ)⁻¹ ^ 3)
    (hprofiles : ∀ i, profileMinorEnergy Q N f (p i) ≤ 4 * (N : ℝ) ^ 3 * s ^ 2) :
    (∑ z ∈ minorPoints Q N (fun z => p (j z) z) A,
      μ z * ‖response N f z (p (j z) z)‖ ^ 2) ≤ 4 * (J : ℝ) * s ^ 2 := by
  classical
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  let R : Base N → Fin J → ℝ := fun z i =>
    if MajorArc Q N (p i z) then 0 else ‖response N f z (p i z)‖ ^ 2
  have hR (z : Base N) (i : Fin J) : 0 ≤ R z i := by
    dsimp [R]
    split_ifs <;> positivity
  have hper (i : Fin J) : (∑ z, R z i) ≤ 4 * (N : ℝ) ^ 3 * s ^ 2 := hprofiles i
  have h := assigned_weighted_energy A μ R j ((N : ℝ)⁻¹ ^ 3)
    (4 * (N : ℝ) ^ 3 * s ^ 2) (by positivity) hμ hR hper
  have hleft : (∑ z ∈ A, μ z * R z (j z)) =
      ∑ z ∈ minorPoints Q N (fun z => p (j z) z) A,
        μ z * ‖response N f z (p (j z) z)‖ ^ 2 := by
    simp only [minorPoints, Finset.sum_filter, R, mul_ite, mul_zero, ite_not]
  rw [hleft] at h
  apply h.trans_eq
  simp only [Fintype.card_fin]
  field_simp

/-- Convert an assigned model's minor-arc energy into positive original major-arc weight. -/
theorem major_mass_of_minor_energy {N : ℕ} (hN : 0 < N) (Q : ℕ)
    (f : ℤ × ℤ → ℂ) (hf : ∀ w, ‖f w‖ ≤ 1)
    (θ p : Base N → Frequency) (lam : Base N → ℂ) (μ : Base N → ℝ)
    (A : Finset (Base N)) (η c E : ℝ) (hη : 0 < η)
    (hμ : ∀ z ∈ A, 0 ≤ μ z) (hmass : c ≤ ∑ z ∈ A, μ z)
    (hlam : ∀ z ∈ A, ‖lam z‖ = 1)
    (hresponse : ∀ z ∈ A, η ≤ (lam z * response N f z (θ z)).re)
    (hclose : ∀ z ∈ A, cubicDistance N (θ z) (p z) ≤ η / 2)
    (henergy : (∑ z ∈ minorPoints Q N p A, μ z * ‖response N f z (p z)‖ ^ 2) ≤ E) :
    c - E / (η / 2) ^ 2 ≤ ∑ z ∈ majorPoints Q N p A, μ z := by
  classical
  apply retained_mass_from_energy A μ (fun z => ‖response N f z (p z)‖)
    (fun z => MajorArc Q N (p z)) (η / 2) E c (by positivity) hμ hmass _ henergy
  intro z hz
  have hzA := (Finset.mem_filter.mp hz).1
  have h := norm_response_transfer hN f hf z (θ z) (p z) (lam z) (hlam z hzA)
    η (η / 2) (hresponse z hzA) (hclose z hzA)
  linarith

end GMZP0
