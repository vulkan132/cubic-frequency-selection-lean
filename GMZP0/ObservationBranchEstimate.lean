import GMZP0.ObservationCorrectionGeometry
import GMZP0.ObservationTopology

/-! Quantitative bounds on the genuine original correction branches. The
fiber coefficients are unrestricted; only their difference enters the bound. -/
noncomputable section
open Set Metric Module
open scoped BigOperators
namespace GMZP0

/-- The real character chord bound, with the exact original exponential. -/
theorem real_circle_character_chord (x y : ℝ) :
    ‖circleCharacter (x : Frequency) - circleCharacter (y : Frequency)‖ ≤
      2 * Real.pi * |x - y| := by
  have hchar : circleCharacter (x : Frequency) =
      circleCharacter ((x - y : ℝ) : Frequency) * circleCharacter (y : Frequency) := by
    rw [← circleCharacter_add, ← AddCircle.coe_add, sub_add_cancel]
  have hnorm : ‖circleCharacter (y : Frequency)‖ = 1 := Circle.norm_coe _
  calc
    ‖circleCharacter (x : Frequency) - circleCharacter (y : Frequency)‖ =
        ‖circleCharacter ((x - y : ℝ) : Frequency) - 1‖ := by
      rw [hchar, show circleCharacter ((x - y : ℝ) : Frequency) * circleCharacter (y : Frequency) -
          circleCharacter (y : Frequency) =
          (circleCharacter ((x - y : ℝ) : Frequency) - 1) * circleCharacter (y : Frequency) by ring,
        norm_mul, hnorm, mul_one]
    _ ≤ 2 * Real.pi * |x - y| := by
      rw [circleCharacter_real]
      have h := Real.norm_exp_I_mul_ofReal_sub_one_le (x := 2 * Real.pi * (x - y))
      rw [mul_comm Complex.I] at h
      simpa only [Real.norm_eq_abs, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2),
        abs_of_pos Real.pi_pos] using h

variable {G : Type*} [Group G] (V : ObservationModule G)
  {iota : Type*} [Fintype iota]

/-- Every original evaluation is quantitatively controlled by the actual
basis coefficient difference, with no coefficient-size restriction. -/
theorem observation_evaluation_difference_bound (b : Basis iota ℝ V.space)
    (P Q : V.space) (g : G) :
    |P g - Q g| ≤ (∑ i, |b i g|) * dist (b.equivFun P) (b.equivFun Q) := by
  classical
  rw [observation_evaluation_basis V b P, observation_evaluation_basis V b Q,
    ← Finset.sum_sub_distrib, Finset.sum_mul]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro i _
  rw [← sub_mul, abs_mul, mul_comm]
  exact mul_le_mul_of_nonneg_left (dist_le_pi_dist (b.equivFun P) (b.equivFun Q) i) (abs_nonneg _)

variable [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]

/-- One branch constant is chosen before all observation coefficients.
Only the original corrections occurring over a fixed compact base chart
enter the finite sum; the specified section is never replaced. -/
theorem original_observation_same_correction_bound (Gamma : Subgroup G)
    [DiscreteTopology Gamma] (c : ObservationSection Gamma)
    (K D : Set G) (hK : IsCompact K) (hD : IsCompact D)
    (hc : Set.range c.representative ⊆ D) (b : Basis iota ℝ V.space) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a e : ObservationGroup V,
      a.base ∈ K → e.base ∈ K → observationCorrection c a.base = observationCorrection c e.base →
      ‖quotientObservation V c (QuotientGroup.mk a) - quotientObservation V c (QuotientGroup.mk e)‖ ≤
        C * dist (b.equivFun a.obs) (b.equivFun e.obs) := by
  classical
  have hfinite := original_corrections_finite_on_compact Gamma c K D hK hD hc
  let T := hfinite.toFinset
  let B : ℝ := ∑ gamma ∈ T, ∑ i, |b i gamma|
  have hB : 0 ≤ B := Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => abs_nonneg _))
  refine ⟨2 * Real.pi * B, by positivity, ?_⟩
  intro a e ha _ heq
  have hmem : observationCorrection c a.base ∈ T := hfinite.mem_toFinset.mpr ⟨a.base, ha, rfl⟩
  have hsum : (∑ i, |b i (observationCorrection c a.base)|) ≤ B := by
    exact Finset.single_le_sum (f := fun gamma : Gamma => ∑ i, |b i gamma|)
      (fun _ _ => Finset.sum_nonneg (fun _ _ => abs_nonneg _)) hmem
  change ‖circleCharacter (observationRealPhase V c a : Frequency) -
    circleCharacter (observationRealPhase V c e : Frequency)‖ ≤ _
  apply (real_circle_character_chord _ _).trans
  simp only [observationRealPhase, ← heq]
  have h := (observation_evaluation_difference_bound V b a.obs e.obs
    (observationCorrection c a.base)).trans (mul_le_mul_of_nonneg_right hsum dist_nonneg)
  have hh := mul_le_mul_of_nonneg_left h (show 0 ≤ 2 * Real.pi by positivity)
  simpa only [mul_assoc] using hh

end GMZP0
