import GMZP0.GlobalFrequencyAverage
import GMZP0.WeightedCollisionRemoval
import GMZP0.LocalGoodFibers

/-! Threshold deletion and the exact unweighted cube normalization.
A discarded product is at most the threshold, giving a stronger loss bound
than a vertex-by-vertex union bound; all original factors remain defined. -/

noncomputable section
open scoped BigOperators
namespace GMZP0

theorem bounded_product_le_factor {I : Type*} [Fintype I] (w : I → ℝ)
    (hw : ∀ i, 0 ≤ w i ∧ w i ≤ 1) (j : I) : ∏ i, w i ≤ w j := by
  classical
  simpa only [Finset.prod_singleton] using
    Finset.prod_le_prod_of_subset_of_le_one (Finset.subset_univ ({j} : Finset I))
      (fun i _ => (hw i).1) (fun i _ _ => (hw i).2)

theorem bounded_product_threshold_indicator {I : Type*} [Fintype I] (w : I → ℝ)
    (hw : ∀ i, 0 ≤ w i ∧ w i ≤ 1) (τ : ℝ) (hτ : 0 ≤ τ)
    (P : Prop) [Decidable P] :
    (if P then ∏ i, w i else 0) ≤ (if (∀ i, τ ≤ w i) ∧ P then (1 : ℝ) else 0) + τ := by
  classical
  by_cases hp : P
  · by_cases ht : ∀ i, τ ≤ w i
    · rw [if_pos hp, if_pos ⟨ht, hp⟩]
      have he : ∏ i, w i ≤ 1 := Finset.prod_le_one (fun i _ => (hw i).1) (fun i _ => (hw i).2)
      linarith
    · obtain ⟨j, hj⟩ : ∃ j, w j < τ := by simpa only [not_forall, not_le] using ht
      simp only [hp, ht, false_and, if_false, if_true, zero_add]
      exact (bounded_product_le_factor w hw j).trans hj.le
  · simp [hp, hτ]

abbrev realCubeThresholdGood {G : Type*} [AddCommGroup G] (d : ℕ)
    (σ F : G → ℝ) (τ : ℝ) (Y : G) (v : Fin d → G) : Prop :=
  (∀ ω : Fin d → Bool, τ ≤ σ (additiveCubeVertex d Y v ω)) ∧
    realSignedCubeSum d (fun ω => F (additiveCubeVertex d Y v ω)) = 0

def globalThresholdCubeDensity {G : Type*} [AddCommGroup G] [Fintype G]
    (d : ℕ) (σ F : G → ℝ) (τ : ℝ) : ℝ := by
  classical
  exact realUniformMean (fun Y : G => realUniformMean (fun v : Fin d → G =>
    if realCubeThresholdGood d σ F τ Y v then 1 else 0))

def globalDistinctThresholdCubeDensity {G : Type*} [AddCommGroup G] [Fintype G]
    (d : ℕ) (σ F : G → ℝ) (τ : ℝ) : ℝ := by
  classical
  exact realUniformMean (fun Y : G => realUniformMean (fun v : Fin d → G =>
    if Function.Injective (additiveCubeVertex d Y v) ∧ realCubeThresholdGood d σ F τ Y v then 1 else 0))

theorem globalThresholdCubeDensity_bounds {G : Type*} [AddCommGroup G] [Fintype G]
    (d : ℕ) (σ F : G → ℝ) (τ : ℝ) :
    0 ≤ globalThresholdCubeDensity d σ F τ ∧ globalThresholdCubeDensity d σ F τ ≤ 1 := by
  classical
  unfold globalThresholdCubeDensity
  constructor
  · exact realUniformMean_nonneg _ (fun _ => realUniformMean_nonneg _ (fun _ => by split_ifs <;> norm_num))
  · apply (realUniformMean_mono _ (fun _ : G => (1 : ℝ)) ?_).trans_eq (realUniformMean_const _)
    intro Y
    apply (realUniformMean_mono _ (fun _ : Fin d → G => (1 : ℝ)) ?_).trans_eq (realUniformMean_const _)
    intro v
    split_ifs <;> norm_num

theorem globalDistinctThresholdCubeDensity_bounds {G : Type*} [AddCommGroup G] [Fintype G]
    (d : ℕ) (σ F : G → ℝ) (τ : ℝ) :
    0 ≤ globalDistinctThresholdCubeDensity d σ F τ ∧ globalDistinctThresholdCubeDensity d σ F τ ≤ 1 := by
  classical
  unfold globalDistinctThresholdCubeDensity
  constructor
  · exact realUniformMean_nonneg _ (fun _ => realUniformMean_nonneg _ (fun _ => by split_ifs <;> norm_num))
  · apply (realUniformMean_mono _ (fun _ : G => (1 : ℝ)) ?_).trans_eq (realUniformMean_const _)
    intro Y
    apply (realUniformMean_mono _ (fun _ : Fin d → G => (1 : ℝ)) ?_).trans_eq (realUniformMean_const _)
    intro v
    split_ifs <;> norm_num

theorem global_threshold_density_lower {G : Type*} [AddCommGroup G] [Fintype G]
    (n : ℕ) (σ F : G → ℝ) (hσ : ∀ y, 0 ≤ σ y ∧ σ y ≤ 1) (τ : ℝ) (hτ : 0 ≤ τ) :
    globalRealCubeMass n σ F - τ ≤ globalThresholdCubeDensity (n + 1) σ F τ := by
  classical
  have hp (Y : G) (v : Fin (n + 1) → G) := bounded_product_threshold_indicator
    (fun ω : Fin (n + 1) → Bool => σ (additiveCubeVertex (n + 1) Y v ω))
    (fun ω => hσ _) τ hτ
    (realSignedCubeSum (n + 1) (fun ω => F (additiveCubeVertex (n + 1) Y v ω)) = 0)
  have hm := realUniformMean_mono _ _ (fun Y => realUniformMean_mono _ _ (hp Y))
  simp only [realUniformMean_add, realUniformMean_const] at hm
  change globalRealCubeMass n σ F ≤ globalThresholdCubeDensity (n + 1) σ F τ + τ at hm
  linarith

def globalDistinctThresholdCubeCount {G : Type*} [AddCommGroup G] [Fintype G]
    (d : ℕ) (σ F : G → ℝ) (τ : ℝ) : ℕ := by
  classical
  exact (Finset.univ.filter (fun z : G × (Fin d → G) =>
    Function.Injective (additiveCubeVertex d z.1 z.2) ∧ realCubeThresholdGood d σ F τ z.1 z.2)).card

theorem globalDistinctThresholdCubeDensity_eq_count {G : Type*} [AddCommGroup G] [Fintype G]
    (d : ℕ) (σ F : G → ℝ) (τ : ℝ) :
    globalDistinctThresholdCubeDensity d σ F τ =
      (globalDistinctThresholdCubeCount d σ F τ : ℝ) / (Fintype.card G : ℝ) ^ (d + 1) := by
  classical
  unfold globalDistinctThresholdCubeDensity globalDistinctThresholdCubeCount
  rw [← realUniformMean_prod (fun (Y : G) (v : Fin d → G) =>
    if Function.Injective (additiveCubeVertex d Y v) ∧ realCubeThresholdGood d σ F τ Y v then (1 : ℝ) else 0)]
  simp only [realUniformMean, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one,
    Fintype.card_prod, Fintype.card_fun, Fintype.card_fin, Nat.cast_mul, Nat.cast_pow, pow_succ]
  ring

theorem distinct_seven_cube_count_lower {q : ℕ} [NeZero q]
    (σ F : ZMod q → ℝ) (τ α : ℝ) (hα : α ≤ globalDistinctThresholdCubeDensity 7 σ F τ) :
    α * (q : ℝ) ^ 8 ≤ globalDistinctThresholdCubeCount 7 σ F τ := by
  rw [globalDistinctThresholdCubeDensity_eq_count, ZMod.card] at hα
  have hq : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  exact (le_div_iff₀ (pow_pos hq 8)).mp hα

end GMZP0
