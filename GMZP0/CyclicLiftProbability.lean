import GMZP0.CyclicLiftValues
import GMZP0.IndependentAssignments
import GMZP0.OriginalCubeVertices

/-! A successful original weighted cube has probability at least 57^(-16) under one global choice. -/

noncomputable section
open scoped BigOperators
namespace GMZP0

theorem cyclicCube_scaled_frequency_sum (N q ℓ : ℕ) (p : Base N → Frequency)
    (d : ℕ) (x : Fin N) (Y : ZMod q) (h : ℤ) (u : CubeShiftPairs ℓ) :
    (∑ ω, cubeSign 4 ω • (d • cyclicField N q p 0 x (cyclicCubeVertex q ℓ h Y u ω))) =
      -(d • cyclicCubeCubicCoeff N q ℓ p x Y h u) := by
  simp only [cyclicCubeCubicCoeff, smul_neg, neg_neg, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro ω _
  exact smul_comm _ _ _

theorem cyclicCubeWeight_pos_vertices (N q ℓ : ℕ) (σ : Base N → ℝ)
    (hσ : ∀ z, 0 ≤ σ z ∧ σ z ≤ 1) (x : Fin N) (Y : ZMod q) (h : ℤ)
    (u : CubeShiftPairs ℓ) (hW : 0 < cyclicCubeWeight N q ℓ σ x Y h u) :
    ∀ ω : Fin 4 → Bool, 0 < cyclicField N q σ 0 x (cyclicCubeVertex q ℓ h Y u ω) := by
  intro ω
  have hn := cyclicCubeWeight_ne_zero_vertices N q ℓ σ x Y h u hW.ne' ω
  have hz : 0 ≤ cyclicField N q σ 0 x (cyclicCubeVertex q ℓ h Y u ω) :=
    cyclicField_property N q σ 0 (fun r : ℝ => 0 ≤ r) (fun z => (hσ z).1) le_rfl _ _
  exact lt_of_le_of_ne hz hn.symm

theorem cyclic_lift_cube_probability {N q ℓ M : ℕ} [NeZero q] (hM : 0 < M)
    (p : Base N → Frequency) (σ : Base N → ℝ) (hσ : ∀ z, 0 ≤ σ z ∧ σ z ≤ 1)
    (d : ℕ) (E : ℝ) (hscale : (M : ℝ) * (E / (N : ℝ) ^ 3) ≤ 1)
    (x : Fin N) (Y : ZMod q) (h : ℤ) (u : CubeShiftPairs ℓ)
    (hgood : 0 < cyclicDistinctCubeNearWeight N q ℓ p σ d E x Y h u) :
    1 / (57 : ℝ) ^ 16 ≤ realUniformMean (fun c : CyclicLiftAssignments N q =>
      if cyclicRealCubeDifference q ℓ (cyclicLiftValue N q M p σ d c) x Y h u = 0 then 1 else 0) := by
  classical
  obtain ⟨hinj, hnear, hW⟩ := (cyclicDistinctCubeNearWeight_pos_iff N q ℓ p σ d E x Y h u).mp hgood
  let e : (Fin 4 → Bool) ↪ (Fin N × ZMod q) :=
    ⟨fun ω => (x, cyclicCubeVertex q ℓ h Y u ω), fun _ _ he => hinj (congrArg Prod.snd he)⟩
  let a : (Fin 4 → Bool) → Frequency :=
    fun ω => d • cyclicField N q p 0 x (cyclicCubeVertex q ℓ h Y u ω)
  have ha : ‖∑ ω, cubeSign 4 ω • a ω‖ ≤ E / (N : ℝ) ^ 3 := by
    simpa only [a, cyclicCube_scaled_frequency_sum, norm_neg] using hnear
  obtain ⟨c₀, hc₀⟩ := exists_cube_lift_zero hM a (E / (N : ℝ) ^ 3) hscale ha
  have hp := uniform_restricted_event_lower e
    (fun c : (Fin 4 → Bool) → LiftChoice => ∑ ω, (cubeSign 4 ω : ℝ) * liftChoiceValue M (a ω) (c ω) = 0)
    c₀ hc₀
  have hpos := cyclicCubeWeight_pos_vertices N q ℓ σ hσ x Y h u hW
  have he (c : CyclicLiftAssignments N q) :
      cyclicRealCubeDifference q ℓ (cyclicLiftValue N q M p σ d c) x Y h u =
        ∑ ω, (cubeSign 4 ω : ℝ) * liftChoiceValue M (a ω) (c (e ω)) := by
    unfold cyclicRealCubeDifference
    apply Finset.sum_congr rfl
    intro ω _
    simp only [cyclicLiftValue, if_pos (hpos ω)]
    rfl
  simpa only [he, card_liftChoice, card_booleanVertices, Nat.cast_ofNat,
    show (2 : ℕ) ^ 4 = 16 by decide] using hp

theorem cyclicDistinctCubeNearWeight_eq_ite_pos (N q ℓ : ℕ) (p : Base N → Frequency)
    (σ : Base N → ℝ) (hσ : ∀ z, 0 ≤ σ z ∧ σ z ≤ 1) (d : ℕ) (E : ℝ)
    (x : Fin N) (Y : ZMod q) (h : ℤ) (u : CubeShiftPairs ℓ) :
    (if 0 < cyclicDistinctCubeNearWeight N q ℓ p σ d E x Y h u
      then cyclicCubeWeight N q ℓ σ x Y h u else 0) =
        cyclicDistinctCubeNearWeight N q ℓ p σ d E x Y h u := by
  classical
  have hw := cyclicCubeWeight_bounds N q ℓ σ x Y h u hσ
  unfold cyclicDistinctCubeNearWeight cyclicCubeNearWeight
  split_ifs <;> simp_all
  linarith

end GMZP0
