import GMZP0.CyclicFrequencyAverage

/-! Positive proportions of actual horizontal/frequency fibres, with the same fixed field. -/

noncomputable section
open scoped BigOperators
namespace GMZP0

theorem bounded_moment_good_fibres {I J : Type*} [Fintype I] [Fintype J]
    [Nonempty I] [Nonempty J] (n : ℕ) (T : I → J → ℝ) (γ : ℝ) (hγ : 0 < γ)
    (hT : ∀ i j, 0 ≤ T i j ∧ T i j ≤ 1)
    (hlarge : γ ≤ realUniformMean (fun i => realUniformMean (fun j => T i j ^ (n + 1)))) :
    γ / 2 ≤ realUniformMean (fun i => if γ / 2 ≤ realUniformMean (T i) then (1 : ℝ) else 0) := by
  have hpow (i : I) (j : J) : T i j ^ (n + 1) ≤ T i j := by
    rw [pow_succ]
    calc
      T i j ^ n * T i j ≤ 1 * T i j :=
        mul_le_mul_of_nonneg_right (pow_le_one₀ (hT i j).1 (hT i j).2) (hT i j).1
      _ = T i j := one_mul _
  have hmean : γ ≤ realUniformMean (fun i => realUniformMean (T i)) :=
    hlarge.trans (realUniformMean_mono _ _ (fun i => realUniformMean_mono _ _ (hpow i)))
  have hb (i : I) : realUniformMean (T i) ≤ 1 := by
    have hh := realUniformMean_mono (T i) (fun _ : J => (1 : ℝ)) (fun j => (hT i j).2)
    simpa only [realUniformMean_const] using hh
  apply weighted_condition_mass (fun _ : I => (1 : ℝ)) (fun i => realUniformMean (T i))
    (fun i => γ / 2 ≤ realUniformMean (T i)) hγ (fun _ => ⟨zero_le_one, le_rfl⟩) hb
  · simpa only [one_mul] using hmean
  · exact fun _ hi => hi

def cyclicLocalFourFiber (N q ℓ M : ℕ) [NeZero q] (σ : Base N → ℝ)
    (F : Fin N → ZMod q → ℝ) (x : Fin N) (j : Fin (1024 * M)) : ℝ :=
  realUniformMean (fun h : Fin N => localCubeNorm 3
    (modulatedCyclicField N q M σ F x j) (cyclicShiftMap q ℓ (label h)))

def cyclicLocalGoodFiberMass (N q ℓ M : ℕ) [NeZero q] (σ : Base N → ℝ)
    (F : Fin N → ZMod q → ℝ) (β : ℝ) : ℝ :=
  realUniformMean (fun z : Fin N × Fin (1024 * M) =>
    if β / 2 ≤ cyclicLocalFourFiber N q ℓ M σ F z.1 z.2 then (1 : ℝ) else 0)

theorem cyclicLocalFourFiber_bounds {N q ℓ M : ℕ} [NeZero q] (hN : 0 < N)
    (σ : Base N → ℝ) (F : Fin N → ZMod q → ℝ) (hσ : ∀ z, 0 ≤ σ z ∧ σ z ≤ 1)
    (x : Fin N) (j : Fin (1024 * M)) :
    0 ≤ cyclicLocalFourFiber N q ℓ M σ F x j ∧ cyclicLocalFourFiber N q ℓ M σ F x j ≤ 1 := by
  let : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  refine ⟨realUniformMean_nonneg _ (fun h => localCubeNorm_nonneg 3 _ _), ?_⟩
  have hm := realUniformMean_mono
    (fun h : Fin N => localCubeNorm 3 (modulatedCyclicField N q M σ F x j) (cyclicShiftMap q ℓ (label h)))
    (fun _ : Fin N => (1 : ℝ))
    (fun _ => localCubeNorm_le_one 3 _ _ (modulatedCyclicField_norm_le N q M σ F hσ x j))
  simpa only [cyclicLocalFourFiber, realUniformMean_const] using hm

theorem cyclic_local_good_fibres {N q ℓ M : ℕ} [NeZero q] (hN : 0 < N) (hM : 0 < M)
    (σ : Base N → ℝ) (F : Fin N → ZMod q → ℝ) (hσ : ∀ z, 0 ≤ σ z ∧ σ z ≤ 1)
    (β : ℝ) (hβ : 0 < β) (hlarge : β ≤ cyclicLocalFourthNormAverage N q ℓ M σ F) :
    β / 2 ≤ cyclicLocalGoodFiberMass N q ℓ M σ F β := by
  let : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  let : Nonempty (Fin (1024 * M)) := ⟨⟨0, by omega⟩⟩
  apply bounded_moment_good_fibres (I := Fin N × Fin (1024 * M)) (J := Fin N) 15
    (fun z h => localCubeNorm 3 (modulatedCyclicField N q M σ F z.1 z.2) (cyclicShiftMap q ℓ (label h))) β hβ
  · intro z h
    exact ⟨localCubeNorm_nonneg 3 _ _, localCubeNorm_le_one 3 _ _
      (modulatedCyclicField_norm_le N q M σ F hσ z.1 z.2)⟩
  · rw [realUniformMean_prod (fun (x : Fin N) (j : Fin (1024 * M)) =>
      realUniformMean (fun h : Fin N => localCubeNorm 3
        (modulatedCyclicField N q M σ F x j) (cyclicShiftMap q ℓ (label h)) ^ (15 + 1)))]
    exact hlarge

end GMZP0
