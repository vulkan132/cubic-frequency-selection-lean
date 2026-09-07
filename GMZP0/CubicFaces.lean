import GMZP0.CyclicSmoothing

/-! An explicit four-face factorization of the actual cubic circle phase.
Each factor is independent of its own coordinate. No real lift is selected. -/

noncomputable section
open scoped BigOperators
namespace GMZP0

def cubicShiftCoefficient (t k s : ℤ) : ℤ := (t - (k + s)) ^ 3 - t ^ 3

def cubicFaceCoefficient (t k : ℤ) (u : Fin 4 → ℤ) : Fin 4 → ℤ :=
  let C := cubicShiftCoefficient t k
  ![C (u 1 + u 2 + u 3),
    C (u 0 + u 2 + u 3) - C (u 2 + u 3),
    C (u 0 + u 1 + u 3) - C (u 0 + u 3) - C (u 1 + u 3) + C (u 3),
    C (u 0 + u 1 + u 2) - C (u 0 + u 1) - C (u 0 + u 2) - C (u 1 + u 2) +
      C (u 0) + C (u 1) + C (u 2) - C 0]

theorem cubicFaceCoefficient_independent (t k : ℤ) (u : Fin 4 → ℤ) (i : Fin 4) (s : ℤ) :
    cubicFaceCoefficient t k (Function.update u i s) i = cubicFaceCoefficient t k u i := by
  fin_cases i <;> simp [cubicFaceCoefficient, Function.update]

theorem sum_cubicFaceCoefficient (t k : ℤ) (u : Fin 4 → ℤ) :
    (∑ i : Fin 4, cubicFaceCoefficient t k u i) =
      -(t ^ 3 - (t - (k + ∑ i : Fin 4, u i)) ^ 3) := by
  simp [Fin.sum_univ_four, cubicFaceCoefficient, cubicShiftCoefficient]
  ring

def cubicFacePhase (t k : ℤ) (c : Frequency) (u : Fin 4 → ℤ) (i : Fin 4) : ℂ :=
  circleCharacter (cubicFaceCoefficient t k u i • c)

theorem cubicFacePhase_norm (t k : ℤ) (c : Frequency) (u : Fin 4 → ℤ) (i : Fin 4) :
    ‖cubicFacePhase t k c u i‖ = 1 := norm_circleCharacter _

theorem cubicFacePhase_independent (t k : ℤ) (c : Frequency) (u : Fin 4 → ℤ)
    (i : Fin 4) (s : ℤ) :
    cubicFacePhase t k c (Function.update u i s) i = cubicFacePhase t k c u i := by
  simp only [cubicFacePhase, cubicFaceCoefficient_independent]

theorem cubicPhase_four_faces (t k : ℤ) (c : Frequency) (u : Fin 4 → ℤ) :
    circleCharacter (-(t ^ 3 - (t - (k + ∑ i : Fin 4, u i)) ^ 3) • c) =
      ∏ i : Fin 4, cubicFacePhase t k c u i := by
  rw [← sum_cubicFaceCoefficient, Fin.sum_univ_four, Fin.prod_univ_four]
  simp only [add_zsmul, circleCharacter_add, cubicFacePhase]

theorem cyclicShiftLagP_four_faces (N q : ℕ) (p : Base N → Frequency) (x : Fin N)
    (v : ZMod q) (h t k : ℤ) (u : Fin 4 → ℤ) :
    circleCharacter (cyclicShiftLagP N q p x v h t (k + ∑ i : Fin 4, u i)) =
      ∏ i : Fin 4, cubicFacePhase t k
        (originalFieldExtension N p 0
          ((x.val : ℤ) + 1 + h, ((v + ((h ^ 2 + 2 * h * t : ℤ) : ZMod q)).val : ℤ))) u i := by
  simpa only [cyclicShiftLagP, neg_zsmul] using cubicPhase_four_faces t k
    (originalFieldExtension N p 0
      ((x.val : ℤ) + 1 + h, ((v + ((h ^ 2 + 2 * h * t : ℤ) : ZMod q)).val : ℤ))) u

theorem cyclicLagSequence_four_faces (N q : ℕ) (p : Base N → Frequency)
    (σ : Base N → ℝ) (lam : Base N → ℂ) (x : Fin N) (v : ZMod q)
    (h t k : ℤ) (u : Fin 4 → ℤ) :
    cyclicLagSequence N q p σ lam x v h t (k + ∑ i : Fin 4, u i) =
      cyclicLagG N q p σ lam x v h t (k + ∑ i : Fin 4, u i) *
        ∏ i : Fin 4, cubicFacePhase t k
          (originalFieldExtension N p 0
            ((x.val : ℤ) + 1 + h, ((v + ((h ^ 2 + 2 * h * t : ℤ) : ZMod q)).val : ℤ))) u i := by
  rw [cyclicLagSequence, cyclicShiftLagP_four_faces]

theorem cyclicSmoothedLagB_four_faces (N q ℓ : ℕ) (p : Base N → Frequency)
    (σ : Base N → ℝ) (lam : Base N → ℂ) (x : Fin N) (v : ZMod q) (h t : ℤ) :
    cyclicSmoothedLagB N q ℓ p σ lam x v h t =
      (∑ k ∈ lagInnerInterval N h t, complexUniformMean (fun u : FourShiftSpace ℓ =>
        cyclicLagG N q p σ lam x v h t (k + fourShiftSum ℓ u) *
          ∏ i : Fin 4, cubicFacePhase t k
            (originalFieldExtension N p 0
              ((x.val : ℤ) + 1 + h, ((v + ((h ^ 2 + 2 * h * t : ℤ) : ZMod q)).val : ℤ)))
            (fun j => (u j).val) i)) / (N : ℂ) := by
  simp only [cyclicSmoothedLagB, fourShiftSmoothedAverage, fourShiftSum,
    cyclicLagSequence_four_faces]

end GMZP0
