import GMZP0.CoordinateMean
import GMZP0.ShiftResidues

/-! Eight independent shift coordinates, with the exact effect of changing one coordinate. -/

noncomputable section
open scoped BigOperators
namespace GMZP0

abbrev FlatCubeShiftSpace (ℓ : ℕ) := (Fin 4 × Bool) → smoothingShiftLabels ℓ

def flatCubePairsEquiv (ℓ : ℕ) : FlatCubeShiftSpace ℓ ≃ CubeShiftPairs ℓ where
  toFun v := fun i => (v (i, false), v (i, true))
  invFun u := fun j => if j.2 then (u j.1).2 else (u j.1).1
  left_inv v := by funext j; rcases j with ⟨i, b⟩; cases b <;> rfl
  right_inv u := by funext i; exact Prod.eta (u i)

def flatCubeShiftSum (ℓ : ℕ) (v : FlatCubeShiftSpace ℓ) (ω : Fin 4 → Bool) : ℤ :=
  ∑ i, (v (i, ω i)).val

theorem cubeShiftSum_flat (ℓ : ℕ) (v : FlatCubeShiftSpace ℓ) (ω : Fin 4 → Bool) :
    cubeShiftSum ℓ (flatCubePairsEquiv ℓ v) ω = flatCubeShiftSum ℓ v ω := by
  unfold cubeShiftSum fourShiftSum flatCubeShiftSum
  apply Finset.sum_congr rfl
  intro i _
  cases h : ω i <;> simp [cubeVertex, flatCubePairsEquiv, h]

theorem flatCubeShiftSum_update_sub (ℓ : ℕ) (v : FlatCubeShiftSpace ℓ)
    (ω : Fin 4 → Bool) (i : Fin 4) (a b : smoothingShiftLabels ℓ) :
    flatCubeShiftSum ℓ (Function.update v (i, ω i) a) ω -
      flatCubeShiftSum ℓ (Function.update v (i, ω i) b) ω = a.val - b.val := by
  unfold flatCubeShiftSum
  rw [← Finset.sum_sub_distrib]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    have he : (j, ω j) ≠ (i, ω i) := by intro h; exact hji (congrArg Prod.fst h)
    simp [Function.update_of_ne he]
  · simp

theorem flatCubeShiftSum_update_other (ℓ : ℕ) (v : FlatCubeShiftSpace ℓ)
    (ω ω' : Fin 4 → Bool) (i : Fin 4) (hi : ω i ≠ ω' i) (a : smoothingShiftLabels ℓ) :
    flatCubeShiftSum ℓ (Function.update v (i, ω i) a) ω' = flatCubeShiftSum ℓ v ω' := by
  apply Finset.sum_congr rfl
  intro j _
  have he : (j, ω' j) ≠ (i, ω i) := by
    intro h
    have hj : j = i := congrArg Prod.fst h
    subst j
    exact hi (congrArg Prod.snd h).symm
  simp [Function.update_of_ne he]

end GMZP0
