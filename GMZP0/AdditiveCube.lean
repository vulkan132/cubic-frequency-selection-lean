import GMZP0.LocalCubeNorm

/-! Global additive cubes and the exact rerooting from local paired shifts. -/

noncomputable section
open scoped BigOperators
namespace GMZP0

def additiveCubeVertex {G : Type*} [AddCommGroup G] (d : ℕ)
    (Y : G) (v : Fin d → G) (ω : Fin d → Bool) : G :=
  Y + ∑ i, if ω i then v i else 0

def additiveCubeProduct {G : Type*} [AddCommGroup G] (d : ℕ)
    (H : G → ℂ) (Y : G) (v : Fin d → G) : ℂ :=
  ∏ ω, cubeConj d ω (H (additiveCubeVertex d Y v ω))

theorem localBoxFunction_additive_vertex {G A : Type*} [AddCommGroup G]
    (n : ℕ) (H : G → ℂ) (r : A → G) (Y : G) (u : Fin (n + 1) → A × A)
    (ω : Fin (n + 1) → Bool) :
    localBoxFunction n H r Y (cubeVertex u ω) =
      H (additiveCubeVertex (n + 1) (Y + ∑ i, r (u i).1)
        (fun i => r (u i).2 - r (u i).1) ω) := by
  unfold localBoxFunction additiveCubeVertex
  congr 1
  rw [add_assoc, ← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  cases hω : ω i <;> simp [cubeVertex, hω]

theorem local_cube_mean_reroot {G A : Type*} [AddCommGroup G] [Fintype G]
    (n : ℕ) (H : G → ℂ) (r : A → G) (u : Fin (n + 1) → A × A) :
    complexUniformMean (fun Y : G => cubeProduct (n + 1) (localBoxFunction n H r Y) u) =
      complexUniformMean (fun Y : G => additiveCubeProduct (n + 1) H Y
        (fun i => r (u i).2 - r (u i).1)) := by
  simp only [cubeProduct, localBoxFunction_additive_vertex]
  exact complexUniformMean_equiv (Equiv.addRight (∑ i, r (u i).1))
    (fun Y => additiveCubeProduct (n + 1) H Y (fun i => r (u i).2 - r (u i).1))

end GMZP0
