import GMZP0.AdditiveCube

/-! Exact additive cube differentiation, including all vertices. -/

noncomputable section
open scoped BigOperators ComplexConjugate
namespace GMZP0

def cubeDerivative {G : Type*} [AddCommGroup G] (H : G → ℂ) (h y : G) : ℂ :=
  H y * conj (H (y + h))

theorem additiveCubeVertex_cons {G : Type*} [AddCommGroup G] (d : ℕ)
    (Y h : G) (v : Fin d → G) (b : Bool) (ω : Fin d → Bool) :
    additiveCubeVertex (d + 1) Y (Fin.cons h v) (Fin.cons b ω) =
      additiveCubeVertex d (Y + if b then h else 0) v ω := by
  simp only [additiveCubeVertex, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, add_assoc]

theorem additiveCubeProduct_zero {G : Type*} [AddCommGroup G]
    (H : G → ℂ) (Y : G) (v : Fin 0 → G) : additiveCubeProduct 0 H Y v = H Y := by
  simp [additiveCubeProduct, additiveCubeVertex, cubeConj]

theorem additiveCubeProduct_succ {G : Type*} [AddCommGroup G] (d : ℕ)
    (H : G → ℂ) (Y h : G) (v : Fin d → G) :
    additiveCubeProduct (d + 1) H Y (Fin.cons h v) =
      additiveCubeProduct d (cubeDerivative H h) Y v := by
  rw [additiveCubeProduct, prod_boolean_cons]
  simp only [additiveCubeVertex_cons, Bool.false_eq_true, if_false, if_true, add_zero,
    cubeConj, Fin.cons_zero, Fin.tail_cons, additiveCubeProduct, cubeDerivative,
    cubeConj_mul, cubeConj_conj, Finset.prod_mul_distrib]
  congr 1
  apply Finset.prod_congr rfl
  intro ω _
  congr 3
  simp only [additiveCubeVertex]
  abel

theorem additiveCubeProduct_one {G : Type*} [AddCommGroup G]
    (H : G → ℂ) (Y h : G) :
    additiveCubeProduct 1 H Y (Fin.cons h default) = H Y * conj (H (Y + h)) := by
  rw [additiveCubeProduct_succ, additiveCubeProduct_zero]
  rfl




end GMZP0
