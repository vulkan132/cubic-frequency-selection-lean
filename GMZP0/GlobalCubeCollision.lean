import GMZP0.AdditiveCube
import GMZP0.CubeCollision

/-! All global seven-cube collisions: each distinct pair has probability at most
one over the group size, and the 8128 unordered pairs give the full bound. -/

noncomputable section
open scoped BigOperators
namespace GMZP0

theorem additiveCubeVertex_update_difference {G : Type*} [AddCommGroup G]
    (d : ℕ) (Y : G) (v : Fin d → G) (ω : Fin d → Bool) (i : Fin d) (a b : G) :
    additiveCubeVertex d Y (Function.update v i a) ω -
      additiveCubeVertex d Y (Function.update v i b) ω = if ω i then a - b else 0 := by
  have he (t : G) : (fun j => if ω j then Function.update v i t j else 0) =
      Function.update (fun j => if ω j then v j else 0) i (if ω i then t else 0) := by
    funext j
    by_cases hj : j = i
    · subst j; simp
    · simp [Function.update_of_ne hj]
  unfold additiveCubeVertex
  rw [he a, he b, Finset.sum_update_of_mem (Finset.mem_univ i),
    Finset.sum_update_of_mem (Finset.mem_univ i)]
  cases ω i <;> simp

theorem additive_cube_pair_update_unique {G : Type*} [AddCommGroup G]
    (d : ℕ) (Y : G) (ω ω' : Fin d → Bool) (i : Fin d) (hi : ω i ≠ ω' i)
    (v : Fin d → G) (a b : G)
    (ha : additiveCubeVertex d Y (Function.update v i a) ω = additiveCubeVertex d Y (Function.update v i a) ω')
    (hb : additiveCubeVertex d Y (Function.update v i b) ω = additiveCubeVertex d Y (Function.update v i b) ω') :
    a = b := by
  have he := congrArg₂ (fun x y : G => x - y) ha hb
  rw [additiveCubeVertex_update_difference, additiveCubeVertex_update_difference] at he
  cases hw : ω i <;> cases hw' : ω' i <;> simp_all [sub_eq_zero]
  exact sub_eq_zero.mp he.symm

theorem additive_cube_pair_collision_probability {G : Type*} [AddCommGroup G]
    [Fintype G] [DecidableEq G] (d : ℕ) (Y : G) (ω ω' : Fin d → Bool) (hne : ω ≠ ω') :
    realUniformMean (fun v : Fin d → G =>
      if additiveCubeVertex d Y v ω = additiveCubeVertex d Y v ω' then (1 : ℝ) else 0) ≤
        1 / (Fintype.card G : ℝ) := by
  obtain ⟨i, hi⟩ : ∃ i, ω i ≠ ω' i := by
    by_contra hn
    push Not at hn
    exact hne (funext hn)
  exact uniform_event_le_of_update_unique i _ (additive_cube_pair_update_unique d Y ω ω' i hi)

def sevenVertexEnumeration : Fin 128 ≃ (Fin 7 → Bool) :=
  Fintype.equivOfCardEq (by simp)

abbrev AscendingSevenLabelPairs := {ij : Fin 128 × Fin 128 // ij.1 < ij.2}

theorem card_ascendingSevenLabelPairs : Fintype.card AscendingSevenLabelPairs = 8128 := by
  rw [Fintype.card_subtype, ← Finset.univ_product_univ, Finset.card_product_filter_lt]
  norm_num [Nat.choose_two_right]

def globalCubeCollisionProbability {G : Type*} [AddCommGroup G] [Fintype G]
    (d : ℕ) (Y : G) : ℝ := by
  classical
  exact realUniformMean (fun v : Fin d → G =>
    if ¬ Function.Injective (additiveCubeVertex d Y v) then (1 : ℝ) else 0)

theorem global_seven_collision_probability {G : Type*} [AddCommGroup G]
    [Fintype G] (Y : G) :
    globalCubeCollisionProbability 7 Y ≤ 8128 / (Fintype.card G : ℝ) := by
  classical
  let P (v : Fin 7 → G) := ¬ Function.Injective (additiveCubeVertex 7 Y v)
  let Q (v : Fin 7 → G) (ij : AscendingSevenLabelPairs) :=
    additiveCubeVertex 7 Y v (sevenVertexEnumeration ij.val.1) =
      additiveCubeVertex 7 Y v (sevenVertexEnumeration ij.val.2)
  have hcover : ∀ v, P v → ∃ ij, Q v ij := by
    intro v hv
    obtain ⟨ω, ω', he, hne⟩ := Function.not_injective_iff.mp hv
    let i := sevenVertexEnumeration.symm ω
    let j := sevenVertexEnumeration.symm ω'
    have hij : i ≠ j := fun hh => hne (sevenVertexEnumeration.symm.injective hh)
    rcases lt_or_gt_of_ne hij with hij | hji
    · refine ⟨⟨(i, j), hij⟩, ?_⟩
      simpa only [Q, i, j, Equiv.apply_symm_apply] using he
    · refine ⟨⟨(j, i), hji⟩, ?_⟩
      simpa only [Q, i, j, Equiv.apply_symm_apply] using he.symm
  have hu := uniform_event_union_le P Q hcover
  have hp (ij : AscendingSevenLabelPairs) :
      realUniformMean (fun v => if Q v ij then (1 : ℝ) else 0) ≤ 1 / (Fintype.card G : ℝ) := by
    apply additive_cube_pair_collision_probability
    exact fun he => (ne_of_lt ij.property) (sevenVertexEnumeration.injective he)
  have hsums := Finset.sum_le_sum (fun ij (_ : ij ∈ (Finset.univ : Finset AscendingSevenLabelPairs)) => hp ij)
  have hc : (∑ _ : AscendingSevenLabelPairs, (1 : ℝ) / (Fintype.card G : ℝ)) =
      8128 / (Fintype.card G : ℝ) := by
    simp only [Finset.sum_const, Finset.card_univ, card_ascendingSevenLabelPairs, nsmul_eq_mul]
    ring
  exact hu.trans (hsums.trans_eq hc)

end GMZP0
