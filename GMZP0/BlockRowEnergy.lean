import GMZP0.BlockCollisions

/-! A nonzero horizontal block has at most N nonzero entries in each row. -/

noncomputable section
open scoped BigOperators ComplexConjugate
namespace GMZP0

theorem horizontal_collision_count {N : ℕ} (x x' : Fin N) (y : Fin (N ^ 2)) :
    (Finset.univ.filter (fun v : Fin (N ^ 2) =>
      ∃ r s : Fin N, endpointIndex (x, y) r = endpointIndex (x', v) s)).card ≤ N := by
  classical
  let V := Finset.univ.filter (fun v : Fin (N ^ 2) =>
    ∃ r s : Fin N, endpointIndex (x, y) r = endpointIndex (x', v) s)
  have hex : ∀ v : V, ∃ r s : Fin N, endpointIndex (x, y) r = endpointIndex (x', v.val) s := by
    intro v
    exact (Finset.mem_filter.mp v.property).2
  choose r s he using hex
  have hinj : Function.Injective r := by
    intro v v' hr
    apply Subtype.ext
    exact (collision_target_unique (x, y) x' (r v) v.val v'.val (s v) (s v')
      (he v) (hr ▸ he v')).1
  have hcard := Fintype.card_le_of_injective r hinj
  simpa only [Fintype.card_coe, Fintype.card_fin] using hcard

/-- The diagonal row energy has N^(-3) scale, using the nonparallel collision uniqueness. -/
theorem horizontalKernel_row_energy_le {N : ℕ} (hN : 0 < N)
    (p : Base N → Frequency) (x x' : Fin N) (hx : x ≠ x') (y : Fin (N ^ 2)) :
    finiteEnergy (horizontalKernel N p x x' y) ≤ (N : ℝ)⁻¹ ^ 3 := by
  classical
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hcount : ((Finset.univ.filter (fun v : Fin (N ^ 2) =>
      ∃ r s : Fin N, endpointIndex (x, y) r = endpointIndex (x', v) s)).card : ℝ) ≤ N := by
    exact_mod_cast horizontal_collision_count x x' y
  simp only [finiteEnergy, horizontalKernel_norm p x x' hx, ite_pow,
    zero_pow (by decide : 2 ≠ 0)]
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul]
  calc
    _ ≤ (N : ℝ) * ((N : ℝ)⁻¹ ^ 2) ^ 2 :=
      mul_le_mul_of_nonneg_right hcount (sq_nonneg _)
    _ = (N : ℝ)⁻¹ ^ 3 := by field_simp

end GMZP0
