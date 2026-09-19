import GMZP0.TriangularIntegerCell
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.Topology.Algebra.MvPolynomial

/-! Lebesgue measure is preserved by measurable strictly triangular
translations in every finite dimension. This uses iterated one-dimensional
translations, not an assumed coordinate Haar-measure identity. -/
noncomputable section
open Set MeasureTheory MeasureTheory.Measure
namespace GMZP0

/-- Split the last actual coordinate from its preceding coordinates. -/
def coordinateLastSplit (n : ℕ) : (Fin (n + 1) → ℝ) ≃ᵐ ((Fin n → ℝ) × ℝ) :=
  (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) (Fin.last n)).trans
    MeasurableEquiv.prodComm

theorem coordinate_last_split_apply (n : ℕ) (u : Fin (n + 1) → ℝ) :
    coordinateLastSplit n u = (Fin.init u, u (Fin.last n)) := by
  ext i <;> simp [coordinateLastSplit, MeasurableEquiv.piFinSuccAbove, MeasurableEquiv.prodComm, Fin.init]

theorem coordinate_last_split_volume (n : ℕ) :
    MeasurePreserving (coordinateLastSplit n) volume volume := by
  exact measurePreserving_swap.comp
    (volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) (Fin.last n))

/-- Appending a zero coordinate is a measurable operation in the original coordinates. -/
theorem measurable_snoc_zero (n : ℕ) :
    Measurable (fun u : Fin n → ℝ => (Fin.snoc u (0 : ℝ) : Fin (n + 1) → ℝ)) := by
  apply measurable_pi_lambda
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simpa only [Fin.snoc_last] using (measurable_const : Measurable (fun _ : Fin n → ℝ => (0 : ℝ)))
  · simpa only [Fin.snoc_castSucc] using (measurable_pi_apply j : Measurable (fun u : Fin n → ℝ => u j))

/-- The last coordinate does not influence any of the strictly triangular corrections. -/
theorem triangular_correction_ignore_last {n : ℕ}
    (q : Fin (n + 1) → (Fin (n + 1) → ℝ) → ℝ)
    (htri : ∀ i u v, (∀ j, j.val < i.val → u j = v j) → q i u = q i v)
    (i : Fin (n + 1)) (u : Fin (n + 1) → ℝ) :
    q i (Fin.snoc (Fin.init u) 0) = q i u := by
  apply htri
  intro j hj
  let k : Fin n := ⟨j.val, by omega⟩
  have he : j = k.castSucc := Fin.ext rfl
  rw [he, Fin.snoc_castSucc]
  rfl

/-- Every measurable translation by corrections depending only on strictly
earlier coordinates preserves actual Lebesgue volume, including dimension zero. -/
theorem triangular_translation_volume (n : ℕ)
    (q : Fin n → (Fin n → ℝ) → ℝ) (hm : ∀ i, Measurable (q i))
    (htri : ∀ i u v, (∀ j, j.val < i.val → u j = v j) → q i u = q i v) :
    MeasurePreserving (fun u i => u i + q i u) volume volume := by
  induction n with
  | zero =>
    have he : (fun (u : Fin 0 → ℝ) i => u i + q i u) = id := by
      funext u i
      exact Fin.elim0 i
    rw [he]
    exact MeasurePreserving.id volume
  | succ n ih =>
    let q' : Fin n → (Fin n → ℝ) → ℝ := fun i u => q i.castSucc (Fin.snoc u 0)
    have hm' : ∀ i, Measurable (q' i) := fun i => (hm i.castSucc).comp (measurable_snoc_zero n)
    have htri' : ∀ i u v, (∀ j, j.val < i.val → u j = v j) → q' i u = q' i v := by
      intro i u v huv
      apply htri
      intro j hj
      let k : Fin n := ⟨j.val, by simp only [Fin.val_castSucc] at hj; omega⟩
      have he : j = k.castSucc := Fin.ext rfl
      rw [he, Fin.snoc_castSucc, Fin.snoc_castSucc]
      exact huv k hj
    have hbase := ih q' hm' htri'
    let f : ((Fin n → ℝ) × ℝ) → ((Fin n → ℝ) × ℝ) :=
      fun p => ((fun i => p.1 i + q' i p.1), p.2 + q (Fin.last n) (Fin.snoc p.1 0))
    have hf : MeasurePreserving f volume volume := by
      change MeasurePreserving f
        ((volume : Measure (Fin n → ℝ)).prod (volume : Measure ℝ))
        ((volume : Measure (Fin n → ℝ)).prod (volume : Measure ℝ))
      dsimp [f]
      apply hbase.skew_product
        (g := fun (u : Fin n → ℝ) (r : ℝ) => r + q (Fin.last n) (Fin.snoc u 0))
        (μc := (volume : Measure ℝ)) (μd := (volume : Measure ℝ))
      · exact measurable_snd.add (((hm (Fin.last n)).comp (measurable_snoc_zero n)).comp measurable_fst)
      · exact Filter.Eventually.of_forall (fun u =>
          (measurePreserving_add_right (volume : Measure ℝ) (q (Fin.last n) (Fin.snoc u 0))).map_eq)
    let e := coordinateLastSplit n
    have he := coordinate_last_split_volume n
    have hcomp := (he.symm e).comp (hf.comp he)
    have heq : (e.symm ∘ f ∘ e) = (fun u i => u i + q i u) := by
      funext u
      apply e.injective
      simp only [Function.comp_apply, e.apply_symm_apply]
      change f (coordinateLastSplit n u) = coordinateLastSplit n (fun i => u i + q i u)
      rw [coordinate_last_split_apply, coordinate_last_split_apply]
      apply Prod.ext
      · funext i
        dsimp [f, q', Fin.init]
        rw [triangular_correction_ignore_last q htri]
      · dsimp [f]
        rw [triangular_correction_ignore_last q htri]
    rwa [heq] at hcomp

/-- Literal lower-coordinate polynomial support supplies all measurability
and triangularity required for volume preservation. -/
theorem triangular_polynomial_volume {n : ℕ} (q : Fin n → MvPolynomial (Fin n) ℝ)
    (hlow : ∀ i d, d ∈ (q i).support → ∀ j ∈ d.support, j.val < i.val) :
    MeasurePreserving (fun (u : Fin n → ℝ) i => u i + MvPolynomial.aeval u (q i)) volume volume := by
  apply triangular_translation_volume n
  · intro i
    simpa only [MvPolynomial.aeval_def, Algebra.algebraMap_self, MvPolynomial.eval₂_id] using
      (MvPolynomial.continuous_eval (q i)).measurable
  · intro i u v huv
    exact polynomial_eval_eq_of_prefix i (q i) (hlow i) u v huv

/-- Allowing a correction to cancel the current coordinate destroys volume
preservation even in dimension one. This is not a counterexample to P0. -/
theorem triangular_volume_diagonal_obstruction :
    ¬ MeasurePreserving (fun (u : Fin 1 → ℝ) i => u i - u i) volume volume := by
  intro h
  have hm := h.measure_preimage (measurableSet_singleton (0 : Fin 1 → ℝ)).nullMeasurableSet
  have he : (fun (u : Fin 1 → ℝ) i => u i - u i) ⁻¹' ({0} : Set (Fin 1 → ℝ)) = Set.univ := by
    ext u
    simp [funext_iff]
  rw [he, measure_singleton] at hm
  have hpos : 0 < (volume : Measure (Fin 1 → ℝ)) Set.univ :=
    isOpen_univ.measure_pos volume Set.univ_nonempty
  exact (ne_of_gt hpos) hm

end GMZP0
