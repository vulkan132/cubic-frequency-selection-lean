import GMZP0.CircleRoots
import GMZP0.RealGrid
import Mathlib.Data.Int.Interval
import Mathlib.Data.Fintype.EquivFin

/-! A data-independent finite grid for the manuscript's cubic major arcs. -/

noncomputable section
namespace GMZP0

/-- The original circle major-arc condition with a positive bounded denominator. -/
def MajorArc (Q N : ℕ) (a : Frequency) : Prop :=
  ∃ q : ℕ, 1 ≤ q ∧ q ≤ Q ∧ ‖q • a‖ ≤ (Q : ℝ) / (N : ℝ) ^ 3

def gridRadius (Q : ℕ) (b : ℝ) (q : ℕ) : ℕ :=
  ⌈(Q : ℝ) / ((q : ℝ) * b)⌉₊ + 1

/-- The index set depends on Q and b, and has no scale or data argument. -/
def gridIndices (Q : ℕ) (b : ℝ) : Finset (ℕ × ℤ × ℤ) :=
  (Finset.Icc 1 Q).biUnion fun q =>
    (Finset.Ico (0 : ℤ) (q : ℤ)).biUnion fun j =>
      (Finset.Icc (-(gridRadius Q b q : ℤ)) (gridRadius Q b q : ℤ)).image
        (fun l => (q, j, l))

def gridValue (N : ℕ) (b : ℝ) (i : ℕ × ℤ × ℤ) : Frequency :=
  (((i.2.1 : ℝ) / (i.1 : ℝ) + (i.2.2 : ℝ) * b / (N : ℝ) ^ 3 : ℝ) : Frequency)

theorem grid_index_mem (Q q : ℕ) (b : ℝ) (j l : ℤ)
    (hq1 : 1 ≤ q) (hqQ : q ≤ Q) (hj0 : 0 ≤ j) (hjq : j < (q : ℤ))
    (hl : -(gridRadius Q b q : ℤ) ≤ l ∧ l ≤ (gridRadius Q b q : ℤ)) :
    (q, j, l) ∈ gridIndices Q b := by
  apply Finset.mem_biUnion.mpr
  refine ⟨q, Finset.mem_Icc.mpr ⟨hq1, hqQ⟩, ?_⟩
  apply Finset.mem_biUnion.mpr
  refine ⟨j, Finset.mem_Ico.mpr ⟨hj0, hjq⟩, ?_⟩
  exact Finset.mem_image.mpr ⟨l, Finset.mem_Icc.mpr hl, rfl⟩

theorem gridIndices_nonempty (Q : ℕ) (hQ : 1 ≤ Q) (b : ℝ) :
    (gridIndices Q b).Nonempty := by
  refine ⟨(1, 0, 0), grid_index_mem Q 1 b 0 0 le_rfl hQ le_rfl (by norm_num) ?_⟩
  constructor <;> omega

/-- Every major-arc frequency is approximated by one of the explicit constant grid points. -/
theorem majorArc_grid_approximation {N : ℕ} (hN : 0 < N) (Q : ℕ)
    (b : ℝ) (hb : 0 < b) (a : Frequency) (ha : MajorArc Q N a) :
    ∃ i ∈ gridIndices Q b, cubicDistance N a (gridValue N b i) ≤ Real.pi * b := by
  obtain ⟨q, hq1, hqQ, hqa⟩ := ha
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq1
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hqa' : ‖q • a - ((0 : ℝ) : Frequency)‖ ≤ (Q : ℝ) / (N : ℝ) ^ 3 := by
    simpa using hqa
  obtain ⟨j, hj0, hjq, hj⟩ := circle_approx_root_decomposition q hq1 a 0
    ((Q : ℝ) / (N : ℝ) ^ 3) hqa'
  simp only [zero_add] at hj
  obtain ⟨t, ht, htnorm⟩ := exists_nearest_frequency_lift
    (a - (((j : ℝ) / (q : ℝ) : ℝ) : Frequency))
  have htbound : |t| ≤ ((Q : ℝ) / (N : ℝ) ^ 3) / (q : ℝ) := htnorm.le.trans hj
  obtain ⟨l, herr, hl⟩ := cubic_scale_grid_rounding hN b hb t
  have hlreal : |(l : ℝ)| ≤ (gridRadius Q b q : ℝ) := by
    have hsize : |t| * (N : ℝ) ^ 3 / b ≤ (Q : ℝ) / ((q : ℝ) * b) := by
      calc
        |t| * (N : ℝ) ^ 3 / b ≤
            (((Q : ℝ) / (N : ℝ) ^ 3) / (q : ℝ)) * (N : ℝ) ^ 3 / b := by
          exact div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_right htbound (by positivity)) hb.le
        _ = _ := by field_simp
    have hceil := Nat.le_ceil ((Q : ℝ) / ((q : ℝ) * b))
    simp only [gridRadius, Nat.cast_add, Nat.cast_one]
    linarith
  have hlint : -(gridRadius Q b q : ℤ) ≤ l ∧ l ≤ (gridRadius Q b q : ℤ) := by
    obtain ⟨hlo, hhi⟩ := abs_le.mp hlreal
    constructor
    · exact_mod_cast hlo
    · exact_mod_cast hhi
  refine ⟨(q, j, l), grid_index_mem Q q b j l hq1 hqQ hj0 hjq hlint, ?_⟩
  have haeq : a = (((j : ℝ) / (q : ℝ) : ℝ) : Frequency) + (t : Frequency) := by
    simpa only [add_comm] using (sub_eq_iff_eq_add).mp ht.symm
  have hdiff : a - gridValue N b (q, j, l) =
      ((t - (l : ℝ) * b / (N : ℝ) ^ 3 : ℝ) : Frequency) := by
    change a - ((((j : ℝ) / (q : ℝ) + (l : ℝ) * b / (N : ℝ) ^ 3 : ℝ)) : Frequency) = _
    rw [haeq, ← AddCircle.coe_add, ← AddCircle.coe_sub]
    congr 1
    ring
  have hclose : ‖a - gridValue N b (q, j, l)‖ ≤ b / (2 * (N : ℝ) ^ 3) := by
    rw [hdiff]
    exact (QuotientAddGroup.norm_mk_le_norm.trans (by simpa only [Real.norm_eq_abs] using herr))
  calc
    cubicDistance N a (gridValue N b (q, j, l)) ≤
        2 * Real.pi * (N : ℝ) ^ 3 * ‖a - gridValue N b (q, j, l)‖ :=
      cubicDistance_le_circle_scale hN a _
    _ ≤ 2 * Real.pi * (N : ℝ) ^ 3 * (b / (2 * (N : ℝ) ^ 3)) :=
      mul_le_mul_of_nonneg_left hclose (by positivity)
    _ = Real.pi * b := by field_simp

/-- The universal finite list is selected before the frequency to be captured and all data. -/
theorem majorArc_universal_list (Q : ℕ) (hQ : 1 ≤ Q) (ε : ℝ) (hε : 0 < ε) :
    ∃ L : ℕ, 1 ≤ L ∧ ∀ N : ℕ, 1 ≤ N → ∃ β : Fin L → Frequency,
      ∀ a : Frequency, MajorArc Q N a → ∃ j : Fin L, cubicDistance N a (β j) ≤ ε / 2 := by
  classical
  let b := ε / (2 * Real.pi)
  have hb : 0 < b := by dsimp [b]; positivity
  let I := gridIndices Q b
  let e := I.equivFin
  refine ⟨I.card, Finset.card_pos.mpr (gridIndices_nonempty Q hQ b), ?_⟩
  intro N hN
  refine ⟨fun j => gridValue N b (e.symm j).val, ?_⟩
  intro a ha
  obtain ⟨i, hi, hdist⟩ := majorArc_grid_approximation hN Q b hb a ha
  refine ⟨e ⟨i, hi⟩, ?_⟩
  simp only [Equiv.symm_apply_apply]
  apply hdist.trans_eq
  dsimp [b]
  field_simp

end GMZP0
