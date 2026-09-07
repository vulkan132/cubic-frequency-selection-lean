import GMZP0.SafeWindowGeometry

/-! Exact integer label ranges and lag coordinates for pairs of original collisions. -/

noncomputable section
namespace GMZP0

def horizontalGap {N : ℕ} (x x' : Fin N) : ℤ := (x'.val : ℤ) - (x.val : ℤ)

def blockLabels (N : ℕ) (h : ℤ) : Finset ℤ :=
  (Finset.Icc 1 (N : ℤ)).filter fun r => 1 ≤ r - h ∧ r - h ≤ N

def lagLabels (N : ℕ) (h k : ℤ) : Finset ℤ :=
  (blockLabels N h).filter fun r => r + k ∈ blockLabels N h

def lagInnerInterval (N : ℕ) (h t : ℤ) : Finset ℤ :=
  Finset.Icc (t - N) (t - 1) ∩ Finset.Icc (t + h - N) (t + h - 1)

theorem integer_label_bounds {N : ℕ} (r : Fin N) : 1 ≤ (label r : ℤ) ∧ (label r : ℤ) ≤ N := by
  have hr := r.isLt
  simp only [label, Nat.cast_add, Nat.cast_one]
  omega

theorem horizontalGap_ne_zero {N : ℕ} (x x' : Fin N) (hx : x ≠ x') : horizontalGap x x' ≠ 0 := by
  intro he
  apply hx
  apply Fin.ext
  unfold horizontalGap at he
  omega

theorem mem_blockLabels_iff (N : ℕ) (h r : ℤ) :
    r ∈ blockLabels N h ↔ (1 ≤ r ∧ r ≤ N) ∧ (1 ≤ r - h ∧ r - h ≤ N) := by
  simp only [blockLabels, Finset.mem_filter, Finset.mem_Icc]

theorem mem_lagLabels_iff (N : ℕ) (h k r : ℤ) :
    r ∈ lagLabels N h k ↔
      ((1 ≤ r ∧ r ≤ N) ∧ (1 ≤ r - h ∧ r - h ≤ N)) ∧
      ((1 ≤ r + k ∧ r + k ≤ N) ∧ (1 ≤ r + k - h ∧ r + k - h ≤ N)) := by
  simp only [lagLabels, Finset.mem_filter, mem_blockLabels_iff]

theorem lag_labels_bound (N : ℕ) (h k r : ℤ) (hr : r ∈ lagLabels N h k) : |k| < N := by
  have hb := (mem_lagLabels_iff N h k r).1 hr
  apply abs_lt.mpr
  constructor <;> omega

/-- The exact t=r+k-h change of variables yields the paper's two outer labels and inner interval. -/
theorem lag_domain_reroot (N : ℕ) (h k t : ℤ) :
    t - k + h ∈ lagLabels N h k ↔
      (1 ≤ t ∧ t ≤ N) ∧ (1 ≤ t + h ∧ t + h ≤ N) ∧ k ∈ lagInnerInterval N h t := by
  simp only [mem_lagLabels_iff, lagInnerInterval, Finset.mem_inter, Finset.mem_Icc]
  omega

/-- Two original endpoint collisions force the lag displacement and preserve the shared target. -/
theorem double_collision_coordinates {N : ℕ} (x x' : Fin N) (y t v : Fin (N ^ 2))
    (r s r' s' : Fin N)
    (he : endpointIndex (x, y) r = endpointIndex (x', v) s)
    (he' : endpointIndex (x, t) r' = endpointIndex (x', v) s') :
    (label s : ℤ) = (label r : ℤ) - horizontalGap x x' ∧
    (label s' : ℤ) = (label r' : ℤ) - horizontalGap x x' ∧
    (v.val : ℤ) + 1 = (y.val : ℤ) + 1 +
      2 * horizontalGap x x' * (label r : ℤ) - horizontalGap x x' ^ 2 ∧
    (t.val : ℤ) + 1 = (y.val : ℤ) + 1 +
      2 * horizontalGap x x' * ((label r : ℤ) - (label r' : ℤ)) := by
  have h1 := (endpointIndex_collision_iff (x, y) (x', v) r s).1 he
  have h2 := (endpointIndex_collision_iff (x, t) (x', v) r' s').1 he'
  simp only [basePoint, add_sub_add_right_eq_sub] at h1 h2
  refine ⟨h1.1, h2.1, h1.2, ?_⟩
  unfold horizontalGap
  nlinarith only [h1.2, h2.2]

theorem double_collision_labels {N : ℕ} (x x' : Fin N) (y t v : Fin (N ^ 2))
    (r s r' s' : Fin N)
    (he : endpointIndex (x, y) r = endpointIndex (x', v) s)
    (he' : endpointIndex (x, t) r' = endpointIndex (x', v) s') :
    (label r' : ℤ) ∈ lagLabels N (horizontalGap x x') ((label r : ℤ) - (label r' : ℤ)) := by
  have hg := double_collision_coordinates x x' y t v r s r' s' he he'
  have hr := integer_label_bounds r
  have hs := integer_label_bounds s
  have hr' := integer_label_bounds r'
  have hs' := integer_label_bounds s'
  rw [mem_lagLabels_iff]
  omega

theorem double_collision_zero_lag_iff {N : ℕ} (x x' : Fin N) (hx : x ≠ x')
    (y t v : Fin (N ^ 2)) (r s r' s' : Fin N)
    (he : endpointIndex (x, y) r = endpointIndex (x', v) s)
    (he' : endpointIndex (x, t) r' = endpointIndex (x', v) s') :
    t = y ↔ (label r : ℤ) - (label r' : ℤ) = 0 := by
  have hg := (double_collision_coordinates x x' y t v r s r' s' he he').2.2.2
  have hzero := vertical_lag_zero_iff ((y.val : ℤ) + 1) (horizontalGap x x')
    ((label r : ℤ) - (label r' : ℤ)) (horizontalGap_ne_zero x x' hx)
  constructor
  · intro hty
    apply hzero.1
    rw [← hg, hty]
  · intro hk
    have hval : (t.val : ℤ) = (y.val : ℤ) := by rw [hk] at hg; linarith only [hg]
    apply Fin.ext
    exact_mod_cast hval

end GMZP0
