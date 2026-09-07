import GMZP0.SafeWindowGeometry
import GMZP0.SecondStatistic

/-! Cardinality and original-weight cost of the two vertical boundary strips. -/

noncomputable section
open scoped BigOperators
namespace GMZP0

theorem fin_initial_strip_card_le (n L : ℕ) :
    (Finset.univ.filter (fun v : Fin n => v.val < L)).card ≤ L := by
  let A := Finset.univ.filter (fun v : Fin n => v.val < L)
  let f : A → Fin L := fun v => ⟨v.val.val, (Finset.mem_filter.mp v.property).2⟩
  have hinj : Function.Injective f := by
    intro v w h
    have he := congrArg (fun a : Fin L => a.val) h
    apply Subtype.ext
    apply Fin.ext
    exact he
  have hc := Fintype.card_le_of_injective f hinj
  simpa only [Fintype.card_coe, Fintype.card_fin] using hc

theorem fin_final_strip_card_le (n L : ℕ) :
    (Finset.univ.filter (fun v : Fin n => n ≤ v.val + L)).card ≤ L := by
  let A := Finset.univ.filter (fun v : Fin n => n ≤ v.val + L)
  let f : A → Fin L := fun v => ⟨n - 1 - v.val.val, by
    have hv := (Finset.mem_filter.mp v.property).2
    have hvn := v.val.isLt
    omega⟩
  have hinj : Function.Injective f := by
    intro v w h
    have he := congrArg Fin.val h
    have hv := v.val.isLt
    have hw := w.val.isLt
    change n - 1 - v.val.val = n - 1 - w.val.val at he
    apply Subtype.ext
    apply Fin.ext
    omega
  have hc := Fintype.card_le_of_injective f hinj
  simpa only [Fintype.card_coe, Fintype.card_fin] using hc

/-- The bound remains valid if the two strips overlap. -/
theorem fin_boundary_strips_card_le (n L : ℕ) :
    (Finset.univ.filter (fun v : Fin n => ¬ (L ≤ v.val ∧ v.val + L < n))).card ≤ 2 * L := by
  let A := Finset.univ.filter (fun v : Fin n => v.val < L)
  let B := Finset.univ.filter (fun v : Fin n => n ≤ v.val + L)
  have hsub : Finset.univ.filter (fun v : Fin n => ¬ (L ≤ v.val ∧ v.val + L < n)) ⊆ A ∪ B := by
    intro v hv
    have hv' := (Finset.mem_filter.mp hv).2
    simp only [A, B, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    omega
  have ha := fin_initial_strip_card_le n L
  have hb := fin_final_strip_card_le n L
  have hc := (Finset.card_le_card hsub).trans (Finset.card_union_le A B)
  dsimp [A, B] at hc
  omega

def safeRows (N H : ℕ) : Finset (Fin (N ^ 2)) :=
  Finset.univ.filter fun v => 3 * H * N ≤ v.val ∧ v.val + 3 * H * N < N ^ 2

def safeBaseSet (N H : ℕ) : Finset (Base N) := Finset.univ ×ˢ safeRows N H

def boundaryBaseSet (N H : ℕ) : Finset (Base N) :=
  Finset.univ ×ˢ (Finset.univ.filter fun v : Fin (N ^ 2) => v ∉ safeRows N H)

/-- The finite row predicate is exactly the manuscript's one-based integer safe interval. -/
theorem mem_safeRows_iff (N H : ℕ) (v : Fin (N ^ 2)) :
    v ∈ safeRows N H ↔ SafeVertical (N : ℤ) H ((v.val : ℤ) + 1) := by
  simp only [safeRows, Finset.mem_filter, Finset.mem_univ, true_and, SafeVertical]
  have hcast : ((3 * H * N : ℕ) : ℤ) = 3 * (H : ℤ) * N := by push_cast; ring
  have hpow : ((N ^ 2 : ℕ) : ℤ) = (N : ℤ) ^ 2 := by push_cast; rfl
  omega

theorem boundaryBaseSet_card_le (N H : ℕ) : (boundaryBaseSet N H).card ≤ 6 * H * N ^ 2 := by
  rw [boundaryBaseSet, Finset.card_product, Finset.card_univ, Fintype.card_fin]
  have hc := fin_boundary_strips_card_le (N ^ 2) (3 * H * N)
  simp only [safeRows, Finset.mem_filter, Finset.mem_univ, true_and]
  calc
    _ ≤ N * (2 * (3 * H * N)) := Nat.mul_le_mul_left N hc
    _ = 6 * H * N ^ 2 := by ring

/-- Deleted boundary mass is bounded using the original pointwise upper bound on mu. -/
theorem boundary_original_mass_le {N : ℕ} (hN : 0 < N) (H : ℕ) (μ : Base N → ℝ)
    (hμ : ∀ z, μ z ≤ (N : ℝ)⁻¹ ^ 3) :
    (∑ z ∈ boundaryBaseSet N H, μ z) ≤ 6 * (H : ℝ) / (N : ℝ) := by
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hc : ((boundaryBaseSet N H).card : ℝ) ≤ 6 * (H : ℝ) * (N : ℝ) ^ 2 := by
    exact_mod_cast boundaryBaseSet_card_le N H
  calc
    (∑ z ∈ boundaryBaseSet N H, μ z) ≤ ∑ _z ∈ boundaryBaseSet N H, (N : ℝ)⁻¹ ^ 3 :=
      Finset.sum_le_sum fun z _ => hμ z
    _ = ((boundaryBaseSet N H).card : ℝ) * (N : ℝ)⁻¹ ^ 3 := by simp
    _ ≤ (6 * (H : ℝ) * (N : ℝ) ^ 2) * (N : ℝ)⁻¹ ^ 3 :=
      mul_le_mul_of_nonneg_right hc (pow_nonneg (inv_nonneg.mpr (Nat.cast_nonneg N)) 3)
    _ = 6 * (H : ℝ) / (N : ℝ) := by field_simp

theorem safe_boundary_mass_partition (N H : ℕ) (μ : Base N → ℝ) :
    (∑ z ∈ safeBaseSet N H, μ z) + (∑ z ∈ boundaryBaseSet N H, μ z) = ∑ z : Base N, μ z := by
  simp only [safeBaseSet, boundaryBaseSet, Finset.sum_product, Finset.sum_filter,
    Fintype.sum_prod_type, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x _
  have hs : ∑ v ∈ safeRows N H, μ (x, v) =
      ∑ v : Fin (N ^ 2), if v ∈ safeRows N H then μ (x, v) else 0 := by simp
  rw [hs, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro v _
  by_cases hv : v ∈ safeRows N H <;> simp [hv]

theorem safe_original_mass_lower {N : ℕ} (hN : 0 < N) (H : ℕ) (μ : Base N → ℝ) (κ : ℝ)
    (hμ : ∀ z, μ z ≤ (N : ℝ)⁻¹ ^ 3) (hmass : κ ≤ ∑ z, μ z) :
    κ - 6 * (H : ℝ) / (N : ℝ) ≤ ∑ z ∈ safeBaseSet N H, μ z := by
  have hdel := boundary_original_mass_le hN H μ hμ
  have hsplit := safe_boundary_mass_partition N H μ
  linarith only [hmass, hdel, hsplit]

end GMZP0
