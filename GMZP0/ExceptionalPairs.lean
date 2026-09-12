import GMZP0.PairGeometry
import GMZP0.FiniteUnionMean
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Cast.Order.Field

/-! Uniform finite counts for small positive labels and pairs with large gcd.
The reciprocal-square tail is proved by finite telescoping, including empty tails. -/

noncomputable section
open scoped BigOperators
namespace GMZP0

theorem positive_label_multiple_mean {N d : ℕ} :
    realUniformMean (fun h : Fin N => if d ∣ label h then (1 : ℝ) else 0) =
      (N / d : ℕ) / (N : ℝ) := by
  unfold realUniformMean label
  rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => if d ∣ i + 1 then (1 : ℝ) else 0)]
  simp only [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one,
    Nat.card_multiples, Fintype.card_fin]

theorem positive_label_multiple_probability {N d : ℕ} (hN : 0 < N) :
    realUniformMean (fun h : Fin N => if d ∣ label h then (1 : ℝ) else 0) ≤ 1 / (d : ℝ) := by
  rw [positive_label_multiple_mean]
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  calc
    _ ≤ ((N : ℝ) / d) / N := div_le_div_of_nonneg_right Nat.cast_div_le (Nat.cast_nonneg N)
    _ = _ := by
      by_cases hd : d = 0
      · simp [hd]
      · field_simp

theorem small_positive_label_probability {N A : ℕ} (hN : 0 < N) (hA : 0 < A) :
    realUniformMean (fun h : Fin N => if A * label h < N then (1 : ℝ) else 0) ≤ 1 / (A : ℝ) := by
  classical
  let S := Finset.univ.filter (fun h : Fin N => A * label h < N)
  have hcard : S.card ≤ N / A := by
    have hm : Set.MapsTo (fun h : Fin N => h.val) (S : Set (Fin N)) (Finset.range (N / A) : Set ℕ) := by
      intro h hh
      have hv := (Finset.mem_filter.mp hh).2
      apply Finset.mem_range.mpr
      have he : h.val + 1 ≤ N / A := (Nat.le_div_iff_mul_le hA).mpr (by simpa [label, Nat.mul_comm] using hv.le)
      change h.val < N / A
      omega
    have hi : (S : Set (Fin N)).InjOn (fun h : Fin N => h.val) := fun _ _ _ _ he => Fin.ext he
    simpa only [Finset.card_range] using Finset.card_le_card_of_injOn (fun h : Fin N => h.val) hm hi
  have hmean : realUniformMean (fun h : Fin N => if A * label h < N then (1 : ℝ) else 0) =
      (S.card : ℝ) / N := by
    simp only [realUniformMean, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one, Fintype.card_fin, S]
  rw [hmean]
  calc
    _ ≤ (N / A : ℕ) / (N : ℝ) := div_le_div_of_nonneg_right (by exact_mod_cast hcard) (Nat.cast_nonneg N)
    _ ≤ _ := by rw [← positive_label_multiple_mean]; exact positive_label_multiple_probability hN

theorem pair_common_divisor_probability {N d : ℕ} (hN : 0 < N) :
    realUniformMean (fun z : Fin N × Fin N => if d ∣ label z.1 ∧ d ∣ label z.2 then (1 : ℝ) else 0) ≤
      1 / (d : ℝ) ^ 2 := by
  let : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  have he (h h' : Fin N) : (if d ∣ label h ∧ d ∣ label h' then (1 : ℝ) else 0) =
      (if d ∣ label h then 1 else 0) * (if d ∣ label h' then 1 else 0) := by
    split_ifs <;> simp_all
  simp_rw [he]
  rw [realUniformMean_prod (fun h h' : Fin N =>
    (if d ∣ label h then (1 : ℝ) else 0) * (if d ∣ label h' then (1 : ℝ) else 0))]
  simp_rw [realUniformMean_const_mul]
  have hr : realUniformMean (fun h : Fin N => (if d ∣ label h then (1 : ℝ) else 0) *
      realUniformMean (fun h' : Fin N => if d ∣ label h' then (1 : ℝ) else 0)) =
      realUniformMean (fun h : Fin N => if d ∣ label h then (1 : ℝ) else 0) ^ 2 := by
    simp only [realUniformMean, ← Finset.sum_mul]
    ring
  rw [hr]
  simpa only [div_pow, one_pow] using pow_le_pow_left₀
    (realUniformMean_nonneg _ (fun _ => by split_ifs <;> norm_num))
    (positive_label_multiple_probability (d := d) hN) 2

theorem reciprocal_square_tail {A N : ℕ} (hA : 0 < A) :
    ∑ d ∈ Finset.Icc (A + 1) N, 1 / (d : ℝ) ^ 2 ≤ 1 / (A : ℝ) := by
  have hstep (k : ℕ) (hk : 0 < k) :
      1 / ((k : ℝ) + 1) ^ 2 ≤ 1 / (k : ℝ) - 1 / ((k : ℝ) + 1) := by
    have hkr : (0 : ℝ) < k := by exact_mod_cast hk
    have he : 1 / (k : ℝ) - 1 / ((k : ℝ) + 1) = 1 / ((k : ℝ) * (k + 1)) := by
      field_simp
      ring
    rw [he]
    exact one_div_le_one_div_of_le (by positivity) (by nlinarith)
  have hbound : ∀ m : ℕ, ∑ d ∈ Finset.Icc (A + 1) m, 1 / (d : ℝ) ^ 2 ≤
      1 / (A : ℝ) - 1 / (max A m : ℕ) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      by_cases hm : A ≤ m
      · rw [Finset.sum_Icc_succ_top (by omega)]
        rw [max_eq_right hm] at ih
        rw [max_eq_right (by omega : A ≤ m + 1)]
        have hs := hstep m (by omega)
        push_cast
        linarith
      · have he : Finset.Icc (A + 1) (m + 1) = ∅ := Finset.Icc_eq_empty_of_lt (by omega)
        rw [he, Finset.sum_empty, max_eq_left (by omega : m + 1 ≤ A), sub_self]
  have hh := hbound N
  have hn : (0 : ℝ) ≤ 1 / (max A N : ℕ) := by positivity
  linarith

theorem pair_large_gcd_probability {N A : ℕ} (hN : 0 < N) (hA : 0 < A) :
    realUniformMean (fun z : Fin N × Fin N => if A < Nat.gcd (label z.1) (label z.2) then (1 : ℝ) else 0) ≤
      1 / (A : ℝ) := by
  classical
  let D := Finset.Icc (A + 1) N
  have hcover (z : Fin N × Fin N) (hz : A < Nat.gcd (label z.1) (label z.2)) :
      ∃ d : D, d.val ∣ label z.1 ∧ d.val ∣ label z.2 := by
    have hg : Nat.gcd (label z.1) (label z.2) ≤ N :=
      (Nat.gcd_le_left _ (by simp [label])).trans (by simp only [label]; omega)
    refine ⟨⟨Nat.gcd (label z.1) (label z.2), Finset.mem_Icc.mpr ⟨by omega, hg⟩⟩,
      Nat.gcd_dvd_left _ _, Nat.gcd_dvd_right _ _⟩
  have hu := uniform_event_union_le
    (fun z : Fin N × Fin N => A < Nat.gcd (label z.1) (label z.2))
    (fun z (d : D) => d.val ∣ label z.1 ∧ d.val ∣ label z.2) hcover
  calc
    _ ≤ ∑ d : D, realUniformMean (fun z : Fin N × Fin N =>
        if d.val ∣ label z.1 ∧ d.val ∣ label z.2 then (1 : ℝ) else 0) := hu
    _ ≤ ∑ d : D, 1 / (d.val : ℝ) ^ 2 :=
      Finset.sum_le_sum (fun d _ => pair_common_divisor_probability hN)
    _ = ∑ d ∈ Finset.Icc (A + 1) N, 1 / (d : ℝ) ^ 2 := by
      exact Finset.sum_coe_sort D (fun d : ℕ => 1 / (d : ℝ) ^ 2)
    _ ≤ _ := reciprocal_square_tail hA

def pairExceptional (N A : ℕ) (z : Fin N × Fin N) : Prop :=
  A * label z.1 < N ∨ A * label z.2 < N ∨ A < Nat.gcd (label z.1) (label z.2)

instance (N A : ℕ) : DecidablePred (pairExceptional N A) := fun z => by
  unfold pairExceptional
  infer_instance

theorem exceptional_pair_probability {N A : ℕ} (hN : 0 < N) (hA : 0 < A) :
    realUniformMean (fun z : Fin N × Fin N => if pairExceptional N A z then (1 : ℝ) else 0) ≤
      3 / (A : ℝ) := by
  classical
  let : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  have hp (z : Fin N × Fin N) : (if pairExceptional N A z then (1 : ℝ) else 0) ≤
      (if A * label z.1 < N then 1 else 0) + (if A * label z.2 < N then 1 else 0) +
        (if A < Nat.gcd (label z.1) (label z.2) then 1 else 0) := by
    by_cases h₁ : A * label z.1 < N <;>
      by_cases h₂ : A * label z.2 < N <;>
      by_cases h₃ : A < Nat.gcd (label z.1) (label z.2) <;>
      simp [pairExceptional, h₁, h₂, h₃]
  have hm := realUniformMean_mono _ _ hp
  rw [realUniformMean_add, realUniformMean_add] at hm
  have hfirst : realUniformMean (fun z : Fin N × Fin N => if A * label z.1 < N then (1 : ℝ) else 0) ≤
      1 / (A : ℝ) := by
    rw [realUniformMean_prod (fun h (_ : Fin N) => if A * label h < N then (1 : ℝ) else 0)]
    simp only [realUniformMean_const]
    exact small_positive_label_probability hN hA
  have hsecond : realUniformMean (fun z : Fin N × Fin N => if A * label z.2 < N then (1 : ℝ) else 0) ≤
      1 / (A : ℝ) := by
    rw [realUniformMean_prod (fun (_ : Fin N) h => if A * label h < N then (1 : ℝ) else 0)]
    rw [realUniformMean_const]
    exact small_positive_label_probability hN hA
  calc
    _ ≤ 1 / (A : ℝ) + 1 / (A : ℝ) + 1 / (A : ℝ) :=
      hm.trans (add_le_add (add_le_add hfirst hsecond) (pair_large_gcd_probability hN hA))
    _ = _ := by ring

def pairCutoff (u : ℝ) : ℕ := ⌈12 / u⌉₊

theorem pairCutoff_pos (u : ℝ) (hu : 0 < u) : 0 < pairCutoff u := by
  exact Nat.ceil_pos.mpr (by positivity)

theorem exceptional_pair_probability_cutoff {N : ℕ} (hN : 0 < N) (u : ℝ) (hu : 0 < u) :
    realUniformMean (fun z : Fin N × Fin N => if pairExceptional N (pairCutoff u) z then (1 : ℝ) else 0) ≤
      u / 4 := by
  classical
  have hA := pairCutoff_pos u hu
  have hAr : (0 : ℝ) < pairCutoff u := by exact_mod_cast hA
  have hceil : 12 / u ≤ (pairCutoff u : ℝ) := Nat.le_ceil _
  have hprod := (div_le_iff₀ hu).mp hceil
  refine (exceptional_pair_probability hN hA).trans ?_
  apply (div_le_iff₀ hAr).mpr
  nlinarith

end GMZP0
