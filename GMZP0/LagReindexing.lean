import GMZP0.IntegerBlockFormula

/-! Complete finite-sum change of variables (r₁,r₂) ↔ (k=r₁-r₂,r=r₂). -/

noncomputable section
open scoped BigOperators
namespace GMZP0

theorem lagLabels_empty_of_large_lag (N : ℕ) (h k : ℤ) (hk : (N : ℤ) ≤ |k|) :
    lagLabels N h k = ∅ := by
  apply Finset.eq_empty_of_forall_notMem
  intro r hr
  exact (not_lt_of_ge hk) (lag_labels_bound N h k r hr)

def lagPairDomain (N : ℕ) (h : ℤ) : Finset (ℤ × ℤ) :=
  ((Finset.Icc (-(N : ℤ)) N) ×ˢ blockLabels N h).filter fun kr =>
    kr.2 + kr.1 ∈ blockLabels N h

theorem mem_lagPairDomain_iff (N : ℕ) (h : ℤ) (kr : ℤ × ℤ) :
    kr ∈ lagPairDomain N h ↔ kr.1 ∈ Finset.Icc (-(N : ℤ)) N ∧ kr.2 ∈ lagLabels N h kr.1 := by
  simp only [lagPairDomain, lagLabels, Finset.mem_filter, Finset.mem_product, and_assoc]

/-- The affine map is a bijection on the complete integer-label domain. -/
theorem integer_label_pair_sum {M : Type*} [AddCommMonoid M] (N : ℕ) (h : ℤ) (F : ℤ → ℤ → M) :
    (∑ a ∈ blockLabels N h, ∑ b ∈ blockLabels N h, F (a - b) b) =
      ∑ k ∈ Finset.Icc (-(N : ℤ)) N, ∑ r ∈ lagLabels N h k, F k r := by
  classical
  rw [← Finset.sum_product']
  calc
    (∑ ab ∈ blockLabels N h ×ˢ blockLabels N h, F (ab.1 - ab.2) ab.2) =
        ∑ kr ∈ lagPairDomain N h, F kr.1 kr.2 := by
      apply Finset.sum_bij (fun ab _ => (ab.1 - ab.2, ab.2))
      · intro ab hab
        have hab' := Finset.mem_product.mp hab
        have hr : ab.2 ∈ lagLabels N h (ab.1 - ab.2) := by
          simp only [lagLabels, Finset.mem_filter]
          exact ⟨hab'.2, by simpa only [add_sub_cancel] using hab'.1⟩
        apply (mem_lagPairDomain_iff N h _).2
        refine ⟨Finset.mem_Icc.mpr ?_, hr⟩
        have hk := abs_lt.mp (lag_labels_bound N h (ab.1 - ab.2) ab.2 hr)
        constructor <;> omega
      · intro a ha b hb he
        have h1 := congrArg Prod.fst he
        have h2 := congrArg Prod.snd he
        apply Prod.ext <;> dsimp at h1 h2 ⊢ <;> omega
      · intro kr hkr
        have hr := (mem_lagPairDomain_iff N h kr).1 hkr
        have hb := (Finset.mem_filter.mp hr.2)
        refine ⟨(kr.2 + kr.1, kr.2), Finset.mem_product.mpr ⟨hb.2, hb.1⟩, ?_⟩
        apply Prod.ext
        · change kr.2 + kr.1 - kr.2 = kr.1
          omega
        · rfl
      · intro ab hab
        rfl
    _ = ∑ k ∈ Finset.Icc (-(N : ℤ)) N, ∑ r ∈ lagLabels N h k, F k r :=
      Finset.sum_finset_product (lagPairDomain N h) (Finset.Icc (-(N : ℤ)) N)
        (lagLabels N h) (mem_lagPairDomain_iff N h)

theorem sum_blockFinLabels {M : Type*} [AddCommMonoid M] (N : ℕ) (h : ℤ) (F : ℤ → M) :
    (∑ r : blockFinLabels N h, F (label r.val)) = ∑ r ∈ blockLabels N h, F r := by
  calc
    (∑ r : blockFinLabels N h, F (label r.val)) =
        ∑ q : blockLabels N h, F (label ((blockLabelEquiv N h).symm q).val) :=
      (Equiv.sum_comp (blockLabelEquiv N h).symm (fun r => F (label r.val))).symm
    _ = ∑ q : blockLabels N h, F q.val := by simp only [blockLabelEquiv_symm_value]
    _ = ∑ r ∈ blockLabels N h, F r := by rw [Finset.sum_coe_sort]

theorem label_difference_ne_zero_iff {N : ℕ} (r s : Fin N) :
    (label r : ℤ) - (label s : ℤ) ≠ 0 ↔ s ≠ r := by
  constructor
  · intro hn he
    subst s
    exact hn (sub_self _)
  · intro hn he
    apply hn
    apply Fin.ext
    simp only [label, Nat.cast_add, Nat.cast_one] at he
    omega

/-- Equal labels become exactly k=0, without deleting or adding any nonzero-lag term. -/
theorem distinct_label_pair_sum (N : ℕ) (h : ℤ) (F : ℤ → ℤ → ℝ) :
    (∑ r : blockFinLabels N h, ∑ s : blockFinLabels N h,
      if s ≠ r then F ((label r.val : ℤ) - (label s.val : ℤ)) (label s.val) else 0) =
      ∑ k ∈ Finset.Icc (-(N : ℤ)) N, ∑ r ∈ lagLabels N h k, if k ≠ 0 then F k r else 0 := by
  classical
  have he : ∀ r s : blockFinLabels N h,
      (s ≠ r) ↔ (label r.val : ℤ) - (label s.val : ℤ) ≠ 0 := by
    intro r s
    rw [label_difference_ne_zero_iff]
    exact not_congr Subtype.val_inj.symm
  simp_rw [he]
  calc
    (∑ r : blockFinLabels N h, ∑ s : blockFinLabels N h,
        if (label r.val : ℤ) - (label s.val : ℤ) ≠ 0 then
          F ((label r.val : ℤ) - (label s.val : ℤ)) (label s.val) else 0) =
        ∑ r : blockFinLabels N h, ∑ b ∈ blockLabels N h,
          if (label r.val : ℤ) - b ≠ 0 then F ((label r.val : ℤ) - b) b else 0 := by
      apply Finset.sum_congr rfl
      intro r _
      exact sum_blockFinLabels N h (fun b => if (label r.val : ℤ) - b ≠ 0 then
        F ((label r.val : ℤ) - b) b else 0)
    _ = ∑ a ∈ blockLabels N h, ∑ b ∈ blockLabels N h,
        if a - b ≠ 0 then F (a - b) b else 0 :=
      sum_blockFinLabels N h (fun a => ∑ b ∈ blockLabels N h, if a - b ≠ 0 then F (a - b) b else 0)
    _ = _ := integer_label_pair_sum N h (fun k r => if k ≠ 0 then F k r else 0)

end GMZP0
