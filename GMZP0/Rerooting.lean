import GMZP0.LagReindexing

/-! Full finite-sum rerooting t=r+k-h, with every original interval restriction. -/

noncomputable section
open scoped BigOperators
namespace GMZP0

def rerootLabels (N : ℕ) (h : ℤ) : Finset ℤ :=
  (Finset.Icc 1 (N : ℤ)).filter fun t => 1 ≤ t + h ∧ t + h ≤ N

theorem mem_rerootLabels_iff (N : ℕ) (h t : ℤ) :
    t ∈ rerootLabels N h ↔ (1 ≤ t ∧ t ≤ N) ∧ (1 ≤ t + h ∧ t + h ≤ N) := by
  simp only [rerootLabels, Finset.mem_filter, Finset.mem_Icc]

theorem reroot_lag_bound (N : ℕ) (h t k : ℤ)
    (ht : t ∈ rerootLabels N h) (hk : k ∈ lagInnerInterval N h t) : |k| < N := by
  have ht' := (mem_rerootLabels_iff N h t).1 ht
  exact lag_labels_bound N h k (t - k + h)
    ((lag_domain_reroot N h k t).2 ⟨ht'.1, ht'.2, hk⟩)

def rerootPairDomain (N : ℕ) (h : ℤ) : Finset (ℤ × ℤ) :=
  (rerootLabels N h ×ˢ Finset.Icc (-(N : ℤ)) N).filter fun tk =>
    tk.2 ∈ lagInnerInterval N h tk.1

theorem mem_rerootPairDomain_iff (N : ℕ) (h : ℤ) (tk : ℤ × ℤ) :
    tk ∈ rerootPairDomain N h ↔ tk.1 ∈ rerootLabels N h ∧ tk.2 ∈ lagInnerInterval N h tk.1 := by
  simp only [rerootPairDomain, Finset.mem_filter, Finset.mem_product]
  constructor
  · exact fun ht => ⟨ht.1.1, ht.2⟩
  · rintro ⟨ht, hk⟩
    have hb := abs_lt.mp (reroot_lag_bound N h tk.1 tk.2 ht hk)
    exact ⟨⟨ht, Finset.mem_Icc.mpr ⟨by omega, by omega⟩⟩, hk⟩

/-- The entire lag sum, including k=0, has the manuscript's rerooted inner interval. -/
theorem lag_sum_reroot (N : ℕ) (h : ℤ) (F : ℤ → ℤ → ℝ) :
    (∑ k ∈ Finset.Icc (-(N : ℤ)) N, ∑ r ∈ lagLabels N h k, F k r) =
      ∑ t ∈ rerootLabels N h, ∑ k ∈ lagInnerInterval N h t, F k (t - k + h) := by
  classical
  rw [← Finset.sum_finset_product (lagPairDomain N h) (Finset.Icc (-(N : ℤ)) N)
    (lagLabels N h) (mem_lagPairDomain_iff N h) (f := fun kr => F kr.1 kr.2)]
  calc
    (∑ kr ∈ lagPairDomain N h, F kr.1 kr.2) =
        ∑ tk ∈ rerootPairDomain N h, F tk.2 (tk.1 - tk.2 + h) := by
      apply Finset.sum_bij (fun kr _ => (kr.2 + kr.1 - h, kr.1))
      · intro kr hkr
        have hr := (mem_lagPairDomain_iff N h kr).1 hkr
        have he : kr.2 + kr.1 - h - kr.1 + h = kr.2 := by ring
        have ht := (lag_domain_reroot N h kr.1 (kr.2 + kr.1 - h)).1 (by rw [he]; exact hr.2)
        exact (mem_rerootPairDomain_iff N h _).2
          ⟨(mem_rerootLabels_iff N h _).2 ⟨ht.1, ht.2.1⟩, ht.2.2⟩
      · intro a ha b hb he
        have ht := congrArg Prod.fst he
        have hk := congrArg Prod.snd he
        apply Prod.ext <;> dsimp at ht hk ⊢ <;> omega
      · intro tk htk
        have ht := (mem_rerootPairDomain_iff N h tk).1 htk
        have hb := abs_lt.mp (reroot_lag_bound N h tk.1 tk.2 ht.1 ht.2)
        have ht' := (mem_rerootLabels_iff N h tk.1).1 ht.1
        refine ⟨(tk.2, tk.1 - tk.2 + h), (mem_lagPairDomain_iff N h _).2
          ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩,
            (lag_domain_reroot N h tk.2 tk.1).2 ⟨ht'.1, ht'.2, ht.2⟩⟩, ?_⟩
        apply Prod.ext
        · change tk.1 - tk.2 + h + tk.2 - h = tk.1
          ring
        · rfl
      · intro kr hkr
        congr 1
        dsimp
        ring
    _ = _ := Finset.sum_finset_product (rerootPairDomain N h) (rerootLabels N h)
      (lagInnerInterval N h) (mem_rerootPairDomain_iff N h)

end GMZP0
