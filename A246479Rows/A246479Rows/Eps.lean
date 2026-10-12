import A246479Rows.Step

/-! # The number of middle letters -/

namespace A246479

lemma eps_eq_one (k : ℕ) {h : Fin (k + 1)} (hh : h.rev = h) : eps k = 1 := by
  unfold eps
  rw [Finset.card_eq_one]
  refine ⟨h, ?_⟩
  ext a; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  exact ⟨fun ha => mid_unique ha hh, fun ha => ha ▸ hh⟩

lemma eps_odd {k : ℕ} (hk : Odd k) : eps k = 0 := by
  unfold eps
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro a _ h
  rw [Fin.ext_iff, Fin.val_rev] at h
  obtain ⟨m, hm⟩ := hk
  have := a.isLt
  omega

lemma eps_even {k : ℕ} (hk : Even k) : eps k = 1 := by
  obtain ⟨m, hm⟩ := hk
  refine eps_eq_one k (h := ⟨m, by omega⟩) ?_
  rw [Fin.ext_iff, Fin.val_rev]; simp; omega

end A246479
