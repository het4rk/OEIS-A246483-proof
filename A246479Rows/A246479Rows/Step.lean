import A246479Rows.Types

/-!
# The linear step and the closed form of `T`
-/

open Finset

namespace A246479

variable (k : ℕ)

/-- one step of the type-value recursion -/
def step (s : St) : St where
  A := Sxx k s
  B := Snm k s
  Bm := Sym k s
  C := Snm k s
  Cm := Sxm k s
  D := Sxx k s - s.B
  Dm := Sxx k s - s.Bm
  E := Snm k s - s.E
  E1 := Snm k s - s.E3
  E2 := Sxm k s - s.E1
  E3 := Sym k s - s.E2

set_option maxHeartbeats 1000000 in
theorem typ_step (s : St) (c x y : Fin (k + 1)) :
    typ k (step k s) c x y =
      if x = c.rev ∨ y = c.rev then 0 else pairv k s x y - typ k s x y c.rev := by
  by_cases h1 : x = c.rev
  · simp [typ, h1]
  by_cases h2 : y = c.rev
  · simp [typ, h2]
  by_cases h3 : y = x.rev
  · simp [typ, pairv, h1, h2, h3]
  have h1' : c ≠ x.rev := fun h => h1 (by rw [h, Fin.rev_rev])
  have h2' : c ≠ y.rev := fun h => h2 (by rw [h, Fin.rev_rev])
  have h3' : x ≠ y.rev := fun h => h3 (by rw [h, Fin.rev_rev])
  have r1 : c.rev ≠ x := fun h => h1' (by rw [← h, Fin.rev_rev])
  have r2 : c.rev ≠ y := fun h => h2' (by rw [← h, Fin.rev_rev])
  have hcmid : c.rev = c → x.rev ≠ x ∧ y.rev ≠ y := fun hc =>
    ⟨fun hx => h1 (by rw [mid_unique hx hc, hc]), fun hy => h2 (by rw [mid_unique hy hc, hc])⟩
  have hxmid : x.rev = x → y.rev ≠ y := fun hx hy => h3 (by rw [mid_unique hy hx, hx])
  by_cases hc : c.rev = c
  · obtain ⟨hx, hy⟩ := hcmid hc
    have hx' : x ≠ x.rev := fun h => hx h.symm
    have hy' : y ≠ y.rev := fun h => hy h.symm
    have hcx : c ≠ x := fun h => hx (h ▸ hc)
    have hcy : c ≠ y := fun h => hy (h ▸ hc)
    by_cases hxy : x = y
    · subst hxy
      simp [typ, pairv, step, h1, h2, h3, h1', h2', h3', r1, r2, hc, hx, hy, hx', hcx, hcy, Ne.symm hcx,
        Ne.symm hcy]
    · simp [typ, pairv, step, h1, h2, h3, h1', h2', h3', r1, r2, hc, hx, hy, hx', hy', hcx, hcy,
        Ne.symm hcx, Ne.symm hcy, hxy, Ne.symm hxy]
  have hc' : c ≠ c.rev := fun h => hc h.symm
  by_cases hx : x.rev = x
  · have hy := hxmid hx
    have hy' : y ≠ y.rev := fun h => hy h.symm
    have hcx : c ≠ x := fun h => hc (h ▸ hx)
    have hxy : x ≠ y := fun h => hy (h ▸ hx)
    by_cases hcy : c = y
    · subst hcy
      simp [typ, pairv, step, h1, h2, h3, h1', h2', h3', r1, r2, hc, hc', hx, hy, hy', hcx, Ne.symm hcx,
        hxy, Ne.symm hxy]
    · simp [typ, pairv, step, h1, h2, h3, h1', h2', h3', r1, r2, hc, hc', hx, hy, hy', hcx, hcy,
        Ne.symm hcx, Ne.symm hcy, hxy, Ne.symm hxy]
  have hx' : x ≠ x.rev := fun h => hx h.symm
  by_cases hy : y.rev = y
  · have hcy : c ≠ y := fun h => hc (h ▸ hy)
    have hxy : x ≠ y := fun h => hx (h ▸ hy)
    by_cases hcx : c = x
    · subst hcx
      simp [typ, pairv, step, h1, h2, h3, h1', h2', h3', r1, r2, hc, hc', hx, hx', hy, hcy, Ne.symm hcy,
        hxy, Ne.symm hxy]
    · simp [typ, pairv, step, h1, h2, h3, h1', h2', h3', r1, r2, hc, hc', hx, hx', hy, hcx, hcy,
        Ne.symm hcx, Ne.symm hcy, hxy, Ne.symm hxy]
  have hy' : y ≠ y.rev := fun h => hy h.symm
  by_cases hcx : c = x <;> by_cases hcy : c = y <;> by_cases hxy : x = y
  all_goals first
    | (simp [typ, pairv, step, h1, h2, h3, h1', h2', h3', r1, r2, hc, hc', hx, hx', hy, hy',
        hcx, hcy, hxy, Ne.symm hcx, Ne.symm hcy, Ne.symm hxy]; done)
    | (simp [typ, pairv, step, h1, h2, h3, h1', h2', h3', r1, r2, hc, hc', hx, hx', hy, hy',
        hcx, hcy, hxy]; done)
    | (simp_all; done)
    | (simp only [hcx, hcy, hxy] at *; simp_all)


lemma N_zero (x y z : Fin (k + 1)) :
    N k 0 x y z = if y = x.rev ∨ z = x.rev ∨ z = y.rev then 0 else 1 := by
  classical
  unfold N
  split_ifs with h
  · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    rintro w _ ⟨hg, h0, h1, h2⟩
    rcases h with h | h | h
    · exact hg 0 1 (by simp) (by simp) (by rw [h0, h1, add_eq_iff]; exact h)
    · exact hg 0 2 (by simp) (by simp) (by rw [h0, h2, add_eq_iff]; exact h)
    · exact hg 1 2 (by simp) (by simp) (by rw [h1, h2, add_eq_iff]; exact h)
  · rw [Finset.card_eq_one]
    refine ⟨![x, y, z], ?_⟩
    ext w
    simp only [mem_filter, mem_univ, true_and, mem_singleton]
    constructor
    · rintro ⟨_, h0, h1, h2⟩
      funext i; fin_cases i <;> simp [h0, h1, h2]
    · rintro rfl
      refine ⟨?_, by simp, by simp, by simp⟩
      simp only [not_or] at h
      intro i j hij hji
      fin_cases i <;> fin_cases j <;> simp at hij
      · simpa [add_eq_iff] using h.1
      · simpa [add_eq_iff] using h.2.1
      · simpa [add_eq_iff] using h.2.2

/-- all type values equal to one -/
def ones : St := ⟨1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1⟩

/-- the type values for words of length `L+3` -/
def V : ℕ → St
  | 0 => ones
  | L + 1 => step k (V L)

lemma V_succ (L : ℕ) : V k (L + 1) = step k (V k L) := rfl

theorem N_eq_typ (L : ℕ) (x y z : Fin (k + 1)) : (N k L x y z : ℤ) = typ k (V k L) x y z := by
  induction L generalizing x y z with
  | zero =>
    rw [N_zero]; unfold typ; simp only [V, ones]
    split_ifs <;> simp
  | succ L ih =>
    rw [N_succ, V_succ, typ_step]
    have hf : univ.filter (fun a : Fin (k + 1) => (x : ℕ) + a ≠ k) = univ.erase x.rev := by
      ext a; simp [add_eq_iff]
    simp only [add_eq_iff]
    split_ifs with h
    · simp
    · rw [hf]; push_cast
      simp only [ih]
      rw [Finset.sum_erase_eq_sub (mem_univ _), pair_sum]

lemma T_eq_sum (n : ℕ) :
    T n k = ∑ x : Fin (k + 1), ∑ y : Fin (k + 1), ∑ z : Fin (k + 1), N k n x y z := by
  classical
  unfold T N
  rw [Finset.card_eq_sum_card_fiberwise (f := fun w : Fin (n + 3) → Fin (k + 1) => w 0)
    (t := univ) (by intro _ _; simp)]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [Finset.card_eq_sum_card_fiberwise (f := fun w : Fin (n + 3) → Fin (k + 1) => w 1)
    (t := univ) (by intro _ _; simp)]
  refine Finset.sum_congr rfl (fun y _ => ?_)
  rw [Finset.card_eq_sum_card_fiberwise (f := fun w : Fin (n + 3) → Fin (k + 1) => w 2)
    (t := univ) (by intro _ _; simp)]
  refine Finset.sum_congr rfl (fun z _ => ?_)
  congr 1; ext w; simp [and_assoc]

/-- row value for a non-middle first letter -/
def Rx (s : St) : ℤ := Sxx k s + (eps k : ℤ) * Sym k s + ((k : ℤ) - 1 - eps k) * Snm k s
/-- row value for the middle letter -/
def Rm (s : St) : ℤ := ((k : ℤ) + 1 - eps k) * Sxm k s

/-- closed form of `T` in terms of the type values -/
def F (s : St) : ℤ := (eps k : ℤ) * Rm k s + ((k : ℤ) + 1 - eps k) * Rx k s

lemma row_sum (s : St) (x : Fin (k + 1)) :
    ∑ y, pairv k s x y = if x.rev = x then Rm k s else Rx k s := by
  classical
  split_ifs with hx
  · rw [sum_spec k _ ∅ (by simp) 0 (Sxm k s)]
    · simp [Rm]
    · intro a ha
      have := mid_unique ha hx; subst this
      simp [pairv, ha]
    · intro a _ ha
      have h1 : ¬ a = x.rev := by rw [hx]; exact fun h => ha (h ▸ hx)
      have h2 : ¬ x = a := fun h => ha (h ▸ hx)
      simp [pairv, h1, h2, Ne.symm h2, hx]
  · have hx' : x ≠ x.rev := fun h => hx h.symm
    rw [sum_spec k _ {x, x.rev} (by
        simp only [mem_insert, mem_singleton]; rintro a (rfl | rfl)
        exacts [hx, rev_ne k hx]) (Sym k s) (Snm k s)]
    · rw [Finset.sum_pair hx', Finset.card_pair hx']
      simp [pairv, Rx, hx, hx'] <;> first | ring1 | exact Or.inl (by ring1)
    · intro a ha
      have h1 : ¬ a = x.rev := ne_rev_of_mid k ha hx
      have h2 : ¬ x = a := fun h => hx (h ▸ ha)
      simp [pairv, h1, h2, hx, ha]
    · intro a ha ham
      simp only [mem_insert, mem_singleton, not_or] at ha
      simp [pairv, ha.1, ha.2, Ne.symm ha.1, ham, hx]

theorem T_eq_F (n : ℕ) : (T n k : ℤ) = F k (V k n) := by
  classical
  rw [T_eq_sum]; push_cast
  simp only [N_eq_typ, pair_sum, row_sum]
  rw [sum_spec k _ ∅ (by simp) (Rm k (V k n)) (Rx k (V k n))]
  · simp [F]
  · intro a ha; simp [ha]
  · intro a _ ha; simp [ha]

end A246479
