import A246479Rows.Basic

/-!
# Triple types for OEIS A246479

`N k L x y z` depends only on the *type* of the triple `(x,y,z)`: which letters coincide and
which (if any) is the self-complementary middle letter `k/2`.  There are eleven types; their
values evolve by an explicit linear step `step`, proved in `N_eq_typ`.
-/

open Finset

namespace A246479

lemma add_eq_iff {k : ℕ} {x y : Fin (k + 1)} : (x : ℕ) + y = k ↔ y = x.rev := by
  rw [Fin.ext_iff, Fin.val_rev]
  have := x.isLt; have := y.isLt
  omega

lemma mid_unique {k : ℕ} {x y : Fin (k + 1)} (hx : x.rev = x) (hy : y.rev = y) : x = y := by
  rw [Fin.ext_iff] at hx hy ⊢
  rw [Fin.val_rev] at hx hy
  omega

lemma eq_rev_comm {k : ℕ} {x y : Fin (k + 1)} : x = y.rev ↔ y = x.rev := by
  constructor <;> rintro rfl <;> simp

variable (k : ℕ)

/-- number of self-complementary letters (1 if `k` is even, 0 if `k` is odd) -/
def eps : ℕ := (univ.filter (fun a : Fin (k + 1) => a.rev = a)).card

/-- Splitting a sum over the alphabet into a finite special set `S` (free of middle letters),
the middle letters, and the rest. -/
lemma sum_spec (f : Fin (k + 1) → ℤ) (S : Finset (Fin (k + 1))) (hS : ∀ a ∈ S, a.rev ≠ a)
    (m o : ℤ) (hm : ∀ a, a.rev = a → f a = m) (ho : ∀ a, a ∉ S → a.rev ≠ a → f a = o) :
    ∑ a, f a = ∑ a ∈ S, f a + (eps k : ℤ) * m + ((k : ℤ) + 1 - S.card - eps k) * o := by
  classical
  rw [← Finset.sum_add_sum_compl S f,
    ← Finset.sum_filter_add_sum_filter_not Sᶜ (fun a : Fin (k + 1) => a.rev = a)]
  have hM : Sᶜ.filter (fun a : Fin (k + 1) => a.rev = a) =
      univ.filter (fun a : Fin (k + 1) => a.rev = a) := by
    ext a; simp only [mem_filter, mem_compl, mem_univ, true_and, and_iff_right_iff_imp]
    intro ha haS; exact hS a haS ha
  have hc := Finset.card_filter_add_card_filter_not (s := Sᶜ)
    (fun a : Fin (k + 1) => a.rev = a)
  rw [hM, Finset.card_compl, Fintype.card_fin] at hc
  have hSle : S.card ≤ k + 1 := by
    simpa using Finset.card_le_univ S
  rw [Finset.sum_congr rfl (fun a ha => hm a (mem_filter.mp ha).2),
    Finset.sum_congr rfl (fun a ha => ho a (mem_compl.mp (mem_filter.mp ha).1)
      (mem_filter.mp ha).2)]
  simp only [sum_const, nsmul_eq_mul]
  unfold eps
  have : (((Sᶜ.filter (fun a : Fin (k + 1) => ¬ a.rev = a)).card : ℕ) : ℤ) =
      (k : ℤ) + 1 - S.card - (univ.filter (fun a : Fin (k + 1) => a.rev = a)).card := by
    omega
  rw [this, hM]; ring

/-- the eleven type values -/
@[ext] structure St where
  A : ℤ
  B : ℤ
  Bm : ℤ
  C : ℤ
  Cm : ℤ
  D : ℤ
  Dm : ℤ
  E : ℤ
  E1 : ℤ
  E2 : ℤ
  E3 : ℤ

/-- value of `N` on a triple according to its type -/
def typ (s : St) (x y z : Fin (k + 1)) : ℤ :=
  if y = x.rev ∨ z = x.rev ∨ z = y.rev then 0
  else if x = y then (if y = z then s.A else if z.rev = z then s.Bm else s.B)
  else if x = z then (if y.rev = y then s.Cm else s.C)
  else if y = z then (if x.rev = x then s.Dm else s.D)
  else if x.rev = x then s.E1 else if y.rev = y then s.E2
  else if z.rev = z then s.E3 else s.E

/-- pair sums, according to the type of the pair -/
def Sxx (s : St) : ℤ := s.A + (eps k : ℤ) * s.Bm + ((k : ℤ) - 1 - eps k) * s.B
def Snm (s : St) : ℤ := s.C + s.D + (eps k : ℤ) * s.E3 + ((k : ℤ) - 3 - eps k) * s.E
def Sxm (s : St) : ℤ := s.Dm + ((k : ℤ) - 1 - eps k) * s.E1
def Sym (s : St) : ℤ := s.Cm + ((k : ℤ) - 1 - eps k) * s.E2

def pairv (s : St) (x y : Fin (k + 1)) : ℤ :=
  if y = x.rev then 0 else if x = y then Sxx k s else if x.rev = x then Sxm k s
  else if y.rev = y then Sym k s else Snm k s

lemma rev_ne_of_ne_rev {x y : Fin (k + 1)} (h : ¬ y = x.rev) : ¬ x = y.rev := by
  rwa [eq_rev_comm]

lemma rev_ne {a : Fin (k + 1)} (h : a.rev ≠ a) : a.rev.rev ≠ a.rev := by
  rw [Fin.rev_rev]; exact fun e => h e.symm

lemma ne_rev_of_mid {a x : Fin (k + 1)} (ha : a.rev = a) (hx : x.rev ≠ x) : a ≠ x.rev := by
  intro h
  have h1 : x = a := by rw [← Fin.rev_rev x, ← h, ha]
  apply hx; rw [h1, ha]

theorem pair_sum (s : St) (x y : Fin (k + 1)) : ∑ a, typ k s x y a = pairv k s x y := by
  classical
  by_cases h0 : y = x.rev
  · rw [Finset.sum_eq_zero (fun a _ => by unfold typ; simp [h0])]
    simp [pairv, h0]
  have h0' := rev_ne_of_ne_rev k h0
  by_cases hxy : x = y
  · subst hxy
    have hx : x.rev ≠ x := fun h => h0 h.symm
    have hx' : x ≠ x.rev := fun h => hx h.symm
    rw [sum_spec k _ {x, x.rev} (by
        simp only [mem_insert, mem_singleton]; rintro a (rfl | rfl)
        exacts [hx, rev_ne k hx]) s.Bm s.B]
    · rw [Finset.sum_pair hx', Finset.card_pair hx']
      simp [typ, pairv, Sxx, hx, hx'] <;> first | ring1 | exact Or.inl trivial | (ring_nf; simp)
    · intro a ha
      have h1 : a ≠ x := fun h => hx (h ▸ ha)
      have h2 : a ≠ x.rev := ne_rev_of_mid k ha hx
      simp [typ, ha, h1, h2, Ne.symm h1, hx, hx']
    · intro a ha ham
      simp only [mem_insert, mem_singleton, not_or] at ha
      simp [typ, ha.1, ha.2, Ne.symm ha.1, ham, hx, hx']
  by_cases hx : x.rev = x
  · have hy : y.rev ≠ y := fun h => hxy (mid_unique hx h)
    have hy' : y ≠ y.rev := fun h => hy h.symm
    rw [sum_spec k _ {y, y.rev} (by
        simp only [mem_insert, mem_singleton]; rintro a (rfl | rfl)
        exacts [hy, rev_ne k hy]) 0 s.E1]
    · rw [Finset.sum_pair hy', Finset.card_pair hy']
      simp [typ, pairv, Sxm, hx, hy, hy', h0, h0', hxy, Ne.symm hxy] <;> first | ring1 | exact Or.inl trivial | (ring_nf; simp)
    · intro a ha
      have := mid_unique ha hx; subst this
      simp [typ, ha]
    · intro a ha ham
      simp only [mem_insert, mem_singleton, not_or] at ha
      have h1 : a ≠ x := fun h => ham (h ▸ hx)
      simp [typ, ha.1, ha.2, Ne.symm ha.1, ham, hx, hxy, h0, h0', h1, Ne.symm h1, Ne.symm hxy]
  have hx' : x ≠ x.rev := fun h => hx h.symm
  by_cases hy : y.rev = y
  · rw [sum_spec k _ {x, x.rev} (by
        simp only [mem_insert, mem_singleton]; rintro a (rfl | rfl)
        exacts [hx, rev_ne k hx]) 0 s.E2]
    · rw [Finset.sum_pair hx', Finset.card_pair hx']
      simp [typ, pairv, Sym, hx, hx', hy, h0, hxy, h0', Ne.symm hxy] <;> first | ring1 | exact Or.inl trivial | (ring_nf; simp)
    · intro a ha
      have := mid_unique ha hy; subst this
      simp [typ, ha]
    · intro a ha ham
      simp only [mem_insert, mem_singleton, not_or] at ha
      have h1 : a ≠ y := fun h => ham (h ▸ hy)
      simp [typ, ha.1, ha.2, Ne.symm ha.1, ham, hx, hxy, h0, h0', h1, hy, Ne.symm h1, Ne.symm hxy]
  -- generic case: four special letters
  have hy' : y ≠ y.rev := fun h => hy h.symm
  have h2 : x.rev ≠ y.rev := fun h => hxy (Fin.rev_injective h)
  rw [sum_spec k _ {x, y, x.rev, y.rev} (by
      simp only [mem_insert, mem_singleton]
      rintro a (rfl | rfl | rfl | rfl)
      exacts [hx, hy, rev_ne k hx, rev_ne k hy]) s.E3 s.E]
  · rw [Finset.sum_insert (by simp [hxy, hx', h0']), Finset.sum_insert (by simp [h0, hy']),
      Finset.sum_pair h2, Finset.card_insert_of_notMem (by simp [hxy, hx', h0']),
      Finset.card_insert_of_notMem (by simp [h0, hy']), Finset.card_pair h2]
    simp [typ, pairv, Snm, hx, hy, hx', hy', h0, hxy, h0', Ne.symm hxy, Ne.symm h0,
      Ne.symm h0'] <;> first | ring1 | exact Or.inl trivial | (ring_nf; simp)
  · intro a ha
    have hax : a ≠ x := fun h => hx (h ▸ ha)
    have hay : a ≠ y := fun h => hy (h ▸ ha)
    have hax' : a ≠ x.rev := ne_rev_of_mid k ha hx
    have hay' : a ≠ y.rev := ne_rev_of_mid k ha hy
    simp [typ, ha, hx, hy, hxy, h0, h0', hax, hay, hax', hay', Ne.symm hax, Ne.symm hay]
  · intro a ha ham
    simp only [mem_insert, mem_singleton, not_or] at ha
    simp [typ, ha.1, ha.2.1, ha.2.2.1, ha.2.2.2, Ne.symm ha.1, Ne.symm ha.2.1, ham, hx, hy,
      hxy, h0, h0']

end A246479
