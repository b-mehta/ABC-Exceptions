import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Order.Interval.Finset.Nat

noncomputable section

open Set

variable {d : ℕ}

-- TODO (BM): move everything in this section to mathlib
section

lemma Nat.Iic_eq_Icc (n : ℕ) : Finset.Iic n = Finset.Icc 0 n := by simp [Finset.Iic_eq_Icc]

theorem Finset.Ico_union_Icc_eq_Icc {α : Type*} [LinearOrder α] [DecidableEq α]
    [LocallyFiniteOrder α] {a b c : α} (h₁ : a ≤ b) (h₂ : b ≤ c) :
    Ico a b ∪ Icc b c = Icc a c := by
  simp [← Finset.coe_inj, Set.Ico_union_Icc_eq_Icc h₁ h₂]

theorem Nat.Ico_union_Icc_eq_Icc {a b c : ℕ} (h₁ : a ≤ b) (h₂ : b ≤ c + 1) :
    Finset.Ico a b ∪ Finset.Icc b c = Finset.Icc a c := by
  ext i
  simp only [Finset.mem_union, Finset.mem_Ico, Finset.mem_Icc]
  omega

theorem Nat.Icc_union_Icc_eq_Icc {a b c : ℕ} (h₁ : a ≤ b) (h₂ : b ≤ c) :
    Finset.Icc a b ∪ Finset.Icc (b + 1) c = Finset.Icc a c := by
  ext i
  simp only [Finset.mem_union, Finset.mem_Icc]
  omega

@[to_additive]
theorem Finset.prod_Icc_succ_bot {M : Type*} [CommMonoid M] {a b : ℕ}
    (hab : a ≤ b) (f : ℕ → M) :
    (∏ k in Icc a b, f k) = f a * (∏ k in Icc (a + 1) b, f k) := by
  rw [← Nat.Icc_insert_succ_left hab, prod_insert]
  simp

lemma Finset.finite_subsets (s : Finset ℕ) : {a | a ⊆ s}.Finite := by
  simpa using s.powerset.finite_toSet

@[to_additive]
lemma prod_Icc_eq_prod_range_mul_prod_Icc {α : Type*} [CommMonoid α] {f : ℕ → α} {t : ℕ}
    (ht : t ≤ d + 1) :
    ∏ i ≤ d, f i = (∏ i ∈ Finset.range t, f i) * ∏ i ∈ Finset.Icc t d, f i := by
  rw [Nat.Iic_eq_Icc, ← Nat.Ico_union_Icc_eq_Icc (zero_le _) ht, Nat.Ico_zero_eq_range,
    Finset.prod_union]
  simp +contextual [Finset.disjoint_left]

-- See note [no_index around OfNat.ofNat]
theorem coe_ofNat_eq_mod (m n : ℕ) [NeZero m] :
    ((no_index (OfNat.ofNat n) : Fin m) : ℕ) = OfNat.ofNat n % m :=
  rfl

@[simp]
theorem coe_ofNat_of_lt (m n : ℕ) [NeZero m] (h : n < m) :
    ((no_index (OfNat.ofNat n) : Fin m) : ℕ) = OfNat.ofNat n := by
  rwa [Fin.coe_ofNat_eq_mod, Nat.mod_eq_of_lt]

lemma Iic_sdiff_Icc_eq_inter {α : Type*} [LinearOrder α]
    [LocallyFiniteOrder α] [LocallyFiniteOrderBot α] {x y : α} :
    Finset.Iic x \ Finset.Icc y x = Finset.Iic x ∩ Finset.Iio y := by
  ext a; simp +contextual [- not_and]

lemma Iic_sdiff_Icc_of_le {α : Type*}  [LinearOrder α]
    [LocallyFiniteOrder α] [LocallyFiniteOrderBot α] {x y : α} (h : y ≤ x) :
    Finset.Iic x \ Finset.Icc y x = Finset.Iio y := by
  ext a
  have : a < y → a < x := fun h₁ ↦ h₁.trans_le h
  simp only [Finset.mem_sdiff, Finset.mem_Icc, not_and']
  aesop (add unsafe forward le_of_lt)

end
