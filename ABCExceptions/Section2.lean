/-
Copyright (c) 2025 Bhavik Mehta, Arend Mellendijk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Arend Mellendijk
-/

import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Data.Nat.Squarefree
import Mathlib.Data.Real.StarOrdered
import Mathlib.Order.CompletePartialOrder

import ABCExceptions.ForMathlib.RingTheory.Radical

open Finset UniqueFactorizationMonoid

/--
The set (as a `Finset`) of exceptions to the abc conjecture at `ε` inside [1, X] ^ 3, in particular
the set of triples `(a, b, c)` which are
* pairwise coprime,
* contained in `[1, X] ^ 3`,
* satisfy `a + b = c`,
* have `radical (a * b * c) < c ^ (1 - ε)`

Note this has a slight difference from the usual formulation, which has
`radical (a * b * c) ^ (1 + ε) < c` instead.
-/
noncomputable def Finset.abcExceptionsBelow (ε : ℝ) (X : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  (Finset.Icc (1, 1, 1) (X, X, X)).filter fun ⟨a, b, c⟩ ↦
    a.Coprime b ∧ a.Coprime c ∧ b.Coprime c ∧
    a + b = c ∧
    radical (a * b * c) < (c ^ (1 - ε) : ℝ)

@[simp]
theorem Finset.mem_abcExceptionsBelow (ε : ℝ) (X : ℕ) (a b c : ℕ) :
    ⟨a, b, c⟩ ∈ abcExceptionsBelow ε X ↔
      a.Coprime b ∧ a.Coprime c ∧ b.Coprime c ∧
      a + b = c ∧
      radical (a * b * c) < (c ^ (1 - ε) : ℝ) ∧
      (a, b, c) ∈ Set.Icc (1, 1, 1) (X, X, X) := by
  simp [abcExceptionsBelow]
  tauto

@[gcongr]
lemma Finset.abcExceptionsBelow_mono_right {ε : ℝ} {X Y : ℕ} (hXY : X ≤ Y) :
    abcExceptionsBelow ε X ⊆ abcExceptionsBelow ε Y := by
  rintro ⟨a, b, c⟩
  simp +contextual
  omega

@[gcongr]
lemma Finset.abcExceptionsBelow_mono_left {ε₁ ε₂ : ℝ} {X : ℕ} (hε : ε₁ ≤ ε₂) :
    abcExceptionsBelow ε₂ X ⊆ abcExceptionsBelow ε₁ X := by
  rintro ⟨a, b, c⟩
  simp +contextual only [mem_abcExceptionsBelow, Nat.Coprime, Set.mem_Icc, Prod.mk_le_mk, and_self,
    and_true, true_and, and_imp]
  rintro - - - - h - - hc - - -
  refine h.trans_le ?_
  gcongr
  simpa

@[gcongr]
lemma Finset.abcExceptionsBelow_mono {ε₁ ε₂ : ℝ} {X Y : ℕ}
    (hε : ε₁ ≤ ε₂) (hXY : X ≤ Y) :
    abcExceptionsBelow ε₂ X ⊆ abcExceptionsBelow ε₁ Y :=
  (abcExceptionsBelow_mono_right hXY).trans (abcExceptionsBelow_mono_left hε)

/--
The number of exceptions to the abc conjecture for a given `ε` which are bounded by `X`.
-/
noncomputable def countTriples (ε : ℝ) (X : ℕ) : ℕ := #(abcExceptionsBelow ε X)

/--
The set of exceptions to the abc conjecture for `ε`, in particular
the set of triples `(a, b, c)` which are
* pairwise coprime,
* positive,
* satisfy `a + b = c`,
* have `radical (a * b * c) ^ (1 + ε) < c`
-/
def abcExceptions (ε : ℝ) : Set (ℕ × ℕ × ℕ) :=
  { (a, b, c) : ℕ × ℕ × ℕ |
    0 < a ∧ 0 < b ∧ 0 < c ∧
    a.Coprime b ∧ a.Coprime c ∧ b.Coprime c ∧
    a + b = c ∧
    radical (a * b * c) ^ (1 + ε) < (c : ℝ) }

@[simp]
theorem mem_abcExceptions (ε : ℝ) (a b c : ℕ) :
    ⟨a, b, c⟩ ∈ abcExceptions ε ↔
      0 < a ∧ 0 < b ∧ 0 < c ∧
      a.Coprime b ∧ a.Coprime c ∧ b.Coprime c ∧
      a + b = c ∧
      radical (a * b * c) ^ (1 + ε) < (c : ℝ) := Iff.rfl

@[gcongr]
lemma abcExceptions_mono {ε₁ ε₂ : ℝ} (hε : ε₂ ≤ ε₁) :
    abcExceptions ε₁ ⊆ abcExceptions ε₂ := by
  rintro ⟨a, b, c⟩
  simp +contextual only [mem_abcExceptions, Prod.mk_le_mk, and_imp, true_and, Nat.Coprime]
  rintro ha hb hc - - - - habc
  refine habc.trans_le' ?_
  gcongr
  simp [Nat.one_le_cast, Nat.add_one_le_iff, Nat.radical_pos]

lemma abcExceptions_subset_Ici_one (ε : ℝ) : abcExceptions ε ⊆ Set.Ici 1 := by
  rintro ⟨a, b, c⟩
  simp only [mem_abcExceptions, Set.mem_Ici, and_imp, ← Prod.mk_one_one, Prod.mk_le_mk,
    Nat.add_one_le_iff]
  omega

/-- The abc conjecture: the set of exceptional triples is finite. -/
def abcConjecture : Prop := ∀ ε > 0, (abcExceptions ε).Finite

open Topology in
lemma abcConjecture_iff_eventually :
    abcConjecture ↔ ∀ᶠ ε in 𝓝[>] 0, (abcExceptions ε).Finite := by
  constructor
  · intro (h : ∀ _, _)
    simp +contextual [eventually_nhdsWithin_iff, h]
  · intro h ε hε
    suffices ∀ᶠ (δ : ℝ) in 𝓝[>] 0, (abcExceptions ε).Finite by simpa
    filter_upwards [h, eventually_nhdsWithin_of_eventually_nhds (eventually_lt_nhds hε)]
      with δ hδ hδε using hδ.subset (abcExceptions_mono hδε.le)

lemma abcExceptionsBelow_eq_abcExceptions_inter (ε : ℝ) (X : ℕ) (hε : ε < 1) :
    abcExceptionsBelow ε X =
      abcExceptions ((1 - ε)⁻¹ - 1) ∩ Set.Icc (1, 1, 1) (X, X, X) := by
  ext ⟨a, b, c⟩
  suffices radical (a * b * c) ^ (1 - ε)⁻¹ < (c : ℝ) ↔ radical (a * b * c) < (c : ℝ) ^ (1 - ε) by
    simp [Nat.add_one_le_iff]
    tauto
  rw [Real.rpow_inv_lt_iff_of_pos (by simp) (by simp) (by simpa)]

lemma abcExceptionsBelow_eq_abcExceptions_inter' (ε : ℝ) (X : ℕ) (hε : 0 < ε) :
    abcExceptionsBelow (1 - (1 + ε)⁻¹) X =
      abcExceptions ε ∩ Set.Icc (1, 1, 1) (X, X, X) := by
  rw [abcExceptionsBelow_eq_abcExceptions_inter _ _]
  · simp
  · simp [add_pos zero_lt_one hε]

open Asymptotics Filter

-- in a PR to mathlib
theorem ciSup_eq_monotonicSequenceLimit {α : Type*} [ConditionallyCompleteLattice α]
    [WellFoundedGT α] (a : ℕ →o α) (ha : BddAbove (Set.range a)) :
    iSup a = monotonicSequenceLimit a := by
  refine (ciSup_le fun m => ?_).antisymm (le_ciSup ha _)
  rcases le_or_lt m (monotonicSequenceLimitIndex a) with hm | hm
  · exact a.monotone hm
  · obtain h := WellFoundedGT.monotone_chain_condition a
    exact (Nat.sInf_mem (s := {n | ∀ m, n ≤ m → a n = a m}) h m hm.le).ge

lemma forall_increasing' {α : Type*} (f : ℕ → Set α) (hf : Monotone f)
    (hf' : ∀ n, (f n).Finite)
    {C : ℕ} (hC : ∀ n, (f n).ncard ≤ C) : (⋃ n, f n).Finite := by
  by_contra!
  obtain ⟨t, ht, ht', ht''⟩ := Set.Infinite.exists_subset_ncard_eq this (C + 1)
  lift t to Finset α using ht'
  obtain ⟨i, hi⟩ := hf.directed_le.exists_mem_subset_of_finset_subset_biUnion ht
  replace hC : (f i).ncard ≤ C := hC i
  have := Set.ncard_le_ncard hi (hf' _)
  omega

lemma forall_increasing {α : Type*} (f : ℕ → Set α) (hf : Monotone f)
    {s : Set α} (hf' : ∀ n, (s ∩ f n).Finite)
    {C : ℕ} (hC : ∀ n, (s ∩ f n).ncard ≤ C) : (s ∩ ⋃ n, f n).Finite := by
  rw [Set.inter_iUnion]
  refine forall_increasing' _ ?_ hf' hC
  intro a b hab
  exact Set.inter_subset_inter_right _ (hf hab)

lemma abcConjecture_iff :
    abcConjecture ↔ ∀ ε > 0, ε < 1 → (countTriples ε · : ℕ → ℝ) =O[atTop] (fun _ ↦ (1 : ℝ)) := by
  simp only [isBigO_one_nat_atTop_iff]
  constructor
  · intro h ε hε₀ hε₁
    have habc := h ((1 - ε)⁻¹ - 1) (by simp [sub_pos, one_lt_inv₀, *])
    use (abcExceptions ((1 - ε)⁻¹ - 1)).ncard
    intro n
    rw [Real.norm_natCast, Nat.cast_le, countTriples,
      ← Set.ncard_coe_Finset, abcExceptionsBelow_eq_abcExceptions_inter _ _ hε₁]
    exact Set.ncard_le_ncard Set.inter_subset_left habc
  · intro h ε hε
    obtain ⟨C, hC⟩ := h (1 - (1 + ε)⁻¹)
      (by simp [inv_lt_one_of_one_lt₀, hε]) (by simp [add_pos, hε])
    have hC₀ : 0 ≤ C := (hC 0).trans' (by simp)
    simp_rw [Real.norm_natCast, countTriples, ← Nat.le_floor_iff hC₀,
      ← Set.ncard_coe_Finset, abcExceptionsBelow_eq_abcExceptions_inter' ε _ hε] at hC
    have : ⋃ n, Set.Icc (1, 1, 1) (n, n, n) = Set.Ici 1 := by
      ext ⟨i, j, k⟩
      simp only [Set.mem_iUnion, Set.mem_Icc, Prod.mk_le_mk, exists_and_left, ← Prod.mk_one_one,
        Set.mem_Ici, and_iff_left_iff_imp, and_imp]
      rintro - - -
      exact ⟨max i (max j k), by simp⟩
    rw [← Set.inter_eq_left.2 (abcExceptions_subset_Ici_one ε), ← this]
    refine forall_increasing _ ?_ ?_ hC
    · intro n m hnm
      dsimp
      gcongr
    · intro n
      exact (Set.finite_Icc (1, 1, 1) (n, n, n)).inter_of_right _

/-- We define reals `x` and `X` to be similar if `x ∈ [X, 2X]`. -/
def similar (x X : ℝ) : Prop := x ∈ Set.Icc X (2 * X)

local infixr:36 " ~ " => similar

theorem similar_pow_natLog (x : ℕ) (hx : x ≠ 0) : x ~ 2 ^ Nat.log 2 x := by
  simp only [similar, Set.mem_Icc]
  norm_cast
  constructor
  · refine Nat.pow_log_le_self 2 hx
  · rw [← Nat.pow_succ']
    exact (Nat.lt_pow_succ_log_self (by omega) _).le

open Classical in
/-- The finite set of exceptions `(a, b, c)` to the abc conjecture for which `X/2 ≤ c ≤ X` and
  `rad a ~ X^α`, `rad b ~ X^β`, `rad c ~ X^γ`. `S*` counts the size of this set. -/
noncomputable def dyadicPoints (α β γ : ℝ) (X : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  (Finset.Icc (1, 1, 1) (2*X, 2*X, 2*X)).filter fun ⟨a, b, c⟩ ↦
    a.Coprime b ∧ a.Coprime c ∧ b.Coprime c ∧
    a + b = c ∧
    (radical a : ℕ) ~ (X ^ α : ℝ) ∧
    (radical b : ℕ) ~ (X ^ β : ℝ) ∧
    (radical c : ℕ) ~ (X ^ γ : ℝ) ∧
    X ≤ 2 * c ∧ c ≤ X

@[simp]
theorem mem_dyadicPoints (α β γ : ℝ) (X : ℕ) (a b c : ℕ) :
    ⟨a, b, c⟩ ∈ dyadicPoints α β γ X ↔
      0 < a ∧ 0 < b ∧ 0 < c ∧
      a.Coprime b ∧ a.Coprime c ∧ b.Coprime c ∧
      a + b = c ∧
      (radical a : ℕ) ~ (X ^ α : ℝ) ∧
      (radical b : ℕ) ~ (X ^ β : ℝ) ∧
      (radical c : ℕ) ~ (X ^ γ : ℝ) ∧
      X ≤ 2 * c ∧ c ≤ X := by
  simp only [dyadicPoints, Finset.mem_filter, Finset.mem_Icc, Prod.mk_le_mk, Nat.add_one_le_iff,
    and_assoc, and_congr_right_iff, similar, Set.mem_Icc, Nat.cast_le, ← and_assoc,
    and_congr_left_iff]
  intro ha hb hc hc_le_X hX_le_c hrc hrb hra habc hbc hac
  omega

/--
This is $$S^*_{α,β,γ}(X)$$ in the paper and blueprint.
-/
noncomputable def refinedCountTriplesStar (α β γ : ℝ) (X : ℕ) : ℕ := #(dyadicPoints α β γ X)

/-- The set over which we take the supremum in lemma 2.2. -/
private noncomputable def indexSet (ε : ℝ) (X : ℕ) : Finset (ℕ × ℕ × ℕ × ℕ) :=
  (Finset.Icc 0 (Nat.log 2 X)) ×ˢ (Finset.Icc 0 (Nat.log 2 X)) ×ˢ
  (Finset.Icc 0 (Nat.log 2 X)) ×ˢ (Finset.Icc 1 (Nat.log 2 X+1)) |>.filter fun ⟨i, j, k, n⟩ ↦
    i + j + k ≤ (1 - ε) * n

private theorem card_indexSet_le (ε : ℝ) (X : ℕ) :
    (indexSet ε X).card ≤ (Nat.log 2 X + 1) ^ 4 := by
  apply (Finset.card_filter_le ..).trans
  simp only [card_product, Nat.card_Icc, tsub_zero, add_tsub_cancel_right]
  linear_combination

@[simp]
private theorem mem_indexSet (ε : ℝ) (X : ℕ) (i j k n : ℕ) :
    ⟨i, j, k, n⟩ ∈ indexSet ε X ↔
      i ≤ Nat.log 2 X ∧ j ≤ Nat.log 2 X ∧ k ≤ Nat.log 2 X ∧
      1 ≤ n ∧ n ≤ Nat.log 2 X + 1 ∧ i + j + k ≤ (1 - ε) * n := by
  simp [indexSet]
  norm_cast
  aesop

theorem Nat.Coprime.isRelPrime (a b : ℕ) (h : a.Coprime b) : IsRelPrime a b := by
  rw [← Nat.coprime_iff_isRelPrime]
  exact h

theorem Finset.abcExceptionsBelow_subset_union_dyadicPoints (ε : ℝ) (X : ℕ) :
    Finset.abcExceptionsBelow ε X ⊆
      (indexSet ε X).biUnion fun ⟨i, j, k, n⟩ ↦
        dyadicPoints (i / n : ℝ) (j / n : ℝ) (k / n : ℝ) (2 ^ n) := by
  rintro ⟨a, b, c⟩
  simp only [mem_abcExceptionsBelow, Set.mem_Icc, Prod.mk_le_mk, Finset.mem_biUnion,
    mem_dyadicPoints, Nat.cast_pow, Nat.cast_ofNat, Prod.exists, mem_indexSet, and_imp]
  intro hab hac hbc habc hrad h1a h1b h1c haX hbX hcX
  have hε : 0 ≤ 1 - ε := by
    by_contra!
    have h₁ : (1 : ℝ) ≤ radical (a * b * c) := mod_cast (Nat.radical_pos _)
    have h₂ : (c : ℝ) ^ (1 - ε) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg (by norm_cast; omega) (by assumption)
    exact (hrad.trans h₂).not_le h₁
  have {a : ℕ} (ha : 1 ≤ a) (haX : a ≤ X) : Nat.log 2 (radical a) ≤ Nat.log 2 X := by
    apply Nat.log_mono_right ((Nat.radical_le_self_iff.2 (by omega)).trans haX)
  let n := Nat.log 2 c + 1
  have hcn : c ≤ 2 ^ n := (Nat.lt_pow_succ_log_self one_lt_two c).le
  refine ⟨Nat.log 2 (radical a), Nat.log 2 (radical b), Nat.log 2 (radical c), n,
    ⟨this h1a haX, this h1b hbX, this h1c hcX, by omega, ?_, ?_⟩, by omega, by omega, by omega,
    hab, hac, hbc, habc, ?_⟩
  · simp [n, Nat.log_mono_right hcX]
  · -- Here we prove that α + β + γ ≤ 1 - ε
    have : radical (a * b * c) = radical a * radical b * radical c := by
      rw [radical_mul (a := a*b) (b := c), radical_mul]
      · convert hab.isRelPrime
      exact hac.mul hbc |>.isRelPrime
    rw [this] at hrad
    clear this
    have := calc
      (2:ℝ) ^ (Nat.log 2 (radical a) + Nat.log 2 (radical b) + Nat.log 2 (radical c)) ≤
        (radical a : ℕ) * (radical b : ℕ) * (radical c : ℕ) := by
        norm_cast
        simp_rw [Nat.pow_add]
        gcongr <;>
        · apply Nat.pow_log_le_self
          exact radical_ne_zero
      _ ≤ ↑c ^ (1 - ε) := by
        exact_mod_cast hrad.le
      _ ≤ (2:ℝ) ^ (n * (1 - ε)) := by
        norm_cast
        rw [Real.rpow_natCast_mul (by norm_num)]
        gcongr
        norm_cast
    rw [← Real.rpow_le_rpow_left_iff (show 1 < (2 : ℝ) by norm_num)]
    norm_cast at this ⊢
    convert this using 1
    ring_nf
  have {a : ℕ} : (2 ^ n : ℝ) ^ (Nat.log 2 (radical a) / n : ℝ) =
      2 ^ Nat.log 2 (radical a) := by
    rw [← Real.rpow_natCast_mul (by norm_num)]
    have : n * (Nat.log 2 (radical a) / n : ℝ) = Nat.log 2 (radical a) := by
      rw [mul_div_cancel₀]
      simp [n]
      norm_cast
    rw [this]
    simp
  have hc2 : 2 ≤ c := by omega
  simp_rw [this]
  have radical_similar {a : ℕ} : (radical a : ℕ) ~ 2 ^ (Nat.log 2 (radical a)) :=
    similar_pow_natLog (radical a) radical_ne_zero
  refine ⟨radical_similar, radical_similar, radical_similar, ?_, hcn⟩
  simp only [Nat.pow_succ', Nat.ofNat_pos, mul_le_mul_left, n]
  apply Nat.pow_log_le_self
  omega

theorem sum_le_card_mul_sup {ι : Type*} (f : ι → ℕ) (s : Finset ι) :
    ∑ i ∈ s, f i ≤ s.card * s.sup f := calc
  ∑ i ∈ s, f i ≤ ∑ i ∈ s, s.sup f := by
    apply Finset.sum_le_sum
    intro i hi
    exact Finset.le_sup hi
  _ = s.card * s.sup f := by
    simp

theorem card_union_dyadicPoints_le_log_pow_mul_sup (ε : ℝ) (X : ℕ) :
    ((indexSet ε X).biUnion fun ⟨i, j, k, n⟩ ↦
      dyadicPoints (i / n : ℝ) (j / n : ℝ) (k / n : ℝ) (2^n)).card ≤
  (Nat.log 2 X+1)^4 * (indexSet ε X).sup fun ⟨i, j, k, n⟩ ↦
    refinedCountTriplesStar (i / n : ℝ) (j / n : ℝ) (k / n : ℝ) (2^n) := by
  apply (Finset.card_biUnion_le ..).trans
  simp only
  apply (sum_le_card_mul_sup _ _).trans
  gcongr
  · apply card_indexSet_le
  · rfl

/-- The supremum that appears in lemma 2.2, taken over a finite subset of α, β, γ > 0 such that
  α + β + γ ≤ 1 - ε -/
noncomputable def dyadicSupBound (ε : ℝ) (X : ℕ) : ℕ :=
  (indexSet ε X).sup fun ⟨i, j, k, n⟩ ↦
    refinedCountTriplesStar (i / n : ℝ) (j / n : ℝ) (k / n : ℝ) (2^n)

theorem countTriples_le_log_pow_mul_sup (ε : ℝ) (X : ℕ) :
    countTriples ε X ≤ (Nat.log 2 X + 1) ^ 4 * dyadicSupBound ε X := by
  simp_rw [countTriples, dyadicSupBound, refinedCountTriplesStar]
  apply le_trans _ (card_union_dyadicPoints_le_log_pow_mul_sup ε X)
  apply Finset.card_le_card
  exact Finset.abcExceptionsBelow_subset_union_dyadicPoints ε X

theorem Real.natLog_isBigO_logb (b : ℕ) :
    (fun x : ℕ ↦ (Nat.log b x : ℝ)) =O[atTop] (fun x : ℕ ↦ Real.logb b x) := by
  apply IsBigO.of_bound'
  filter_upwards with x
  rw [Real.norm_natCast, Real.norm_eq_abs]
  exact (Real.natLog_le_logb _ _).trans (le_abs_self _)

theorem Real.logb_isBigO_log (b : ℝ) :
    logb b =O[atTop] log :=
  .of_bound |Real.log b|⁻¹ <| by filter_upwards using by simp [Real.logb, div_eq_inv_mul]

theorem Real.log_isBigO_logb (b : ℝ) (hb : 1 < b) :
    log =O[atTop] logb b :=
  .of_bound |Real.log b| <| by
    filter_upwards using by simp [Real.logb, mul_div_cancel₀, abs_ne_zero, (log_pos hb).ne']

theorem Nat.log_isBigO_log (b : ℕ) :
    (fun x : ℕ ↦ (Nat.log b x : ℝ)) =O[atTop] (fun x : ℕ ↦ Real.log x) :=
  (Real.natLog_isBigO_logb _).trans
    ((Real.logb_isBigO_log _).comp_tendsto tendsto_natCast_atTop_atTop)

theorem countTriples_isBigO_dyadicSup (ε : ℝ) :
    (fun X ↦ (countTriples ε X : ℝ)) =O[atTop] (fun X ↦ (Real.log X) ^ 4 * dyadicSupBound ε X) := by
  trans fun X ↦ (Nat.log 2 X+1:ℝ)^4 * dyadicSupBound ε X
  · apply IsBigO.of_norm_le
    simp only [Real.norm_natCast, Prod.forall]
    exact_mod_cast fun b ↦ countTriples_le_log_pow_mul_sup _ _
  · apply IsBigO.mul _ (isBigO_refl ..)
    apply IsBigO.pow
    apply IsBigO.add
    · exact Nat.log_isBigO_log 2
    apply IsLittleO.isBigO
    apply Real.isLittleO_const_log_atTop.natCast_atTop

/-- The finite set of `d`-tuples `a i` such that `a i ~ X i` for all `i`. -/
def dyadicTuples {d : ℕ} (X : Fin d → ℕ) : Finset (Fin d → ℕ) :=
  Fintype.piFinset (fun i ↦ Finset.Icc (X i) (2 * X i))

@[simp]
theorem mem_dyadicTuples {d : ℕ} (X x : Fin d → ℕ) :
    x ∈ dyadicTuples X ↔ ∀ i, x i ~ X i := by
  simp [dyadicTuples, similar]
  norm_cast

open Classical in
/-- The finite set counted by `B_d(C, X, Y, X)`. We choose to add `C` as an entry in these tuples,
  as this allows us to write down a surjective map from a union of these sets back to triples
  `(a, b, c)` in `dyadicTriples α β γ`. -/
noncomputable def B_finset (d : ℕ) (C : Fin 3 → ℕ) (X Y Z : Fin d → ℕ) :
    Finset ((Fin d → ℕ) × (Fin d → ℕ) × (Fin d → ℕ) × (Fin 3 → ℕ)) :=
  ((dyadicTuples X) ×ˢ (dyadicTuples Y) ×ˢ (dyadicTuples Z) ×ˢ {C}).filter fun ⟨x, y, z, c⟩ ↦
    c 0 * ∏ i, x i ^ (i.val + 1) + c 1 * ∏ i, y i ^ (i.val + 1) = c 2 * ∏ i, z i ^ (i.val + 1) ∧
    Nat.gcd (c 0 * ∏ i, x i) (c 1 * ∏ i, y i) = 1 ∧ -- TODO: write these as Coprime?
    Nat.gcd (c 0 * ∏ i, x i) (c 2 * ∏ i, z i) = 1 ∧
    Nat.gcd (c 1 * ∏ i, y i) (c 2 * ∏ i, z i) = 1

theorem mem_B_finset (d : ℕ) (C : Fin 3 → ℕ) (X Y Z : Fin d → ℕ)
    (x y z : Fin d → ℕ) (c : Fin 3 → ℕ) :
    (x, y, z, c) ∈ B_finset d C X Y Z ↔
      C = c ∧
      (∀ i, x i ~ X i) ∧ (∀ i, y i ~ Y i) ∧ (∀ i, z i ~ Z i) ∧
      c 0 * ∏ i, (x i)^(i.val + 1) + c 1 * ∏ i, (y i)^(i.val + 1) = c 2 * ∏ i, (z i)^(i.val + 1) ∧
      Nat.gcd (c 0 * ∏ i, (x i)) (c 1 * ∏ i, (y i)) = 1 ∧
      Nat.gcd (c 0 * ∏ i, (x i)) (c 2 * ∏ i, (z i)) = 1 ∧
      Nat.gcd (c 1 * ∏ i, (y i)) (c 2 * ∏ i, (z i)) = 1 := by
  simp only [B_finset, Fin.isValue, Finset.mem_singleton, Finset.mem_filter, Finset.mem_product,
    mem_dyadicTuples, Function.Embedding.coeFn_mk, Prod.mk.injEq]
  tauto

/-- Definition 2.4 -/
noncomputable def B (d : ℕ) (c : Fin 3 → ℕ) (X Y Z : Fin d → ℕ) : ℕ := (B_finset d c X Y Z).card

theorem Nat.factorization_le_right (p n : ℕ) (hp : p.Prime) : n.factorization p ≤ n := by
  refine factorization_le_of_le_pow ?_
  induction n with
  | zero => simp
  | succ n ih =>
    have : 1 ≤ p ^ n := by
      apply Nat.one_le_pow
      apply hp.pos
    have : 2 ≤ p := hp.two_le
    rw [pow_succ]
    calc _ ≤ p^n + p^n := by gcongr
      _ = p^n * 2 := by ring
      _ ≤ p^n * p := by gcongr

theorem Nat.ceil_lt_floor (a b : ℝ) (ha : 0 ≤ a) (hab : a + 2 ≤ b) : ⌈a⌉₊ < ⌊b⌋₊ := by
  exact_mod_cast calc
    ⌈a⌉₊ < a + 1 := by
      exact ceil_lt_add_one ha
    _ ≤ b - 1 := by
      linarith
    _ < ⌊b⌋₊ := by
      exact sub_one_lt_floor b

namespace NiceFactorization

/-- The data and assumptions of lemma 2.5. We treat `d` as a free variable constrained by `hd` here
  because `d` appears in a type and this gives the user some leeway to rewrite the value of `d`. -/
class ProofData where
  /-- The value of epsilon in Lemma 2.5-/
  ε : ℝ
  hε_pos : 0 < ε
  hε : ε < 1/2
  /-- `d` in Lemma 2.5 -/
  d : ℕ
  hd : d = ⌊5/2 * ε⁻¹^2⌋₊
  /-- `n` in Lemma 2.5 -/
  n : ℕ
  /-- `X` in Lemma 2.5 -/
  X : ℕ
  h1n : 1 ≤ n
  hnX : n ≤ X

open ProofData NiceFactorization
variable [data : ProofData]

/-- `y j` is the product of primes dividing `n` with multiplicity `j`. -/
def y (j : ℕ) : ℕ := ∏ p ∈ n.primeFactors with n.factorization p = j, p

@[simp]
private theorem y_zero : y 0 = 1 := by
  simp +contextual [y, Nat.factorization_eq_zero_iff]

private theorem hy_pos (j : ℕ) : 0 < y j := by
  apply Finset.prod_pos
  simp only [Finset.mem_filter, Nat.mem_primeFactors, ne_eq, and_imp, y]
  intro p hp _ _ _
  exact hp.pos

private theorem prod_y_pow_eq_n_subset {s : Finset ℕ}
    (hs : ∀ p, p.Prime → p ∣ n → n.factorization p ∈ s) :
    ∏ m ∈ s, y m ^ m = n := by
  have := h1n
  simp_rw [y]
  conv =>
    rhs
    rw [← Nat.factorization_prod_pow_eq_self (show n ≠ 0 by omega)]
  simp_rw [← Finset.prod_pow]
  rw [Nat.prod_factorization_eq_prod_primeFactors]
  convert Finset.prod_fiberwise_of_maps_to  (f := fun p ↦ p ^ n.factorization p)
    (g := n.factorization) (s := n.primeFactors) (t := s) ?_ using 1
  · apply Finset.prod_congr rfl
    intro k hk
    apply Finset.prod_congr rfl
    simp only [Finset.mem_filter, Nat.mem_primeFactors, ne_eq, and_imp, y]
    rintro _ _ _ _ rfl
    rfl
  · simp only [Nat.mem_primeFactors, ne_eq, Finset.mem_Icc, and_imp, y]
    intro p hp hpn hn'
    apply hs p hp hpn

private theorem prod_y_pow_eq_n : ∏ m ∈ Finset.Icc 1 d ∪ Finset.Ioc d n, y m ^ m = n := by
  apply prod_y_pow_eq_n_subset
  intro p hp hpn
  simp only [Finset.mem_union, Finset.mem_range, Finset.mem_Icc]
  have : n.factorization p ≤ n := Nat.factorization_le_right p n hp
  have : n.factorization p ≤ d ∨ d < n.factorization p := le_or_lt (n.factorization p) d
  simp only [Finset.mem_Ioc]
  have : 1 ≤ n.factorization p := by
    rw [← hp.dvd_iff_one_le_factorization]
    · exact hpn
    · have := h1n
      omega
  tauto

private theorem p_dvd_y_iff (i : ℕ) (p : ℕ) (hp : p.Prime) : p ∣ y i → n.factorization p = i := by
  rw [y, Prime.dvd_finset_prod_iff hp.prime]
  simp only [Finset.mem_filter, Nat.mem_primeFactors, ne_eq]
  rintro ⟨q, ⟨⟨hq, _⟩, rfl⟩, hpq⟩
  congr
  rw [eq_comm, ← hq.dvd_iff_eq hp.ne_one]
  exact hpq

private theorem hy_cop (i j : ℕ) (hij : i ≠ j) : Nat.Coprime (y i) (y j) := by
  apply Nat.coprime_of_dvd
  intro p hp hpi hpj
  apply p_dvd_y_iff _ _ hp at hpi
  apply p_dvd_y_iff _ _ hp at hpj
  subst hpi hpj
  exact hij rfl

open Function in
omit data in
theorem _root_.Nat.prod_squarefree {ι : Type*} (f : ι → ℕ) {s : Finset ι}
    (hf : ∀ i ∈ s, Squarefree (f i))
    (h : Set.Pairwise s.toSet (Nat.Coprime on f)) :
    Squarefree (∏ i ∈ s, f i) := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons i s his ih =>
    simp only [Finset.prod_cons]
    simp only [mem_cons, forall_eq_or_imp] at hf
    rw [coe_cons, Set.pairwise_insert_of_symmetric_of_notMem _ (by simpa using his)] at h
    swap
    · exact Nat.Coprime.symmetric.comap _
    rw [Nat.squarefree_mul]
    · exact ⟨hf.1, ih hf.2 h.1⟩
    apply Nat.Coprime.prod_right
    intro j hj
    exact h.2 j hj

omit data in
theorem _root_.Associated.nat_eq {a b : ℕ} (h : Associated a b) : a = b := by
  rwa [associated_iff_eq] at h

theorem y_squarefree {i : ℕ} : Squarefree (y i) := by
  rw [y]
  apply Nat.prod_squarefree
  · simp +contextual [Finset.mem_filter, Nat.mem_primeFactors, Nat.Prime.prime, Prime.squarefree]
  · simp +contextual [Nat.coprime_primes, Function.onFun, Set.Pairwise]

private theorem prod_y_eq_radical_n : ∏ m ∈ Finset.Icc 1 d ∪ Finset.Ioc d n, y m = radical n := by
  conv => rhs; rw [← prod_y_pow_eq_n]
  rw [radical_prod]
  · apply Finset.prod_congr rfl
    simp only [Finset.mem_union, Finset.mem_range, Finset.mem_Icc]
    intro i _
    by_cases hi : i = 0
    · simp [hi]
    · rw [radical_pow _ (by omega)]
      have := radical_associated (y_squarefree (i := i)).isRadical (hy_pos _).ne'
      exact associated_iff_eq.1 this.symm
  · intro i _ j _ hij
    apply Nat.Coprime.isRelPrime
    apply Nat.Coprime.pow_right
    apply Nat.Coprime.pow_left
    apply hy_cop i j hij

/-- `K` in the proof of lemma 2.5 -/
noncomputable def K := ⌈ε⁻¹⌉₊

private theorem two_lt_eps_inv : 2 < ε⁻¹ := by
  have := hε_pos
  rw [← inv_inv 2]
  gcongr
  linarith only [hε]

private theorem hK_pos : 0 < K := by
  rw [K, Nat.ceil_pos]
  simp [hε_pos]

private theorem two_lt_K : 2 < K := by
  rw [K, Nat.lt_ceil]
  simp [two_lt_eps_inv]

private theorem K_inv_le_eps : (K : ℝ)⁻¹ ≤ ε := by
  rw [inv_le_iff_one_le_mul₀]
  · calc
    1 = ε * ε⁻¹ := by
      field_simp [hε_pos.ne.symm]
    _ ≤ ε * K := by
      have := hε_pos
      gcongr
      rw [K]
      apply Nat.le_ceil
  · simp [hK_pos]

private theorem hd_pos : 0 < d := by
  rw [hd, Nat.floor_pos]
  nlinarith only [two_lt_eps_inv]

private instance hd_ne_zero : NeZero d := by
  simp_rw [neZero_iff]
  apply ne_of_gt hd_pos

private theorem hKd : K < d := by
  have := two_lt_eps_inv
  simp_rw [K, hd]
  rw [Nat.lt_iff_add_one_le]
  apply Nat.ceil_lt_floor
  · positivity
  nlinarith

private theorem hK_div_d : (K / d : ℝ) ≤ ε := by
  have := hε
  have := hε_pos
  have := two_lt_eps_inv
  rw [div_le_iff₀ (mod_cast hd_pos)]
  simp only [K, d]
  calc
    _ ≤ ε⁻¹ + 1 := by
      apply le_of_lt
      apply Nat.ceil_lt_add_one
      positivity
    _ ≤ 5 / 2 * ε⁻¹ - ε := by
      linarith
    _ = ε * (5/2 * ε⁻¹^2 - 1) := by
      field_simp [hε_pos.ne.symm]
      ring
    _ ≤ _ := by
      rw [hd]
      gcongr
      apply le_of_lt
      apply Nat.sub_one_lt_floor

/-- `x` in the proof of lemma 2.5 -/
noncomputable def x (j : Fin d) : ℕ :=
  y (j.val+1) * if j.val + 1 = K then (∏ m ∈ Finset.Ioc d n, y m ^ (m / K)) else 1

theorem x_pos (j : Fin d) : 0 < x j := by
  rw [x]
  split_ifs with h
  · apply mul_pos
    · apply hy_pos
    · apply Finset.prod_pos
      intros
      apply pow_pos (hy_pos _)
  · simp [hy_pos]

private theorem x_pairwise_coprime (i j : Fin d) (hij : i ≠ j) : Nat.gcd (x i) (x j) = 1 := by
  have hij' : i.val ≠ j.val := by
    simp [Fin.val_inj, hij]
  have hij'' : i.val + 1 ≠ j.val + 1 := by
    simp [Fin.val_inj, hij]
  simp_rw [x]
  rw [← Nat.coprime_iff_gcd_eq_one]
  split_ifs with hik hjk
  · rw [← hik] at hjk
    exact (hij''.symm hjk).elim
  · rw [Nat.coprime_mul_iff_left, mul_one]
    refine ⟨hy_cop _ _ hij'', ?_⟩
    rw [Nat.coprime_prod_left_iff]
    simp only [Finset.mem_Ioc, and_imp]
    intro m hMm hmn
    apply Nat.Coprime.pow_left
    apply hy_cop
    omega
  · /- deduce from above instead? -/
    rw [Nat.coprime_mul_iff_right, mul_one]
    refine ⟨hy_cop _ _ hij'', ?_⟩
    rw [Nat.coprime_prod_right_iff]
    simp only [Finset.mem_Ioc, and_imp]
    intro m hMm hmn
    apply Nat.Coprime.pow_right
    apply hy_cop
    omega
  · simp_rw [mul_one]
    apply hy_cop _ _ hij''


/-- `c` in the proof of lemma 2.5-/
noncomputable def c : ℕ := ∏ m ∈ Finset.Ioc d n, y m ^ (m % K)

private theorem c_pos : 0 < c := by
  rw [c]
  apply Finset.prod_pos
  simp only [Finset.mem_Ioc, and_imp]
  intro i _ _
  apply pow_pos
  exact hy_pos _

omit data in
theorem nat_eq_fin_iff {n a : ℕ} {b : Fin n} [NeZero n] (ha : a < n) :
    (a : Fin n) = b ↔ a = b.val := by
  rw [← Fin.val_inj]
  simp only [Fin.val_natCast, Nat.mod_eq_of_lt ha]

omit data in
theorem fin_eq_nat_iff {n a : ℕ} {b : Fin n} [NeZero n] (ha : a < n) :
    b = (a : Fin n) ↔ b.val = a := by
  rw [← Fin.val_inj]
  simp only [Fin.val_natCast, Nat.mod_eq_of_lt ha]

private theorem aux (f : ℕ → ℕ) :
    (∏ i : Fin d, if i.val + 1 = K then f (i.val + 1) else 1) = f K := by
  obtain ⟨K', hK'⟩ := Nat.exists_eq_add_one.mpr hK_pos
  simp +contextual [hK', ← Finset.prod_filter]
  have : Finset.univ.filter (fun a : Fin d ↦ a.val = K') = ({(↑K' : Fin d)} : Finset (Fin d)) := by
    ext x; simp only [mem_filter, mem_univ, true_and, mem_singleton]
    rw [eq_comm]
    conv => rhs; rw [eq_comm]
    apply (nat_eq_fin_iff _).symm
    have := hKd
    omega
  simp [this]

private theorem c_mul_prod_x_eq_n : c * ∏ j, x j ^ (j.val + 1) = n := by
  simp_rw [c, x]
  simp_rw [mul_pow, Finset.prod_mul_distrib]
  simp only [ite_pow, one_pow]
  simp +contextual only
  rw [Fin.prod_univ_eq_prod_range (fun i ↦ y (i+1) ^ (i+1))]
  rw [mul_comm, mul_assoc, ← Finset.prod_pow, aux (fun _ ↦ _), ← Finset.prod_mul_distrib]
  simp_rw [← pow_mul, ← pow_add, mul_comm _ (K), Nat.div_add_mod]
  conv => rhs; rw [← prod_y_pow_eq_n]
  rw [Finset.prod_union]
  · have : (Finset.range d).map (addRightEmbedding 1) = Finset.Icc 1 d := by
      rw [range_eq_Ico, Finset.map_add_right_Ico, zero_add, Ico_add_one_right_eq_Icc]
    rw [← this]
    simp
  refine Finset.disjoint_left.mpr ?_
  simp +contextual

private theorem prod_y_large_le_X_pow : ∏ m ∈ Finset.Ioc d n, y m ≤ (X:ℝ) ^ (d⁻¹ : ℝ) := by
  have := hnX
  calc
    _ ≤ (∏ m ∈ Finset.Ioc d n, y m ^ m : ℝ) ^ (d⁻¹ : ℝ) := by
      rw [← Real.finset_prod_rpow]
      · push_cast
        apply Finset.prod_le_prod
        · intros; positivity
        simp only [Finset.mem_Ioc, and_imp]
        intro i hMi hin
        conv => lhs; rw [← Real.rpow_one (y i : ℝ)]
        rw [← Real.rpow_natCast_mul (by simp)]
        gcongr
        · norm_cast
          apply hy_pos
        · rw [le_mul_inv_iff₀]
          · simp [hMi.le]
          · simp [hd_pos]
      intros; positivity
    _ ≤ (n:ℝ) ^ (d⁻¹ : ℝ) := by
      gcongr
      norm_cast
      conv => rhs; rw [← prod_y_pow_eq_n]
      apply Finset.prod_le_prod_of_subset_of_one_le'
      · simp
      simp only [Finset.mem_union, Finset.mem_range, Finset.mem_Icc, not_and, not_le, y]
      intro i hi _
      erw [Nat.succ_le]
      simp only [Nat.zero_eq, d, K, x, c]
      by_cases hi0 : i = 0
      · simp [hi0]
      apply pow_pos (hy_pos ..)
    _ ≤ _ := by
      gcongr

private theorem c_le_X_pow : c ≤ (X:ℝ) ^ ε := calc
  c ≤ ∏ m ∈ Finset.Ioc d n, (y m : ℝ) ^ K := by
    simp_rw [c]
    push_cast
    apply Finset.prod_le_prod
    · intros; positivity
    simp only [Finset.mem_Ioc, and_imp]
    intro x hMx hxn
    gcongr
    · simp only [Nat.one_le_cast, *]
      apply hy_pos
    · apply (Nat.mod_lt ..).le
      exact hK_pos
  _ ≤ (X ^ (d⁻¹ : ℝ)) ^ (K:ℝ) := by
    simp only [Real.rpow_natCast]
    rw [Finset.prod_pow]
    gcongr
    exact_mod_cast prod_y_large_le_X_pow
  _ = (X:ℝ) ^ (K/d : ℝ) := by
    rw [← Real.rpow_mul]
    · ring_nf
    positivity
  _ ≤ X ^ ε := by
    have := h1n
    have := hnX
    have := hK_div_d
    gcongr
    · norm_cast
      linarith

@[simp]
private theorem tmp'' : ((K-1: Fin d).val + 1) = K := by
  have : (K:Fin d) - 1 = ((K-1: ℕ) : Fin d) := by
    rw [Nat.cast_sub]
    · simp
    have := two_lt_K
    omega
  rw [this]
  simp only [Fin.val_natCast]
  rw [Nat.mod_eq_of_lt]
  · simp [Nat.add_one_le_iff.eq ▸ hK_pos]
  · have := hKd
    omega

private theorem radical_le_X_pow_mul_prod : (radical n : ℕ) ≤ (X : ℝ)^ε * ∏ j, x j := calc
    (radical n : ℕ) ≤ ((radical c : ℕ) : ℝ) * radical (∏ j, x j ^ (j.val + 1)) := by
      norm_cast
      apply Nat.le_of_dvd
      · positivity
      rw [← c_mul_prod_x_eq_n]
      apply radical_mul_dvd
    _ ≤ ((radical c : ℕ) : ℝ)* ∏ j, (radical (x j ^ (j.val + 1)) : ℕ) := by
      gcongr
      apply Nat.le_of_dvd
      · positivity
      apply radical_prod_dvd
    _ = ((radical c : ℕ) : ℝ)* ∏ j, (radical (x j) : ℕ) := by
      congr 3 with j
      by_cases hj : (j : ℕ) = 0
      · simp [hj]
      rw [radical_pow]
      omega
    _ ≤ (X : ℝ)^ε * ∏ j, x j := by
      gcongr
      · calc
          _ ≤ ↑c := by
            norm_cast
            apply Nat.le_of_dvd c_pos
            apply radical_dvd_self
          _ ≤ (_:ℝ) := by
            apply c_le_X_pow
      apply Nat.le_of_dvd
      · apply x_pos
      apply radical_dvd_self

theorem x_K_le_X_pow : x (K-1) ≤ (X : ℝ) ^ ε := by
  have h1n := h1n
  have hnX := hnX
  rw [x, if_pos ?side]
  case side =>
    simp
  have := hKd
  simp only [tmp'', Nat.cast_mul, Nat.cast_prod, Nat.cast_pow, ge_iff_le]
  exact_mod_cast calc
    (y K * ∏ m ∈ Finset.Ioc d n, y m ^ (m / K) : ℝ) ≤
      (y K ^ K)^(K⁻¹:ℝ) * (∏ m ∈ Finset.Ioc d n, y m ^ m) ^ (K⁻¹:ℝ)  := by
        gcongr
        · rw [← Real.rpow_natCast_mul, mul_inv_cancel₀]
          · simp
          · simp only [ne_eq, Nat.cast_eq_zero]
            apply hK_pos.ne.symm
          · exact_mod_cast (hy_pos _).le
        · push_cast
          rw [← Real.finset_prod_rpow _ _ (by simp)]
          gcongr with i hi
          rw [← Real.rpow_natCast_mul, ← Real.rpow_natCast]
          · gcongr
            · simp only [Nat.one_le_cast]
              apply Nat.add_one_le_of_lt
              apply hy_pos
            · rw [← Nat.floor_div_eq_div (K := ℝ), div_eq_mul_inv]
              apply Nat.floor_le
              positivity
          · simp
    _ = (∏ m ∈ {K} ∪ Finset.Ioc d n, y m ^ m) ^ (K⁻¹:ℝ)  := by
        rw [Finset.prod_union]
        · simp only [Nat.cast_prod, Nat.cast_pow, Finset.prod_singleton, Nat.cast_mul]
          rw [Real.mul_rpow]
          · simp
          · positivity
        · simp only [disjoint_singleton_left, mem_Ioc, not_and, not_le]
          intro
          linarith
    _ ≤ (∏ m ∈ Finset.Icc 1 d ∪ Finset.Ioc d n, y m ^ m) ^ (K⁻¹:ℝ)  := by
      gcongr
      · intros
        apply Nat.add_one_le_of_lt
        simp [hy_pos]
      · intro i
        simp +contextual [hKd.le, Nat.add_one_le_iff.eq ▸ hK_pos]
    _ = (n : ℝ) ^ (K⁻¹ : ℝ) := by
      congr
      rw [prod_y_pow_eq_n]
    _ ≤ (X : ℝ) ^ (K⁻¹ : ℝ) := by
      gcongr
    _ ≤ (X:ℝ)^ε := by
      gcongr
      · norm_cast
        omega
      apply K_inv_le_eps

private theorem X_pow_mul_prod_le_radical : (X : ℝ)^(-ε) * ∏ j, x j ≤ (radical n : ℕ) := calc
    (X : ℝ) ^ (-ε) * ∏ j, x j ≤ ∏ (j : Fin d), if j ≠ (K-1:ℕ) then x j else 1 := by
      rw [Real.rpow_neg (by positivity)]
      apply inv_mul_le_of_le_mul₀
      · positivity
      · positivity
      · calc
          _ ≤ (x (K-1):ℝ) * ∏ j : Fin d, if j ≠ (K-1:ℕ) then x j else 1 := by
            norm_cast
            push_cast
            have : (K:Fin d) - 1 = ((K-1: ℕ) : Fin d) := by
              rw [Nat.cast_sub]
              · simp
              have := two_lt_K
              omega
            rw [← Finset.prod_filter, Finset.filter_ne', this, Finset.mul_prod_erase]
            exact Finset.mem_univ _
          _ ≤ _ := by
            have := x_K_le_X_pow
            gcongr
    _ = ∏ j : Fin d, if j.val ≠ (K-1:ℕ) then y (j.val + 1) else 1 := by
      have (j : Fin d) : j.val = (K-1) ↔ j = (K-1 : ℕ) := by
        apply (fin_eq_nat_iff _).symm
        have := hKd
        omega
      norm_cast
      simp_rw [← Finset.prod_filter, this]
      apply Finset.prod_congr
      · ext j; simp
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      intro j h
      have : j.val + 1 ≠ K := by
        intro hK
        rw [← hK] at h
        simp only [add_tsub_cancel_right, Fin.cast_val_eq_self, not_true_eq_false] at h
      simp [x, y, mul_ite, mul_one, ite_eq_right_iff, h, this]
    _ ≤ ∏ j : Fin d, if j.val + 1 ≠ (K:ℕ) then y (j.val + 1) else 1 := by
      gcongr with j
      apply le_of_eq
      apply if_congr _ rfl rfl
      apply Iff.not
      rw [eq_comm, Nat.sub_eq_iff_eq_add, eq_comm]
      have := two_lt_K
      omega
    _ = ∏ m ∈ Finset.range d with m + 1 ≠ K, y (m+1) := by
      norm_cast
      rw [Finset.prod_filter,
        Fin.prod_univ_eq_prod_range (fun j ↦ if j + 1 ≠ K then y (j + 1) else 1) d]
    _ ≤ ∏ m ∈ Finset.range d, y (m+1) := by
      norm_cast
      apply Finset.prod_le_prod_of_subset_of_one_le'
      · exact Finset.filter_subset (fun m ↦ m + 1 ≠ K) (Finset.range d)
      · intros
        apply hy_pos
    _ = ∏ m ∈ Finset.Icc 1 d, y m := by
      norm_cast
      have : (Finset.range d).map (addRightEmbedding 1) = Finset.Icc 1 d := by
        have : 1 ≤ d := by
          apply hd_pos
        rw [Nat.range_eq_Icc_zero_sub_one _ (by omega), Finset.map_add_right_Icc]
        simp [this]
      simp [← this, Finset.prod_map]
    _ ≤ ∏ m ∈ Finset.Icc 1 d ∪ Finset.Ioc d n, y m := by
      norm_cast
      apply Finset.prod_le_prod_of_subset_of_one_le'
      · intro x
        simp +contextual
      · simp only [Finset.mem_union, Finset.mem_range, Finset.mem_Icc, Finset.mem_filter, not_and,
          Decidable.not_not, hy_pos]
        intro i _ _
        apply hy_pos
    _ = (radical n : ℕ) := mod_cast prod_y_eq_radical_n

theorem exists_nice_factorization :
  ∃ (x : (Fin d) → ℕ), ∃ c : ℕ,
    n = c * ∏ j, x j ^ (j.val + 1:ℕ) ∧
    c ≤ (X:ℝ)^(ε) ∧
    (∀ i j, i ≠ j → Nat.gcd (x i) (x j) = 1) ∧
    (X:ℝ)^(- ε) * ∏ j, x j ≤ (radical n : ℕ) ∧ (radical n : ℕ) ≤ (X:ℝ)^(ε) * ∏ j, x j := by
  refine ⟨x, c, c_mul_prod_x_eq_n.symm, c_le_X_pow, x_pairwise_coprime, X_pow_mul_prod_le_radical,
    radical_le_X_pow_mul_prod⟩

end NiceFactorization


open NiceFactorization in
/-- Proposition 2.5. The bulk of the proof is in the section `NiceFactorization`. -/
theorem exists_nice_factorization
  {ε : ℝ}
  (hε_pos : 0 < ε)
  (hε : ε < 1/2)
  {d : ℕ}
  (hd : d = ⌊5/2 * ε⁻¹^2⌋₊)
  {n : ℕ}
  {X : ℕ}
  (h1n : 1 ≤ n)
  (hnX : n ≤ X) :
  ∃ (x : (Fin d) → ℕ), ∃ c : ℕ,
    n = c * ∏ j, x j ^ (j.val + 1 : ℕ) ∧
    c ≤ (X : ℝ) ^ ε ∧
    (∀ i j, i ≠ j → Nat.gcd (x i) (x j) = 1) ∧
    (X:ℝ)^(- ε) * ∏ j, x j ≤ (radical n : ℕ) ∧ (radical n : ℕ) ≤ (X:ℝ)^(ε) * ∏ j, x j ∧
    0 < c ∧ (∀ i, 0 < x i) ∧ (∀ i, x i ≤ X) := by
  let data : NiceFactorization.ProofData := ⟨
    ε, hε_pos, hε, d, hd, n, X, h1n, hnX
  ⟩
  obtain ⟨x, c, hn, hc, hcop, h_le_rad, h_rad_le⟩ := NiceFactorization.exists_nice_factorization
  have : NeZero ProofData.d := by infer_instance
  simp_rw [data] at *
  have hc_pos : 0 < c := by
    have : 0 < n := by omega
    apply Nat.pos_of_mul_pos_right (hn ▸ this)
  have x_le_X (i : Fin d) : x i ≤ X := by
    apply le_trans _ hnX
    apply Nat.le_of_dvd
    · omega
    rw [hn]
    apply Dvd.dvd.mul_left
    trans x i ^ (i.val + 1)
    · apply dvd_pow (dvd_rfl)
      omega
    apply Finset.dvd_prod_of_mem
    exact Finset.mem_univ i
  have hx_pos (i : Fin d) : 0 < x i := by
    apply Nat.pos_of_ne_zero
    intro h
    rw [Finset.prod_eq_zero (Finset.mem_univ i)] at hn
    · omega
    · simp [h]
  exact ⟨x, c, hn, hc, hcop, h_le_rad, h_rad_le, hc_pos, hx_pos, x_le_X⟩

/-- Some basic consequences of Proposition 2.5, phrased in a way that make them more useful in the
  proof of Proposition 2.6. -/
theorem exists_nice_factorization'
  {ε : ℝ}
  (hε_pos : 0 < ε)
  (hε : ε < 1/2)
  {d : ℕ}
  (hd : d = ⌊10 * ε⁻¹^4⌋₊)
  {n : ℕ}
  {X : ℕ}
  (h1n : 1 ≤ n)
  (hnX : n ≤ X)
  (α : ℝ)
  (hsim : (radical n : ℕ) ~ (X : ℝ) ^ α) :
  ∃ (x : (Fin d) → ℕ), ∃ c : ℕ,
    n = c * ∏ j, x j ^ (j.val + 1 : ℕ) ∧
    c ≤ (X : ℝ) ^ (ε^2) ∧
    c ≤ ⌊(X : ℝ) ^ (ε/4)⌋₊ ∧
    (∀ i j, i ≠ j → Nat.gcd (x i) (x j) = 1) ∧
    (X : ℝ)^(α - ε) ≤ ∏ j, x j ∧ ∏ j, x j ≤ 2 * (X : ℝ)^(α + ε) ∧
    0 < c ∧ (∀ i, 0 < x i) ∧ (∀ i, x i ≤ X) := by
  have hε_sq : ε^2/2 < 1/2 := by
    nlinarith only [hε, hε_pos]
  have : 0 < X := by omega
  simp only [similar, Set.mem_Icc] at hsim
  obtain ⟨x, c, x_eq_c_mul_prod, c_le_pow, hx_cop, le_rad_n, rad_n_le, c_pos, hx_pos, hx_le_X⟩ :=
    exists_nice_factorization (ε := ε^2/2) (by positivity) hε_sq (d := d) (by rw [hd]; ring_nf)
      h1n hnX
  refine ⟨x, c, x_eq_c_mul_prod, ?_, ?_, hx_cop, ?_, ?_, c_pos, hx_pos, hx_le_X⟩
  · trans (X : ℝ)^(ε^2/2)
    · exact c_le_pow
    gcongr
    · norm_cast
    · linarith [sq_nonneg ε]
  · rw [Nat.le_floor_iff]
    · apply c_le_pow.trans
      gcongr _ ^ ?_
      · norm_cast
      · nlinarith
    positivity
  · rw [sub_eq_add_neg, Real.rpow_add, Real.rpow_neg, mul_inv_le_iff₀]
    · apply hsim.1.trans (rad_n_le.trans _)
      rw [mul_comm]
      gcongr
      · norm_cast
      · nlinarith only [hε, hε_pos]
    · positivity
    · positivity
    · positivity
  · rw [Real.rpow_add, ← mul_assoc, ← mul_inv_le_iff₀]
    · apply le_trans (le_trans _ le_rad_n) hsim.2
      rw [mul_comm, Real.rpow_neg (by positivity)]
      gcongr
      · norm_cast
      · nlinarith only [hε, hε_pos]
    · positivity
    · norm_cast


/-- A surjective map ⋃_{c, X, Y ,Z} B (c, X, Y, Z) → S*_α β γ (X) -/
def B_to_triple {d : ℕ} : (Fin d → ℕ) × (Fin d → ℕ) × (Fin d → ℕ) × (Fin 3 → ℕ) → ℕ × ℕ × ℕ :=
  fun ⟨X, Y, Z, c⟩ ↦
    ⟨c 0 * ∏ i, X i ^ (i.val + 1), c 1 * ∏ i, Y i ^ (i.val + 1), c 2 * ∏ i, Z i ^ (i.val + 1)⟩

open Classical in
/-- The finite set over which we will take a supremum in proposition 2.6 -/
noncomputable def indexSet' (α β γ : ℝ) (d : ℕ) (x : ℕ) (ε : ℝ) :
    Finset ((Fin d → ℕ) × (Fin d → ℕ) × (Fin d → ℕ) × (Fin 3 → ℕ)) :=
  ((Fintype.piFinset (fun _ ↦ Finset.Icc 0 (Nat.log 2 x))) ×ˢ
  (Fintype.piFinset (fun _ ↦ Finset.Icc 0 (Nat.log 2 x))) ×ˢ
  (Fintype.piFinset (fun _ ↦ Finset.Icc 0 (Nat.log 2 x)) ×ˢ
  (Fintype.piFinset (fun _ ↦ Finset.Ioc 0 ⌊(x:ℝ)^(ε/4)⌋₊) : Finset (Fin 3 → ℕ))
  ) |>.filter fun ⟨r, s, t, c⟩ ↦
    (x:ℝ) ^ (α - ε) ≤ 2^d * ∏ i, 2 ^ r i ∧ ∏ i, 2 ^ r i ≤ 2 * (x:ℝ) ^ (α + ε) ∧
    (x:ℝ) ^ (β - ε) ≤ 2^d * ∏ i, 2 ^ s i ∧ ∏ i, 2 ^ s i ≤ 2 * (x:ℝ) ^ (β + ε) ∧
    (x:ℝ) ^ (γ - ε) ≤ 2^d * ∏ i, 2 ^ t i ∧ ∏ i, 2 ^ t i ≤ 2 * (x:ℝ) ^ (γ + ε) ∧
    ∏ i, (2 ^ r i)^(i.val + 1) ≤ x ∧
    ∏ i, (2 ^ s i)^(i.val + 1) ≤ x ∧
    ∏ i, (2 ^ t i)^(i.val + 1) ≤ x ∧
    (x : ℝ)^(1-ε^2) ≤ 2^(Nat.choose (d+1) 2 + 1) * ∏ i, (2 ^ t i)^(i.val + 1) ∧
    (Nat.Coprime (c 0) (c 1)) ∧ (Nat.Coprime (c 1) (c 2)) ∧ (Nat.Coprime (c 0) (c 2)))

theorem card_indexSet'_le (α β γ : ℝ) (d : ℕ) (x : ℕ) (ε : ℝ)  :
    (indexSet' α β γ d x ε).card ≤ (Nat.log 2 x + 1)^(3*d) * (⌊(x:ℝ) ^ (ε/4)⌋₊)^3 := by
  rw [indexSet']
  apply Finset.card_filter_le .. |>.trans
  simp only [card_product, Fintype.card_piFinset, Nat.card_Icc, tsub_zero, prod_const, card_univ,
    Fintype.card_fin, Nat.card_Ioc]
  apply le_of_eq
  ring

/-- The union of `B`-sets used in the proof of proposition 2.6. -/
noncomputable def BUnion (α β γ : ℝ) {d : ℕ} (x : ℕ) (ε : ℝ) :
    Finset ((Fin d → ℕ) × (Fin d → ℕ) × (Fin d → ℕ) × (Fin 3 → ℕ)) :=
  (indexSet' α β γ d x ε).sup fun ⟨r, s, t, c⟩ ↦
    B_finset d c (fun i ↦ 2^r i) (fun i ↦ 2^s i) (fun i ↦ 2^t i)

theorem similar_pow_log {x : ℕ} (hx : 0 < x) : x ~ 2 ^ Nat.log 2 x := by
  simp only [similar, Set.mem_Icc]
  norm_cast
  constructor
  · refine Nat.pow_log_le_self 2 hx.ne.symm
  · rw [mul_comm, ← Nat.pow_succ]
    apply le_of_lt
    refine Nat.lt_pow_succ_log_self ?_ x
    norm_num

theorem coprime_mul_prod_aux {ι : Type*} {s : Finset ι} {f g u v : ι → ℕ} {a b : ℕ}
    (hu : ∀ i, 0 < u i) (hv : ∀ i, 0 < v i)
    (hcop : Nat.Coprime (a * ∏ i ∈ s, (f i) ^ (u i)) (b * ∏ i ∈ s, g i ^ (v i))) :
    Nat.Coprime (a * ∏ i ∈ s, f i) (b * ∏ i ∈ s, g i) := by
  simpa only [Nat.coprime_mul_iff_right, Nat.coprime_mul_iff_left, Nat.coprime_prod_left_iff,
    Nat.coprime_prod_right_iff, hu, Nat.coprime_pow_left_iff, hv, Nat.coprime_pow_right_iff] using
    hcop

open Finset in
theorem Nat.sum_Ico_choose (n k : ℕ) : ∑ m ∈ Ico k n, m.choose k = n.choose (k + 1) := by
  rcases le_or_lt n k with h | h
  · rw [choose_eq_zero_of_lt (by omega), Ico_eq_empty_of_le h, sum_empty]
  · induction n, h using le_induction with
    | base => simp
    | succ n _ ih =>
      rw [← insert_Ico_right_eq_Ico_add_one (by omega), sum_insert (by simp), ih,
        choose_succ_succ' n]

open Finset in
lemma Nat.sum_range_add_choose' (n k : ℕ) :
    ∑ i ∈ Finset.range n, (i + k).choose k = (n + k).choose (k + 1) := by
  rw [← sum_Ico_choose, range_eq_Ico]
  convert (sum_map _ (addRightEmbedding k) (·.choose k)).symm using 2
  rw [Finset.map_add_right_Ico, zero_add]

theorem sum_range_id_add_one {d : ℕ} : ∑ i ∈ Finset.range d, (i + 1) = (d + 1).choose 2 := by
  simpa using Nat.sum_range_add_choose' d 1

theorem B_to_triple_surjOn {α β γ : ℝ}  (x : ℕ) (ε : ℝ) (hε_pos : 0 < ε) (hε : ε < 1/2) {d : ℕ}
    (hd : d = ⌊10 * ε⁻¹ ^ 4⌋₊) :
    Set.SurjOn (B_to_triple (d := d)) (BUnion α β γ x ε).toSet (dyadicPoints α β γ x).toSet := by
  intro ⟨a, b, c⟩
  simp only [Finset.mem_coe, mem_dyadicPoints, BUnion, Set.mem_image, Finset.mem_sup,
    Fintype.mem_piFinset, Finset.mem_Icc, zero_le, true_and, Prod.exists, and_imp]
  intro ha hb hc hab hac hbc habc hrada hradb hradc hxc hcx
  obtain ⟨u, c₀, a_eq_c_mul_prod, _, c₀_le_floor, hu_cop, x_pow_α_le, le_x_pow_α,
    c₀_pos, hu_pos, _⟩ :=
    exists_nice_factorization' hε_pos hε hd ha (show a ≤ x by linarith) _ hrada
  obtain ⟨v, c₁, b_eq_c_mul_prod, _, c₁_le_floor, hv_cop, x_pow_β_le, le_x_pow_β,
    c₁_pos, hv_pos, _⟩ :=
    exists_nice_factorization' hε_pos hε hd hb (show b ≤ x by linarith) _ hradb
  obtain ⟨w, c₂, c_eq_c_mul_prod, c₂_le_pow, c₂_le_floor, hw_cop, x_pow_γ_le,
    le_x_pow_γ, c₂_pos, hw_pos, _⟩ :=
    exists_nice_factorization' hε_pos hε hd hc (show c ≤ x by linarith) _ hradc
  have hax : a ≤ x := by omega
  have hbx : b ≤ x := by omega
  have hcx : c ≤ x := by omega

  let c' : Fin 3 → ℕ := ![c₀, c₁, c₂]

  have prod_pow_le {u : Fin d → ℕ} (h : ∀ i, 0 < u i) : ∏ i, 2 ^ Nat.log 2 (u i) ≤ ∏ i, u i := by
    gcongr with i
    apply Nat.pow_log_le_self
    exact (h i).ne.symm

  have le_prod_pow {u : Fin d → ℕ} : ∏ i, u i ≤ 2 ^ d * ∏ i, 2 ^ Nat.log 2 (u i) := calc
    _ ≤ ∏ i, 2 ^ (Nat.log 2 (u i) + 1) := by
      gcongr with i
      apply (Nat.lt_pow_succ_log_self ..).le
      norm_num
    _ = _ := by
      simp [Nat.pow_add, Finset.prod_mul_distrib]
      ring

  have prod_log_pow_le_prod_pow {u : Fin d → ℕ} (hu : ∀ i, 0 < u i):
      ∏ i, (2 ^ Nat.log 2 (u i)) ^ (i.val + 1) ≤ ∏ i, u i ^ (i.val + 1) := by
    apply Finset.prod_le_prod
    · simp
    simp only [Finset.mem_univ, forall_const]
    intro i
    gcongr
    refine Nat.pow_log_le_self 2 ?_
    apply (hu _).ne.symm

  refine ⟨u, v, w, c', ?_, ?easy⟩
  case easy =>
    simp only [B_to_triple, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
      Prod.mk.injEq, c']
    refine ⟨a_eq_c_mul_prod.symm, b_eq_c_mul_prod.symm, c_eq_c_mul_prod.symm⟩
  refine ⟨fun i ↦ Nat.log 2 (u i), fun i ↦ Nat.log 2 (v i), fun i ↦ Nat.log 2 (w i), c', ?_, ?_⟩
  · simp only [indexSet', Fin.isValue, mem_filter, mem_product, Fintype.mem_piFinset, mem_Icc,
      zero_le, true_and, mem_Ioc]
    refine ⟨?_, ?_⟩
    · refine ⟨?_, ?_, ?_, ?_⟩ <;> try {
      · intro i
        apply Nat.log_mono_right
        simp [*] }
      simp only [c']
      intro i
      fin_cases i <;>
        simp [c₀_pos, c₁_pos, c₂_pos, c₀_le_floor, c₁_le_floor, c₂_le_floor]
    refine ⟨x_pow_α_le.trans (mod_cast le_prod_pow),
      le_trans (mod_cast (prod_pow_le hu_pos)) le_x_pow_α,
      x_pow_β_le.trans (mod_cast le_prod_pow),
      le_trans (mod_cast (prod_pow_le hv_pos)) le_x_pow_β,
      x_pow_γ_le.trans (mod_cast le_prod_pow),
      le_trans (mod_cast (prod_pow_le hw_pos)) le_x_pow_γ, ?_⟩
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · apply (prod_log_pow_le_prod_pow hu_pos).trans
        ((a_eq_c_mul_prod ▸ Nat.le_mul_of_pos_left _ c₀_pos).trans hax)
    · apply (prod_log_pow_le_prod_pow hv_pos).trans
        ((b_eq_c_mul_prod ▸ Nat.le_mul_of_pos_left _ c₁_pos).trans hbx)
    · apply (prod_log_pow_le_prod_pow hw_pos).trans
        ((c_eq_c_mul_prod ▸ Nat.le_mul_of_pos_left _ c₂_pos).trans hcx)
    · calc
        _ ≤ 2 * (∏ i, w i^(i.val+1) : ℝ):= by
          rw [Real.rpow_sub, div_eq_mul_inv, mul_inv_le_iff₀, mul_comm]
          · simp only [Real.rpow_one]
            trans 2 * (c₂ *(∏ i, (w i : ℝ) ^ (i.val + 1)))
            · norm_cast
              rw [← c_eq_c_mul_prod]
              apply hxc
            · rw [← mul_assoc, mul_comm 2, mul_assoc]
              gcongr
          · apply Real.rpow_pos_of_pos
            norm_cast
            omega
          · norm_cast
            omega
        _ ≤ 2 * (∏ i, (2 ^ (Nat.log 2 (w i)+1))^(i.val+1) : ℝ):= by
          norm_cast
          gcongr _ * ?_
          apply Finset.prod_le_prod
          · simp
          intro i _
          gcongr
          rw [← Nat.succ_eq_add_one]
          apply le_of_lt
          apply Nat.lt_pow_succ_log_self
          norm_num
        _ = _ := by
          rw [add_comm, pow_add _ 1, pow_one, mul_assoc]
          congr 1
          norm_cast
          conv =>
            lhs
            right
            ext i;
            rw [pow_add 2 _ 1, pow_one, mul_pow, mul_comm]
          simp_rw [Finset.prod_mul_distrib]
          rw [Finset.prod_pow_eq_pow_sum]
          congr
          rw [Finset.sum_fin_eq_sum_range]
          simp +contextual only [← mem_range, ↓reduceDIte]
          apply sum_range_id_add_one
    · simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, c']
      simp_rw [a_eq_c_mul_prod, b_eq_c_mul_prod, c_eq_c_mul_prod] at hab hbc hac
      refine ⟨hab.coprime_mul_right.coprime_mul_right_right,
        hbc.coprime_mul_right.coprime_mul_right_right,
        hac.coprime_mul_right.coprime_mul_right_right⟩
  · simp only [mem_B_finset, Nat.cast_pow, Nat.cast_ofNat, Fin.isValue, true_and, c']
    simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Nat.succ_eq_add_one, Nat.reduceAdd, Matrix.tail_cons, c']
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · apply fun i ↦ (similar_pow_log (hu_pos i))
    · apply fun i ↦ (similar_pow_log (hv_pos i))
    · apply fun i ↦ (similar_pow_log (hw_pos i))
    · rw [←a_eq_c_mul_prod, ←b_eq_c_mul_prod, ←c_eq_c_mul_prod]
      exact habc
    · apply coprime_mul_prod_aux _ _ (a_eq_c_mul_prod ▸ b_eq_c_mul_prod ▸ hab) <;> omega
    · apply coprime_mul_prod_aux _ _ (a_eq_c_mul_prod ▸ c_eq_c_mul_prod ▸ hac) <;> omega
    · apply coprime_mul_prod_aux _ _ (b_eq_c_mul_prod ▸ c_eq_c_mul_prod ▸ hbc) <;> omega

theorem refinedCountTriplesStar_le_card_BUnion (α β γ : ℝ) {d : ℕ} (x : ℕ) (ε : ℝ)
    (hε_pos : 0 < ε) (hε : ε < 1/2) (hd : d = ⌊10 * ε⁻¹ ^ 4⌋₊) :
    refinedCountTriplesStar α β γ x ≤ (BUnion α β γ x ε (d := d)).card := by
  rw [refinedCountTriplesStar]
  apply Finset.card_le_card_of_surjOn _ (B_to_triple_surjOn ..)
  · exact hε_pos
  · exact hε
  · exact hd

section Asymptotics
/- TODO: The results in this section should probably be cleaned up - in the end we also lose a
  factor of (log x)^4 going from N to S, perhaps this should also be rolled into this constant. -/

theorem log_le_const_mul_pow {ε : ℝ} (hε : 0 < ε) (d : ℕ) (hd : 0 < d) :
    ∃ c ≥ 0, ∀ x : ℕ, (Real.log x)^d ≤ c * (x : ℝ)^ε := by
  have := (isLittleO_log_rpow_rpow_atTop d hε).isBigO.natCast_atTop
  have := this.nat_of_atTop (l := ⊤) ?_
  · simp only [Real.rpow_natCast, Asymptotics.isBigO_iff', norm_pow, Real.norm_eq_abs] at this
    simp only [gt_iff_lt, eventually_top] at this
    obtain ⟨c, hc_pos, hc⟩ := this
    refine ⟨c, hc_pos.le, ?_⟩
    intro x
    calc
      _ ≤ _ := by
        gcongr
        exact le_abs_self (Real.log ↑x)
      _ ≤ _ := hc x
      _ ≤ _ := by
        rw [abs_of_nonneg]
        positivity
  · simp [Real.rpow_natCast, hε.ne', hd.ne']

theorem tmp {ε : ℝ} (hε : 0 < ε) (d : ℕ) (hd : 0 < d) :
    ∃ c, ∀ x : ℕ, 2 ≤ x → (Nat.log 2 x + 1) ^ (3 * d) ≤ c * (x : ℝ)^(ε/4) := by
  obtain ⟨c, hc_nonneg, hc⟩ := log_le_const_mul_pow (show 0 < ε/4 by linarith) (3*d) (by omega)
  use (Real.log 2)⁻¹ ^ (3*d) * c * 2^(ε/4)
  intro x hx
  specialize hc (2*x)
  have log_add : Nat.log 2 x + 1 = Nat.log 2 (2 * x) := by
    rw [mul_comm, Nat.log_mul_base]
    · norm_num
    omega
  have : (Nat.log 2 (2 * x))^(3*d) ≤ (Real.log 2)⁻¹ ^ (3*d) * Real.log (2 * x) ^ (3*d) := by
    trans (Real.logb 2 (2 * x))^(3*d)
    · gcongr
      rw [← Real.natFloor_logb_natCast]
      push_cast
      apply Nat.floor_le
      apply Real.logb_nonneg <;> norm_cast
      omega
    · apply le_of_eq
      rw [← Real.log_div_log]
      ring
  calc
    _ ≤ ((Nat.log 2 (2 * x)) ^ (3 * d) : ℝ) :=  by
      rw_mod_cast [log_add]
    _ ≤ ((Real.log 2)⁻¹ ^ (3*d) * c * 2^(ε/4) * (x : ℝ)^(ε/4): ℝ) :=  by
      apply this.trans
      simp_rw [mul_assoc]
      gcongr
      push_cast at hc
      apply hc.trans
      gcongr
      rw [Real.mul_rpow] <;> norm_num

/-- The implicit constant in the conclusion of proposition 2.6 -/
noncomputable def const (ε : ℝ) : ℝ :=
  if h : 0 < ε then
    if h' : ε < 1/2 then
      let d := ⌊10 * ε⁻¹^4⌋₊
      have : 2 < ε⁻¹ := by
        rw [← show (2:ℝ)⁻¹⁻¹ = 2 by norm_num]
        gcongr
        linarith
      have : 2 ^ 4 < ε⁻¹^4 := by gcongr
      have hd : 0 < d := by rw [Nat.floor_pos]; linarith
      Classical.choose (tmp h d hd)
    else 0
  else 0

theorem const_spec {ε : ℝ} (hε_pos : 0 < ε) (hε : ε < 1/2) :
    let d := ⌊10 * ε⁻¹^4⌋₊
    ∀ x : ℕ, 2 ≤ x → (Nat.log 2 x + 1) ^ (3 * d) ≤ const ε * (x : ℝ)^(ε/4) := by
  rw [const, dif_pos hε_pos, dif_pos hε]
  extract_lets d _ _ _ hd
  apply Classical.choose_spec (tmp hε_pos d hd)

theorem const_nonneg {ε : ℝ} : 0 ≤ const ε := by
  by_cases hε_pos : 0 < ε
  · by_cases hε : ε < 1/2
    · have := const_spec hε_pos hε 2 le_rfl
      simp only [inv_pow, Nat.cast_ofNat] at this
      have := calc
        0 ≤ _ := mod_cast zero_le _
        _ ≤ _ := this
      -- surely there's a better lemma that doesn't require strict positivity
      apply nonneg_of_mul_nonneg_left this
      apply Real.rpow_pos_of_pos
      norm_num
    · rw [const, dif_pos hε_pos, dif_neg hε]
  · rw [const, dif_neg hε_pos]

end Asymptotics

theorem card_indexSet'_le_pow (ε α β γ : ℝ) (d x : ℕ) (hd : d = ⌊10* ε⁻¹^4⌋₊) (hx : 2 ≤ x)
    (hε_pos : 0 < ε) (hε : ε < 1/2) :
    (indexSet' α β γ d x ε).card ≤ const ε * (x:ℝ)^ε := by
  have := const_spec hε_pos hε x hx
  rw [← hd] at this
  calc
    _ ≤ ((Nat.log 2 x + 1) ^ (3 * d) * ⌊(x : ℝ) ^ (ε / 4)⌋₊ ^ 3 : ℝ) :=
      mod_cast card_indexSet'_le α β γ d x ε
    _ ≤ (const ε * (x : ℝ) ^ (ε/4) * (x : ℝ) ^ (3/4 * ε) : ℝ) :=  by
      gcongr
      · have := const_nonneg (ε := ε)
        positivity
      · trans (x ^ (ε / 4)) ^ 3
        · gcongr
          apply Nat.floor_le
          positivity
        apply le_of_eq
        rw [← Real.rpow_mul_natCast (by positivity)]
        ring_nf
    _ = const ε * (x : ℝ) ^ ε  :=  by
      rw [mul_assoc, ← Real.rpow_add]
      · ring_nf
      · positivity

/-- The value of `d` chosen in proposition 2.6 -/
noncomputable def d (ε : ℝ) : ℕ := ⌊10 * ε⁻¹ ^ 4⌋₊

/- Proposition 2.7. Reformulated slightly in terms of the existence of a `Finset` whose elements
  have certain properties. As it stands the statement in the blueprint implicitly assumes that
  this `Finset` is nonempty. That might be true, but is rather annoying to prove and unnecessary
  if we just need an upper bound on S*. -/
theorem refinedCountTriplesStar_isBigO_B
  {α β γ : ℝ}
  /- I'm surprised these assumptions are not necessary.
    Shoud think about if I've done something wrong - Arend -/
  -- (hα_pos : 0 < α) (hβ_pos : 0 < β) (hγ_pos : 0 < γ)
  -- (hα1 : α ≤ 1) (hβ1 : β ≤ 1) (hγ1 : γ ≤ 1)
  {x : ℕ} (h2X : 2 ≤ x) {ε : ℝ} (hε_pos : 0 < ε) (hε : ε < 1/2) :
  ∃ s : Finset ((Fin (d ε) → ℕ) × (Fin (d ε) → ℕ) × (Fin (d ε) → ℕ) × (Fin 3 → ℕ)),
    refinedCountTriplesStar α β γ x ≤
      const ε * (x : ℝ) ^ ε * ↑(s.sup (fun ⟨X, Y, Z, c⟩ ↦ B (d ε) c X Y Z): ℕ) ∧
    ∀ X Y Z : Fin (d ε) → ℕ,
    ∀ c : Fin 3 → ℕ,
    ⟨X, Y, Z, c⟩ ∈ s →
    (x:ℝ)^(α - ε) ≤ 2 ^ d ε * ∏ j, X j ∧ ∏ j, X j ≤ 2 * (x : ℝ) ^ (α + ε) ∧
    (x:ℝ)^(β - ε) ≤ 2 ^ d ε * ∏ j, Y j ∧ ∏ j, Y j ≤ 2 * (x : ℝ) ^ (β + ε) ∧
    (x:ℝ)^(γ - ε) ≤ 2 ^ d ε * ∏ j, Z j ∧ ∏ j, Z j ≤ 2 * (x : ℝ) ^ (γ + ε) ∧
    ∏ i, X i ^ (i.val + 1) ≤ x ∧
    ∏ i, Y i ^ (i.val + 1) ≤ x ∧
    ∏ i, Z i ^ (i.val + 1) ≤ x ∧
    (x : ℝ) ^ (1 - ε^2) ≤ 2^(Nat.choose (d ε + 1) 2 + 1) * ∏ i, Z i ^ (i.val + 1) ∧
    (Nat.Coprime (c 0) (c 1)) ∧ (Nat.Coprime (c 1) (c 2)) ∧ (Nat.Coprime (c 0) (c 2)) ∧
    (∀ i, 1 ≤ c i) ∧
    (∀ i, (c i : ℝ) ≤ (x : ℝ) ^ ε)
    := by
  have h₁ := refinedCountTriplesStar_le_card_BUnion α β γ (d := d ε) x ε hε_pos hε rfl
  simp_rw [BUnion, Finset.sup_eq_biUnion] at h₁
  have h₂ := h₁.trans Finset.card_biUnion_le |>.trans (sum_le_card_mul_sup ..)
  use (indexSet' α β γ (d ε) x ε).image fun ⟨u, v, w, c⟩ ↦
    ⟨fun i ↦ 2 ^ u i, fun i ↦ 2 ^ v i, fun i ↦ 2 ^ w i, c⟩
  simp only [Finset.sup_image, Finset.mem_image, Prod.mk.injEq, Prod.exists, Nat.cast_prod,
    Nat.cast_pow, forall_exists_index, and_imp]
  refine ⟨?_, ?_⟩
  · calc
      _ ≤ ((_ : ℕ) : ℝ) := Nat.cast_le.2 h₂
      _ ≤ _ := by
        push_cast
        gcongr
        · have := const_nonneg (ε := ε)
          positivity
        · exact card_indexSet'_le_pow ε α β γ (d ε) x rfl h2X hε_pos hε
        rfl
  rintro X Y Z _ u v w c huvwc rfl rfl rfl rfl
  simp only [Nat.cast_pow, Nat.cast_ofNat]
  revert huvwc
  simp only [indexSet', Finset.mem_filter, Finset.mem_product, Fintype.mem_piFinset, Finset.mem_Icc,
    zero_le, true_and, Finset.mem_Ioc, and_imp]
  rintro _ _ _ hc _ _ _ _ _ _ _ _ _ _ _ _ _
  refine ⟨by assumption, by assumption, by assumption, by assumption, by assumption, by assumption,
    by assumption, by assumption, by assumption, by assumption, by assumption, by assumption,
    by assumption, ?_, ?_⟩
  · intro i
    apply Nat.succ_le_of_lt
    apply hc i |>.1
  · intro i
    calc
      (c i : ℝ) ≤ (⌊(x:ℝ) ^ (ε / 4)⌋₊ : ℝ) := by
        norm_cast
        apply (hc i).2
      _ ≤ (x : ℝ)^(ε/4) := by
        apply Nat.floor_le
        positivity
      _ ≤  _ := by
        gcongr
        · norm_cast; omega
        · linarith
