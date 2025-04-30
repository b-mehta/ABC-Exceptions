import Mathlib.Algebra.GCDMonoid.Nat
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.StarOrdered
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Radical
import Mathlib.RingTheory.SimpleModule
import Mathlib.RingTheory.UniqueFactorizationDomain.Nat

open UniqueFactorizationMonoid

open Classical in
noncomputable def ABCTriples_finset (μ : ℝ) (X : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  (Finset.Icc (2, 2, 2) (X, X, X)).filter fun ⟨a, b, c⟩ ↦
    a.Coprime b ∧ a.Coprime c ∧ b.Coprime c ∧
    a + b = c ∧
    radical (a * b * c) < (c ^ μ : ℝ)

@[simp]
theorem mem_ABCTriples (μ : ℝ) (X : ℕ) (a b c : ℕ) :
  ⟨a, b, c⟩ ∈ ABCTriples_finset μ X ↔
    a.Coprime b ∧ a.Coprime c ∧ b.Coprime c ∧
    a + b = c ∧
    radical (a * b * c) < (c ^ μ : ℝ) ∧
    (a, b, c) ∈ Set.Icc (2, 2, 2) (X, X, X) := by
  sorry

def ABCTriples (μ : ℝ) (X : ℕ) : Set (ℕ × ℕ × ℕ) :=
  { (a, b, c) : ℕ × ℕ × ℕ |
    a.Coprime b ∧ a.Coprime c ∧ b.Coprime c ∧
    a + b = c ∧
    radical (a * b * c) < (c ^ μ : ℝ) ∧
    (a, b, c) ∈ Set.Icc (2, 2, 2) (X, X, X) }

noncomputable def countTriples (μ : ℝ) (X : ℕ) : ℕ :=
  (ABCTriples μ X).ncard

lemma countTriples_eq (μ : ℝ) (X : ℕ) :
    countTriples μ X =
      ({ (a, b, c) | 1 < a ∧ 1 < b ∧ 1 < c ∧ a.Coprime b ∧ a.Coprime c ∧ b.Coprime c ∧ a + b = c ∧
         radical (a * b * c) < (c ^ μ : ℝ) } ∩
       Set.Icc (2, 2, 2) (X, X, X)).ncard := by
  rw [countTriples, ABCTriples]
  congr 1
  ext ⟨a, b, c⟩
  simp [and_assoc, ← Prod.mk_one_one]
  aesop

lemma ABCTriples_eq_ABCTriples_finset (μ : ℝ) (X : ℕ) :
    ABCTriples μ X = ABCTriples_finset μ X := by
  sorry

lemma countTriples_eq_finset_card (μ : ℝ) (X : ℕ) :
    countTriples μ X = (ABCTriples_finset μ X).card := by
  sorry

def ABCConjecture : Prop := ∀ ε : ℝ, 0 < ε →
  Set.Finite
  { (a, b, c) : ℕ × ℕ × ℕ |
    0 < a ∧ 0 < b ∧ 0 < c ∧
    a.Coprime b ∧ a.Coprime c ∧ b.Coprime c ∧
    a + b = c ∧
    radical (a * b * c) ^ (1 + ε) < (c : ℝ) }

open Asymptotics Filter

theorem WellFounded.ciSup_eq_monotonicSequenceLimit {α : Type*} [ConditionallyCompleteLattice α]
    (h : WellFounded ((· > ·) : α → α → Prop)) (a : ℕ →o α) (ha : BddAbove (Set.range a)) :
    iSup a = monotonicSequenceLimit a := by
  refine (ciSup_le fun m => ?_).antisymm (le_ciSup ha _)
  rcases le_or_lt m (monotonicSequenceLimitIndex a) with hm | hm
  · exact a.monotone hm
  · cases' WellFounded.monotone_chain_condition'.1 h a with n hn
    have : n ∈ {n | ∀ m, n ≤ m → a n = a m} := fun k hk => (a.mono hk).eq_of_not_lt (hn k hk)
    exact (Nat.sInf_mem ⟨n, this⟩ m hm.le).ge

lemma forall_increasing {α : Type*} (f : ℕ → Set α) (hf : Monotone f) (hf' : ∀ n, (f n).Finite)
    {s : Set α} {C : ℕ} (hC : ∀ n, (s ∩ f n).ncard ≤ C) : (s ∩ ⋃ n, f n).Finite := by
  rw [Set.inter_iUnion]
  by_contra!
  obtain ⟨t, ht, ht', ht''⟩ := Set.Infinite.exists_subset_ncard_eq this (C + 1)
  lift t to Finset α using ht'
  have hg : Monotone (s ∩ f ·) := fun a b hab ↦ Set.inter_subset_inter_right _ (hf hab)
  obtain ⟨i, hi⟩ := hg.directed_le.exists_mem_subset_of_finset_subset_biUnion ht
  replace hC : (s ∩ f i).ncard ≤ C := hC i
  have := Set.ncard_le_ncard hi ((hf' _).inter_of_right _)
  omega

/- This proof broke because we changed the definition of countTriples to have 2 ≤ a, b, c. -/
lemma abcConjecture_iff :
    ABCConjecture ↔ ∀ μ > 0, μ < 1 → (countTriples μ · : ℕ → ℝ) =O[atTop] (fun _ ↦ (1 : ℝ)) := by
  stop
  simp only [isBigO_one_nat_atTop_iff]

  constructor
  · intro h μ hμ₀ hμ₁
    let ε : ℝ := μ⁻¹ - 1
    have hε : ε > 0 := by simp [ε, one_lt_inv₀ hμ₀, hμ₁]
    have habc := h ε hε
    simp only [countTriples_eq]
    change Set.Finite ?S at habc
    set S : Set (ℕ × ℕ × ℕ) := ?S
    refine ⟨S.ncard, fun n ↦ ?_⟩
    simp only [Real.norm_natCast, Nat.cast_le, Prod.mk.eta]
    refine Set.ncard_le_ncard ?_ habc
    simp +contextual only [Set.subset_def, Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_Icc,
      true_and, and_imp, Prod.forall, Prod.mk_le_mk, S]
    rintro a b c - - - hab hac hbc - h - - - - - -
    refine ⟨hab, hac, hbc, ?_⟩
    rwa [add_sub_cancel, Real.rpow_inv_lt_iff_of_pos (by simp) (by simp) hμ₀]

  · intro h ε hε
    let μ := (1 + ε)⁻¹
    have hμ₀ : μ > 0 := by positivity
    have hμ₁ : μ < 1 := inv_lt_one_of_one_lt₀ (by simpa)
    obtain ⟨C, hC⟩ := h μ hμ₀ hμ₁
    simp only [Real.norm_natCast] at hC
    change Set.Finite ?S'
    set S := ?S'
    have hS : S =
        {(a, b, c) | 0 < a ∧ 0 < b ∧ 0 < c ∧ a.Coprime b ∧ a.Coprime c ∧ b.Coprime c ∧ a + b = c ∧
          radical (a * b * c) < (c : ℝ) ^ μ} := by
      simp only [Set.ext_iff, Set.mem_setOf_eq, and_congr_right_iff, Prod.forall, S]
      intro a b c _ _ _ hab hac hbc habc
      simp only [μ]
      rw [Real.lt_rpow_inv_iff_of_pos (by simp) (by simp) (by positivity)]
    have hC₀ : 0 ≤ C := (hC 0).trans' (Nat.cast_nonneg _)
    replace hC' : ∀ n, (S ∩ Set.Icc (1, 1, 1) (n, n, n)).ncard ≤ ⌊C⌋₊ := by
      intro n
      rw [Nat.le_floor_iff hC₀]
      convert hC n
      rw [countTriples_eq, hS]
    have : Monotone fun n ↦ Set.Icc (1, 1, 1) (n, n, n) :=
      fun n m hnm ↦ Set.Icc_subset_Icc_right (by simpa)
    have := forall_increasing _ this (fun n ↦ Set.finite_Icc _ _) hC'
    have : ⋃ n, Set.Icc (1, 1, 1) (n, n, n) = Set.Ici 1 := by
      ext ⟨i, j, k⟩
      simp only [Set.mem_iUnion, Set.mem_Icc, Prod.mk_le_mk, exists_and_left, ← Prod.mk_one_one,
        Set.mem_Ici, and_iff_left_iff_imp, and_imp]
      intro hi hj hk
      exact ⟨max i (max j k), by simp⟩
    have : S ⊆ ⋃ n, Set.Icc (1, 1, 1) (n, n, n) := by
      rw [this]
      rintro ⟨a, b, c⟩
      simp only [Set.mem_setOf_eq, ← Prod.mk_one_one, Set.mem_Ici, Prod.mk_le_mk, and_imp, S]
      rintro ha hb hc - - - - -
      exact ⟨ha, hb, hc⟩
    rwa [← Set.inter_eq_self_of_subset_left this]

noncomputable def refinedCountTriples (α β γ : ℝ) (X : ℕ) : ℕ :=
  Set.ncard
  { (a, b, c) : ℕ × ℕ × ℕ |
    a.Coprime b ∧ a.Coprime c ∧ b.Coprime c ∧
    a + b = c ∧
    radical a ≤ (a ^ α : ℝ) ∧ radical b ≤ (b ^ β : ℝ) ∧ radical c ≤ (c ^ γ : ℝ) ∧
    (a, b, c) ∈ Set.Icc (1, 1, 1) (X, X, X) }

lemma countTriples_le_max_refinedCountTriples (μ : ℝ) (X : ℕ) :
    ∃ α β γ : ℝ, 0 < α ∧ 0 < β ∧ 0 < γ ∧ α + β + γ ≤ μ ∧
      countTriples μ X ≤ refinedCountTriples α β γ X := by
  sorry

def similar (x X : ℝ) : Prop := x ∈ Set.Icc X (2 * X)

local infixr:36 " ~ " => similar

open Classical in
noncomputable def dyadicPoints (α β γ : ℝ) (X : ℕ) : Finset (ℕ × ℕ × ℕ) :=
   (Finset.Icc (0, 0, 0) (2*X, 2*X, 2*X)).filter fun ⟨a, b, c⟩ ↦
      a.Coprime b ∧ a.Coprime c ∧ b.Coprime c ∧
      a + b = c ∧
      (radical a : ℕ) ~ (X ^ α : ℝ) ∧ (radical b : ℕ) ~ (X ^ β : ℝ) ∧ (radical c : ℕ) ~ (X ^ γ : ℝ) ∧
      c ~ X

@[simp]
theorem mem_dyadicPoints (α β γ : ℝ) (X : ℕ) (a b c : ℕ) :
  ⟨a, b, c⟩ ∈ dyadicPoints α β γ X ↔
    a.Coprime b ∧ a.Coprime c ∧ b.Coprime c ∧
      a + b = c ∧
      (radical a : ℕ) ~ (X ^ α : ℝ) ∧ (radical b : ℕ) ~ (X ^ β : ℝ) ∧ (radical c : ℕ) ~ (X ^ γ : ℝ) ∧
      c ~ X := by
  simp only [dyadicPoints, Finset.mem_filter, Finset.mem_Icc, Prod.mk_le_mk,
    and_iff_right_iff_imp, and_imp]
  intro _ _ _ habc _ _ _ hc
  simp only [zero_le, and_self, true_and]
  simp only [similar, Set.mem_Icc, Nat.cast_le] at hc
  norm_cast at hc
  omega

noncomputable def refinedCountTriplesStar (α β γ : ℝ) (X : ℕ) : ℕ :=
  (dyadicPoints α β γ X).card


theorem Nat.radical_le_self {n : ℕ} (hn : n ≠ 0) : radical n ≤ n := by
  apply Nat.le_of_dvd (by omega)
  exact radical_dvd_self n

theorem Nat.two_le_radical  {n : ℕ} (hn : 2 ≤ n) : 2 ≤ radical n := by
  obtain ⟨p, hp⟩ := Nat.exists_prime_and_dvd (show n ≠ 1 by omega)
  trans p
  · apply hp.1.two_le
  · apply Nat.le_of_dvd
    · apply Nat.pos_of_ne_zero
      exact radical_ne_zero n
    sorry

theorem ABCTriples_subset_union_dyadicPoints (μ : ℝ) (X : ℕ) :
    ABCTriples_finset μ X ⊆
      (Finset.Icc 1 (Nat.log 2 X)).biUnion fun i ↦
      (Finset.Icc 1 (Nat.log 2 X)).biUnion fun j ↦
      (Finset.Icc 1 (Nat.log 2 X)).biUnion fun k ↦
      (Finset.Icc 1 (Nat.log 2 X)).biUnion fun n ↦
        dyadicPoints (i / n : ℝ) (j / n : ℝ) (k / n : ℝ) (2^n) := by
  rintro ⟨a, b, c⟩
  simp only [mem_ABCTriples, Set.mem_Icc, Prod.mk_le_mk, Finset.mem_biUnion,
    Finset.mem_Icc, mem_dyadicPoints, Nat.cast_pow, Nat.cast_ofNat, and_imp]
  intro hab hac hbc habc hrad h1a h1b h1c haX hbX hcX
  -- refine ⟨hab, hac, hbc, habc, ?_⟩
  have {a : ℕ} (h2a : 2 ≤ a) (haX : a ≤ X) : 1 ≤ Nat.log 2 (radical a) ∧ Nat.log 2 (radical a) ≤ Nat.log 2 X := by
    constructor
    · apply Nat.le_log_of_pow_le (by norm_num)
      simp [Nat.two_le_radical h2a]
    · apply Nat.log_mono_right
      apply (Nat.radical_le_self (by omega)).trans haX
  refine ⟨Nat.log 2 (radical a), this h1a haX, Nat.log 2 (radical b), this h1b hbX, Nat.log 2 (radical c), this h1c hcX,  Nat.log 2 c, sorry, ?_⟩
  have {a c : ℕ} (hc : 2 ≤ c) : ((2:ℝ) ^ (Nat.log 2 c)) ^ ((↑(Nat.log 2 (radical a))) / (↑(Nat.log 2 c) ) : ℝ) =
      2^(Nat.log 2 (radical a)) := by
    rw [← Real.rpow_natCast_mul (by norm_num)]
    have : ↑(Nat.log 2 c) * (↑(Nat.log 2 (radical a)) / ↑(Nat.log 2 c):ℝ) = Nat.log 2 (radical a) := by
      rw [mul_div_cancel₀]
      simp [hc]
    rw [this]
    norm_cast
  have hc2 : 2 ≤ c := by
    omega
  simp_rw [this hc2]
  have {a : ℕ} :  (radical a : ℕ) ~ 2 ^ (Nat.log 2 (radical a)) := by
    simp [similar]
    norm_cast
    constructor
    · apply Nat.pow_log_le_self
      exact radical_ne_zero a
    · rw [mul_comm, ← Nat.pow_succ]
      apply (Nat.lt_pow_succ_log_self ..).le
      norm_num
  refine ⟨hab, hac, hbc, habc, this, this, this, ?_⟩
  simp [similar]
  norm_cast
  refine ⟨?_, ?_⟩
  · apply Nat.pow_log_le_self
    omega
  · rw [mul_comm, ← Nat.pow_succ]
    apply (Nat.lt_pow_succ_log_self ..).le
    norm_num

theorem sum_le_card_mul_sup {ι : Type*} (f : ι → ℕ) (s : Finset ι) :
    ∑ i ∈ s, f i ≤ s.card * s.sup f := calc
  ∑ i ∈ s, f i ≤ ∑ i ∈ s, s.sup f := by
    apply Finset.sum_le_sum
    intro i hi
    exact Finset.le_sup hi
  _ = s.card * s.sup f := by
    simp

theorem card_union_dyadicPoints_le_log_pow_mul_sup (X : ℕ) :
  ((Finset.Icc 1 (Nat.log 2 X)).biUnion fun i ↦
    (Finset.Icc 1 (Nat.log 2 X)).biUnion fun j ↦
    (Finset.Icc 1 (Nat.log 2 X)).biUnion fun k ↦
    (Finset.Icc 1 (Nat.log 2 X)).biUnion fun n ↦
      dyadicPoints (i / n : ℝ) (j / n : ℝ) (k / n : ℝ) (2^n)).card  ≤
  (Nat.log 2 X)^4 *
  (Finset.Icc 1 (Nat.log 2 X)).sup fun i ↦
  (Finset.Icc 1 (Nat.log 2 X)).sup fun j ↦
  (Finset.Icc 1 (Nat.log 2 X)).sup fun k ↦
  (Finset.Icc 1 (Nat.log 2 X)).sup fun n ↦
    refinedCountTriplesStar (i / n : ℝ) (j / n : ℝ) (k / n : ℝ) (2^n) := by

  have : ((Finset.Icc 1 (Nat.log 2 X)).biUnion fun i ↦
    (Finset.Icc 1 (Nat.log 2 X)).biUnion fun j ↦
    (Finset.Icc 1 (Nat.log 2 X)).biUnion fun k ↦
    (Finset.Icc 1 (Nat.log 2 X)).biUnion fun n ↦
      dyadicPoints (i / n : ℝ) (j / n : ℝ) (k / n : ℝ) (2^n)) =
    (Finset.Icc 1 (Nat.log 2 X) ×ˢ
      Finset.Icc 1 (Nat.log 2 X) ×ˢ
      Finset.Icc 1 (Nat.log 2 X) ×ˢ
      Finset.Icc 1 (Nat.log 2 X)).biUnion fun ⟨i, j, k, n⟩ ↦ dyadicPoints (i / n : ℝ) (j / n : ℝ) (k / n : ℝ) (2^n)
    := by
    simp_rw [Finset.product_biUnion]
  rw [this]
  clear this
  apply (Finset.card_biUnion_le ..).trans
  simp only
  apply (sum_le_card_mul_sup _ _).trans
  simp only [Finset.card_product, Nat.card_Icc, add_tsub_cancel_right]
  gcongr
  · apply le_of_eq
    ring
  apply le_of_eq
  simp_rw [refinedCountTriplesStar]
  simp_rw [Finset.sup_product_left]


/- Note: Here we're assuming for now that the implicit constant is 1. -/
theorem countTriples_le_log_pow_mul_sup (μ : ℝ) (X : ℕ) : countTriples μ X ≤
  (Nat.log 2 X)^4 *
  (Finset.Icc 1 (Nat.log 2 X)).sup fun i ↦
  (Finset.Icc 1 (Nat.log 2 X)).sup fun j ↦
  (Finset.Icc 1 (Nat.log 2 X)).sup fun k ↦
  (Finset.Icc 1 (Nat.log 2 X)).sup fun n ↦
    refinedCountTriplesStar (i / n : ℝ) (j / n : ℝ) (k / n : ℝ) (2^n) := by
  simp_rw [countTriples_eq_finset_card, refinedCountTriplesStar]
  apply le_trans _ (card_union_dyadicPoints_le_log_pow_mul_sup X)
  apply Finset.card_le_card
  exact ABCTriples_subset_union_dyadicPoints μ X
