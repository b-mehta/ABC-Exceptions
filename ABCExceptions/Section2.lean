import Mathlib.Algebra.GCDMonoid.Nat
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.StarOrdered
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Radical
import Mathlib.RingTheory.SimpleModule
import Mathlib.RingTheory.UniqueFactorizationDomain.Nat

import ABCExceptions.ForMathlib.RingTheory.Radical

open UniqueFactorizationMonoid

open Classical in
noncomputable def ABCTriples_finset (μ : ℝ) (X : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  (Finset.Icc (1, 1, 1) (X, X, X)).filter fun ⟨a, b, c⟩ ↦
    a.Coprime b ∧ a.Coprime c ∧ b.Coprime c ∧
    a + b = c ∧
    radical (a * b * c) < (c ^ μ : ℝ)

@[simp]
theorem mem_ABCTriples (μ : ℝ) (X : ℕ) (a b c : ℕ) :
  ⟨a, b, c⟩ ∈ ABCTriples_finset μ X ↔
    a.Coprime b ∧ a.Coprime c ∧ b.Coprime c ∧
    a + b = c ∧
    radical (a * b * c) < (c ^ μ : ℝ) ∧
    (a, b, c) ∈ Set.Icc (1, 1, 1) (X, X, X) := by
  simp [ABCTriples_finset]
  aesop

def ABCTriples (μ : ℝ) (X : ℕ) : Set (ℕ × ℕ × ℕ) :=
  { (a, b, c) : ℕ × ℕ × ℕ |
    a.Coprime b ∧ a.Coprime c ∧ b.Coprime c ∧
    a + b = c ∧
    radical (a * b * c) < (c ^ μ : ℝ) ∧
    (a, b, c) ∈ Set.Icc (1, 1, 1) (X, X, X) }

noncomputable def countTriples (μ : ℝ) (X : ℕ) : ℕ :=
  (ABCTriples μ X).ncard

lemma countTriples_eq (μ : ℝ) (X : ℕ) :
    countTriples μ X =
      ({(a, b, c) | 0 < a ∧ 0 < b ∧ 0 < c ∧ a.Coprime b ∧ a.Coprime c ∧ b.Coprime c ∧ a + b = c ∧
         radical (a * b * c) < (c ^ μ : ℝ) } ∩
       Set.Icc (1, 1, 1) (X, X, X)).ncard := by
  rw [countTriples, ABCTriples]
  congr 1
  ext ⟨a, b, c⟩
  simp [and_assoc, ← Prod.mk_one_one]
  aesop

lemma ABCTriples_eq_ABCTriples_finset (μ : ℝ) (X : ℕ) :
    ABCTriples μ X = ABCTriples_finset μ X := by
  ext ⟨a, b, c⟩
  simp [ABCTriples]

lemma countTriples_eq_finset_card (μ : ℝ) (X : ℕ) :
    countTriples μ X = (ABCTriples_finset μ X).card := by
  rw [countTriples, ← Set.ncard_coe_Finset, ABCTriples_eq_ABCTriples_finset]

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

theorem similar_pow_nat_log (x : ℕ) (hx : x ≠ 0) : x ~ 2 ^ Nat.log 2 x := by
  simp [similar]
  norm_cast
  constructor
  · refine Nat.pow_log_le_self 2 hx
  · rw [mul_comm, ← Nat.pow_succ]
    apply (Nat.lt_pow_succ_log_self ..).le
    norm_num

open Classical in
noncomputable def dyadicPoints (α β γ : ℝ) (X : ℕ) : Finset (ℕ × ℕ × ℕ) :=
   (Finset.Icc (0, 0, 0) (2*X, 2*X, 2*X)).filter fun ⟨a, b, c⟩ ↦
      a.Coprime b ∧ a.Coprime c ∧ b.Coprime c ∧
      a + b = c ∧
      (radical a : ℕ) ~ (X ^ α : ℝ) ∧ (radical b : ℕ) ~ (X ^ β : ℝ) ∧ (radical c : ℕ) ~ (X ^ γ : ℝ) ∧
      X / 2 ≤ c ∧ c ≤ X

@[simp]
theorem mem_dyadicPoints (α β γ : ℝ) (X : ℕ) (a b c : ℕ) :
  ⟨a, b, c⟩ ∈ dyadicPoints α β γ X ↔
    a.Coprime b ∧ a.Coprime c ∧ b.Coprime c ∧
      a + b = c ∧
      (radical a : ℕ) ~ (X ^ α : ℝ) ∧ (radical b : ℕ) ~ (X ^ β : ℝ) ∧ (radical c : ℕ) ~ (X ^ γ : ℝ) ∧
      X / 2 ≤ c ∧ c ≤ X := by
  simp only [dyadicPoints, Finset.mem_filter, Finset.mem_Icc, Prod.mk_le_mk,
    and_iff_right_iff_imp, and_imp]
  intro _ _ _ habc _ _ _ hc hc'
  simp only [zero_le, and_self, true_and]
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
    rw [dvd_radical_iff_of_irreducible hp.1.prime.irreducible (by omega)]
    exact hp.2

open Classical in
private noncomputable def indexSet (μ : ℝ) (X : ℕ) : Finset (ℕ × ℕ × ℕ × ℕ) :=
  (Finset.Icc 0 (Nat.log 2 X)) ×ˢ (Finset.Icc 0 (Nat.log 2 X)) ×ˢ
  (Finset.Icc 0 (Nat.log 2 X)) ×ˢ (Finset.Icc 1 (Nat.log 2 X+1)) |>.filter fun ⟨i, j, k, n⟩ ↦
    i + j + k ≤ μ * n

private theorem card_indexSet_le (μ : ℝ) (X : ℕ) :
    (indexSet μ X).card ≤ (Nat.log 2 X + 1)^4 := by
  apply (Finset.card_filter_le ..).trans
  simp
  apply le_of_eq
  ring

@[simp]
private theorem mem_indexSet (μ : ℝ) (X : ℕ) (i j k n : ℕ) :
    ⟨i, j, k, n⟩ ∈ indexSet μ X ↔
      i ≤ Nat.log 2 X ∧ j ≤ Nat.log 2 X ∧ k ≤ Nat.log 2 X ∧ 1 ≤ n ∧ n ≤ Nat.log 2 X + 1 ∧ i + j + k ≤ μ * n := by
  simp [indexSet]
  norm_cast
  aesop

theorem Nat.Coprime.isRelPrime (a b : ℕ) (h : a.Coprime b) : IsRelPrime a b := by
  rw [← Nat.coprime_iff_isRelPrime]
  exact h

theorem ABCTriples_subset_union_dyadicPoints (μ : ℝ) (X : ℕ) :
    ABCTriples_finset μ X ⊆
      (indexSet μ X).biUnion fun ⟨i, j, k, n⟩ ↦
        dyadicPoints (i / n : ℝ) (j / n : ℝ) (k / n : ℝ) (2^n) := by
  rintro ⟨a, b, c⟩
  simp only [mem_ABCTriples, Set.mem_Icc, Prod.mk_le_mk, Finset.mem_biUnion, mem_dyadicPoints,
    Nat.cast_pow, Nat.cast_ofNat, Prod.exists, mem_indexSet, and_imp]
  intro hab hac hbc habc hrad h1a h1b h1c haX hbX hcX
  have hμ : 0 ≤ μ := by
    by_contra hμ
    have : (1:ℝ) ≤ (radical (a * b * c) : ℕ) := by
      norm_cast
      have := radical_ne_zero (a * b * c)
      omega
    have : (c : ℝ) ^ μ < 1 := by
      apply Real.rpow_lt_one_of_one_lt_of_neg
      · norm_cast
        omega
      · linarith
    linarith
  have h {a : ℕ} (h2a : 2 ≤ a) (haX : a ≤ X) : 1 ≤ Nat.log 2 a ∧ Nat.log 2 a ≤ Nat.log 2 X := by
    constructor
    · apply Nat.le_log_of_pow_le (by norm_num)
      simp [h2a]
    · apply Nat.log_mono_right haX
  have {a : ℕ} (ha : 1 ≤ a) (haX : a ≤ X) : Nat.log 2 (radical a) ≤ Nat.log 2 X := by
    apply Nat.log_mono_right ((Nat.radical_le_self (by omega)).trans haX)
  let n := Nat.log 2 c + 1
  refine ⟨Nat.log 2 (radical a), Nat.log 2 (radical b), Nat.log 2 (radical c), n,
  ⟨this h1a haX, this h1b hbX, this h1c hcX, by omega, ?_, ?_⟩, hab, hac, hbc, habc, ?_⟩
  · simp [n, Nat.log_mono_right hcX]
  · -- Here we prove that α + β + γ ≤ μ
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
          exact radical_ne_zero _
      _ ≤ ↑c ^ μ := by
        exact_mod_cast hrad.le
      _ ≤ (2:ℝ) ^ (n * μ) := by
        norm_cast
        rw [Real.rpow_natCast_mul (by norm_num)]
        gcongr
        norm_cast
        simp [n]
        apply le_of_lt
        rw [Nat.lt_pow_iff_log_lt]
        · omega
        · norm_num
        · omega
    rw [← Real.rpow_le_rpow_left_iff (show 1 < (2 : ℝ) by norm_num)]
    norm_cast at this ⊢
    convert this using 1
    ring_nf
  have {a : ℕ} : ((2:ℝ) ^ n) ^ ((↑(Nat.log 2 (radical a))) / ↑(n)  : ℝ) =
      2^(Nat.log 2 (radical a)) := by
    rw [← Real.rpow_natCast_mul (by norm_num)]
    have : ↑(n) * (↑(Nat.log 2 (radical a)) / ↑(n):ℝ) = Nat.log 2 (radical a) := by
      rw [mul_div_cancel₀]
      simp [n]
      norm_cast
    rw [this]
    simp
  have hc2 : 2 ≤ c := by
    omega
  simp_rw [this]
  have radical_similar {a : ℕ} :  (radical a : ℕ) ~ 2 ^ (Nat.log 2 (radical a)) := by
    simp [similar]
    norm_cast
    constructor
    · apply Nat.pow_log_le_self
      exact radical_ne_zero a
    · rw [mul_comm, ← Nat.pow_succ]
      apply (Nat.lt_pow_succ_log_self ..).le
      norm_num
  refine ⟨radical_similar, radical_similar, radical_similar, ?_⟩
  simp [n, similar, Nat.pow_succ]
  refine ⟨?_, ?_⟩
  · apply Nat.pow_log_le_self
    omega
  · rw [← Nat.pow_succ]
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

theorem card_union_dyadicPoints_le_log_pow_mul_sup (μ : ℝ) (X : ℕ) :
  ((indexSet μ X).biUnion fun ⟨i, j, k, n⟩ ↦
    dyadicPoints (i / n : ℝ) (j / n : ℝ) (k / n : ℝ) (2^n)).card ≤
  (Nat.log 2 X+1)^4 * (indexSet μ X).sup fun ⟨i, j, k, n⟩ ↦
    refinedCountTriplesStar (i / n : ℝ) (j / n : ℝ) (k / n : ℝ) (2^n) := by
  apply (Finset.card_biUnion_le ..).trans
  simp only
  apply (sum_le_card_mul_sup _ _).trans
  gcongr
  · apply card_indexSet_le
  · rfl

noncomputable def dyadicSupBound (μ : ℝ) (X : ℕ) : ℕ :=
  (indexSet μ X).sup fun ⟨i, j, k, n⟩ ↦
    refinedCountTriplesStar (i / n : ℝ) (j / n : ℝ) (k / n : ℝ) (2^n)

theorem countTriples_le_log_pow_mul_sup (μ : ℝ) (X : ℕ) : countTriples μ X ≤
  (Nat.log 2 X+1)^4 * dyadicSupBound μ X := by
  simp_rw [countTriples_eq_finset_card, dyadicSupBound, refinedCountTriplesStar]
  apply le_trans _ (card_union_dyadicPoints_le_log_pow_mul_sup μ X)
  apply Finset.card_le_card
  exact ABCTriples_subset_union_dyadicPoints μ X

theorem Nat.log_isBigO_log (b : ℕ) :
    (fun x : ℕ ↦ (Nat.log b x : ℝ)) =O[atTop] (fun x : ℕ ↦ Real.log x) := by
  rw [isBigO_iff]
  use (Real.log b)⁻¹
  filter_upwards with x
  simp only [RCLike.norm_natCast, Real.norm_eq_abs]
  rw [abs_of_nonneg]
  apply Real.natLog_le_logb _ _ |>.trans
  simp [← Real.log_div_log]
  apply le_of_eq
  · ring
  positivity

theorem countTriples_isBigO_dyadicSup :
    (fun ⟨X, μ⟩ ↦ (countTriples μ X : ℝ)) =O[atTop ×ˢ ⊤]
      (fun ⟨X, μ⟩ ↦ (Real.log X)^4 * dyadicSupBound μ X) := by
  trans fun ⟨X, μ⟩ ↦ (Nat.log 2 X+1:ℝ)^4 * dyadicSupBound μ X
  · simp only
    apply IsBigO.of_norm_le
    simp only [Real.norm_natCast, Prod.forall]
    exact_mod_cast fun a b ↦ countTriples_le_log_pow_mul_sup b a
  · apply IsBigO.mul _ (isBigO_refl ..)
    apply Asymptotics.IsBigO.comp_fst (g := fun x : ℕ ↦ (Real.log x)^4) (f := fun x ↦ (Nat.log 2 x+1:ℝ)^4)
    apply IsBigO.pow
    apply IsBigO.add
    · exact Nat.log_isBigO_log 2
    apply IsLittleO.isBigO
    apply Real.isLittleO_const_log_atTop.natCast_atTop

def dyadicTuples {d : ℕ} (X : Fin d → ℕ) : Finset (Fin d → ℕ) :=
  Fintype.piFinset (fun i ↦ Finset.Icc (X i) (2 * X i))

@[simp]
theorem mem_dyadicTuples {d : ℕ} (X x : Fin d → ℕ) :
  x ∈ dyadicTuples X ↔ ∀ i, x i ~ X i := by
  simp [dyadicTuples, similar]
  norm_cast

open Classical in
noncomputable def B_finset (d : ℕ) (C : Fin 3 → ℕ) (X Y Z : Fin d → ℕ) :
  Finset ((Fin d → ℕ) × (Fin d → ℕ) × (Fin d → ℕ) × (Fin 3 → ℕ)) :=
  ((dyadicTuples X) ×ˢ (dyadicTuples Y) ×ˢ (dyadicTuples Z) ×ˢ {C}).filter fun ⟨x, y, z, c⟩ ↦
    c 0 * ∏ i, (x i)^(i:ℕ) + c 1 * ∏ i, (y i)^(i:ℕ) = c 2 * ∏ i, (z i)^(i:ℕ) ∧
    Nat.gcd (c 0 * ∏ i, (x i)) (c 1 * ∏ i, (y i)) = 1 ∧
    Nat.gcd (c 0 * ∏ i, (x i)) (c 2 * ∏ i, (z i)) = 1 ∧
    Nat.gcd (c 1 * ∏ i, (y i)) (c 2 * ∏ i, (z i)) = 1

theorem mem_B_finset (d : ℕ) (C : Fin 3 → ℕ) (X Y Z : Fin d → ℕ) (x y z : Fin d → ℕ) (c : Fin 3 → ℕ) :
  (x, y, z, c) ∈ B_finset d C X Y Z ↔
    C = c ∧
    (∀ i, x i ~ X i) ∧ (∀ i, y i ~ Y i) ∧ (∀ i, z i ~ Z i) ∧
    c 0 * ∏ i, (x i)^(i:ℕ) + c 1 * ∏ i, (y i)^(i:ℕ) = c 2 * ∏ i, (z i)^(i:ℕ) ∧
    Nat.gcd (c 0 * ∏ i, (x i)) (c 1 * ∏ i, (y i)) = 1 ∧
    Nat.gcd (c 0 * ∏ i, (x i)) (c 2 * ∏ i, (z i)) = 1 ∧
    Nat.gcd (c 1 * ∏ i, (y i)) (c 2 * ∏ i, (z i)) = 1 := by
  simp only [B_finset, Fin.isValue, Finset.mem_singleton, Finset.mem_filter, Finset.mem_product,
    mem_dyadicTuples, Function.Embedding.coeFn_mk, Prod.mk.injEq]
  tauto

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

theorem Finset.Ico_union_Icc_eq_Icc {α : Type*} [LinearOrder α] [LocallyFiniteOrder α] (a b c : α)
  (hab : a ≤ b) (hbc : b ≤ c) :
    Finset.Ico a b ∪ Finset.Icc b c = Finset.Icc a c := by
  ext x
  simp
  constructor
  · rintro (⟨hax, hxb⟩ | ⟨hbx, hxc⟩)
    · refine ⟨hax, hxb.le.trans hbc⟩
    · refine ⟨hab.trans hbx, hxc⟩
  rintro ⟨hax, hxc⟩
  by_cases hxb : x < b
  · left
    refine ⟨hax, hxb⟩
  right
  refine ⟨le_of_not_gt hxb, hxc⟩

theorem exists_nice_factorization {ε : ℝ} (hε_pos : 0 < ε) (hε : ε < 1/2) (d : ℕ) (hd : d = ⌊5/2 * ε⁻¹^2⌋₊) {n X : ℕ} (h2n : 2 ≤ n) (hnX : n ≤ X) :
  ∃ (x : (Fin d) → ℕ), ∃ c : ℕ,
    n = c * ∏ j, x j ^ (j:ℕ) ∧
    c ≤ (X:ℝ)^(ε) ∧
    (∀ i j, i ≠ j → Nat.gcd (x i) (x j) = 1) ∧
    (X:ℝ)^(- ε) * ∏ j, x j ≤ (radical n : ℕ) ∧ (radical n : ℕ) ≤ (X:ℝ)^(ε) * ∏ j, x j := by

  have two_lt_eps_inv : 2 < ε⁻¹ := by
    rw [← inv_inv 2]
    gcongr
    linarith only [hε]

  let K := ⌈ε⁻¹⌉₊
  set M := ⌊5/2 * ε⁻¹^2⌋₊
  have hK_pos : 0 < K := by
    rw [Nat.ceil_pos]
    simp [hε_pos]

  have hM_pos : 0 < M := by
    rw [Nat.floor_pos]
    nlinarith only [two_lt_eps_inv]

  have hM_ne_zero : NeZero M := by
    simp_rw [M, neZero_iff]
    apply ne_of_gt hM_pos

  have hKM : K < M := by
    simp_rw [K, M]
    rw [Nat.lt_iff_add_one_le]
    apply Nat.ceil_lt_floor
    · positivity
    nlinarith

  have hK_div_M : (K / M : ℝ) ≤ ε := by
    rw [div_le_iff₀ (mod_cast hM_pos)]
    simp only [K, M]
    calc
      _ ≤ ε⁻¹ + 1 := by
        apply le_of_lt
        apply Nat.ceil_lt_add_one
        positivity
      _ ≤ 5 / 2 * ε⁻¹ - ε := by
        linarith
      _ = ε * (5/2 * ε⁻¹^2 - 1) := by
        field_simp
        ring
      _ ≤ _ := by
        gcongr
        apply le_of_lt
        apply Nat.sub_one_lt_floor

  let y (j : ℕ) := ∏ p ∈ {p ∈ n.primeFactors | n.factorization p = j}, p

  have hy_pos (j : ℕ) : 0 < y j := by
    apply Finset.prod_pos
    simp only [Finset.mem_filter, Nat.mem_primeFactors, ne_eq, and_imp, y]
    intro p hp _ _ _
    exact hp.pos

  have prod_y_pow_eq_n_subset {s : Finset ℕ} (hs : ∀ p, p.Prime → p ∣ n → n.factorization p ∈ s) :
      ∏ m ∈ s, y m ^ m = n := by
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
  have prod_y_pow_eq_n : ∏ m ∈ (Finset.range M) ∪ (Finset.Icc M n), y m ^ m = n := by
    apply prod_y_pow_eq_n_subset
    intro p hp hpn
    simp only [Finset.mem_union, Finset.mem_range, Finset.mem_Icc]
    have : n.factorization p ≤ n := by
      apply Nat.factorization_le_right p n hp
    have : n.factorization p < M ∨ M ≤ n.factorization p := by
      exact Nat.lt_or_ge (n.factorization p) M
    tauto

  have p_dvd_y_iff (i : ℕ) (p : ℕ) (hp : p.Prime) : p ∣ y i → n.factorization p = i := by
    rw [Prime.dvd_finset_prod_iff hp.prime]
    simp only [Finset.mem_filter, Nat.mem_primeFactors, ne_eq]
    rintro ⟨q, ⟨⟨hq, _⟩, rfl⟩, hpq⟩
    congr
    rw [eq_comm, ← hq.dvd_iff_eq hp.ne_one]
    exact hpq
  have hy_cop (i j : ℕ) (hij : i ≠ j) : Nat.Coprime (y i) (y j) := by
    apply Nat.coprime_of_dvd
    intro p hp hpi hpj
    apply p_dvd_y_iff _ _ hp at hpi
    apply p_dvd_y_iff _ _ hp at hpj
    subst hpi hpj
    exact hij rfl

  let x (j : Fin M) : ℕ :=
    y j * if j = K then (∏ m ∈ Finset.Icc M n, y m ^ (m / K)) else 1

  have x_zero : x 0 = 1 := by
    sorry


  have x_pairwise_coprime (i j : Fin M) (hij : i ≠ j) : Nat.gcd (x i) (x j) = 1 := by
    have hij' : i.val ≠ j.val := by
      simp [Fin.val_inj, hij]
    simp_rw [x]
    rw [← Nat.coprime_iff_gcd_eq_one]
    split_ifs with hik hjk
    · rw [← hik] at hjk
      exact (hij.symm hjk).elim
    · rw [Nat.coprime_mul_iff_left, mul_one]
      refine ⟨hy_cop _ _ hij', ?_⟩
      rw [Nat.coprime_prod_left_iff]
      simp only [Finset.mem_Icc, and_imp, x]
      intro m hMm hmn
      apply Nat.Coprime.pow_left
      apply hy_cop
      omega
    · /- deduce from above? -/
      sorry
    · simp_rw [mul_one]
      apply hy_cop i j hij'

  let c : ℕ := ∏ m ∈ Finset.Icc M n, y m ^ (m % K)

  have c_mul_prod_x_eq_n : c * ∏ j, x j ^ (j : ℕ) = n := by
    simp_rw [c, x]
    simp_rw [mul_pow, Finset.prod_mul_distrib]
    simp only [ite_pow, one_pow]
    simp only [Finset.prod_ite_eq', Finset.mem_univ, ↓reduceIte, Fin.val_natCast]
    rw [Fin.prod_univ_eq_prod_range (fun i ↦ y i ^ i)]
    rw [mul_comm, mul_assoc, ← Finset.prod_pow, ← Finset.prod_mul_distrib]
    simp_rw [← pow_mul, ← pow_add, Nat.mod_eq_of_lt hKM, mul_comm _ K, Nat.div_add_mod]
    conv => rhs; rw [← prod_y_pow_eq_n]
    rw [← Finset.prod_union]
    refine Finset.disjoint_left.mpr ?_
    simp +contextual

  have : ∏ m ∈ Finset.Icc M n, y m ≤ (X:ℝ) ^ (M⁻¹ : ℝ) := calc
    _ ≤ (∏ m ∈ Finset.Icc M n, y m ^ m : ℝ) ^ (M⁻¹ : ℝ) := by
      rw [← Real.finset_prod_rpow]
      · push_cast
        apply Finset.prod_le_prod
        · intros; positivity
        simp only [Finset.mem_Icc, and_imp]
        intro i hMi hin
        conv => lhs; rw [← Real.rpow_one (y i : ℝ)]
        rw [← Real.rpow_natCast_mul (by simp)]
        gcongr
        · norm_cast
          apply hy_pos
        · rw [le_mul_inv_iff₀]
          · simp [hMi]
          · simp [hM_pos]
      intros; positivity
    _ ≤ (n:ℝ) ^ (M⁻¹ : ℝ) := by
      gcongr
      norm_cast
      conv => rhs; rw [← prod_y_pow_eq_n]
      apply Finset.prod_le_prod_of_subset_of_one_le'
      · simp
      simp only [Finset.mem_union, Finset.mem_range, Finset.mem_Icc, not_and, not_le, y]
      intro i hi _
      erw [Nat.succ_le]
      simp only [Nat.zero_eq, M, K, x, c]
      by_cases hi0 : i = 0
      · simp [hi0]
      apply pow_pos (hy_pos ..)
    _ ≤ _ := by
      gcongr


  have c_le_X_pow := calc
    c ≤ ∏ m ∈ Finset.Icc M n, (y m : ℝ) ^ K := by
      simp_rw [c]
      push_cast
      apply Finset.prod_le_prod
      · intros; positivity
      simp only [Finset.mem_Icc, and_imp]
      intro x hMx hxn
      gcongr
      · simp only [Nat.one_le_cast, *]
        apply hy_pos
      · apply (Nat.mod_lt ..).le
        exact hK_pos
    _ ≤ (X ^ (M⁻¹ : ℝ)) ^ (K:ℝ) := by
      simp only [Real.rpow_natCast]
      rw [Finset.prod_pow]
      gcongr
      exact_mod_cast this
    _ = (X:ℝ) ^ (K/M : ℝ) := by
      rw [← Real.rpow_mul]
      ring_nf
      positivity
    _ ≤ X ^ ε := by
      gcongr
      · norm_cast
        linarith

  have radical_le_X_pow_mul_prod := calc
    (radical n : ℕ)  ≤ ((radical c : ℕ) : ℝ) * radical (∏ j, x j ^ j.val : ℕ) := by
      norm_cast
      apply Nat.le_of_dvd
      · sorry
      rw [← c_mul_prod_x_eq_n]
      apply radical_mul_dvd
    _ ≤ ((radical c : ℕ) : ℝ)* ∏ j, (radical (x j ^ j.val) : ℕ) := by
      gcongr
      apply Nat.le_of_dvd
      · apply Finset.prod_pos
        intro i _
        apply Nat.pos_of_ne_zero (radical_ne_zero _)
      apply radical_prod_dvd
    _ = ((radical c : ℕ) : ℝ)* ∏ j, (radical (x j) : ℕ) := by
      congr 3 with j
      by_cases hj : (j : ℕ) = 0
      · simp [hj]
        have : j = 0 := by
          rw [← Fin.val_inj]
          simp [hj]
        simp [this, x_zero]
      rw [radical_pow]
      omega
    _ ≤ (X : ℝ)^ε * ∏ j, x j := by
      gcongr
      · calc
          _ ≤ ↑c := by
            norm_cast
            apply Nat.le_of_dvd
            · sorry
            apply radical_dvd_self
          _ ≤ (_:ℝ) := by
            apply c_le_X_pow
      apply Nat.le_of_dvd
      · sorry
      apply radical_dvd_self

  have x_K_le_X_pow : x K ≤ (X : ℝ) ^ ε := by
    sorry

  have X_pow_mul_prod_le_radical := calc
    (X : ℝ) ^ (-ε) * ∏ j, x j ≤ ∏ (j : Fin M), if j ≠ K then x j else 1 := by
      sorry
    _ = ∏ j : Fin M, if j.val ≠ K then y j else 1 := by
      norm_cast
      simp_rw [← Finset.prod_filter]
      apply Finset.prod_congr
      · ext j; simp
        rw [@not_iff_not]
        sorry
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      intro j h
      simp only [x, h]
      sorry
    _ = ∏ m ∈ Finset.range M with m ≠ K, y m := by
      norm_cast
      rw [Finset.prod_filter, Fin.prod_univ_eq_prod_range (fun j ↦ if ¬ j = K then y j else 1) M]
    _ ≤ ∏ m ∈ Finset.range M ∪ Finset.Icc M n, y m := by
      norm_cast
      apply Finset.prod_le_prod_of_subset_of_one_le'
      · intro x;
        simp
        intro hxM hxK
        sorry
      · simp only [Finset.mem_union, Finset.mem_range, Finset.mem_Icc, Finset.mem_filter, not_and,
        Decidable.not_not]
        intro i _ _
        apply hy_pos
    _ = (radical n : ℕ) := by
      norm_cast
      sorry
  subst hd
  refine ⟨x, c, c_mul_prod_x_eq_n.symm, c_le_X_pow, x_pairwise_coprime, X_pow_mul_prod_le_radical, radical_le_X_pow_mul_prod⟩


def powersLE (a : ℕ) (x : ℕ) : Finset ℕ :=
  (Finset.Icc 0 (Nat.log a x)).image fun n ↦ a^n

@[simp]
theorem mem_powersLE (a x n : ℕ) :
    n ∈ powersLE a x ↔ n ≤ x ∧ ∃ k, n = a^k := by
  simp [powersLE]
  sorry

-- surjective map S*_α β γ (X) <- ⋃_{c, X, Y ,Z} B (c, X, Y, Z)
def B_to_triple {d : ℕ} : (Fin d → ℕ) × (Fin d → ℕ) × (Fin d → ℕ) × (Fin 3 → ℕ) → ℕ × ℕ × ℕ :=
  fun ⟨X, Y, Z, c⟩ ↦
    ⟨c 0 * ∏ i, X i ^ (i : ℕ), c 1 * ∏ i, Y i ^ (i : ℕ), c 2 * ∏ i, Z i ^ (i : ℕ)⟩

open Classical in
noncomputable def indexSet' (α β γ : ℝ) (d : ℕ) (x : ℕ) (ε : ℝ) :
    Finset ((Fin d → ℕ) × (Fin d → ℕ) × (Fin d → ℕ)) :=
  (Fintype.piFinset (fun _ ↦ Finset.Icc 0 (Nat.log 2 x))) ×ˢ
  (Fintype.piFinset (fun _ ↦ Finset.Icc 0 (Nat.log 2 x))) ×ˢ
  (Fintype.piFinset (fun _ ↦ Finset.Icc 0 (Nat.log 2 x))) |>.filter fun ⟨r, s ,t⟩ ↦
    (x:ℝ) ^ (α - ε) ≤ 2^d * ∏ i, 2 ^ r i ∧ ∏ i, 2 ^ r i ≤ 2 * (x:ℝ) ^ (α + ε) ∧
    (x:ℝ) ^ (β - ε) ≤ 2^d * ∏ i, 2 ^ s i ∧ ∏ i, 2 ^ s i ≤ 2 * (x:ℝ) ^ (β + ε) ∧
    (x:ℝ) ^ (γ - ε) ≤ 2^d * ∏ i, 2 ^ t i ∧ ∏ i, 2 ^ t i ≤ 2 * (x:ℝ) ^ (γ + ε) ∧
    ∏ i, (2 ^ r i)^(i:ℕ) ≤ x ∧
    ∏ i, (2 ^ s i)^(i:ℕ) ≤ x ∧
    ∏ i, (2 ^ t i)^(i:ℕ) ≤ x ∧
    (x : ℝ)^(1-ε^2) ≤ 2^(Nat.choose d 2) * ∏ i, (2 ^ t i)^(i : ℕ)

theorem card_indexSet'_le (α β γ : ℝ) (d : ℕ) (x : ℕ) (ε : ℝ)  :
    (indexSet' α β γ d x ε).card ≤ (Nat.log 2 x + 1)^(3*d) := by
  rw [indexSet']
  apply Finset.card_filter_le .. |>.trans
  simp
  apply le_of_eq
  ring

theorem indexSet'_nonempty (α β γ : ℝ) (d : ℕ) (x : ℕ) (ε : ℝ) :
    Finset.Nonempty (indexSet' α β γ d x ε) := by
  have : NeZero d := by
    sorry
  let fst (n : ℕ) : Fin d → ℕ := fun i ↦ if i = 0 then n else 0
  /- This is incorrect. Some care needs to be taken to get the lower bound on ∏ Z i ^ i -/
  refine ⟨⟨fst (Nat.log 2 ⌊(x:ℝ) ^ (α + ε)⌋₊), fst (Nat.log 2 ⌊(x:ℝ) ^ (β + ε)⌋₊), fst (Nat.log 2 ⌊(x:ℝ) ^ (γ + ε)⌋₊)⟩, ?_⟩
  simp [fst, indexSet']
  sorry

noncomputable def BUnion (α β γ : ℝ) {d : ℕ} (x : ℕ) (ε : ℝ) :
    Finset ((Fin d → ℕ) × (Fin d → ℕ) × (Fin d → ℕ) × (Fin 3 → ℕ)) :=
  (indexSet' α β γ d x ε).sup fun ⟨r, s, t⟩ ↦
  (Fintype.piFinset (fun _ ↦ Finset.Icc 0 ⌊(x:ℝ)^(ε/4)⌋₊) : Finset (Fin 3 → ℕ)).sup fun c ↦
    B_finset d c (fun i ↦ 2^r i) (fun i ↦ 2^s i) (fun i ↦ 2^t i)

theorem B_to_triple_surjOn {α β γ : ℝ}  (x : ℕ) (ε : ℝ) (hε_pos : 0 < ε) (hε : ε < 1/2) {d : ℕ} (hd : d = ⌊5 / 2 * (ε ^ 2 / 2)⁻¹ ^ 2⌋₊) :
    Set.SurjOn (B_to_triple (d := d)) (BUnion α β γ x ε).toSet (dyadicPoints α β γ x).toSet := by
  intro ⟨a, b, c⟩
  simp only [Finset.mem_coe, mem_dyadicPoints, BUnion, Set.mem_image, Finset.mem_sup,
    Fintype.mem_piFinset, Finset.mem_Icc, zero_le, true_and, Prod.exists, and_imp]
  intro hab hac hbc habc hrada hradb hradc hxc hcx
  have h2a : 2 ≤ a := by sorry
  have h2b : 2 ≤ b := by sorry
  have h2c : 2 ≤ c := by omega
  have hε_sq : ε^2/2 < 1/2 := by
    nlinarith
  obtain ⟨u, c₀, a_eq_c_mul_prod, c₀_le_pow, hu_cop, le_rad_a, rad_a_le⟩ := exists_nice_factorization (ε := ε^2/2) (by positivity) hε_sq d hd h2a (show a ≤ x by linarith)
  obtain ⟨v, c₁, b_eq_c_mul_prod, c₁_le_pow, hv_cop, le_rad_b, rad_b_le⟩ := exists_nice_factorization (ε := ε^2/2) (by positivity) hε_sq d hd h2b (show b ≤ x by linarith)
  obtain ⟨w, c₂, c_eq_c_mul_prod, c₂_le_pow, hw_cop, le_rad_c, rad_c_le⟩ := exists_nice_factorization (ε := ε^2/2) (by positivity) hε_sq d hd h2c (show c ≤ x by linarith)
  let c' : Fin 3 → ℕ := ![c₀, c₁, c₂]
  refine ⟨u, v, w, c', ?_, ?easy⟩
  case easy =>
    simp [B_to_triple, c']
    refine ⟨a_eq_c_mul_prod.symm, b_eq_c_mul_prod.symm, c_eq_c_mul_prod.symm⟩
  refine ⟨fun i ↦ Nat.log 2 (u i), fun i ↦ Nat.log 2 (v i), fun i ↦ Nat.log 2 (w i), ?_, ?_⟩
  · simp [indexSet']
    sorry
  · use c'
    simp only [mem_B_finset, Nat.cast_pow, Nat.cast_ofNat, Fin.isValue, true_and, c']
    sorry


theorem refinedCountTriplesStar_le_card_BUnion (α β γ : ℝ) {d : ℕ} (x : ℕ) (ε : ℝ) :
    refinedCountTriplesStar α β γ x ≤ (BUnion α β γ x ε (d := d)).card := by
  stop
  rw [refinedCountTriplesStar]
  apply Finset.card_le_card_of_surjOn _ (B_to_triple_surjOn ..)



def const (ε : ℝ) : ℝ := sorry

noncomputable def d (ε : ℝ) : ℕ := ⌊5 / 2 * (ε ^ 2 / 2)⁻¹ ^ 2⌋₊

theorem refinedCountTriplesStar_isBigO_B
  {α β γ : ℝ}
  (hα_pos : 0 < α) (hβ_pos : 0 < β) (hγ_pos : 0 < γ)
  (hα1 : α ≤ 1) (hβ1 : β ≤ 1) (hγ1 : γ ≤ 1)
  {x : ℕ} (h2X : 2 ≤ x) {ε : ℝ} (hε_pos : 0 < ε) :
  ∃ X Y Z : Fin (d ε) → ℕ,
    (x:ℝ)^(α - ε) ≤ 2 ^ d ε * ∏ j, X j ∧ ∏ j, X j ≤ 2 * (x : ℝ) ^ (α + ε) ∧
    (x:ℝ)^(β - ε) ≤ 2 ^ d ε * ∏ j, Y j ∧ ∏ j, Y j ≤ 2 * (x : ℝ) ^ (β + ε) ∧
    (x:ℝ)^(γ - ε) ≤ 2 ^ d ε * ∏ j, Z j ∧ ∏ j, Z j ≤ 2 * (x : ℝ) ^ (γ + ε) ∧
    ∏ i, X i ^ (i : ℕ) ≤ x ∧
    ∏ i, Y i ^ (i : ℕ) ≤ x ∧
    ∏ i, Z i ^ (i : ℕ) ≤ x ∧
    (x : ℝ) ^ (1 - ε^2) ≤ 2^(Nat.choose (d ε) 2) * ∏ i, Z i ^ (i : ℕ) ∧
    ∃ c : Fin 3 → ℕ,
    (∀ i, 1 ≤ c i) ∧
    (∀ i, (c i : ℝ) ≤ (x : ℝ) ^ ε) ∧
    refinedCountTriplesStar α β γ x ≤ const ε * (x : ℝ) ^ ε * B (d ε) c X Y Z := by
  have := refinedCountTriplesStar_le_card_BUnion α β γ (d := d ε) x ε
  simp_rw [BUnion, Finset.sup_eq_biUnion] at this
  have := this.trans Finset.card_biUnion_le |>.trans (sum_le_card_mul_sup ..)
  obtain ⟨⟨u, v, w⟩, h_mem, hsup_eq⟩ := Finset.exists_mem_eq_sup _ (indexSet'_nonempty α β γ (d ε) x ε) fun (a : (Fin (d ε) → ℕ) × (Fin (d ε) → ℕ) × (Fin (d ε) → ℕ)) ↦
      ((Fintype.piFinset fun x_1 ↦ Finset.Icc 0 ⌊(x:ℝ) ^ (ε / 4)⌋₊).biUnion fun c ↦
          B_finset (d ε) c (fun i ↦ 2 ^ a.1 i) (fun i ↦ 2 ^ a.2.1 i) fun i ↦ 2 ^ a.2.2 i).card
  rw [hsup_eq] at this
  clear hsup_eq
  simp only [indexSet', Finset.mem_filter, Finset.mem_product, Fintype.mem_piFinset, Finset.mem_Icc,
    zero_le, true_and] at h_mem
  refine ⟨(fun i ↦ 2 ^ u i), (fun i ↦ 2 ^ v i), (fun i ↦ 2 ^ w i), ?_⟩
  obtain ⟨_, hxu, hux, hxv, hvx, hxw, hwx, hux', hvx', hwx', hxw'⟩ := h_mem
  refine ⟨mod_cast hxu, mod_cast hux, mod_cast hxv, mod_cast hvx, mod_cast hxw, mod_cast hwx, hux', hvx', hwx', mod_cast hxw', ?_⟩

  sorry
