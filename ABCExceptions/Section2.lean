import Mathlib.Algebra.GCDMonoid.Nat
import Mathlib.Analysis.SpecialFunctions.Log.Base
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

theorem exists_nice_factorization {ε : ℝ} (hε_pos : 0 < ε) (hε : ε < 1/2) {n X : ℕ} (h2n : 2 ≤ n) (hnX : n ≤ X) :
  ∃ (x : (Fin ⌊5/2 * ε⁻¹^2⌋₊) → ℕ), ∃ c : ℕ,
    n = c * ∏ j, x j ^ (j:ℕ) ∧
    c ≤ (X:ℝ)^(ε) ∧
    (∀ i j, i ≠ j → Nat.gcd (x i) (x j) = 1) ∧
    (X:ℝ)^(- ε) * ∏ j, x j ≤ (radical n : ℕ) ∧ (radical n : ℕ) ≤ (X:ℝ)^(ε) * ∏ j, x j := by

  let K := ⌈ε⁻¹⌉₊
  set M := ⌊5/2 * ε⁻¹^2⌋₊
  let y (j : ℕ) := ∏ p ∈ {p ∈ n.primeFactors | n.factorization p = j}, p
  /- This is just the fiberwise product along the factorization. -/
  have : ∏ m ∈ Finset.Icc 1 n, y m ^ m = n := by
    simp_rw [y]
    conv =>
      rhs
      rw [← Nat.factorization_prod_pow_eq_self (show n ≠ 0 by omega)]
    simp_rw [← Finset.prod_pow]
    rw [Nat.prod_factorization_eq_prod_primeFactors]
    convert Finset.prod_fiberwise_of_maps_to  (f := fun p ↦ p ^ n.factorization p)
      (g := n.factorization) (s := n.primeFactors) (t := Finset.Icc 1 n) ?_ using 1
    · apply Finset.prod_congr rfl
      intro k hk
      apply Finset.prod_congr rfl
      simp only [Finset.mem_filter, Nat.mem_primeFactors, ne_eq, and_imp, y]
      rintro _ _ _ _ rfl
      rfl
    · simp only [Nat.mem_primeFactors, ne_eq, Finset.mem_Icc, and_imp, y]
      intro p hp hpn hn'
      refine ⟨(Nat.Prime.dvd_iff_one_le_factorization hp hn').mp hpn, Nat.factorization_le_right p n hp⟩
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

  have x_pairwise_coprime (i j : Fin M) (hij : i ≠ j) : Nat.gcd (x i) (x j) = 1 := by
    have hij' : i.val ≠ j.val := by
      simp [Fin.val_inj, hij]
    simp_rw [x]
    rw [← Nat.coprime_iff_gcd_eq_one]
    split_ifs with hik hjk
    · rw [← hik] at hjk
      exact (hij'.symm hjk).elim
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
    have hM_ne_zero : NeZero M := by
      sorry
    have hKM : K < M := by
      sorry
    have {x : Fin M} : x.val = K ↔ x = (K : Fin M) := by
      constructor
      · intro hxK
        refine Fin.eq_of_val_eq ?_
        simp only [Fin.val_natCast, *]
        rw [Nat.mod_eq_of_lt hKM]
      · intro hxK
        refine (Fin.eq_mk_iff_val_eq (hk := hKM) ).mp ?_
        rw [hxK]
        refine Fin.eq_mk_iff_val_eq.mpr ?_
        simp
        rw [Nat.mod_eq_of_lt hKM]
    simp_rw [this]
    simp only [Finset.prod_ite_eq', Finset.mem_univ, ↓reduceIte, Fin.val_natCast]
    rw [Fin.prod_univ_eq_prod_range (fun i ↦ y i ^ i)]
    rw [mul_comm, mul_assoc, ← Finset.prod_pow, ← Finset.prod_mul_distrib]
    simp_rw [← pow_mul, ← pow_add, Nat.mod_eq_of_lt hKM, mul_comm _ K, Nat.div_add_mod]
    rw [← Finset.prod_union]
    · sorry
    · sorry


  have : ∏ m ∈ Finset.Icc M n, y m ≤ (X:ℝ) ^ (M⁻¹ : ℝ) := by
    sorry

  have c_le_X_pow := calc
    c ≤ ∏ m ∈ Finset.Icc M n, (y m : ℝ) ^ K := by
      sorry
    _ ≤ (X:ℝ) ^ (K/M : ℝ) := by
      sorry
    _ ≤ X ^ ε := by
      sorry

  have radical_le_X_pow_mul_prod := calc
    (radical n : ℕ) ≤ ((radical c : ℕ) : ℝ)* ∏ j, (radical (x j) : ℕ) := by
      sorry
    _ ≤ (X : ℝ)^ε * ∏ i, x i := by
      sorry

  have : NeZero M := sorry

  have x_K_le_X_pow : x K ≤ (X : ℝ) ^ ε := by
    sorry

  have X_pow_mul_prod_le_radical := calc
    (X : ℝ) ^ (-ε) * ∏ j, x j ≤ ∏ (j : Fin M), if j ≠ K then x j else 1 := by
      sorry
    _ ≤ ∏ m ∈ Finset.Icc 1 n, y m := by
      sorry
    _ ≤ (radical n : ℕ) := by
      sorry

  refine ⟨x, c, c_mul_prod_x_eq_n.symm, c_le_X_pow, x_pairwise_coprime, X_pow_mul_prod_le_radical, radical_le_X_pow_mul_prod⟩



def const (ε : ℝ) : ℝ := sorry

-- surjective map S*_α β γ (X) <- ⋃_{c, X, Y ,Z} B (c, X, Y, Z)
def B_to_triple {d : ℕ} : (Fin d → ℕ) × (Fin d → ℕ) × (Fin d → ℕ) × (Fin 3 → ℕ) → ℕ × ℕ × ℕ :=
  fun ⟨X, Y, Z, c⟩ ↦
    ⟨c 0 * ∏ i, X i, c 1 * ∏ i, Y i, c 2 * ∏ i, Z i⟩



-- def indexSet' (α β γ : ℝ) {d : ℕ} (X Y Z : Fin d → ℕ) (c : Fin 3 → ℕ) :


/-- -/
-- def dyadicSet_covered
--   {α β γ : ℝ}
--   (hα_pos : 0 < α) (hβ_pos : 0 < β) (hγ_pos : 0 < γ)
--   (hα1 : α ≤ 1) (hβ1 : β ≤ 1) (hγ1 : γ ≤ 1)
--   {x : ℕ} (h2X : 2 ≤ x) {ε : ℝ} (hε_pos : 0 < ε) :
--       (dyadicPoints α β γ x)
--   -- dyadicPoints α β γ x  := by
--   sorry := sorry

/- Here's what I think is happening in this proof: Every point in S* α β γ corresponds to a tuple in some B-set
  by taking the dyadic factorization. Specifically we can guarantee that the X, Y, Z, C corresponding to that
  B-set satisfy these nice properties. This gives us a cover of S* with one set for every point.
  BUT: because these B-sets have nice dyadic properties, we can find a subcover of size << (log X)^{3d} -/

theorem refinedCountTriplesStar_isBigO_B
  {α β γ : ℝ}
  (hα_pos : 0 < α) (hβ_pos : 0 < β) (hγ_pos : 0 < γ)
  (hα1 : α ≤ 1) (hβ1 : β ≤ 1) (hγ1 : γ ≤ 1)
  {x : ℕ} (h2X : 2 ≤ x) {ε : ℝ} (hε_pos : 0 < ε) :
  ∃ d ≥ (1 : ℕ), ∃ X Y Z : Fin d → ℕ,
    (x:ℝ)^(α - ε) ≤ ∏ j, X j ∧ ∏ j, X j ≤ (x : ℝ) ^ (α + ε) ∧
    (x:ℝ)^(β - ε) ≤ ∏ j, Y j ∧ ∏ j, Y j ≤ (x : ℝ) ^ (β + ε) ∧
    (x:ℝ)^(γ - ε) ≤ ∏ j, Z j ∧ ∏ j, Z j ≤ (x : ℝ) ^ (γ + ε) ∧
    ∏ i, X i ^ (i : ℕ) ≤ x ∧
    ∏ i, Y i ^ (i : ℕ) ≤ x ∧
    ∏ i, Z i ^ (i : ℕ) ≤ x ∧
    (x : ℝ) ^ (1 - ε^2) ≤ ∏ i, Z i ^ (i : ℕ) ∧
    ∃ c : Fin 3 → ℕ,
    (∀ i, 1 ≤ c i) ∧
    (∀ i, (c i : ℝ) ≤ (x : ℝ) ^ ε) ∧
    refinedCountTriplesStar α β γ x ≤ const ε * (x : ℝ) ^ ε * B d c X Y Z := by

  sorry
