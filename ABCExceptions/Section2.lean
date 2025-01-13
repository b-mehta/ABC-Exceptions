import Mathlib

open UniqueFactorizationMonoid

noncomputable def countTriples (μ : ℝ) (X : ℕ) : ℕ :=
  Set.ncard
  { (a, b, c) : ℕ × ℕ × ℕ |
    a.Coprime b ∧ a.Coprime c ∧ b.Coprime c ∧
    a + b = c ∧
    radical (a * b * c) < (c ^ μ : ℝ) ∧
    (a, b, c) ∈ Set.Icc (1, 1, 1) (X, X, X) }

lemma countTriples_eq (μ : ℝ) (X : ℕ) :
    countTriples μ X =
      ({ (a, b, c) | 0 < a ∧ 0 < b ∧ 0 < c ∧ a.Coprime b ∧ a.Coprime c ∧ b.Coprime c ∧ a + b = c ∧
         radical (a * b * c) < (c ^ μ : ℝ) } ∩
       Set.Icc (1, 1, 1) (X, X, X)).ncard := by
  rw [countTriples]
  congr 1
  ext ⟨a, b, c⟩
  simp [and_assoc, ← Prod.mk_one_one]
  aesop

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

def similar (x X : ℝ) : Prop := x ∈ Set.Ioc X (2 * X)

local infixr:36 " ~ " => similar

noncomputable def refinedCountTriplesStar (α β γ : ℝ) (X : ℕ) : ℕ :=
  Set.ncard
  { (a, b, c) : ℕ × ℕ × ℕ |
    a.Coprime b ∧ a.Coprime c ∧ b.Coprime c ∧
    a + b = c ∧
    radical a ~ (X ^ α : ℝ) ∧ radical b ~ (X ^ β : ℝ) ∧ radical c ~ (X ^ γ : ℝ) ∧
    c ∈ Set.Icc (X / 2) X }
