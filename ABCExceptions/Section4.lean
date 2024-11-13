import Mathlib.Analysis.RCLike.Basic
import Mathlib.Data.Real.StarOrdered
import Mathlib.Tactic.NormNum.BigOperators
import Mathlib

noncomputable section

open Set

variable {d : ℕ} {δ ε ν : ℝ} {a b c : ℕ → ℝ}

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

@[to_additive]
theorem Finset.prod_Icc_succ_bot {M : Type*} [CommMonoid M] {a b : ℕ}
    (hab : a ≤ b) (f : ℕ → M) :
    (∏ k in Icc a b, f k) = f a * (∏ k in Icc (a + 1) b, f k) := by
  rw [← Nat.Icc_insert_succ_left hab, prod_insert]
  simp

lemma Finset.finite_subsets (s : Finset ℕ) : {a | a ⊆ s}.Finite := by
  simpa using s.powerset.finite_toSet

lemma sum_Icc_eq_sum_range_add_sum_Icc {α : Type*} [AddCommMonoid α] {f : ℕ → α} {t : ℕ}
    (ht : t ≤ d + 1) :
    ∑ i ≤ d, f i = ∑ i ∈ Finset.range t, f i + ∑ i ∈ Finset.Icc t d, f i := by
  rw [Nat.Iic_eq_Icc, ← Nat.Ico_union_Icc_eq_Icc (zero_le _) ht, Nat.Ico_zero_eq_range,
    Finset.sum_union]
  simp +contextual [Finset.disjoint_left]

-- See note [no_index around OfNat.ofNat]
@[simp]
theorem coe_ofNat_eq_mod (m n : ℕ) [NeZero m] :
    ((no_index (OfNat.ofNat n) : Fin m) : ℕ) = OfNat.ofNat n % m :=
  rfl

end

structure baseAssumptions (d : ℕ) (a : ℕ → ℝ) : Prop where
(nonneg : ∀ i, 0 ≤ a i)
(zero : a 0 = 0)
(sum_bound : ∑ i ≤ d, i * a i ≤ 1)

variable (ha : baseAssumptions d a) (hb : baseAssumptions d b) (hc : baseAssumptions d c)

lemma baseAssumptions.sum_restrict_bound (ha : baseAssumptions d a) :
    ∑ i in Finset.Icc 1 d, i * a i ≤ 1 := by
  simpa [Nat.Iic_eq_Icc, Finset.sum_Icc_succ_bot (a := 0)] using ha.sum_bound

def Bound4Point3 (d : ℕ) (ε : ℝ) (a b : ℕ → ℝ) : Prop :=
  0.66 - ε ^ 2 ≤ ∑ i ≤ d, (a i + b i)

def Bound4Point4 (d : ℕ) (δ ε : ℝ) (a b c : ℕ → ℝ) : Prop :=
  ∑ i ≤ d, (a i + b i + c i) ≤ 1 + δ - ε

-- we will later show that 4.5 can be safely assumed in context, after we've assumed 1.2 and 4.4
structure Bound4Point5 (d : ℕ) (δ ε : ℝ) (a : ℕ → ℝ) : Prop where
(lower : 0.32 - δ ≤ ∑ i ≤ d, a i)
(upper : ∑ i ≤ d, a i ≤ 0.34 + δ - ε / 2)

def FourierBound (d : ℕ) (δ ν : ℝ) (a b : ℕ → ℝ) : Prop :=
  ν < 1/2 * (1 + δ + ∑ i ≤ d, max (a i) (b i) - sSup {max (a i) (b i) | i ∈ Ioc 1 d})

variable (hfab : FourierBound d δ ν a b)
         (hfac : FourierBound d δ ν a c)
         (hfbc : FourierBound d δ ν b c)

section

include hfab

/-- From the Fourier bound, we can deduce bounds for each `j ∈ (1, d]`. -/
lemma FourierBound.special (j : ℕ) (hj : j ∈ Ioc 1 d) :
    ν < 1/2 * (1 + δ + ∑ i ≤ d, max (a i) (b i) - max (a j) (b j)) := by
  apply hfab.trans_le ?_
  gcongr
  exact le_csSup ((finite_Ioc 1 d).image _).bddAbove ⟨_, hj, rfl⟩

lemma FourierBound.special' (j : ℕ) (hj : j ∈ Ioc 1 d) :
    ν < 1/2 * (1 + δ + ∑ i ≤ d with i ≠ j, max (a i) (b i)) := by
  refine (hfab.special j hj).trans_eq ?_
  rw [add_sub_assoc, Finset.filter_ne', Finset.sum_erase_eq_sub]
  simp only [mem_Ioc] at hj
  simp [hj]

lemma FourierBound.two (hd : 2 ≤ d) :
    ν < 1/2 * (1 + δ + ∑ i ≤ d, max (a i) (b i) - max (a 2) (b 2)) :=
  hfab.special _ (by simpa)

lemma FourierBound.three (hd : 3 ≤ d) :
    ν < 1/2 * (1 + δ + ∑ i ≤ d, max (a i) (b i) - max (a 3) (b 3)) :=
  hfab.special _ (by simpa)

lemma FourierBound.symm : FourierBound d δ ν b a := hfab.trans_eq (by simp [max_comm])

end

def DeterminantBound (d : ℕ) (δ ν : ℝ) (a b : ℕ → ℝ) : Prop :=
  ν < sInf {1 + δ - a p - b q + min (a p / q) (b q / p) |
    (p : ℕ) (q : ℕ) (_ : p ∈ Ioc 1 d) (_ : q ∈ Ioc 1 d)}

section

end

def ThueBound (d : ℕ) (δ ν : ℝ) (a b : ℕ → ℝ) : Prop :=
  ν < 1 + δ - sSup {∑ i ≤ d with p ∣ i, (a i + b i) | p ∈ Ioc 1 d}

variable (htab : ThueBound d δ ν a b) (htac : ThueBound d δ ν a c) (htbc : ThueBound d δ ν b c)

section

include htab

lemma ThueBound.symm : ThueBound d δ ν b a :=
  htab.trans_eq (by simp [add_comm])

lemma ThueBound.special (p : ℕ) (hp : p ∈ Ioc 1 d) :
    ν < 1 + δ - ∑ i ≤ d with p ∣ i, (a i + b i) := by
  refine htab.trans_le ?_
  gcongr
  exact le_csSup ((finite_Ioc 1 d).image _).bddAbove ⟨_, hp, rfl⟩

include ha hb
lemma ThueBound.very_special (p : ℕ) (hp : p ∈ Ioc 1 d) :
    ν < 1 + δ - (a p + b p) := by
  refine (htab.special p hp).trans_le ?_
  gcongr
  refine Finset.single_le_sum (f := fun i ↦ a i + b i) ?_ ?_
  · simp only [Finset.mem_filter, Finset.mem_Iic, and_imp]
    intro i hi _
    exact add_nonneg (ha.nonneg i) (hb.nonneg i)
  · simp only [mem_Ioc] at hp
    simp [hp]

lemma ThueBound.special_two (hd : 4 ≤ d) :
    ν < 1 + δ - (a 2 + a 4 + (b 2 + b 4)) := by
  refine (htab.special 2 (by simp; omega)).trans_le ?_
  gcongr
  rw [add_add_add_comm]
  refine Finset.add_le_sum (f := fun i ↦ a i + b i) ?_ (by simp; omega) (by norm_num [hd]) (by simp)
  simp only [Finset.mem_filter, Finset.mem_Iic, and_imp]
  intro i hi h2i
  exact add_nonneg (ha.nonneg i) (hb.nonneg i)

end

def s (a b c : ℕ → ℝ) (i : ℕ) := a i + b i + c i
local notation "s" => s a b c

lemma s_apply (i : ℕ) : s i = a i + b i + c i := rfl

include ha hb hc in
lemma s_nonneg (i : ℕ) : 0 ≤ s i :=
  add_nonneg (add_nonneg (ha.nonneg _) (hb.nonneg _)) (hc.nonneg _)

include ha hb hc in
lemma s_zero : s 0 = 0 := by
  simp [s_apply, ha.zero, hb.zero, hc.zero]

-- TODO: change geometry bound things to eqn 4.6 instead, and deduce this version from that.

/--
A statement of the Geometry bound. Note that this is _not_ saying the bound holds, but defining
what it means for the bound to hold. In Section4.lean, we will take this as an assumption to many
statements in order to deduce bounds on `ν`.
Elsewhere we will show that the bound holds, and thus its proof can be fed in to those lemmas
which have it as an assumption.
-/
def GeometryBound (d : ℕ) (δ ν : ℝ) (a b c : ℕ → ℝ) : Prop :=
  ν < δ + sInf
    { max 1 (∑ i ∈ I, i * a i + ∑ i ∈ I', i * b i + ∑ i ∈ I'', i * c i) -
      (∑ i ∈ I, a i + ∑ i ∈ I', b i + ∑ i ∈ I'', c i) |
      (I ⊆ Finset.Icc 1 d) (I' ⊆ Finset.Icc 1 d) (I'' ⊆ Finset.Icc 1 d) }

variable (hg : GeometryBound d δ ν a b c)

section

/--
The set that we are taking the infimum over in the geometry bound is a finite set.
-/
lemma geometryBound_set_finite :
    Set.Finite
      { max 1 (∑ i ∈ I, i * a i + ∑ i ∈ I', i * b i + ∑ i ∈ I'', i * c i) -
        (∑ i ∈ I, a i + ∑ i ∈ I', b i + ∑ i ∈ I'', c i) |
        (I ⊆ Finset.Icc 1 d) (I' ⊆ Finset.Icc 1 d) (I'' ⊆ Finset.Icc 1 d) } := by
  let f (I I' I'' : Finset ℕ) : ℝ :=
    max 1 (∑ i ∈ I, i * a i + ∑ i ∈ I', i * b i + ∑ i ∈ I'', i * c i) -
        (∑ i ∈ I, a i + ∑ i ∈ I', b i + ∑ i ∈ I'', c i)
  have : { f I I' I'' | (I ⊆ Finset.Icc 1 d) (I' ⊆ Finset.Icc 1 d) (I'' ⊆ Finset.Icc 1 d) } =
      (fun x ↦ f x.1 x.2.1 x.2.2) ''
        ((Finset.Icc 1 d).powerset ×ˢ (Finset.Icc 1 d).powerset ×ˢ (Finset.Icc 1 d).powerset) := by
    ext y
    simp only [mem_setOf_eq, mem_image, mem_prod, Finset.mem_coe, Finset.mem_powerset, Prod.exists]
    constructor
    · rintro ⟨I, hI, I', hI', I'', hI'', rfl⟩
      exact ⟨I, I', I'', ⟨hI, hI', hI''⟩, rfl⟩
    · rintro ⟨I, I', I'', ⟨hI, hI', hI''⟩, rfl⟩
      exact ⟨I, hI, I', hI', I'', hI'', rfl⟩
  rw [this]
  exact Set.Finite.image _ (toFinite _)

include hg

lemma GeometryBound.special (I I' I'' : Finset ℕ)
    (hI : I ⊆ Finset.Icc 1 d) (hI' : I' ⊆ Finset.Icc 1 d) (hI'' : I'' ⊆ Finset.Icc 1 d) :
    ν < δ + (max 1 (∑ i ∈ I, i * a i + ∑ i ∈ I', i * b i + ∑ i ∈ I'', i * c i) -
          (∑ i ∈ I, a i + ∑ i ∈ I', b i + ∑ i ∈ I'', c i)) := by
  refine hg.trans_le ?_
  gcongr
  exact csInf_le (Set.Finite.bddBelow geometryBound_set_finite) ⟨I, hI, I', hI', I'', hI'', rfl⟩

lemma GeometryBound.special_s
    (I : Finset ℕ) (hI : I ⊆ Finset.Icc 1 d) :
    ν < δ + (max 1 (∑ i ∈ I, (i * s i)) - (∑ i ∈ I, s i)) := by
  refine (hg.special I I I hI hI hI).trans_eq ?_
  simp [s_apply, mul_add, Finset.sum_add_distrib]

end

def δ_ (d : ℕ) (f : ℕ → ℝ) : ℝ := 1 / 3 - ∑ i ≤ d, f i

/-- 4.7 -/
lemma sum_eq_δ_ (d : ℕ) (f : ℕ → ℝ) : ∑ i ≤ d, f i = 1 / 3 - δ_ d f := by simp [δ_]

lemma bound_4_point_8 (h43 : Bound4Point3 d ε a b) : δ_ d a + δ_ d b ≤ 2 / 300 + ε ^ 2 := by
  simp only [δ_, sub_add_sub_comm, ← Finset.sum_add_distrib, Bound4Point3] at h43 ⊢
  norm_num at h43 ⊢
  linarith

lemma bound_4_point_9_lower (hε : 0 < ε) (f : ℕ → ℝ) (h45 : Bound4Point5 d δ ε f) :
    - 2 / 300 - δ ≤ δ_ d f := by
  replace h45 := h45.upper
  norm_num [δ_] at h45 ⊢
  linarith

lemma bound_4_point_9_upper (hε : 0 < ε) (f : ℕ → ℝ) (h45 : Bound4Point5 d δ ε f) :
    δ_ d f ≤ 1 / 75 + δ + ε := by
  replace h45 := h45.lower
  norm_num [δ_] at h45 ⊢
  linarith

def delta_s (d : ℕ) (a b c : ℕ → ℝ) := δ_ d a + δ_ d b + δ_ d c
local notation "δₛ" => delta_s d a b c

lemma δₛ_eq : δₛ = δ_ d a + δ_ d b + δ_ d c := rfl

lemma bound_4_point_10_lower (hε : 0 < ε) (h44 : Bound4Point4 d δ ε a b c) :
    - δ < δₛ := by
  simp only [δₛ_eq, Bound4Point4, Finset.sum_add_distrib, δ_] at h44 ⊢
  linarith

lemma sum_s : ∑ i ≤ d, s i = 1 - δₛ := by
  simp [s_apply, δₛ_eq, Finset.sum_add_distrib, δ_]
  ring

lemma bound_4_point_10_upper (hε : 0 < ε) (hε₁ : ε ≤ 2 / 3)
    (h43ab : Bound4Point3 d ε a b)
    (h43ac : Bound4Point3 d ε a c)
    (h43bc : Bound4Point3 d ε b c) :
    δₛ ≤ 0.01 + ε := by
  have := bound_4_point_8 h43ab
  have := bound_4_point_8 h43ac
  have := bound_4_point_8 h43bc
  have : 2 * δₛ ≤ 0.02 + 3 * ε ^ 2 := by
    norm_num1 at *
    rw [δₛ_eq]
    linarith
  have : 3 * ε ^ 2 ≤ 2 * ε := by nlinarith
  norm_num1 at *
  linarith

lemma bound_4_point_11_2 (h : baseAssumptions d a) (hd : 1 ≤ d) :
    ∑ i ∈ Finset.Icc 2 d, (i - 1) * a i ≤ 2 / 3 + δ_ d a :=
  calc
    _ = ∑ i ∈ insert 1 (Finset.Icc 2 d), (i - 1) * a i := by simp
    _ = ∑ i ∈ Finset.Icc 1 d, (i - 1) * a i := by rw [← Nat.Icc_insert_succ_left hd]
    _ = ∑ i ∈ Finset.Icc 1 d, i * a i - ∑ i ∈ Finset.Icc 1 d, a i := by simp [sub_one_mul]
    _ ≤ _ := by
      rw [δ_, Nat.Iic_eq_Icc, ← Nat.Icc_insert_succ_left (show 0 ≤ d by simp)]
      simp only [zero_add, Finset.mem_Icc, nonpos_iff_eq_zero, one_ne_zero, zero_le,
        and_true, not_false_eq_true, Finset.sum_insert, h.zero]
      linarith [h.sum_restrict_bound]

lemma bound_4_point_11_3 (ha : baseAssumptions d a) (hd : 2 ≤ d) :
    ∑ i ∈ Finset.Icc 3 d, (i - 2) * a i ≤ 1 / 3 + a 1 + 2 * δ_ d a := by
  have hd' : 3 ≤ d + 1 := by omega
  have h₁ : ∑ i ≤ d, i * a i ≤ 1 := ha.sum_bound
  replace h₁ : a 1 + 2 * a 2 + ∑ i ∈ Finset.Icc 3 d, i * a i ≤ 1 := by
    rw [sum_Icc_eq_sum_range_add_sum_Icc hd'] at h₁
    simpa [Finset.sum_range, Fin.sum_univ_three] using h₁
  have h₂ : δ_ d a = 1 / 3 - (a 1 + a 2 + ∑ x ∈ Finset.Icc 3 d, a x) := by
    rw [δ_, sum_Icc_eq_sum_range_add_sum_Icc hd']
    simp [Finset.sum_range, Fin.sum_univ_three, ha.zero]
  simp only [sub_mul, Finset.sum_sub_distrib, h₂, ← Finset.mul_sum]
  linarith

lemma bound_4_point_11_4 (ha : baseAssumptions d a) (hd : 3 ≤ d) :
    ∑ i ∈ Finset.Icc 4 d, (i - 3) * a i ≤ 2 * a 1 + a 2 + 3 * δ_ d a := by
  have hd' : 4 ≤ d + 1 := by omega
  have h₁ : ∑ i ≤ d, i * a i ≤ 1 := ha.sum_bound
  replace h₁ : a 1 + 2 * a 2 + 3 * a 3 + ∑ i ∈ Finset.Icc 4 d, i * a i ≤ 1 := by
    rw [sum_Icc_eq_sum_range_add_sum_Icc hd'] at h₁
    simpa [Finset.sum_range, Fin.sum_univ_four] using h₁
  have h₂ : δ_ d a = 1 / 3 - (a 1 + a 2 + a 3 + ∑ x ∈ Finset.Icc 4 d, a x) := by
    rw [δ_, sum_Icc_eq_sum_range_add_sum_Icc hd']
    simp [Finset.sum_range, Fin.sum_univ_four, ha.zero]
  simp only [sub_mul, Finset.sum_sub_distrib, h₂, ← Finset.mul_sum]
  linarith

include ha hb htab in
lemma bound_4_point_12 (j : ℕ) (hj : j ∈ Ioc 1 d) (hν : 0.66 < ν) :
    a j + b j < 0.34 + δ := by
  norm_num1 at hν ⊢
  linarith [htab.very_special ha hb j hj]

include ha hb htab in
lemma bound_4_point_13 (hd : 4 ≤ d) (hν : 0.66 < ν) :
    a 2 + a 4 + (b 2 + b 4) < 0.34 + δ := by
  norm_num1 at hν ⊢
  linarith [htab.special_two ha hb hd]

include ha hb hc htab htac htbc in
lemma bound_4_point_14_general
    (j : ℕ) (hj : j ∈ Ioc 1 d) (hν : 0.66 < ν) :
    s j < 0.51 + 1.5 * δ := by
  replace hab := bound_4_point_12 ha hb htab j hj hν
  replace hac := bound_4_point_12 ha hc htac j hj hν
  replace hbc := bound_4_point_12 hb hc htbc j hj hν
  norm_num [s_apply] at hab hac hbc ⊢
  linarith

include ha hb hc htab htac htbc in
lemma bound_4_point_14_two_four
    (hd : 4 ≤ d) (hν : 0.66 < ν) :
    s 2 + s 4 < 0.51 + 1.5 * δ := by
  replace hab := bound_4_point_13 ha hb htab hd hν
  replace hac := bound_4_point_13 ha hc htac hd hν
  replace hbc := bound_4_point_13 hb hc htbc hd hν
  norm_num [s_apply] at hab hac hbc ⊢
  linarith

-- see also `sum_s`
include ha hb hc in
lemma sum_s_2
    (hd : 1 ≤ d) :
    ∑ i ∈ Finset.Icc 2 d, (i - 1) * s i ≤ 2 + δₛ := by
  simp only [s_apply, mul_add, Finset.sum_add_distrib, δₛ_eq]
  linarith [bound_4_point_11_2 ha hd, bound_4_point_11_2 hb hd, bound_4_point_11_2 hc hd]

include ha hb hc in
lemma sum_s_3
    (hd : 2 ≤ d) :
    ∑ i ∈ Finset.Icc 3 d, (i - 2) * s i ≤ 1 + s 1 + 2 * δₛ := by
  simp only [s_apply, mul_add, Finset.sum_add_distrib, δₛ_eq]
  linarith [bound_4_point_11_3 ha hd, bound_4_point_11_3 hb hd, bound_4_point_11_3 hc hd]

include ha hb hc in
lemma sum_s_4
    (hd : 3 ≤ d) :
    ∑ i ∈ Finset.Icc 4 d, (i - 3) * s i ≤ 2 * s 1 + s 2 + 3 * δₛ := by
  simp only [s_apply, mul_add, Finset.sum_add_distrib, δₛ_eq]
  linarith [bound_4_point_11_4 ha hd, bound_4_point_11_4 hb hd, bound_4_point_11_4 hc hd]

include ha hb hc htab htac htbc hg in
lemma bound_4_point_15
    (hδ : δ ≤ 0.06)
    (hν : 0.66 < ν) (hd : 2 ≤ d) :
    s 1 + s 2 ≤ 0.34 + δ := by
  have h₁ : ν < δ + (max 1 (s 1 + 2 * s 2) - (s 1 + s 2)) := by
    have := hg.special_s {1, 2} (by simp [Finset.insert_subset_iff]; constructor <;> omega)
    simpa using this
  replace h₁ : ν < max (δ + (1 - (s 1 + s 2))) (δ + s 2) := calc
    _ < δ + (max 1 (s 1 + 2 * s 2) - (s 1 + s 2)) := h₁
    _ = δ + (1 - (s 1 + s 2)) ⊔ (s 1 + 2 * s 2 - (s 1 + s 2)) := by rw [max_sub_sub_right]
    _ = δ + max (1 - (s 1 + s 2)) (s 2) := by ring_nf
    _ = max (δ + (1 - (s 1 + s 2))) (δ + s 2) := by rw [max_add_add_left]
  by_contra! h₃ : 0.34 + δ < s 1 + s 2
  replace h₃ : δ + (1 - (s 1 + s 2)) < 0.66 := by
    norm_num1 at h₃ ⊢
    linarith only [h₃]
  have h₂ : s 2 < 0.51 + 1.5 * δ :=
    bound_4_point_14_general ha hb hc htab htac htbc 2 (by simp [hd]) hν
  replace h₂ : δ + s 2 < 0.66 := calc
    _ < δ + (0.51 + 1.5 * δ) := by gcongr
    _ = 0.51 + 2.5 * δ := by ring
    _ ≤ 0.66 := by norm_num1 at hδ ⊢; linarith
  have h₄ : max (δ + (1 - (s 1 + s 2))) (δ + s 2) < 0.66 := by simp [h₂, h₃]
  linarith

/-- 4.16 -/
def SubSums (j : ℕ) (a b c : ℕ → ℝ) : Set ℝ :=
    {a j, b j, c j, a j + b j, a j + c j, b j + c j, a j + b j + c j}

include hg in
lemma GeometryBound.subSums
    {τ : ℝ} (j : ℕ) (hj : j ∈ Icc 3 d) (hτ : τ ∈ SubSums j a b c) :
    ν < δ + (max 1 (s 1 + 2 * s 2 + j * τ) - (s 1 + s 2 + τ)) ∧
    ν < δ + (max 1 (s 1 + j * τ) - (s 1 + τ)) := by
  simp only [SubSums, mem_insert_iff, mem_singleton_iff] at hτ
  simp only [mem_Icc] at hj
  have hj₁ : 1 ≠ j := by omega
  have hj₂ : 2 ≠ j := by omega
  have hj₁'' : {1} ⊆ Finset.Icc 1 d := by simp; omega
  have hj₂'' : {1, 2} ⊆ Finset.Icc 1 d := by simp [Finset.insert_subset_iff]; omega
  have hj₁' : {1, j} ⊆ Finset.Icc 1 d := by simp [Finset.insert_subset_iff]; omega
  have hj₂' : {1, 2, j} ⊆ Finset.Icc 1 d := by simp [Finset.insert_subset_iff]; omega
  obtain rfl | rfl | rfl | rfl | rfl | rfl | rfl := hτ
  · have h₁ := hg.special {1, j} {1} {1} ‹_› ‹_› ‹_›
    have h₂ := hg.special {1, 2, j} {1, 2} {1, 2} ‹_› ‹_› ‹_›
    simp only [Finset.mem_singleton, hj₁, not_false_eq_true, Finset.sum_insert, Nat.cast_one,
      one_mul, Finset.sum_singleton, Finset.mem_insert, OfNat.one_ne_ofNat, or_self, hj₂,
      Nat.cast_ofNat] at h₁ h₂
    simp only [s_apply]
    exact ⟨h₂.trans_eq (by ring_nf), h₁.trans_eq (by ring_nf)⟩
  · have h₁ := hg.special {1} {1, j} {1} ‹_› ‹_› ‹_›
    have h₂ := hg.special {1, 2} {1, 2, j} {1, 2} ‹_› ‹_› ‹_›
    simp only [Finset.mem_singleton, hj₁, not_false_eq_true, Finset.sum_insert, Nat.cast_one,
      one_mul, Finset.sum_singleton, Finset.mem_insert, OfNat.one_ne_ofNat, or_self, hj₂,
      Nat.cast_ofNat] at h₁ h₂
    simp only [s_apply]
    exact ⟨h₂.trans_eq (by ring_nf), h₁.trans_eq (by ring_nf)⟩
  · have h₁ := hg.special {1} {1} {1, j} ‹_› ‹_› ‹_›
    have h₂ := hg.special {1, 2} {1, 2} {1, 2, j} ‹_› ‹_› ‹_›
    simp only [Finset.mem_singleton, hj₁, not_false_eq_true, Finset.sum_insert, Nat.cast_one,
      one_mul, Finset.sum_singleton, Finset.mem_insert, OfNat.one_ne_ofNat, or_self, hj₂,
      Nat.cast_ofNat] at h₁ h₂
    simp only [s_apply]
    exact ⟨h₂.trans_eq (by ring_nf), h₁.trans_eq (by ring_nf)⟩
  · have h₁ := hg.special {1, j} {1, j} {1} ‹_› ‹_› ‹_›
    have h₂ := hg.special {1, 2, j} {1, 2, j} {1, 2} ‹_› ‹_› ‹_›
    simp only [Finset.mem_singleton, hj₁, not_false_eq_true, Finset.sum_insert, Nat.cast_one,
      one_mul, Finset.sum_singleton, Finset.mem_insert, OfNat.one_ne_ofNat, or_self, hj₂,
      Nat.cast_ofNat] at h₁ h₂
    simp only [s_apply]
    exact ⟨h₂.trans_eq (by ring_nf), h₁.trans_eq (by ring_nf)⟩
  · have h₁ := hg.special {1, j} {1} {1, j} ‹_› ‹_› ‹_›
    have h₂ := hg.special {1, 2, j} {1, 2} {1, 2, j} ‹_› ‹_› ‹_›
    simp only [Finset.mem_singleton, hj₁, not_false_eq_true, Finset.sum_insert, Nat.cast_one,
      one_mul, Finset.sum_singleton, Finset.mem_insert, OfNat.one_ne_ofNat, or_self, hj₂,
      Nat.cast_ofNat] at h₁ h₂
    simp only [s_apply]
    exact ⟨h₂.trans_eq (by ring_nf), h₁.trans_eq (by ring_nf)⟩
  · have h₁ := hg.special {1} {1, j} {1, j} ‹_› ‹_› ‹_›
    have h₂ := hg.special {1, 2} {1, 2, j} {1, 2, j} ‹_› ‹_› ‹_›
    simp only [Finset.mem_singleton, hj₁, not_false_eq_true, Finset.sum_insert, Nat.cast_one,
      one_mul, Finset.sum_singleton, Finset.mem_insert, OfNat.one_ne_ofNat, or_self, hj₂,
      Nat.cast_ofNat] at h₁ h₂
    simp only [s_apply]
    exact ⟨h₂.trans_eq (by ring_nf), h₁.trans_eq (by ring_nf)⟩
  · have h₁ := hg.special_s {1, j} ‹_›
    have h₂ := hg.special_s {1, 2, j} ‹_›
    simp only [Finset.mem_singleton, hj₁, not_false_eq_true, Finset.sum_insert, Nat.cast_one,
      one_mul, Finset.sum_singleton, Finset.mem_insert, OfNat.one_ne_ofNat, or_self, hj₂,
      Nat.cast_ofNat, s_apply] at h₁ h₂
    simp only [s_apply]
    exact ⟨h₂.trans_eq (by ring_nf), h₁.trans_eq (by ring_nf)⟩

include hg in
lemma bound_4_point_17_aux1 {τ : ℝ} (hτ : τ ∈ SubSums 3 a b c) (hν : 0.66 < ν) (hd : 3 ≤ d) :
    τ ∉ Icc (0.34 - s 1 - s 2 + δ) (0.33 - 1 / 2 * s 2 - 1 / 2 * δ) := by
  have h₁ := (hg.subSums 3 (by simp [hd]) hτ).1
  contrapose! h₁
  simp only [mem_Icc] at h₁
  rw [← max_sub_sub_right, ← max_add_add_left, max_le_iff]
  simp only [s_apply] at *
  norm_num1 at *
  constructor
  · linarith
  · linarith

include hg in
lemma bound_4_point_17_aux2 {τ : ℝ} (hτ : τ ∈ SubSums 3 a b c) (hν : 0.66 < ν) (hd : 3 ≤ d) :
    τ ∉ Icc (0.34 - s 1 + δ) (0.33 - 1 / 2 * δ) := by
  have h₁ := (hg.subSums 3 (by simp [hd]) hτ).2
  contrapose! h₁
  simp only [mem_Icc] at h₁
  rw [← max_sub_sub_right, ← max_add_add_left, max_le_iff]
  simp only [s_apply] at *
  norm_num1 at *
  constructor
  · linarith
  · linarith

include hg in
lemma bound_4_point_17 {τ : ℝ} (hτ : τ ∈ SubSums 3 a b c) (hd : 3 ≤ d) (hν : 0.66 < ν) :
    τ ∉ Icc (0.34 - s 1 - s 2 + δ) (0.33 - 1 / 2 * s 2 - 1 / 2 * δ) ∪
        Icc (0.34 - s 1 + δ) (0.33 - 1 / 2 * δ) := by
  simp only [mem_union, not_or]
  exact ⟨bound_4_point_17_aux1 hg hτ hν hd, bound_4_point_17_aux2 hg hτ hν hd⟩

include ha in
lemma bound_4_point_18_first (hd : 3 ≤ d) :
    1 / 3 - 4 * δ_ d a - 3 * a 1 - 2 * a 2 ≤ a 3 := by
  have hd' : 4 ≤ d + 1 := by omega
  have h₁ : ∑ i ∈ Finset.Icc 4 d, a i ≤ ∑ i ∈ Finset.Icc 4 d, (i - 3) * a i := by
    gcongr with i hi
    have ha' := ha.nonneg i
    simp only [Finset.mem_Icc] at hi
    have : (4 : ℝ) ≤ i := by simp_all
    linear_combination a i * this
  have h₂ : ∑ i ∈ Finset.Icc 4 d, (i - 3) * a i ≤ 2 * a 1 + a 2 + 3 * δ_ d a :=
    bound_4_point_11_4 ha hd
  have h₃ : a 1 + a 2 + a 3 + ∑ i ∈ Finset.Icc 4 d, a i = 1 / 3 - δ_ d a := by
    rw [← sum_eq_δ_, sum_Icc_eq_sum_range_add_sum_Icc hd']
    simp [Finset.sum_range, Fin.sum_univ_four, ha.zero]
  linarith -- linear_combination h₁ + h₂ - h₃

include ha in
lemma bound_4_point_18_second (hd : 4 ≤ d) :
    1 / 3 - (5 / 2) * δ_ d a - 2 * a 1 - (3 / 2) * a 2 - 1 / 2 * a 4 ≤ a 3 := by
  have hd' : 5 ≤ d + 1 := by omega
  have h₃ : a 1 + a 2 + a 3 + a 4 + ∑ i ∈ Finset.Icc 5 d, a i = 1 / 3 - δ_ d a := by
    rw [← sum_eq_δ_, sum_Icc_eq_sum_range_add_sum_Icc hd']
    simp [Finset.sum_range, Fin.sum_univ_five, ha.zero]
  have h₁ : ∑ i ∈ Finset.Icc 5 d, a i ≤ 1 / 2 * ∑ i ∈ Finset.Icc 5 d, (i - 3) * a i := by
    rw [Finset.mul_sum]
    gcongr with i hi
    have ha' := ha.nonneg i
    simp only [Finset.mem_Icc] at hi
    have : (5 : ℝ) ≤ i := by simp_all
    linear_combination 1 / 2 * a i * this
  have h₂ : ∑ i ∈ Finset.Icc 4 d, (i - 3) * a i ≤ 2 * a 1 + a 2 + 3 * δ_ d a :=
    bound_4_point_11_4 ha (by omega)
  replace h₂ : ∑ i ∈ Finset.Icc 5 d, (i - 3) * a i ≤ 2 * a 1 + a 2 + 3 * δ_ d a - a 4 := by
    rw [Finset.sum_Icc_succ_bot hd] at h₂
    linear_combination h₂
  linarith

include ha hb hc in
lemma bound_4_point_19 (hd : 3 ≤ d) :
    1 - 4 * δₛ - 3 * s 1 - 2 * s 2 ≤ s 3 := by
  simp only [δₛ_eq, s_apply]
  linear_combination
    bound_4_point_18_first ha hd + bound_4_point_18_first hb hd + bound_4_point_18_first hc hd

include ha hb hc in
lemma bound_4_point_20 (hd : 4 ≤ d) :
    1 - (5 / 2) * δₛ - 2 * s 1 - (3 / 2) * s 2 - 1 / 2 * s 4 ≤ s 3 := by
  simp only [δₛ_eq, s_apply]
  linear_combination
    bound_4_point_18_second ha hd + bound_4_point_18_second hb hd + bound_4_point_18_second hc hd

include ha hb hc htab htac htbc hg in
lemma bound_4_point_21 (hν : 0.66 < ν) (hs₂ : 0.3 ≤ s 2) (hδ : δ ≤ 0.06) (hd : 2 ≤ d) :
    s 1 ≤ 0.04 + δ := by
  linear_combination bound_4_point_15 ha hb hc htab htac htbc hg hδ hν hd + hs₂

include ha hb hc htab htac htbc in
lemma case_1_helper (hν : 0.66 < ν) (hs₂ : 0.3 ≤ s 2) (hd : 4 ≤ d) :
    s 4 < 0.21 + 3 / 2 * δ := by
  linear_combination bound_4_point_14_two_four ha hb hc htab htac htbc hd hν + hs₂

include ha hb hc hg htab htac htbc hg in
lemma subcase_1_point_1
    (h43ab : Bound4Point3 d ε a b)
    (h43ac : Bound4Point3 d ε a c)
    (h43bc : Bound4Point3 d ε b c)
    (hd : 4 ≤ d)
    (hν : 0.66 < ν)
    (hδ₀ : 0 ≤ δ)
    (hδ : δ ≤ 0.001)
    (hbc : c 3 ≤ b 3)
    (hs₂ : 0.3 ≤ s 2)
    (hb₃ : b 3 ≤ 0.34 - s 1 - s 2 + δ)
    (hε : ε ≤ 1 / 1000000)
    (hε₀ : 0 < ε) :
    False := by
  have h₁ : b 3 + c 3 ≤ 0.33 - 1 / 2 * s 2 - 1 / 2* δ := by
    linear_combination hbc + 2 * hb₃ + 2 * s_nonneg ha hb hc 1 + 3 / 2 * hs₂ + 5 / 2 * hδ
  have hbcs : b 3 + c 3 ∈ SubSums 3 a b c := by simp [SubSums]
  have h₂ : b 3 + c 3 < 0.34 - s 1 - s 2 + δ := by
    simpa [h₁.not_lt, -one_div] using bound_4_point_17_aux1 hg hbcs hν (by omega)
  have hs3 : a 3 = s 3 - (b 3 + c 3) := by rw [s_apply]; ring
  have hδ' : δ ≤ 0.06 := by linear_combination hδ
  have := bound_4_point_14_two_four ha hb hc htab htac htbc hd hν
  have i : δₛ = δ_ d a + δ_ d b + δ_ d c := by simp [δₛ_eq]
  have h₃ : 0.365 - (5 / 2) * δₛ - 3 * δ ≤ a 3 := calc
    _ ≤ 0.66 - 5 / 2 * δₛ - s 1 - 1 / 2 * s 2 - 1 / 2 * s 4 - δ := by
      linear_combination 1 / 2 * this + 1 / 4 * hδ₀ +
        bound_4_point_21 ha hb hc htab htac htbc hg hν hs₂ hδ' (by omega)
    _ ≤ a 3 := by
        linear_combination h₂ - hs3 + bound_4_point_20 ha hb hc hd
  have h₄ : a 3 ≤ 1 / 3 - δ_ d a := by
    rw [← sum_eq_δ_]
    apply Finset.single_le_sum
    · intro i hi
      apply ha.nonneg i
    · simp
      omega
  have hbc := bound_4_point_8 h43bc
  have h₅ := bound_4_point_10_upper hε₀ (by linarith only [hε]) h43ab h43ac h43bc
  have h₆ : (0.365 - 1 / 3) ≤ (3 / 2) * δₛ + δ_ d b + δ_ d c + 3 * δ := by
    linear_combination h₃ + h₄ + i
  have : ε ^ 2 ≤ ε := by nlinarith only [hε₀, hε]
  have : (3 / 2) * δₛ + δ_ d b + δ_ d c + 3 * δ < 0.0247 := by
    linear_combination (3 / 2) * h₅ + hbc + 3 * hδ + this + 5 / 2 * hε
  norm_num1 at h₆ this
  linarith only [h₆, this]

lemma case_1
    (hν : 0.66 < ν)
    (hs₂ : 0.3 ≤ s 2) :
    False := by
  sorry

lemma case_2
    (hν : 0.66 < ν)
    (hs₂ : s 2 < 0.3) :
    False := by
  sorry

include a b c in
theorem thm_4_point_3 : ν ≤ 0.66 := by
  by_contra! hν
  cases le_or_lt 0.3 (s 2)
  case inl hs₂ => exact case_1 (hs₂ := hs₂) (hν := hν)
  case inr hs₂ => exact case_2 (hs₂ := hs₂) (hν := hν)

end
