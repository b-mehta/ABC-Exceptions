import Mathlib.Analysis.RCLike.Basic
import Mathlib.Data.Real.StarOrdered
import Mathlib.Tactic.NormNum.BigOperators

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

variable (h43ab : Bound4Point3 d ε a b)
         (h43ac : Bound4Point3 d ε a c)
         (h43bc : Bound4Point3 d ε b c)
section

include h43ab

lemma Bound4Point3.symm : Bound4Point3 d ε b a :=
  h43ab.trans_eq <| Finset.sum_congr rfl fun _ _ ↦ add_comm _ _

end

def Bound4Point4 (d : ℕ) (δ ε : ℝ) (a b c : ℕ → ℝ) : Prop :=
  ∑ i ≤ d, (a i + b i + c i) ≤ 1 + δ - ε

variable (h44 : Bound4Point4 d δ ε a b c)

-- we will later show that 4.5 can be safely assumed in context, after we've assumed 1.2 and 4.4
structure Bound4Point5 (d : ℕ) (δ ε : ℝ) (a : ℕ → ℝ) : Prop where
(lower : 0.32 - δ ≤ ∑ i ≤ d, a i)
(upper : ∑ i ≤ d, a i ≤ 0.34 + δ - ε / 2)

variable (h45a : Bound4Point5 d δ ε a) (h45b : Bound4Point5 d δ ε b) (h45c : Bound4Point5 d δ ε c)

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
  hfab.special 2 (by simpa)

lemma FourierBound.three (hd : 3 ≤ d) :
    ν < 1/2 * (1 + δ + ∑ i ≤ d, max (a i) (b i) - max (a 3) (b 3)) :=
  hfab.special _ (by simpa)

lemma FourierBound.symm : FourierBound d δ ν b a := hfab.trans_eq (by simp [max_comm])

end

def DeterminantBound (d : ℕ) (δ ν : ℝ) (a b : ℕ → ℝ) : Prop :=
  ν < sInf {1 + δ - a p - b q + min (a p / q) (b q / p) |
    (p : ℕ) (q : ℕ) (_ : p ∈ Ioc 1 d) (_ : q ∈ Ioc 1 d)}

variable
  (hdab : DeterminantBound d δ ν a b)
  (hdac : DeterminantBound d δ ν a c)
  (hdbc : DeterminantBound d δ ν b c)

section

-- KEEP THIS, it might be relevant for lean4#4615
-- lemma determinantBound_set_finite :
--     {1 + δ - a p - b q + min (a p / q) (b q / p) |
--       (p : ℕ) (q : ℕ) (_ : p ∈ Ioc 1 d) (_ : q ∈ Ioc 1 d)}.Finite := by
--   have :
--       {1 + δ - a p - b q + min (a p / q) (b q / p) |
--         (p : ℕ) (q : ℕ) (_ : p ∈ Ioc 1 d) (_ : q ∈ Ioc 1 d)} =
--       Set.image2 (fun p q ↦ 1 + δ - a p - b q + min (a p / q) (b q / p)) (Ioc 1 d) (Ioc 1 d) := by
--     ext x
--     simp? [- mem_Ioc]
--     simp only [exists_prop, exists_and_left, mem_setOf_eq, mem_image2]
--   sorry

lemma determinantBound_set_finite :
    {1 + δ - a p - b q + min (a p / q) (b q / p) |
      (p : ℕ) (q : ℕ) (_ : p ∈ Ioc 1 d) (_ : q ∈ Ioc 1 d)}.Finite := by
  have :
      {1 + δ - a p - b q + min (a p / q) (b q / p) |
        (p : ℕ) (q : ℕ) (_ : p ∈ Ioc 1 d) (_ : q ∈ Ioc 1 d)} =
      Set.image2 (fun p q ↦ 1 + δ - a p - b q + min (a p / q) (b q / p)) (Ioc 1 d) (Ioc 1 d) := by
    ext x
    simp only [exists_prop, exists_and_left, mem_setOf_eq, mem_image2]
  exact this ▸ Set.Finite.image2 _ (finite_Ioc 1 d) (finite_Ioc 1 d)

include hdab

lemma DeterminantBound.symm : DeterminantBound d δ ν b a := by
  refine hdab.trans_eq ?_
  congr! 3 with x
  constructor
  all_goals
    rintro ⟨p, q, hp, hq, rfl⟩
    refine ⟨q, p, hq, hp, ?_⟩
    rw [inf_comm]
    ring

include ha hdac

/-- A particular application of the determinant bound used in subcase 2.1 -/
lemma DeterminantBound.application (hd : 4 ≤ d) (M : ℝ)
    (hM : M = sSup {max (b i) (c i) | i ∈ Icc 4 d}) :
    ν < 1 + δ - a 3 - M + min (a 3 / 4) (M / 3) := by
  have hM' : M ∈ {max (b i) (c i) | i ∈ Icc 4 d} := by
    rw [hM]
    exact ((nonempty_Icc.2 hd).image _).csSup_mem ((finite_Icc 4 d).image _)
  obtain ⟨i, ⟨hi₁, hi₂⟩, hM'⟩ := hM'
  wlog hbc : c i ≤ b i generalizing b c
  · exact this hdac hdab (by simp [hM, max_comm]) (by simp [hM', max_comm]) (le_of_not_le hbc)
  replace hM' : M = b i := by simp [← hM', hbc]
  refine hdab.trans_le ?_
  refine csInf_le_of_le determinantBound_set_finite.bddBelow
    ⟨3, i, by simp; omega, by simp; omega, rfl⟩ ?_
  simp only [hM']
  gcongr _ + min (_ / ?_) _
  · exact ha.nonneg 3
  · simpa

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

def S (a b c : ℕ → ℝ) (i : ℕ) := a i + b i + c i
local notation "s" => S a b c

variable (a b c) in
lemma s_apply (i : ℕ) : s i = a i + b i + c i := rfl

include ha hb hc in
lemma s_nonneg (i : ℕ) : 0 ≤ s i :=
  add_nonneg (add_nonneg (ha.nonneg _) (hb.nonneg _)) (hc.nonneg _)

include ha hb hc in
lemma s_zero : s 0 = 0 := by
  simp [s_apply, ha.zero, hb.zero, hc.zero]

lemma s_rotate : S b c a = s := by ext i; simp only [s_apply]; ring
lemma s_left_comm : S b a c = s := by ext i; simp only [s_apply]; ring
lemma s_right_comm : S a c b = s := by ext i; simp only [s_apply]; ring

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

lemma GeometryBound.left_comm : GeometryBound d δ ν b a c := by
  refine hg.trans_eq ?_
  congr! 4 with x
  constructor
  all_goals
    rintro ⟨I, hI, I', hI', I'', hI'', rfl⟩
    exact ⟨I', hI', I, hI, I'', hI'', by ring_nf⟩

lemma GeometryBound.right_comm : GeometryBound d δ ν a c b := by
  refine hg.trans_eq ?_
  congr! 4 with x
  constructor
  all_goals
    rintro ⟨I, hI, I', hI', I'', hI'', rfl⟩
    exact ⟨I, hI, I'', hI'', I', hI', by ring_nf⟩

lemma GeometryBound.rotate : GeometryBound d δ ν b c a := hg.left_comm.right_comm

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
lemma bound_4_point_17 (τ : ℝ) {j : ℕ} (hτ : τ ∈ SubSums j a b c) (hν : 0.66 < ν)
    (hj : j ∈ Icc 3 d) :
    τ ∉ Icc (0.34 - s 1 - s 2 + δ) ((0.66 - s 2 - δ) / (j - 1)) := by
  have h₁ := (hg.subSums j hj hτ).1
  contrapose! h₁
  simp only [mem_Icc] at h₁
  rw [← max_sub_sub_right, ← max_add_add_left, max_le_iff]
  norm_num1 at *
  constructor
  · linarith
  · have : 0 < (j - 1 : ℝ) := by
      simp only [mem_Icc] at hj
      simp
      omega
    rw [le_div_iff₀ this] at h₁
    linarith

include hg in
lemma bound_4_point_17_3 (τ : ℝ) (hτ : τ ∈ SubSums 3 a b c) (hν : 0.66 < ν) (hd : 3 ≤ d) :
    τ ∉ Icc (0.34 - s 1 - s 2 + δ) (0.33 - 1 / 2 * s 2 - 1 / 2 * δ) := by
  have := bound_4_point_17 hg τ hτ hν (by simp [hd])
  convert this using 3
  ring

include hg in
lemma bound_4_point_18_aux (τ : ℝ) (hτ : τ ∈ SubSums 3 a b c) (hν : 0.66 < ν) (hd : 3 ≤ d) :
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
lemma bound_4_point_18 (τ : ℝ) (hτ : τ ∈ SubSums 3 a b c) (hd : 3 ≤ d) (hν : 0.66 < ν) :
    τ ∉ Icc (0.34 - s 1 - s 2 + δ) (0.33 - 1 / 2 * s 2 - 1 / 2 * δ) ∪
        Icc (0.34 - s 1 + δ) (0.33 - 1 / 2 * δ) := by
  simp only [mem_union, not_or]
  exact ⟨bound_4_point_17_3 hg τ hτ hν hd, bound_4_point_18_aux hg τ hτ hν hd⟩

include ha in
lemma bound_4_point_19_first (hd : 3 ≤ d) :
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
lemma bound_4_point_19_second (hd : 4 ≤ d) :
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
lemma bound_4_point_20 (hd : 3 ≤ d) :
    1 - 4 * δₛ - 3 * s 1 - 2 * s 2 ≤ s 3 := by
  simp only [δₛ_eq, s_apply]
  linear_combination
    bound_4_point_19_first ha hd + bound_4_point_19_first hb hd + bound_4_point_19_first hc hd

include ha hb hc in
lemma bound_4_point_21 (hd : 4 ≤ d) :
    1 - (5 / 2) * δₛ - 2 * s 1 - (3 / 2) * s 2 - 1 / 2 * s 4 ≤ s 3 := by
  simp only [δₛ_eq, s_apply]
  linear_combination
    bound_4_point_19_second ha hd + bound_4_point_19_second hb hd + bound_4_point_19_second hc hd

include ha hb hc htab htac htbc hg in
lemma bound_4_point_22 (hν : 0.66 < ν) (hs₂ : 0.3 ≤ s 2) (hδ : δ ≤ 0.06) (hd : 2 ≤ d) :
    s 1 ≤ 0.04 + δ := by
  linear_combination bound_4_point_15 ha hb hc htab htac htbc hg hδ hν hd + hs₂

include ha hb hc htab htac htbc in
lemma case_1_helper (hν : 0.66 < ν) (hs₂ : 0.3 ≤ s 2) (hd : 4 ≤ d) :
    s 4 < 0.21 + 3 / 2 * δ := by
  linear_combination bound_4_point_14_two_four ha hb hc htab htac htbc hd hν + hs₂

macro "hack" : tactic => do `(tactic | (ring_nf; apply le_refl))

include ha hb hc h43ab h43ac h43bc hg htab htac htbc hg in
lemma subcase_1_point_1
    (hd : 4 ≤ d)
    (hν : 0.66 < ν)
    (hδ : δ ≤ 0.003)
    (hcb : c 3 ≤ b 3)
    (hs₂ : 0.3 ≤ s 2)
    (hε : ε ≤ 1 / 10000)
    (hε₀ : 0 < ε)
    (hb₃ : b 3 ≤ 0.34 - s 1 - s 2 + δ) :
    False := by
  -- We have an upper bound on b₃ + c₃
  have h₁ : b 3 + c 3 ≤ 0.33 - 1 / 2 * s 2 - 1 / 2 * δ := by
    linear_combination hcb + 2 * hb₃ + 2 * s_nonneg ha hb hc 1 + 3 / 2 * hs₂ + 5 / 2 * hδ
  have hbcs : b 3 + c 3 ∈ SubSums 3 a b c := by simp [SubSums]
  -- From 4.17, the upper bound strengthens
  have h₂ : b 3 + c 3 < 0.34 - s 1 - s 2 + δ := by
    simpa [h₁.not_lt, -one_div] using bound_4_point_17_3 hg (b 3 + c 3) hbcs hν (by omega)
  -- Collect applications of earlier inequalities
  have h_4_20 : 1 - 5 / 2 * δₛ - 2 * s 1 - 3 / 2 * s 2 - 1 / 2 * s 4 ≤ s 3 :=
    bound_4_point_21 ha hb hc hd
  have h_4_21 : s 1 ≤ 0.04 + δ :=
    bound_4_point_22 ha hb hc htab htac htbc hg hν hs₂ (by linear_combination hδ) (by omega)
  have h_4_14 : s 2 + s 4 < 0.51 + 1.5 * δ :=
    bound_4_point_14_two_four ha hb hc htab htac htbc hd hν

  -- Combine the above facts to deduce a lower bound on a₃
  have h₃ : 0.365 - 5 / 2 * δₛ - 11 / 4 * δ ≤ a 3 := calc
    _ ≤ s 3 - (b 3 + c 3) := by
      linear_combination h_4_20 + h_4_21 + (1 / 2) * h_4_14 + h₂
    _ = a 3 := by simp [s_apply]

  -- We have a simple upper bound on a₃ in terms of δₐ
  have h₄ : a 3 ≤ 1 / 3 - δ_ d a := calc
    a 3 ≤ ∑ i ≤ d, a i := Finset.single_le_sum (fun i hi ↦ ha.nonneg i) (by simp; omega)
    _ = 1 / 3 - δ_ d a := sum_eq_δ_ _ _

  have i : δₛ = δ_ d a + δ_ d b + δ_ d c := by simp [δₛ_eq]
  -- Combining the bounds on a₃, we derive the following inequality
  replace h₄ : 0.365 - 1 / 3 ≤ 3 / 2 * δₛ + δ_ d b + δ_ d c + 11 / 4 * δ := by
    linear_combination h₃ + h₄ + i

  -- But this inequality is easily contradicted by 4.8 and 4.10
  have h_4_8 := bound_4_point_8 h43bc
  have h_4_10 := bound_4_point_10_upper hε₀ (by linear_combination hε) h43ab h43ac h43bc
  have : ε ^ 2 ≤ ε := by nlinarith only [hε₀, hε]

  have : 3 / 2 * δₛ + δ_ d b + δ_ d c + 11 / 4 * δ < 0.365 - 1 / 3 := by
    linear_combination (3 / 2) * h_4_10 + h_4_8 + this + (11 / 4) * hδ + (5 / 2) * hε

  exact h₄.not_lt this

include hg in
lemma bound_4_point_23
    (hd : 3 ≤ d)
    (hν : 0.66 < ν)
    (hb₃ : 0.34 - s 1 - s 2 + δ < b 3) :
    0.33 - 1 / 2 * s 2 - 1 / 2 * δ < b 3 := by
  have hbcs : b 3 ∈ SubSums 3 a b c := by simp [SubSums]
  simpa [hb₃.le] using bound_4_point_17_3 hg _ hbcs hν (by omega)

include ha hb hc h45b hg htab htac htbc in
lemma b4_bound
    (hd : 4 ≤ d) (hν : 0.66 < ν) (hb₃ : 0.34 - s 1 - s 2 + δ < b 3) (hε₀ : 0 < ε) (hδ : δ ≤ 0.003)
    (hε : ε ≤ 1 / 10000) :
    b 4 < (0.66 - s 2 - δ) / 3 := by
  have h₁ : b 1 ≤ s 1 := by
    rw [s_apply]
    linear_combination ha.nonneg 1 + hc.nonneg 1
  have h₂ : s 1 ≤ 0.34 - s 2 + δ := by
    linear_combination bound_4_point_15 ha hb hc htab htac htbc hg
      (by linear_combination hδ) hν (by omega)
  have h₃ : ∑ i ∈ Finset.Icc 4 d, (i - 2) * b i ≤ 1 / 3 - b 3 + b 1 + 2 * δ_ d b := by
    have : b 3 + ∑ i ∈ Finset.Icc 4 d, (i - 2) * b i = ∑ i ∈ Finset.Icc 3 d, (i - 2) * b i := by
      rw [Finset.sum_Icc_succ_bot (show 3 ≤ d by omega)]
      norm_num
    linear_combination bound_4_point_11_3 hb (by omega) + this
  have h₄ := bound_4_point_9_upper hε₀ b h45b
  have h₅ := bound_4_point_23 hg (by omega) hν hb₃
  have h₆ : s 2 ≤ 0.34 + δ := by
    have : 0 ≤ s 1 := s_nonneg ha hb hc 1
    linear_combination bound_4_point_15 ha hb hc htab htac htbc hg
      (by linear_combination hδ) hν (by omega) + this
  calc b 4 ≤ 1 / 2 * (∑ i ∈ Finset.Icc 4 d, (i - 2) * b i) := by
        rw [Finset.mul_sum]
        refine (Finset.single_le_sum (a := 4) ?_ (by simp [hd])).trans' ?_
        · intro i hi
          simp only [Finset.mem_Icc] at hi
          have : 0 ≤ (i - 2 : ℝ) := by simp; omega
          have := hb.nonneg i
          positivity
        · norm_num
          linarith
    _ ≤ 1 / 2 * (1 / 3 + b 1 - b 3 + 2 * δ_ d b) := by linear_combination 1 / 2 * h₃
    _ ≤ 1 / 2 * (1 / 3 + 0.34 - s 2 + δ - (0.33 - 1 / 2 * s 2 - 1 / 2 * δ) + 2 * δ_ d b) := by
      linear_combination 1 / 2 * h₁ + 1 / 2 * h₂ + 1 / 2 * h₅
    _ ≤ 1 / 2 * (1 / 3 + 0.01 - 1 / 2 * s 2 + 7 / 2 * δ + 2 / 75 + 2 * ε) := by
      linear_combination h₄
    _ < 1 / 3 * (0.66 - s 2 - δ) := by
      linear_combination 1 / 12 * h₆ + (13 / 6) * hδ + hε
    _ = (0.66 - s 2 - δ) / 3 := by ring

include ha hb hc h45b hg htab htac htbc in
lemma b5_bound
    (hd : 5 ≤ d) (hν : 0.66 < ν) (hb₃ : 0.34 - s 1 - s 2 + δ < b 3) (hε₀ : 0 < ε) (hδ : δ ≤ 0.003)
    (hε : ε ≤ 1 / 10000) :
    b 5 < (0.66 - s 2 - δ) / 4 := by
  have h₁ : b 1 ≤ s 1 := by
    rw [s_apply]
    linear_combination ha.nonneg 1 + hc.nonneg 1
  have h₂ : s 1 ≤ 0.34 - s 2 + δ := by
    linear_combination bound_4_point_15 ha hb hc htab htac htbc hg
      (by linear_combination hδ) hν (by omega)
  have h₃ : ∑ i ∈ Finset.Icc 4 d, (i - 2) * b i ≤ 1 / 3 - b 3 + b 1 + 2 * δ_ d b := by
    have : b 3 + ∑ i ∈ Finset.Icc 4 d, (i - 2) * b i = ∑ i ∈ Finset.Icc 3 d, (i - 2) * b i := by
      rw [Finset.sum_Icc_succ_bot (show 3 ≤ d by omega)]
      norm_num
    linear_combination bound_4_point_11_3 hb (by omega) + this
  have h₄ := bound_4_point_9_upper hε₀ b h45b
  have h₅ := bound_4_point_23 hg (by omega) hν hb₃
  have h₆ : s 2 ≤ 0.34 + δ := by
    have : 0 ≤ s 1 := s_nonneg ha hb hc 1
    linear_combination
      bound_4_point_15 ha hb hc htab htac htbc hg (by linear_combination hδ) hν (by omega) + this
  calc b 5 ≤ 1 / 3 * (∑ i ∈ Finset.Icc 4 d, (i - 2) * b i) := by
        rw [Finset.mul_sum]
        refine (Finset.single_le_sum (a := 5) ?_ (by simp; omega)).trans' ?_
        · intro i hi
          simp only [Finset.mem_Icc] at hi
          have : 0 ≤ (i - 2 : ℝ) := by simp; omega
          have := hb.nonneg i
          positivity
        · norm_num
          linarith
    _ ≤ 1 / 3 * (1 / 3 + b 1 - b 3 + 2 * δ_ d b) := by linear_combination 1 / 3 * h₃
    _ ≤ 1 / 3 * (1 / 3 + 0.34 - s 2 + δ - (0.33 - 1 / 2 * s 2 - 1 / 2 * δ) + 2 * δ_ d b) := by
      linear_combination 1 / 3 * h₁ + 1 / 3 * h₂ + 1 / 3 * h₅
    _ ≤ 1 / 3 * (1 / 3 + 0.01 - 1 / 2 * s 2 + 7 / 2 * δ + 2 / 75 + 2 * ε) := by
      linear_combination 2 / 3 * h₄
    _ < 1 / 4 * (0.66 - s 2 - δ) := by
      linear_combination 1 / 12 * h₆ + (3 / 2) * hδ + (2 / 3) * hε
    _ = (0.66 - s 2 - δ) / 4 := by ring

include ha hb hc h45b hg htab htac htbc in
lemma b6_bound
    (hd : 6 ≤ d) (hν : 0.66 < ν) (hb₃ : 0.34 - s 1 - s 2 + δ < b 3) (hε₀ : 0 < ε) (hδ : δ ≤ 0.003)
    (hε : ε ≤ 1 / 10000) :
    b 6 < (0.66 - s 2 - δ) / 5 := by
  have h₁ : b 1 ≤ s 1 := by
    rw [s_apply]
    linear_combination ha.nonneg 1 + hc.nonneg 1
  have h₂ : s 1 ≤ 0.34 - s 2 + δ := by
    linear_combination bound_4_point_15 ha hb hc htab htac htbc hg
      (by linear_combination hδ) hν (by omega)
  have h₃ : ∑ i ∈ Finset.Icc 4 d, (i - 2) * b i ≤ 1 / 3 - b 3 + b 1 + 2 * δ_ d b := by
    have : b 3 + ∑ i ∈ Finset.Icc 4 d, (i - 2) * b i = ∑ i ∈ Finset.Icc 3 d, (i - 2) * b i := by
      rw [Finset.sum_Icc_succ_bot (show 3 ≤ d by omega)]
      norm_num
    linear_combination bound_4_point_11_3 hb (by omega) + this
  have h₄ := bound_4_point_9_upper hε₀ b h45b
  have h₅ := bound_4_point_23 hg (by omega) hν hb₃
  have h₆ : s 2 ≤ 0.34 + δ := by
    have : 0 ≤ s 1 := s_nonneg ha hb hc 1
    linear_combination bound_4_point_15 ha hb hc htab htac htbc hg
      (by linear_combination hδ) hν (by omega) + this
  calc b 6 ≤ 1 / 4 * (∑ i ∈ Finset.Icc 4 d, (i - 2) * b i) := by
        rw [Finset.mul_sum]
        refine (Finset.single_le_sum (a := 6) ?_ (by simp; omega)).trans' ?_
        · intro i hi
          simp only [Finset.mem_Icc] at hi
          have : 0 ≤ (i - 2 : ℝ) := by simp; omega
          have := hb.nonneg i
          positivity
        · norm_num
          linarith
    _ ≤ 1 / 4 * (1 / 3 + b 1 - b 3 + 2 * δ_ d b) := by linear_combination 1 / 4 * h₃
    _ ≤ 1 / 4 * (1 / 3 + 0.34 - s 2 + δ - (0.33 - 1 / 2 * s 2 - 1 / 2 * δ) + 2 * δ_ d b) := by
      linear_combination 1 / 4 * h₁ + 1 / 4 * h₂ + 1 / 4 * h₅
    _ ≤ 1 / 4 * (1 / 3 + 0.01 - 1 / 2 * s 2 + 7 / 2 * δ + 2 / 75 + 2 * ε) := by
      linear_combination 1 / 2 * h₄
    _ < 1 / 5 * (0.66 - s 2 - δ) := by
      linear_combination 3 / 40 * h₆ + (23 / 20) * hδ + (1 / 2) * hε
    _ = (0.66 - s 2 - δ) / 5 := by ring

include ha hb hc h45a hg htab htac htbc in
lemma a4_bound
    (hd : 4 ≤ d) (hν : 0.66 < ν) (hb₃ : 0.34 - s 1 - s 2 + δ < b 3) (hε₀ : 0 < ε) (hδ : δ ≤ 0.003)
    (hε : ε ≤ 1 / 10000) (hba : b 3 ≤ a 3) :
    a 4 < (0.66 - s 2 - δ) / 3 := by
  refine (b4_bound hb ha hc h45a htab.symm htbc htac hg.left_comm hd hν ?_ hε₀ hδ hε).trans_le ?_
  · rw [s_left_comm]
    exact hb₃.trans_le hba
  · rw [s_left_comm]

include ha hb hc h45a hg htab htac htbc in
lemma a5_bound
    (hd : 5 ≤ d) (hν : 0.66 < ν) (hb₃ : 0.34 - s 1 - s 2 + δ < b 3) (hε₀ : 0 < ε) (hδ : δ ≤ 0.003)
    (hε : ε ≤ 1 / 10000) (hba : b 3 ≤ a 3) :
    a 5 < (0.66 - s 2 - δ) / 4 := by
  refine (b5_bound hb ha hc h45a htab.symm htbc htac hg.left_comm hd hν ?_ hε₀ hδ hε).trans_le ?_
  · rw [s_left_comm]
    exact hb₃.trans_le hba
  · rw [s_left_comm]

include ha hb hc h45a hg htab htac htbc in
lemma a6_bound
    (hd : 6 ≤ d) (hν : 0.66 < ν) (hb₃ : 0.34 - s 1 - s 2 + δ < b 3) (hε₀ : 0 < ε) (hδ : δ ≤ 0.003)
    (hε : ε ≤ 1 / 10000) (hba : b 3 ≤ a 3) :
    a 6 < (0.66 - s 2 - δ) / 5 := by
  refine (b6_bound hb ha hc h45a htab.symm htbc htac hg.left_comm hd hν ?_ hε₀ hδ hε).trans_le ?_
  · rw [s_left_comm]
    exact hb₃.trans_le hba
  · rw [s_left_comm]

include ha hb hc h45a h45b hg htab htac htbc in
lemma self_improve_bounds
    (hd : 6 ≤ d) (hν : 0.66 < ν) (hb₃ : 0.34 - s 1 - s 2 + δ < b 3) (hε₀ : 0 < ε) (hδ : δ ≤ 0.003)
    (hε : ε ≤ 1 / 10000) (hba : b 3 ≤ a 3) :
    (max (a 4) (b 4) < 0.34 - s 1 - s 2 + δ) ∧
    (max (a 5) (b 5) < 0.34 - s 1 - s 2 + δ) ∧
    (max (a 6) (b 6) < 0.34 - s 1 - s 2 + δ) := by
  simp only [max_lt_iff]
  refine ⟨?_, ?_, ?_⟩
  · constructor
    · have h₁ := bound_4_point_17 (j := 4) hg (a 4) (by simp [SubSums]) hν (by simp; omega)
      have h₂ := a4_bound ha hb hc h45a htab htac htbc hg (by omega) hν hb₃ hε₀ hδ hε hba
      norm_num only [Nat.cast_ofNat, mem_Icc, not_and', not_le] at h₁ h₂
      specialize h₁ h₂.le
      norm_num1
      exact h₁
    · have h₁ := bound_4_point_17 (j := 4) hg (b 4) (by simp [SubSums]) hν (by simp; omega)
      have h₂ := b4_bound ha hb hc h45b htab htac htbc hg (by omega) hν hb₃ hε₀ hδ hε
      norm_num only [Nat.cast_ofNat, mem_Icc, not_and', not_le] at h₁ h₂
      specialize h₁ h₂.le
      norm_num1
      exact h₁
  · constructor
    · have h₁ := bound_4_point_17 (j := 5) hg (a 5) (by simp [SubSums]) hν (by simp; omega)
      have h₂ := a5_bound ha hb hc h45a htab htac htbc hg (by omega) hν hb₃ hε₀ hδ hε hba
      norm_num only [Nat.cast_ofNat, mem_Icc, not_and', not_le] at h₁ h₂
      specialize h₁ h₂.le
      norm_num1
      exact h₁
    · have h₁ := bound_4_point_17 (j := 5) hg (b 5) (by simp [SubSums]) hν (by simp; omega)
      have h₂ := b5_bound ha hb hc h45b htab htac htbc hg (by omega) hν hb₃ hε₀ hδ hε
      norm_num only [Nat.cast_ofNat, mem_Icc, not_and', not_le] at h₁ h₂
      specialize h₁ h₂.le
      norm_num1
      exact h₁
  · constructor
    · have h₁ := bound_4_point_17 (j := 6) hg (a 6) (by simp [SubSums]) hν (by simp; omega)
      have h₂ := a6_bound ha hb hc h45a htab htac htbc hg (by omega) hν hb₃ hε₀ hδ hε hba
      norm_num only [Nat.cast_ofNat, mem_Icc, not_and', not_le] at h₁ h₂
      specialize h₁ h₂.le
      norm_num1
      exact h₁
    · have h₁ := bound_4_point_17 (j := 6) hg (b 6) (by simp [SubSums]) hν (by simp; omega)
      have h₂ := b6_bound ha hb hc h45b htab htac htbc hg (by omega) hν hb₃ hε₀ hδ hε
      norm_num only [Nat.cast_ofNat, mem_Icc, not_and', not_le] at h₁ h₂
      specialize h₁ h₂.le
      norm_num1
      exact h₁

lemma test {α : Type*} [AddCommMonoid α] {a b : ℕ} {f : ℕ → α} (hab : a ≤ b) :
    ∑ i ≤ a, f i + ∑ i ∈ Finset.Icc (a + 1) b, f i = ∑ i ≤ b, f i := by
  rw [Nat.Iic_eq_Icc, Nat.Iic_eq_Icc, ← Finset.sum_union, Nat.Icc_union_Icc_eq_Icc (by omega) hab]
  simp +contextual [Finset.disjoint_left, Nat.add_one_le_iff]

include ha hb hfab in
lemma apply_fourier
    (hd : 6 ≤ d) :
    2 * ν - 1 - δ <
      2 / 3 - (δ_ d a + δ_ d b) - ∑ i ≤ 6 with i ≠ 2, min (a i) (b i) - (a 2 + b 2) := calc
  2 * ν - 1 - δ < (∑ i ≤ d, max (a i) (b i) - max (a 2) (b 2)) := by
    linear_combination 2 * hfab.two (by omega)
  _ = ∑ i ≤ 6, max (a i) (b i) + ∑ i ∈ Finset.Icc (6 + 1) d, max (a i) (b i) - max (a 2) (b 2) := by
    rw [test hd]
  _ ≤ ∑ i ≤ 6, max (a i) (b i) + ∑ i ∈ Finset.Icc (6 + 1) d, (a i + b i) - max (a 2) (b 2) := by
    gcongr; exact max_le_add_of_nonneg (ha.nonneg _) (hb.nonneg _)
  _ = ∑ i ≤ 6, (max (a i) (b i) - (a i + b i)) - max (a 2) (b 2) + 2 / 3 - (δ_ d a + δ_ d b) := by
    simp only [δ_, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← test hd]; ring
  _ = ∑ i ≤ 6 with i ≠ 2, (max (a i) (b i) - (a i + b i)) + (max (a 2) (b 2) - (a 2 + b 2))
      - max (a 2) (b 2) + 2 / 3 - (δ_ d a + δ_ d b) := by
    rw [Finset.filter_ne', Finset.sum_erase_add]; simp
  _ = ∑ i ≤ 6 with i ≠ 2, (max (a i) (b i) - (a i + b i)) - (a 2 + b 2) +
      2 / 3 - (δ_ d a + δ_ d b) := by ring
  _ = ∑ i ≤ 6 with i ≠ 2, (- min (a i) (b i)) - (a 2 + b 2) + 2 / 3 - (δ_ d a + δ_ d b) := by
    congr! 4 with i hi; rw [← min_add_max]; ring
  _ = _ := by rw [Finset.sum_neg_distrib]; ring

include ha in
lemma two_bound (hd : 6 ≤ d) :
    4 / 15 - 1 / 5 * ∑ i ≤ 6 with i ≠ 2, (7 - i) * a i - 7 / 5 * δ_ d a ≤ a 2 := by
  suffices 7 * ∑ i ≤ d, a i - (∑ i ≤ 6 with i ≠ 2, (7 - i) * a i + (7 - (2 : ℕ)) * a 2) ≤ 1 by
    linear_combination 1 / 5 * this - 7 / 5 * sum_eq_δ_ d a
  rw [Finset.filter_ne', Finset.sum_erase_add _ _ (by simp)]
  calc
    _ = ∑ i ≤ 6, i * a i + ∑ i ∈ Finset.Icc 7 d, 7 * a i := by
      rw [Finset.mul_sum, ← test hd]
      simp only [sub_mul, Finset.sum_sub_distrib]
      ring
    _ ≤ ∑ i ≤ 6, i * a i + ∑ i ∈ Finset.Icc 7 d, i * a i := by
      gcongr with i hi
      · exact ha.nonneg i
      · simp only [Finset.mem_Icc] at hi
        exact mod_cast hi.1
    _ = ∑ i ≤ d, i * a i := by rw [test hd]
    _ ≤ 1 := ha.sum_bound

lemma summation_range_eq : (Finset.Iic 6).filter (· ≠ 2) = {0, 1, 3, 4, 5, 6} := by
  ext i; simp; omega

include ha hb hfab in
lemma bound_4_point_24 (hd : 6 ≤ d) (hba : b 3 ≤ a 3) :
    2 * ν - 1 - δ < 2 / 15 + 2 / 5 * (δ_ d a + δ_ d b) + 1 / 5 *
      (6 * max (a 1) (b 1) + min (a 1) (b 1) + 4 * a 3 - b 3 +
        3 * max (a 4) (b 4) + 2 * max (a 5) (b 5) + max (a 6) (b 6)) :=
  calc _ < 2 / 3 - (δ_ d a + δ_ d b) - ∑ i ≤ 6 with i ≠ 2, min (a i) (b i) - (a 2 + b 2) :=
      apply_fourier ha hb hfab hd
    _ ≤ 2 / 15 + 2 / 5 * (δ_ d a + δ_ d b) - ∑ i ≤ 6 with i ≠ 2, min (a i) (b i) +
        (1 / 5 * ∑ i ≤ 6 with i ≠ 2, (7 - i) * a i +
         1 / 5 * ∑ i ≤ 6 with i ≠ 2, (7 - i) * b i) := by
      linear_combination two_bound ha hd + two_bound hb hd
    _ = 2 / 15 + 2 / 5 * (δ_ d a + δ_ d b) - ∑ i ≤ 6 with i ≠ 2, min (a i) (b i) +
        1 / 5 * ∑ i ≤ 6 with i ≠ 2, (7 - i) * (a i + b i) := by
      simp only [mul_add, Finset.sum_add_distrib]
    _ = 2 / 15 + 2 / 5 * (δ_ d a + δ_ d b) - ∑ i ≤ 6 with i ≠ 2, min (a i) (b i) +
        1 / 5 * ∑ i ≤ 6 with i ≠ 2, (7 - i) * (min (a i) (b i) + max (a i) (b i)) := by
      simp only [min_add_max]
    _ = 2 / 15 + 2 / 5 * (δ_ d a + δ_ d b) + 1 / 5 * ∑ i ≤ 6 with i ≠ 2,
        ((7 - i) * (min (a i) (b i) + max (a i) (b i)) - 5 * min (a i) (b i)) := by
      simp only [Finset.sum_sub_distrib, mul_sub, ← Finset.mul_sum]
      ring
    _ ≤ _ := by
      simp only [summation_range_eq]
      have h4 : 0 ≤ min (a 4) (b 4) := le_min (ha.nonneg _) (hb.nonneg _)
      have h5 : 0 ≤ min (a 5) (b 5) := le_min (ha.nonneg _) (hb.nonneg _)
      have h6 : 0 ≤ min (a 6) (b 6) := le_min (ha.nonneg _) (hb.nonneg _)
      simp [ha.zero, hb.zero, -min_add_max, hba]
      linear_combination 2 * h4 + 3 * h5 + 4 * h6

include ha hb htab hg in
lemma subcase_1_point_2_aux (hd : 3 ≤ d) (hν : 0.66 < ν) (hb₃ : 0.34 - s 1 - s 2 + δ < b 3) :
    4 * a 3 - b 3 ≤ 5 / 2 * s 2 - 0.29 + 13 / 2 * δ := by
  have h₁ := bound_4_point_12 ha hb htab 3 (by simpa) hν
  linear_combination 4 * h₁ + 5 * bound_4_point_23 hg hd hν hb₃

include ha hb hc h43ab h45a h45b hg htab htac htbc hfab in
lemma subcase_1_point_2
    (hd : 6 ≤ d) (hν : 0.66 < ν) (hba : b 3 ≤ a 3) (hs₂ : 0.3 ≤ s 2)
    (hb₃ : 0.34 - s 1 - s 2 + δ < b 3) (hε₀ : 0 < ε) (hδ : δ ≤ 0.003) (hε : ε ≤ 1 / 10000) :
    False := by
  have h₁ : 6 * max (a 1) (b 1) + min (a 1) (b 1) ≤ 6 * s 1 := by
    linear_combination min_add_max (a 1) (b 1)
                     + 5 * max_le_add_of_nonneg (ha.nonneg 1) (hb.nonneg 1)
                     - 6 * s_apply a b c 1 + 6 * hc.nonneg 1
  have h₂ := bound_4_point_8 h43ab
  have h₃ : ε ^ 2 ≤ 1 / 4000 := by nlinarith only [hε₀, hε]
  obtain ⟨h₄, h₅, h₆⟩ :=
    self_improve_bounds ha hb hc h45a h45b htab htac htbc hg hd hν hb₃ hε₀ hδ hε hba
  have : 2 * ν - 1 - δ < (5 / 2) * δ + 0.2761 := calc
    2 * ν - 1 - δ < _ := bound_4_point_24 ha hb hfab hd hba
    _ ≤ 0.334 + 1 / 5 * (4 * a 3 - b 3 + 6 * δ + 2 * ε ^ 2) - 1 / 2 * s 2 := by
      linear_combination 1 / 5 * (h₁ + 3 * h₄ + 2 * h₅ + h₆ + 2 * h₂ + 7 / 2 * hs₂)
    _ ≤ 0.276 + δ * (5 / 2) + ε ^ 2 * (2 / 5) := by
      linear_combination 1 / 5 * subcase_1_point_2_aux ha hb htab hg (by omega) hν hb₃
    _ ≤ (5 / 2) * δ + 0.2761 := by linear_combination (2 / 5) * h₃
  have : ν < 0.66 := by linear_combination 1 / 2 * this + (7 / 4) * hδ
  exact this.not_le (by linear_combination hν)

include ha hb hc h43ab h43ac h43bc h45a h45b hg htab htac htbc hfab in
lemma case_1
    (hd : 6 ≤ d) (hν : 0.66 < ν) (hs₂ : 0.3 ≤ s 2) (hδ : δ ≤ 0.003)
    (hε₀ : 0 < ε) (hε : ε ≤ 1 / 10000)
    (hcb : c 3 ≤ b 3) (hba : b 3 ≤ a 3) :
    False := by
  obtain hb₃ | hb₃ := le_or_lt (b 3) (0.34 - s 1 - s 2 + δ)
  · exact subcase_1_point_1 ha hb hc h43ab h43ac h43bc htab htac htbc hg (by omega) hν
      (by linear_combination hδ) hcb hs₂ hε hε₀ hb₃
  · exact subcase_1_point_2 ha hb hc h43ab h45a h45b hfab htab htac htbc hg hd hν hba hs₂ hb₃
      hε₀ hδ hε

include ha hb htab in
lemma bound_4_point_25
    (hd : 3 ≤ d)
    (hν : 0.66 < ν)
    (h : b 3 ≤ a 3) :
    b 3 < 0.17 + 1 / 2 * δ := by
  linear_combination 1 / 2 * h + 1 / 2 * bound_4_point_12 ha hb htab 3 (by simp; omega) hν

include ha hb htab hg in
lemma bound_4_point_26_aux
    (hd : 3 ≤ d) (hν : 0.66 < ν) (hs₂ : s 2 < 0.3) (hδ : δ ≤ 0.01)
    (hba : b 3 ≤ a 3) (hcb : c 3 ≤ b 3) :
    b 3 < 0.34 - s 1 - s 2 + δ ∧ c 3 < 0.34 - s 1 - s 2 + δ := by
  have h₁ : b 3 < 0.33 - 1 / 2 * s 2 - 1 / 2 * δ := calc
    b 3 < 0.17 + (1 / 2) * δ := bound_4_point_25 ha hb htab hd hν hba
    _ ≤ 0.33 - 1 / 2 * s 2 - 1 / 2 * δ := by linear_combination 1 / 2 * hs₂ + hδ
  have hb3 : b 3 ∈ SubSums 3 a b c := by simp [SubSums]
  have h₂ : b 3 < 0.34 - s 1 - s 2 + δ := by
    simpa [h₁.not_lt, -one_div] using bound_4_point_17_3 hg _ hb3 hν hd
  have h₃ : c 3 < 0.34 - s 1 - s 2 + δ := hcb.trans_lt h₂
  exact ⟨h₂, h₃⟩

include ha hb hc htab hg in
lemma bound_4_point_26
    (hd : 3 ≤ d) (hν : 0.66 < ν) (hs₂ : s 2 < 0.3) (hδ : δ ≤ 0.01)
    (hba : b 3 ≤ a 3) (hcb : c 3 ≤ b 3) :
    0.32 - 4 * δₛ - s 1 - 2 * δ ≤ a 3 := by
  obtain ⟨h₂, h₃⟩ := bound_4_point_26_aux ha hb htab hg hd hν hs₂ (by linear_combination hδ) hba hcb
  linear_combination h₂ + h₃ + bound_4_point_20 ha hb hc hd + s_apply a b c 3

include ha hdab hdac in
lemma case_2_subcase_1_large_sum
    (hd : 4 ≤ d)
    (hν : 0.66 < ν)
    (hδ : δ ≤ 0.015)
    (h : 0.32 ≤ a 3)
    (hmax : ∃ i ∈ Icc 4 d, 3 / 4 * 0.09 < max (b i) (c i)) :
    False := by
  let M := sSup {x | ∃ i ∈ Icc 4 d, b i ⊔ c i = x}
  have hM : 3 / 4 * 0.09 < M := by
    obtain ⟨i, hi, h⟩ := hmax
    exact lt_csSup_of_lt (Set.Finite.image _ (finite_Icc _ _)).bddAbove ⟨i, hi, rfl⟩ h
  have hdet := hdab.application ha hdac hd M rfl
  have : ν < 0.65 := by
    linear_combination hdet + (min_le_right (a 3 / 4) (M / 3)) + (2 / 3) * hM + h + hδ
  exact (hν.trans this).not_le (by norm_num)

include ha hb hc h43ab h43ac h43bc htab htac htbc hg hdab hdac in
lemma case_2_subcase_1
    (hd : 4 ≤ d)
    (hν : 0.66 < ν)
    (hs₂ : s 2 < 0.3)
    (hδ : δ ≤ 0.015)
    (h : 0.32 ≤ a 3) :
    False := by
  by_cases hmax : ∃ i ∈ Icc 4 d, 3 / 4 * 0.09 < max (b i) (c i)
  · exact case_2_subcase_1_large_sum ha hdab hdac hd hν (by linear_combination hδ) h hmax
  have : ∀ i ∈ Icc 4 d, b i + c i ≤ 0.135 := by
    intro i hi
    have : b i + c i ≤ 2 * max (b i) (c i) := by
      linear_combination le_max_left (b i) (c i) + le_max_right (b i) (c i)
    simp only [not_exists, not_and, not_lt] at hmax
    specialize hmax i hi
    linear_combination this + 2 * hmax
  have : ∑ i ≤ d, (i - 1) * (b i + c i) ≤ 4 / 3 + (δ_ d b + δ_ d c) := calc
    _ = ∑ x ≤ d, x * b x - ∑ x ≤ d, b x + (∑ x ≤ d, x * c x - ∑ x ≤ d, c x) := by
      simp only [mul_add, sub_one_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    _ ≤ _ := by linear_combination hb.sum_bound + hc.sum_bound - sum_eq_δ_ d b - sum_eq_δ_ d c
  sorry

    -- linear_combination
    -- sorry

    -- simp only [mem_Icc, not_exists, not_and, not_lt, and_imp] at hmax

  -- have' := bound_4_point_12 ha hb htab
  -- sorry

#exit

include ha hb hc h43ab h43ac h43bc htab htac htbc hg in
lemma case_2_subcase_2
    (hd : 4 ≤ d)
    (hν : 0.66 < ν)
    (hs₂ : s 2 < 0.3)
    (hδ : δ ≤ 0.01)
    (hε₀ : 0 < ε)
    (hε : ε ≤ 1 / 10000)
    (h : b 3 + c 3 < 0.33 - 1 / 2 * s 2 - 1 / 2 * δ) :
    False := by
  have h₁ : b 3 + c 3 < 0.34 - s 1 - s 2 + δ := by
    have := bound_4_point_17_3 hg (b 3 + c 3) (by simp [SubSums]) hν (by omega)
    contrapose! this
    exact ⟨this, h.le⟩
  suffices h₂ : 0.34 - s 1 + δ < a 3 by
    apply case_2_subcase_1 hν hs₂
    have h₃ := bound_4_point_18_aux hg (a 3) (by simp [SubSums]) hν (by omega)
    contrapose! h₃
    exact ⟨h₂.le, by linear_combination h₃ + 1 / 2 * hδ⟩
  have h421 := bound_4_point_21 ha hb hc hd
  have h410 := bound_4_point_10_upper hε₀ (by linear_combination hε) h43ab h43ac h43bc
  have h414 := bound_4_point_14_two_four ha hb hc htab htac htbc hd hν
  linear_combination s_apply a b c 3 + h₁ +
    h421 + 5 / 2 * h410 + 1 / 2 * h414 + 11 / 4 * hδ + 5 / 2 * hε

include ha hb hc h43ab h43ac h43bc htab htac htbc hg in
lemma case_2_subcase_3
    (hd : 4 ≤ d) (hν : 0.66 < ν) (hs₂ : s 2 < 0.3)
    (hδ : δ ≤ 0.004) (hε₀ : 0 < ε) (hε : ε ≤ 1 / 10000)
    (hba : b 3 ≤ a 3) (hcb : c 3 ≤ b 3)
    (h : 0.73 < 4 * s 1 + 3 * s 2) :
    False := by
  suffices b 3 + c 3 < 0.33 - 1 / 2 * s 2 - 1 / 2 * δ from
    case_2_subcase_2 ha hb hc h43ab h43ac h43bc htab htac htbc hg (by omega) hν hs₂
      (by linear_combination hδ) hε₀ hε this
  obtain ⟨h₁, h₂⟩ := bound_4_point_26_aux ha hb htab hg (by omega) hν hs₂
    (by linear_combination hδ) hba hcb
  linear_combination h₁ + h₂ + 1 / 2 * h + 5 / 2 * hδ

include ha hb hc h43ab h43ac h43bc htab htac htbc hg in
lemma case_2_subcase_4
    (hd : 4 ≤ d)
    (hν : 0.66 < ν)
    (hs₂ : s 2 < 0.3)
    (hδ : δ ≤ 0.004)
    (hε₀ : 0 < ε)
    (hε : ε ≤ 1 / 100000)
    (hba : b 3 ≤ a 3)
    (hcb : c 3 ≤ b 3)
    (h : 4 * s 1 + s 2 < 0.35) :
    False := by
  suffices b 3 + c 3 < 0.33 - 1 / 2 * s 2 - 1 / 2 * δ from
    case_2_subcase_2 ha hb hc h43ab h43ac h43bc htab htac htbc hg (by omega) hν hs₂
      (by linear_combination hδ) hε₀ (by linear_combination hε) this
  have h₁ : b 3 ≤ 0.34 - a 3 + δ := by
    linear_combination bound_4_point_12 ha hb htab 3 (by simp; omega) hν
  have h₂ : c 3 ≤ 0.34 - a 3 + δ := by
    linear_combination bound_4_point_12 ha hc htac 3 (by simp; omega) hν
  have : 0.34 - a 3 + δ < 0.15 - 1 / 4 * s 2 + 3 * δ + 4 * ε := by
    linear_combination
      bound_4_point_26 ha hb hc htab hg (by omega) hν hs₂ (by linear_combination hδ) hba hcb +
      1 / 4 * h + 4 * bound_4_point_10_upper hε₀ (by linear_combination hε) h43ab h43ac h43bc
  linear_combination h₁ + h₂ + 2 * this + 8 * hε + 13 / 2 * hδ

include ha hb hc h43ab h43ac h43bc htab htac htbc hg in
lemma case_2_subcase_5
    (hd : 4 ≤ d)
    (hν : 0.66 < ν)
    (hs₂ : s 2 < 0.3)
    (hδ : δ ≤ 0.003)
    (hε₀ : 0 < ε)
    (hε : ε ≤ 1 / 100000)
    (hba : b 3 ≤ a 3)
    (hcb : c 3 ≤ b 3)
    (h : s 2 ∈ Icc 0.07 0.199) :
    False := by

  suffices b 3 + c 3 < 0.33 - 1 / 2 * s 2 - 1 / 2 * δ from
    case_2_subcase_2 ha hb hc h43ab h43ac h43bc htab htac htbc hg (by omega) hν hs₂
      (by linear_combination hδ) hε₀ (by linear_combination hε) this

  simp only [mem_Icc] at h
  have h426 :=
    bound_4_point_26 ha hb hc htab hg (by omega) hν hs₂ (by linear_combination hδ) hba hcb
  have h410 :=
    bound_4_point_10_upper hε₀ (by linear_combination hε) h43ab h43ac h43bc
  have h₁ : a 3 > 0.34 - s 1 - s 2 + δ := by
    linear_combination h426 + 4 * h410 + h.1 + 3 * hδ + 4 * hε
  replace h₁ : a 3 > 0.33 - 1 / 2 * s 2 - 1 / 2 * δ := by
    have := bound_4_point_17_3 hg (a 3) (by simp [SubSums]) hν (by omega)
    contrapose! this
    exact ⟨h₁.le, this⟩

  have h₂ := bound_4_point_12 ha hb htab 3 (by simp; omega) hν
  have h₃ := bound_4_point_12 ha hc htac 3 (by simp; omega) hν

  linear_combination h₂ + h₃ + 2 * h₁ + (3 / 2) * h.2 + (7 / 2) * hδ

lemma case_2_subcase_6
    (hν : 0.66 < ν)
    (hs₂ : s 2 < 0.3)
    (h : 0.024 < 2 * s 1 - s 2) :
    False := by
  sorry

include ha hb hc h43ab h43ac h43bc htab htac htbc hg in
lemma case_2
    (hd : 4 ≤ d) (hν : 0.66 < ν)
    (hs₂ : s 2 < 0.3) (hδ : δ ≤ 0.003) (hε₀ : 0 < ε) (hε : ε ≤ 1 / 100000)
    (hba : b 3 ≤ a 3) (hcb : c 3 ≤ b 3) :
    False := by
  suffices (0.73 < 4 * s 1 + 3 * s 2) ∨ (4 * s 1 + s 2 < 0.35) ∨
      (s 2 ∈ Icc 0.07 0.199) ∨ (0.024 < 2 * s 1 - s 2) by
    obtain h | h | h | h := this
    · exact case_2_subcase_3 ha hb hc h43ab h43ac h43bc htab htac htbc hg (by omega) hν hs₂
        (by linear_combination hδ) hε₀ (by linear_combination hε) hba hcb h
    · exact case_2_subcase_4 ha hb hc h43ab h43ac h43bc htab htac htbc hg hd hν hs₂
        (by linear_combination hδ) hε₀ hε hba hcb h
    · exact case_2_subcase_5 ha hb hc h43ab h43ac h43bc htab htac htbc hg hd hν hs₂
        (by linear_combination hδ) hε₀ hε hba hcb h
    · exact case_2_subcase_6 hν hs₂ h
  by_contra! h
  simp only [mem_Icc, not_and_or, not_le] at h
  obtain ⟨h₁, h₂, (h₃ | h₃), h₄⟩ := h
  all_goals
    norm_num1 at *
    linarith +splitHypotheses

include ha hb hc h43ab h43ac h43bc h45a h45b hg htab htac htbc hfab in
theorem thm_4_point_3 (hd : 6 ≤ d) (hδ : δ ≤ 0.003) (hε₀ : 0 < ε) (hε : ε ≤ 1 / 100000)
    (hba : b 3 ≤ a 3) (hcb : c 3 ≤ b 3) :
    ν ≤ 0.66 := by
  by_contra! hν
  cases le_or_lt 0.3 (s 2)
  case inl hs₂ =>
    exact case_1 ha hb hc h43ab h43ac h43bc h45a h45b hfab htab htac htbc hg hd hν hs₂
      (by linear_combination hδ) hε₀ (by linear_combination hε) hcb hba
  case inr hs₂ =>
    exact case_2 ha hb hc h43ab h43ac h43bc htab htac htbc hg (by omega) hν hs₂
      (by linear_combination hδ) hε₀ hε hba hcb

end
