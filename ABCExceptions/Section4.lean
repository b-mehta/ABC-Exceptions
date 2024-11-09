import Mathlib

noncomputable section

open Set

variable {d : ℕ} {δ ε ν : ℝ} {a b c : ℕ → ℝ}

-- TODO (BM): move everything in this section to mathlib
section

lemma Nat.Iic_eq_Icc (n : ℕ) : Finset.Iic n = Finset.Icc 0 n := by simp [Finset.Iic_eq_Icc]

@[to_additive]
theorem Finset.prod_Icc_succ_bot {M : Type*} [CommMonoid M] {a b : ℕ}
    (hab : a ≤ b) (f : ℕ → M) :
    (∏ k in Icc a b, f k) = f a * (∏ k in Icc (a + 1) b, f k) := by
  rw [← Nat.Icc_insert_succ_left hab, prod_insert]
  simp

lemma Finset.finite_subsets (s : Finset ℕ) : {a | a ⊆ s}.Finite := by
  simpa using s.powerset.finite_toSet

end

structure baseAssumptions (d : ℕ) (a : ℕ → ℝ) : Prop where
(nonneg : ∀ i ≤ d, 0 ≤ a i)
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

/-- From the Fourier bound, we can deduce bounds for each `j ∈ (1, d]`. -/
lemma FourierBound.special (h : FourierBound d δ ν a b) (j : ℕ) (hj : j ∈ Ioc 1 d) :
    ν < 1/2 * (1 + δ + ∑ i ≤ d, max (a i) (b i) - max (a j) (b j)) := by
  apply h.trans_le ?_
  gcongr
  exact le_csSup ((finite_Ioc 1 d).image _).bddAbove ⟨_, hj, rfl⟩

lemma FourierBound.special' (h : FourierBound d δ ν a b) (j : ℕ) (hj : j ∈ Ioc 1 d) :
    ν < 1/2 * (1 + δ + ∑ i ≤ d with i ≠ j, max (a i) (b i)) := by
  refine (h.special j hj).trans_eq ?_
  rw [add_sub_assoc, Finset.filter_ne', Finset.sum_erase_eq_sub]
  simp only [mem_Ioc] at hj
  simp [hj]

lemma FourierBound.two (h : FourierBound d δ ν a b) (hd : 2 ≤ d) :
    ν < 1/2 * (1 + δ + ∑ i ≤ d, max (a i) (b i) - max (a 2) (b 2)) :=
  h.special _ (by simpa)

lemma FourierBound.three (h : FourierBound d δ ν a b) (hd : 3 ≤ d) :
    ν < 1/2 * (1 + δ + ∑ i ≤ d, max (a i) (b i) - max (a 3) (b 3)) :=
  h.special _ (by simpa)

def DeterminantBound (d : ℕ) (δ ν : ℝ) (a b : ℕ → ℝ) : Prop :=
  ν < sInf {1 + δ - a p - b q + min (a p / q) (b q / p) |
    (p : ℕ) (q : ℕ) (_ : p ∈ Ioc 1 d) (_ : q ∈ Ioc 1 d)}

def ThueBound (d : ℕ) (δ ν : ℝ) (a b : ℕ → ℝ) : Prop :=
  ν < 1 + δ - sSup {∑ i ≤ d with p ∣ i, (a i + b i) | p ∈ Ioc 1 d}

lemma ThueBound.special (h : ThueBound d δ ν a b) (p : ℕ) (hp : p ∈ Ioc 1 d) :
    ν < 1 + δ - ∑ i ≤ d with p ∣ i, (a i + b i) := by
  refine h.trans_le ?_
  gcongr
  exact le_csSup ((finite_Ioc 1 d).image _).bddAbove ⟨_, hp, rfl⟩

lemma ThueBound.very_special (ha : baseAssumptions d a) (hb : baseAssumptions d b)
    (h : ThueBound d δ ν a b) (p : ℕ) (hp : p ∈ Ioc 1 d) :
    ν < 1 + δ - (a p + b p) := by
  refine (h.special p hp).trans_le ?_
  gcongr
  refine Finset.single_le_sum (f := fun i ↦ a i + b i) ?_ ?_
  · simp only [Finset.mem_filter, Finset.mem_Iic, and_imp]
    intro i hi _
    exact add_nonneg (ha.nonneg i hi) (hb.nonneg i hi)
  · simp only [mem_Ioc] at hp
    simp [hp]

lemma ThueBound.special_two (ha : baseAssumptions d a) (hb : baseAssumptions d b)
    (h : ThueBound d δ ν a b) (hd : 4 ≤ d) :
    ν < 1 + δ - (a 2 + a 4 + (b 2 + b 4)) := by
  refine (h.special 2 (by simp; omega)).trans_le ?_
  gcongr
  rw [add_add_add_comm]
  refine Finset.add_le_sum (f := fun i ↦ a i + b i) ?_ (by simp; omega) (by norm_num [hd]) (by simp)
  simp only [Finset.mem_filter, Finset.mem_Iic, and_imp]
  intro i hi h2i
  exact add_nonneg (ha.nonneg i hi) (hb.nonneg i hi)

def s (a b c : ℕ → ℝ) (i : ℕ) := a i + b i + c i
local notation "s" => s a b c

lemma s_apply {i : ℕ} : s i = a i + b i + c i := rfl

lemma s_nonneg
    (ha : baseAssumptions d a) (hb : baseAssumptions d b) (hc : baseAssumptions d c)
    {i : ℕ} (hi : i ≤ d) : 0 ≤ s i :=
  add_nonneg (add_nonneg (ha.nonneg _ hi) (hb.nonneg _ hi)) (hc.nonneg _ hi)

lemma s_zero
    (ha : baseAssumptions d a) (hb : baseAssumptions d b) (hc : baseAssumptions d c) :
    s 0 = 0 := by
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

lemma GeometryBound.special (h : GeometryBound d δ ν a b c) (I I' I'' : Finset ℕ)
    (hI : I ⊆ Finset.Icc 1 d) (hI' : I' ⊆ Finset.Icc 1 d) (hI'' : I'' ⊆ Finset.Icc 1 d) :
    ν < δ + (max 1 (∑ i ∈ I, i * a i + ∑ i ∈ I', i * b i + ∑ i ∈ I'', i * c i) -
          (∑ i ∈ I, a i + ∑ i ∈ I', b i + ∑ i ∈ I'', c i)) := by
  refine h.trans_le ?_
  gcongr
  exact csInf_le (Set.Finite.bddBelow geometryBound_set_finite) ⟨I, hI, I', hI', I'', hI'', rfl⟩

lemma GeometryBound.special_s (h : GeometryBound d δ ν a b c)
    (I : Finset ℕ) (hI : I ⊆ Finset.Icc 1 d) :
    ν < δ + (max 1 (∑ i ∈ I, (i * s i)) - (∑ i ∈ I, s i)) := by
  refine (h.special I I I hI hI hI).trans_eq ?_
  simp [s_apply, mul_add, Finset.sum_add_distrib]

def δ_ (d : ℕ) (f : ℕ → ℝ) : ℝ := 1 / 3 - ∑ i ≤ d, f i

/-- 4.7 -/
lemma sum_eq_δ_ (d : ℕ) (f : ℕ → ℝ) : ∑ i ≤ d, f i = 1 / 3 - δ_ d f := by simp [δ_]

variable {δ ε : ℝ}

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

abbrev delta_s (d : ℕ) (a b c : ℕ → ℝ) := δ_ d a + δ_ d b + δ_ d c
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
      norm_num [h.zero]
      norm_num
      linarith [h.sum_restrict_bound]

lemma bound_4_point_11_3 (h : baseAssumptions d a) (hd : 2 ≤ d) :
    ∑ i ∈ Finset.Icc 3 d, (i - 2) * a i ≤ 1 / 3 + a 1 + 2 * δ_ d a := by
  have h₁ := h.sum_bound
  rw [Nat.Iic_eq_Icc, ← Nat.Icc_insert_succ_left (by omega), ← Nat.Icc_insert_succ_left (by omega),
    ← Nat.Icc_insert_succ_left (by omega)] at h₁
  conv =>
    rhs
    rw [δ_, Nat.Iic_eq_Icc, ← Nat.Icc_insert_succ_left (by omega),
      ← Nat.Icc_insert_succ_left (by omega), ← Nat.Icc_insert_succ_left (by omega)]
  simp at h₁
  norm_num [sub_mul, h.zero, ← Finset.mul_sum]
  linarith

-- these proofs are a bit silly; hopefully there aren't more cases like these
lemma bound_4_point_11_4 (ha : baseAssumptions d a) (hd : 3 ≤ d) :
    ∑ i ∈ Finset.Icc 4 d, (i - 3) * a i ≤ 2 * a 1 + a 2 + 3 * δ_ d a := by
  have h₁ : ∑ i ≤ d, i * a i ≤ 1 := ha.sum_bound
  replace h₁ : a 1 + (2 * a 2 + (3 * a 3 + ∑ i ∈ Finset.Icc 4 d, i * a i)) ≤ 1 := by
    rw [Nat.Iic_eq_Icc, Finset.sum_Icc_succ_bot, Finset.sum_Icc_succ_bot,
      Finset.sum_Icc_succ_bot, Finset.sum_Icc_succ_bot] at h₁
    · simpa using h₁
    all_goals omega
  have h₂ : δ_ d a = 1 / 3 - (a 0 + (a 1 + (a 2 + (a 3 + ∑ x ∈ Finset.Icc 4 d, a x)))) := by
    rw [δ_, Nat.Iic_eq_Icc, Finset.sum_Icc_succ_bot, Finset.sum_Icc_succ_bot,
      Finset.sum_Icc_succ_bot, Finset.sum_Icc_succ_bot] <;>
    omega
  norm_num [sub_mul, h₂, ← Finset.mul_sum, ha.zero]
  linarith only [h₁]

lemma bound_4_point_12 (ha : baseAssumptions d a) (hb : baseAssumptions d b)
    (h : ThueBound d δ ν a b) (j : ℕ) (hj : j ∈ Ioc 1 d) (hν : 0.66 < ν) :
    a j + b j < 0.34 + δ := by
  norm_num1 at hν ⊢
  linarith [h.very_special ha hb j hj]

lemma bound_4_point_13 (ha : baseAssumptions d a) (hb : baseAssumptions d b)
    (h : ThueBound d δ ν a b) (hd : 4 ≤ d) (hν : 0.66 < ν) :
    a 2 + a 4 + (b 2 + b 4) < 0.34 + δ := by
  norm_num1 at hν ⊢
  linarith [h.special_two ha hb hd]

include ha hb hc in
lemma bound_4_point_14_general
    (hab : ThueBound d δ ν a b) (hac : ThueBound d δ ν a c) (hbc : ThueBound d δ ν b c)
    (j : ℕ) (hj : j ∈ Ioc 1 d) (hν : 0.66 < ν) :
    s j < 0.51 + 1.5 * δ := by
  replace hab := bound_4_point_12 ha hb hab j hj hν
  replace hac := bound_4_point_12 ha hc hac j hj hν
  replace hbc := bound_4_point_12 hb hc hbc j hj hν
  norm_num [s_apply] at hab hac hbc ⊢
  linarith

include ha hb hc in
lemma bound_4_point_14_two_four
    (hab : ThueBound d δ ν a b) (hac : ThueBound d δ ν a c) (hbc : ThueBound d δ ν b c)
    (hd : 4 ≤ d) (hν : 0.66 < ν) :
    s 2 + s 4 < 0.51 + 1.5 * δ := by
  replace hab := bound_4_point_13 ha hb hab hd hν
  replace hac := bound_4_point_13 ha hc hac hd hν
  replace hbc := bound_4_point_13 hb hc hbc hd hν
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

-- theorem extracted_1 {d : ℕ} {ν : ℝ} {a b c : ℕ → ℝ}
--     {δ : ℝ} (hν : 33 / 50 < ν)
--     (h₃ : δ + (1 - (a 1 + a 2)) < 33 / 50)
--     (h₂ : δ + a 2 < 33 / 50)
--     (h_1 : ν < δ + (1 - (a 1 + a 2))) : False := by
--   linarith

include ha hb hc in
lemma bound_4_point_15
    (hab : ThueBound d δ ν a b) (hac : ThueBound d δ ν a c) (hbc : ThueBound d δ ν b c)
    (h : GeometryBound d δ ν a b c)
    (hδ : δ ≤ 0.06)
    (hν : 0.66 < ν) (hd : 2 ≤ d) :
    s 1 + s 2 ≤ 0.34 + δ := by
  have h₁ : ν < δ + (max 1 (s 1 + 2 * s 2) - (s 1 + s 2)) := by
    have := h.special_s {1, 2} (by simp [Finset.insert_subset_iff]; constructor <;> omega)
    simpa using this
  replace h₁ : ν < max (δ + (1 - (s 1 + s 2))) (δ + s 2) := calc
    ν < δ + (max 1 (s 1 + 2 * s 2) - (s 1 + s 2)) := h₁
    _ = δ + (1 - (s 1 + s 2)) ⊔ (s 1 + 2 * s 2 - (s 1 + s 2)) := by rw [max_sub_sub_right]
    _ = δ + max (1 - (s 1 + s 2)) (s 2) := by ring_nf
    _ = max (δ + (1 - (s 1 + s 2))) (δ + s 2) := by rw [max_add_add_left]
  by_contra! h₃ : 0.34 + δ < s 1 + s 2
  replace h₃ : δ + (1 - (s 1 + s 2)) < 0.66 := by
    norm_num1 at h₃ ⊢
    linarith only [h₃]
  have h₂ : s 2 < 0.51 + 1.5 * δ :=
    bound_4_point_14_general ha hb hc hab hac hbc 2 (by simp [hd]) hν
  replace h₂ : δ + s 2 < 0.66 := calc
    _ < δ + (0.51 + 1.5 * δ) := by gcongr
    _ = 0.51 + 2.5 * δ := by ring
    _ ≤ 0.66 := by norm_num1 at hδ ⊢; linarith
  have h₄ : max (δ + (1 - (s 1 + s 2))) (δ + s 2) < 0.66 := by simp [h₂, h₃]
  linarith

/-- 4.16 -/
def SubSums (j : ℕ) (a b c : ℕ → ℝ) : Set ℝ :=
    {a j, b j, c j, a j + b j, a j + c j, b j + c j, a j + b j + c j}

lemma GeometryBound.subSums (h : GeometryBound d δ ν a b c)
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
  · have h₁ := h.special {1, j} {1} {1} ‹_› ‹_› ‹_›
    have h₂ := h.special {1, 2, j} {1, 2} {1, 2} ‹_› ‹_› ‹_›
    simp only [Finset.mem_singleton, hj₁, not_false_eq_true, Finset.sum_insert, Nat.cast_one,
      one_mul, Finset.sum_singleton, Finset.mem_insert, OfNat.one_ne_ofNat, or_self, hj₂,
      Nat.cast_ofNat] at h₁ h₂
    simp only [s_apply]
    exact ⟨h₂.trans_eq (by ring_nf), h₁.trans_eq (by ring_nf)⟩
  · have h₁ := h.special {1} {1, j} {1} ‹_› ‹_› ‹_›
    have h₂ := h.special {1, 2} {1, 2, j} {1, 2} ‹_› ‹_› ‹_›
    simp only [Finset.mem_singleton, hj₁, not_false_eq_true, Finset.sum_insert, Nat.cast_one,
      one_mul, Finset.sum_singleton, Finset.mem_insert, OfNat.one_ne_ofNat, or_self, hj₂,
      Nat.cast_ofNat] at h₁ h₂
    simp only [s_apply]
    exact ⟨h₂.trans_eq (by ring_nf), h₁.trans_eq (by ring_nf)⟩
  · have h₁ := h.special {1} {1} {1, j} ‹_› ‹_› ‹_›
    have h₂ := h.special {1, 2} {1, 2} {1, 2, j} ‹_› ‹_› ‹_›
    simp only [Finset.mem_singleton, hj₁, not_false_eq_true, Finset.sum_insert, Nat.cast_one,
      one_mul, Finset.sum_singleton, Finset.mem_insert, OfNat.one_ne_ofNat, or_self, hj₂,
      Nat.cast_ofNat] at h₁ h₂
    simp only [s_apply]
    exact ⟨h₂.trans_eq (by ring_nf), h₁.trans_eq (by ring_nf)⟩
  · have h₁ := h.special {1, j} {1, j} {1} ‹_› ‹_› ‹_›
    have h₂ := h.special {1, 2, j} {1, 2, j} {1, 2} ‹_› ‹_› ‹_›
    simp only [Finset.mem_singleton, hj₁, not_false_eq_true, Finset.sum_insert, Nat.cast_one,
      one_mul, Finset.sum_singleton, Finset.mem_insert, OfNat.one_ne_ofNat, or_self, hj₂,
      Nat.cast_ofNat] at h₁ h₂
    simp only [s_apply]
    exact ⟨h₂.trans_eq (by ring_nf), h₁.trans_eq (by ring_nf)⟩
  · have h₁ := h.special {1, j} {1} {1, j} ‹_› ‹_› ‹_›
    have h₂ := h.special {1, 2, j} {1, 2} {1, 2, j} ‹_› ‹_› ‹_›
    simp only [Finset.mem_singleton, hj₁, not_false_eq_true, Finset.sum_insert, Nat.cast_one,
      one_mul, Finset.sum_singleton, Finset.mem_insert, OfNat.one_ne_ofNat, or_self, hj₂,
      Nat.cast_ofNat] at h₁ h₂
    simp only [s_apply]
    exact ⟨h₂.trans_eq (by ring_nf), h₁.trans_eq (by ring_nf)⟩
  · have h₁ := h.special {1} {1, j} {1, j} ‹_› ‹_› ‹_›
    have h₂ := h.special {1, 2} {1, 2, j} {1, 2, j} ‹_› ‹_› ‹_›
    simp only [Finset.mem_singleton, hj₁, not_false_eq_true, Finset.sum_insert, Nat.cast_one,
      one_mul, Finset.sum_singleton, Finset.mem_insert, OfNat.one_ne_ofNat, or_self, hj₂,
      Nat.cast_ofNat] at h₁ h₂
    simp only [s_apply]
    exact ⟨h₂.trans_eq (by ring_nf), h₁.trans_eq (by ring_nf)⟩
  · have h₁ := h.special_s {1, j} ‹_›
    have h₂ := h.special_s {1, 2, j} ‹_›
    simp only [Finset.mem_singleton, hj₁, not_false_eq_true, Finset.sum_insert, Nat.cast_one,
      one_mul, Finset.sum_singleton, Finset.mem_insert, OfNat.one_ne_ofNat, or_self, hj₂,
      Nat.cast_ofNat, s_apply] at h₁ h₂
    simp only [s_apply]
    exact ⟨h₂.trans_eq (by ring_nf), h₁.trans_eq (by ring_nf)⟩

-- lemma bound_4_point_15
--     (hab : ThueBound d δ ν a b) (hac : ThueBound d δ ν a c) (hbc : ThueBound d δ ν b c)
--     (h : GeometryBound d δ ν a b c)
--     (hδ : δ ≤ 0.06)
--     (hν : 0.66 < ν) (hd : 2 ≤ d) :

lemma bound_4_point_17_aux1
    {τ : ℝ} (h : GeometryBound d δ ν a b c)
    (hτ : τ ∈ SubSums 3 a b c) (hν : 0.66 < ν) (hd : 3 ≤ d) :
    τ ∉ Icc (0.34 - s 1 - s 2 + δ) (0.33 - s 2 / 2 - δ / 2) := by
  have h₁ := (h.subSums 3 (by simp [hd]) hτ).1
  contrapose! h₁
  simp only [mem_Icc] at h₁
  rw [← max_sub_sub_right, ← max_add_add_left, max_le_iff]
  simp only [s_apply] at *
  norm_num1 at *
  constructor
  · linarith
  · linarith

lemma bound_4_point_17_aux2
    {τ : ℝ} (h : GeometryBound d δ ν a b c)
    (hτ : τ ∈ SubSums 3 a b c) (hν : 0.66 < ν) (hd : 3 ≤ d) :
    τ ∉ Icc (0.34 - s 1 + δ) (0.33 - δ / 2) := by
  have h₁ := (h.subSums 3 (by simp [hd]) hτ).2
  contrapose! h₁
  simp only [mem_Icc] at h₁
  rw [← max_sub_sub_right, ← max_add_add_left, max_le_iff]
  simp only [s_apply] at *
  norm_num1 at *
  constructor
  · linarith
  · linarith

lemma bound_4_point_17
    {τ : ℝ} (h : GeometryBound d δ ν a b c)
    (hτ : τ ∈ SubSums 3 a b c) (hd : 3 ≤ d) (hν : 0.66 < ν) :
    τ ∉ Icc (0.34 - s 1 - s 2 + δ) (0.33 - s 2 / 2 - δ / 2) ∪
        Icc (0.34 - s 1 + δ) (0.33 - δ / 2) := by
  simp only [mem_union, not_or]
  exact ⟨bound_4_point_17_aux1 h hτ hν hd, bound_4_point_17_aux2 h hτ hν hd⟩

-- theorem thm_4_point_3 : ν ≤ 0.66 :=
--   sorry

end
