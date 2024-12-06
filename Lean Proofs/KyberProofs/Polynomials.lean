
import Mathlib.Data.Int.CardIntervalMod
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.FieldTheory.Finite.Basic

open Nat Finset Polynomial BigOperators
open scoped Polynomial

noncomputable section

variable {n k q r : ℕ} [Fact (q.Prime)] {ζ : ZMod q}

@[reducible]
def odds := (range n).filter (fun i => Odd i)
@[reducible]
def quad (i : ℕ) := X^2 - Polynomial.C (ζ^i)
@[reducible]
def quads := image (quad (ζ := ζ)) (odds (n := n))



--------------------
--     LEMMAS     --
--------------------

lemma even_two_pow (hk : k ≠ 0) :
  Even (2^k)
  := (even_pow' hk).mpr even_two

lemma card_odds :
  #(odds (n := n)) = n / 2
  := by
    unfold odds
    conv =>
      lhs
      arg 1
      arg 1
      intro i
      rw [odd_iff]
      change i ≡ 1 [MOD 2]
    rw [← count_eq_card_filter_range, Nat.count_modEq_card _ (by norm_num)]
    simp
    apply le_of_lt_succ
    apply Nat.mod_lt
    norm_num

lemma odds_eq_image_range (hn : Even n) :
  odds (n := n) = image (fun i => 2 * i + 1) (range (n / 2))
  := by
    unfold odds
    ext i
    constructor
    · intro hi
      obtain ⟨hi', hi''⟩ := mem_filter.mp hi
      rw [mem_image]
      use i / 2
      constructor
      · rw [mem_range] at hi' ⊢
        apply div_lt_div_of_lt_of_dvd (even_iff_two_dvd.mp hn) hi'
      · obtain ⟨j, hij⟩ := hi''
        rw [hij]
        simp
        rw [mul_add_div (by norm_num)]
        simp
    · intro hi
      obtain ⟨j, ⟨hj, hij⟩⟩ := mem_image.mp hi
      rw [mem_range] at hj
      rw [mem_filter, mem_range, ← hij]
      constructor
      · apply succ_le.mp
        rw [← add_succ]
        change 2 * j + 2 ≤ n
        nth_rw 2 [← mul_one 2]
        rw [
          ← mul_add,
          mul_comm,
          ← Nat.le_div_iff_mul_le two_pos,
          ← succ_eq_add_one,
          succ_le,
        ]
        exact hj
      · exact odd_two_mul_add_one j

lemma quad_monic {i : ℕ} :
    (quad (ζ := ζ) i).Monic
  :=
    monic_X_pow_sub_C _ two_ne_zero

lemma quad_natDegree {i : ℕ} :
  (quad (ζ := ζ) i).natDegree = 2
  :=
    natDegree_X_pow_sub_C



--------------------
--     STEP 1     --
--------------------

def f : (ZMod q)[X] →+* (ZMod q)[X] :=
  eval₂RingHom C (X^2)

lemma pow_orderOf_div_two {a : ZMod q} (ha₁ : orderOf a ≠ 0) (ha₂ : Even (orderOf a)) :
  a^(orderOf a / 2) = -1
  := by
    apply IsPrimitiveRoot.eq_neg_one_of_two_right
    apply IsPrimitiveRoot.pow (pos_iff_ne_zero.mpr ha₁) (IsPrimitiveRoot.orderOf _)  
    exact Eq.symm (div_two_mul_two_of_even ha₂)

-- STEP 1
theorem quad_dvd
  {i : ℕ} (hi : Odd i)
  (hn₁ : n ≠ 0) (hn₂ : Even n)
  (hζ : orderOf ζ = n)
:
  (quad (ζ := ζ) i) ∣ X^n + 1
  := by
    unfold quad
    have : (X^2 - Polynomial.C (ζ^i) : (ZMod q)[X]) = f (X - Polynomial.C (ζ^i)) := by
      unfold f
      rw [coe_eval₂RingHom, eval₂_sub, eval₂_X, eval₂_C]
    rw [this]
    have : (X^n + 1 : (ZMod q)[X]) = f (X^(n / 2) + 1) := by
      unfold f
      rw [coe_eval₂RingHom, eval₂_add, eval₂_X_pow, eval₂_one, ← pow_mul]
      congr
      exact Eq.symm (two_mul_div_two_of_even hn₂)
    rw [this]
    apply RingHom.map_dvd
    rw [dvd_iff_isRoot, IsRoot]
    simp
    rw [pow_right_comm, ← hζ, pow_orderOf_div_two]
    · simp [hi]
    all_goals {
      rw [hζ]
      assumption
    }



--------------------
--     STEP 2     --
--------------------

lemma Polynomial.Monic.linear_of_natDegree_eq_one {p : (ZMod q)[X]} (hp₁ : p.Monic) (hp₂ : p.natDegree = 1) :
  ∃ b : ZMod q, p = X + C b
  := by
    rw [natDegree_eq_one] at hp₂
    rcases hp₂ with ⟨a, ha, b, hb⟩
    use b
    rw [Monic, ← hb, leadingCoeff_linear ha] at hp₁
    rw [hp₁] at hb
    simp at hb
    exact Eq.symm hb

lemma coeffs_eq_of_monic_quadratic_eq {b₁ c₁ b₂ c₂ : ZMod q} (h : X^2 + (C b₁) * X + C c₁ = X^2 + (C b₂) * X + C c₂) :
  b₁ = b₂ ∧ c₁ = c₂
  := by
    constructor
    · apply congr_arg (fun p => coeff p 1) at h
      simp at h
      exact h
    · apply congr_arg (fun p => coeff p 0) at h
      simp at h
      exact h

theorem irreducible_X_sq_sub_C {c : ZMod q} (hc : ¬IsSquare c) :
  Irreducible (X^2 - C c)
  := by
    have h_natDegree : (X^2 - C c).natDegree = 2 := by
      simp
    apply (Monic.irreducible_iff_natDegree' (monic_X_pow_sub_C _ (by norm_num))).mpr
    constructor
    · intro h
      apply congr_arg (fun p => p.coeff 2) at h
      simp [coeff_one] at h
    · intro f g hf hg hfg hg'
      simp [h_natDegree] at hg'
      have hf' : f.natDegree = 1 := by
        apply congr_arg natDegree at hfg
        rw [h_natDegree, natDegree_mul] at hfg
        · rw [hg'] at hfg
          simp at hfg
          exact hfg
        all_goals {
          apply Monic.ne_zero
          assumption
        }
      let ⟨b₁, hf'⟩ := Monic.linear_of_natDegree_eq_one hf hf'
      let ⟨b₂, hg'⟩ := Monic.linear_of_natDegree_eq_one hg hg'
      rw [
        hf',
        hg',
        mul_add,
        add_mul,
        add_mul,
        ← sq,
        ← add_assoc,
        sub_eq_add_neg,
        ← C_neg,
      ] at hfg
      nth_rw 2 [add_assoc, ← add_zero (X^2), mul_comm] at hfg
      rw [← zero_mul X, ← C_0, ← add_mul, ← C_add, ← C_mul] at hfg
      obtain ⟨hb₁, hb₂⟩ := coeffs_eq_of_monic_quadratic_eq hfg
      rw [add_eq_zero_iff_neg_eq'] at hb₁
      rw [← hb₁] at hb₂
      simp at hb₂
      rw [IsSquare] at hc
      push_neg at hc
      exact hc b₂ (Eq.symm hb₂)

lemma gcd_two_of_even {a : ℕ} (ha : Even a) :
  a.gcd 2 = 2
  := by
    obtain ⟨x, h⟩ := Even.exists_two_nsmul a ha
    rw [h]
    simp

lemma orderOf_zero {R : Type} [Ring R] [Nontrivial R] :
  orderOf (0 : R) = 0
  := by
    rw [orderOf_eq_zero_iff']
    intro n hn
    rw [zero_pow (pos_iff_ne_zero.mp hn)]
    norm_num

-- STEP 2
theorem quad_irreducible
  {i : ℕ} (hi : Odd i)
  (hn : n = 2^k) (hk : k ≠ 0)
  (hq : q = n * r + 1) (hr : Odd r)
  (hζ : orderOf ζ = n)
:
  Irreducible (quad (ζ := ζ) i)
  := by
    unfold quad
    apply irreducible_X_sq_sub_C
    intro h
    obtain ⟨a, h⟩ := h
    have hi' : i ≠ 0 := by
      rw [← pos_iff_ne_zero]
      exact Odd.pos hi
    have hni : Coprime n i := by
      rw [hn, Nat.coprime_pow_left_iff (pos_iff_ne_zero.mpr hk)]
      exact coprime_two_left.mpr hi
    rw [← sq] at h
    apply congr_arg orderOf at h
    rw [
      orderOf_pow' _ hi',
      hζ,
      hni,
      Nat.div_one,
      orderOf_pow' _ (by norm_num),
    ] at h
    by_cases ha : Even (orderOf a)
    · rw [gcd_two_of_even ha, Eq.comm] at h
      apply Nat.eq_mul_of_div_eq_right (Even.two_dvd ha) at h
      have : orderOf a ∣ q - 1 := by
        apply ZMod.orderOf_dvd_card_sub_one
        intro ha'
        rw [ha', orderOf_zero, hn, mul_comm, ← pow_succ] at h
        have h_not := Nat.two_pow_pos (k + 1)
        rw [pos_iff_ne_zero, ne_comm] at h_not
        contradiction
      rw [h, hq, mul_comm, hn] at this
      simp at this
      apply Nat.dvd_of_mul_dvd_mul_left (Nat.two_pow_pos k) at this
      exact (Odd.not_two_dvd_nat hr) this
    · simp at ha
      simp [coprime_comm.mp (coprime_two_left.mpr ha)] at h
      rw [← h, ← not_even_iff_odd, hn] at ha
      have := even_two_pow hk
      contradiction



--------------------
--     STEP 3     --
--------------------

lemma Monic.not_dvd_of_not_associated_of_natDegree_eq
  {R : Type} [CommRing R] [NoZeroDivisors R] [Nontrivial R]
  {a b : R[X]} (ha : a.Monic) (hb : b.Monic)
  (h₁ : a ≠ b)
  (h₂ : a.natDegree = b.natDegree) :
  ¬a ∣ b
  := by
    rw [dvd_iff_exists_eq_mul_right]
    push_neg
    intro c h
    have ha₀ : a ≠ 0 := by
      intro ha₀
      rw [ha₀] at h
      simp at h
      rw [ha₀, h] at h₁
      simp at h₁
    have hc : c ≠ 0 := by
      intro hc
      simp [hc] at h
      exact Monic.ne_zero hb h
    have hc_leadingCoeff : c.leadingCoeff = 1 := by
      apply congr_arg leadingCoeff at h
      rw [leadingCoeff_mul, ha, hb, one_mul, Eq.comm] at h
      exact h
    have hc_natDegree : c.natDegree = 0 := by
      apply congr_arg natDegree at h
      rw [natDegree_mul ha₀ hc] at h
      rw [h₂] at h
      rw [Eq.comm] at h
      exact Nat.add_eq_left.mp h
    obtain ⟨d, hd⟩ := natDegree_eq_zero.mp hc_natDegree
    have : c = 1 := by
      have hd' := congr_arg leadingCoeff hd
      rw [hc_leadingCoeff, leadingCoeff_C] at hd'
      rw [hd', C_1, Eq.comm] at hd
      exact hd
    rw [this, mul_one, Eq.comm] at h
    contradiction

lemma modEq_of_pow_eq_pow {i j : ℕ} (hζ : ζ ≠ 0) (h : ζ^i = ζ^j) :
  i ≡ j [MOD (orderOf ζ)]
  := by
    wlog hij : j ≤ i
    · specialize this (j := i) (i := j) hζ h.symm
      rw [not_le] at hij
      apply le_of_lt at hij
      exact (this hij).symm
    · apply congr_arg (fun x => x * (ζ^j)⁻¹) at h
      simp [hζ] at h
      rw [← pow_sub₀ ζ hζ hij] at h
      apply orderOf_dvd_of_pow_eq_one at h
      rw [← modEq_iff_dvd' hij] at h
      exact h.symm

lemma ne_zero_of_orderOf_ne_zero (hζ : orderOf ζ ≠ 0) :
  ζ ≠ 0
  := by
    intro h
    rw [h] at hζ
    exact hζ orderOf_zero

-- STEP 3
theorem pairwise_coprime
  (hn : n = 2^k) (hk : k ≠ 0)
  (hq : q = n * r + 1) (hr : Odd r)
  (hζ : orderOf ζ = n)
:
  Set.Pairwise (odds (n := n)) (IsCoprime on quad (ζ := ζ))
  := by
    intro i hi j hj hij
    have hi' : Odd i := (mem_filter.mp hi).2
    rw [Function.onFun]
    apply (Irreducible.coprime_iff_not_dvd _).mpr
    · apply Monic.not_dvd_of_not_associated_of_natDegree_eq quad_monic quad_monic
      · unfold quad
        intro h
        apply congr_arg (fun p => p.coeff 0) at h
        simp only [coeff_sub, coeff_X_pow, OfNat.zero_ne_ofNat, ↓reduceIte, zero_sub, neg_inj, coeff_C_zero] at h
        apply modEq_of_pow_eq_pow at h
        · have hi'' : i < n := mem_range.mp (mem_filter.mp hi).1
          have hj'' : j < n := mem_range.mp (mem_filter.mp hj).1
          rw [ModEq, hζ, mod_eq_of_lt hi'', mod_eq_of_lt hj''] at h
          contradiction
        · apply ne_zero_of_orderOf_ne_zero
          rw [hζ, hn, ← pos_iff_ne_zero]
          apply Nat.two_pow_pos
      · repeat rw [quad_natDegree]
    · exact quad_irreducible hi' hn hk hq hr hζ



--------------------
--      GOAL      --
--------------------

-- GOAL
theorem prod_quads
  (hn : n = 2^k) (hk : k ≠ 0)
  (hq : q = n * r + 1) (hr : Odd r)
  (hζ : orderOf ζ = n)
:
  ∏ i ∈ (odds (n := n)), quad (ζ := ζ) i = X^n + 1
  := by
    let lhs := ∏ i ∈ (odds (n := n)), quad (ζ := ζ) i
    let rhs : (ZMod q)[X] := X^n + 1
    change lhs = rhs
    have hn₁ : n ≠ 0 := by
      rw [hn, ← pos_iff_ne_zero]
      exact Nat.two_pow_pos k
    have hn₂ : Even n := by
      rw [hn]
      exact even_two_pow hk
    have h_dvd : lhs ∣ rhs := by
      apply prod_dvd_of_coprime (pairwise_coprime hn hk hq hr hζ)
      intro i hi
      have hi' : Odd i := (mem_filter.mp hi).2
      unfold rhs
      apply quad_dvd <;> assumption
    have h_natDegree : lhs.natDegree = rhs.natDegree := by
      unfold lhs rhs
      rw [natDegree_prod_of_monic]
      · unfold quad
        conv =>
          lhs
          arg 2
          intro i
          rw [natDegree_X_pow_sub_C]
        rw [
          sum_const,
          card_odds,
          Nat.nsmul_eq_mul,
          Nat.div_mul_cancel (even_iff_two_dvd.mp hn₂),
          ← C_1,
          natDegree_X_pow_add_C,
        ]
      · intro i hi
        exact (monic_X_pow_sub_C _ (by norm_num))
    apply Eq.symm (Polynomial.eq_of_monic_of_dvd_of_natDegree_le _ _ h_dvd (ge_of_eq h_natDegree))
    · apply monic_prod_of_monic
      intro i hi
      exact monic_X_pow_sub_C _ two_ne_zero
    · exact monic_X_pow_add_C _ hn₁

theorem prod_quads'
  (hn : n = 2^k) (hk : k ≠ 0)
  (hq : q = n * r + 1) (hr : Odd r)
  (hζ : orderOf ζ = n)
:
  ∏ i ∈ range (n / 2), (X^2 - C (ζ^(2 * i + 1))) = X^n + 1
  := by
    change ∏ i ∈ range (n / 2), quad ((fun i => 2 * i + 1) i) = X ^ n + 1
    rw [← prod_image]
    · rw [← prod_quads hn hk hq hr hζ]
      congr
      rw [hn, odds_eq_image_range]
      exact even_two_pow hk
    · intro i hi j hj hij
      apply congr_arg (fun x => x / 2) at hij
      rw [mul_add_div (by norm_num), mul_add_div (by norm_num)] at hij
      simp at hij
      exact hij

end
