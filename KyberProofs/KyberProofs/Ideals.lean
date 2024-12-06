
import Mathlib

open Polynomial Ideal DirectSum
open scoped Polynomial

noncomputable section

variable {α : Type} [DecidableEq α] {R : Type*} [CommRing R] {I J : Ideal R}

lemma Ideal.mem_mul {a : R} (h : IsCoprime I J) :
  a ∈ I * J ↔ a ∈ I ∧ a ∈ J
  := by
    constructor
    · intro ha
      constructor
      · exact mul_le_right ha
      · exact mul_le_left ha
    · intro ha
      obtain ⟨i, hi, j, hj, h⟩ := isCoprime_iff_exists.mp h
      apply congr_arg (fun x => a * x) at h
      rw [mul_one, mul_add, mul_comm] at h
      rw [← h]
      apply Ideal.add_mem
      · exact mul_mem_mul hi ha.right
      · exact mul_mem_mul ha.left hj

lemma Ideal.prod_mem_prod'
  {ι : Finset α}
  {I : α → Ideal R} {x : ι → R}
  (h : ∀ i : ι, x i ∈ I i)
:
  ∏ i : ι, x i ∈ ∏ i ∈ ι, I i
  := by
    let x' (a : α) :=
      if ha : a ∈ ι
      then x ⟨a, ha⟩
      else 0
    have h' : ∀ i ∈ ι, x' i ∈ I i := by
      unfold x'
      intro i hi
      simp [*]
      have := h ⟨i, hi⟩
      simp [this]
    have : ∏ i : ι, x i = ∏ i ∈ ι, x' i := by
      rw [Finset.prod_dite_of_true (fun i a ↦ a) (fun i ha ↦ x ⟨i, ha⟩) fun i ha ↦ 0]
    rw [this]
    apply Ideal.prod_mem_prod h'

lemma Ideal.mem_prod'
  {a : R}
  {ι : Finset α} [Nonempty ι]
  {I : α → Ideal R}
  {s : ι → R} (hs : ∀ i : ι, s i ∈ I i)
  (hs' : Pairwise (IsCoprime on s))
:
  a ∈ ∏ i : ι, I i ↔ ∀ i : ι, a ∈ I i
  := by
    constructor
    rw [Finset.prod_coe_sort ι I]
    · intro ha
      simp
      rw [← Submodule.mem_finset_inf]
      have : ι.prod I ≤ ι.inf I := Ideal.prod_le_inf
      exact this ha
    · intro ha
      obtain ⟨μ, hμ⟩ := exists_sum_eq_one_iff_pairwise_coprime'.mpr hs'
      apply congr_arg (fun x => a * x) at hμ
      rw [mul_one, Finset.mul_sum] at hμ
      rw [← hμ]
      rw [Finset.prod_coe_sort ι I]
      apply Ideal.sum_mem
      intro i hi
      rw [mul_left_comm]
      apply Ideal.mul_mem_left
      let f (j : ι) := if i = j then a else s j
      have : ∏ j ∈ {i}ᶜ, s j = ∏ j ∈ {i}ᶜ, f j := by
        apply Finset.prod_bijective id (by simp) (by simp)
        intro j hj
        rw [Finset.mem_compl, Finset.not_mem_singleton] at hj
        unfold f
        simp
        rw [if_neg (Ne.symm hj)]
      have : a * ∏ j ∈ {i}ᶜ, s j = f i * ∏ j ∈ {i}ᶜ, f j := by
        rw [this]
        congr
        unfold f
        simp
      have new : f i = ∏ j ∈ {i}, f j := by
        simp
      have : a * ∏ j ∈ {i}ᶜ, s j = ∏ j : ι, f j := by
        rw [this, new]
        rw [Finset.prod_mul_prod_compl]
      rw [this]
      apply Ideal.prod_mem_prod'
      intro j
      unfold f
      by_cases hij : i = j
      · simp [hij, ha]
      · simp [hij, hs]

def lift :
  R ⧸ I → R
  :=
    Classical.choose (Function.Surjective.hasRightInverse Ideal.Quotient.mk_surjective)

lemma quotient_mk_lift {I : Ideal R} {a : R ⧸ I} :
  Ideal.Quotient.mk I (lift a) = a
  := by
    have : Function.RightInverse lift (Ideal.Quotient.mk I) := Classical.choose_spec (Function.Surjective.hasRightInverse Ideal.Quotient.mk_surjective)
    exact this a

lemma quotient_mk_coprime {i j : R} (hi : i ∈ I) (hij : i + j = 1) :
  Ideal.Quotient.mk I j = 1
  := by
    apply congr_arg (Ideal.Quotient.mk I) at hij
    rw [
      RingHom.map_add,
      RingHom.map_one,
      Quotient.eq_zero_iff_mem.mpr hi,
      zero_add,
    ] at hij
    exact hij

def chinese_remainder {h : IsCoprime I J} :
  R ⧸ (I * J) ≃+* (R ⧸ I) × (R ⧸ J)
  := by
    let A := R ⧸ (I * J)
    let B := (R ⧸ I) × (R ⧸ J)
    change A ≃+* B
    let f₀ : R →+* B := (Ideal.Quotient.mk I).prod (Ideal.Quotient.mk J)
    let f : A →+* B := Ideal.Quotient.lift (I * J) f₀ (by
      intro a ha
      unfold f₀
      rw [RingHom.prod_apply, Prod.mk_eq_zero, Quotient.eq_zero_iff_mem, Quotient.eq_zero_iff_mem]
      exact (mem_mul h).mp ha)
    apply RingEquiv.ofBijective f
    constructor
    · unfold f f₀
      rw [Ideal.injective_lift_iff _]
      apply Ideal.ext
      intro a
      rw [
        RingHom.mem_ker,
        RingHom.prod_apply,
        Prod.mk_eq_zero,
        Quotient.eq_zero_iff_mem,
        Quotient.eq_zero_iff_mem,
        mem_mul h,
      ]
    · unfold f f₀
      apply Ideal.Quotient.lift_surjective_of_surjective
      intro b
      unfold B at b
      obtain ⟨i, hi, j, hj, hij⟩ := isCoprime_iff_exists.mp h
      use i * (lift b.snd) + (j * lift b.fst)
      rw [@RingHom.prod_apply]
      apply Prod.ext
      · simp
        rw [
          quotient_mk_lift,
          Quotient.eq_zero_iff_mem.mpr hi,
          zero_mul,
          zero_add,
          quotient_mk_coprime hi hij,
          one_mul,
        ]
      · simp
        rw [add_comm] at hij
        rw [
          quotient_mk_lift,
          Quotient.eq_zero_iff_mem.mpr hj,
          zero_mul,
          add_zero,
          quotient_mk_coprime hj hij,
          one_mul,
        ]

lemma prod_eq_zero {ι : Finset α} {i j : ι} {f : ι → R} (h : i ≠ j) :
  (∏ k ∈ {j}ᶜ, if k = i then 0 else f k) = 0
  := by
    have : i ∉ ({j} : Finset {x // x ∈ ι}) := by
      simp [h]
    apply Finset.mem_compl.mpr at this
    apply Finset.prod_eq_zero this
    simp

def chinese_remainder'
  {α : Type} [DecidableEq α]
  {ι : Finset α} [Nonempty ι]
  {I : α → Ideal R}
  {s : ι → R} (hs : ∀ i : ι, s i ∈ I i)
  (hs' : Pairwise (IsCoprime on s))
:
  R ⧸ (∏ i : ι, I i) ≃+* ((i : ι) → R ⧸ I i)
  := by
    let A := R ⧸ (∏ i : ι, I i)
    let B := (i : ι) → R ⧸ (I i)
    change A ≃+* B
    let f₀ : R →+* B := Pi.ringHom (fun i => Ideal.Quotient.mk (I i))
    have {a : R} : f₀ a = 0 ↔ a ∈ ∏ i : ι, I i := by
      unfold f₀
      rw [funext_iff]
      conv =>
        lhs
        intro i
        rw [Pi.ringHom_apply, Pi.zero_apply, Quotient.eq_zero_iff_mem]
      rw [mem_prod' hs hs']
    let f : A →+* B := Ideal.Quotient.lift (∏ i : ι, I i) f₀ (by
      intro a ha
      exact this.mpr ha)
    apply RingEquiv.ofBijective f
    constructor
    · unfold f
      rw [Ideal.injective_lift_iff _]
      apply Ideal.ext
      intro a
      rw [RingHom.mem_ker, ← this]
    · unfold f f₀
      apply Ideal.Quotient.lift_surjective_of_surjective
      intro b
      unfold B at b
      obtain ⟨μ, hμ⟩ := exists_sum_eq_one_iff_pairwise_coprime'.mpr hs'
      use ∑ i : ι, lift (b i) * (μ i) * ∏ j ∈ {i}ᶜ, s j
      conv =>
        lhs
        intro i
        rw [Pi.ringHom_apply]
      rw [funext_iff]
      intro i
      have {k : ι} : Ideal.Quotient.mk (I i) (s k) = if i = k then 0 else Ideal.Quotient.mk (I i) (s k) := by
        rw [Eq.comm, ite_eq_iff']
        constructor
        · intro hik
          rw [hik, Eq.comm]
          exact Quotient.eq_zero_iff_mem.mpr (hs k)
        · intro hik
          rfl
      have {k : ι} (hk : i ≠ k) : Ideal.Quotient.mk (I i) (∏ j ∈ {k}ᶜ, s j) = 0 := by
        rw [map_prod]
        conv =>
          lhs
          arg 2
          intro k
          rw [this]
          arg 1
          rw [Eq.comm]
        apply prod_eq_zero hk
      have {k : ι} : Ideal.Quotient.mk (I i) (μ k * ∏ j ∈ {k}ᶜ, s j) = if i = k then Ideal.Quotient.mk (I i) (μ k * ∏ j ∈ {k}ᶜ, s j) else 0 := by
        rw [Eq.comm, ite_eq_iff']
        constructor
        · intro hik
          rfl
        · intro hik
          rw [_root_.map_mul, this hik, mul_zero]
      have : Ideal.Quotient.mk (I i) (∑ k : ι, μ k * (∏ j ∈ {k}ᶜ, s j)) = Ideal.Quotient.mk (I i) (μ i * (∏ j ∈ {i}ᶜ, s j)) := by
        rw [map_sum]
        conv =>
          lhs
          arg 2
          intro k
          rw [this]
        rw [@Fintype.sum_ite_eq]
      have : (Ideal.Quotient.mk (I i)) (μ i * ∏ j ∈ {i}ᶜ, s j) = 1 := by
        apply congr_arg (Ideal.Quotient.mk (I i)) at hμ
        rw [this] at hμ
        rw [RingHom.map_one] at hμ
        exact hμ
      have : (Ideal.Quotient.mk (I i)) (lift (b i) * μ i * ∏ j ∈ {i}ᶜ, s j) = (lift (b i)) := by
        rw [mul_assoc]
        rw [_root_.map_mul]
        rw [this, mul_one]
      simp only [map_sum]
      have {k : ι} : (Ideal.Quotient.mk (I i)) (lift (b k) * μ k * ∏ j ∈ {k}ᶜ, s j) = if i = k then (Ideal.Quotient.mk (I i)) (lift (b k) * μ k * ∏ j ∈ {k}ᶜ, s j) else 0 := by
        rw [Eq.comm, ite_eq_iff']
        constructor
        · intro hik
          rfl
        · intro hik
          simp [*]
      conv =>
        lhs
        arg 2
        intro k
        rw [this]
      simp only [Finset.univ_eq_attach, Finset.sum_ite_eq, Finset.mem_attach, ↓reduceIte]
      simp [*]
      simp [quotient_mk_lift]

end
