
import Mathlib

open Polynomial Ideal DirectSum
open scoped Polynomial

noncomputable section

variable {R : Type*} [CommRing R] {I J : Ideal R}

lemma Ideal.min_eq_mul_of_coprime (h : IsCoprime I J) :
  I ⊓ J = I * J
  := by
    apply Ideal.ext
    intro a
    rw [Ideal.mem_inf]
    constructor
    · intro ha
      obtain ⟨i, hi, j, hj, h⟩ := isCoprime_iff_exists.mp h
      apply congr_arg (fun x => a * x) at h
      rw [mul_one, mul_add, mul_comm] at h
      rw [← h]
      apply Ideal.add_mem
      · exact mul_mem_mul hi ha.right
      · exact mul_mem_mul ha.left hj
    · intro ha
      constructor
      · exact mul_le_right ha
      · exact mul_le_left ha

lemma Ideal.mem_mul {a : R} (h : IsCoprime I J) :
  a ∈ I * J ↔ a ∈ I ∧ a ∈ J
  := by
    rw [← min_eq_mul_of_coprime h, mem_inf]

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

-- I * J = I ∩ J => helps prove injectivity
example {h : IsCoprime I J} :
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

-- variable {R : Type*} [CommRing R] {A B P : R[X]}
-- 
-- theorem polynomial_chinese_remainder :
--   R[X] ≃+* R[X]
--   := by
--     -- apply RingEquiv.ofRingHom
--     sorry
--   -- Ideal.quotient_inf_equiv_prod (span {A}) (span {B})
--   --   (by rw [←span_mul, h])
--   -- coprime

end