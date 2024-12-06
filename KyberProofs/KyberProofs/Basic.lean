
import Mathlib
import KyberProofs.Ideals
import KyberProofs.Polynomials

open Polynomial Ideal DirectSum
open scoped Polynomial

noncomputable section

variable {n k q r : ℕ} [Fact (q.Prime)] {ζ : ZMod q}

--------------------
--     LEMMAS     --
--------------------

lemma Function.onFun_onFun {α β γ φ : Type} {f : γ → γ → φ} {g : β → γ} {h : α → β} :
  (f on g on h) = (f on (g ∘ h))
  := by
    unfold Function.onFun
    simp


--------------------
--      GOAL      --
--------------------

abbrev T := (ZMod q)[X]

def ntt
  (hn : n = 2^k) (hk : k ≠ 0)
  (hq : q = n * r + 1) (hr : Odd r)
  (hζ : orderOf ζ = n)
:
  (ZMod q)[X] ⧸ (span {X^n + 1} : Ideal (ZMod q)[X]) ≃+* ((i : Finset.range (n / 2)) → (ZMod q)[X] ⧸ span {X^2 - C (ζ^(2 * i.val + 1))})
  := by
    let R := (ZMod q)[X]
    let ι := Finset.range (n / 2)
    let s' (i : ℕ) := X^2 - C (ζ^(2 * i + 1))
    let s (i : ι) := s' i.val
    let I (i : ℕ) := span {s' i}
    change R ⧸ (span {X^n + 1}) ≃+* ((i : ι) → R ⧸ I i)
    have : ∏ i : ι, s i = ∏ i ∈ ι, s' i := by
      unfold s
      rw [Finset.prod_coe_sort]
    have : ∏ i : ι, I i = span {X^n + 1} := by
      rw [prod_span_singleton]
      congr
      rw [this]
      exact prod_quads' hn hk hq hr hζ
    rw [← this]
    have inst : Nonempty ι := by
      apply Finset.Nonempty.to_subtype
      rw [Finset.nonempty_range_iff]
      apply (Nat.div_ne_zero_iff (by norm_num)).mpr
      rw [hn]
      exact Nat.le_self_pow hk 2
    apply chinese_remainder (s := s)
    · intro i
      unfold s I
      apply mem_span_singleton_self
    · have : Pairwise (IsCoprime on s) ↔ Set.Pairwise ι (IsCoprime on s') := by
        rw [← Finset.pairwise_subtype_iff_pairwise_finset']
      rw [this]
      have : s' = quad (ζ := ζ) ∘ (fun i => 2 * i + 1) := by
        apply _root_.funext
        intro i
        unfold s' quad
        simp
      have : (IsCoprime on s') = ((IsCoprime on quad (ζ := ζ)) on (fun i => 2 * i + 1)) := by
        nth_rw 2 [Function.onFun_onFun]
        rw [this]
      rw [this]
      rw [← Set.InjOn.pairwise_image]
      · have : (fun i => 2 * i + 1) '' ι = odds (n := n) := by
          rw [odds_eq_image_range (by
            rw [hn]
            exact even_two_pow hk
          )]
          unfold ι
          simp
        rw [this]
        apply pairwise_coprime hn hk hq hr hζ
      · intro i hi j hj hij
        simp at hij
        exact hij

end
