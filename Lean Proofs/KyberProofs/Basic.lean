
import KyberProofs.Ideals
import KyberProofs.Polynomials

open Finset Ideal Polynomial
open scoped Polynomial

noncomputable section

variable (n q : ℕ) [Fact (q.Prime)] {k r : ℕ} (ζ : ZMod q)

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

abbrev R := (ZMod q)[X] ⧸ (span {X^n + 1} : Ideal (ZMod q)[X])
abbrev T := ((i : Finset.range (n / 2)) → (ZMod q)[X] ⧸ span {X^2 - C (ζ^(2 * i.val + 1))})

def ntt_equiv
  (hn : n = 2^k) (hk : k ≠ 0)
  (hq : q = n * r + 1) (hr : Odd r)
  (hζ : orderOf ζ = n)
:
  R n q ≃+* T n q ζ
  := by
    let ι := Finset.range (n / 2)
    let s' (i : ℕ) := X^2 - C (ζ^(2 * i + 1))
    let s (i : ι) := s' i.val
    let I (i : ℕ) := span {s' i}
    change
      (ZMod q)[X] ⧸ (span {(X^n + 1 : (ZMod q)[X])}) ≃+*
      ((i : ι) → (ZMod q)[X] ⧸ I i)
    rw [← prod_quads' hn hk hq hr hζ, ← prod_span_singleton, ← prod_coe_sort]
    change
      (ZMod q)[X] ⧸ ∏ i : { x // x ∈ ι }, I ↑i ≃+*
      ((i : { x // x ∈ ι }) → (ZMod q)[X] ⧸ I ↑i)
    have instNonempty_ι : Nonempty ι := by
      apply Finset.Nonempty.to_subtype
      rw [Finset.nonempty_range_iff, hn]
      apply (Nat.div_ne_zero_iff (by norm_num)).mpr
      exact Nat.le_self_pow hk 2
    apply chinese_remainder (s := s)
    · intro i
      apply mem_span_singleton_self
    · rw [Finset.pairwise_subtype_iff_pairwise_finset']
      have : s' = quad (ζ := ζ) ∘ (fun i => 2 * i + 1) := by
        apply _root_.funext
        intro i
        simp
      rw [this, ← Function.onFun_onFun (g := quad), ← Set.InjOn.pairwise_image]
      · have : (fun i => 2 * i + 1) '' ι = odds (n := n) := by
          rw [odds_eq_image_range (by
            rw [hn]
            exact even_two_pow hk
          )]
          simp [ι]
        rw [this]
        apply pairwise_coprime hn hk hq hr hζ
      · intro i hi j hj hij
        simp at hij
        exact hij

end
