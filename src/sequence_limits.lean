import data.real.basic

-- based on Lean Tutorial / 05_sequence_limits.lean

notation `|`x`|` := abs x

def seq_limit (sequence : ℕ → ℝ) (a : ℝ) : Prop :=
∀ ε : ℝ, ε > 0 → ∃ n₀ : ℕ, ∀ n : ℕ, n ≥ n₀ → |sequence n - a| ≤ ε

lemma eq_of_abs_sub_le_all_pos (x y : ℝ) : (∀ ε > 0, |x - y| ≤ ε) → x = y :=
begin
  contrapose!,
  intro ass,
  use |x - y| / 2,
  cases ne.lt_or_lt ass,
  {
    have neg_case : |x - y| = y - x,
    {
      unfold abs,
      simp,
      exact le_of_lt h,
    },
    rw neg_case at *,
    split;
    linarith,
  },
  {
    have pos_case : |x - y| = x - y,
    {
      unfold abs,
      simp,
      exact le_of_lt h,
    },
    rw pos_case at *,
    split;
    linarith,
  },
end

/- 
Useful lemmata:

  (about maximum)
  `max_le_iff r p q :  max p q ≤ r ↔ p ≤ r ∧ q ≤ r`
  `le_max_left  p q :  p ≤ max p q`
  `le_max_right p q :  q ≤ max p q`
-/


-- If `u` tends to `a` and `v` tends to `b` then `u + v` tends to `a + b`.
example (u v : ℕ → ℝ) (a b : ℝ) (hu : seq_limit u a) (hv : seq_limit v b) :
seq_limit (u + v) (a + b) :=
begin
  sorry,
end


-- Sandwich theorem (a.k.a. "two policemen").
example (u v w : ℕ → ℝ) (z : ℝ) (hu : seq_limit u z) (hv : seq_limit v z)
(below : ∀ n, u n ≤ w n)
(above : ∀ n, w n ≤ v n) :
seq_limit w z :=
begin
  sorry,
end


-- A sequence admits at most one limit.
example (w : ℕ → ℝ) (a b : ℝ) : seq_limit w a → seq_limit w b → a = b :=
begin
  sorry,
end
