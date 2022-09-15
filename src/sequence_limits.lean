-- based on Lean Tutorial / 05_sequence_limits.lean
import resources

/- 
Useful lemmata:

`le_max_left  p q` says `p ≤ max p q`
`le_max_right p q` says `q ≤ max p q`

`eq_of_abs_sub_le_all_pos x y` says `(∀ ε > 0, |x - y| ≤ ε) → x = y`
-/

-- This is the definition of limit we will work with in all exercises here.
def seq_limit (s : ℕ → ℝ) (a : ℝ) : Prop :=
∀ ε : ℝ, ε > 0 → ∃ n₀ : ℕ, ∀ n : ℕ, n ≥ n₀ → |s n - a| ≤ ε


-- Arithmetic of limits ... the sum law:
-- If [`u` approaches `a`] and [`v` approaches `b`],
-- then [`u + v` approaches `a + b`].
example (u v : ℕ → ℝ) (a b : ℝ) (hu : seq_limit u a) (hv : seq_limit v b) :
  seq_limit (u + v) (a + b) :=
begin
  sorry,
end

-- Squeeze theorem (a.k.a. "Sandwich rule" or "Two policemen and a drunk"):
-- If [`u` approaches `z`] and [`v` approaches `z`],
-- then [`w` such that `u ≤ w ≤ v` approaches `z` as well].
example (u v w : ℕ → ℝ) (z : ℝ) (hu : seq_limit u z) (hv : seq_limit v z)
        (below : ∀ n, u n ≤ w n) (above : ∀ n, w n ≤ v n) :
  seq_limit w z :=
begin
  sorry,
end

-- A sequence admits at most one limit.
example (w : ℕ → ℝ) (a b : ℝ) (ha : seq_limit w a) (hb : seq_limit w b) :
  a = b :=
begin
  sorry,
end
