-- založeno na Lean Tutorial / 05_sequence_limits.lean
import resources

/- 
Užitečná lemmata:

`le_max_left  p q` říká `p ≤ max p q`
`le_max_right p q` říká `q ≤ max p q`

`eq_of_abs_sub_le_all_pos x y` říká `(∀ ε > 0, |x - y| ≤ ε) → x = y`
-/

-- S touto definicí limity posloupnosti budeme pracovat ve všech následujících cvičeních.
def seq_limit (s : ℕ → ℝ) (a : ℝ) : Prop :=
∀ ε : ℝ, ε > 0 → ∃ n₀ : ℕ, ∀ n : ℕ, n ≥ n₀ → |s n - a| ≤ ε


-- Součet limit:
-- Pokud [`u` konverguje k `a`] a [`v` konverguje k `b`],
-- pak [`u + v` konverguje k `a + b`].
example (u v : ℕ → ℝ) (a b : ℝ) (hu : seq_limit u a) (hv : seq_limit v b) :
  seq_limit (u + v) (a + b) :=
begin
  sorry,
end

-- Věta o dvou policajtech:
-- Pokud [posloupnost `u` konverguje k `z`] a stejně tak [posloupnost `v` konverguje k `z`],
-- pak [posloupnost `w` taková že `u ≤ w ≤ v` konverguje k `z` taktéž].
example (u v w : ℕ → ℝ) (z : ℝ) (hu : seq_limit u z) (hv : seq_limit v z)
        (below : ∀ n, u n ≤ w n) (above : ∀ n, w n ≤ v n) :
  seq_limit w z :=
begin
  sorry,
end

-- Každá posloupnost má nejvýše jednu limitu.
example (w : ℕ → ℝ) (a b : ℝ) (ha : seq_limit w a) (hb : seq_limit w b) :
  a = b :=
begin
  sorry,
end
