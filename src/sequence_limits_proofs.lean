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
  intros ε epp,
  cases hu (ε / 2) (half_pos epp) with Nᵤ ha,
  cases hv (ε / 2) (half_pos epp) with Nᵥ hb,
  use max Nᵤ Nᵥ,
  intros n n_large,

  specialize ha n (by calc
    n   ≥ max Nᵤ Nᵥ : n_large
    ... ≥ Nᵤ        : le_max_left Nᵤ Nᵥ
  ),
  specialize hb n (by calc
    n   ≥ max Nᵤ Nᵥ : n_large
    ... ≥ Nᵥ        : le_max_right Nᵤ Nᵥ
  ),

  calc  |(u + v) n - (a + b)|
      = |u n + v n - (a + b)|   : rfl
  ... = |(u n - a) + (v n - b)| : by ring_nf
  ... ≤  |u n - a| + |v n - b|  : abs_add (u n - a) (v n - b)
  ... ≤    (ε / 2) + (ε / 2)    : add_le_add ha hb
  ... =            ε            : add_halves ε,
end

-- Squeeze theorem (a.k.a. "Sandwich rule" or "Two policemen and a drunk"):
-- If [`u` approaches `z`] and [`v` approaches `z`],
-- then [`w` such that `u ≤ w ≤ v` approaches `z` as well].
example (u v w : ℕ → ℝ) (z : ℝ) (hu : seq_limit u z) (hv : seq_limit v z)
        (below : ∀ n, u n ≤ w n) (above : ∀ n, w n ≤ v n) :
  seq_limit w z :=
begin
  intros ε epp,
  cases hu ε epp with Nᵤ huz,
  cases hv ε epp with Nᵥ hvz,
  use max Nᵤ Nᵥ,
  intros n n_large,
  specialize huz n (le_of_max_le_left  n_large),
  specialize hvz n (le_of_max_le_right n_large),
  specialize below n,
  specialize above n,
  cases abs_sub_le_iff.mp huz with hu_left hu_right,
  cases abs_sub_le_iff.mp hvz with hv_left hv_right,
  rw abs_sub_le_iff,
  split;
  linarith,
end

-- A sequence admits at most one limit.
example (w : ℕ → ℝ) (a b : ℝ) (ha : seq_limit w a) (hb : seq_limit w b) :
  a = b :=
begin
  apply eq_of_abs_sub_le_all_pos,
  intros ε epp,
  cases ha (ε / 2) (half_pos epp) with N₁ hwa,
  cases hb (ε / 2) (half_pos epp) with N₂ hwb,
  specialize hwa (max N₁ N₂) (le_max_left  N₁ N₂),
  specialize hwb (max N₁ N₂) (le_max_right N₁ N₂),
  cases abs_sub_le_iff.mp hwa with ha_left ha_right,
  cases abs_sub_le_iff.mp hwb with hb_left hb_right,
  rw abs_sub_le_iff,
  split;
  linarith,
end
