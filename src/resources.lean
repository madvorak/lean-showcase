import data.real.basic


private meta def finish_proof_about_abs : tactic unit := `[
  unfold abs,
  simp,
  exact le_of_lt h,
  rw undo_abs at *,
  split;
  linarith
]

lemma eq_of_abs_sub_le_all_pos (x y : ℝ) : (∀ ε > 0, |x - y| ≤ ε) → x = y :=
begin
  contrapose!,
  intro ass,
  use |x - y| / 2,
  cases ne.lt_or_lt ass,
  {
    have undo_abs : |x - y| = y - x,
    finish_proof_about_abs,
  },
  {
    have undo_abs : |x - y| = x - y,
    finish_proof_about_abs,
  },
end
