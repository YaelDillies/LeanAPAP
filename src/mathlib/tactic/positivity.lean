import tactic.positivity

namespace tactic
open positivity
open_locale positivity
variables {R : Type*}

private lemma pow_nonneg_of_pos [ordered_semiring R] {a : R} (ha : 0 < a) (n : ℕ) : 0 ≤ a ^ n :=
pow_nonneg ha.le _

private lemma pow_zero_pos [ordered_semiring R] [nontrivial R] (a : R) : 0 < a ^ 0 :=
zero_lt_one.trans_le (pow_zero a).ge

private lemma zpow_zero_pos [linear_ordered_semifield R] (a : R) : 0 < a ^ (0 : ℤ) :=
zero_lt_one.trans_le (zpow_zero a).ge

/-- Extension for the `positivity` tactic: raising a number `a` to a natural/integer power `n` is
positive if `n = 0` (since `a ^ 0 = 1`) or if `0 < a`, and is nonnegative if `n` is even (squares
are nonnegative) or if `0 ≤ a`. -/
@[positivity]
meta def positivity_pow' : expr → tactic strictness
| e@`(%%a ^ %%n) := do
  typ ← infer_type n,
  (do
    unify typ `(ℕ),
    if n = `(0) then
      positive <$> mk_app ``pow_zero_pos [a]
    else
      do -- even powers are nonnegative
      -- Note this is automatically strengthened to `0 < a ^ n` when `a ≠ 0` thanks to the `orelse'`
        match n with -- TODO: Decision procedure for parity
        | `(bit0 %% n) := nonnegative <$> mk_app ``pow_bit0_nonneg [a, n]
        | _ := do
                  e' ← pp e,
                  fail (e' ++ "is not an even power so positivity can't prove it's nonnegative")
        end ≤|≥
      do -- `a ^ n` is positive if `a` is, and nonnegative if `a` is
        strictness_a ← core a,
        match strictness_a with
        | positive p := (positive <$> mk_app ``pow_pos [p, n]) <|>
            nonnegative <$> mk_app ``pow_nonneg_of_pos [p, n]
        | nonnegative p := nonnegative <$> mk_app `pow_nonneg [p, n]
        | nonzero p := nonzero <$> to_expr ``(pow_ne_zero %%n %%p)
        end) <|>
  (do
    unify typ `(ℤ),
    if n = `(0 : ℤ) then
      positive <$> mk_app ``zpow_zero_pos [a]
    else
      do -- even powers are nonnegative
    -- Note this is automatically strengthened to `0 < a ^ n` when `a ≠ 0` thanks to the `orelse'`
        match n with -- TODO: Decision procedure for parity
        | `(bit0 %%n) := nonnegative <$> mk_app ``zpow_bit0_nonneg [a, n]
        | _ := do
                  e' ← pp e,
                  fail (e' ++ "is not an even power so positivity can't prove it's nonnegative")
            end ≤|≥
      do -- `a ^ n` is positive if `a` is, and nonnegative if `a` is
        strictness_a ← core a,
        match strictness_a with
        | positive p := positive <$> mk_app ``zpow_pos_of_pos [p, n]
        | nonnegative p := nonnegative <$> mk_app ``zpow_nonneg [p, n]
        | nonzero p := nonzero <$> to_expr ``(zpow_ne_zero %%n %%p)
        end)
| e := pp e >>= fail ∘ format.bracket "The expression `" "` isn't of the form `a ^ n`"

end tactic
