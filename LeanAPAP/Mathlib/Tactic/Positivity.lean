import Mathbin.Tactic.Positivity

#align_import mathlib.tactic.positivity

namespace Tactic

open Positivity

open scoped Positivity

variable {R : Type _}

private theorem pow_nonneg_of_pos [OrderedSemiring R] {a : R} (ha : 0 < a) (n : ℕ) : 0 ≤ a ^ n :=
  pow_nonneg ha.le _

private theorem pow_zero_pos [OrderedSemiring R] [Nontrivial R] (a : R) : 0 < a ^ 0 :=
  zero_lt_one.trans_le (pow_zero a).ge

private theorem zpow_zero_pos [LinearOrderedSemifield R] (a : R) : 0 < a ^ (0 : ℤ) :=
  zero_lt_one.trans_le (zpow_zero a).ge

-- PLEASE REPORT THIS TO MATHPORT DEVS, THIS SHOULD NOT HAPPEN.
-- failed to format: unknown constant 'term.pseudo.antiquot'
/--
      Extension for the `positivity` tactic: raising a number `a` to a natural/integer power `n` is
      positive if `n = 0` (since `a ^ 0 = 1`) or if `0 < a`, and is nonnegative if `n` is even (squares
      are nonnegative) or if `0 ≤ a`. -/
    @[ positivity ]
    unsafe
  def
    positivity_pow'
    : expr → tactic strictness
    |
        e @ q( $ ( a ) ^ $ ( n ) )
        =>
        do
          let typ ← infer_type n
            (
                do
                  unify typ q( ℕ )
                    if
                      n = q( 0 )
                      then
                      positive <$> mk_app ` ` pow_zero_pos [ a ]
                      else
                      do
                        (
                            match
                              n
                              with
                              |
                                  q( bit0 $ ( n ) )
                                  =>
                                  nonnegative <$> mk_app ` ` pow_bit0_nonneg [ a , n ]
                                |
                                  _
                                  =>
                                  do
                                    let e' ← pp e
                                      fail
                                        (
                                          e'
                                            ++
                                            "is not an even power so positivity can't prove it's nonnegative"
                                          )
                            )
                          ≤|≥
                          do
                            let strictness_a ← core a
                              match
                                strictness_a
                                with
                                |
                                    positive p
                                    =>
                                    positive <$> mk_app ` ` pow_pos [ p , n ]
                                      <|>
                                      nonnegative <$> mk_app ` ` pow_nonneg_of_pos [ p , n ]
                                  | nonnegative p => nonnegative <$> mk_app `pow_nonneg [ p , n ]
                                  |
                                    nonzero p
                                    =>
                                    nonzero <$> to_expr ` `( pow_ne_zero $ ( n ) $ ( p ) )
                )
              <|>
              do
                unify typ q( ℤ )
                  if
                    n = q( ( 0 : ℤ ) )
                    then
                    positive <$> mk_app ` ` zpow_zero_pos [ a ]
                    else
                    do
                      (
                          match
                            n
                            with
                            |
                                q( bit0 $ ( n ) )
                                =>
                                nonnegative <$> mk_app ` ` zpow_bit0_nonneg [ a , n ]
                              |
                                _
                                =>
                                do
                                  let e' ← pp e
                                    fail
                                      (
                                        e'
                                          ++
                                          "is not an even power so positivity can't prove it's nonnegative"
                                        )
                          )
                        ≤|≥
                        do
                          let strictness_a ← core a
                            match
                              strictness_a
                              with
                              | positive p => positive <$> mk_app ` ` zpow_pos_of_pos [ p , n ]
                                | nonnegative p => nonnegative <$> mk_app ` ` zpow_nonneg [ p , n ]
                                |
                                  nonzero p
                                  =>
                                  nonzero <$> to_expr ` `( zpow_ne_zero $ ( n ) $ ( p ) )
      | e => pp e >>= fail ∘ format.bracket "The expression `" "` isn't of the form `a ^ n`"

end Tactic

