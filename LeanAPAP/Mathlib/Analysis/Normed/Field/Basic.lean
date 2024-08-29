import Mathlib.Analysis.Normed.Field.Basic

variable {R : Type*} [SeminormedRing R] {a b c : R}

lemma norm_one_sub_mul (ha : ‖a‖ ≤ 1) : ‖c - a * b‖ ≤ ‖c - a‖ + ‖1 - b‖ :=
  calc
    _ ≤ ‖c - a‖ + ‖a * (1 - b)‖ := by
        simpa [mul_one_sub] using norm_sub_le_norm_sub_add_norm_sub c a (a * b)
    _ ≤ ‖c - a‖ + ‖a‖ * ‖1 - b‖ := by gcongr; exact norm_mul_le ..
    _ ≤ ‖c - a‖ + 1 * ‖1 - b‖ := by gcongr
    _ = ‖c - a‖ + ‖1 - b‖ := by simp

lemma norm_one_sub_mpul' (hb : ‖b‖ ≤ 1) : ‖c - a * b‖ ≤ ‖1 - a‖ + ‖c - b‖ := by
  rw [add_comm]; exact norm_one_sub_mul (R := Rᵐᵒᵖ) hb

lemma nnnorm_one_sub_mul (ha : ‖a‖₊ ≤ 1) : ‖c - a * b‖₊ ≤ ‖c - a‖₊ + ‖1 - b‖₊ := norm_one_sub_mul ha
lemma nnnorm_one_sub_mul' (hb : ‖b‖₊ ≤ 1) : ‖c - a * b‖₊ ≤ ‖1 - a‖₊ + ‖c - b‖₊ :=
  norm_one_sub_mul' hb
