import Mathlib.Data.Nat.Prime
import Mathlib.Data.Nat.Parity

namespace Nat
variable {n : ℕ}

@[simp] lemma coprime_two_left : coprime 2 n ↔ Odd n := by
  rw [prime_two.coprime_iff_not_dvd, odd_iff_not_even, even_iff_two_dvd]

@[simp] lemma coprime_two_right : n.coprime 2 ↔ Odd n := coprime_comm.trans coprime_two_left

alias ⟨coprime.odd_of_left, _root_.Odd.coprime_two_left⟩ := coprime_two_left
alias ⟨coprime.odd_of_right, _root_.Odd.coprime_two_right⟩ := coprime_two_right

end Nat
