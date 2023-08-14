import data.nat.prime
import data.nat.parity

namespace nat
variables {n : ℕ}

@[simp] lemma coprime_two_left : coprime 2 n ↔ odd n :=
by rw [prime_two.coprime_iff_not_dvd, odd_iff_not_even, even_iff_two_dvd]

@[simp] lemma coprime_two_right : n.coprime 2 ↔ odd n := coprime_comm.trans coprime_two_left

alias coprime_two_left ↔ coprime.odd_of_left _root_.odd.coprime_two_left
alias coprime_two_right ↔ coprime.odd_of_right _root_.odd.coprime_two_right

end nat
