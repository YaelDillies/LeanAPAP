import Mathlib.Data.Fintype.BigOperators

open Finset

namespace Fintype
variable {α β : Type*} {δ : α → Type*} {s : Finset α} {n : ℕ}

local notation:70 s:70 " ^^ " n:71 => Fintype.piFinset fun _ : Fin n ↦ s

protected lemma _root_.Finset.Nonempty.piFinset_const (hs : s.Nonempty) : (s ^^ n).Nonempty :=
  piFinset_nonempty.2 fun _ ↦ hs

lemma card_piFinset_const (s : Finset α) (n : ℕ) : (s ^^ n).card = s.card ^ n := by simp

end Fintype
