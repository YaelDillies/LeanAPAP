import Mathlib.Data.Fintype.BigOperators

open Finset

namespace Fintype
variable {α β : Type*} {δ : α → Type*} {s : Finset α} {n : ℕ}

@[reducible]
def piFinsetConst (s : Finset α) (n : ℕ) := piFinset fun _ : Fin n ↦ s

infixl:70 "^^" => piFinsetConst

protected lemma _root_.Finset.Nonempty.piFinsetConst (hs : s.Nonempty) : (s ^^ n).Nonempty :=
  piFinset_nonempty.2 fun _ ↦ hs

@[simp] lemma card_piFinsetConst (s : Finset α) (n : ℕ) : (s ^^ n).card = s.card ^ n := by
  simp [piFinsetConst, card_piFinset]

end Fintype
