import Mathlib.Order.LiminfLimsup

namespace Filter
variable {α β γ ι ι' : Type*}

lemma IsBoundedUnder.le_of_finite [Nonempty α] [Preorder α] [IsDirected α (· ≤ ·)] [Finite β]
    {f : Filter β} {u : β → α} : IsBoundedUnder (· ≤ ·) f u :=
  (Set.toFinite _).bddAbove.isBoundedUnder univ_mem

lemma IsBoundedUnder.ge_of_finite [Nonempty α] [Preorder α] [IsDirected α (· ≥ ·)] [Finite β]
    {f : Filter β} {u : β → α} : IsBoundedUnder (· ≥ ·) f u :=
  (Set.toFinite _).bddBelow.isBoundedUnder univ_mem

end Filter
