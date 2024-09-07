import Mathlib.Order.CompleteLattice

variable {α : Type*} [CompleteLattice α]

lemma iSup_le_iSup_of_imp {p q : Prop} {a : α} (h : p → q) : ⨆ _h : p, a ≤ ⨆ _h : q, a := by aesop
lemma iInf_le_iInf_of_imp {p q : Prop} {a : α} (h : p → q) : ⨅ _h : q, a ≤ ⨅ _h : p, a := by aesop
