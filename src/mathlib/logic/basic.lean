import logic.basic

lemma iff.ne {α β : Sort*} {a₁ a₂ : α} {b₁ b₂ : β} (h : a₁ = a₂ ↔ b₁ = b₂) :
  a₁ ≠ a₂ ↔ b₁ ≠ b₂ := h.not
