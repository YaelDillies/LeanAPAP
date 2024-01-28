import Mathlib.Algebra.BigOperators.Ring
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Prod

/-!
## TODO

More explicit arguments to `finset.mul_sum`/`finset.sum_mul`
-/

open scoped BigOperators

namespace Finset
variable {ι α β : Type*}

section CommSemiring
variable [CommSemiring β]

-- TODO: Fix decidability in `Finset.sum_pow'`
lemma sum_pow'' (s : Finset α) (f : α → β) (n : ℕ) :
    (∑ a in s, f a) ^ n = ∑ p in Fintype.piFinset fun _i : Fin n ↦ s, ∏ i, f (p i) := by
  classical exact sum_pow' _ _ _

end CommSemiring

end Finset

namespace Fintype
variable {α β : Type*} [Fintype α] [CommSemiring β]

lemma sum_pow (f : α → β) (n : ℕ) : (∑ a, f a) ^ n = ∑ p : Fin n → α, ∏ i, f (p i) := by
  simp [Finset.sum_pow'']

lemma sum_mul_sum {ι : Type*} {κ : Type*} [Fintype ι] [Fintype κ] (f : ι → β) (g : κ → β) :
    (∑ i, f i) * ∑ j, g j = ∑ i, ∑ j, f i * g j := Finset.sum_mul_sum _ _ _ _

end Fintype

namespace Fintype
variable {α β : Type*} [CommSemiring β] [DecidableEq α] [Fintype α]
open Finset
open scoped BigOperators

lemma prod_add (f g : α → β) : ∏ a, (f a + g a) = ∑ t, (∏ a in t, f a) * ∏ a in tᶜ, g a := by
  simpa [compl_eq_univ_sdiff] using Finset.prod_add f g univ

end Fintype

open Finset

namespace Nat
variable {α : Type*} {s : Finset α} {f : α → ℕ} {n : ℕ}

protected lemma sum_div (hf : ∀ i ∈ s, n ∣ f i) : (∑ i in s, f i) / n = ∑ i in s, f i / n := by
  obtain rfl | hn := n.eq_zero_or_pos
  · simp
  rw [Nat.div_eq_iff_eq_mul_left hn (dvd_sum hf), sum_mul]
  refine' sum_congr rfl fun s hs ↦ _
  rw [Nat.div_mul_cancel (hf _ hs)]

end Nat
