import algebra.direct_sum.basic

open function
open_locale direct_sum

variables {ι γ : Type*} [decidable_eq ι] {β : ι → Type*} [Π i, add_comm_monoid (β i)]
  [add_comm_monoid γ]

namespace direct_sum

lemma to_add_monoid_injective : injective (to_add_monoid : (Π i, β i →+ γ) → (⨁ i, β i) →+ γ) :=
begin
  rintro f g h,
  ext i b,
  simpa using fun_like.congr_fun h (direct_sum.of _ i b),
end

@[simp] lemma to_add_monoid_inj {f g : Π i, β i →+ γ} : to_add_monoid f = to_add_monoid g ↔ f = g :=
to_add_monoid_injective.eq_iff

end direct_sum
