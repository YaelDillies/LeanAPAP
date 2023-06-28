import algebra.star.pi

open_locale complex_conjugate

--TODO: This is a hack to help Lean synthesize the instance. It has nothing to do with type
-- dependency. Rather, it seems to be about the `non_unital_semiring` structure on `α`.
instance function.star_ring {ι α : Type*} [comm_semiring α] [star_ring α] : star_ring (ι → α) :=
pi.star_ring

@[simp] lemma pi.conj_apply {ι : Type*} {α : ι → Type*} [Π i, comm_semiring (α i)]
  [Π i, star_ring (α i)] (f : Π i, α i) (i : ι) :
  @star_ring_end (Π i, α i) _ (@pi.star_ring ι α _ _) f i = conj (f i) := rfl
