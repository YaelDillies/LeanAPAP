import Mathlib.Data.NNRat.Lemmas

variable {F ι α β : Type*}

namespace MonoidWithZeroHom
variable {M₀ : Type*} [MonoidWithZero M₀] [FunLike F ℚ≥0 M₀] [MonoidWithZeroHomClass F ℚ≥0 M₀]
  {f g : F}

/-- If `f` and `g` agree on the naturals then they are equal `φ`. -/
lemma ext_nnrat' (h : ∀ n : ℕ, f n = g n) : f = g :=
  (DFunLike.ext f g) fun r => by
    rw [← r.num_div_den, div_eq_mul_inv, map_mul, map_mul, h, eq_on_inv₀ f g]
    apply h

/-- If `f` and `g` agree on the integers then they are equal `φ`.

See note [partially-applied ext lemmas] for why `comp` is used here. -/
@[ext]
lemma ext_nnrat {f g : ℚ≥0 →*₀ M₀}
    (h : f.comp (Nat.castRingHom ℚ≥0 : ℕ →*₀ ℚ≥0) = g.comp (Nat.castRingHom ℚ≥0)) : f = g :=
  ext_nnrat' <| DFunLike.congr_fun h

-- /-- Positive integer values of a morphism `φ` and its value on `-1` completely determine `φ`. -/
-- lemma ext_nnrat_on_pnat (same_on_pnat : ∀ n : ℕ, 0 < n → f n = g n) : f = g :=
--   ext_nnrat' <| FunLike.congr_fun <|
--       show
--         (f : ℚ≥0 →*₀ M₀).comp (Nat.castRingHom ℚ≥0 : ℕ →*₀ ℚ≥0) =
--           (g : ℚ≥0 →*₀ M₀).comp (Nat.castRingHom ℚ≥0 : ℕ →*₀ ℚ≥0)
--         from ext_nat'' (by simpa) (by simpa) (same_on_pnat _)

end MonoidWithZeroHom

-- /-- Any two ring homomorphisms from `ℚ≥0` to a semiring are equal. If the codomain is a division ring,
-- then this lemma follows from `eq_ratCast`. -/
-- lemma RingHom.ext_nnrat {R : Type*} [Semiring R] [RingHomClass F ℚ≥0 R] (f g : F) : f = g :=
--   MonoidWithZeroHom.ext_nnrat' <| RingHom.congr_fun <|
--       ((f : ℚ≥0 →+* R).comp (Nat.castRingHom ℚ≥0)).ext_nat ((g : ℚ≥0 →+* R).comp (Nat.castRingHom ℚ≥0))

-- instance NNRat.subsingleton_ringHom {R : Type*} [Semiring R] : Subsingleton (ℚ≥0 →+* R) :=
--   ⟨RingHom.ext_rat⟩
