import probability.independence.basic
import probability.notation

/-!
# Marcinkiewicz-Zygmund inequality

## TODO

Complex-valued versions.
-/

open measure_theory probability_theory
open_locale big_operators ennreal nnreal measure_theory probability_theory

--TODO: Generalise to `measurable_space`?
variables {Ω : Type*} [measure_space Ω] [is_probability_measure (volume : measure Ω)] {n : ℕ}
  {X : Ω → fin n → ℝ}

lemma marcinkiewicz_zygmund (hXmeas : measurable X) (hXint : integrable X)
  (hX : Indep_fun infer_instance (λ i ω, X ω i)) (hX₀ : ∀ i, 𝔼[λ ω, X ω i] = 0) (m : ℕ) :
  𝔼[λ ω, (∑ i, X ω i) ^ (2 * m)] ≤ (4 * m) ^ m * 𝔼[λ ω, (∑ i, X ω i ^ 2) ^ m] :=
sorry
