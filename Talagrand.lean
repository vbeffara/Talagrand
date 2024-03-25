import Mathlib

set_option autoImplicit false

open Classical Real MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ] {N : ℕ}

def pp (_ : Measure Ω) (N : ℕ) := Fin N → Ω

instance : MeasurableSpace (pp μ N) := MeasurableSpace.pi

noncomputable instance : MeasureSpace (pp μ N) := ⟨Measure.pi (fun _ => μ)⟩

instance : IsProbabilityMeasure (volume : Measure (pp μ N)) := by
  constructor ; simp [volume] ; rw [Measure.pi_univ] ; simp

noncomputable def d (x y : pp μ N) : ℕ := hammingDist x y

lemma d_le_dim {x y : pp μ N} : d x y ≤ N := by
  convert hammingDist_le_card_fintype ; simp

noncomputable def f (A : Set (pp μ N)) (x : pp μ N) : ℕ := ⨅ y ∈ A, d x y

lemma f_empty {x : pp μ N} : f (∅ : Set (pp μ N)) x = 0 := by simp [f]

noncomputable def nnexp (t : ℝ) : NNReal := ⟨exp t, exp_nonneg t⟩

theorem Theorem_2_1_1 {t : ℝ} (ht : 0 < t) (A : Set (pp μ N)) :
    ∫⁻ x, nnexp (t * f A x) ≤ (volume A)⁻¹ * (2⁻¹ + (nnexp t + nnexp (-t)) / 4) ^ N := by

  by_cases hN : N = 0
  · subst N
    simp [pp, f, nnexp, d, hammingDist]
    have : IsProbabilityMeasure (volume : Measure (pp μ 0)) := by infer_instance
    rw [lintegral_coe_eq_integral]
    · simpa using prob_le_one
    · apply integrable_const
  · sorry
