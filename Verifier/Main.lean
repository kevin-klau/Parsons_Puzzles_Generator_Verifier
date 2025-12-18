import Mathlib

def BigO (f g : ℕ → ℝ) : Prop :=
  ∃ c > (0:ℝ), ∃ n0 : ℕ, ∀ n ≥ n0, f n ≤ c * g n

namespace Parsons

def f : ℕ → ℝ := fun n => (11:ℝ) * ((n:ℝ)^2) + (6:ℝ) * (n:ℝ) + (15:ℝ)
def g : ℕ → ℝ := fun n => ((n:ℝ)^2)

theorem puzzle : BigO f g := by
  refine ⟨(37 : ℝ), ?_, 1, ?_⟩
  · nlinarith
  · intro n hn
    simp [Parsons.f, Parsons.g]
    have hn' : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
    have hsq : (n:ℝ) ≤ ((n:ℝ)^2) := by nlinarith [hn']
    have h1sq : (1:ℝ) ≤ ((n:ℝ)^2) := by nlinarith [hn']
    have hb : (6:ℝ) * (n:ℝ) ≤ (6:ℝ) * ((n:ℝ)^2) := by nlinarith [hsq]
    have hd : (15:ℝ) ≤ (15:ℝ) * ((n:ℝ)^2) := by nlinarith [h1sq]
    have hsum : (11:ℝ) * ((n:ℝ)^2) + (6:ℝ) * (n:ℝ) + (15:ℝ) ≤ (32:ℝ) * ((n:ℝ)^2) := by nlinarith [hb, hd]
    have hn2nonneg : (0:ℝ) ≤ ((n:ℝ)^2) := by exact sq_nonneg (n:ℝ)
    have hbound : (32:ℝ) * ((n:ℝ)^2) ≤ (37:ℝ) * ((n:ℝ)^2) := by nlinarith [hn2nonneg]
    exact le_trans hsum hbound

end Parsons
