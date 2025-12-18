import Mathlib

def BigO (f g : ℕ → ℝ) : Prop :=
  ∃ c > (0:ℝ), ∃ n0 : ℕ, ∀ n ≥ n0, f n ≤ c * g n

namespace Parsons

def f : ℕ → ℝ := fun n => (8:ℝ) * ((n:ℝ)^2) + (15:ℝ) * (n:ℝ) + 9
def g : ℕ → ℝ := fun n => ((n:ℝ)^2)

theorem puzzle : BigO f g := by
  refine ⟨(40 : ℝ), ?_, 1, ?_⟩
  · nlinarith
  · intro n hn
    set c : ℝ := (40:ℝ) with hc
    rw [←hc]
    simp [g]
    have hn' : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
    have hsq0 : (0:ℝ) ≤ ((n:ℝ)^2) := by nlinarith [hn']
    have h15 : (15:ℝ) * (n:ℝ) ≤ (15:ℝ) * ((n:ℝ)^2) := by nlinarith [hn']
    have h9 : (9:ℝ) ≤ (9:ℝ) * ((n:ℝ)^2) := by nlinarith [hn']
    have hsum : f n ≤ (32:ℝ) * ((n:ℝ)^2) := by dsimp [f]; nlinarith [h15, h9]

end Parsons
