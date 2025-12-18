import Mathlib

def BigO (f g : ℕ → ℝ) : Prop :=
  ∃ c > (0:ℝ), ∃ n0 : ℕ, ∀ n ≥ n0, f n ≤ c * g n

namespace Parsons

def f : ℕ → ℝ := fun n => (5:ℝ) * ((n:ℝ)^2) + (12:ℝ) * (n:ℝ) + 40
def g : ℕ → ℝ := fun n => ((n:ℝ)^2)

theorem puzzle : BigO f g := by
  refine ⟨(60 : ℝ), ?_, 1, ?_⟩
  · nlinarith
  · intro n hn
    have hn' : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
    have hsq : (n:ℝ) ≤ ((n:ℝ)^2) := by nlinarith [hn']
    have hone : (1:ℝ) ≤ ((n:ℝ)^2) := by nlinarith [hn']
    have h12 : (12:ℝ) * (n:ℝ) ≤ (12:ℝ) * ((n:ℝ)^2) := by nlinarith [hsq]
    have h40 : (40:ℝ) ≤ (40:ℝ) * ((n:ℝ)^2) := by nlinarith [hone]
    have hsum : f n ≤ (57:ℝ) * ((n:ℝ)^2) := by dsimp [f]; nlinarith [h12, h40]
    have h57_60 : (57:ℝ) * ((n:ℝ)^2) ≤ (60:ℝ) * ((n:ℝ)^2) := by nlinarith [hone]
    have hg : g n = ((n:ℝ)^2) := by rfl
    exact le_trans hsum h57_60

end Parsons
