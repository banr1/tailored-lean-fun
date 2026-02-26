import LeanFun.Definitions

open abelian

def DoublyMacroSet (b : ℕ) : Set (FreeAbelianMonoid 1) :=
  { m | ∃ i : Fin 1, ∃ j : ℕ, m = Multiset.replicate (b ^ (b ^ j)) i }

theorem theorem5_density (b : ℕ) (hb : 2 ≤ b) :
  ∃ (d1 d2 : ℝ), ∀ (x : ℕ), x ≥ b ^ b →
    0 < d1 ∧ 0 < d2 ∧
      d1 * (Real.log (Real.log x)) ≤ ((DoublyMacroSet b) ∩ Ball x (A 1)).ncard ∧
      ((DoublyMacroSet b) ∩ Ball x (A 1)).ncard ≤ d2 * (Real.log (Real.log x)) := by
      sorry

theorem theorem5_lower_bound (b : ℕ) (hb : 2 ≤ b) :
  (∃ C₁ B : ℝ,
    0 < C₁ ∧
    (∀ (s : ℕ), (s ≥ B) →
      let rs := Real.rpow s ((b : ℝ) / (b - 1))
      (Ball (Int.toNat <| Int.ceil <| C₁ * rs) (A 1) ⊆ Ball s (M ∪ (A 1))))
    ) := by
    sorry

theorem theorem5_upper_bound (b : ℕ) (hb : 2 ≤ b) :
  (∃ C₂ B : ℝ,
      0 < C₂ ∧
      (∀ (s : ℕ), (s ≥ B) →
      let rs := Real.rpow s ((b : ℝ) / (b - 1))
      ¬ (Ball (1 + Int.toNat <| Int.floor <| C₂ * rs)) (A 1) ⊆ Ball s (M ∪ (A 1)))
    ) := by
    sorry

theorem theorem5_upper_bound_neg (b : ℕ) (hb : 2 ≤ b) :
  let M := DoublyMacroSet b
  ¬ (∃ C₂ B : ℝ,
      0 < C₂ ∧
      (∀ (s : ℕ), (s ≥ B) →
      let rs := Real.rpow s ((b : ℝ) / (b - 1))
      ¬ (Ball (1 + Int.toNat <| Int.floor <| C₂ * rs)) (A 1) ⊆ Ball s (M ∪ (A 1)))
    ) := by
    sorry

theorem theorem5
  (b : ℕ)
  (hb : 2 ≤ b) :
  let M := DoublyMacroSet b
  (∃ (d1 d2 : ℝ), ∀ (x : ℕ), (x ≥ b ^ b) → 0 < d1 ∧ 0 < d2
      ∧ d1 * (Real.log (Real.log x)) ≤ (M ∩ (Ball x (A 1))).ncard
      ∧ (M ∩ (Ball x (A 1))).ncard ≤ d2 * (Real.log (Real.log x))) ∧
  (∃ C₁ C₂ B : ℝ,
    0 < C₁ ∧ 0 < C₂ ∧
    (∀ (s : ℕ), (s ≥ B) →
      let rs := Real.rpow s ((b : ℝ) / (b - 1))
      (Ball (Int.toNat <| Int.ceil <| C₁ * rs) (A 1) ⊆ Ball s (M ∪ (A 1))) ∧
        ¬ (Ball (1 + Int.toNat <| Int.floor <| C₂ * rs)) (A 1) ⊆ Ball s (M ∪ (A 1)))
    ) :=
  sorry
