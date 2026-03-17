import LeanFun.Definitions

open abelian

def DoublyMacroSet (b : ℕ) : Set (FreeAbelianMonoid 1) :=
  { m | ∃ i : Fin 1, ∃ j : ℕ, m = Multiset.replicate (b ^ (b ^ j)) i }

theorem theorem6
  (b : ℕ)
  (hb : 2 ≤ b) :
  let M := DoublyMacroSet b
  (∃ (d1 d2 : ℝ), ∀ (x : ℕ), (x ≥ b ^ b) → 0 < d1 ∧ 0 < d2
      ∧ d1 * (Real.log (Real.log x)) ≤ (M ∩ (Ball x (A 1))).ncard
      ∧ (M ∩ (Ball x (A 1))).ncard ≤ d2 * (Real.log (Real.log x))) ∧
  (∃ C₁ C₂ : ℝ,
    0 < C₁ ∧ 0 < C₂ ∧
    (∀ (s : ℕ), (s ≥ 1) →
      let lb := Real.rpow s ((b : ℝ) / (b - 1))
      (Ball (Int.toNat <| Int.ceil <| C₁ * lb) (A 1) ⊆ Ball s (M ∪ (A 1))) ∧
        let ub := Real.rpow s ((2 * (b : ℝ) - 1) / (b - 1))
        ¬ (Ball (1 + Int.toNat <| Int.floor <| C₂ * ub) (A 1) ⊆ Ball s (M ∪ (A 1))))) :=
  sorry
