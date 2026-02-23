import LeanFun.Definitions

open abelian

theorem theorem_1_place_notation_exponential_expansion
  (n b : ℕ)
  (h1 : 1 ≤ n)
  (hb : 2 ≤ b) :
  let M := MacroSet n b
  (∃ (d1 d2 : ℝ), ∀ (x : ℕ), (x ≥ b) → 0 < d1 ∧ 0 < d2
      ∧ d1 * (Real.log x) ≤ (M ∩ (Ball x (A n))).ncard
      ∧ (M ∩ (Ball x (A n))).ncard ≤ d2 * (Real.log x))
    ∧
    ∀ s : ℕ, s ≥ 1 → (
      let r1 := Int.toNat <| Int.ceil <| Real.rpow b ((s : ℝ) / (n * (b - 1)) - 1)
      (Ball r1 (A n) ⊆ (Ball s (M ∪ (A n))))
      ∧
      let r2 := 1 + n * b * (Int.toNat <| Int.floor <| Real.rpow b ((s : ℝ) / (n * (b - 1))))
      ¬ (Ball r2 (A n) ⊆ (Ball s (M ∪ (A n))))) :=
      sorry
