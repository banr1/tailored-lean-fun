import LeanFun.Definitions

open abelian

theorem theorem_2_quasi_exponential_expansion
  (n : ℕ)
  (h1 : 1 ≤ n)
  (M : Set (FreeAbelianMonoid n))
  (c q : ℝ) (hc : 0 < c) (hq : 0 < q):
  (∀ (r : ℕ), (M ∩ (Ball r (A n))).ncard ≤ c * (Real.rpow (Real.log ((Real.exp 1) + r)) q)) →
    (∃ (K : ℕ), ∀ (s : ℕ), (s ≥ 2) → ((K > 0) ∧
      let r := 1 + Int.toNat <| Int.floor <| Real.exp (K * s * (Real.log s))
      ¬ (Ball r (A n) ⊆ Ball s (M ∪ (A n))))) := by
    sorry
