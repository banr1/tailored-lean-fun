import LeanFun.Definitions

open free

def isGoodDLemma4 (n : ℕ) (c p : ℝ) (d : ℕ) : Prop :=
  (d ≥ 3) ∧ (Real.rpow n d > 4 * (Real.exp 1) * (n + c) * (Real.rpow d (p + 1)))

theorem theorem_4_polynomial_density
  (n : ℕ) (hn : n ≥ 2)
  (M : Set (FreeMonoid (Fin n)))
  (c : ℝ) (hc : c > 0)
  (p : ℝ) (hp : p ≥ 0)
  (hG : ∀ l : ℕ, l ≥ 2 → (Set.ncard { x ∈ M | x.length = l } ≤ c * Real.rpow l p )) :
    ∀ (s d : ℕ), (s ≥ 1) ∧ (isGoodDLemma4 n c p d) → ¬ (Ball (d * s) (A n) ⊆ Ball s (M ∪ (A n))) :=
    sorry
