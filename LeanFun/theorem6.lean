import LeanFun.Definitions

open abelian

theorem theorem6
  (M : Finset (FreeAbelianMonoid 1)) :
  ∃ C₁ C₂ : ℝ,
    0 < C₁ ∧ 0 < C₂ ∧
    (∀ (s : ℕ), (s ≥ 1) →
      (Ball (Int.toNat <| Int.ceil <| C₁ * s) (A 1) ⊆ Ball s (M ∪ A 1)) ∧
      ¬ (Ball (1 + Int.toNat <| Int.floor <| C₂ * s) (A 1) ⊆ Ball s (M ∪ A 1))
    ) :=
  sorry
