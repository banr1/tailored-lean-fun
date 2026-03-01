import LeanFun.Definitions


open scoped BigOperators
open Filter

open free

def Sphere (n r : ℕ) : Set (FreeMonoid (Fin n)) :=
  {w | w.length = r}

noncomputable def expansion {n : ℕ} (G G' : Set (FreeMonoid (Fin n))) (s : ℕ) : ℕ :=
    sSup { r : ℕ | Ball r G ⊆ Ball s G' }

theorem theorem5_simplification
    (n : ℕ) (hn : 2 ≤ n) :
    ∃ M : Set (FreeMonoid (Fin n)),
      Tendsto
        (fun r : ℕ =>
          ((Set.ncard (M ∩ Sphere n r) : ℝ) / (Set.ncard (Sphere n r) : ℝ)))
        atTop (nhds 0)
      ∧
      ∃ (K : ℕ), 0 < K ∧
        (∀ᶠ r : ℕ in atTop,
          Ball r (A n) ⊆ Ball (K * (Nat.log2 r) ^ 2) (M ∪ (A n))) := by
  sorry

theorem theorem5
    (n : ℕ) (hn : 2 ≤ n) :
    ∃ M : Set (FreeMonoid (Fin n)),
      Tendsto
        (fun r : ℕ =>
          ((Set.ncard (M ∩ Sphere n r) : ℝ) / (Set.ncard (Sphere n r) : ℝ)))
        atTop (nhds 0)
      ∧
      Tendsto
        (fun s : ℕ =>
          ((expansion (A n) (M ∪ (A n)) s : ℝ) / (s : ℝ)))
        atTop atTop
      ∧
      ∃ (K : ℕ) (c : ℝ), 0 < K ∧ 0 < c ∧
        (∀ᶠ r : ℕ in atTop,
          Ball r (A n) ⊆ Ball (K * (Nat.log2 r) ^ 2) (M ∪ (A n)))
        ∧
        (∀ᶠ s : ℕ in atTop,
          (Real.exp (c * Real.sqrt (s : ℝ)) ≤ (expansion (A n) (M ∪ (A n)) s : ℝ))) := by
  sorry
