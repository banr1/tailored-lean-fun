import LeanFun.Definitions

open abelian

theorem Ball_mono {n : ℕ} {R : ℕ} {X Y : Set (FreeAbelianMonoid n)} (hXY : X ⊆ Y) :
  Ball R X ⊆ Ball R Y := by
  intro m hm
  rcases hm with ⟨l, hlR, hlX, rfl⟩
  refine ⟨l, hlR, ?_, rfl⟩
  intro x hx
  exact hXY (hlX x hx)


def macroMaxCard (M : Finset (FreeAbelianMonoid 1)) : ℕ :=
  max (M.sup Multiset.card) 1

theorem card_le_mul_macroMax (M : Finset (FreeAbelianMonoid 1)) (s : ℕ) {m : FreeAbelianMonoid 1}
  (hm : m ∈ Ball s (M ∪ A 1)) :
  m.card ≤ s * macroMaxCard M := by
  classical
  rcases hm with ⟨l, hl_len, hl_mem, hl_sum⟩
  have hx_le : ∀ x : FreeAbelianMonoid 1, x ∈ l → x.card ≤ macroMaxCard M := by
    intro x hx
    have hxX : x ∈ (M ∪ A 1 : Set (FreeAbelianMonoid 1)) := hl_mem x hx
    rcases hxX with hxM | hxA
    · -- x ∈ M
      have hle : x.card ≤ M.sup Multiset.card := by
        simpa using (Finset.le_sup (s := M) (f := Multiset.card) hxM)
      exact le_trans hle (by
        simpa [macroMaxCard] using (le_max_left (M.sup Multiset.card) 1))
    · -- x ∈ A 1
      have hxA' : ∃ i : Fin 1, x = ({i} : FreeAbelianMonoid 1) := by
        simpa [A] using hxA
      rcases hxA' with ⟨i, rfl⟩
      simp [macroMaxCard]
  have hcard : m.card = (l.map Multiset.card).sum := by
    have : Multiset.cardHom l.sum = (l.map Multiset.cardHom).sum := by
      simpa using (Multiset.cardHom.map_list_sum l)
    simpa [hl_sum] using this
  have hsum_le : (l.map Multiset.card).sum ≤ l.length * macroMaxCard M := by
    have hbound : ∀ n : ℕ, n ∈ l.map Multiset.card → n ≤ macroMaxCard M := by
      intro n hn
      rcases List.mem_map.1 hn with ⟨x, hx, rfl⟩
      exact hx_le x hx
    have h' := List.sum_le_card_nsmul (l := l.map Multiset.card) (n := macroMaxCard M) hbound
    simpa [Nat.nsmul_eq_mul] using h'
  calc
    m.card = (l.map Multiset.card).sum := hcard
    _ ≤ l.length * macroMaxCard M := hsum_le
    _ ≤ s * macroMaxCard M := by
      exact Nat.mul_le_mul_right (macroMaxCard M) hl_len

theorem replicate_mem_Ball_A1 (r : ℕ) :
  Multiset.replicate r (0 : Fin 1) ∈ Ball r (A 1) := by
  classical
  refine ⟨List.replicate r ({(0 : Fin 1)} : Multiset (Fin 1)), ?_⟩
  refine ⟨?_, ?_⟩
  · simp
  refine ⟨?_, ?_⟩
  · intro x hx
    have hx' : x ∈ ([({(0 : Fin 1)} : Multiset (Fin 1))]) :=
      (List.replicate_subset_singleton r ({(0 : Fin 1)} : Multiset (Fin 1))) hx
    have hxg : x = ({(0 : Fin 1)} : Multiset (Fin 1)) := by
      simpa using hx'
    subst hxg
    exact ⟨(0 : Fin 1), rfl⟩
  · simpa [List.sum_replicate, Multiset.nsmul_singleton]

theorem theorem6 (M : Finset (FreeAbelianMonoid 1)) :
  ∃ C₁ C₂ : ℝ,
    0 < C₁ ∧ 0 < C₂ ∧
    (∀ (s : ℕ), (s ≥ 1) →
      (Ball (Int.toNat <| Int.ceil <| C₁ * s) (A 1) ⊆ Ball s (M ∪ A 1)) ∧
      ¬ (Ball (1 + Int.toNat <| Int.floor <| C₂ * s) (A 1) ⊆ Ball s (M ∪ A 1))
    ) := by
  classical
  let L : ℕ := macroMaxCard M
  refine ⟨(1 : ℝ), (L : ℝ), ?_, ?_, ?_⟩
  · norm_num
  · have h1 : (1 : ℕ) ≤ L := by
      dsimp [L, macroMaxCard]
      exact Nat.le_max_right _ _
    have hLpos : 0 < L := lt_of_lt_of_le Nat.zero_lt_one h1
    exact_mod_cast hLpos
  · intro s hs
    constructor
    · -- inclusion
      have hs' : Int.toNat (Int.ceil ((1 : ℝ) * (s : ℝ))) = s := by
        simp
      simpa [hs'] using
        (Ball_mono (n := 1) (R := s) (X := A 1) (Y := (M ∪ A 1)) (by
          intro x hx
          exact Or.inr hx))
    · -- non-inclusion
      have hfloor : Int.toNat (Int.floor ((L : ℝ) * (s : ℝ))) = L * s := by
        -- rewrite the product as a nat cast
        simpa [Nat.cast_mul, mul_comm, mul_left_comm, mul_assoc] using
          (congrArg Int.toNat (by
            -- `Int.floor_natCast` needs a nat-cast argument
            simpa [Nat.cast_mul, mul_comm, mul_left_comm, mul_assoc] using
              (Int.floor_natCast (R := ℝ) (L * s))))
      let w : FreeAbelianMonoid 1 := Multiset.replicate (1 + L * s) (0 : Fin 1)
      have hwA : w ∈ Ball (1 + L * s) (A 1) := by
        simpa [w] using replicate_mem_Ball_A1 (r := (1 + L * s))
      intro hsub
      have hwMs : w ∈ Ball s (M ∪ A 1) := hsub (by
        simpa [hfloor, w] using hwA)
      have hcard := card_le_mul_macroMax M s (m := w) hwMs
      have hwcard : w.card = 1 + L * s := by
        simp [w]
      have : ¬ (w.card ≤ s * L) := by
        simp [hwcard, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
      exact this (by
        simpa [Nat.mul_comm] using hcard)


