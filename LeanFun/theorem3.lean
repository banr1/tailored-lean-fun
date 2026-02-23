import LeanFun.Definitions

open abelian

def isWarring (k : ℕ) (n : ℕ) : Prop :=
  ∀ x : ℕ, ∃ l : List ℕ, l.length ≤ n ∧ (l.map (fun (y : ℕ) => y ^ k)).sum = x

theorem Ball_add {n R S : ℕ} {X : Set (FreeAbelianMonoid n)} {m₁ m₂ : FreeAbelianMonoid n} :
  m₁ ∈ Ball R X → m₂ ∈ Ball S X → m₁ + m₂ ∈ Ball (R + S) X := by
  intro hm1 hm2
  rcases hm1 with ⟨l1, hl1len, hl1mem, hl1sum⟩
  rcases hm2 with ⟨l2, hl2len, hl2mem, hl2sum⟩
  refine ⟨l1 ++ l2, ?_, ?_, ?_⟩
  ·
    have h : l1.length + l2.length ≤ R + S := Nat.add_le_add hl1len hl2len
    simpa [List.length_append] using h
  ·
    intro x hx
    have hx' : x ∈ l1 ∨ x ∈ l2 := by
      simpa [List.mem_append] using hx
    cases hx' with
    | inl hx1 => exact hl1mem x hx1
    | inr hx2 => exact hl2mem x hx2
  ·
    calc
      (l1 ++ l2).sum = l1.sum + l2.sum := by
        simpa using List.sum_append l1 l2
      _ = m₁ + m₂ := by
        rw [hl1sum, hl2sum]


def PolyMacroSet (n k : ℕ) : Set (FreeAbelianMonoid n) :=
  { m | ∃ i : Fin n, ∃ t : ℕ, 1 ≤ t ∧ m = Multiset.replicate (t ^ k) i }

theorem ball_A_iff_card_le (n r : ℕ) (m : FreeAbelianMonoid n) : m ∈ Ball r (A n) ↔ m.card ≤ r := by
  classical
  constructor
  · intro hm
    rcases hm with ⟨l, hl_len, hl_mem, hl_sum⟩

    have hcard : m.card = (l.map Multiset.card).sum := by
      -- `card` is an additive monoid hom, so it preserves list sums.
      simpa using (by
        simpa [hl_sum] using (Multiset.cardHom.map_list_sum l))

    have hsum_len : (l.map Multiset.card).sum = l.length := by
      -- Every element of `A n` is a singleton, hence has card `1`.
      clear hl_len hl_sum hcard
      revert hl_mem
      induction l with
      | nil =>
          intro hl_mem
          simp
      | cons a t ih =>
          intro hl_mem
          have ha_mem : a ∈ A n := hl_mem a (by simp)
          have ha_card : a.card = 1 := by
            rcases (by simpa [A] using ha_mem) with ⟨i, rfl⟩
            simpa using (Multiset.card_singleton i)
          have ht_mem : ∀ x, x ∈ t → x ∈ A n := by
            intro x hx
            exact hl_mem x (by simp [hx])
          have ih' : (t.map Multiset.card).sum = t.length := ih ht_mem
          simp [List.sum_cons, List.length_cons, ha_card, ih', Nat.succ_eq_add_one, Nat.add_comm,
            Nat.add_left_comm, Nat.add_assoc]

    have hm_len : m.card = l.length := by
      calc
        m.card = (l.map Multiset.card).sum := hcard
        _ = l.length := hsum_len

    -- Now `m.card = l.length ≤ r`.
    simpa [hm_len.symm] using hl_len

  · intro hmcard
    refine ⟨m.toList.map (fun i : Fin n => ({i} : Multiset (Fin n))), ?_, ?_, ?_⟩

    · -- Length bound.
      have hlen : (m.toList.map (fun i : Fin n => ({i} : Multiset (Fin n)))).length = m.card := by
        simp [Multiset.length_toList]
      simpa [hlen] using hmcard

    · -- Each element lies in `A n`.
      intro x hx
      -- Extract the index `i` such that `x = {i}`.
      have hx' : ∃ i : Fin n, ({i} : Multiset (Fin n)) = x := by
        revert x hx
        induction m.toList with
        | nil =>
            intro x hx
            cases hx
        | cons a t ih =>
            intro x hx
            have hx'' : x = ({a} : Multiset (Fin n)) ∨
                x ∈ t.map (fun i : Fin n => ({i} : Multiset (Fin n))) := by
              simpa [List.mem_cons] using hx
            cases hx'' with
            | inl hxa =>
                refine ⟨a, hxa.symm⟩
            | inr hxt =>
                exact ih x hxt
      simpa [A] using hx'

    · -- Sum equals `m`.
      let f : Fin n → Multiset (Fin n) := fun i => ({i} : Multiset (Fin n))
      calc
        (m.toList.map f).sum
            = (((m.toList.map f : List (Multiset (Fin n))) : Multiset (Multiset (Fin n))).sum) := by
                simpa using (Multiset.sum_coe (l := (m.toList.map f))).symm
        _ = ((Multiset.map f (m.toList : Multiset (Fin n))).sum) := by
              -- Rewrite the coerced list as a multiset map.
              have hmap : ((m.toList.map f : List (Multiset (Fin n))) : Multiset (Multiset (Fin n))) =
                  Multiset.map f (m.toList : Multiset (Fin n)) := by
                simpa using (Multiset.map_coe f m.toList).symm
              simpa [hmap]
        _ = (m.toList : Multiset (Fin n)) := by
              simpa [f] using (Multiset.sum_map_singleton (s := (m.toList : Multiset (Fin n))))
        _ = m := by
              simpa using (Multiset.coe_toList m)


theorem ncard_pow_le_rpow (k r : ℕ) (hk : k ≥ 2) :
  ({t : ℕ | 1 ≤ t ∧ t ^ k ≤ r} : Set ℕ).ncard ≤ Real.rpow r ((1 : ℝ) / k) := by
  classical
  let S : Set ℕ := {t : ℕ | 1 ≤ t ∧ t ^ k ≤ r}
  let root : ℝ := Real.rpow (r : ℝ) ((1 : ℝ) / (k : ℝ))
  have hkpos_nat : 0 < k := by
    omega
  have hkpos : (0 : ℝ) < (k : ℝ) := by
    exact_mod_cast hkpos_nat
  have hsub : S ⊆ Set.Icc 1 (Nat.floor root) := by
    intro t ht
    rcases ht with ⟨ht1, htPow⟩
    refine ⟨ht1, ?_⟩
    have htPow' : ((t : ℝ) ^ k) ≤ (r : ℝ) := by
      have : ((t ^ k : ℕ) : ℝ) ≤ (r : ℝ) := by
        exact_mod_cast htPow
      simpa [Nat.cast_pow] using this
    have htPow'' : ((t : ℝ) ^ (k : ℝ)) ≤ (r : ℝ) := by
      simpa [Real.rpow_natCast] using htPow'
    have ht_le_root' : (t : ℝ) ≤ (r : ℝ) ^ ((k : ℝ)⁻¹) := by
      have hx : (0 : ℝ) ≤ (t : ℝ) := by
        exact_mod_cast (Nat.zero_le t)
      have hy : (0 : ℝ) ≤ (r : ℝ) := by
        exact_mod_cast (Nat.zero_le r)
      exact (Real.le_rpow_inv_iff_of_pos hx hy hkpos).2 htPow''
    have ht_le_root : (t : ℝ) ≤ root := by
      simpa [root, one_div] using ht_le_root'
    exact Nat.le_floor ht_le_root
  have hfinite_Icc : (Set.Icc 1 (Nat.floor root)).Finite := by
    simpa using (Set.finite_Icc (a := (1 : ℕ)) (b := Nat.floor root))
  have hncard_le : S.ncard ≤ (Set.Icc 1 (Nat.floor root)).ncard :=
    Set.ncard_le_ncard hsub hfinite_Icc
  have hIcc_ncard : (Set.Icc 1 (Nat.floor root)).ncard = Nat.floor root := by
    -- convert to finset card
    have h1 : (Set.Icc 1 (Nat.floor root)).ncard = (Finset.Icc (1 : ℕ) (Nat.floor root)).card := by
      -- ncard of coe finset
      simpa [Finset.coe_Icc] using
        (Set.ncard_coe_finset (s := Finset.Icc (1 : ℕ) (Nat.floor root)))
    -- compute card of finset Icc
    have h2 : (Finset.Icc (1 : ℕ) (Nat.floor root)).card = Nat.floor root := by
      -- Nat.card_Icc gives card = b + 1 - a
      have : (Finset.Icc (1 : ℕ) (Nat.floor root)).card = Nat.floor root + 1 - 1 := by
        simpa using (Nat.card_Icc (a := (1 : ℕ)) (b := Nat.floor root))
      simpa using this
    exact h1.trans h2
  have hncard_le_floor : S.ncard ≤ Nat.floor root := by
    simpa [hIcc_ncard] using hncard_le
  have hroot_nonneg : (0 : ℝ) ≤ root := by
    have : (0 : ℝ) ≤ (r : ℝ) := by
      exact_mod_cast (Nat.zero_le r)
    simpa [root] using (Real.rpow_nonneg this ((1 : ℝ) / (k : ℝ)))
  have hfloor_le_root : (Nat.floor root : ℝ) ≤ root := by
    simpa using (Nat.floor_le hroot_nonneg)
  have : (S.ncard : ℝ) ≤ root := by
    -- cast hncard_le_floor to ℝ
    have hncard_le_floor' : (S.ncard : ℝ) ≤ (Nat.floor root : ℝ) := by
      exact_mod_cast hncard_le_floor
    exact le_trans hncard_le_floor' hfloor_le_root
  simpa [S, root] using this

theorem polyMacroSet_inter_ball_ncard_le (n k r : ℕ) (hk : k ≥ 2) :
  (PolyMacroSet n k ∩ Ball r (A n)).ncard ≤ n * ({t : ℕ | 1 ≤ t ∧ t ^ k ≤ r} : Set ℕ).ncard := by
  classical
  let S : Set ℕ := {t : ℕ | 1 ≤ t ∧ t ^ k ≤ r}
  let D : Set (Fin n × ℕ) := (Set.univ : Set (Fin n)) ×ˢ S
  let f : Fin n × ℕ → FreeAbelianMonoid n := fun p => Multiset.replicate (p.2 ^ k) p.1
  have hsubset : PolyMacroSet n k ∩ Ball r (A n) ⊆ f '' D := by
    intro m hm
    rcases hm with ⟨hmPoly, hmBall⟩
    rcases hmPoly with ⟨i, t, ht1, rfl⟩
    have hcard : (Multiset.replicate (t ^ k) i : FreeAbelianMonoid n).card ≤ r := by
      exact (ball_A_iff_card_le n r (Multiset.replicate (t ^ k) i)).1 hmBall
    have htk : t ^ k ≤ r := by
      simpa [Multiset.card_replicate] using hcard
    refine ⟨(i, t), ?_, rfl⟩
    refine Set.mem_prod.2 ?_
    refine ⟨by simp, ?_⟩
    exact ⟨ht1, htk⟩

  have hSsubset : S ⊆ Set.Icc 1 r := by
    intro t ht
    rcases ht with ⟨ht1, htk⟩
    refine ⟨ht1, ?_⟩
    have hk0 : k ≠ 0 := by omega
    have ht_le_pow : t ≤ t ^ k := le_self_pow ht1 hk0
    exact le_trans ht_le_pow htk

  have hSfinite : S.Finite := by
    exact (Set.finite_Icc (1 : ℕ) r).subset hSsubset

  have hDfinite : D.Finite := by
    -- product of a finite type with a finite set
    simpa [D] using (Set.finite_univ.prod hSfinite)

  have h1 : (PolyMacroSet n k ∩ Ball r (A n)).ncard ≤ (f '' D).ncard := by
    exact Set.ncard_le_ncard hsubset (hDfinite.image f)

  have h2 : (f '' D).ncard ≤ D.ncard := by
    haveI : Finite D := hDfinite.to_subtype
    simpa using (Set.ncard_image_le (f := f) (s := D))

  have hDcard : D.ncard = n * S.ncard := by
    -- compute ncard of a product
    simp [D, Set.ncard_prod, Set.ncard_univ, Nat.card_fin, Nat.mul_assoc, Nat.mul_left_comm,
      Nat.mul_comm]

  calc
    (PolyMacroSet n k ∩ Ball r (A n)).ncard ≤ (f '' D).ncard := h1
    _ ≤ D.ncard := h2
    _ = n * S.ncard := hDcard
    _ = n * ({t : ℕ | 1 ≤ t ∧ t ^ k ≤ r} : Set ℕ).ncard := by
      simp [S]


theorem polyMacroSet_growth_bound (n k : ℕ) (hk : k ≥ 2) :
  ∀ r : ℕ, (PolyMacroSet n k ∩ Ball r (A n)).ncard ≤ (n : ℝ) * Real.rpow r ((1 : ℝ) / k) := by
  classical
  intro r
  let S : Set ℕ := {t : ℕ | 1 ≤ t ∧ t ^ k ≤ r}
  have hnat : (PolyMacroSet n k ∩ Ball r (A n)).ncard ≤ n * S.ncard := by
    simpa [S] using polyMacroSet_inter_ball_ncard_le n k r hk
  have h1 : ((PolyMacroSet n k ∩ Ball r (A n)).ncard : ℝ) ≤ (n * S.ncard : ℝ) := by
    exact_mod_cast hnat
  have hS : (S.ncard : ℝ) ≤ Real.rpow r ((1 : ℝ) / k) := by
    simpa [S] using ncard_pow_le_rpow k r hk
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := by
    positivity
  have h2 : (n * S.ncard : ℝ) ≤ (n : ℝ) * Real.rpow r ((1 : ℝ) / k) := by
    have h2' : (n : ℝ) * (S.ncard : ℝ) ≤ (n : ℝ) * Real.rpow r ((1 : ℝ) / k) :=
      mul_le_mul_of_nonneg_left hS hn0
    simpa [Nat.cast_mul] using h2'
  exact le_trans h1 h2

theorem replicate_warring_mem_ball (n k g : ℕ) (hk : k ≥ 2) (i : Fin n) (x : ℕ) :
  isWarring k g → Multiset.replicate x i ∈ Ball g (PolyMacroSet n k ∪ A n) := by
  intro hg
  rcases hg x with ⟨l, hl_len, hl_sum⟩
  -- remove zero terms
  let l' : List ℕ := l.filter (fun y => y ≠ 0)
  have hl'len : l'.length ≤ g := by
    have hsub : List.Sublist l' l := by
      simpa [l'] using (List.filter_sublist (l := l) (p := fun y : ℕ => y ≠ 0))
    have : l'.length ≤ l.length := hsub.length_le
    exact le_trans this hl_len
  have hk0 : k ≠ 0 := by
    have : (0 : ℕ) < k := lt_of_lt_of_le (by decide : (0 : ℕ) < 2) hk
    exact Nat.ne_of_gt this
  have hl'sum : (l'.map (fun y => y ^ k)).sum = x := by
    -- compare with the "conditional" sum and use `0^k = 0`
    have hfilter : (l.map (fun y => if y ≠ 0 then y ^ k else 0)).sum =
        (l'.map (fun y => y ^ k)).sum := by
      -- `List.sum_map_ite` gives a decomposition; the "else" part is zero.
      simpa [l', Nat.add_zero] using
        (List.sum_map_ite (l := l) (p := fun y : ℕ => y ≠ 0)
          (f := fun y : ℕ => y ^ k) (g := fun _ : ℕ => (0 : ℕ)))
    have hcond : (l.map (fun y => if y ≠ 0 then y ^ k else 0)).sum = (l.map (fun y => y ^ k)).sum := by
      -- pointwise simplify the map
      refine congrArg List.sum ?_
      refine List.map_congr_left ?_
      intro y hy
      by_cases hy0 : y = 0
      · subst hy0
        simp [hk0]
      · have : y ≠ 0 := hy0
        simp [this]
    -- finish
    calc
      (l'.map (fun y => y ^ k)).sum
          = (l.map (fun y => if y ≠ 0 then y ^ k else 0)).sum := by simpa using hfilter.symm
      _ = (l.map (fun y => y ^ k)).sum := hcond
      _ = x := hl_sum
  -- build the macro list in the free abelian monoid
  let L : List (FreeAbelianMonoid n) := l'.map (fun y => Multiset.replicate (y ^ k) i)
  refine ⟨L, ?_, ?_, ?_⟩
  · -- length bound
    simpa [L] using hl'len
  · -- membership in the union
    intro m hm
    rcases List.mem_map.1 hm with ⟨y, hy, rfl⟩
    refine Or.inl ?_
    have hydec : decide (y ≠ 0) = true := List.of_mem_filter (p := fun z : ℕ => z ≠ 0) hy
    have hy0 : y ≠ 0 := (Bool.decide_iff (p := y ≠ 0)).1 hydec
    have hy1 : 1 ≤ y := Nat.succ_le_iff.mpr (Nat.pos_of_ne_zero hy0)
    exact ⟨i, y, hy1, rfl⟩
  · -- compute the sum
    let f : ℕ →+ Multiset (Fin n) := Multiset.replicateAddMonoidHom i
    have hL : L = (l'.map (fun y => y ^ k)).map f := by
      -- rewrite each `replicate` as an application of the homomorphism
      simp [L, f, List.map_map, Function.comp, Multiset.replicateAddMonoidHom_apply]
    calc
      L.sum = ((l'.map (fun y => y ^ k)).map f).sum := by simpa [hL]
      _ = f ((l'.map (fun y => y ^ k)).sum) := by
        simpa using (f.map_list_sum (l'.map (fun y => y ^ k))).symm
      _ = Multiset.replicate ((l'.map (fun y => y ^ k)).sum) i := by
        simp [f, Multiset.replicateAddMonoidHom_apply]
      _ = Multiset.replicate x i := by
        simpa [hl'sum]

theorem sum_univ_replicate_count (n : ℕ) (m : FreeAbelianMonoid n) :
  (Finset.univ.sum (fun i : Fin n => Multiset.replicate (m.count i) i)) = m := by
  classical
  ext a
  simp [Multiset.count_sum', Multiset.count_replicate, Finset.sum_ite_eq]

theorem polyMacroSet_warring_all (n k g : ℕ) (hk : k ≥ 2) :
  isWarring k g → ∀ m : FreeAbelianMonoid n, m ∈ Ball (n * g) (PolyMacroSet n k ∪ A n) := by
  classical
  intro hg m
  let X : Set (FreeAbelianMonoid n) := PolyMacroSet n k ∪ A n
  have hsum : (Finset.univ.sum (fun i : Fin n => Multiset.replicate (m.count i) i)) ∈ Ball (n * g) X := by
    have hfinset :
        ∀ s : Finset (Fin n),
          (s.sum (fun i : Fin n => Multiset.replicate (m.count i) i)) ∈ Ball (s.card * g) X := by
      intro s
      classical
      refine Finset.induction_on s ?base ?step
      · -- empty
        -- simplify sum and card
        -- `Ball 0 X` contains 0 via empty list
        change (0 : FreeAbelianMonoid n) ∈ Ball (0 * g) X
        -- unfold Ball
        dsimp [Ball]
        refine ⟨[], ?_, ?_, ?_⟩
        · simp
        · intro x hx
          simp at hx
        · simp
      · intro a s ha ih
        have haBall : Multiset.replicate (m.count a) a ∈ Ball g X :=
          replicate_warring_mem_ball n k g hk a (m.count a) hg
        have hAdd :
            (Multiset.replicate (m.count a) a + s.sum (fun i : Fin n => Multiset.replicate (m.count i) i))
              ∈ Ball (g + s.card * g) X :=
          Ball_add (m₁ := Multiset.replicate (m.count a) a)
            (m₂ := s.sum (fun i : Fin n => Multiset.replicate (m.count i) i))
            (R := g) (S := s.card * g) haBall ih
        have hr : g + s.card * g = (s.card + 1) * g := by
          calc
            g + s.card * g = s.card * g + g := by
              simpa [Nat.add_comm]
            _ = (s.card + 1) * g := by
              have hmul : (s.card + 1) * g = s.card * g + g := by
                simpa [Nat.add_mul, Nat.one_mul] using (Nat.add_mul s.card 1 g)
              exact hmul.symm
        have hAdd' :
            (Multiset.replicate (m.count a) a + s.sum (fun i : Fin n => Multiset.replicate (m.count i) i))
              ∈ Ball ((s.card + 1) * g) X := by
          simpa [hr] using hAdd
        simpa [Finset.sum_insert, ha, Finset.card_insert_of_not_mem ha] using hAdd'
    have huniv' := hfinset (Finset.univ : Finset (Fin n))
    simpa [X, Finset.card_univ, Fintype.card_fin] using huniv'
  simpa [X, sum_univ_replicate_count n m] using hsum

theorem polyMacroSet_warring_ball (n k g : ℕ) (hk : k ≥ 2) :
  isWarring k g → ∀ r : ℕ, Ball r (A n) ⊆ Ball (n * g) (PolyMacroSet n k ∪ A n) := by
  intro hg r m hm
  exact polyMacroSet_warring_all n k g hk hg m


theorem theorem_3_polynomial_density (n k : ℕ) (hk : k ≥ 2) :
  ∃ (M : Set (FreeAbelianMonoid n)),
    (∀ (r : ℕ), (M ∩ (Ball r (A n))).ncard ≤ n * (Real.rpow r ((1 : ℝ) / k))) ∧
    (∀ (g : ℕ), (isWarring k g) → (∀ (r : ℕ), (Ball r (A n)) ⊆ (Ball (n * g) (M ∪ (A n))))) := by
  classical
  refine ⟨PolyMacroSet n k, ?_⟩
  refine ⟨?_, ?_⟩
  · intro r
    -- growth bound
    simpa using polyMacroSet_growth_bound n k hk r
  · intro g hg
    intro r
    -- warring ball
    simpa using polyMacroSet_warring_ball n k g hk hg r


