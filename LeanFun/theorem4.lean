import LeanFun.Definitions

open free

def isGoodDLemma4 (n : ℕ) (c p : ℝ) (d : ℕ) : Prop :=
  (d ≥ 3) ∧ (Real.rpow n d > 4 * (Real.exp 1) * (n + c) * (Real.rpow d (p + 1)))

theorem lemma4_amgm_composition_prod_le (N : ℕ) (c : Composition N) (hk : 1 ≤ c.length) :
  (∏ i : Fin c.length, (c.blocksFun i : ℝ)) ^ ((c.length : ℝ)⁻¹) ≤ (N : ℝ) / c.length := by
  classical
  have hlen_pos_nat : 0 < c.length := by
    omega
  have hlen_pos_real : (0 : ℝ) < (c.length : ℝ) := by
    exact_mod_cast hlen_pos_nat

  have hw : ∀ i ∈ (Finset.univ : Finset (Fin c.length)), 0 ≤ (1 : ℝ) := by
    intro i hi
    simp

  have hw' : 0 < ∑ i ∈ (Finset.univ : Finset (Fin c.length)), (1 : ℝ) := by
    simpa using hlen_pos_real

  have hz : ∀ i ∈ (Finset.univ : Finset (Fin c.length)), 0 ≤ (c.blocksFun i : ℝ) := by
    intro i hi
    exact_mod_cast (Nat.zero_le (c.blocksFun i))

  have h :=
    Real.geom_mean_le_arith_mean (s := (Finset.univ : Finset (Fin c.length)))
      (w := fun _ => (1 : ℝ)) (z := fun i => (c.blocksFun i : ℝ)) hw hw' hz

  have h' :
      (∏ i : Fin c.length, (c.blocksFun i : ℝ)) ^ ((c.length : ℝ)⁻¹)
        ≤ (∑ i : Fin c.length, (c.blocksFun i : ℝ)) / c.length := by
    -- simplify h
    simpa using h

  have hsum : (∑ i : Fin c.length, (c.blocksFun i : ℝ)) = (N : ℝ) := by
    -- cast sum_blocksFun
    exact_mod_cast c.sum_blocksFun

  simpa [hsum] using h'

theorem lemma4_choose_ds_sub1_le_choose_ds_s (d s k : ℕ) (hk : 1 ≤ k) (hks : k ≤ s) (hd : d ≥ 3) :
  Nat.choose (d * s - 1) (k - 1) ≤ Nat.choose (d * s) s := by
  classical
  set N : ℕ := d * s
  have hs : 1 ≤ s := le_trans hk hks
  have hk1 : k - 1 ≤ s - 1 := Nat.sub_le_sub_right hks 1
  have hhalf : s - 1 ≤ (N - 1) / 2 := by
    have hd2 : 2 ≤ d := le_trans (by decide : (2 : ℕ) ≤ 3) hd
    have h2s_le : 2 * s ≤ N := by
      simpa [N] using (Nat.mul_le_mul_right s hd2)
    have hA : (s - 1) * 2 ≤ 2 * s - 1 := by
      omega
    have hB : 2 * s - 1 ≤ N - 1 := Nat.sub_le_sub_right h2s_le 1
    have h2 : (s - 1) * 2 ≤ N - 1 := le_trans hA hB
    exact (Nat.le_div_iff_mul_le (by decide : 0 < (2 : ℕ))).2 h2
  have hchoose : Nat.choose (N - 1) (k - 1) ≤ Nat.choose (N - 1) (s - 1) := by
    have hP : ∀ n (hn : k - 1 ≤ n), n ≤ s - 1 → Nat.choose (N - 1) (k - 1) ≤ Nat.choose (N - 1) n := by
      refine Nat.le_induction (m := k - 1)
        (P := fun n hn => n ≤ s - 1 → Nat.choose (N - 1) (k - 1) ≤ Nat.choose (N - 1) n) ?_ ?_
      · intro _
        exact le_rfl
      · intro n hn ih
        intro hn1S
        have hnS : n ≤ s - 1 := le_trans (Nat.le_succ n) hn1S
        have hmn : Nat.choose (N - 1) (k - 1) ≤ Nat.choose (N - 1) n := ih hnS
        have hnlt : n < (N - 1) / 2 := by
          have : n + 1 ≤ (N - 1) / 2 := le_trans hn1S hhalf
          exact lt_of_lt_of_le (Nat.lt_succ_self n) this
        have hstep : Nat.choose (N - 1) n ≤ Nat.choose (N - 1) (n + 1) :=
          Nat.choose_le_succ_of_lt_half_left hnlt
        exact le_trans hmn hstep
    exact hP (s - 1) hk1 le_rfl
  have hN1 : 1 ≤ N := by
    have hd1 : 1 ≤ d := le_trans (by decide : (1 : ℕ) ≤ 3) hd
    have h := Nat.mul_le_mul hd1 hs
    simpa [N] using h
  have hpascal : Nat.choose N s = Nat.choose (N - 1) (s - 1) + Nat.choose (N - 1) s := by
    simpa [Nat.sub_add_cancel hN1, Nat.sub_add_cancel hs] using
      (Nat.choose_succ_succ' (N - 1) (s - 1))
  have hsle : Nat.choose (N - 1) (s - 1) ≤ Nat.choose N s := by
    calc
      Nat.choose (N - 1) (s - 1)
          ≤ Nat.choose (N - 1) (s - 1) + Nat.choose (N - 1) s := Nat.le_add_right _ _
      _ = Nat.choose N s := by
          symm
          exact hpascal
  have : Nat.choose (N - 1) (k - 1) ≤ Nat.choose N s := le_trans hchoose hsle
  simpa [N] using this

theorem lemma4_choose_mul_le_ed_pow (d s : ℕ) (hs : 1 ≤ s) : ((Nat.choose (d * s) s : ℝ) ≤ (Real.exp 1 * d) ^ s) := by
  classical
  have hchoose : (Nat.choose (d * s) s : ℝ) ≤ ((d * s) ^ s : ℝ) / Nat.factorial s := by
    simpa using (Nat.choose_le_pow_div (α := ℝ) (r := s) (n := d * s))

  have hsnonneg : (0 : ℝ) ≤ (s : ℝ) := by
    exact_mod_cast (Nat.zero_le s)

  have hexp : ((s : ℝ) ^ s) / Nat.factorial s ≤ Real.exp (s : ℝ) := by
    -- lemma: Real.pow_div_factorial_le_exp
    simpa using (Real.pow_div_factorial_le_exp (x := (s : ℝ)) hsnonneg s)

  have hdnonneg : (0 : ℝ) ≤ (d : ℝ) ^ s := by
    positivity

  have hmul : (d : ℝ) ^ s * (((s : ℝ) ^ s) / Nat.factorial s) ≤ (d : ℝ) ^ s * Real.exp (s : ℝ) := by
    exact mul_le_mul_of_nonneg_left hexp hdnonneg

  have hpow : ((d * s) ^ s : ℝ) / Nat.factorial s ≤ (Real.exp 1 * d) ^ s := by
    calc
      ((d * s) ^ s : ℝ) / Nat.factorial s
          = ((d : ℝ) ^ s * (s : ℝ) ^ s) / Nat.factorial s := by
              -- rewrite numerator
              have hrew : ((d * s) ^ s : ℝ) = (d : ℝ) ^ s * (s : ℝ) ^ s := by
                calc
                  ((d * s) ^ s : ℝ)
                      = ((d * s : ℝ) ^ s) := by
                          simpa using (Nat.cast_pow (R := ℝ) (d * s) s)
                  _ = ((d : ℝ) * (s : ℝ)) ^ s := by
                          simpa [Nat.cast_mul]
                  _ = (d : ℝ) ^ s * (s : ℝ) ^ s := by
                          simpa using (mul_pow (d : ℝ) (s : ℝ) s)
              simpa [hrew]
      _ = (d : ℝ) ^ s * (((s : ℝ) ^ s) / Nat.factorial s) := by
              -- pull out factor
              simpa [mul_assoc] using (mul_div_assoc ((d : ℝ) ^ s) ((s : ℝ) ^ s) (Nat.factorial s))
      _ ≤ (d : ℝ) ^ s * Real.exp (s : ℝ) := by
              exact hmul
      _ = (Real.exp 1 * (d : ℝ)) ^ s := by
              -- rewrite exp and combine
              calc
                (d : ℝ) ^ s * Real.exp (s : ℝ)
                    = (d : ℝ) ^ s * (Real.exp 1 ^ s) := by
                        simpa using congrArg (fun t => (d : ℝ) ^ s * t) ((Real.exp_one_pow s).symm)
                _ = Real.exp 1 ^ s * (d : ℝ) ^ s := by
                        ac_rfl
                _ = (Real.exp 1 * (d : ℝ)) ^ s := by
                        simpa [mul_pow]

  exact le_trans hchoose (by
    -- hpow already ends with (Real.exp 1 * (d:ℝ))^s; need cast match
    simpa using hpow)


theorem lemma4_compositionAsSetEquiv_symm_boundaries (N : ℕ) (s : Finset (Fin (N - 1))) :
  ((compositionAsSetEquiv N).symm s).boundaries =
    insert (0 : Fin N.succ)
      (insert (Fin.last N)
        (s.image (fun j : Fin (N - 1) =>
          (⟨(j : ℕ) + 1,
            Nat.lt_succ_of_le
              (le_trans (Nat.succ_le_of_lt j.is_lt) (Nat.sub_le N 1))⟩ : Fin N.succ)))) := by
  classical
  ext i
  simp [compositionAsSetEquiv]
  constructor
  · intro h
    rcases h with h0 | hlast | hrest
    · exact Or.inl h0
    · exact Or.inr (Or.inl hlast)
    · rcases hrest with ⟨j, hj, hij⟩
      refine Or.inr (Or.inr ?_)
      refine ⟨j, hj, ?_⟩
      apply Fin.ext
      exact hij.symm
  · intro h
    rcases h with h0 | hlast | hrest
    · exact Or.inl h0
    · exact Or.inr (Or.inl hlast)
    · rcases hrest with ⟨j, hj, hEq⟩
      refine Or.inr (Or.inr ?_)
      refine ⟨j, hj, ?_⟩
      have hval : (↑j + 1) = (↑i : ℕ) := by
        simpa using congrArg Fin.val hEq
      exact hval.symm

theorem lemma4_compositionAsSetEquiv_symm_length (N : ℕ) (hN : 1 ≤ N) (s : Finset (Fin (N - 1))) :
  ((compositionAsSetEquiv N).symm s).length = s.card + 1 := by
  classical
  -- Define the shift map appearing in the boundaries formula
  let shift : Fin (N - 1) → Fin N.succ := fun j : Fin (N - 1) =>
    (⟨(j : ℕ) + 1,
        Nat.lt_succ_of_le
          (le_trans (Nat.succ_le_of_lt j.is_lt) (Nat.sub_le N 1))⟩ : Fin N.succ)

  have hboundaries : ((compositionAsSetEquiv N).symm s).boundaries =
      insert (0 : Fin N.succ) (insert (Fin.last N) (s.image shift)) := by
    simpa [shift] using lemma4_compositionAsSetEquiv_symm_boundaries N s

  have hN0 : N ≠ 0 := by
    omega

  have h0_last : (0 : Fin N.succ) ≠ Fin.last N := by
    intro h
    have : (0 : ℕ) = N := by
      simpa using congrArg Fin.val h
    exact hN0 this.symm

  have h0_not_mem_image : (0 : Fin N.succ) ∉ s.image shift := by
    intro hmem
    rcases Finset.mem_image.mp hmem with ⟨j, hj, hj0⟩
    have : (j : ℕ) + 1 = 0 := by
      -- take values
      simpa [shift] using congrArg Fin.val hj0
    have : Nat.succ (j : ℕ) = 0 := by
      simpa [Nat.succ_eq_add_one] using this
    exact (Nat.succ_ne_zero (j : ℕ)) this

  have hlast_not_mem_image : (Fin.last N) ∉ s.image shift := by
    intro hmem
    rcases Finset.mem_image.mp hmem with ⟨j, hj, hjlast⟩
    have hval : (j : ℕ) + 1 = N := by
      simpa [shift] using congrArg Fin.val hjlast
    have hjle : (j : ℕ) + 1 ≤ N - 1 := Nat.succ_le_of_lt j.is_lt
    have hNm1_lt : N - 1 < N := by
      omega
    have hjlt : (j : ℕ) + 1 < N := lt_of_le_of_lt hjle hNm1_lt
    have : N < N := by
      simpa [hval] using hjlt
    exact (Nat.lt_irrefl N) this

  have h0_not_mem_insert : (0 : Fin N.succ) ∉ insert (Fin.last N) (s.image shift) := by
    -- membership in an insert
    simp [Finset.mem_insert, h0_last, h0_not_mem_image]

  have hshift_inj : Function.Injective shift := by
    intro a b hab
    apply Fin.ext
    have hval : (a : ℕ) + 1 = (b : ℕ) + 1 := by
      simpa [shift] using congrArg Fin.val hab
    exact Nat.add_right_cancel hval

  have hcard_image : (s.image shift).card = s.card := by
    simpa using (Finset.card_image_of_injective s hshift_inj)

  have hcard_boundaries : ((compositionAsSetEquiv N).symm s).boundaries.card = s.card + 2 := by
    -- rewrite boundaries, then compute card by two inserts
    -- first insert Fin.last N
    have hcard1 : (insert (Fin.last N) (s.image shift)).card = (s.image shift).card + 1 :=
      Finset.card_insert_of_notMem hlast_not_mem_image
    have hcard2 : (insert (0 : Fin N.succ) (insert (Fin.last N) (s.image shift))).card =
        (insert (Fin.last N) (s.image shift)).card + 1 :=
      Finset.card_insert_of_notMem h0_not_mem_insert
    -- combine
    --
    calc
      ((compositionAsSetEquiv N).symm s).boundaries.card
          = (insert (0 : Fin N.succ) (insert (Fin.last N) (s.image shift))).card := by
              simpa [hboundaries]
      _ = (insert (Fin.last N) (s.image shift)).card + 1 := by
              simpa using hcard2
      _ = ((s.image shift).card + 1) + 1 := by
              simpa [hcard1]
      _ = s.card + 2 := by
              -- use card of image
              omega

  -- finally, unfold length
  -- length is boundaries.card - 1
  simp [CompositionAsSet.length, hcard_boundaries]


theorem lemma4_card_compositions_length_eq_choose (N k : ℕ) (hN : 1 ≤ N) (hk : 1 ≤ k) :
  Fintype.card {c : Composition N // c.length = k} = Nat.choose (N - 1) (k - 1) := by
  classical
  let e : Finset (Fin (N - 1)) ≃ Composition N :=
    (compositionAsSetEquiv N).symm.trans (compositionEquiv N).symm
  have hlen : ∀ s : Finset (Fin (N - 1)), (e s).length = s.card + 1 := by
    intro s
    -- unfold both equivalences and use the length lemma for `CompositionAsSet.toComposition`
    simp [e, Equiv.trans_apply, compositionEquiv,
      lemma4_compositionAsSetEquiv_symm_length N hN s]
  have hcard :
      Fintype.card {c : Composition N // c.length = k} =
        Fintype.card {s : Finset (Fin (N - 1)) // s.card = k - 1} := by
    -- transfer the length condition along `e`
    have E : {s : Finset (Fin (N - 1)) // s.card = k - 1} ≃
        {c : Composition N // c.length = k} := by
      refine Equiv.subtypeEquiv e ?_
      intro s
      constructor
      · intro hs
        -- hs : s.card = k - 1
        have hk' : (k - 1) + 1 = k := Nat.sub_add_cancel hk
        -- show (e s).length = k
        have : s.card + 1 = k := by
          calc
            s.card + 1 = (k - 1) + 1 := by simpa [hs]
            _ = k := hk'
        simpa [hlen s] using this
      · intro hs
        -- hs : (e s).length = k
        have : s.card + 1 = k := by simpa [hlen s] using hs
        have hk' : (k - 1) + 1 = k := Nat.sub_add_cancel hk
        have : s.card + 1 = (k - 1) + 1 := by simpa [hk'] using this
        exact Nat.add_right_cancel this
    simpa using (Fintype.card_congr E).symm
  calc
    Fintype.card {c : Composition N // c.length = k}
        = Fintype.card {s : Finset (Fin (N - 1)) // s.card = k - 1} := hcard
    _ = Nat.choose (Fintype.card (Fin (N - 1))) (k - 1) := by
          simpa using (Fintype.card_finset_len (α := Fin (N - 1)) (k := k - 1))
    _ = Nat.choose (N - 1) (k - 1) := by
          simp

theorem lemma4_length_list_prod (n : ℕ) (l : List (FreeMonoid (Fin n))) :
  (l.prod).length = (l.map FreeMonoid.length).sum := by
  induction l with
  | nil =>
      simp
  | cons a t ih =>
      -- step
      simp [List.prod_cons, FreeMonoid.length_mul, ih]

theorem lemma4_mem_ball_A_iff_length_le (n R : ℕ) (w : FreeMonoid (Fin n)) : w ∈ Ball R (A n) ↔ w.length ≤ R := by
  -- Unfold the definitions of `Ball` and `A`.
  simp [free.Ball, free.A]
  constructor
  · rintro ⟨l, hlR, hlA, hlprod⟩
    -- Length of a product of singletons is the length of the list.
    have hlen : l.prod.length = l.length := by
      -- Prove a general statement by induction on the list.
      have hlen' : ∀ l : List (FreeMonoid (Fin n)), (∀ x ∈ l, ∃ i, [i] = x) → l.prod.length = l.length := by
        intro l hlA
        induction l with
        | nil =>
            simp
        | cons a t ih =>
            have ha : a.length = 1 := by
              rcases hlA a (by simp) with ⟨i, rfl⟩
              simp [FreeMonoid.length]
            have ht : t.prod.length = t.length := by
              apply ih
              intro x hx
              exact hlA x (by simp [hx])
            simp [List.prod_cons, FreeMonoid.length_mul, ha, ht, Nat.succ_eq_add_one, Nat.add_comm,
              Nat.add_left_comm, Nat.add_assoc]
      exact hlen' l hlA
    have hwlen : w.length = l.length := by
      have hprodlen : l.prod.length = w.length := by
        simpa using congrArg FreeMonoid.length hlprod
      exact hprodlen.symm.trans hlen
    -- Conclude using `l.length ≤ R`.
    simpa [hwlen] using hlR
  · intro hwlen
    refine ⟨w.toList.map FreeMonoid.of, ?_, ?_, ?_⟩
    · -- bound the number of factors
      simpa [FreeMonoid.length] using hwlen
    · -- each factor lies in `A n`
      intro x hx
      rcases List.mem_map.1 hx with ⟨i, -, rfl⟩
      exact ⟨i, rfl⟩
    · -- the product of the singleton letters is the original word
      have hlift_w :
          FreeMonoid.lift (FreeMonoid.of : Fin n → FreeMonoid (Fin n)) w = w := by
        -- `lift of` is the identity homomorphism.
        have :=
          congrArg (fun g : FreeMonoid (Fin n) →* FreeMonoid (Fin n) => g w)
            (FreeMonoid.lift_restrict (f := MonoidHom.id (FreeMonoid (Fin n))))
        simpa using this
      have happly :
          FreeMonoid.lift (FreeMonoid.of : Fin n → FreeMonoid (Fin n)) w =
            (w.toList.map (FreeMonoid.of)).prod := by
        simpa using
          (FreeMonoid.lift_apply (f := (FreeMonoid.of : Fin n → FreeMonoid (Fin n))) (l := w))
      exact happly.symm.trans hlift_w

theorem lemma4_ncard_pi_univ_eq_prod (α : Type*) (k : ℕ) (S : Fin k → Set α) :
  Set.ncard (Set.pi (Set.univ : Set (Fin k)) S) = ∏ i : Fin k, Set.ncard (S i) := by
  classical
  calc
    Set.ncard (Set.pi (Set.univ : Set (Fin k)) S)
        = Nat.card (Set.pi (Set.univ : Set (Fin k)) S) := by
            simpa using
              (Set.Nat.card_coe_set_eq (Set.pi (Set.univ : Set (Fin k)) S)).symm
    _ = Nat.card (∀ i : Fin k, S i) := by
            exact Nat.card_congr (Equiv.Set.univPi S)
    _ = ∏ i : Fin k, Nat.card (S i) := by
            simpa using (Nat.card_pi (β := fun i : Fin k => S i))
    _ = ∏ i : Fin k, Set.ncard (S i) := by
            simp [Set.Nat.card_coe_set_eq]

theorem lemma4_ncard_vector_pi_univ_eq_prod (α : Type*) (k : ℕ) (S : Fin k → Set α) :
  Set.ncard {v : List.Vector α k | ∀ i : Fin k, v.get i ∈ S i} = ∏ i : Fin k, Set.ncard (S i) := by
  classical
  let e : List.Vector α k ≃ (Fin k → α) := Equiv.vectorEquivFin α k
  have hcongr :
      Set.ncard {v : List.Vector α k | ∀ i : Fin k, v.get i ∈ S i} =
        Set.ncard (Set.pi (Set.univ : Set (Fin k)) S) := by
    classical
    refine
      Set.ncard_congr (s := {v : List.Vector α k | ∀ i : Fin k, v.get i ∈ S i})
        (t := Set.pi (Set.univ : Set (Fin k)) S) (f := fun v hv => e v) ?_ ?_ ?_
    · intro v hv
      refine (Set.mem_univ_pi).2 ?_
      intro i
      simpa [e] using hv i
    · intro v w hv hw hEq
      exact e.injective hEq
    · intro b hb
      refine ⟨e.symm b, ?_, ?_⟩
      · have hb' : ∀ i : Fin k, b i ∈ S i := (Set.mem_univ_pi).1 hb
        intro i
        have hget : (e.symm b).get i = b i := by
          simpa [e, Equiv.vectorEquivFin] using (List.Vector.get_ofFn (f := b) i)
        simpa [hget] using hb' i
      · exact e.apply_symm_apply b
  calc
    Set.ncard {v : List.Vector α k | ∀ i : Fin k, v.get i ∈ S i} =
        Set.ncard (Set.pi (Set.univ : Set (Fin k)) S) := hcongr
    _ = ∏ i : Fin k, Set.ncard (S i) := lemma4_ncard_pi_univ_eq_prod α k S

theorem lemma4_ncard_words_length_eq_pow (n r : ℕ) : Set.ncard { w : FreeMonoid (Fin n) | w.length = r } = n ^ r := by
  classical
  rw [← Set.Nat.card_coe_set_eq (s := { w : FreeMonoid (Fin n) | w.length = r })]
  change Nat.card { w : FreeMonoid (Fin n) // w.length = r } = n ^ r
  change Nat.card (List.Vector (Fin n) r) = n ^ r
  rw [Nat.card_eq_fintype_card]
  simpa [Fintype.card_fin] using (card_vector (α := Fin n) r)

theorem lemma4_ncard_generators_length_le (n : ℕ) (hn : n ≥ 2) (M : Set (FreeMonoid (Fin n))) (c : ℝ) (hc : c > 0) (p : ℝ)
  (hG : ∀ l : ℕ, l ≥ 2 → Set.ncard { x ∈ M | x.length = l } ≤ c * Real.rpow l p) :
  ∀ l : ℕ, 1 ≤ l → Set.ncard { x ∈ (M ∪ A n) | x.length = l } ≤ (n + c) * Real.rpow l p := by
  intro l hl
  classical
  by_cases h1 : l = 1
  · subst h1
    -- case l = 1
    let S : Set (FreeMonoid (Fin n)) := {x ∈ (M ∪ A n) | x.length = 1}
    let T : Set (FreeMonoid (Fin n)) := {w : FreeMonoid (Fin n) | w.length = 1}
    have hST : S ⊆ T := by
      intro x hx
      exact hx.2
    have hn0 : n ≠ 0 := by
      omega
    have hTne : Set.ncard T ≠ 0 := by
      have hT : Set.ncard T = n ^ 1 := by
        simpa [T] using lemma4_ncard_words_length_eq_pow n 1
      rw [hT]
      simpa [pow_one, hn0]
    have hTfin : T.Finite := Set.finite_of_ncard_ne_zero hTne
    have hcardNat : Set.ncard S ≤ Set.ncard T := Set.ncard_le_ncard hST hTfin
    have hcard : (Set.ncard S : ℝ) ≤ (Set.ncard T : ℝ) := by
      exact_mod_cast hcardNat
    have hTnat : Set.ncard T = n := by
      have hT : Set.ncard T = n ^ 1 := by
        simpa [T] using lemma4_ncard_words_length_eq_pow n 1
      simpa [pow_one] using hT
    have hSn : (Set.ncard S : ℝ) ≤ (n : ℝ) := by
      have hTval : (Set.ncard T : ℝ) = (n : ℝ) := by
        exact_mod_cast hTnat
      simpa [hTval] using hcard
    have hnle : (n : ℝ) ≤ (n + c) * Real.rpow 1 p := by
      have : (n : ℝ) ≤ (n : ℝ) + c := by
        linarith [hc]
      simpa [Real.one_rpow] using this
    have hSle : (Set.ncard S : ℝ) ≤ (n + c) * Real.rpow 1 p := le_trans hSn hnle
    simpa [S] using hSle
  · have hl2 : 2 ≤ l := by
      omega
    have hset : {x ∈ (M ∪ A n) | x.length = l} = {x ∈ M | x.length = l} := by
      ext x
      constructor
      · rintro ⟨hxU, hxlen⟩
        refine ⟨?_, hxlen⟩
        rcases hxU with hxM | hxA
        · exact hxM
        · rcases (by simpa [free.A] using hxA) with ⟨i, rfl⟩
          have hl1 : l = 1 := by
            simpa using hxlen.symm
          omega
      · rintro ⟨hxM, hxlen⟩
        exact ⟨Or.inl hxM, hxlen⟩
    have h1 : Set.ncard {x ∈ (M ∪ A n) | x.length = l} ≤ c * Real.rpow l p := by
      have hM : Set.ncard {x ∈ M | x.length = l} ≤ c * Real.rpow l p := hG l hl2
      -- rewrite the set
      simpa only [hset] using hM
    have h2 : c * Real.rpow l p ≤ (n + c) * Real.rpow l p := by
      have hnnonneg : (0 : ℝ) ≤ (n : ℝ) := by
        exact_mod_cast (Nat.zero_le n)
      have hc_le : c ≤ (n : ℝ) + c := by
        linarith [hnnonneg]
      have hr : 0 ≤ Real.rpow l p := by
        have : (0 : ℝ) ≤ (l : ℝ) := by
          exact_mod_cast (Nat.zero_le l)
        exact Real.rpow_nonneg this p
      exact mul_le_mul_of_nonneg_right hc_le hr
    exact le_trans h1 h2

theorem lemma4_pow_div_le_d_pow (s k d : ℕ) (hk : 1 ≤ k) (hks : k ≤ s) (hd : d ≥ 3) :
  (((s : ℝ) / k) ^ k) ≤ (d : ℝ) ^ (s - k) := by
  classical
  set t : ℕ := s - k
  have hs : k + t = s := by
    simpa [t] using (Nat.add_sub_of_le hks)
  have hk0nat : k ≠ 0 := by
    exact (Nat.one_le_iff_ne_zero.mp hk)
  have hk0 : (k : ℝ) ≠ 0 := by
    exact_mod_cast hk0nat
  have hs_nat : s = k + t := hs.symm

  have hdiv : (s : ℝ) / k = 1 + (t : ℝ) / k := by
    calc
      (s : ℝ) / k = ((k + t : ℕ) : ℝ) / k := by
        simpa [hs_nat]
      _ = ((k : ℝ) + (t : ℝ)) / k := by
        simp [Nat.cast_add]
      _ = (k : ℝ) / k + (t : ℝ) / k := by
        simpa [add_div]
      _ = 1 + (t : ℝ) / k := by
        simp [hk0, add_comm, add_left_comm, add_assoc]

  have h1 : 1 + (t : ℝ) / k ≤ Real.exp ((t : ℝ) / k) := by
    simpa [add_comm, add_left_comm, add_assoc] using
      (Real.add_one_le_exp ((t : ℝ) / k))

  have hpow : (1 + (t : ℝ) / k) ^ k ≤ (Real.exp ((t : ℝ) / k)) ^ k := by
    have hnonneg : (0 : ℝ) ≤ 1 + (t : ℝ) / k := by
      have hkpos : (0 : ℝ) < (k : ℝ) := by
        exact_mod_cast (Nat.pos_of_ne_zero hk0nat)
      have ht0 : (0 : ℝ) ≤ (t : ℝ) := by
        exact_mod_cast (Nat.zero_le t)
      have : (0 : ℝ) ≤ (t : ℝ) / k := by
        exact div_nonneg ht0 (le_of_lt hkpos)
      linarith
    exact (pow_le_pow_left₀ hnonneg h1 k)

  have hexp : (Real.exp ((t : ℝ) / k)) ^ k = Real.exp (t : ℝ) := by
    have h := (Real.exp_nat_mul ((t : ℝ) / k) k)
    have hsymm : (Real.exp ((t : ℝ) / k)) ^ k = Real.exp ((k : ℝ) * ((t : ℝ) / k)) := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using h.symm
    calc
      (Real.exp ((t : ℝ) / k)) ^ k = Real.exp ((k : ℝ) * ((t : ℝ) / k)) := hsymm
      _ = Real.exp (t : ℝ) := by
        have : (k : ℝ) * ((t : ℝ) / k) = (t : ℝ) := by
          field_simp [hk0]
        simpa [this]

  have hexp1_le_d : Real.exp 1 ≤ (d : ℝ) := by
    have hconst : (2.7182818286 : ℝ) < 3 := by
      norm_num
    have hlt3 : Real.exp 1 < (3 : ℝ) := by
      exact lt_trans Real.exp_one_lt_d9 hconst
    have hd3 : (3 : ℝ) ≤ (d : ℝ) := by
      exact_mod_cast hd
    exact le_trans (le_of_lt hlt3) hd3

  have hexpt_le : Real.exp (t : ℝ) ≤ (d : ℝ) ^ t := by
    have hrew : Real.exp (t : ℝ) = (Real.exp 1) ^ t := by
      exact (Real.exp_one_pow t).symm
    have hnonneg : (0 : ℝ) ≤ Real.exp 1 := by
      exact le_of_lt (Real.exp_pos 1)
    have hpowd : (Real.exp 1) ^ t ≤ (d : ℝ) ^ t :=
      pow_le_pow_left₀ hnonneg hexp1_le_d t
    -- rewrite goal using hrew
    rw [hrew]
    exact hpowd

  have hleft : ((s : ℝ) / k) ^ k = (1 + (t : ℝ) / k) ^ k := by
    simpa [hdiv]

  have hfinal : ((s : ℝ) / k) ^ k ≤ (d : ℝ) ^ t := by
    calc
      ((s : ℝ) / k) ^ k = (1 + (t : ℝ) / k) ^ k := hleft
      _ ≤ (Real.exp ((t : ℝ) / k)) ^ k := hpow
      _ = Real.exp (t : ℝ) := hexp
      _ ≤ (d : ℝ) ^ t := hexpt_le

  simpa [t] using hfinal

theorem lemma4_composition_prod_rpow_le_d_rpow (p : ℝ) (hp : 0 ≤ p) (s d : ℕ) (hs : 1 ≤ s) (hd : d ≥ 3)
  (c : Composition (d * s)) (hcs : c.length ≤ s) :
  (∏ i : Fin c.length, (c.blocksFun i : ℝ) ^ p) ≤ (Real.rpow d p) ^ s := by
  classical
  have hspos : 0 < s := by
    exact Nat.succ_le_iff.mp hs
  have hdpos : 0 < d := by
    exact lt_of_lt_of_le (by decide : 0 < (3 : ℕ)) hd
  have hNpos : 0 < d * s := Nat.mul_pos hdpos hspos
  have hkpos : 0 < c.length := by
    exact Composition.length_pos_of_pos (c := c) hNpos
  have hk : 1 ≤ c.length := by
    exact Nat.succ_le_iff.mpr hkpos
  have hk0 : (c.length : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_zero_of_lt hkpos)
  have hnonneg : ∀ i : Fin c.length, 0 ≤ (c.blocksFun i : ℝ) := by
    intro i
    exact_mod_cast (Nat.zero_le (c.blocksFun i))
  have hprod_eq : (∏ i : Fin c.length, (c.blocksFun i : ℝ) ^ p)
      = (∏ i : Fin c.length, (c.blocksFun i : ℝ)) ^ p := by
    simpa using
      (Real.finset_prod_rpow (s := (Finset.univ : Finset (Fin c.length)))
        (f := fun i : Fin c.length => (c.blocksFun i : ℝ))
        (hs := by
          intro i hi
          exact hnonneg i)
        (r := p))
  set P : ℝ := ∏ i : Fin c.length, (c.blocksFun i : ℝ) with hP
  have hP_nonneg : 0 ≤ P := by
    rw [hP]
    exact Finset.prod_nonneg (fun i hi => hnonneg i)
  have hgm : P ^ ((c.length : ℝ)⁻¹) ≤ (d * s : ℝ) / c.length := by
    simpa [hP] using (lemma4_amgm_composition_prod_le (N := d * s) (c := c) hk)
  have hz : 0 ≤ p * (c.length : ℝ) := by
    have hk_nonneg : 0 ≤ (c.length : ℝ) := by
      exact_mod_cast (Nat.zero_le c.length)
    exact mul_nonneg hp hk_nonneg
  have hgm_rpow : (P ^ ((c.length : ℝ)⁻¹)) ^ (p * (c.length : ℝ))
      ≤ ((d * s : ℝ) / c.length) ^ (p * (c.length : ℝ)) := by
    exact Real.rpow_le_rpow (Real.rpow_nonneg hP_nonneg _) hgm hz
  have hleft_simp : (P ^ ((c.length : ℝ)⁻¹)) ^ (p * (c.length : ℝ)) = P ^ p := by
    have hmul : ((c.length : ℝ)⁻¹) * (p * (c.length : ℝ)) = p := by
      calc
        ((c.length : ℝ)⁻¹) * (p * (c.length : ℝ))
            = ((c.length : ℝ)⁻¹) * ((c.length : ℝ) * p) := by
                simp [mul_assoc, mul_comm, mul_left_comm]
        _ = (((c.length : ℝ)⁻¹ * (c.length : ℝ)) * p) := by
                rw [← mul_assoc]
        _ = (1 * p) := by
                simp [hk0]
        _ = p := by simp
    have : (P ^ ((c.length : ℝ)⁻¹)) ^ (p * (c.length : ℝ)) =
        P ^ (((c.length : ℝ)⁻¹) * (p * (c.length : ℝ))) := by
      simpa [mul_assoc] using
        (Real.rpow_mul hP_nonneg ((c.length : ℝ)⁻¹) (p * (c.length : ℝ))).symm
    simpa [this, hmul]
  rw [hprod_eq]
  rw [hP]
  have hP_le : P ^ p ≤ ((d * s : ℝ) / c.length) ^ (p * (c.length : ℝ)) := by
    simpa [hleft_simp] using hgm_rpow

  have hbound : ((d * s : ℝ) / c.length) ^ (p * (c.length : ℝ)) ≤ (Real.rpow d p) ^ s := by
    have hd_nonneg : 0 ≤ (d : ℝ) := by positivity
    have hs_nonneg : 0 ≤ (s : ℝ) := by positivity
    have hk_pos_real : 0 < (c.length : ℝ) := by
      exact_mod_cast hkpos
    have hsk_nonneg : 0 ≤ ((s : ℝ) / c.length) := by
      exact div_nonneg hs_nonneg (le_of_lt hk_pos_real)

    have hbase : ((d * s : ℝ) / c.length) = (d : ℝ) * ((s : ℝ) / c.length) := by
      simpa [Nat.cast_mul, mul_div_assoc, mul_assoc]

    have hpow_div : (((s : ℝ) / c.length) ^ c.length) ≤ (d : ℝ) ^ (s - c.length) := by
      simpa using (lemma4_pow_div_le_d_pow s c.length d hk hcs hd)

    have hpow_div_rpow : (((s : ℝ) / c.length) ^ c.length) ^ p ≤ ((d : ℝ) ^ (s - c.length)) ^ p := by
      have hx : 0 ≤ ((s : ℝ) / c.length) ^ c.length := by
        have : 0 ≤ (s : ℝ) / c.length := by
          exact div_nonneg hs_nonneg (le_of_lt hk_pos_real)
        exact pow_nonneg this _
      exact Real.rpow_le_rpow hx hpow_div hp

    calc
      ((d * s : ℝ) / c.length) ^ (p * (c.length : ℝ))
          = (d : ℝ) ^ (p * (c.length : ℝ)) * ((s : ℝ) / c.length) ^ (p * (c.length : ℝ)) := by
              simpa [hbase] using
                (Real.mul_rpow (x := (d : ℝ)) (y := (s : ℝ) / c.length) (z := (p * (c.length : ℝ)))
                  hd_nonneg hsk_nonneg)
      _ = ((d : ℝ) ^ p) ^ c.length * (((s : ℝ) / c.length) ^ c.length) ^ p := by
              -- rewrite both factors
              have hd1 : (d : ℝ) ^ (p * (c.length : ℝ)) = ((d : ℝ) ^ p) ^ c.length := by
                simpa using (Real.rpow_mul_natCast hd_nonneg p c.length)
              have hs1 : ((s : ℝ) / c.length) ^ (p * (c.length : ℝ)) = (((s : ℝ) / c.length) ^ c.length) ^ p := by
                have hsbase_nonneg : 0 ≤ (s : ℝ) / c.length := by
                  exact div_nonneg hs_nonneg (le_of_lt hk_pos_real)
                -- rpow_natCast_mul gives exponent (c.length : ℝ) * p
                have : ((s : ℝ) / c.length) ^ ((c.length : ℝ) * p) =
                    (((s : ℝ) / c.length) ^ c.length) ^ p := by
                  simpa using (Real.rpow_natCast_mul hsbase_nonneg c.length p)
                simpa [mul_comm, mul_left_comm, mul_assoc] using this
              -- finish
              simp [hd1, hs1, mul_assoc]
      _ ≤ ((d : ℝ) ^ p) ^ c.length * ((d : ℝ) ^ (s - c.length)) ^ p := by
              have hdleft_nonneg : 0 ≤ ((d : ℝ) ^ p) ^ c.length := by
                have : 0 ≤ (d : ℝ) ^ p := Real.rpow_nonneg hd_nonneg _
                exact pow_nonneg this _
              exact mul_le_mul_of_nonneg_left hpow_div_rpow hdleft_nonneg
      _ = ((d : ℝ) ^ p) ^ s := by
              -- rewrite (d^(s-k))^p as (d^p)^(s-k)
              have hd_comm : ((d : ℝ) ^ (s - c.length)) ^ p = ((d : ℝ) ^ p) ^ (s - c.length) := by
                simpa using (Real.rpow_pow_comm (x := (d : ℝ)) hd_nonneg p (s - c.length)).symm
              -- now combine powers
              have hadd : c.length + (s - c.length) = s := Nat.add_sub_of_le hcs
              calc
                ((d : ℝ) ^ p) ^ c.length * ((d : ℝ) ^ (s - c.length)) ^ p
                    = ((d : ℝ) ^ p) ^ c.length * ((d : ℝ) ^ p) ^ (s - c.length) := by
                        simp [hd_comm]
                _ = ((d : ℝ) ^ p) ^ (c.length + (s - c.length)) := by
                        -- use pow_add
                        simpa [pow_add, mul_assoc]
                _ = ((d : ℝ) ^ p) ^ s := by
                        simpa [hadd]
      _ = (Real.rpow d p) ^ s := by
              rfl

  exact le_trans hP_le hbound

theorem lemma4_ncard_vector_fixed_composition_le (n : ℕ) (hn : n ≥ 2)
  (M : Set (FreeMonoid (Fin n)))
  (c : ℝ) (hc : c > 0)
  (p : ℝ) (hp : p ≥ 0)
  (hG : ∀ l : ℕ, l ≥ 2 → Set.ncard { x ∈ M | x.length = l } ≤ c * Real.rpow l p) :
  ∀ (s d : ℕ), s ≥ 1 → d ≥ 3 →
    ∀ (comp : Composition (d * s)), comp.length ≤ s →
      (Set.ncard { v : List.Vector (FreeMonoid (Fin n)) comp.length |
          ∀ i : Fin comp.length,
            v.get i ∈ { x ∈ (M ∪ A n) | x.length = comp.blocksFun i } }
        ≤ ((n + c) * Real.rpow d p) ^ s) := by
  intro s d hs hd comp hcomp
  classical
  let S : Fin comp.length → Set (FreeMonoid (Fin n)) :=
    fun i => { x ∈ (M ∪ A n) | x.length = comp.blocksFun i }
  have hcardNat :
      Set.ncard { v : List.Vector (FreeMonoid (Fin n)) comp.length |
          ∀ i : Fin comp.length,
            v.get i ∈ { x ∈ (M ∪ A n) | x.length = comp.blocksFun i } }
        = ∏ i : Fin comp.length, Set.ncard (S i) := by
    simpa [S] using
      (lemma4_ncard_vector_pi_univ_eq_prod (α := FreeMonoid (Fin n)) (k := comp.length) S)
  have hcardReal :
      (Set.ncard { v : List.Vector (FreeMonoid (Fin n)) comp.length |
          ∀ i : Fin comp.length,
            v.get i ∈ { x ∈ (M ∪ A n) | x.length = comp.blocksFun i } } : ℝ)
        = ∏ i : Fin comp.length, (Set.ncard (S i) : ℝ) := by
    have := congrArg (fun m : ℕ => (m : ℝ)) hcardNat
    simpa [S] using this
  have hfactor : ∀ i : Fin comp.length,
      (Set.ncard (S i) : ℝ) ≤ (n + c) * Real.rpow (comp.blocksFun i) p := by
    intro i
    have hlen : 1 ≤ comp.blocksFun i := Composition.one_le_blocksFun (c := comp) i
    simpa [S] using
      (lemma4_ncard_generators_length_le (n := n) hn (M := M) (c := c) hc (p := p) hG
        (l := comp.blocksFun i) hlen)
  have hprod :
      (∏ i : Fin comp.length, (Set.ncard (S i) : ℝ))
        ≤ ∏ i : Fin comp.length, ((n + c) * Real.rpow (comp.blocksFun i) p) := by
    classical
    simpa using
      (Finset.prod_le_prod (s := (Finset.univ : Finset (Fin comp.length)))
        (f := fun i => (Set.ncard (S i) : ℝ))
        (g := fun i => ((n + c) * Real.rpow (comp.blocksFun i) p))
        (h0 := by
          intro i hi
          simpa using (Nat.cast_nonneg (Set.ncard (S i)) : (0 : ℝ) ≤ (Set.ncard (S i) : ℝ)))
        (h1 := by
          intro i hi
          exact hfactor i))
  have hprod_simp :
      (∏ i : Fin comp.length, ((n + c) * Real.rpow (comp.blocksFun i) p))
        = (n + c) ^ comp.length * (∏ i : Fin comp.length, (comp.blocksFun i : ℝ) ^ p) := by
    classical
    have hmul :
        (∏ i : Fin comp.length, ((n + c) * (comp.blocksFun i : ℝ) ^ p))
          = (∏ _i : Fin comp.length, (n + c)) * (∏ i : Fin comp.length, (comp.blocksFun i : ℝ) ^ p) := by
      simpa using
        (Finset.prod_mul_distrib (s := (Finset.univ : Finset (Fin comp.length)))
          (f := fun _i : Fin comp.length => (n + c))
          (g := fun i : Fin comp.length => (comp.blocksFun i : ℝ) ^ p))
    simpa [hmul, Fin.prod_const, mul_assoc]
  have hbound :
      (Set.ncard { v : List.Vector (FreeMonoid (Fin n)) comp.length |
          ∀ i : Fin comp.length,
            v.get i ∈ { x ∈ (M ∪ A n) | x.length = comp.blocksFun i } } : ℝ)
        ≤ (n + c) ^ comp.length * (∏ i : Fin comp.length, (comp.blocksFun i : ℝ) ^ p) := by
    calc
      (Set.ncard { v : List.Vector (FreeMonoid (Fin n)) comp.length |
          ∀ i : Fin comp.length,
            v.get i ∈ { x ∈ (M ∪ A n) | x.length = comp.blocksFun i } } : ℝ)
          = ∏ i : Fin comp.length, (Set.ncard (S i) : ℝ) := hcardReal
      _ ≤ ∏ i : Fin comp.length, ((n + c) * Real.rpow (comp.blocksFun i) p) := hprod
      _ = (n + c) ^ comp.length * (∏ i : Fin comp.length, (comp.blocksFun i : ℝ) ^ p) := hprod_simp
  have hblocks :
      (∏ i : Fin comp.length, (comp.blocksFun i : ℝ) ^ p) ≤ (Real.rpow d p) ^ s := by
    simpa using
      (lemma4_composition_prod_rpow_le_d_rpow (p := p) (hp := hp) (s := s) (d := d)
        (hs := hs) (hd := hd) (c := comp) (hcs := hcomp))
  have hone : (1 : ℝ) ≤ (n + c) := by
    have hn' : (2 : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast hn
    have hc' : (0 : ℝ) < c := hc
    linarith
  have hpow : (n + c) ^ comp.length ≤ (n + c) ^ s := by
    exact pow_le_pow_right₀ hone hcomp
  have :
      (Set.ncard { v : List.Vector (FreeMonoid (Fin n)) comp.length |
          ∀ i : Fin comp.length,
            v.get i ∈ { x ∈ (M ∪ A n) | x.length = comp.blocksFun i } } : ℝ)
        ≤ (n + c) ^ s * (Real.rpow d p) ^ s := by
    calc
      (Set.ncard { v : List.Vector (FreeMonoid (Fin n)) comp.length |
          ∀ i : Fin comp.length,
            v.get i ∈ { x ∈ (M ∪ A n) | x.length = comp.blocksFun i } } : ℝ)
          ≤ (n + c) ^ comp.length * (∏ i : Fin comp.length, (comp.blocksFun i : ℝ) ^ p) := hbound
      _ ≤ (n + c) ^ comp.length * (Real.rpow d p) ^ s := by
          gcongr
      _ ≤ (n + c) ^ s * (Real.rpow d p) ^ s := by
          have hnonneg : 0 ≤ (Real.rpow d p) ^ s := by
            have : 0 ≤ Real.rpow (d : ℝ) p := by
              exact Real.rpow_nonneg (by exact_mod_cast (Nat.zero_le d)) _
            exact pow_nonneg this _
          exact mul_le_mul_of_nonneg_right hpow hnonneg
  simpa [mul_pow, mul_assoc, mul_left_comm, mul_comm] using this


theorem lemma4_ncard_reps_len_eq_k_le_choose_mul_vector (n : ℕ) (hn : n ≥ 2)
  (M : Set (FreeMonoid (Fin n)))
  (c : ℝ) (hc : c > 0)
  (p : ℝ) (hp : p ≥ 0)
  (hG : ∀ l : ℕ, l ≥ 2 → (Set.ncard { x ∈ M | x.length = l } ≤ c * Real.rpow l p )) :
  ∀ (s d k : ℕ), s ≥ 1 → d ≥ 3 → 1 ≤ k → k ≤ s →
    (Set.ncard { v : List.Vector (FreeMonoid (Fin n)) k |
      (∀ i : Fin k, v.get i ∈ (M ∪ A n)) ∧
      (∀ i : Fin k, 1 ≤ (v.get i).length) ∧
      (v.toList.prod).length = d * s }
      ≤ (Nat.choose (d * s) s : ℝ) * ((n + c) * Real.rpow d p) ^ s) := by
  classical
  intro s d k hs hd hk hks

  let V : Set (List.Vector (FreeMonoid (Fin n)) k) :=
    { v : List.Vector (FreeMonoid (Fin n)) k |
        (∀ i : Fin k, v.get i ∈ (M ∪ A n)) ∧
        (∀ i : Fin k, 1 ≤ (v.get i).length) ∧
        (v.toList.prod).length = d * s }

  let I : Type := { comp : Composition (d * s) // comp.length = k }

  let F : I → Set (List.Vector (FreeMonoid (Fin n)) k) := fun comp =>
    { v : List.Vector (FreeMonoid (Fin n)) k |
        ∀ i : Fin k,
          v.get i ∈ { x ∈ (M ∪ A n) | x.length = comp.1.blocksFun (Fin.cast comp.2.symm i) } }

  -- V ⊆ ⋃ comp, F comp
  have hVsub : V ⊆ ⋃ comp : I, F comp := by
    intro v hv
    rcases hv with ⟨hmem, hpos, hlen⟩

    let blocks : List ℕ := (v.map FreeMonoid.length).toList

    have blocks_pos : ∀ {i}, i ∈ blocks → 0 < i := by
      intro i hi
      rcases (List.Vector.mem_iff_get (v := v.map FreeMonoid.length) (a := i)).1 hi with ⟨j, rfl⟩
      have hjpos : 0 < (v.get j).length := lt_of_lt_of_le Nat.zero_lt_one (hpos j)
      simpa [List.Vector.get_map] using hjpos

    have blocks_sum : blocks.sum = d * s := by
      have hprod := lemma4_length_list_prod n v.toList
      have hblocks : blocks = v.toList.map FreeMonoid.length := by
        simpa [blocks] using (List.Vector.toList_map (v := v) (f := FreeMonoid.length)).symm
      calc
        blocks.sum = (v.toList.map FreeMonoid.length).sum := by simpa [hblocks]
        _ = (v.toList.prod).length := by simpa using hprod.symm
        _ = d * s := hlen

    let comp0 : Composition (d * s) :=
      ⟨blocks, (by
        intro i hi
        exact blocks_pos hi), blocks_sum⟩

    have hblockslen : blocks.length = k := by
      simpa [blocks] using (List.Vector.toList_length (v := v.map FreeMonoid.length))

    have hlencomp : comp0.length = k := by
      simpa [Composition.length, comp0] using hblockslen

    refine Set.mem_iUnion.2 ?_
    refine ⟨⟨comp0, hlencomp⟩, ?_⟩
    intro i
    refine ⟨hmem i, ?_⟩

    -- compute the i-th block size
    have hwget : (v.map FreeMonoid.length).get i =
        (v.map FreeMonoid.length).toList.get
          (Fin.cast (List.Vector.toList_length (v := v.map FreeMonoid.length)).symm i) := by
      simpa using (List.Vector.get_eq_get_toList (v := v.map FreeMonoid.length) (i := i))

    have hcast :
        Fin.cast hlencomp.symm i =
          Fin.cast (List.Vector.toList_length (v := v.map FreeMonoid.length)).symm i := by
      have : hlencomp.symm = (List.Vector.toList_length (v := v.map FreeMonoid.length)).symm :=
        Subsingleton.elim _ _
      simpa [this]

    have hwget' : (v.map FreeMonoid.length).get i =
        (v.map FreeMonoid.length).toList.get (Fin.cast hlencomp.symm i) := by
      simpa [hcast] using hwget

    have hblock : comp0.blocksFun (Fin.cast hlencomp.symm i) = (v.get i).length := by
      have : comp0.blocksFun (Fin.cast hlencomp.symm i) = (v.map FreeMonoid.length).get i := by
        simpa [comp0, blocks, Composition.blocksFun] using hwget'.symm
      simpa [List.Vector.get_map] using this

    exact hblock.symm

  -- ⋃ comp, F comp ⊆ V
  have hUnionSub : (⋃ comp : I, F comp) ⊆ V := by
    intro v hv
    rcases (Set.mem_iUnion.1 hv) with ⟨comp, hvcomp⟩
    have hvcomp' : ∀ i : Fin k,
        v.get i ∈ { x ∈ (M ∪ A n) | x.length = comp.1.blocksFun (Fin.cast comp.2.symm i) } := hvcomp

    refine ⟨?_, ?_, ?_⟩
    · intro i
      exact (hvcomp' i).1
    · intro i
      have hb : 1 ≤ comp.1.blocksFun (Fin.cast comp.2.symm i) := by
        simpa using (comp.1.one_le_blocksFun (Fin.cast comp.2.symm i))
      simpa [(hvcomp' i).2.symm] using hb
    ·
      have hprod := lemma4_length_list_prod n v.toList
      have htoList : List.ofFn (fun i : Fin k => v.get i) = v.toList := by
        simpa only [List.Vector.toList_ofFn] using
          congrArg List.Vector.toList (List.Vector.ofFn_get v)
      have hmap : List.ofFn (fun i : Fin k => (v.get i).length) = v.toList.map FreeMonoid.length := by
        have := congrArg (fun l : List (FreeMonoid (Fin n)) => l.map FreeMonoid.length) htoList
        simpa [List.map_ofFn, Function.comp] using this

      have hsum_lengths : (v.toList.map FreeMonoid.length).sum = d * s := by
        have hsum1 : (v.toList.map FreeMonoid.length).sum =
            (List.ofFn (fun i : Fin k => (v.get i).length)).sum := by
          simpa [hmap.symm]
        have hsum2 : (List.ofFn (fun i : Fin k => (v.get i).length)).sum =
            (∑ i : Fin k, (v.get i).length) := by
          simpa using (Fin.sum_ofFn (f := fun i : Fin k => (v.get i).length))
        have hsum3 : (∑ i : Fin k, (v.get i).length) =
            ∑ i : Fin k, comp.1.blocksFun (Fin.cast comp.2.symm i) := by
          classical
          change (Finset.univ.sum (fun i : Fin k => (v.get i).length)) =
            Finset.univ.sum (fun i : Fin k => comp.1.blocksFun (Fin.cast comp.2.symm i))
          refine Finset.sum_congr rfl ?_
          intro i _
          exact (hvcomp' i).2

        have hsum4 : (∑ i : Fin k, comp.1.blocksFun (Fin.cast comp.2.symm i)) = d * s := by
          have hcast :
              (∑ i : Fin k, comp.1.blocksFun (Fin.cast comp.2.symm i)) =
                (∑ i : Fin comp.1.length, comp.1.blocksFun i) := by
            simpa using (Fin.sum_congr' (f := comp.1.blocksFun) (h := comp.2.symm))
          simpa using hcast.trans comp.1.sum_blocksFun

        calc
          (v.toList.map FreeMonoid.length).sum =
              (List.ofFn (fun i : Fin k => (v.get i).length)).sum := hsum1
          _ = (∑ i : Fin k, (v.get i).length) := hsum2
          _ = (∑ i : Fin k, comp.1.blocksFun (Fin.cast comp.2.symm i)) := hsum3
          _ = d * s := hsum4

      calc
        (v.toList.prod).length = (v.toList.map FreeMonoid.length).sum := by
          simpa using hprod
        _ = d * s := hsum_lengths

  have hVeq : V = ⋃ comp : I, F comp := by
    apply le_antisymm
    · exact hVsub
    · exact hUnionSub

  have hV_le_sum : V.ncard ≤ ∑ comp : I, (F comp).ncard := by
    simpa [hVeq] using (Set.ncard_iUnion_le_of_fintype (s := F))

  -- uniform bound on each fiber
  have hF_bound : ∀ comp : I, (Set.ncard (F comp) : ℝ) ≤ ((n + c) * Real.rpow d p) ^ s := by
    intro comp
    rcases comp with ⟨comp, hlen⟩
    cases hlen
    have hlenle : comp.length ≤ s := by
      simpa using hks
    simpa [F] using
      (lemma4_ncard_vector_fixed_composition_le n hn M c hc p hp hG s d hs hd comp hlenle)

  -- sum bound in ℝ
  let C : ℝ := ((n + c) * Real.rpow d p) ^ s

  have hV_le_cardI : (V.ncard : ℝ) ≤ (Fintype.card I : ℝ) * C := by
    have hV_le_sumR : (V.ncard : ℝ) ≤ ((∑ comp : I, (F comp).ncard) : ℝ) := by
      exact_mod_cast hV_le_sum
    have hcast_sum : ((∑ comp : I, (F comp).ncard) : ℝ) = ∑ comp : I, ((F comp).ncard : ℝ) := by
      classical
      simp
    have hV_le_sumR' : (V.ncard : ℝ) ≤ ∑ comp : I, ((F comp).ncard : ℝ) := by
      simpa [hcast_sum] using hV_le_sumR

    have hsum_le : (∑ comp : I, ((F comp).ncard : ℝ)) ≤ ∑ _comp : I, C := by
      classical
      simpa [C] using
        (Finset.sum_le_sum (s := (Finset.univ : Finset I))
          (f := fun comp : I => ((F comp).ncard : ℝ))
          (g := fun _ : I => C)
          (by
            intro comp _
            simpa [C] using (hF_bound comp)))

    have hsum_const : (∑ _comp : I, C) = (Fintype.card I : ℝ) * C := by
      classical
      simp [C]

    calc
      (V.ncard : ℝ) ≤ ∑ comp : I, ((F comp).ncard : ℝ) := hV_le_sumR'
      _ ≤ ∑ _comp : I, C := hsum_le
      _ = (Fintype.card I : ℝ) * C := hsum_const

  -- count compositions
  have hN : 1 ≤ d * s := by
    have hspos : 0 < s := lt_of_lt_of_le Nat.zero_lt_one hs
    have hdpos : 0 < d := lt_of_lt_of_le (by decide : 0 < 3) hd
    exact Nat.succ_le_iff.2 (Nat.mul_pos hdpos hspos)

  have hcardI : (Fintype.card I : ℝ) = (Nat.choose (d * s - 1) (k - 1) : ℝ) := by
    have h := lemma4_card_compositions_length_eq_choose (N := d * s) (k := k) hN hk
    have h' : Fintype.card I = Nat.choose (d * s - 1) (k - 1) := by
      simpa [I] using h
    exact_mod_cast h'

  have hchoose_le : (Nat.choose (d * s - 1) (k - 1) : ℝ) ≤ (Nat.choose (d * s) s : ℝ) := by
    have h := lemma4_choose_ds_sub1_le_choose_ds_s d s k hk hks hd
    exact_mod_cast h

  have hconst_nonneg : 0 ≤ C := by
    -- show base is nonnegative
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := by positivity
    have hc0 : (0 : ℝ) ≤ c := le_of_lt hc
    have hncp : 0 ≤ (n : ℝ) + c := add_nonneg hn0 hc0
    have hd0 : (0 : ℝ) < (d : ℝ) := by
      have : (0 : ℕ) < d := lt_of_lt_of_le (by decide : 0 < 3) hd
      exact_mod_cast this
    have hrpow0 : 0 ≤ Real.rpow (d : ℝ) p := le_of_lt (Real.rpow_pos_of_pos hd0 p)
    have hbase : 0 ≤ ((n : ℝ) + c) * Real.rpow (d : ℝ) p := mul_nonneg hncp hrpow0
    -- finish
    simpa [C] using pow_nonneg hbase s

  have hcardI_le : (Fintype.card I : ℝ) ≤ (Nat.choose (d * s) s : ℝ) := by
    calc
      (Fintype.card I : ℝ) = (Nat.choose (d * s - 1) (k - 1) : ℝ) := hcardI
      _ ≤ (Nat.choose (d * s) s : ℝ) := hchoose_le

  have : (V.ncard : ℝ) ≤ (Nat.choose (d * s) s : ℝ) * C := by
    have hmul : (Fintype.card I : ℝ) * C ≤ (Nat.choose (d * s) s : ℝ) * C :=
      mul_le_mul_of_nonneg_right hcardI_le hconst_nonneg
    exact le_trans hV_le_cardI hmul

  -- unfold V and C and finish
  simpa [V, C] using this

theorem lemma4_ncard_reps_len_eq_k_le_choose_mul (n : ℕ) (hn : n ≥ 2)
  (M : Set (FreeMonoid (Fin n)))
  (c : ℝ) (hc : c > 0)
  (p : ℝ) (hp : p ≥ 0)
  (hG : ∀ l : ℕ, l ≥ 2 → (Set.ncard { x ∈ M | x.length = l } ≤ c * Real.rpow l p )) :
  ∀ (s d k : ℕ), s ≥ 1 → d ≥ 3 → 1 ≤ k → k ≤ s →
    (Set.ncard { l : List (FreeMonoid (Fin n)) |
      l.length = k ∧
      (∀ x, x ∈ l → x ∈ (M ∪ A n)) ∧
      (∀ x, x ∈ l → 1 ≤ x.length) ∧
      (l.prod).length = d * s }
      ≤ (Nat.choose (d * s) s : ℝ) * ((n + c) * Real.rpow d p) ^ s) := by
  intro s d k hs hd hk hks
  classical
  let SList : Set (List (FreeMonoid (Fin n))) :=
    { l : List (FreeMonoid (Fin n)) |
        l.length = k ∧
          (∀ x, x ∈ l → x ∈ (M ∪ A n)) ∧
            (∀ x, x ∈ l → 1 ≤ x.length) ∧ (l.prod).length = d * s }
  let SV : Set (List.Vector (FreeMonoid (Fin n)) k) :=
    { v : List.Vector (FreeMonoid (Fin n)) k |
        (∀ i : Fin k, List.Vector.get v i ∈ (M ∪ A n)) ∧
          (∀ i : Fin k, 1 ≤ (List.Vector.get v i).length) ∧
            (List.Vector.toList v).prod.length = d * s }
  have hcongr : SList.ncard = SV.ncard := by
    classical
    refine
      Set.ncard_congr (s := SList) (t := SV)
        (f := fun l hl => (⟨l, hl.1⟩ : List.Vector (FreeMonoid (Fin n)) k)) ?_ ?_ ?_
    · intro l hl
      rcases hl with ⟨hlen, hm, hlen1, hprod⟩
      refine ⟨?_, ?_, ?_⟩
      · intro i
        have hi : List.Vector.get (⟨l, hlen⟩ : List.Vector (FreeMonoid (Fin n)) k) i ∈ l := by
          -- get_mem gives membership in toList; toList is l
          simpa using
            (List.Vector.get_mem i (⟨l, hlen⟩ : List.Vector (FreeMonoid (Fin n)) k))
        exact hm _ hi
      · intro i
        have hi : List.Vector.get (⟨l, hlen⟩ : List.Vector (FreeMonoid (Fin n)) k) i ∈ l := by
          simpa using
            (List.Vector.get_mem i (⟨l, hlen⟩ : List.Vector (FreeMonoid (Fin n)) k))
        exact hlen1 _ hi
      · simpa using hprod
    · intro a b ha hb hab
      have := congrArg (fun v : List.Vector (FreeMonoid (Fin n)) k => List.Vector.toList v) hab
      simpa using this
    · intro v hv
      refine ⟨List.Vector.toList v, ?_, ?_⟩
      · refine ⟨?_, ?_, ?_, ?_⟩
        · simpa using (List.Vector.toList_length v)
        · intro x hx
          rcases (List.Vector.mem_iff_get (v := v) (a := x)).1 hx with ⟨i, rfl⟩
          exact hv.1 i
        · intro x hx
          rcases (List.Vector.mem_iff_get (v := v) (a := x)).1 hx with ⟨i, rfl⟩
          exact hv.2.1 i
        · simpa using hv.2.2
      · simpa using (List.Vector.mk_toList v (by simpa using (List.Vector.toList_length v)))
  have hvec : (SV.ncard : ℝ) ≤
      (Nat.choose (d * s) s : ℝ) * ((n + c) * Real.rpow d p) ^ s := by
    simpa [SV] using
      (lemma4_ncard_reps_len_eq_k_le_choose_mul_vector n hn M c hc p hp hG s d k hs hd hk hks)
  have hlist : (SList.ncard : ℝ) ≤
      (Nat.choose (d * s) s : ℝ) * ((n + c) * Real.rpow d p) ^ s := by
    simpa [hcongr] using hvec
  simpa [SList] using hlist

theorem lemma4_ncard_reps_le_choose_mul (n : ℕ) (hn : n ≥ 2)
  (M : Set (FreeMonoid (Fin n)))
  (c : ℝ) (hc : c > 0)
  (p : ℝ) (hp : p ≥ 0)
  (hG : ∀ l : ℕ, l ≥ 2 → (Set.ncard { x ∈ M | x.length = l } ≤ c * Real.rpow l p )) :
  ∀ (s d : ℕ), s ≥ 1 → d ≥ 3 →
    (Set.ncard { l : List (FreeMonoid (Fin n)) |
      l.length ≤ s ∧
      (∀ x, x ∈ l → x ∈ (M ∪ A n)) ∧
      (∀ x, x ∈ l → 1 ≤ x.length) ∧
      (l.prod).length = d * s }
      ≤ (Nat.choose (d * s) s : ℝ) * (2 * (n + c) * Real.rpow d p) ^ s) := by
  intro s d hs hd
  classical
  -- Abbreviations
  let Reps : Set (List (FreeMonoid (Fin n))) :=
    { l : List (FreeMonoid (Fin n)) |
      l.length ≤ s ∧
      (∀ x, x ∈ l → x ∈ (M ∪ A n)) ∧
      (∀ x, x ∈ l → 1 ≤ x.length) ∧
      (l.prod).length = d * s }
  let Repsk : ℕ → Set (List (FreeMonoid (Fin n))) := fun k =>
    { l : List (FreeMonoid (Fin n)) |
      l.length = k ∧
      (∀ x, x ∈ l → x ∈ (M ∪ A n)) ∧
      (∀ x, x ∈ l → 1 ≤ x.length) ∧
      (l.prod).length = d * s }
  let t : Finset ℕ := Finset.Icc 1 s

  have hReps_eq : Reps = ⋃ k ∈ t, Repsk k := by
    ext l
    constructor
    · intro hl
      rcases hl with ⟨hlen_le, hmem, hlen1, hprod⟩
      have hspos : 0 < s := by omega
      have hdpos : 0 < d := by omega
      have hdspos : 0 < d * s := Nat.mul_pos hdpos hspos
      have hlen_ne0 : l.length ≠ 0 := by
        intro hlen0
        cases l with
        | nil =>
            have h0 : d * s = 0 := by
              have : (0 : ℕ) = d * s := by
                simpa using hprod
              simpa using this.symm
            exact (Nat.ne_of_gt hdspos) h0
        | cons a l =>
            have : Nat.succ l.length = 0 := by
              simpa using hlen0
            exact (Nat.succ_ne_zero l.length) this
      have hlen_pos : 0 < l.length := Nat.pos_of_ne_zero hlen_ne0
      have hlen_ge1 : 1 ≤ l.length := (Nat.succ_le_iff).2 hlen_pos
      have ht_mem : l.length ∈ t := by
        have : 1 ≤ l.length ∧ l.length ≤ s := ⟨hlen_ge1, hlen_le⟩
        simpa [t, Finset.mem_Icc] using this
      refine Set.mem_iUnion.2 ?_
      refine ⟨l.length, ?_⟩
      refine Set.mem_iUnion.2 ?_
      refine ⟨ht_mem, ?_⟩
      exact ⟨rfl, hmem, hlen1, hprod⟩
    · intro hl
      rcases (by
        classical
        simpa [t] using hl) with ⟨k, hk, hlk⟩
      rcases (by
        classical
        simpa [Repsk] using hlk) with ⟨hlen_eq, hmem, hlen1, hprod⟩
      have hk_le : k ≤ s := hk.2
      refine ⟨?_, hmem, hlen1, hprod⟩
      simpa [hlen_eq] using hk_le

  -- Union bound, cast to ℝ
  have hUnionReal : ((⋃ k ∈ t, Repsk k).ncard : ℝ) ≤
      Finset.sum t (fun k => ((Repsk k).ncard : ℝ)) := by
    have hnat := Finset.set_ncard_biUnion_le (t := t) (s := Repsk)
    have hcast : ((⋃ k ∈ t, Repsk k).ncard : ℝ) ≤
        ((Finset.sum t (fun k => (Repsk k).ncard) : ℕ) : ℝ) := by
      exact_mod_cast hnat
    simpa [Nat.cast_sum] using hcast

  have hReps_le_sum : (Reps.ncard : ℝ) ≤ Finset.sum t (fun k => ((Repsk k).ncard : ℝ)) := by
    simpa [hReps_eq] using hUnionReal

  -- Bound each slice using the axiom lemma
  let B : ℝ := (Nat.choose (d * s) s : ℝ) * ((n + c) * Real.rpow d p) ^ s

  have hsum_le : Finset.sum t (fun k => ((Repsk k).ncard : ℝ)) ≤ Finset.sum t (fun _ => B) := by
    refine Finset.sum_le_sum ?_
    intro k hk
    have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
    have hk2 : k ≤ s := (Finset.mem_Icc.mp hk).2
    simpa [Repsk, B] using
      (lemma4_ncard_reps_len_eq_k_le_choose_mul (n := n) hn (M := M) (c := c) hc (p := p) hp hG
        (s := s) (d := d) (k := k) hs hd hk1 hk2)

  have hsum_const : Finset.sum t (fun _ => B) = (t.card : ℝ) * B := by
    simp [Finset.sum_const, mul_assoc, mul_left_comm, mul_comm]

  have htcard_nat : t.card = s := by
    have ht' : t.card = s + 1 - 1 := by
      simpa [t] using (Nat.card_Icc (a := (1 : ℕ)) (b := s))
    -- simplify (s + 1 - 1)
    have hsimp : s + 1 - 1 = s := by omega
    simpa [hsimp] using ht'

  have htcard : (t.card : ℝ) = s := by
    exact_mod_cast htcard_nat

  have hReps_le : (Reps.ncard : ℝ) ≤ (s : ℝ) * B := by
    calc
      (Reps.ncard : ℝ)
          ≤ Finset.sum t (fun k => ((Repsk k).ncard : ℝ)) := hReps_le_sum
      _ ≤ Finset.sum t (fun _ => B) := hsum_le
      _ = (t.card : ℝ) * B := hsum_const
      _ = (s : ℝ) * B := by simpa [htcard]

  -- show (s:ℝ) ≤ (2:ℝ)^s
  have hs_le_two_pow : (s : ℝ) ≤ (2 : ℝ) ^ s := by
    have hs_le_two_mul : s ≤ 2 * s := by omega
    have htwo_mul_le_pow : 2 * s ≤ 2 ^ s := by
      simpa using (Nat.mul_le_pow (a := 2) (by decide : (2 : ℕ) ≠ 1) s)
    have hs_le_pow_nat : s ≤ 2 ^ s := le_trans hs_le_two_mul htwo_mul_le_pow
    exact_mod_cast hs_le_pow_nat

  -- Nonnegativity of B
  have hB_nonneg : 0 ≤ B := by
    have hchoose_nonneg : 0 ≤ (Nat.choose (d * s) s : ℝ) := by
      exact_mod_cast (Nat.zero_le (Nat.choose (d * s) s))
    have hn_nonneg : 0 ≤ (n : ℝ) := by
      exact_mod_cast (Nat.zero_le n)
    have hc_nonneg : 0 ≤ c := le_of_lt hc
    have hnc_nonneg : 0 ≤ (n : ℝ) + c := add_nonneg hn_nonneg hc_nonneg
    have hd_nonneg : 0 ≤ (d : ℝ) := by
      exact_mod_cast (Nat.zero_le d)
    have hrpow_nonneg : 0 ≤ Real.rpow (d : ℝ) p := by
      simpa using (Real.rpow_nonneg hd_nonneg p)
    have hbase_nonneg : 0 ≤ ((n : ℝ) + c) * Real.rpow (d : ℝ) p := mul_nonneg hnc_nonneg hrpow_nonneg
    have hpow_nonneg : 0 ≤ (((n : ℝ) + c) * Real.rpow (d : ℝ) p) ^ s := pow_nonneg hbase_nonneg s
    dsimp [B]
    exact mul_nonneg hchoose_nonneg hpow_nonneg

  have hReps_le' : (Reps.ncard : ℝ) ≤ ((2 : ℝ) ^ s) * B := by
    have hmul : (s : ℝ) * B ≤ ((2 : ℝ) ^ s) * B := by
      have := mul_le_mul_of_nonneg_right hs_le_two_pow hB_nonneg
      simpa [mul_assoc] using this
    exact le_trans hReps_le hmul

  have hfinal : (Reps.ncard : ℝ) ≤ (Nat.choose (d * s) s : ℝ) * (2 * (n + c) * Real.rpow d p) ^ s := by
    have hrewrite : ((2 : ℝ) ^ s) * B = (Nat.choose (d * s) s : ℝ) * (2 * (n + c) * Real.rpow d p) ^ s := by
      simp [B, mul_pow, mul_assoc, mul_left_comm, mul_comm]
    calc
      (Reps.ncard : ℝ) ≤ ((2 : ℝ) ^ s) * B := hReps_le'
      _ = (Nat.choose (d * s) s : ℝ) * (2 * (n + c) * Real.rpow d p) ^ s := hrewrite

  simpa [Reps] using hfinal

theorem lemma4_prod_filter_length_ne_zero (n : ℕ) (l : List (FreeMonoid (Fin n))) :
  (List.prod (l.filter (fun x : FreeMonoid (Fin n) => decide (x.length ≠ 0)))) = l.prod := by
  classical
  induction l with
  | nil =>
      simp
  | cons a t ih =>
      have ih' : (List.filter (fun x : FreeMonoid (Fin n) => !decide (x = 1)) t).prod = t.prod := by
        simpa [FreeMonoid.length_eq_zero] using ih
      by_cases ha : a.length = 0
      · have a1 : a = 1 := (FreeMonoid.length_eq_zero).1 ha
        subst a1
        simp [List.filter, FreeMonoid.length_one, ih', FreeMonoid.length_eq_zero]
      · have ha' : a.length ≠ 0 := ha
        simp [List.filter, ha', ih', FreeMonoid.length_eq_zero]

theorem lemma4_ncard_ball_slice_le_ncard_reps (n : ℕ) (M : Set (FreeMonoid (Fin n))) (s R : ℕ) :
  Set.ncard { w ∈ Ball s (M ∪ A n) | w.length = R } ≤
    Set.ncard { l : List (FreeMonoid (Fin n)) |
      l.length ≤ s ∧
      (∀ x, x ∈ l → x ∈ (M ∪ A n)) ∧
      (∀ x, x ∈ l → 1 ≤ x.length) ∧
      (l.prod).length = R } := by
  classical
  let X : Set (FreeMonoid (Fin n)) := M ∪ A n
  let W : Set (FreeMonoid (Fin n)) := { w ∈ Ball s X | w.length = R }
  let Reps : Set (List (FreeMonoid (Fin n))) :=
    { l : List (FreeMonoid (Fin n)) |
      l.length ≤ s ∧
        (∀ x, x ∈ l → x ∈ X) ∧
        (∀ x, x ∈ l → 1 ≤ x.length) ∧
        (l.prod).length = R }

  have hsub : W ⊆ (fun l : List (FreeMonoid (Fin n)) => l.prod) '' Reps := by
    intro w hw
    rcases hw with ⟨hwBall, hwLen⟩
    rcases hwBall with ⟨l, hl_len, hl_mem, hl_prod⟩
    let l0 : List (FreeMonoid (Fin n)) :=
      l.filter (fun x : FreeMonoid (Fin n) => decide (x.length ≠ 0))
    have hl0_prod : l0.prod = w := by
      have hprod : l0.prod = l.prod := by
        simpa [l0] using (lemma4_prod_filter_length_ne_zero n l)
      exact hprod.trans hl_prod
    have hl0_len : l0.length ≤ s := by
      have hlen : l0.length ≤ l.length := by
        simpa [l0] using
          (List.length_filter_le (p := fun x : FreeMonoid (Fin n) => decide (x.length ≠ 0)) l)
      exact le_trans hlen hl_len
    have hl0_mem : ∀ x, x ∈ l0 → x ∈ X := by
      intro x hx
      apply hl_mem x
      exact List.mem_of_mem_filter hx
    have hl0_pos : ∀ x, x ∈ l0 → 1 ≤ x.length := by
      intro x hx
      have hxdec : decide (x.length ≠ 0) :=
        List.of_mem_filter (p := fun x : FreeMonoid (Fin n) => decide (x.length ≠ 0)) hx
      have hxne : x.length ≠ 0 := Bool.of_decide_true hxdec
      exact Nat.succ_le_iff.2 (Nat.pos_of_ne_zero hxne)
    refine ⟨l0, ?_, hl0_prod⟩
    refine ⟨hl0_len, ?_, ?_, ?_⟩
    · intro x hx
      exact hl0_mem x hx
    · intro x hx
      exact hl0_pos x hx
    · calc
        (l0.prod).length = w.length := by
          simpa using congrArg (fun t : FreeMonoid (Fin n) => t.length) hl0_prod
        _ = R := hwLen

  -- finiteness of the sphere
  have hsphere : ({ w : FreeMonoid (Fin n) | w.length = R }).Finite := by
    simpa [FreeMonoid, FreeMonoid.length] using (List.finite_length_eq (α := Fin n) R)

  have himgSubset : ((fun l : List (FreeMonoid (Fin n)) => l.prod) '' Reps) ⊆
      { w : FreeMonoid (Fin n) | w.length = R } := by
    intro w hw
    rcases hw with ⟨l, hl, rfl⟩
    simpa using hl.2.2.2

  have himgFinite : ((fun l : List (FreeMonoid (Fin n)) => l.prod) '' Reps).Finite :=
    hsphere.subset himgSubset

  -- length of an element is bounded by length of the product
  have hlen_le_prod : ∀ (l : List (FreeMonoid (Fin n))) (x : FreeMonoid (Fin n)),
      x ∈ l → x.length ≤ l.prod.length := by
    intro l
    induction l with
    | nil =>
        intro x hx
        cases hx
    | cons a t ih =>
        intro x hx
        cases List.mem_cons.1 hx with
        | inl hx_eq =>
            subst x
            have : a.length ≤ a.length + t.prod.length := Nat.le_add_right _ _
            simpa [List.prod_cons, FreeMonoid.length_mul] using this
        | inr hx_mem =>
            have hxt : x.length ≤ t.prod.length := ih x hx_mem
            have ht : t.prod.length ≤ (a :: t).prod.length := by
              have : t.prod.length ≤ a.length + t.prod.length := Nat.le_add_left _ _
              simpa [List.prod_cons, FreeMonoid.length_mul] using this
            exact le_trans hxt ht

  let T : Set (List (FreeMonoid (Fin n))) :=
    { l : List (FreeMonoid (Fin n)) | l.length ≤ s ∧ ∀ x, x ∈ l → x.length ≤ R }

  have hReps_sub : Reps ⊆ T := by
    intro l hl
    refine ⟨hl.1, ?_⟩
    intro x hx
    have hxle : x.length ≤ l.prod.length := hlen_le_prod l x hx
    have hprodlen : l.prod.length = R := hl.2.2.2
    simpa [hprodlen] using hxle

  -- finite set of words of length ≤ R
  have hWordsLe : ({ w : FreeMonoid (Fin n) | w.length ≤ R }).Finite := by
    simpa [FreeMonoid, FreeMonoid.length] using (List.finite_length_le (α := Fin n) R)

  -- make the bounded-length words into a finite type
  let β := { w : FreeMonoid (Fin n) // w.length ≤ R }
  haveI : Fintype β := hWordsLe.fintype
  haveI : Finite β := by infer_instance

  have hDom : ({ l : List β | l.length ≤ s }).Finite := by
    simpa using (List.finite_length_le (α := β) s)

  let f : List β → List (FreeMonoid (Fin n)) := fun l => l.map Subtype.val

  have hTfinite : T.Finite := by
    have hImageFinite : (f '' { l : List β | l.length ≤ s }).Finite :=
      (hDom.image f)
    refine hImageFinite.subset ?_
    intro l hl
    rcases hl with ⟨hl_len, hl_all⟩
    let lβ : List β :=
      l.attach.map (fun x : {w // w ∈ l} => ⟨x.1, hl_all x.1 x.2⟩)
    refine ⟨lβ, ?_, ?_⟩
    ·
      have : lβ.length = l.length := by
        simp [lβ]
      simpa [this] using hl_len
    ·
      dsimp [f]
      calc
        lβ.map Subtype.val = l.attach.map Subtype.val := by
          simp [lβ]
        _ = l := List.attach_map_subtype_val l

  have hRepsFinite : Reps.Finite := hTfinite.subset hReps_sub

  have hWle : Set.ncard W ≤ Set.ncard ((fun l : List (FreeMonoid (Fin n)) => l.prod) '' Reps) :=
    Set.ncard_le_ncard hsub himgFinite

  have hImgle :
      Set.ncard ((fun l : List (FreeMonoid (Fin n)) => l.prod) '' Reps) ≤ Set.ncard Reps := by
    simpa using
      (Set.ncard_image_le (f := fun l : List (FreeMonoid (Fin n)) => l.prod) (s := Reps)
        (hs := hRepsFinite))

  have : Set.ncard W ≤ Set.ncard Reps := le_trans hWle hImgle

  simpa [W, Reps, X] using this

theorem lemma4_ncard_ball_length_le (n : ℕ) (hn : n ≥ 2)
  (M : Set (FreeMonoid (Fin n)))
  (c : ℝ) (hc : c > 0)
  (p : ℝ) (hp : p ≥ 0)
  (hG : ∀ l : ℕ, l ≥ 2 → (Set.ncard { x ∈ M | x.length = l } ≤ c * Real.rpow l p )) :
  ∀ (s d : ℕ), s ≥ 1 → d ≥ 3 →
    (Set.ncard { w ∈ Ball s (M ∪ (A n)) | w.length = d * s }
      ≤ (4 * (Real.exp 1) * (n + c) * Real.rpow d (p + 1)) ^ s) := by
  classical
  intro s d hs hd

  -- Step 1: ball slice ≤ reps (in ℕ)
  have hsliceNat :
      Set.ncard { w ∈ Ball s (M ∪ A n) | w.length = d * s } ≤
        Set.ncard { l : List (FreeMonoid (Fin n)) |
          l.length ≤ s ∧
            (∀ x, x ∈ l → x ∈ (M ∪ A n)) ∧
              (∀ x, x ∈ l → 1 ≤ x.length) ∧ (l.prod).length = d * s } :=
    lemma4_ncard_ball_slice_le_ncard_reps n M s (d * s)

  -- cast to ℝ
  have hslice :
      (Set.ncard { w ∈ Ball s (M ∪ A n) | w.length = d * s } : ℝ) ≤
        (Set.ncard { l : List (FreeMonoid (Fin n)) |
          l.length ≤ s ∧
            (∀ x, x ∈ l → x ∈ (M ∪ A n)) ∧
              (∀ x, x ∈ l → 1 ≤ x.length) ∧ (l.prod).length = d * s } : ℝ) := by
    exact_mod_cast hsliceNat

  -- Step 2: reps ≤ choose * (2*(n+c)*d^p)^s
  have hreps :
      (Set.ncard { l : List (FreeMonoid (Fin n)) |
          l.length ≤ s ∧
            (∀ x, x ∈ l → x ∈ (M ∪ A n)) ∧
              (∀ x, x ∈ l → 1 ≤ x.length) ∧ (l.prod).length = d * s } : ℝ)
        ≤ (Nat.choose (d * s) s : ℝ) * (2 * (n + c) * Real.rpow d p) ^ s :=
    lemma4_ncard_reps_le_choose_mul n hn M c hc p hp hG s d hs hd

  -- combine
  have hball :
      (Set.ncard { w ∈ Ball s (M ∪ A n) | w.length = d * s } : ℝ)
        ≤ (Nat.choose (d * s) s : ℝ) * (2 * (n + c) * Real.rpow d p) ^ s :=
    le_trans hslice hreps

  -- Step 3: choose bound
  have hchoose : (Nat.choose (d * s) s : ℝ) ≤ (Real.exp 1 * d) ^ s :=
    lemma4_choose_mul_le_ed_pow d s hs

  -- basic nonneg facts
  have hc0 : (0 : ℝ) ≤ c := le_of_lt hc
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := by exact Nat.cast_nonneg n
  have hnc0 : (0 : ℝ) ≤ (n : ℝ) + c := add_nonneg hn0 hc0
  have hd0 : (0 : ℝ) ≤ (d : ℝ) := by exact Nat.cast_nonneg d
  have hrpowdp0 : (0 : ℝ) ≤ Real.rpow (d : ℝ) p := Real.rpow_nonneg hd0 p

  have hbase0 : (0 : ℝ) ≤ 2 * ((n : ℝ) + c) * Real.rpow (d : ℝ) p := by
    have h2 : (0 : ℝ) ≤ (2 : ℝ) := by norm_num
    exact mul_nonneg (mul_nonneg h2 hnc0) hrpowdp0

  have hnonneg : 0 ≤ (2 * (n + c) * Real.rpow d p) ^ s := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using (pow_nonneg hbase0 s)

  have hmul :
      (Nat.choose (d * s) s : ℝ) * (2 * (n + c) * Real.rpow d p) ^ s ≤
        (Real.exp 1 * d) ^ s * (2 * (n + c) * Real.rpow d p) ^ s :=
    mul_le_mul_of_nonneg_right hchoose hnonneg

  have hbound :
      (Set.ncard { w ∈ Ball s (M ∪ A n) | w.length = d * s } : ℝ)
        ≤ (Real.exp 1 * d) ^ s * (2 * (n + c) * Real.rpow d p) ^ s :=
    le_trans hball hmul

  -- Step 4: rewrite d * d^p = d^(p+1)
  have hrpow : (d : ℝ) * Real.rpow (d : ℝ) p = Real.rpow (d : ℝ) (p + 1) := by
    have h1 : Real.rpow (d : ℝ) (p + 1) = Real.rpow (d : ℝ) p * Real.rpow (d : ℝ) (1 : ℝ) := by
      simpa [add_assoc] using
        (Real.rpow_add_of_nonneg hd0 hp (by norm_num : (0 : ℝ) ≤ (1 : ℝ)) (x := (d : ℝ)) (y := p)
          (z := (1 : ℝ)))
    calc
      (d : ℝ) * Real.rpow (d : ℝ) p
          = Real.rpow (d : ℝ) p * (d : ℝ) := by ac_rfl
      _ = Real.rpow (d : ℝ) p * Real.rpow (d : ℝ) (1 : ℝ) := by simp [Real.rpow_one]
      _ = Real.rpow (d : ℝ) (p + 1) := by
          simpa [h1] using h1.symm

  -- nonneg K for the final 2 ≤ 4 comparison
  have hK : 0 ≤ Real.exp 1 * ((n : ℝ) + c) * Real.rpow (d : ℝ) (p + 1) := by
    have hexp0 : (0 : ℝ) ≤ Real.exp 1 := le_of_lt (Real.exp_pos 1)
    have hrpow0 : (0 : ℝ) ≤ Real.rpow (d : ℝ) (p + 1) := Real.rpow_nonneg hd0 (p + 1)
    exact mul_nonneg (mul_nonneg hexp0 hnc0) hrpow0

  have hbase_le :
      (2 : ℝ) * (Real.exp 1 * ((n : ℝ) + c) * Real.rpow (d : ℝ) (p + 1)) ≤
        (4 : ℝ) * (Real.exp 1 * ((n : ℝ) + c) * Real.rpow (d : ℝ) (p + 1)) := by
    have h24 : (2 : ℝ) ≤ 4 := by norm_num
    exact mul_le_mul_of_nonneg_right h24 hK

  have hpow :
      ((2 : ℝ) * (Real.exp 1 * ((n : ℝ) + c) * Real.rpow (d : ℝ) (p + 1))) ^ s ≤
        ((4 : ℝ) * (Real.exp 1 * ((n : ℝ) + c) * Real.rpow (d : ℝ) (p + 1))) ^ s := by
    have h0 : 0 ≤ (2 : ℝ) * (Real.exp 1 * ((n : ℝ) + c) * Real.rpow (d : ℝ) (p + 1)) := by
      have h2 : (0 : ℝ) ≤ (2 : ℝ) := by norm_num
      exact mul_nonneg h2 hK
    exact (pow_le_pow_left₀ h0 hbase_le s)

  -- Finish with a calc chain
  calc
    (Set.ncard { w ∈ Ball s (M ∪ A n) | w.length = d * s } : ℝ)
        ≤ (Real.exp 1 * d) ^ s * (2 * (n + c) * Real.rpow d p) ^ s := hbound
    _ = ((Real.exp 1 * d) * (2 * (n + c) * Real.rpow d p)) ^ s := by
          simpa [mul_assoc, mul_left_comm, mul_comm] using
            (mul_pow (Real.exp 1 * (d : ℝ)) (2 * ((n : ℝ) + c) * Real.rpow (d : ℝ) p) s).symm
    _ = (2 * Real.exp 1 * ((n : ℝ) + c) * ((d : ℝ) * Real.rpow (d : ℝ) p)) ^ s := by
          have hmulEq :
              (Real.exp 1 * (d : ℝ)) * (2 * ((n : ℝ) + c) * Real.rpow (d : ℝ) p) =
                2 * Real.exp 1 * ((n : ℝ) + c) * ((d : ℝ) * Real.rpow (d : ℝ) p) := by
            ac_rfl
          simpa [hmulEq] using congrArg (fun x : ℝ => x ^ s) hmulEq
    _ = (2 * Real.exp 1 * ((n : ℝ) + c) * Real.rpow (d : ℝ) (p + 1)) ^ s := by
          -- apply hrpow inside the base
          have hbaseEq :
              2 * Real.exp 1 * ((n : ℝ) + c) * ((d : ℝ) * Real.rpow (d : ℝ) p) =
                2 * Real.exp 1 * ((n : ℝ) + c) * Real.rpow (d : ℝ) (p + 1) := by
            -- just rewrite the final factor
            simpa [mul_assoc] using congrArg (fun x : ℝ => 2 * Real.exp 1 * ((n : ℝ) + c) * x) hrpow
          simpa [hbaseEq] using congrArg (fun x : ℝ => x ^ s) hbaseEq
    _ = ((2 : ℝ) * (Real.exp 1 * ((n : ℝ) + c) * Real.rpow (d : ℝ) (p + 1))) ^ s := by
          ring_nf
    _ ≤ ((4 : ℝ) * (Real.exp 1 * ((n : ℝ) + c) * Real.rpow (d : ℝ) (p + 1))) ^ s := hpow
    _ = (4 * Real.exp 1 * (n + c) * Real.rpow d (p + 1)) ^ s := by
          ring_nf


theorem theorem_4_polynomial_density (n : ℕ) (hn : n ≥ 2)
  (M : Set (FreeMonoid (Fin n)))
  (c : ℝ) (hc : c > 0)
  (p : ℝ) (hp : p ≥ 0)
  (hG : ∀ l : ℕ, l ≥ 2 → (Set.ncard { x ∈ M | x.length = l } ≤ c * Real.rpow l p )) :
    ∀ (s d : ℕ), (s ≥ 1) ∧ (isGoodDLemma4 n c p d) →
      ¬ (Ball (d * s) (A n) ⊆ Ball s (M ∪ (A n))) := by
  intro s d hsd
  rcases hsd with ⟨hs, hd⟩
  classical
  intro hsub
  -- Define the set of words of length d*s and the corresponding slice of the ball
  let S : Set (FreeMonoid (Fin n)) := {w : FreeMonoid (Fin n) | w.length = d * s}
  let T : Set (FreeMonoid (Fin n)) := {w : FreeMonoid (Fin n) | w ∈ Ball s (M ∪ (A n)) ∧ w.length = d * s}

  -- S ⊆ T using the assumed inclusion of balls
  have hST : S ⊆ T := by
    intro w hw
    have hwlen : w.length ≤ d * s := by
      exact le_of_eq (by simpa [S] using hw)
    have hwballA : w ∈ Ball (d * s) (A n) :=
      (lemma4_mem_ball_A_iff_length_le n (d * s) w).2 hwlen
    have hwball : w ∈ Ball s (M ∪ (A n)) := hsub hwballA
    refine ⟨hwball, ?_⟩
    simpa [S] using hw

  -- Cardinality of S
  have hcardS : Set.ncard S = n ^ (d * s) := by
    simpa [S] using (lemma4_ncard_words_length_eq_pow (n := n) (r := d * s))

  -- S is finite (since its ncard is nonzero)
  have hSfinite : S.Finite := by
    have hn0 : 0 < n := by omega
    have hpowpos : 0 < n ^ (d * s) := pow_pos hn0 (d * s)
    have hncard_ne0 : Set.ncard S ≠ 0 := by
      exact ne_of_gt (by simpa [hcardS] using hpowpos)
    exact Set.finite_of_ncard_ne_zero hncard_ne0

  -- T is finite since T ⊆ S
  have hTfinite : T.Finite := by
    refine hSfinite.subset ?_
    intro w hw
    have : w.length = d * s := hw.2
    simpa [S] using this

  -- ncard inequality from subset
  have hcard_le : Set.ncard S ≤ Set.ncard T := by
    exact Set.ncard_le_ncard hST hTfinite

  -- Bound the ncard of T using lemma4_ncard_ball_length_le
  have hd3 : d ≥ 3 := hd.1
  let C : ℝ := 4 * Real.exp 1 * (n + c) * Real.rpow d (p + 1)
  have hTbound : (Set.ncard T : ℝ) ≤ C ^ s := by
    simpa [T, C] using
      (lemma4_ncard_ball_length_le (n := n) (hn := hn) (M := M) (c := c) (hc := hc)
        (p := p) (hp := hp) (hG := hG) s d hs hd3)

  -- Combine inequalities to get (n^(d*s) : ℝ) ≤ C^s
  have hle : ((n ^ (d * s) : ℕ) : ℝ) ≤ C ^ s := by
    have hle' : ((Set.ncard S : ℕ) : ℝ) ≤ (Set.ncard T : ℝ) := by
      exact (Nat.cast_le (α := ℝ)).2 hcard_le
    have hle'' : ((n ^ (d * s) : ℕ) : ℝ) ≤ (Set.ncard T : ℝ) := by
      simpa [hcardS] using hle'
    exact le_trans hle'' hTbound

  -- On the other hand, from isGoodDLemma4 we get C^s < (n^(d*s) : ℝ)
  have hC_lt : C < Real.rpow n d := by
    simpa [C] using hd.2
  have hC_nonneg : 0 ≤ C := by
    simp [C]
    positivity
  have hsne : s ≠ 0 := by
    have hspos : 0 < s := by omega
    exact ne_of_gt hspos
  have hpow_lt : C ^ s < (Real.rpow n d) ^ s := by
    exact pow_lt_pow_left₀ hC_lt hC_nonneg hsne
  have hrpow : Real.rpow (n : ℝ) (d : ℝ) = (n : ℝ) ^ d := by
    simpa using (Real.rpow_natCast (x := (n : ℝ)) d)
  have hpow_lt' : C ^ s < (n : ℝ) ^ (d * s) := by
    have htmp : C ^ s < ((n : ℝ) ^ d) ^ s := by
      simpa [hrpow] using hpow_lt
    have hEq : ((n : ℝ) ^ d) ^ s = (n : ℝ) ^ (d * s) := by
      simpa using (pow_mul (n : ℝ) d s).symm
    exact lt_of_lt_of_eq htmp hEq
  have hpow_lt'' : C ^ s < ((n ^ (d * s) : ℕ) : ℝ) := by
    simpa [Nat.cast_pow] using hpow_lt'

  -- Contradiction
  exact (not_lt_of_ge hle) hpow_lt''

