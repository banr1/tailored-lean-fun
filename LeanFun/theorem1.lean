import LeanFun.Definitions

open abelian

theorem ball_A_iff_card_le {n : ℕ} {R : ℕ} (m : FreeAbelianMonoid n) :
  m ∈ Ball R (A n) ↔ m.card ≤ R := by
  classical
  constructor
  · intro hm
    rcases hm with ⟨l, hlR, hlA, rfl⟩
    have hsum_card : ∀ l : List (FreeAbelianMonoid n),
        (∀ x, x ∈ l → x ∈ A n) → (l.sum).card = l.length := by
      intro l
      induction l with
      | nil =>
          intro hl
          simp
      | cons a t ih =>
          intro hl
          have ha_mem : a ∈ A n := hl a (by simp)
          rcases (by simpa [A] using ha_mem) with ⟨i, rfl⟩
          have ht : (t.sum).card = t.length := ih (by
            intro x hx
            exact hl x (by simp [hx]))
          simp [List.sum_cons, Multiset.card_add, ht]
    have : (l.sum).card = l.length := hsum_card l hlA
    -- goal: (l.sum).card ≤ R
    exact le_trans (by simpa [this]) hlR
  · intro hmcard
    -- build a list of singleton multisets summing to m
    have hrepr : ∀ m : FreeAbelianMonoid n,
        ∃ l : List (FreeAbelianMonoid n),
          (∀ x, x ∈ l → x ∈ A n) ∧ l.sum = m ∧ l.length = m.card := by
      intro m
      induction m using Multiset.induction_on with
      | empty =>
          refine ⟨[], ?_, ?_, ?_⟩
          · intro x hx; cases hx
          · simp
          · simp
      | @cons a m ih =>
          rcases ih with ⟨l, hlA, hsum, hlen⟩
          refine ⟨({a} : Multiset (Fin n)) :: l, ?_, ?_, ?_⟩
          · intro x hx
            rcases (List.mem_cons.1 hx) with rfl | hx'
            · -- x = {a}
              exact ⟨a, rfl⟩
            · exact hlA x hx'
          · -- sum
            -- ({a} :: l).sum = {a} + l.sum
            -- = {a} + m = a ::ₘ m
            simpa [List.sum_cons, hsum, Multiset.singleton_add]
          · -- length
            -- length cons = length l + 1, card cons = card m + 1
            simpa [List.length_cons, hlen, Multiset.card_cons, Nat.succ_eq_add_one]
    rcases hrepr m with ⟨l, hlA, hsum, hlen⟩
    refine ⟨l, ?_, hlA, hsum⟩
    -- show length ≤ R
    simpa [hlen] using hmcard

theorem ball_mono_R {n : ℕ} {R R' : ℕ} {X : Set (FreeAbelianMonoid n)} (h : R ≤ R') :
  Ball R X ⊆ Ball R' X := by
  intro m hm
  rcases hm with ⟨l, hlR, hlX, rfl⟩
  refine ⟨l, ?_, hlX, rfl⟩
  exact le_trans hlR h


theorem ball_mono_X {n : ℕ} {R : ℕ} {X Y : Set (FreeAbelianMonoid n)} (h : X ⊆ Y) :
  Ball R X ⊆ Ball R Y := by
  intro z hz
  rcases hz with ⟨l, hlR, hlX, rfl⟩
  refine ⟨l, hlR, ?_, rfl⟩
  intro x hx
  exact h (hlX x hx)


theorem coin_lower_bound_bpow_sub_one (b k : ℕ) (hb : 2 ≤ b) :
  ∀ l : List ℕ,
    (∀ x ∈ l, x = 1 ∨ ∃ j : ℕ, 1 ≤ j ∧ x = b ^ j) →
    l.sum = b ^ k - 1 →
    (b - 1) * k ≤ l.length := by
  induction k with
  | zero =>
      intro l hl hsum
      simp
  | succ k ih =>
      intro l hl hsum
      classical
      -- split `l` into `1`s and the rest
      let ones : List ℕ := l.filter (fun x => x = 1)
      let rest : List ℕ := l.filter (fun x => x ≠ 1)
      let t : ℕ := ones.length
      let m : ℕ := t / b
      let restDiv : List ℕ := rest.map (fun x => x / b)
      let l' : List ℕ := List.replicate m 1 ++ restDiv

      have hb1 : 1 ≤ b := le_trans (by decide : (1 : ℕ) ≤ 2) hb
      have hbpos : 0 < b := lt_of_lt_of_le (by decide : (0 : ℕ) < 2) hb
      have hb0 : b ≠ 0 := Nat.ne_of_gt hbpos

      -- sums split
      have hsum_split : ones.sum + rest.sum = l.sum := by
        simpa [ones, rest] using
          (List.sum_map_filter_add_sum_map_filter_not (p := fun x : ℕ => x = 1)
            (f := fun x : ℕ => x) l)

      -- all elements of `ones` are `1`
      have hones_const : ∀ x ∈ ones, x = (1 : ℕ) := by
        intro x hx
        have hx' : x ∈ l.filter (fun y => y = 1) := by
          simpa [ones] using hx
        have hxpred : decide (x = 1) = true := (List.mem_filter.1 hx').2
        exact decide_eq_true_eq.mp hxpred

      -- `ones.sum = ones.length`
      have hones_sum : ones.sum = t := by
        have := List.sum_eq_card_nsmul ones (1 : ℕ) hones_const
        simpa [t] using this

      -- every element of `rest` is divisible by `b`
      have hrest_dvd_each : ∀ x ∈ rest, b ∣ x := by
        intro x hx
        have hx' : x ∈ l.filter (fun y => y ≠ 1) := by
          simpa [rest] using hx
        have hxL : x ∈ l := (List.mem_filter.1 hx').1
        have hxpred : decide (x ≠ 1) = true := (List.mem_filter.1 hx').2
        have hxne : x ≠ 1 := decide_eq_true_eq.mp hxpred
        have hxmem := hl x hxL
        rcases hxmem with rfl | hxmem
        · exact (hxne rfl).elim
        · rcases hxmem with ⟨j, hjpos, rfl⟩
          have hj0 : j ≠ 0 := by
            apply Nat.ne_of_gt
            exact lt_of_lt_of_le Nat.zero_lt_one hjpos
          exact dvd_pow_self b hj0

      have hrest_dvd : b ∣ rest.sum := by
        exact List.dvd_sum (l := rest) (a := b) (h := hrest_dvd_each)

      -- `l.sum ≡ t [MOD b]`
      have hlsum_modEq : l.sum ≡ t [MOD b] := by
        have hrest0 : rest.sum ≡ 0 [MOD b] := hrest_dvd.modEq_zero_nat
        have htmp : ones.sum + rest.sum ≡ ones.sum [MOD b] := by
          simpa using (Nat.ModEq.add_left ones.sum hrest0)
        -- rewrite using the sum decomposition and `ones.sum = t`
        have htmp' := htmp
        rw [hsum_split] at htmp'
        rw [hones_sum] at htmp'
        exact htmp'

      -- `(b^(k+1) - 1) ≡ (b - 1) [MOD b]`
      have hpow_modEq : b ^ (k + 1) - 1 ≡ b - 1 [MOD b] := by
        have hpow0 : b ^ (k + 1) ≡ 0 [MOD b] :=
          (dvd_pow_self b (Nat.succ_ne_zero k)).modEq_zero_nat
        have hb0' : b ≡ 0 [MOD b] := (dvd_rfl : b ∣ b).modEq_zero_nat
        have hab : b ^ (k + 1) ≡ b [MOD b] := hpow0.trans hb0'.symm
        have hle1 : 1 ≤ b ^ (k + 1) := by
          simpa using (one_le_pow₀ hb1 (n := k + 1))
        exact Nat.ModEq.sub hle1 hb1 hab Nat.ModEq.rfl

      have ht_modEq : t ≡ b - 1 [MOD b] := by
        have : b ^ (k + 1) - 1 ≡ t [MOD b] := by
          simpa [hsum] using hlsum_modEq
        exact this.symm.trans hpow_modEq

      have hb_lt : b - 1 < b := by
        exact tsub_lt_self hbpos (Nat.succ_pos 0)

      have ht_mod : t % b = b - 1 := Nat.mod_eq_of_modEq ht_modEq hb_lt

      -- `t = (b-1) + b*m`
      have ht_eq : t = (b - 1) + b * m := by
        have := (Nat.mod_add_div t b).symm
        simpa [m, ht_mod, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using this

      -- `rest.sum = b * restDiv.sum`
      have hrest_sum_mul : rest.sum = b * restDiv.sum := by
        have hgen :
            ∀ L : List ℕ,
              (∀ x ∈ L, b ∣ x) →
                L.sum = b * (L.map (fun x => x / b)).sum := by
          intro L hL
          induction L with
          | nil =>
              simp
          | cons x xs ih =>
              have hx : b ∣ x := hL x (by simp)
              have hxs : ∀ y ∈ xs, b ∣ y := by
                intro y hy
                exact hL y (by simp [hy])
              have ih' := ih hxs
              have hxmod : x % b = 0 := Nat.mod_eq_zero_of_dvd hx
              have hxmul : b * (x / b) = x := by
                have := Nat.mod_add_div x b
                simpa [hxmod] using this
              -- compute sums
              simp [List.sum_cons, List.map_cons, Nat.mul_add, hxmul, ih', Nat.add_assoc,
                Nat.add_left_comm, Nat.add_comm]
        simpa [restDiv] using hgen rest hrest_dvd_each

      -- compute `l'.sum = b^k - 1`
      have hl'_sum : l'.sum = b ^ k - 1 := by
        have hl'_sum' : l'.sum = m + restDiv.sum := by
          simp [l', List.sum_append, List.sum_replicate]
        have htr : t + rest.sum = b ^ (k + 1) - 1 := by
          have : ones.sum + rest.sum = b ^ (k + 1) - 1 := Eq.trans hsum_split hsum
          simpa [hones_sum] using this
        have htr' : (b - 1) + (b * m + rest.sum) = b ^ (k + 1) - 1 := by
          -- rewrite `t` using `ht_eq`
          simpa [ht_eq, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using htr
        have hsub : b * m + rest.sum = (b ^ (k + 1) - 1) - (b - 1) := by
          calc
            b * m + rest.sum = ((b - 1) + (b * m + rest.sum)) - (b - 1) := by
              simpa using (Nat.add_sub_cancel_left (b - 1) (b * m + rest.sum)).symm
            _ = (b ^ (k + 1) - 1) - (b - 1) := by
              simpa [htr']
        have hsub' : b * m + rest.sum = b ^ (k + 1) - b := by
          have : b ^ (k + 1) - 1 - (b - 1) = b ^ (k + 1) - b := by
            simpa using
              (tsub_tsub_tsub_cancel_right (a := b ^ (k + 1)) (b := b) (c := (1 : ℕ)) hb1)
          simpa [this] using hsub
        have hsub'' : b * m + rest.sum = b * (b ^ k - 1) := by
          calc
            b * m + rest.sum = b ^ (k + 1) - b := hsub'
            _ = b ^ k * b - b := by
              simp [Nat.pow_succ]
            _ = (b ^ k - 1) * b := by
              simpa using (tsub_one_mul (a := b ^ k) (b := b)).symm
            _ = b * (b ^ k - 1) := by
              ac_rfl
        have hsub_b : b * m + b * restDiv.sum = b * (b ^ k - 1) := by
          simpa [hrest_sum_mul] using hsub''
        have hmul : b * (m + restDiv.sum) = b * (b ^ k - 1) := by
          calc
            b * (m + restDiv.sum) = b * m + b * restDiv.sum := by
              simp [Nat.mul_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
            _ = b * (b ^ k - 1) := hsub_b
        have hmain : m + restDiv.sum = b ^ k - 1 := (mul_left_cancel_iff_of_pos hbpos).1 hmul
        -- finish
        calc
          l'.sum = m + restDiv.sum := hl'_sum'
          _ = b ^ k - 1 := hmain

      -- membership property for `l'`
      have hl'_mem : ∀ x ∈ l', x = 1 ∨ ∃ j : ℕ, 1 ≤ j ∧ x = b ^ j := by
        intro x hx
        rcases List.mem_append.1 hx with hx | hx
        · -- replicate part
          left
          simpa using (List.eq_of_mem_replicate hx)
        · -- restDiv part
          rcases List.mem_map.1 hx with ⟨y, hy, rfl⟩
          have hy' : y ∈ l.filter (fun z => z ≠ 1) := by
            simpa [rest] using hy
          have hyL : y ∈ l := (List.mem_filter.1 hy').1
          have hypred : decide (y ≠ 1) = true := (List.mem_filter.1 hy').2
          have hyne : y ≠ 1 := decide_eq_true_eq.mp hypred
          have hy_mem := hl y hyL
          rcases hy_mem with rfl | hy_mem
          · exact (hyne rfl).elim
          · rcases hy_mem with ⟨j, hjpos, hyj⟩
            subst hyj
            cases j with
            | zero =>
                -- impossible since `1 ≤ 0`
                exfalso
                exact Nat.not_succ_le_zero 0 hjpos
            | succ j' =>
                have hdiv : b ^ Nat.succ j' / b = b ^ j' := by
                  simpa [Nat.pow_succ] using
                    (MulDivCancelClass.mul_div_cancel (a := b ^ j') (b := b) hb0)
                cases j' with
                | zero =>
                    left
                    -- `b / b = 1`
                    simpa [one_mul] using
                      (MulDivCancelClass.mul_div_cancel (a := (1 : ℕ)) (b := b) hb0)
                | succ j'' =>
                    right
                    refine ⟨Nat.succ j'', Nat.succ_le_succ (Nat.zero_le j''), ?_⟩
                    simpa using hdiv

      have hIH : (b - 1) * k ≤ l'.length := ih l' hl'_mem hl'_sum

      have hl'_len : l'.length = m + rest.length := by
        simp [l', restDiv]

      have hl_len : l.length = t + rest.length := by
        -- length splits by the predicate `(· = 1)`
        simpa [ones, rest, t] using
          (List.length_eq_length_filter_add (l := l) (f := fun x : ℕ => decide (x = 1)))

      have hl_len' : l.length = (b - 1) + (b * m + rest.length) := by
        calc
          l.length = t + rest.length := hl_len
          _ = ((b - 1) + b * m) + rest.length := by
            simpa [ht_eq]
          _ = (b - 1) + (b * m + rest.length) := by
            simp [Nat.add_assoc]

      have hk1 : (b - 1) * k ≤ m + rest.length := by
        simpa [hl'_len] using hIH

      have hm_le : m ≤ b * m := le_mul_of_one_le_left (Nat.zero_le m) hb1

      have hk2 : (b - 1) * k ≤ b * m + rest.length := by
        exact le_trans hk1 (Nat.add_le_add_right hm_le (rest.length))

      have hk3 : (b - 1) + (b - 1) * k ≤ (b - 1) + (b * m + rest.length) :=
        Nat.add_le_add_left hk2 (b - 1)

      have hk4 : (b - 1) * k + (b - 1) ≤ l.length := by
        have hk3' : (b - 1) * k + (b - 1) ≤ (b - 1) + (b * m + rest.length) := by
          simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hk3
        simpa [hl_len'] using hk3'

      simpa [Nat.mul_succ] using hk4

theorem delta_ge_one_div_of_mod (s d : ℕ) (hd : 0 < d) :
  (1 : ℝ) / d ≤ (1 : ℝ) - ((s % d : ℕ) : ℝ) / d := by
  classical
  set r : ℕ := s % d
  have hd0 : (0 : ℝ) < d := by
    exact_mod_cast hd
  have hd0' : (d : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hd)
  have hrlt : r < d := by
    simpa [r] using Nat.mod_lt s hd
  have hrle : r ≤ d - 1 := by
    exact Nat.le_pred_of_lt hrlt
  -- cast through `((d - 1 : ℕ) : ℝ)` (not `(d - 1 : ℝ)`)
  have hrle_real : (r : ℝ) ≤ ((d - 1 : ℕ) : ℝ) := by
    exact_mod_cast hrle
  have hdiv : (r : ℝ) / d ≤ ((d - 1 : ℕ) : ℝ) / d := by
    exact div_le_div_of_nonneg_right hrle_real (le_of_lt hd0)
  have hsub : (1 : ℝ) - ((d - 1 : ℕ) : ℝ) / d ≤ (1 : ℝ) - (r : ℝ) / d := by
    simpa using (sub_le_sub_left hdiv (1 : ℝ))
  have hnum : (d : ℝ) - ((d - 1 : ℕ) : ℝ) = (1 : ℝ) := by
    -- rewrite `((d - 1 : ℕ) : ℝ)` as `(d : ℝ) - 1`
    simpa [Nat.cast_pred (R := ℝ) hd] using (sub_sub_cancel (d : ℝ) (1 : ℝ))
  have hleft : (1 : ℝ) - ((d - 1 : ℕ) : ℝ) / d = (1 : ℝ) / d := by
    calc
      (1 : ℝ) - ((d - 1 : ℕ) : ℝ) / d
          = ((d : ℝ) - ((d - 1 : ℕ) : ℝ)) / d := by
              simpa using (one_sub_div (a := ((d - 1 : ℕ) : ℝ)) (b := (d : ℝ)) hd0')
      _ = (1 : ℝ) / d := by
            simp [hnum]
  have : (1 : ℝ) / d ≤ (1 : ℝ) - (r : ℝ) / d := by
    simpa [hleft] using hsub
  simpa [r] using this

theorem encodeCount_in_ball_macro_union (n b : ℕ) (hb : 2 ≤ b) (i : Fin n) (x : ℕ) :
  Multiset.replicate x i ∈ Ball ((b - 1) * (Nat.log b x + 1)) (MacroSet n b ∪ A n) := by
  classical
  have hb1 : 1 < b := lt_of_lt_of_le (by decide : 1 < 2) hb

  have hgen_mem : ∀ j : ℕ, Multiset.replicate (b ^ j) i ∈ MacroSet n b ∪ A n := by
    intro j
    cases j with
    | zero =>
        right
        refine ⟨i, ?_⟩
        simp only [A, pow_zero, Multiset.replicate_one]
    | succ j =>
        left
        refine ⟨i, j.succ, ?_, rfl⟩
        simpa using (Nat.succ_le_succ (Nat.zero_le j))

  let build : List ℕ → ℕ → List (FreeAbelianMonoid n) :=
    fun ds =>
      ds.recOn (fun _ => [])
        (fun d ds ih j => List.replicate d (Multiset.replicate (b ^ j) i) ++ ih (j + 1))

  have hbuild_len : ∀ (ds : List ℕ) (j : ℕ), (build ds j).length = ds.sum := by
    intro ds j
    induction ds generalizing j with
    | nil =>
        simp [build]
    | cons d ds ih =>
        simp [build, ih, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

  have hbuild_mem : ∀ (ds : List ℕ) (j : ℕ) (m : FreeAbelianMonoid n),
      m ∈ build ds j → m ∈ MacroSet n b ∪ A n := by
    intro ds j m hm
    induction ds generalizing j with
    | nil =>
        simpa [build] using hm
    | cons d ds ih =>
        have hm' : m ∈ List.replicate d (Multiset.replicate (b ^ j) i) ∨ m ∈ build ds (j + 1) := by
          have : m ∈ List.replicate d (Multiset.replicate (b ^ j) i) ++ build ds (j + 1) := by
            simpa [build] using hm
          exact (List.mem_append.mp this)
        cases hm' with
        | inl hrep =>
            have hm_eq : m = Multiset.replicate (b ^ j) i := by
              rcases (List.mem_replicate.mp hrep) with ⟨_, rfl⟩
              rfl
            simpa [hm_eq] using (hgen_mem j)
        | inr htail =>
            exact ih (j := j + 1) htail

  have hbuild_sum : ∀ (ds : List ℕ) (j : ℕ),
      (build ds j).sum = Multiset.replicate (Nat.ofDigits b ds * b ^ j) i := by
    intro ds j
    induction ds generalizing j with
    | nil =>
        simp [build]
    | cons d ds ih =>
        simp [build, ih, Nat.ofDigits, Multiset.nsmul_replicate, Multiset.replicate_add, Nat.pow_succ,
          Nat.mul_add, Nat.add_mul, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm, Nat.add_assoc, Nat.add_left_comm,
          Nat.add_comm]

  let digs : List ℕ := Nat.digits b x
  let l : List (FreeAbelianMonoid n) := build digs 0

  refine ⟨l, ?_, ?_, ?_⟩
  ·
    have hlen_eq : l.length = digs.sum := by
      simp [l, digs, hbuild_len, build]

    have hsum_le : digs.sum ≤ digs.length * (b - 1) := by
      have hdigit_le : ∀ d ∈ digs, d ≤ b - 1 := by
        intro d hd
        have hdlt : d < b := Nat.digits_lt_base hb1 (by simpa [digs] using hd)
        exact (Order.le_pred_of_lt hdlt)
      simpa [nsmul_eq_mul] using (List.sum_le_card_nsmul digs (b - 1) hdigit_le)

    by_cases hx : x = 0
    · subst hx
      have : l.length = 0 := by
        simp [l, digs, build]
      simpa [this] using (Nat.zero_le ((b - 1) * (Nat.log b 0 + 1)))
    · have hlen_digits : digs.length = Nat.log b x + 1 := by
        simpa [digs] using (Nat.digits_len b x hb1 hx)
      calc
        l.length = digs.sum := hlen_eq
        _ ≤ digs.length * (b - 1) := hsum_le
        _ = (b - 1) * (Nat.log b x + 1) := by
              simpa [hlen_digits, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]

  ·
    intro m hm
    have hm' : m ∈ build digs 0 := by
      simpa [l] using hm
    exact hbuild_mem digs 0 m hm'

  ·
    have : l.sum = Multiset.replicate x i := by
      have hsum : (build digs 0).sum = Multiset.replicate (Nat.ofDigits b digs * b ^ 0) i := hbuild_sum digs 0
      simpa [l, digs, pow_zero, Nat.ofDigits_digits] using hsum
    simpa using this


theorem compression_length_bound (n b r : ℕ) (hb : 2 ≤ b) :
  Ball r (A n) ⊆ Ball (n * (b - 1) * (Nat.log b r + 1)) (MacroSet n b ∪ A n) := by
  intro m hm
  classical
  -- Bound the total number of generators by the total cardinality
  have hcard : m.card ≤ r := (ball_A_iff_card_le (n := n) (R := r) m).1 hm
  -- A convenient radius bound for each coordinate
  let R0 : ℕ := (b - 1) * (Nat.log b r + 1)
  -- Build a witness list for the sum over the support `m.toFinset`
  have hbuild :
      ∃ l : List (FreeAbelianMonoid n),
        l.length ≤ m.toFinset.card * R0 ∧
          (∀ x, x ∈ l → x ∈ (MacroSet n b ∪ A n)) ∧
            l.sum = ∑ i ∈ m.toFinset, Multiset.replicate (m.count i) i := by
    classical
    -- Induction over the finite support of `m`
    refine Finset.induction_on m.toFinset ?_ ?_
    · refine ⟨[], ?_, ?_, ?_⟩
      · simp
      · intro x hx
        cases hx
      · simp
    · intro a s ha hs
      rcases hs with ⟨l, hllen, hlmem, hlsum⟩
      -- Get an encoding list for the `a`-coordinate
      have haBall := encodeCount_in_ball_macro_union n b hb a (m.count a)
      rcases haBall with ⟨la, hla_len, hla_mem, hla_sum⟩
      -- Upgrade the length bound using `m.count a ≤ r`
      have hcount_le_r : m.count a ≤ r :=
        le_trans (Multiset.count_le_card a m) hcard
      have hlog_le : Nat.log b (m.count a) ≤ Nat.log b r := Nat.log_mono_right hcount_le_r
      have hRa : (b - 1) * (Nat.log b (m.count a) + 1) ≤ R0 := by
        have : Nat.log b (m.count a) + 1 ≤ Nat.log b r + 1 := Nat.add_le_add_right hlog_le 1
        simpa [R0, Nat.mul_assoc] using Nat.mul_le_mul_left (b - 1) this
      have hla_len' : la.length ≤ R0 := le_trans hla_len hRa
      refine ⟨l ++ la, ?_, ?_, ?_⟩
      · -- length bound
        have hlen_add : l.length + la.length ≤ s.card * R0 + R0 :=
          Nat.add_le_add hllen hla_len'
        have hRHS : s.card * R0 + R0 ≤ (s.card + 1) * R0 := by
          have hEq : s.card * R0 + R0 = (s.card + 1) * R0 := by
            calc
              s.card * R0 + R0 = s.card * R0 + 1 * R0 := by simp [Nat.one_mul]
              _ = (s.card + 1) * R0 := by
                simpa using (Nat.add_mul s.card 1 R0).symm
          exact le_of_eq hEq
        have hlen1 : (l ++ la).length ≤ (s.card + 1) * R0 := by
          have : (l ++ la).length = l.length + la.length := by simp [List.length_append]
          exact (this ▸ le_trans hlen_add hRHS)
        simpa [Finset.card_insert_of_notMem ha] using hlen1
      · -- membership in the union set
        intro x hx
        have hx' : x ∈ l ∨ x ∈ la := by
          simpa [List.mem_append] using hx
        cases hx' with
        | inl hxL => exact hlmem x hxL
        | inr hxLa => exact hla_mem x hxLa
      · -- sum identity
        let f : Fin n → FreeAbelianMonoid n := fun i => Multiset.replicate (m.count i) i
        have hf_a : f a = Multiset.replicate (m.count a) a := rfl
        calc
          (l ++ la).sum = l.sum + la.sum := by simpa [List.sum_append]
          _ = (∑ i ∈ s, f i) + f a := by
            simpa [f, hlsum, hf_a, hla_sum]
          _ = f a + ∑ i ∈ s, f i := by
            simpa using (add_comm (∑ i ∈ s, f i) (f a))
          _ = ∑ i ∈ insert a s, f i := by
            simpa [f] using (Finset.sum_insert ha (f := f) (s := s)).symm
  rcases hbuild with ⟨l, hllen, hlmem, hlsum⟩
  -- Bound the support size by `n`
  have hcard_support : m.toFinset.card ≤ n := by
    simpa [Fintype.card_fin n] using
      (Finset.card_le_univ (s := m.toFinset) : m.toFinset.card ≤ Fintype.card (Fin n))
  have hlen' : l.length ≤ n * R0 := by
    have : m.toFinset.card * R0 ≤ n * R0 := Nat.mul_le_mul_right R0 hcard_support
    exact le_trans hllen this
  -- Show the coordinate sum is `m`
  have hsum_m : (∑ i ∈ m.toFinset, Multiset.replicate (m.count i) i) = m := by
    simpa [Multiset.nsmul_singleton] using
      (Multiset.toFinset_sum_count_nsmul_eq (s := m))
  -- Finish: provide the witness list for membership in the larger ball
  refine ⟨l, ?_, hlmem, ?_⟩
  · -- length bound matches the target radius
    simpa [R0, Nat.mul_assoc] using hlen'
  · -- sum equals `m`
    simpa [hlsum, hsum_m]

def hardMultiset (n b k : ℕ) : FreeAbelianMonoid n :=
  Finset.sum Finset.univ (fun i : Fin n => Multiset.replicate (b ^ k - 1) i)

theorem hardMultiset_card (n b k : ℕ) :
  (hardMultiset n b k).card = n * (b ^ k - 1) := by
  classical
  unfold hardMultiset
  simp [Multiset.card_sum, Multiset.card_replicate]

theorem hardMultiset_mem_ballA_of_le (n b k R : ℕ) (hb : 2 ≤ b) (hR : n * (b ^ k - 1) ≤ R) :
  hardMultiset n b k ∈ Ball R (A n) := by
  have hcard : (hardMultiset n b k).card ≤ R := by
    simpa [hardMultiset_card] using hR
  exact (ball_A_iff_card_le (n := n) (R := R) (hardMultiset n b k)).2 hcard

theorem hardMultiset_not_mem_ball_of_lt (n b k s : ℕ) (hb : 2 ≤ b) (hs : s < n * (b - 1) * k) :
  hardMultiset n b k ∉ Ball s (MacroSet n b ∪ A n) := by
  classical
  intro hBall
  rcases hBall with ⟨l, hl_len, hl_mem, hl_sum⟩
  let li : Fin n → List ℕ := fun i => (l.filter (fun m => i ∈ m)).map (fun m => m.count i)

  -- coin-type condition on each coordinate list
  have hli_coin : ∀ i : Fin n,
      (∀ x ∈ li i, x = 1 ∨ ∃ j : ℕ, 1 ≤ j ∧ x = b ^ j) := by
    intro i x hx
    rcases (List.mem_map.1 hx) with ⟨m, hm, rfl⟩
    have hm_in : m ∈ l := List.mem_of_mem_filter hm
    have hm_mem' : decide (i ∈ m) = true := by
      simpa using (List.of_mem_filter (p := fun m : FreeAbelianMonoid n => i ∈ m) hm)
    have hm_mem : i ∈ m := (Bool.decide_iff (i ∈ m)).1 hm_mem'
    have hm_count : m.count i ≠ 0 := (Multiset.count_ne_zero).2 hm_mem
    have hmX : m ∈ MacroSet n b ∪ A n := hl_mem m hm_in
    rcases hmX with hmMacro | hmA
    · rcases hmMacro with ⟨i0, j, hj, rfl⟩
      -- use nonzero count to pin down the generator
      have hi0 : i0 = i := by
        by_contra hne
        have : (Multiset.replicate (b ^ j) i0).count i = 0 := by
          simp [Multiset.count_replicate, hne]
        exact hm_count this
      subst hi0
      right
      refine ⟨j, hj, ?_⟩
      simp [Multiset.count_replicate]
    · rcases (by
        simpa [A] using hmA) with ⟨i0, rfl⟩
      have hi0 : i = i0 := by
        by_contra hne
        have : ({i0} : Multiset (Fin n)).count i = 0 := by
          simp [Multiset.count_singleton, hne]
        exact hm_count this
      left
      simp [Multiset.count_singleton, hi0]

  -- helper lemma: sum over filter equals sum over all (since others contribute 0)
  have hfilter_sum (i : Fin n) (l0 : List (FreeAbelianMonoid n)) :
      ((l0.filter (fun m => i ∈ m)).map (fun m => m.count i)).sum =
        (l0.map (fun m => m.count i)).sum := by
    induction l0 with
    | nil => simp
    | cons m t ih =>
        by_cases hm : i ∈ m
        · simp [hm, ih]
        · have hm0 : m.count i = 0 := (Multiset.count_eq_zero).2 hm
          simp [hm, hm0, ih]

  -- sum condition on each coordinate list
  have hli_sum : ∀ i : Fin n, (li i).sum = b ^ k - 1 := by
    intro i
    -- relate filter sum and count i of l.sum
    have hcount : (l.map (fun m => m.count i)).sum = (l.sum).count i := by
      simpa using ((Multiset.countAddMonoidHom i).map_list_sum l).symm
    have hcountHard : (hardMultiset n b k).count i = b ^ k - 1 := by
      classical
      simp [hardMultiset, Multiset.count_sum', Multiset.count_replicate]
    calc
      (li i).sum = (l.map (fun m => m.count i)).sum := by
        simpa [li] using (hfilter_sum i l)
      _ = (l.sum).count i := hcount
      _ = (hardMultiset n b k).count i := by simpa [hl_sum]
      _ = b ^ k - 1 := hcountHard

  have hli_len : ∀ i : Fin n, (b - 1) * k ≤ (li i).length := by
    intro i
    exact coin_lower_bound_bpow_sub_one b k hb (li i) (hli_coin i) (hli_sum i)

  have hsum_lower : n * ((b - 1) * k) ≤ Finset.sum Finset.univ (fun i : Fin n => (li i).length) := by
    have h : Finset.sum Finset.univ (fun _ : Fin n => (b - 1) * k) ≤
        Finset.sum Finset.univ (fun i : Fin n => (li i).length) := by
      refine Finset.sum_le_sum ?_
      intro i hi
      exact hli_len i
    simpa using h

  -- uniqueness: elements in MacroSet∪A have at most one generator
  have h_unique :
      ∀ m : FreeAbelianMonoid n, m ∈ MacroSet n b ∪ A n →
        ∀ {i j : Fin n}, i ∈ m → j ∈ m → i = j := by
    intro m hm i j hi hj
    rcases hm with hmMacro | hmA
    · rcases hmMacro with ⟨i0, j0, hj0, rfl⟩
      rcases (Multiset.mem_replicate).1 hi with ⟨_, rfl⟩
      rcases (Multiset.mem_replicate).1 hj with ⟨_, rfl⟩
      rfl
    · rcases (by
        simpa [A] using hmA) with ⟨i0, rfl⟩
      have hi0 : i = i0 := (Multiset.mem_singleton).1 hi
      have hj0 : j = i0 := (Multiset.mem_singleton).1 hj
      simpa [hi0, hj0]

  have hsum_upper : Finset.sum Finset.univ (fun i : Fin n => (li i).length) ≤ l.length := by
    -- bound filter lengths by induction
    have hsum_filter_le :
        ∀ (l0 : List (FreeAbelianMonoid n)),
          (∀ x ∈ l0, x ∈ MacroSet n b ∪ A n) →
            Finset.sum Finset.univ (fun i : Fin n => (l0.filter (fun m => i ∈ m)).length) ≤ l0.length := by
      intro l0 hmem
      induction l0 with
      | nil =>
          simp
      | cons a t ih =>
          have ha : a ∈ MacroSet n b ∪ A n := hmem a (by simp)
          have hmem_t : ∀ x ∈ t, x ∈ MacroSet n b ∪ A n := by
            intro x hx
            exact hmem x (by simp [hx])
          have ih' := ih hmem_t
          -- pointwise length formula
          have hlen :
              ∀ i : Fin n,
                ((a :: t).filter (fun m => i ∈ m)).length =
                  (t.filter (fun m => i ∈ m)).length + ite (i ∈ a) 1 0 := by
            intro i
            by_cases hi : i ∈ a
            · simp [hi]
            · simp [hi]
          have hsum_decomp :
              Finset.sum Finset.univ (fun i : Fin n => ((a :: t).filter (fun m => i ∈ m)).length) =
                Finset.sum Finset.univ (fun i : Fin n => (t.filter (fun m => i ∈ m)).length) +
                  Finset.sum Finset.univ (fun i : Fin n => ite (i ∈ a) 1 0) := by
            calc
              Finset.sum Finset.univ (fun i : Fin n => ((a :: t).filter (fun m => i ∈ m)).length)
                  = Finset.sum Finset.univ (fun i : Fin n =>
                      (t.filter (fun m => i ∈ m)).length + ite (i ∈ a) 1 0) := by
                        refine Finset.sum_congr rfl ?_
                        intro i hi
                        exact hlen i
              _ = Finset.sum Finset.univ (fun i : Fin n => (t.filter (fun m => i ∈ m)).length) +
                    Finset.sum Finset.univ (fun i : Fin n => ite (i ∈ a) 1 0) := by
                        simpa [Finset.sum_add_distrib]
          -- bound indicator sum by 1
          have hind_le : Finset.sum Finset.univ (fun i : Fin n => ite (i ∈ a) 1 0) ≤ 1 := by
            have hcard_le : (Finset.filter (fun i : Fin n => i ∈ a) Finset.univ).card ≤ 1 := by
              refine (Finset.card_le_one.2 ?_)
              intro i1 hi1 i2 hi2
              have hi1a : i1 ∈ a := (Finset.mem_filter.1 hi1).2
              have hi2a : i2 ∈ a := (Finset.mem_filter.1 hi2).2
              exact h_unique a ha hi1a hi2a
            have hsum_card :
                Finset.sum Finset.univ (fun i : Fin n => ite (i ∈ a) 1 0) =
                  (Finset.filter (fun i : Fin n => i ∈ a) Finset.univ).card := by
              simpa using (Finset.card_filter (p := fun i : Fin n => i ∈ a) (s := Finset.univ)).symm
            simpa [hsum_card] using hcard_le
          -- final inequality
          have :
              Finset.sum Finset.univ (fun i : Fin n => ((a :: t).filter (fun m => i ∈ m)).length)
                ≤ (a :: t).length := by
            rw [hsum_decomp]
            have := Nat.add_le_add ih' hind_le
            simpa using this
          exact this
    have hmain := hsum_filter_le l hl_mem
    simpa [li] using hmain

  have hge : n * (b - 1) * k ≤ s := by
    have : n * ((b - 1) * k) ≤ l.length := le_trans hsum_lower hsum_upper
    have : n * (b - 1) * k ≤ l.length := by
      simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using this
    exact le_trans this hl_len

  exact (Nat.not_lt_of_ge hge hs)


theorem macro_inter_ball_ncard (n b x : ℕ) (hb : 2 ≤ b) :
  (MacroSet n b ∩ Ball x (A n)).ncard = n * Nat.log b x := by
  classical
  by_cases hx : x = 0
  · subst hx
    have hS : MacroSet n b ∩ Ball 0 (A n) = (∅ : Set (FreeAbelianMonoid n)) := by
      ext m
      constructor
      · intro hm
        rcases hm with ⟨hmM, hmB⟩
        rcases hmM with ⟨i, j, hj1, rfl⟩
        have hcard : (Multiset.replicate (b ^ j) i).card ≤ 0 :=
          (ball_A_iff_card_le (n := n) (R := 0) (m := Multiset.replicate (b ^ j) i)).1 hmB
        have hpowle : b ^ j ≤ 0 := by
          simpa [Multiset.card_replicate] using hcard
        have hpow0 : b ^ j = 0 := Nat.le_zero.mp hpowle
        have hb0 : b ≠ 0 := by
          have hbpos : 0 < b := lt_of_lt_of_le Nat.zero_lt_two hb
          exact Nat.ne_of_gt hbpos
        exact (pow_ne_zero j hb0) hpow0
      · intro hm
        cases hm
    simp only [hS, Set.ncard_empty, Nat.log_zero_right, Nat.mul_zero]
  · have hx0 : x ≠ 0 := hx
    let f : (Fin n × Fin (Nat.log b x)) → FreeAbelianMonoid n := fun p =>
      Multiset.replicate (b ^ p.2.1.succ) p.1
    have hS : MacroSet n b ∩ Ball x (A n) = Set.range f := by
      ext m
      constructor
      · intro hm
        rcases hm with ⟨hmM, hmB⟩
        rcases hmM with ⟨i, j, hj1, rfl⟩
        have hcard : (Multiset.replicate (b ^ j) i).card ≤ x :=
          (ball_A_iff_card_le (n := n) (R := x) (m := Multiset.replicate (b ^ j) i)).1 hmB
        have hpowle : b ^ j ≤ x := by
          simpa [Multiset.card_replicate] using hcard
        have hb1 : 1 < b := lt_of_lt_of_le Nat.one_lt_two hb
        have hjle : j ≤ Nat.log b x := Nat.le_log_of_pow_le hb1 hpowle
        have hjpos : 0 < j := lt_of_lt_of_le Nat.zero_lt_one hj1
        have hklt : j - 1 < Nat.log b x := by
          have hkltj : j - 1 < j := tsub_lt_self hjpos Nat.zero_lt_one
          exact lt_of_lt_of_le hkltj hjle
        let k : Fin (Nat.log b x) := ⟨j - 1, hklt⟩
        refine ⟨⟨i, k⟩, ?_⟩
        have hj' : (j - 1).succ = j := by
          simpa [Nat.succ_eq_add_one] using (Nat.sub_add_cancel hj1)
        simp only [f, k, hj']
      · rintro ⟨p, rfl⟩
        constructor
        · refine ⟨p.1, p.2.1.succ, ?_, rfl⟩
          exact Nat.succ_le_succ (Nat.zero_le _)
        · apply (ball_A_iff_card_le (n := n) (R := x)
            (m := Multiset.replicate (b ^ p.2.1.succ) p.1)).2
          have hpow : b ^ p.2.1.succ ≤ x :=
            Nat.pow_le_of_le_log (b := b) (x := p.2.1.succ) (y := x) hx0
              (Nat.succ_le_of_lt p.2.2)
          simpa [Multiset.card_replicate] using hpow
    have hf : Function.Injective f := by
      rintro ⟨i, k⟩ ⟨i', k'⟩ hk
      have hcard : b ^ k.1.succ = b ^ k'.1.succ := by
        simpa [f, Multiset.card_replicate] using congrArg Multiset.card hk
      have hkval_succ : k.1.succ = k'.1.succ := (Nat.pow_right_injective hb) hcard
      have hkval : k.1 = k'.1 := Nat.succ_injective hkval_succ
      have hkFin : k = k' := Fin.ext hkval
      cases hkFin
      have hb0 : b ≠ 0 := by
        have hbpos : 0 < b := lt_of_lt_of_le Nat.zero_lt_two hb
        exact Nat.ne_of_gt hbpos
      have hpow0 : b ^ k.1.succ ≠ 0 := pow_ne_zero _ hb0
      have hi : i = i' :=
        (Multiset.replicate_right_inj (a := i) (b := i') (n := b ^ k.1.succ) hpow0).1
          (by simpa [f] using hk)
      exact Prod.ext hi rfl
    calc
      (MacroSet n b ∩ Ball x (A n)).ncard = (Set.range f).ncard := by
        simpa [hS]
      _ = Nat.card (Fin n × Fin (Nat.log b x)) := Set.ncard_range_of_injective hf
      _ = n * Nat.log b x := by
        simpa [Nat.card_prod, Nat.card_fin]

theorem macro_log_density (n b : ℕ) (h1 : 1 ≤ n) (hb : 2 ≤ b) :
  ∃ (d1 d2 : ℝ), ∀ (x : ℕ), x ≥ b →
    0 < d1 ∧ 0 < d2 ∧
      d1 * (Real.log x) ≤ (MacroSet n b ∩ Ball x (A n)).ncard ∧
      (MacroSet n b ∩ Ball x (A n)).ncard ≤ d2 * (Real.log x) := by
  classical
  let d1 : ℝ := (n : ℝ) / (2 * Real.log b)
  let d2 : ℝ := (n : ℝ) / (Real.log b)
  refine ⟨d1, d2, ?_⟩
  intro x hx
  have hb1 : 1 < b := lt_of_lt_of_le (by decide : (1 : ℕ) < 2) hb
  have hbpos : 0 < b := lt_of_lt_of_le (by decide : (0 : ℕ) < 2) hb
  have hxpos : 0 < x := lt_of_lt_of_le hbpos hx
  have hx0 : x ≠ 0 := Nat.ne_of_gt hxpos
  have hb1R : (1 : ℝ) < (b : ℝ) := by exact_mod_cast hb1
  have hlogb : 0 < Real.log (b : ℝ) := Real.log_pos hb1R
  have hnpos : 0 < n := lt_of_lt_of_le (by decide : (0 : ℕ) < 1) h1
  have hnposR : 0 < (n : ℝ) := by exact_mod_cast hnpos
  have hd2pos : 0 < d2 := by
    dsimp [d2]
    exact div_pos hnposR hlogb
  have hd1pos : 0 < d1 := by
    dsimp [d1]
    have h2log : 0 < (2 : ℝ) * Real.log (b : ℝ) := by
      have h2 : (0 : ℝ) < (2 : ℝ) := by norm_num
      exact mul_pos h2 hlogb
    exact div_pos hnposR h2log
  -- set k
  let k : ℕ := Nat.log b x
  have hncard : (MacroSet n b ∩ Ball x (A n)).ncard = n * k := by
    simpa [k] using macro_inter_ball_ncard n b x hb
  -- upper bound for k
  have hpow_le : b ^ k ≤ x := by
    simpa [k] using (Nat.pow_log_le_self b (x := x) hx0)
  have hpow_leR : ( (b : ℝ) ^ k ) ≤ (x : ℝ) := by
    exact_mod_cast hpow_le
  have hbposR : 0 < (b : ℝ) := by exact_mod_cast hbpos
  have hklog : (k : ℝ) * Real.log (b : ℝ) ≤ Real.log (x : ℝ) := by
    simpa using (Real.le_log_of_pow_le hbposR hpow_leR)
  have hk_le : (k : ℝ) ≤ Real.log (x : ℝ) / Real.log (b : ℝ) := by
    exact (le_div_iff₀ hlogb).2 hklog
  have hnnonnegR : 0 ≤ (n : ℝ) := le_of_lt hnposR
  have hupper : (n : ℝ) * (k : ℝ) ≤ (d2) * Real.log (x : ℝ) := by
    have := mul_le_mul_of_nonneg_left hk_le hnnonnegR
    simpa [d2, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using this
  -- lower bound
  have hkpos : 0 < k := Nat.log_pos hb1 hx
  have hpow_lt : x < b ^ k.succ := by
    simpa [k] using (Nat.lt_pow_succ_log_self hb1 x)
  have hpow_ltR : (x : ℝ) < ( (b : ℝ) ^ k.succ ) := by
    exact_mod_cast hpow_lt
  have hxposR : 0 < (x : ℝ) := by exact_mod_cast hxpos
  have hlog_lt : Real.log (x : ℝ) < Real.log ((b : ℝ) ^ k.succ) := by
    exact Real.log_lt_log hxposR hpow_ltR
  have hlog_le : Real.log (x : ℝ) ≤ (k.succ : ℝ) * Real.log (b : ℝ) := by
    have : Real.log (x : ℝ) ≤ Real.log ((b : ℝ) ^ k.succ) := le_of_lt hlog_lt
    simpa [Real.log_pow, mul_assoc] using this
  have hk_succ_le : (k.succ : ℝ) ≤ (2 : ℝ) * (k : ℝ) := by
    have : k.succ ≤ 2 * k := by
      omega
    exact_mod_cast this
  have hlog_le2 : Real.log (x : ℝ) ≤ (2 : ℝ) * (k : ℝ) * Real.log (b : ℝ) := by
    have := mul_le_mul_of_nonneg_right hk_succ_le (le_of_lt hlogb)
    have := le_trans hlog_le this
    simpa [mul_assoc, mul_left_comm, mul_comm] using this
  have hk_lower : Real.log (x : ℝ) / (2 * Real.log (b : ℝ)) ≤ (k : ℝ) := by
    have hden : 0 < (2 : ℝ) * Real.log (b : ℝ) := by
      have h2 : (0 : ℝ) < (2 : ℝ) := by norm_num
      exact mul_pos h2 hlogb
    have : Real.log (x : ℝ) ≤ (k : ℝ) * (2 * Real.log (b : ℝ)) := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using hlog_le2
    exact (div_le_iff₀ hden).2 this
  have hlower : d1 * Real.log (x : ℝ) ≤ (n : ℝ) * (k : ℝ) := by
    have := mul_le_mul_of_nonneg_left hk_lower hnnonnegR
    simpa [d1, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using this
  -- now assemble
  refine ⟨hd1pos, hd2pos, ?_, ?_⟩
  · have : d1 * Real.log (x : ℝ) ≤ (n * k : ℝ) := by
      -- use hlower
      -- cast
      simpa [Nat.cast_mul, mul_assoc] using hlower
    simpa [hncard, k] using this
  · have : (n * k : ℝ) ≤ d2 * Real.log (x : ℝ) := by
      simpa [Nat.cast_mul, mul_assoc] using hupper
    simpa [hncard, k] using this

theorem natCast_mul_div_cancel (d q : ℕ) (hd : (d : ℝ) ≠ 0) :
  ((d * q : ℕ) : ℝ) / d = (q : ℝ) := by
  -- Rewrite the natural cast product, then cancel.
  simpa [Nat.cast_mul, mul_assoc, mul_comm, mul_left_comm] using
    (mul_div_cancel_left₀ (a := (d : ℝ)) (b := (q : ℝ)) hd)

theorem r1_gt_imp_bn_le_s (n b s : ℕ) (h1 : 1 ≤ n) (hb : 2 ≤ b) (hs : 1 ≤ s) :
  Int.toNat (Int.ceil (Real.rpow b ((s : ℝ) / (n * (b - 1)) - 1))) > s → b * n ≤ s := by
  classical
  intro hr1_gt
  set a : ℝ := Real.rpow (b : ℝ) ((s : ℝ) / (n * (b - 1)) - 1)
  have hr1_gt' : (⌈a⌉₊) > s := by
    simpa [a, Int.ceil_toNat] using hr1_gt
  by_contra hbnle
  have hslt : s < b * n := Nat.lt_of_not_ge hbnle
  have hb1 : (1 : ℝ) < (b : ℝ) := by
    have hb1' : (1 : ℕ) < b := lt_of_lt_of_le (by decide : (1 : ℕ) < 2) hb
    exact_mod_cast hb1'
  have he_lt_one : ((s : ℝ) / (n * (b - 1)) - 1) < (1 : ℝ) := by
    have hnpos : 0 < n := lt_of_lt_of_le (by decide : (0 : ℕ) < 1) h1
    have hb1nat : 1 < b := lt_of_lt_of_le (by decide : (1 : ℕ) < 2) hb
    have hb1mpos : 0 < b - 1 := Nat.sub_pos_of_lt hb1nat
    have hdenposNat : 0 < n * (b - 1) := Nat.mul_pos hnpos hb1mpos
    have hdenpos : (0 : ℝ) < (n * (b - 1) : ℝ) := by
      have : (0 : ℝ) < (n * (b - 1) : ℕ) := (Nat.cast_pos).2 hdenposNat
      simpa [Nat.cast_mul, Nat.cast_sub (le_of_lt hb1nat)] using this
    have hsltR : (s : ℝ) < (b * n : ℝ) := by exact_mod_cast hslt
    have hdivlt : (s : ℝ) / (n * (b - 1) : ℝ) < (b * n : ℝ) / (n * (b - 1) : ℝ) :=
      div_lt_div_of_pos_right hsltR hdenpos
    have hbn_le : (b * n : ℝ) / (n * (b - 1) : ℝ) ≤ (2 : ℝ) := by
      have hb_le : b ≤ 2 * (b - 1) := by omega
      have hmul : b * n ≤ (2 * (b - 1)) * n := Nat.mul_le_mul_right n hb_le
      have hmul' : b * n ≤ 2 * (n * (b - 1)) := by
        simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hmul
      have hmulR : (b * n : ℝ) ≤ (2 : ℝ) * (n * (b - 1) : ℝ) := by
        have : (b * n : ℝ) ≤ (2 * (n * (b - 1)) : ℕ) := by
          exact_mod_cast hmul'
        simpa [Nat.cast_mul, Nat.cast_sub (le_of_lt hb1nat), Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm,
          mul_assoc, mul_left_comm, mul_comm] using this
      exact (div_le_iff₀ hdenpos).2 (by simpa [mul_assoc, mul_left_comm, mul_comm] using hmulR)
    have hdivlt2 : (s : ℝ) / (n * (b - 1) : ℝ) < (2 : ℝ) := lt_of_lt_of_le hdivlt hbn_le
    nlinarith
  have ha_lt_b : a < (b : ℝ) := by
    have : (b : ℝ) ^ ((s : ℝ) / (n * (b - 1)) - 1) < (b : ℝ) ^ (1 : ℝ) :=
      Real.rpow_lt_rpow_of_exponent_lt hb1 he_lt_one
    simpa [a, Real.rpow_one] using this
  have ha_le_b : a ≤ (b : ℝ) := le_of_lt ha_lt_b
  have hceil_le_b : (⌈a⌉₊) ≤ b := (Nat.ceil_le).2 ha_le_b
  have hsltb : s < b := lt_of_lt_of_le hr1_gt' hceil_le_b
  have he_nonpos : ((s : ℝ) / (n * (b - 1)) - 1) ≤ (0 : ℝ) := by
    have hnpos : 0 < n := lt_of_lt_of_le (by decide : (0 : ℕ) < 1) h1
    have hb1nat : 1 < b := lt_of_lt_of_le (by decide : (1 : ℕ) < 2) hb
    have hb1mpos : 0 < b - 1 := Nat.sub_pos_of_lt hb1nat
    have hdenposNat : 0 < n * (b - 1) := Nat.mul_pos hnpos hb1mpos
    have hdenpos : (0 : ℝ) < (n * (b - 1) : ℝ) := by
      have : (0 : ℝ) < (n * (b - 1) : ℕ) := (Nat.cast_pos).2 hdenposNat
      simpa [Nat.cast_mul, Nat.cast_sub (le_of_lt hb1nat)] using this
    have hsle_nat : s ≤ b - 1 := Nat.le_pred_of_lt hsltb
    have hsle1 : (s : ℝ) ≤ (b - 1 : ℝ) := by
      have : (s : ℝ) ≤ (b - 1 : ℕ) := by exact_mod_cast hsle_nat
      simpa [Nat.cast_sub (le_of_lt hb1nat)] using this
    have hb1m_nonneg : (0 : ℝ) ≤ (b - 1 : ℝ) := by
      have : (0 : ℝ) ≤ (b - 1 : ℕ) := by exact_mod_cast (Nat.zero_le (b - 1))
      simpa [Nat.cast_sub (le_of_lt hb1nat)] using this
    have hn1R : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast h1
    have hb1m_le : (b - 1 : ℝ) ≤ (n * (b - 1) : ℝ) := by
      have : (b - 1 : ℝ) ≤ (n : ℝ) * (b - 1 : ℝ) := by
        simpa [one_mul] using (mul_le_mul_of_nonneg_right hn1R hb1m_nonneg)
      simpa [Nat.cast_mul, Nat.cast_sub (le_of_lt hb1nat), mul_assoc, mul_left_comm, mul_comm] using this
    have hsle : (s : ℝ) ≤ (n * (b - 1) : ℝ) := le_trans hsle1 hb1m_le
    have hs_div_le : (s : ℝ) / (n * (b - 1) : ℝ) ≤ (1 : ℝ) := by
      have := (div_le_one hdenpos).2 hsle
      simpa using this
    nlinarith
  have ha_le_one : a ≤ (1 : ℝ) := by
    have hb1le : (1 : ℝ) ≤ (b : ℝ) := le_of_lt hb1
    simpa [a] using (Real.rpow_le_one_of_one_le_of_nonpos hb1le he_nonpos)
  have hceil_le_one : (⌈a⌉₊) ≤ 1 := (Nat.ceil_le).2 (by simpa using ha_le_one)
  have hceil_le_s : (⌈a⌉₊) ≤ s := le_trans hceil_le_one hs
  exact (not_lt_of_ge hceil_le_s) hr1_gt'

theorem r2_witness_card_bound (n b s : ℕ) (h1 : 1 ≤ n) (hb : 2 ≤ b) (hs : 1 ≤ s) :
  let t : ℝ := (s : ℝ) / (n * (b - 1))
  let m : ℕ := (Int.floor (Real.rpow b t)).toNat
  let k : ℕ := Nat.log b m + 1
  n * (b ^ k - 1) ≤ 1 + n * b * m := by
  classical
  -- Unfold the `let` bindings.
  simp
  -- Name the intermediate quantities.
  set t : ℝ := (s : ℝ) / ((n : ℝ) * ((b : ℝ) - 1)) with ht
  set m : ℕ := (Int.floor ((b : ℝ) ^ t)).toNat with hm
  set k : ℕ := Nat.log b m + 1 with hk

  -- First show that `m ≠ 0`.
  have hspos_nat : 0 < s := lt_of_lt_of_le Nat.zero_lt_one hs
  have hnpos_nat : 0 < n := lt_of_lt_of_le Nat.zero_lt_one h1
  have hb1_nat : 1 < b := lt_of_lt_of_le (by decide : 1 < 2) hb

  have hspos : (0 : ℝ) < (s : ℝ) := by
    exact_mod_cast hspos_nat
  have hnpos : (0 : ℝ) < (n : ℝ) := by
    exact_mod_cast hnpos_nat
  have hb1 : (1 : ℝ) < (b : ℝ) := by
    exact_mod_cast hb1_nat
  have hbsub : (0 : ℝ) < (b : ℝ) - 1 := sub_pos.mpr hb1

  have htpos' : (0 : ℝ) < (s : ℝ) / ((n : ℝ) * ((b : ℝ) - 1)) := by
    exact div_pos hspos (mul_pos hnpos hbsub)
  have htpos : (0 : ℝ) < t := by
    simpa [ht] using htpos'

  have hpow1 : (1 : ℝ) < (b : ℝ) ^ t := Real.one_lt_rpow hb1 htpos
  have hmpos_natfloor : 0 < (⌊(b : ℝ) ^ t⌋₊ : ℕ) :=
    (Nat.floor_pos).2 (le_of_lt hpow1)
  have hmpos' : 0 < (Int.floor ((b : ℝ) ^ t)).toNat := by
    simpa [Int.floor_toNat] using hmpos_natfloor
  have hmpos : 0 < m := by
    simpa [hm] using hmpos'
  have hmne : m ≠ 0 := Nat.ne_of_gt hmpos

  -- Use the standard bound `b^(log_b m) ≤ m` for `m ≠ 0`.
  have hlog : b ^ Nat.log b m ≤ m := Nat.pow_log_le_self b hmne

  -- Deduce `b^k ≤ b*m`.
  have hpowk' : b ^ (Nat.log b m + 1) ≤ b * m := by
    -- Multiply the inequality by `b` and rewrite using `pow_succ`.
    have hmul : (b ^ Nat.log b m) * b ≤ m * b := Nat.mul_le_mul_right b hlog
    have hpow : b ^ (Nat.log b m + 1) ≤ m * b := by
      simpa [pow_succ] using hmul
    -- Commute the product on the right.
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hpow

  have hpowk : b ^ k ≤ b * m := by
    simpa [hk] using hpowk'

  -- Now bound `b^k - 1` by `b*m`.
  have hsub : b ^ k - 1 ≤ b * m := by
    exact le_trans (tsub_le_self) hpowk

  -- Multiply by `n` and finish.
  calc
    n * (b ^ k - 1) ≤ n * (b * m) := Nat.mul_le_mul_left n hsub
    _ = n * b * m := by
      simp [Nat.mul_assoc]
    _ ≤ 1 + n * b * m := by
      -- `x ≤ 1 + x`.
      simpa [Nat.add_comm] using (Nat.le_succ (n * b * m))

theorem r2_witness_k_gt (n b s : ℕ) (h1 : 1 ≤ n) (hb : 2 ≤ b) (hs : 1 ≤ s) :
  let t : ℝ := (s : ℝ) / (n * (b - 1))
  let m : ℕ := (Int.floor (Real.rpow b t)).toNat
  let k : ℕ := Nat.log b m + 1
  n * (b - 1) * k > s := by
  classical
  dsimp
  set t : ℝ := (s : ℝ) / (n * (b - 1)) with ht
  set m : ℕ := (Int.floor (Real.rpow b t)).toNat with hm
  set k : ℕ := Nat.log b m + 1 with hk
  set d : ℕ := n * (b - 1) with hd
  have : d * k > s := by
    set q : ℕ := s / d with hq
    have hbge1 : 1 ≤ b := le_trans (by decide : (1:ℕ) ≤ 2) hb
    have hbcast : ((b - 1 : ℕ) : ℝ) = (b : ℝ) - 1 := by
      simpa using (Nat.cast_sub (R := ℝ) hbge1)

    have hqt : (q : ℝ) ≤ t := by
      have h := (Nat.cast_div_le (m := s) (n := d) (α := ℝ))
      have h' : (q : ℝ) ≤ (s : ℝ) / d := by
        simpa [hq] using h
      simpa [ht, hd, Nat.cast_mul, hbcast] using h'

    have hb1 : 1 < b := by
      exact lt_of_lt_of_le (by decide : 1 < 2) hb
    have hb1r : (1 : ℝ) ≤ (b : ℝ) := by
      exact_mod_cast (le_trans (by decide : (1 : ℕ) ≤ 2) hb)

    have hrpow : ( (b : ℝ) ^ (q : ℝ) ) ≤ ( (b : ℝ) ^ t ) := by
      exact Real.rpow_le_rpow_of_exponent_le hb1r hqt

    have hrpow' : ( (b : ℝ) ^ q ) ≤ ( (b : ℝ) ^ t ) := by
      simpa [Real.rpow_natCast] using hrpow

    have hrpow'' : ( (b ^ q : ℕ) : ℝ ) ≤ ( (b : ℝ) ^ t ) := by
      simpa [Nat.cast_pow] using hrpow'

    have ha : (0 : ℝ) ≤ (b : ℝ) ^ t := by
      exact Real.rpow_nonneg (by exact_mod_cast (Nat.zero_le b)) t

    have hpow_le_floor : b ^ q ≤ ⌊(b : ℝ) ^ t⌋₊ := by
      have := (Nat.le_floor_iff (n := b ^ q) (a := (b : ℝ) ^ t) ha)
      exact (this).2 hrpow''

    have hpow_le_m : b ^ q ≤ m := by
      simpa [hm, Int.floor_toNat] using hpow_le_floor

    have hq_le_log : q ≤ Nat.log b m := by
      exact Nat.le_log_of_pow_le hb1 hpow_le_m

    have hq1_le_k : q + 1 ≤ k := by
      have := Nat.add_le_add_right hq_le_log 1
      simpa [hk, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using this

    -- show s < d * (q + 1)
    have hnpos : 0 < n := by
      exact lt_of_lt_of_le (by decide : (0 : ℕ) < 1) h1
    have hbsub : 0 < b - 1 := by
      exact Nat.sub_pos_of_lt hb1
    have hdpos : 0 < d := by
      have : 0 < n * (b - 1) := Nat.mul_pos hnpos hbsub
      simpa [hd] using this

    have hdecomp : s = d * q + s % d := by
      have h := (Nat.div_add_mod s d).symm
      simpa [hq, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using h

    have hmod : s % d < d := by
      exact Nat.mod_lt s hdpos

    have hs_lt_dq1 : d * q + s % d < d * (q + 1) := by
      have h' : d * q + s % d < d * q + d := by
        exact Nat.add_lt_add_left hmod (d * q)
      exact lt_of_lt_of_eq h' (Nat.mul_succ d q).symm

    have hs_lt_dq1' : s < d * (q + 1) := by
      exact lt_of_eq_of_lt hdecomp hs_lt_dq1

    have hs_lt_dk : s < d * k := by
      have hmul : d * (q + 1) ≤ d * k := by
        exact Nat.mul_le_mul_left d hq1_le_k
      exact lt_of_lt_of_le hs_lt_dq1' hmul

    exact hs_lt_dk

  simpa [hd] using this


theorem macro_expansion_upper (n b : ℕ) (h1 : 1 ≤ n) (hb : 2 ≤ b) :
  ∀ s : ℕ, s ≥ 1 →
    (let r2 := 1 + n * b * (Int.toNat <| Int.floor <| Real.rpow b ((s : ℝ) / (n * (b - 1))))
     ¬ (Ball r2 (A n) ⊆ Ball s (MacroSet n b ∪ (A n)))) := by
  intro s hs
  classical
  -- Define the auxiliary parameters appearing in the witness axioms
  let t : ℝ := (s : ℝ) / (n * (b - 1))
  let m : ℕ := (Int.floor (Real.rpow b t)).toNat
  let k : ℕ := Nat.log b m + 1
  let w : FreeAbelianMonoid n := hardMultiset n b k

  have hs1 : 1 ≤ s := by
    exact hs

  have hle : n * (b ^ k - 1) ≤ 1 + n * b * m := by
    simpa [t, m, k] using (r2_witness_card_bound n b s h1 hb hs1)

  have hgt : n * (b - 1) * k > s := by
    simpa [t, m, k] using (r2_witness_k_gt n b s h1 hb hs1)

  have hw_mem : w ∈ Ball (1 + n * b * m) (A n) := by
    simpa [w] using (hardMultiset_mem_ballA_of_le n b k (1 + n * b * m) hb hle)

  have hw_not_mem : w ∉ Ball s (MacroSet n b ∪ A n) := by
    have hslt : s < n * (b - 1) * k := by
      exact hgt
    simpa [w] using (hardMultiset_not_mem_ball_of_lt n b k s hb hslt)

  -- Unfold the `let r2 := ...` in the goal
  dsimp

  intro hsub
  have hw_mem' :
      w ∈ Ball
        (1 + n * b * (Int.toNat <| Int.floor <| Real.rpow b ((s : ℝ) / (n * (b - 1)))))
        (A n) := by
    simpa [m, t] using hw_mem

  have : w ∈ Ball s (MacroSet n b ∪ A n) := hsub hw_mem'
  exact hw_not_mem this

theorem real_div_eq_of_div_add_mod (s d q r : ℕ) (hd : 0 < d) (h : d * q + r = s) :
  (s : ℝ) / d = (q : ℝ) + (r : ℝ) / d := by
  classical
  have hd0 : (d : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hd)

  calc
    (s : ℝ) / d = ((d * q + r : ℕ) : ℝ) / d := by
      have : (s : ℝ) = ((d * q + r : ℕ) : ℝ) := by
        exact_mod_cast h.symm
      simpa [this]
    _ = (((d * q : ℕ) : ℝ) + (r : ℝ)) / d := by
      simp [Nat.cast_add]
    _ = ((d * q : ℕ) : ℝ) / d + (r : ℝ) / d := by
      simpa [add_div]
    _ = (q : ℝ) + (r : ℝ) / d := by
      -- rewrite `(d*q : ℕ)` cast as product of casts, then cancel
      calc
        ((d * q : ℕ) : ℝ) / d + (r : ℝ) / d
            = ((d : ℝ) * (q : ℝ)) / d + (r : ℝ) / d := by
                simp [Nat.cast_mul]
        _ = (q : ℝ) + (r : ℝ) / d := by
                -- simplify the first term using the given axiom
                -- first, revert to the axiom's form
                have : ((d * q : ℕ) : ℝ) / d = (q : ℝ) := natCast_mul_div_cancel d q hd0
                -- also note `((d : ℝ) * (q : ℝ)) = ((d*q : ℕ) : ℝ)`
                -- use the previous simp lemma
                -- We can simply rewrite and finish by simp
                --
                -- Let's just `simp` using the axiom
                simpa [Nat.cast_mul, this, add_assoc]

theorem rpow_delta_inv_le_bn (n b : ℕ) (h1 : 1 ≤ n) (hb : 2 ≤ b) :
  ((b : ℝ) ^ ((1 : ℝ) / (n * (b - 1))) - 1)⁻¹ ≤ (b * n : ℝ) := by
  classical
  have hbpos_nat : 0 < b := lt_of_lt_of_le (by decide : (0:ℕ) < 2) hb
  have hnpos_nat : 0 < n := lt_of_lt_of_le (by decide : (0:ℕ) < 1) h1
  have hbpos : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hbpos_nat
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hnpos_nat

  set y : ℝ := (1 : ℝ) / ((n : ℝ) * ((b : ℝ) - 1))

  have hrpow : (b : ℝ) ^ y = Real.exp (Real.log (b : ℝ) * y) := by
    simpa [y] using (Real.rpow_def_of_pos hbpos y)

  have h_add : Real.log (b : ℝ) * y + 1 ≤ (b : ℝ) ^ y := by
    have := Real.add_one_le_exp (Real.log (b : ℝ) * y)
    simpa [hrpow] using this

  have h_sub : Real.log (b : ℝ) * y ≤ (b : ℝ) ^ y - 1 := by
    linarith

  have hlog0 : 1 - (b : ℝ)⁻¹ ≤ Real.log (b : ℝ) := by
    simpa using Real.one_sub_inv_le_log_of_pos hbpos

  have hb_gt_one : (1 : ℝ) < (b : ℝ) := by
    exact_mod_cast hb
  have hb_minus_one_pos : (0 : ℝ) < (b : ℝ) - 1 := by
    linarith
  have hypos : 0 < y := by
    have hden : 0 < (n : ℝ) * ((b : ℝ) - 1) := by
      exact mul_pos hnpos hb_minus_one_pos
    have : 0 < (1 : ℝ) / ((n : ℝ) * ((b : ℝ) - 1)) := by
      exact one_div_pos.mpr hden
    simpa [y] using this

  have hlog_mul : y * (1 - (b : ℝ)⁻¹) ≤ y * Real.log (b : ℝ) := by
    exact mul_le_mul_of_nonneg_left hlog0 (le_of_lt hypos)

  have hlog_mul2 : y * (1 - (b : ℝ)⁻¹) ≤ Real.log (b : ℝ) * y := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using hlog_mul

  have hbn_inv : y * (1 - (b : ℝ)⁻¹) = ((b : ℝ) * (n : ℝ))⁻¹ := by
    have hbne : (b : ℝ) ≠ 0 := ne_of_gt hbpos
    have hnne : (n : ℝ) ≠ 0 := ne_of_gt hnpos
    have hb1ne : (b : ℝ) - 1 ≠ 0 := by
      linarith
    simp [y]
    field_simp [hbne, hnne, hb1ne]

  have hbninv_le_log : ((b : ℝ) * (n : ℝ))⁻¹ ≤ Real.log (b : ℝ) * y := by
    simpa [hbn_inv] using hlog_mul2

  have hbninv_le_gap : ((b : ℝ) * (n : ℝ))⁻¹ ≤ (b : ℝ) ^ y - 1 := by
    exact le_trans hbninv_le_log h_sub

  -- invert inequality
  have hbnpos : 0 < (b : ℝ) * (n : ℝ) := by
    exact mul_pos hbpos hnpos
  have hbninv_pos : 0 < ((b : ℝ) * (n : ℝ))⁻¹ := by
    exact inv_pos.mpr hbnpos

  have hfinal : ((b : ℝ) ^ y - 1)⁻¹ ≤ (b : ℝ) * (n : ℝ) := by
    -- inv_anti₀ : 0 < a -> a ≤ b -> b⁻¹ ≤ a⁻¹ ???
    -- Here: b = (b^y - 1), a = (b*n)⁻¹
    have := inv_anti₀ hbninv_pos hbninv_le_gap
    -- simplify ((b*n)⁻¹)⁻¹
    simpa using this

  -- finish, rewrite y
  simpa [y, mul_comm, mul_left_comm, mul_assoc] using hfinal


theorem r1_lt_pow_div (n b s : ℕ) (h1 : 1 ≤ n) (hb : 2 ≤ b) (hs : 1 ≤ s) :
  let r1 := Int.toNat <| Int.ceil <| Real.rpow b ((s : ℝ) / (n * (b - 1)) - 1)
  r1 > s → r1 < b ^ (s / (n * (b - 1))) := by
  classical
  dsimp
  intro hr1
  set d : ℕ := n * (b - 1)
  set q : ℕ := s / d
  set r : ℕ := s % d
  set t : ℝ := (s : ℝ) / d
  set a : ℝ := (b : ℝ) ^ (t - 1)

  have hb1 : (1 : ℕ) ≤ b := le_trans (by decide : (1 : ℕ) ≤ 2) hb
  have hr1_nat : (Int.ceil a).toNat > s := by
    simpa [a, t, d, Nat.cast_mul, Nat.cast_sub hb1] using hr1
  have hr1_ceil : (Nat.ceil a) > s := by
    simpa [Int.ceil_toNat] using hr1_nat
  have hs_lt_a : (s : ℝ) < a := (Nat.lt_ceil).1 hr1_ceil

  have hbn_le_s : b * n ≤ s := r1_gt_imp_bn_le_s n b s h1 hb hs hr1
  have hbn_le_s_real : (b * n : ℝ) ≤ (s : ℝ) := by
    exact_mod_cast hbn_le_s

  have hd_pos : 0 < d := by
    have hn : 0 < n := Nat.succ_le_iff.mp h1
    have hb' : 0 < b - 1 := by
      have : 1 < b := lt_of_lt_of_le (by decide : (1 : ℕ) < 2) hb
      exact Nat.sub_pos_of_lt this
    simpa [d] using Nat.mul_pos hn hb'

  have h_div_mod : d * q + r = s := by
    have h := Nat.div_add_mod s d
    simpa [q, r, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, d] using h

  have ht_decomp : t = (q : ℝ) + (r : ℝ) / d := by
    simpa [t] using real_div_eq_of_div_add_mod s d q r hd_pos h_div_mod

  set δ : ℝ := (1 : ℝ) - (r : ℝ) / d
  set c : ℝ := (b : ℝ) ^ δ

  have hδ_ge : (1 : ℝ) / d ≤ δ := by
    simpa [δ] using delta_ge_one_div_of_mod s d hd_pos

  have hb1_real : (1 : ℝ) < (b : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by decide : (1 : ℕ) < 2) hb)

  have hb_pos : 0 < (b : ℝ) := lt_trans (by norm_num : (0 : ℝ) < 1) hb1_real

  have h_one_div_d_pos : 0 < (1 : ℝ) / d := by
    have hd_real_pos : 0 < (d : ℝ) := by exact_mod_cast hd_pos
    simpa using (one_div_pos.mpr hd_real_pos)

  have hb_ge_one : (1 : ℝ) ≤ (b : ℝ) := le_of_lt hb1_real

  have hc_ge : (b : ℝ) ^ ((1 : ℝ) / d) ≤ c := by
    have := Real.rpow_le_rpow_of_exponent_le hb_ge_one hδ_ge
    simpa [c] using this

  have h_sub_le : (b : ℝ) ^ ((1 : ℝ) / d) - 1 ≤ c - 1 := sub_le_sub_right hc_ge 1

  have h_rpow1d_pos : 0 < (b : ℝ) ^ ((1 : ℝ) / d) - 1 := by
    have hpow : (1 : ℝ) < (b : ℝ) ^ ((1 : ℝ) / d) := Real.one_lt_rpow hb1_real h_one_div_d_pos
    exact sub_pos.mpr hpow

  have hinv_le : (c - 1)⁻¹ ≤ ((b : ℝ) ^ ((1 : ℝ) / d) - 1)⁻¹ := by
    have := inv_anti₀ h_rpow1d_pos h_sub_le
    simpa [c] using this

  have hbn_inv : ((b : ℝ) ^ ((1 : ℝ) / d) - 1)⁻¹ ≤ (b * n : ℝ) := by
    have hb1' : ((b - 1 : ℕ) : ℝ) = (b : ℝ) - 1 := by
      simpa using (Nat.cast_sub hb1 : ((b - 1 : ℕ) : ℝ) = (b : ℝ) - (1 : ℕ))
    simpa [d, Nat.cast_mul, hb1'] using rpow_delta_inv_le_bn n b h1 hb

  have hcinv_le_bn : (c - 1)⁻¹ ≤ (b * n : ℝ) := le_trans hinv_le hbn_inv
  have hcinv_le_s : (c - 1)⁻¹ ≤ (s : ℝ) := le_trans hcinv_le_bn hbn_le_s_real

  have ha_pos : 0 < a := Real.rpow_pos_of_pos hb_pos (t - 1)
  have ha_nonneg : 0 ≤ a := le_of_lt ha_pos

  have hδ_pos : 0 < δ := lt_of_lt_of_le h_one_div_d_pos hδ_ge

  have hc1 : (1 : ℝ) < c := by
    simpa [c] using Real.one_lt_rpow hb1_real hδ_pos

  have hca_pos : 0 < c - 1 := sub_pos.mpr hc1

  have hcinv_le_a : (c - 1)⁻¹ ≤ a := le_trans hcinv_le_s (le_of_lt hs_lt_a)

  have h_one_le_mul : (1 : ℝ) ≤ a * (c - 1) := by
    have hmul := mul_le_mul_of_nonneg_right hcinv_le_a (le_of_lt hca_pos)
    have hleft : (c - 1)⁻¹ * (c - 1) = (1 : ℝ) := by
      simpa using (inv_mul_cancel₀ (ne_of_gt hca_pos) : (c - 1)⁻¹ * (c - 1) = (1 : ℝ))
    simpa [hleft, mul_assoc] using hmul

  have ha1_le : a + 1 ≤ c * a := by
    have h' : a + 1 ≤ a + a * (c - 1) := by
      simpa [add_assoc, add_left_comm, add_comm] using add_le_add_left h_one_le_mul a
    have h'' : a + a * (c - 1) = c * a := by
      ring
    exact le_trans h' (by simpa [h''] )

  have hceil_lt : (Nat.ceil a : ℝ) < c * a := by
    have hceil : (Nat.ceil a : ℝ) < a + 1 := Nat.ceil_lt_add_one ha_nonneg
    exact lt_of_lt_of_le hceil ha1_le

  have h_exp : δ + (t - 1) = (q : ℝ) := by
    simp [δ, ht_decomp]

  have hc_mul_a : c * a = (b : ℝ) ^ (q : ℝ) := by
    have hmul : c * a = (b : ℝ) ^ (δ + (t - 1)) := by
      have h := (Real.rpow_add hb_pos δ (t - 1))
      simpa [c, a, mul_comm, mul_left_comm, mul_assoc] using h.symm
    simpa [h_exp] using hmul

  have hceil_lt_pow : (Nat.ceil a : ℝ) < (b : ℝ) ^ q := by
    have : (Nat.ceil a : ℝ) < (b : ℝ) ^ (q : ℝ) := by
      simpa [hc_mul_a] using hceil_lt
    simpa [Real.rpow_natCast] using this

  have hceil_lt_pow' : (Nat.ceil a : ℝ) < (b ^ q : ℝ) := by
    simpa [Nat.cast_pow] using hceil_lt_pow

  have hnat : Nat.ceil a < b ^ q := by
    exact_mod_cast hceil_lt_pow'

  -- final rewriting
  have : (Int.ceil a).toNat < b ^ q := by
    simpa [Int.ceil_toNat] using hnat

  -- goal is `Int.toNat (Int.ceil (Real.rpow b ((s:ℝ)/(n*(b-1)) -1))) < b^(s/(n*(b-1)))`
  --
  --
  --
  --
  --
  simpa [a, t, d, q, Nat.cast_mul, Nat.cast_sub hb1] using this

theorem r1_log_bound_of_gt (n b s : ℕ) (h1 : 1 ≤ n) (hb : 2 ≤ b) (hs : 1 ≤ s) :
  let r1 := Int.toNat <| Int.ceil <| Real.rpow b ((s : ℝ) / (n * (b - 1)) - 1)
  r1 > s → n * (b - 1) * (Nat.log b r1 + 1) ≤ s := by
  classical
  dsimp
  intro hr1_gt

  -- Abbreviate the definition of `r1`.
  set r1 : ℕ :=
      Int.toNat (Int.ceil (Real.rpow b ((s : ℝ) / (n * (b - 1)) - 1))) with hr1

  have hr1_gt' : r1 > s := by
    simpa [hr1] using hr1_gt

  -- From the auxiliary bound we get `r1 < b ^ (s / (n * (b - 1)))`.
  have hr1_lt' : r1 < b ^ (s / (n * (b - 1))) := by
    have h := r1_lt_pow_div n b s h1 hb hs
    dsimp at h
    have :
        Int.toNat (Int.ceil (Real.rpow b ((s : ℝ) / (n * (b - 1)) - 1))) <
          b ^ (s / (n * (b - 1))) :=
      h hr1_gt
    simpa [hr1] using this

  have hs0 : 0 < s := (Nat.succ_le_iff).1 hs
  have hr1_pos : 0 < r1 := lt_trans hs0 hr1_gt'
  have hr1_ne0 : r1 ≠ 0 := Nat.ne_of_gt hr1_pos

  -- Convert `r1 < b^q` into a bound on `Nat.log`.
  have hlog_lt : Nat.log b r1 < s / (n * (b - 1)) :=
    Nat.log_lt_of_lt_pow (b := b) (x := s / (n * (b - 1))) (y := r1) hr1_ne0 hr1_lt'

  have hlog_succ_le : Nat.log b r1 + 1 ≤ s / (n * (b - 1)) := by
    have : Nat.succ (Nat.log b r1) ≤ s / (n * (b - 1)) := (Nat.succ_le_iff).2 hlog_lt
    simpa [Nat.succ_eq_add_one] using this

  have hmul :
      n * (b - 1) * (Nat.log b r1 + 1) ≤
        n * (b - 1) * (s / (n * (b - 1))) :=
    Nat.mul_le_mul_left (n * (b - 1)) hlog_succ_le

  -- Show `n * (b - 1) > 0` to use the Galois connection.
  have hnpos : 0 < n := (Nat.succ_le_iff).1 h1
  have hb1 : 1 < b := (Nat.succ_le_iff).1 hb
  have hbpos : 0 < b - 1 := tsub_pos_of_lt hb1
  have hdpos : 0 < n * (b - 1) := Nat.mul_pos hnpos hbpos

  have hdiv : n * (b - 1) * (s / (n * (b - 1))) ≤ s := by
    have gc := Nat.galoisConnection_mul_div (k := n * (b - 1)) hdpos
    have : (s / (n * (b - 1))) * (n * (b - 1)) ≤ s :=
      (gc (s / (n * (b - 1))) s).2 le_rfl
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using this

  have : n * (b - 1) * (Nat.log b r1 + 1) ≤ s := le_trans hmul hdiv
  simpa [hr1] using this

theorem macro_expansion_lower (n b : ℕ) (h1 : 1 ≤ n) (hb : 2 ≤ b) :
  ∀ s : ℕ, s ≥ 1 →
    (let r1 := Int.toNat <| Int.ceil <| Real.rpow b ((s : ℝ) / (n * (b - 1)) - 1)
     Ball r1 (A n) ⊆ Ball s (MacroSet n b ∪ (A n))) := by
  intro s hs
  classical
  simp (config := { zeta := true })
  set r1 : ℕ :=
      Int.toNat (Int.ceil (Real.rpow b ((s : ℝ) / (n * (b - 1)) - 1))) with hr1
  by_cases hrs : r1 ≤ s
  ·
    have hsubset : (A n : Set (FreeAbelianMonoid n)) ⊆ MacroSet n b ∪ A n := by
      intro x hx
      exact Or.inr hx
    have h1' : Ball r1 (A n) ⊆ Ball r1 (MacroSet n b ∪ A n) :=
      ball_mono_X (R := r1) (X := (A n : Set (FreeAbelianMonoid n))) (Y := MacroSet n b ∪ A n) hsubset
    have h2' : Ball r1 (MacroSet n b ∪ A n) ⊆ Ball s (MacroSet n b ∪ A n) :=
      ball_mono_R (R := r1) (R' := s) (X := MacroSet n b ∪ A n) hrs
    exact Set.Subset.trans h1' h2'
  ·
    have hgt : r1 > s := lt_of_not_ge hrs
    have haux := r1_log_bound_of_gt (n := n) (b := b) (s := s) h1 hb hs
    have haux' :
        (Int.toNat (Int.ceil (Real.rpow b ((s : ℝ) / (n * (b - 1)) - 1)))) > s →
          n * (b - 1) *
              (Nat.log b
                    (Int.toNat (Int.ceil (Real.rpow b ((s : ℝ) / (n * (b - 1)) - 1)))) +
                      1) ≤
                s := by
      simpa using haux
    have hgt' :
        (Int.toNat (Int.ceil (Real.rpow b ((s : ℝ) / (n * (b - 1)) - 1)))) > s := by
      simpa [hr1] using hgt
    have hbound_t :
        n * (b - 1) *
            (Nat.log b
                  (Int.toNat (Int.ceil (Real.rpow b ((s : ℝ) / (n * (b - 1)) - 1)))) +
                    1) ≤
              s :=
      haux' hgt'
    have hbound : n * (b - 1) * (Nat.log b r1 + 1) ≤ s := by
      simpa [hr1] using hbound_t
    have hcomp :
        Ball r1 (A n) ⊆ Ball (n * (b - 1) * (Nat.log b r1 + 1)) (MacroSet n b ∪ A n) :=
      compression_length_bound n b r1 hb
    have hmono :
        Ball (n * (b - 1) * (Nat.log b r1 + 1)) (MacroSet n b ∪ A n) ⊆
          Ball s (MacroSet n b ∪ A n) :=
      ball_mono_R (R := n * (b - 1) * (Nat.log b r1 + 1)) (R' := s) (X := MacroSet n b ∪ A n) hbound
    exact Set.Subset.trans hcomp hmono

theorem macro_expansion_bounds (n b : ℕ) (h1 : 1 ≤ n) (hb : 2 ≤ b) :
  ∀ s : ℕ, s ≥ 1 →
    (let r1 := Int.toNat <| Int.ceil <| Real.rpow b ((s : ℝ) / (n * (b - 1)) - 1)
     (Ball r1 (A n) ⊆ Ball s (MacroSet n b ∪ (A n)))
     ∧
     let r2 := 1 + n * b * (Int.toNat <| Int.floor <| Real.rpow b ((s : ℝ) / (n * (b - 1))))
     ¬ (Ball r2 (A n) ⊆ Ball s (MacroSet n b ∪ (A n)))) := by
  intro s hs
  refine And.intro ?_ ?_
  · exact macro_expansion_lower n b h1 hb s hs
  · exact macro_expansion_upper n b h1 hb s hs


theorem theorem_1_place_notation_exponential_expansion (n b : ℕ)
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
      ¬ (Ball r2 (A n) ⊆ (Ball s (M ∪ (A n))))) := by
  classical
  dsimp
  constructor
  · exact macro_log_density n b h1 hb
  · exact macro_expansion_bounds n b h1 hb

