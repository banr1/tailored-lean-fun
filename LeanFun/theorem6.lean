import LeanFun.Definitions

import Mathlib
open abelian

def DoublyMacroSet (b : ℕ) : Set (FreeAbelianMonoid 1) :=
  { m | ∃ i : Fin 1, ∃ j : ℕ, m = Multiset.replicate (b ^ (b ^ j)) i }

theorem a1_normal_form: ∀ m : FreeAbelianMonoid 1, m = Multiset.replicate m.card (0 : Fin 1) := by
  intro m
  exact Multiset.ext.2 (by
    intro i
    fin_cases i
    simpa using (Multiset.count_eq_card.2 (by
      intro x hx
      fin_cases x
      rfl)))


def dblmacro_m (b k : ℕ) : ℕ := b ^ (b ^ k)

def dblmacro_prefix (b k : ℕ) : Set (FreeAbelianMonoid 1) :=
  { m | ∃ j : ℕ, j ≤ k ∧ m = Multiset.replicate (dblmacro_m b j) (0 : Fin 1) }

theorem dblmacro_ball_card_list (b k R N : ℕ) : Multiset.replicate N (0 : Fin 1) ∈ Ball R (dblmacro_prefix b k ∪ A 1) → ∃ l : List ℕ, l.length ≤ R ∧ (∀ x ∈ l, x = 1 ∨ ∃ j : ℕ, j ≤ k ∧ x = dblmacro_m b j) ∧ l.sum = N := by
  intro hball
  rcases hball with ⟨L, hlen, hmem, hsum⟩
  refine ⟨L.map Multiset.card, ?_, ?_, ?_⟩
  · simpa using hlen
  · intro x hx
    rcases List.mem_map.mp hx with ⟨m, hmL, rfl⟩
    have hmX := hmem m hmL
    rcases hmX with hpre | hA
    · right
      rcases (show ∃ j : ℕ, j ≤ k ∧ m = Multiset.replicate (dblmacro_m b j) (0 : Fin 1) from by
        simpa [dblmacro_prefix] using hpre) with ⟨j, hjk, hm⟩
      refine ⟨j, hjk, ?_⟩
      rw [hm]
      simp
    · left
      rcases (show ∃ i : Fin 1, m = ({i} : Multiset (Fin 1)) from by
        simpa [A] using hA) with ⟨i, hi⟩
      rw [hi]
      simp
  · calc
      (L.map Multiset.card).sum = (L.sum).card := by
        simpa using (AddMonoidHom.map_list_sum Multiset.cardHom L).symm
      _ = (Multiset.replicate N (0 : Fin 1)).card := by rw [hsum]
      _ = N := by simp

theorem dblmacro_prefix_union_subset_full (b k : ℕ) : dblmacro_prefix b k ∪ A 1 ⊆ DoublyMacroSet b ∪ A 1 := by
  intro x hx
  rcases hx with hx | hx
  · left
    rcases hx with ⟨j, hj, rfl⟩
    exact ⟨0, j, by simp [dblmacro_m]⟩
  · right
    exact hx

theorem dblmacro_small_ball_restrict_prefix (b : ℕ) (hb : 2 ≤ b) (k s N : ℕ) : N < dblmacro_m b (k + 1) → Multiset.replicate N (0 : Fin 1) ∈ Ball s (DoublyMacroSet b ∪ A 1) → Multiset.replicate N (0 : Fin 1) ∈ Ball s (dblmacro_prefix b k ∪ A 1) := by
  intro hN hBall
  rcases hBall with ⟨l, hlens, hmem, hsum⟩
  refine ⟨l, hlens, ?_, hsum⟩
  have hcardsum : (l.map Multiset.card).sum = N := by
    have hcard : Multiset.cardHom l.sum = (l.map Multiset.cardHom).sum := by
      simpa using (Multiset.cardHom.map_list_sum l)
    simpa [hsum] using hcard.symm
  have hb1 : 1 ≤ b := by
    omega
  intro x hx
  rcases hmem x hx with hxD | hxA
  · left
    rcases hxD with ⟨i, j, rfl⟩
    have hxle : dblmacro_m b j ≤ N := by
      calc
        dblmacro_m b j = (Multiset.replicate (dblmacro_m b j) i).card := by simp [dblmacro_m]
        _ ≤ (l.map Multiset.card).sum := by
          exact List.le_sum_of_mem (by
            exact List.mem_map.2 ⟨Multiset.replicate (dblmacro_m b j) i, hx, by simp [dblmacro_m]⟩)
        _ = N := hcardsum
    have hjle : j ≤ k := by
      by_contra hjle
      have hkj : k + 1 ≤ j := by
        omega
      have hinner : b ^ (k + 1) ≤ b ^ j := by
        exact pow_le_pow_right' hb1 hkj
      have houter : b ^ (b ^ (k + 1)) ≤ b ^ (b ^ j) := by
        exact pow_le_pow_right' hb1 hinner
      have : dblmacro_m b (k + 1) ≤ dblmacro_m b j := by
        simpa [dblmacro_m] using houter
      exact (not_lt_of_ge (le_trans this hxle)) hN
    refine ⟨j, hjle, ?_⟩
    have hi0 : i = (0 : Fin 1) := Subsingleton.elim _ _
    simpa [dblmacro_m, hi0]
  · right
    exact hxA

def dblmacro_step (b k : ℕ) : ℕ := b ^ (b ^ k * (b - 1))

def dblmacro_T (b : ℕ) : ℕ → ℕ
  | 0 => b - 1
  | k + 1 => (dblmacro_step b k - 1) + dblmacro_T b k

theorem dblmacro_T_growth (b : ℕ) (hb : 2 ≤ b) : ∀ k : ℕ, 1 ≤ k → dblmacro_step b (k - 1) ≤ dblmacro_T b k + 1 ∧ dblmacro_T b k + 1 ≤ 2 * dblmacro_step b (k - 1) := by
  have hgrow : ∀ n : ℕ, 2 * dblmacro_step b n ≤ dblmacro_step b (n + 1) := by
    intro n
    have hb1 : 1 < b := by omega
    have hbpos : 0 < b := by omega
    have he : 1 ≤ b ^ n * (b - 1) := by
      exact one_le_mul (Nat.one_le_pow _ _ hbpos) (by omega)
    calc
      2 * dblmacro_step b n ≤ b * dblmacro_step b n := by
        exact Nat.mul_le_mul_right _ hb
      _ = b ^ (b ^ n * (b - 1) + 1) := by
        rw [dblmacro_step]
        symm
        rw [pow_succ, Nat.mul_comm]
      _ ≤ b ^ ((b ^ n * (b - 1)) * b) := by
        exact Nat.pow_le_pow_of_le hb1 (by
          have h1 : b ^ n * (b - 1) + 1 ≤ (b ^ n * (b - 1)) * 2 := by
            omega
          have h2 : (b ^ n * (b - 1)) * 2 ≤ (b ^ n * (b - 1)) * b := by
            exact Nat.mul_le_mul_left (b ^ n * (b - 1)) hb
          exact le_trans h1 h2)
      _ = dblmacro_step b (n + 1) := by
        rw [dblmacro_step, pow_succ]
        congr 1
        ac_rfl
  have hmain : ∀ n : ℕ,
      dblmacro_step b n ≤ dblmacro_T b (n + 1) + 1 ∧
      dblmacro_T b (n + 1) + 1 ≤ 2 * dblmacro_step b n := by
    intro n
    induction n with
    | zero =>
        constructor
        · rw [dblmacro_T, dblmacro_T]
          have hspos : 0 < dblmacro_step b 0 := by
            rw [dblmacro_step]
            positivity
          omega
        · rw [dblmacro_T, dblmacro_T]
          have hb1 : 1 < b := by omega
          have hble : b - 1 ≤ dblmacro_step b 0 := by
            have hpow : b ^ 1 ≤ b ^ (b - 1) := by
              exact Nat.pow_le_pow_of_le hb1 (by omega)
            exact le_trans (Nat.sub_le _ _) (by simpa [dblmacro_step] using hpow)
          have hspos : 0 < dblmacro_step b 0 := by
            rw [dblmacro_step]
            positivity
          omega
    | succ n ih =>
        rcases ih with ⟨ih1, ih2⟩
        constructor
        · rw [dblmacro_T]
          have hspos : 0 < dblmacro_step b (n + 1) := by
            rw [dblmacro_step]
            positivity
          omega
        · rw [dblmacro_T]
          have hspos : 0 < dblmacro_step b (n + 1) := by
            rw [dblmacro_step]
            positivity
          have htail : dblmacro_T b (n + 1) + 1 ≤ dblmacro_step b (n + 1) := by
            exact le_trans ih2 (hgrow n)
          omega
  intro k hk
  cases k with
  | zero => cases hk
  | succ n =>
      simpa using hmain n

theorem dblmacro_T_interval (b : ℕ) (hb : 2 ≤ b) (s : ℕ) : b - 1 ≤ s → ∃ k : ℕ, dblmacro_T b k ≤ s ∧ s < dblmacro_T b (k + 1) := by
  intro hs
  let P : ℕ → Prop := fun k => dblmacro_T b k ≤ s
  have hP0 : P 0 := by
    simpa [P, dblmacro_T] using hs
  have hstep_ge_two : ∀ k : ℕ, 2 ≤ dblmacro_step b k := by
    intro k
    unfold dblmacro_step
    have hbpos : 0 < b := by omega
    have hbm1 : 0 < b - 1 := by omega
    have hpowpos : 0 < b ^ k := Nat.pow_pos hbpos
    have hexp : 0 < b ^ k * (b - 1) := Nat.mul_pos hpowpos hbm1
    exact le_trans hb (Nat.le_pow hexp)
  have hstep_ge_one : ∀ k : ℕ, 1 ≤ dblmacro_step b k - 1 := by
    intro k
    have h2 := hstep_ge_two k
    omega
  have hT_lower : ∀ k : ℕ, k + (b - 1) ≤ dblmacro_T b k := by
    intro k
    induction k with
    | zero =>
        simp [dblmacro_T]
    | succ k ih =>
        have h1 := hstep_ge_one k
        simp [dblmacro_T]
        omega
  have hPs1 : ¬ P (s + 1) := by
    have hlower := hT_lower (s + 1)
    change ¬ dblmacro_T b (s + 1) ≤ s
    omega
  let k := Nat.findGreatest P (s + 1)
  have hk_left : dblmacro_T b k ≤ s := by
    have hfg := Nat.findGreatest_spec (P := P) (m := 0) (n := s + 1) (Nat.zero_le _) hP0
    simpa [k, P] using hfg
  have hk_le_s : k ≤ s := by
    dsimp [k]
    rw [Nat.findGreatest_of_not hPs1]
    exact Nat.findGreatest_le s
  have hk_right : s < dblmacro_T b (k + 1) := by
    have hk1_not : ¬ P (k + 1) := by
      have hk_le_s' : Nat.findGreatest P (s + 1) ≤ s := by
        simpa [k] using hk_le_s
      change ¬ P (Nat.findGreatest P (s + 1) + 1)
      exact Nat.findGreatest_is_greatest (P := P) (n := s + 1)
        (k := Nat.findGreatest P (s + 1) + 1) (Nat.lt_succ_self _) (Nat.succ_le_succ hk_le_s')
    change ¬ dblmacro_T b (k + 1) ≤ s at hk1_not
    exact lt_of_not_ge hk1_not
  exact ⟨k, hk_left, hk_right⟩

theorem dblmacro_cover_below_mk (b : ℕ) (hb : 2 ≤ b) : ∀ k x, x < dblmacro_m b k → Multiset.replicate x (0 : Fin 1) ∈ Ball (dblmacro_T b k) (dblmacro_prefix b k ∪ A 1) := by
  intro k
  induction k with
  | zero =>
      intro x hx
      refine ⟨List.replicate x ({(0 : Fin 1)}), ?_, ?_, ?_⟩
      · have hx' : x < b := by simpa [dblmacro_m] using hx
        simpa [dblmacro_T] using Nat.le_pred_of_lt hx'
      · intro m hm
        rcases List.mem_replicate.mp hm with ⟨_, rfl⟩
        exact Or.inr (by simp [A])
      · simpa [List.sum_replicate, Multiset.nsmul_singleton]
  | succ k ih =>
      intro x hx
      let q : ℕ := x / dblmacro_m b k
      let r : ℕ := x % dblmacro_m b k
      let block : FreeAbelianMonoid 1 := Multiset.replicate (dblmacro_m b k) (0 : Fin 1)
      have hbpos : 0 < b := lt_of_lt_of_le (by decide : 0 < 2) hb
      have hmpos : 0 < dblmacro_m b k := by
        simpa [dblmacro_m] using (Nat.pow_pos (n := b ^ k) hbpos)
      have hr_lt : r < dblmacro_m b k := by
        dsimp [r]
        exact Nat.mod_lt _ hmpos
      have hrBall : Multiset.replicate r (0 : Fin 1) ∈ Ball (dblmacro_T b k) (dblmacro_prefix b k ∪ A 1) :=
        ih r hr_lt
      have hexp : b ^ (k + 1) = b ^ k * (b - 1) + b ^ k := by
        have hb1 : 1 ≤ b := le_trans (by decide : 1 ≤ 2) hb
        calc
          b ^ (k + 1) = b ^ k * b := by rw [Nat.pow_succ]
          _ = b ^ k * ((b - 1) + 1) := by rw [Nat.sub_add_cancel hb1]
          _ = b ^ k * (b - 1) + b ^ k * 1 := by rw [Nat.mul_add]
          _ = b ^ k * (b - 1) + b ^ k := by simp
      have hm_succ : dblmacro_m b (k + 1) = dblmacro_step b k * dblmacro_m b k := by
        calc
          dblmacro_m b (k + 1) = b ^ (b ^ k * (b - 1) + b ^ k) := by
            simp [dblmacro_m, hexp]
          _ = b ^ (b ^ k * (b - 1)) * b ^ (b ^ k) := by rw [Nat.pow_add]
          _ = dblmacro_step b k * dblmacro_m b k := by
            simp [dblmacro_step, dblmacro_m]
      have hq_lt : q < dblmacro_step b k := by
        dsimp [q]
        exact (Nat.div_lt_iff_lt_mul hmpos).2 (by simpa [hm_succ, Nat.mul_comm] using hx)
      rcases hrBall with ⟨lr, hlr_len, hlr_mem, hlr_sum⟩
      refine ⟨List.replicate q block ++ lr, ?_, ?_, ?_⟩
      · have hq_le : q ≤ dblmacro_step b k - 1 := by
          omega
        have hlen : q + lr.length ≤ (dblmacro_step b k - 1) + dblmacro_T b k := Nat.add_le_add hq_le hlr_len
        simpa [dblmacro_T, List.length_append] using hlen
      · intro m hm
        rcases List.mem_append.mp hm with hm | hm
        · rcases List.mem_replicate.mp hm with ⟨_, rfl⟩
          exact Or.inl ⟨k, Nat.le_succ k, rfl⟩
        · rcases hlr_mem m hm with hm | hm
          · rcases hm with ⟨j, hj, rfl⟩
            exact Or.inl ⟨j, le_trans hj (Nat.le_succ k), rfl⟩
          · exact Or.inr hm
      · have hsum_blocks : (List.replicate q block).sum = Multiset.replicate (q * dblmacro_m b k) (0 : Fin 1) := by
          simp [block, List.sum_replicate, Multiset.nsmul_replicate]
        have hqre : q * dblmacro_m b k + r = x := by
          simpa [q, r] using (Nat.div_add_mod' x (dblmacro_m b k))
        calc
          (List.replicate q block ++ lr).sum = (List.replicate q block).sum + lr.sum := by
            simpa using List.sum_append (List.replicate q block) lr
          _ = Multiset.replicate (q * dblmacro_m b k) (0 : Fin 1) + Multiset.replicate r (0 : Fin 1) := by
            rw [hsum_blocks, hlr_sum]
          _ = Multiset.replicate (q * dblmacro_m b k + r) (0 : Fin 1) := by
            rw [← Multiset.replicate_add]
          _ = Multiset.replicate x (0 : Fin 1) := by rw [hqre]

theorem dblmacro_m_succ (b : ℕ) (hb : 2 ≤ b) (k : ℕ) : dblmacro_m b (k + 1) = dblmacro_step b k * dblmacro_m b k := by
  have hb1 : 1 ≤ b := le_trans (by decide : 1 ≤ 2) hb
  calc
    dblmacro_m b (k + 1) = b ^ (b ^ k * b) := by
      simp [dblmacro_m, Nat.pow_succ]
    _ = b ^ (b ^ k * ((b - 1) + 1)) := by
      rw [Nat.sub_add_cancel hb1]
    _ = b ^ (b ^ k * (b - 1) + b ^ k * 1) := by
      rw [Nat.mul_add]
    _ = b ^ (b ^ k * (b - 1) + b ^ k) := by
      simp
    _ = b ^ (b ^ k * (b - 1)) * b ^ (b ^ k) := by
      rw [Nat.pow_add]
    _ = dblmacro_step b k * dblmacro_m b k := by
      rfl

theorem dblmacro_step_eq_pow (b k : ℕ) : dblmacro_step b k = dblmacro_m b k ^ (b - 1) := by
  simpa [dblmacro_step, dblmacro_m] using (Nat.pow_mul b (b ^ k) (b - 1))

theorem dblmacro_step_rpow_inv_eq_m (b : ℕ) (hb : 2 ≤ b) (k : ℕ) : ((dblmacro_step b k : ℝ) ^ ((b - 1 : ℝ)⁻¹)) = dblmacro_m b k := by
  have hne : (b - 1 : ℕ) ≠ 0 := by
    omega
  have h1 : 1 ≤ b := by
    omega
  have hm_nonneg : 0 ≤ (dblmacro_m b k : ℝ) := by
    exact_mod_cast (Nat.zero_le (dblmacro_m b k))
  rw [dblmacro_step_eq_pow, Nat.cast_pow]
  have hcast : ((b - 1 : ℕ) : ℝ) = (b : ℝ) - 1 := by
    norm_num [Nat.cast_sub h1]
  rw [show ((b : ℝ) - 1)⁻¹ = (((b - 1 : ℕ) : ℝ))⁻¹ by rw [hcast]
    ]
  simpa using Real.pow_rpow_inv_natCast hm_nonneg hne

theorem dblmacro_step_root_mul_eq_m_succ (b : ℕ) (hb : 2 ≤ b) (k : ℕ) : ((dblmacro_step b k : ℝ) ^ ((b - 1 : ℝ)⁻¹)) * dblmacro_step b k = dblmacro_m b (k + 1) := by
  rw [dblmacro_step_rpow_inv_eq_m b hb k, mul_comm]
  exact_mod_cast (dblmacro_m_succ b hb k).symm

theorem dblmacro_step_rpow_alpha_eq_m_succ (b : ℕ) (hb : 2 ≤ b) (k : ℕ) : ((dblmacro_step b k : ℝ) ^ ((b : ℝ) / (b - 1))) = dblmacro_m b (k + 1) := by
  have hb0 : 0 < b := lt_of_lt_of_le (by norm_num) hb
  have hstep_pos_nat : 0 < dblmacro_step b k := by
    dsimp [dblmacro_step]
    exact pow_pos hb0 _
  have hstep_pos : 0 < (dblmacro_step b k : ℝ) := by
    exact_mod_cast hstep_pos_nat
  have hb_real : (1 : ℝ) < b := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num) hb)
  have hden_ne : (b : ℝ) - 1 ≠ 0 := by
    linarith
  have hexp : (b : ℝ) / (b - 1) = ((b - 1 : ℝ)⁻¹) + 1 := by
    field_simp [hden_ne]
    ring
  calc
    ((dblmacro_step b k : ℝ) ^ ((b : ℝ) / (b - 1))) = (dblmacro_step b k : ℝ) ^ (((b - 1 : ℝ)⁻¹) + 1) := by
      rw [hexp]
    _ = ((dblmacro_step b k : ℝ) ^ ((b - 1 : ℝ)⁻¹)) * dblmacro_step b k := by
      simpa [Real.rpow_one] using (Real.rpow_add hstep_pos ((b - 1 : ℝ)⁻¹) (1 : ℝ))
    _ = dblmacro_m b (k + 1) := dblmacro_step_root_mul_eq_m_succ b hb k

def dblmacro_witness (b k q : ℕ) : ℕ := q * dblmacro_m b k + (dblmacro_m b k - 1)

theorem dblmacro_hard_prefix (b : ℕ) (hb : 2 ≤ b) : ∀ k q, Multiset.replicate (dblmacro_witness b k q) (0 : Fin 1) ∉ Ball (q + dblmacro_T b k - 1) (dblmacro_prefix b k ∪ A 1) := by
  have hb1 : 1 ≤ b := le_trans (by decide : (1 : ℕ) ≤ 2) hb
  have hbpos : 0 < b := lt_of_lt_of_le (by decide : (0 : ℕ) < 2) hb
  have m_pos : ∀ j : ℕ, 0 < dblmacro_m b j := by
    intro j
    dsimp [dblmacro_m]
    exact Nat.pow_pos hbpos
  have m_one_le : ∀ j : ℕ, 1 ≤ dblmacro_m b j := by
    intro j
    exact Nat.succ_le_of_lt (m_pos j)
  have step_pos : ∀ j : ℕ, 0 < dblmacro_step b j := by
    intro j
    dsimp [dblmacro_step]
    exact Nat.pow_pos hbpos
  have step_one_le : ∀ j : ℕ, 1 ≤ dblmacro_step b j := by
    intro j
    exact Nat.succ_le_of_lt (step_pos j)
  have T_pos : ∀ j : ℕ, 0 < dblmacro_T b j := by
    intro j
    induction j with
    | zero =>
        simpa [dblmacro_T] using Nat.sub_pos_of_lt (lt_of_lt_of_le (by decide : (1 : ℕ) < 2) hb)
    | succ j ih =>
        simpa [dblmacro_T] using Nat.add_pos_right (dblmacro_step b j - 1) ih
  have add_mul_sub_one (A m : ℕ) (hm : 1 ≤ m) :
      A * m + (m - 1) = (A + 1) * m - 1 := by
    calc
      A * m + (m - 1) = A * m + m - 1 := by
        simpa [Nat.add_assoc] using (Nat.add_sub_assoc hm (A * m)).symm
      _ = (A + 1) * m - 1 := by
        ring_nf
  have sub_one_mul_add (A m : ℕ) (hA : 1 ≤ A) (hm : 1 ≤ m) :
      (A - 1) * m + (m - 1) = A * m - 1 := by
    calc
      (A - 1) * m + (m - 1) = (A - 1) * m + m - 1 := by
        simpa [Nat.add_assoc] using (Nat.add_sub_assoc hm ((A - 1) * m)).symm
      _ = m + (A * m - m) - 1 := by
        rw [tsub_one_mul]
        ring_nf
      _ = A * m - 1 := by
        have hmul : m ≤ A * m := by
          simpa [one_mul] using (Nat.mul_le_mul_right m hA)
        have hcancel : m + (A * m - m) = A * m := by
          simpa [Nat.add_comm] using (Nat.sub_add_cancel hmul)
        simpa [hcancel]
  have m_succ (j : ℕ) : dblmacro_m b (j + 1) = dblmacro_step b j * dblmacro_m b j := by
    calc
      dblmacro_m b (j + 1) = b ^ (b ^ j * b) := by
        simp [dblmacro_m, Nat.pow_succ]
      _ = b ^ (b ^ j * ((b - 1) + 1)) := by
        rw [Nat.sub_add_cancel hb1]
      _ = b ^ (b ^ j * (b - 1) + b ^ j * 1) := by rw [Nat.mul_add]
      _ = b ^ (b ^ j * (b - 1) + b ^ j) := by simp
      _ = b ^ (b ^ j * (b - 1)) * b ^ (b ^ j) := by rw [Nat.pow_add]
      _ = dblmacro_step b j * dblmacro_m b j := by rfl
  have witness_succ_eq (j d : ℕ) :
      dblmacro_witness b (j + 1) d = dblmacro_witness b j (((d + 1) * dblmacro_step b j) - 1) := by
    calc
      dblmacro_witness b (j + 1) d = (d + 1) * dblmacro_m b (j + 1) - 1 := by
        simpa [dblmacro_witness] using add_mul_sub_one d (dblmacro_m b (j + 1)) (m_one_le (j + 1))
      _ = ((d + 1) * dblmacro_step b j) * dblmacro_m b j - 1 := by
        rw [m_succ]
        ring_nf
      _ = dblmacro_witness b j (((d + 1) * dblmacro_step b j) - 1) := by
        symm
        simpa [dblmacro_witness] using
          sub_one_mul_add (((d + 1) * dblmacro_step b j)) (dblmacro_m b j)
            (by
              have h1 : 1 ≤ d + 1 := Nat.succ_le_succ (Nat.zero_le d)
              have hmul : dblmacro_step b j ≤ (d + 1) * dblmacro_step b j := by
                simpa [one_mul] using Nat.mul_le_mul_right (dblmacro_step b j) h1
              exact le_trans (step_one_le j) hmul)
            (m_one_le j)
  have hmain :
      ∀ k q (l : List ℕ),
        (∀ x ∈ l, x = 1 ∨ ∃ j : ℕ, j ≤ k ∧ x = dblmacro_m b j) →
        l.sum = dblmacro_witness b k q →
        q + dblmacro_T b k ≤ l.length := by
    intro k
    induction k with
    | zero =>
        intro q l hl hsum
        let top : List ℕ := l.filter (fun x => x = dblmacro_m b 0)
        let rest : List ℕ := l.filter (fun x => x ≠ dblmacro_m b 0)
        let c : ℕ := top.length
        have hsum_split : top.sum + rest.sum = l.sum := by
          simpa [top, rest] using
            (List.sum_map_filter_add_sum_map_filter_not (p := fun x : ℕ => x = dblmacro_m b 0)
              (f := fun x : ℕ => x) l)
        have htop_const : ∀ x ∈ top, x = dblmacro_m b 0 := by
          intro x hx
          have hx' : x ∈ l.filter (fun y => y = dblmacro_m b 0) := by
            simpa [top] using hx
          have hxpred : decide (x = dblmacro_m b 0) = true := (List.mem_filter.1 hx').2
          exact decide_eq_true_eq.mp hxpred
        have htop_sum : top.sum = c * dblmacro_m b 0 := by
          have := List.sum_eq_card_nsmul top (dblmacro_m b 0) htop_const
          simpa [c, Nat.nsmul_eq_mul] using this
        have hrest_one : ∀ x ∈ rest, x = 1 := by
          intro x hx
          have hx' : x ∈ l.filter (fun y => y ≠ dblmacro_m b 0) := by
            simpa [rest] using hx
          have hxL : x ∈ l := (List.mem_filter.1 hx').1
          have hxpred : decide (x ≠ dblmacro_m b 0) = true := (List.mem_filter.1 hx').2
          have hxne : x ≠ dblmacro_m b 0 := decide_eq_true_eq.mp hxpred
          have hxmem := hl x hxL
          rcases hxmem with rfl | hxmem
          · rfl
          · rcases hxmem with ⟨j, hj, hxj⟩
            have hj0 : j = 0 := by omega
            subst hj0
            exact (hxne hxj).elim
        have hrest_sum : rest.sum = rest.length := by
          have := List.sum_eq_card_nsmul rest 1 hrest_one
          simpa using this
        have hlen : l.length = c + rest.length := by
          simpa [top, rest, c] using
            (List.length_eq_length_filter_add (l := l) (f := fun x : ℕ => decide (x = dblmacro_m b 0)))
        have htotal : c * dblmacro_m b 0 + rest.sum = q * dblmacro_m b 0 + (dblmacro_m b 0 - 1) := by
          calc
            c * dblmacro_m b 0 + rest.sum = top.sum + rest.sum := by simp [htop_sum]
            _ = l.sum := hsum_split
            _ = q * dblmacro_m b 0 + (dblmacro_m b 0 - 1) := by simpa [dblmacro_witness] using hsum
        have hc_le : c ≤ q := by
          have hcle : c * dblmacro_m b 0 ≤ q * dblmacro_m b 0 + (dblmacro_m b 0 - 1) := by
            have : c * dblmacro_m b 0 ≤ c * dblmacro_m b 0 + rest.sum := Nat.le_add_right _ _
            rw [htotal] at this
            exact this
          have hlt : q * dblmacro_m b 0 + (dblmacro_m b 0 - 1) < (q + 1) * dblmacro_m b 0 := by
            rw [add_mul_sub_one q (dblmacro_m b 0) (m_one_le 0)]
            exact Nat.sub_lt (Nat.mul_pos (Nat.succ_pos q) (m_pos 0)) (by decide)
          by_contra hc
          have hq1 : q + 1 ≤ c := Nat.succ_le_of_lt (Nat.lt_of_not_ge hc)
          have hmul : (q + 1) * dblmacro_m b 0 ≤ c * dblmacro_m b 0 :=
            Nat.mul_le_mul_right (dblmacro_m b 0) hq1
          have : (q + 1) * dblmacro_m b 0 ≤ q * dblmacro_m b 0 + (dblmacro_m b 0 - 1) :=
            le_trans hmul hcle
          exact (Nat.not_le_of_gt hlt) this
        let d : ℕ := q - c
        have hq : q = c + d := by
          have hq' : q - c + c = q := Nat.sub_add_cancel hc_le
          have : d + c = q := by simpa [d] using hq'
          simpa [Nat.add_comm] using this.symm
        have hrest_eq : rest.sum = d * dblmacro_m b 0 + (dblmacro_m b 0 - 1) := by
          have htmp : c * dblmacro_m b 0 + rest.sum = c * dblmacro_m b 0 + (d * dblmacro_m b 0 + (dblmacro_m b 0 - 1)) := by
            calc
              c * dblmacro_m b 0 + rest.sum = q * dblmacro_m b 0 + (dblmacro_m b 0 - 1) := htotal
              _ = (c + d) * dblmacro_m b 0 + (dblmacro_m b 0 - 1) := by simpa [hq]
              _ = c * dblmacro_m b 0 + (d * dblmacro_m b 0 + (dblmacro_m b 0 - 1)) := by
                  simp [Nat.add_mul, Nat.mul_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
          exact Nat.add_left_cancel htmp
        have hrest_len_eq : rest.length = d * dblmacro_m b 0 + (dblmacro_m b 0 - 1) := by
          simpa [hrest_sum] using hrest_eq
        have hd_mul : d ≤ d * dblmacro_m b 0 := by
          simpa [one_mul] using Nat.mul_le_mul_left d (m_one_le 0)
        have hbase_le : q + dblmacro_T b 0 ≤ c + rest.length := by
          have htmp0 : d + (dblmacro_m b 0 - 1) ≤ d * dblmacro_m b 0 + (dblmacro_m b 0 - 1) := by
            exact Nat.add_le_add_right hd_mul (dblmacro_m b 0 - 1)
          have htmp : c + (d + (dblmacro_m b 0 - 1)) ≤ c + rest.length := by
            rw [hrest_len_eq]
            exact Nat.add_le_add_left htmp0 c
          simpa [hq, dblmacro_T, dblmacro_m, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm, pow_zero] using htmp
        have : q + dblmacro_T b 0 ≤ l.length := by
          rw [hlen]
          exact hbase_le
        simpa using this
    | succ k ih =>
        intro q l hl hsum
        let top : List ℕ := l.filter (fun x => x = dblmacro_m b (k + 1))
        let rest : List ℕ := l.filter (fun x => x ≠ dblmacro_m b (k + 1))
        let c : ℕ := top.length
        have hsum_split : top.sum + rest.sum = l.sum := by
          simpa [top, rest] using
            (List.sum_map_filter_add_sum_map_filter_not (p := fun x : ℕ => x = dblmacro_m b (k + 1))
              (f := fun x : ℕ => x) l)
        have htop_const : ∀ x ∈ top, x = dblmacro_m b (k + 1) := by
          intro x hx
          have hx' : x ∈ l.filter (fun y => y = dblmacro_m b (k + 1)) := by
            simpa [top] using hx
          have hxpred : decide (x = dblmacro_m b (k + 1)) = true := (List.mem_filter.1 hx').2
          exact decide_eq_true_eq.mp hxpred
        have htop_sum : top.sum = c * dblmacro_m b (k + 1) := by
          have := List.sum_eq_card_nsmul top (dblmacro_m b (k + 1)) htop_const
          simpa [c, Nat.nsmul_eq_mul] using this
        have hrest_prop : ∀ x ∈ rest, x = 1 ∨ ∃ j : ℕ, j ≤ k ∧ x = dblmacro_m b j := by
          intro x hx
          have hx' : x ∈ l.filter (fun y => y ≠ dblmacro_m b (k + 1)) := by
            simpa [rest] using hx
          have hxL : x ∈ l := (List.mem_filter.1 hx').1
          have hxpred : decide (x ≠ dblmacro_m b (k + 1)) = true := (List.mem_filter.1 hx').2
          have hxne : x ≠ dblmacro_m b (k + 1) := decide_eq_true_eq.mp hxpred
          have hxmem := hl x hxL
          rcases hxmem with hx1 | ⟨j, hj, hxj⟩
          · exact Or.inl hx1
          · rcases Nat.eq_or_lt_of_le hj with rfl | hjlt
            · exfalso
              exact hxne hxj
            · exact Or.inr ⟨j, Nat.le_of_lt_succ hjlt, hxj⟩
        have hlen : l.length = c + rest.length := by
          simpa [top, rest, c] using
            (List.length_eq_length_filter_add (l := l) (f := fun x : ℕ => decide (x = dblmacro_m b (k + 1))))
        have htotal : c * dblmacro_m b (k + 1) + rest.sum = q * dblmacro_m b (k + 1) + (dblmacro_m b (k + 1) - 1) := by
          calc
            c * dblmacro_m b (k + 1) + rest.sum = top.sum + rest.sum := by simp [htop_sum]
            _ = l.sum := hsum_split
            _ = q * dblmacro_m b (k + 1) + (dblmacro_m b (k + 1) - 1) := by
                simpa [dblmacro_witness] using hsum
        have hc_le : c ≤ q := by
          have hcle : c * dblmacro_m b (k + 1) ≤ q * dblmacro_m b (k + 1) + (dblmacro_m b (k + 1) - 1) := by
            have : c * dblmacro_m b (k + 1) ≤ c * dblmacro_m b (k + 1) + rest.sum := Nat.le_add_right _ _
            rw [htotal] at this
            exact this
          have hlt : q * dblmacro_m b (k + 1) + (dblmacro_m b (k + 1) - 1) < (q + 1) * dblmacro_m b (k + 1) := by
            rw [add_mul_sub_one q (dblmacro_m b (k + 1)) (m_one_le (k + 1))]
            exact Nat.sub_lt (Nat.mul_pos (Nat.succ_pos q) (m_pos (k + 1))) (by decide)
          by_contra hc
          have hq1 : q + 1 ≤ c := Nat.succ_le_of_lt (Nat.lt_of_not_ge hc)
          have hmul : (q + 1) * dblmacro_m b (k + 1) ≤ c * dblmacro_m b (k + 1) :=
            Nat.mul_le_mul_right (dblmacro_m b (k + 1)) hq1
          have : (q + 1) * dblmacro_m b (k + 1) ≤ q * dblmacro_m b (k + 1) + (dblmacro_m b (k + 1) - 1) :=
            le_trans hmul hcle
          exact (Nat.not_le_of_gt hlt) this
        let d : ℕ := q - c
        have hq : q = c + d := by
          have hq' : q - c + c = q := Nat.sub_add_cancel hc_le
          have : d + c = q := by simpa [d] using hq'
          simpa [Nat.add_comm] using this.symm
        have hrest_sum : rest.sum = dblmacro_witness b (k + 1) d := by
          have htmp : c * dblmacro_m b (k + 1) + rest.sum = c * dblmacro_m b (k + 1) + dblmacro_witness b (k + 1) d := by
            calc
              c * dblmacro_m b (k + 1) + rest.sum = q * dblmacro_m b (k + 1) + (dblmacro_m b (k + 1) - 1) := htotal
              _ = (c + d) * dblmacro_m b (k + 1) + (dblmacro_m b (k + 1) - 1) := by simpa [hq]
              _ = c * dblmacro_m b (k + 1) + (d * dblmacro_m b (k + 1) + (dblmacro_m b (k + 1) - 1)) := by
                  simp [Nat.add_mul, Nat.mul_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
              _ = c * dblmacro_m b (k + 1) + dblmacro_witness b (k + 1) d := by
                  simp [dblmacro_witness]
          exact Nat.add_left_cancel htmp
        have hrest_sum' : rest.sum = dblmacro_witness b k (((d + 1) * dblmacro_step b k) - 1) := by
          simpa [witness_succ_eq] using hrest_sum
        have hrest_len : (((d + 1) * dblmacro_step b k) - 1) + dblmacro_T b k ≤ rest.length := by
          exact ih (((d + 1) * dblmacro_step b k) - 1) rest hrest_prop hrest_sum'
        have hd_mul : d ≤ d * dblmacro_step b k := by
          simpa [one_mul] using Nat.mul_le_mul_left d (step_one_le k)
        have hstep_le : d + (dblmacro_step b k - 1) ≤ ((d + 1) * dblmacro_step b k) - 1 := by
          have htmp : d + (dblmacro_step b k - 1) ≤ d * dblmacro_step b k + (dblmacro_step b k - 1) := by
            exact Nat.add_le_add_right hd_mul (dblmacro_step b k - 1)
          calc
            d + (dblmacro_step b k - 1) ≤ d * dblmacro_step b k + (dblmacro_step b k - 1) := htmp
            _ = (d + 1) * dblmacro_step b k - 1 := by
                simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
                  add_mul_sub_one d (dblmacro_step b k) (step_one_le k)
        have hgoal : q + dblmacro_T b (k + 1) ≤ c + rest.length := by
          have htmp : c + (d + (dblmacro_step b k - 1) + dblmacro_T b k) ≤
              c + ((((d + 1) * dblmacro_step b k) - 1) + dblmacro_T b k) := by
            exact Nat.add_le_add_left (Nat.add_le_add_right hstep_le (dblmacro_T b k)) c
          have htmp' : c + (d + (dblmacro_step b k - 1) + dblmacro_T b k) ≤ c + rest.length := by
            exact le_trans htmp (Nat.add_le_add_left hrest_len c)
          simpa [hq, dblmacro_T, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using htmp'
        have : q + dblmacro_T b (k + 1) ≤ l.length := by
          rw [hlen]
          exact hgoal
        simpa using this
  intro k q hBall
  rcases hBall with ⟨l, hlR, hl_mem, hl_sum⟩
  have hprop : ∀ x ∈ l.map Multiset.card, x = 1 ∨ ∃ j : ℕ, j ≤ k ∧ x = dblmacro_m b j := by
    intro x hx
    rcases List.mem_map.1 hx with ⟨m, hm, rfl⟩
    have hmX : m ∈ dblmacro_prefix b k ∪ A 1 := hl_mem m hm
    rcases hmX with hmP | hmA
    · rcases hmP with ⟨j, hj, rfl⟩
      right
      refine ⟨j, hj, ?_⟩
      simp
    · rcases (by simpa [A] using hmA) with ⟨i, rfl⟩
      left
      simp
  have hsum_cards : (l.map Multiset.card).sum = dblmacro_witness b k q := by
    calc
      (l.map Multiset.card).sum = Multiset.card l.sum := by
        simpa using (Multiset.cardHom.map_list_sum l).symm
      _ = dblmacro_witness b k q := by
        simpa [hl_sum]
  have hlen_cards : q + dblmacro_T b k ≤ (l.map Multiset.card).length := hmain k q (l.map Multiset.card) hprop hsum_cards
  have hlen_cards' : q + dblmacro_T b k ≤ l.length := by
    simpa using hlen_cards
  have hbad : q + dblmacro_T b k - 1 < q + dblmacro_T b k :=
    Nat.sub_lt (Nat.add_pos_right q (T_pos k)) (by decide)
  exact (Nat.not_le_of_gt hbad) (le_trans hlen_cards' hlR)

theorem dblmacro_interval_lower_real_base (b : ℕ) (hb : 2 ≤ b) : ∃ C0 : ℝ, 0 < C0 ∧ ∀ {s : ℕ}, dblmacro_T b 0 ≤ s → s < dblmacro_T b 1 → C0 * Real.rpow s ((b : ℝ) / (b - 1)) ≤ (dblmacro_witness b 0 (s - dblmacro_T b 0) : ℝ) := by
  have hb0 : 0 < b := by
    omega
  have hb1 : 1 ≤ b := by
    omega
  have hstep_nat_pos : 0 < dblmacro_step b 0 := by
    unfold dblmacro_step
    exact Nat.pow_pos hb0
  have hM_nat_pos : 0 < 2 * dblmacro_step b 0 := by
    exact Nat.mul_pos (by decide) hstep_nat_pos
  have hbsub_pos : 0 < (b : ℝ) - 1 := by
    have hb_real : (2 : ℝ) ≤ b := by
      exact_mod_cast hb
    linarith
  let α : ℝ := (((b : ℝ) - 1)⁻¹)
  let M : ℝ := (2 * dblmacro_step b 0 : ℝ)
  have hM_pos : 0 < M := by
    dsimp [M]
    exact_mod_cast hM_nat_pos
  have hα_nonneg : 0 ≤ α := by
    dsimp [α]
    positivity
  have hpowM_pos : 0 < Real.rpow M α := by
    exact Real.rpow_pos_of_pos hM_pos α
  let C0 : ℝ := (Real.rpow M α)⁻¹
  refine ⟨C0, ?_, ?_⟩
  · dsimp [C0]
    exact inv_pos.mpr hpowM_pos
  · intro s hs0 hs1
    have hs_nonneg : 0 ≤ (s : ℝ) := by
      positivity
    have hg := dblmacro_T_growth b hb 1 (by omega)
    have hupper : dblmacro_T b 1 + 1 ≤ 2 * dblmacro_step b 0 := by
      simpa using hg.2
    have hsM_nat : s ≤ 2 * dblmacro_step b 0 := by
      omega
    have hsM : (s : ℝ) ≤ M := by
      dsimp [M]
      exact_mod_cast hsM_nat
    have hpow_le : Real.rpow (s : ℝ) α ≤ Real.rpow M α := by
      exact Real.rpow_le_rpow hs_nonneg (by simpa using hsM) hα_nonneg
    have hC0_nonneg : 0 ≤ C0 := by
      exact le_of_lt (by dsimp [C0]; exact inv_pos.mpr hpowM_pos)
    have hscaled : C0 * Real.rpow (s : ℝ) α ≤ 1 := by
      calc
        C0 * Real.rpow (s : ℝ) α ≤ C0 * Real.rpow M α := by
          exact mul_le_mul_of_nonneg_left hpow_le hC0_nonneg
        _ = 1 := by
          simpa [C0] using inv_mul_cancel₀ hpowM_pos.ne'
    have hβ : ((b : ℝ) / (b - 1)) = α + 1 := by
      calc
        (b : ℝ) / (b - 1) = (b : ℝ) * (((b : ℝ) - 1)⁻¹) := by
          rw [div_eq_mul_inv]
        _ = (((b : ℝ) - 1) + 1) * (((b : ℝ) - 1)⁻¹) := by
          ring
        _ = ((b : ℝ) - 1) * (((b : ℝ) - 1)⁻¹) + 1 * (((b : ℝ) - 1)⁻¹) := by
          ring
        _ = 1 + (((b : ℝ) - 1)⁻¹) := by
          simp [mul_inv_cancel₀ hbsub_pos.ne']
        _ = α + 1 := by
          dsimp [α]
          ring
    have hrpow_split : Real.rpow (s : ℝ) (α + 1) = Real.rpow (s : ℝ) α * (s : ℝ) := by
      calc
        Real.rpow (s : ℝ) (α + 1) = Real.rpow (s : ℝ) α * Real.rpow (s : ℝ) 1 := by
          simpa using (Real.rpow_add_of_nonneg hs_nonneg hα_nonneg (show (0 : ℝ) ≤ 1 by positivity))
        _ = Real.rpow (s : ℝ) α * (s : ℝ) := by
          simp [Real.rpow_natCast]
    have hs_mul : (C0 * Real.rpow (s : ℝ) α) * s ≤ (s : ℝ) := by
      have := mul_le_mul_of_nonneg_right hscaled hs_nonneg
      simpa [one_mul]
    have hs0' : b - 1 ≤ s := by
      simpa [dblmacro_T] using hs0
    have hq_le : s - (b - 1) ≤ (s - (b - 1)) * b := by
      calc
        s - (b - 1) = (s - (b - 1)) * 1 := by
          symm
          exact Nat.mul_one _
        _ ≤ (s - (b - 1)) * b := by
          exact Nat.mul_le_mul_left _ hb1
    have hw_nat : s ≤ dblmacro_witness b 0 (s - dblmacro_T b 0) := by
      calc
        s = (s - (b - 1)) + (b - 1) := by
          symm
          exact Nat.sub_add_cancel hs0'
        _ ≤ (s - (b - 1)) * b + (b - 1) := by
          exact Nat.add_le_add_right hq_le (b - 1)
        _ = dblmacro_witness b 0 (s - dblmacro_T b 0) := by
          simp [dblmacro_witness, dblmacro_T, dblmacro_m, Nat.pow_zero, Nat.pow_one]
    have hw : (s : ℝ) ≤ (dblmacro_witness b 0 (s - dblmacro_T b 0) : ℝ) := by
      exact_mod_cast hw_nat
    calc
      C0 * Real.rpow s ((b : ℝ) / (b - 1))
          = C0 * Real.rpow (s : ℝ) (α + 1) := by rw [hβ]
      _ = C0 * (Real.rpow (s : ℝ) α * (s : ℝ)) := by rw [hrpow_split]
      _ = (C0 * Real.rpow (s : ℝ) α) * s := by ring
      _ ≤ s := hs_mul
      _ ≤ (dblmacro_witness b 0 (s - dblmacro_T b 0) : ℝ) := hw

theorem dblmacro_interval_lower_real_far (b : ℕ) (hb : 2 ≤ b) : ∃ C2 : ℝ, 0 < C2 ∧ ∀ {s n : ℕ}, dblmacro_T b (n + 1) ≤ s → s < dblmacro_T b (n + 2) → 2 * dblmacro_T b (n + 1) < s → C2 * Real.rpow s ((b : ℝ) / (b - 1)) ≤ (dblmacro_witness b (n + 1) (s - dblmacro_T b (n + 1)) : ℝ) := by
  have hb_real : (2 : ℝ) ≤ b := by
    exact_mod_cast hb
  have hb1_pos : (0 : ℝ) < (b : ℝ) - 1 := by
    nlinarith
  have hb1_ne : (b : ℝ) - 1 ≠ 0 := ne_of_gt hb1_pos
  refine ⟨Real.rpow (1 / 2 : ℝ) ((b : ℝ) / (b - 1)), ?_, ?_⟩
  · exact Real.rpow_pos_of_pos (by norm_num) _
  · intro s n hs1 hs2 hs3
    let q : ℕ := s - dblmacro_T b (n + 1)
    let α : ℝ := ((b - 1 : ℝ)⁻¹)
    let a : ℝ := (b : ℝ) / (b - 1)
    have hs_eq : q + dblmacro_T b (n + 1) = s := by
      dsimp [q]
      exact Nat.sub_add_cancel hs1
    have hs2' : s < (dblmacro_step b (n + 1) - 1) + dblmacro_T b (n + 1) := by
      simpa [dblmacro_T] using hs2
    have hq_le_step : q ≤ dblmacro_step b (n + 1) := by
      omega
    have hs_le_two_q : s ≤ 2 * q := by
      omega
    have hα_nonneg : 0 ≤ α := by
      dsimp [α]
      exact inv_nonneg.mpr (le_of_lt hb1_pos)
    have ha_nonneg : 0 ≤ a := by
      dsimp [a]
      exact div_nonneg (by positivity) (le_of_lt hb1_pos)
    have hq_nonneg : 0 ≤ (q : ℝ) := by
      positivity
    have hs_nonneg : 0 ≤ (s : ℝ) := by
      positivity
    have hs_half_le_q : (s : ℝ) / 2 ≤ q := by
      have hs_le_two_q_real : (s : ℝ) ≤ 2 * q := by
        exact_mod_cast hs_le_two_q
      nlinarith
    have ha : a = α + 1 := by
      dsimp [a, α]
      field_simp [hb1_ne]
      ring
    have hq_rpow_le_m : Real.rpow (q : ℝ) α ≤ dblmacro_m b (n + 1) := by
      calc
        Real.rpow (q : ℝ) α ≤ Real.rpow (dblmacro_step b (n + 1) : ℝ) α := by
          exact Real.rpow_le_rpow hq_nonneg (by exact_mod_cast hq_le_step) hα_nonneg
        _ = dblmacro_m b (n + 1) := dblmacro_step_rpow_inv_eq_m b hb (n + 1)
    have hq_rpow_one : Real.rpow (q : ℝ) 1 = (q : ℝ) := by
      simpa using (Real.rpow_natCast (q : ℝ) 1)
    have hqa_le_qm : Real.rpow (q : ℝ) a ≤ (q : ℝ) * dblmacro_m b (n + 1) := by
      have hmul : Real.rpow (q : ℝ) α * (q : ℝ) ≤ (dblmacro_m b (n + 1) : ℝ) * (q : ℝ) := by
        exact mul_le_mul_of_nonneg_right hq_rpow_le_m hq_nonneg
      calc
        Real.rpow (q : ℝ) a = Real.rpow (q : ℝ) α * (q : ℝ) := by
          calc
            Real.rpow (q : ℝ) a = Real.rpow (q : ℝ) (α + 1) := by rw [ha]
            _ = Real.rpow (q : ℝ) α * Real.rpow (q : ℝ) 1 := by
              exact Real.rpow_add_of_nonneg hq_nonneg hα_nonneg (by positivity)
            _ = Real.rpow (q : ℝ) α * (q : ℝ) := by
              rw [hq_rpow_one]
        _ ≤ (dblmacro_m b (n + 1) : ℝ) * (q : ℝ) := hmul
        _ = (q : ℝ) * dblmacro_m b (n + 1) := by ring
    have hm1_nonneg : (0 : ℝ) ≤ ((dblmacro_m b (n + 1) - 1 : ℕ) : ℝ) := by
      positivity
    have hqpow_le_witness : Real.rpow (q : ℝ) a ≤ (dblmacro_witness b (n + 1) q : ℝ) := by
      calc
        Real.rpow (q : ℝ) a ≤ (q : ℝ) * dblmacro_m b (n + 1) := hqa_le_qm
        _ ≤ (q : ℝ) * dblmacro_m b (n + 1) + ((dblmacro_m b (n + 1) - 1 : ℕ) : ℝ) := by
          exact le_add_of_nonneg_right hm1_nonneg
        _ = (dblmacro_witness b (n + 1) q : ℝ) := by
          simp only [dblmacro_witness, Nat.cast_add, Nat.cast_mul]
    have hs_div_pow_le : Real.rpow ((s : ℝ) / 2) a ≤ (dblmacro_witness b (n + 1) q : ℝ) := by
      calc
        Real.rpow ((s : ℝ) / 2) a ≤ Real.rpow (q : ℝ) a := by
          exact Real.rpow_le_rpow (by positivity) hs_half_le_q ha_nonneg
        _ ≤ (dblmacro_witness b (n + 1) q : ℝ) := hqpow_le_witness
    simpa [a, q] using
      (calc
        Real.rpow (1 / 2 : ℝ) a * Real.rpow s a = Real.rpow ((1 / 2 : ℝ) * s) a := by
          symm
          exact Real.mul_rpow (by positivity) hs_nonneg
        _ = Real.rpow ((s : ℝ) / 2) a := by
          congr 1
          ring
        _ ≤ (dblmacro_witness b (n + 1) q : ℝ) := hs_div_pow_le)

theorem dblmacro_interval_lower_real_near (b : ℕ) (hb : 2 ≤ b) : ∃ C1 : ℝ, 0 < C1 ∧ ∀ {s n : ℕ}, dblmacro_T b (n + 1) ≤ s → s < dblmacro_T b (n + 2) → s ≤ 2 * dblmacro_T b (n + 1) → C1 * Real.rpow s ((b : ℝ) / (b - 1)) ≤ (dblmacro_witness b (n + 1) (s - dblmacro_T b (n + 1)) : ℝ) := by
  let α : ℝ := (b : ℝ) / ((b : ℝ) - 1)
  refine ⟨(2 * Real.rpow (4 : ℝ) α)⁻¹, ?_, ?_⟩
  · have hpow4_pos : 0 < Real.rpow (4 : ℝ) α := by
      exact Real.rpow_pos_of_pos (by norm_num) α
    have hden_pos : 0 < 2 * Real.rpow (4 : ℝ) α := by
      positivity
    exact inv_pos.mpr hden_pos
  · intro s n hs hsnext hsnear
    have hTgrowth := dblmacro_T_growth b hb (n + 1) (by omega)
    have hThigh : dblmacro_T b (n + 1) + 1 ≤ 2 * dblmacro_step b n := by
      simpa using hTgrowth.2
    have hs_le_4step_nat : s ≤ 4 * dblmacro_step b n := by
      omega
    have hs_nonneg : (0 : ℝ) ≤ (s : ℝ) := by
      positivity
    have hs_le_4step : (s : ℝ) ≤ 4 * dblmacro_step b n := by
      exact_mod_cast hs_le_4step_nat
    have hexp_pos : 0 < b ^ (n + 1) := by
      apply Nat.pow_pos
      omega
    have hb_le_m : b ≤ dblmacro_m b (n + 1) := by
      dsimp [dblmacro_m]
      simpa using (Nat.le_pow hexp_pos)
    have hm_ge_two : 2 ≤ dblmacro_m b (n + 1) := le_trans hb hb_le_m
    have hnat1 : dblmacro_m b (n + 1) - 1 ≤ dblmacro_witness b (n + 1) (s - dblmacro_T b (n + 1)) := by
      dsimp [dblmacro_witness]
      omega
    have hmsub1_le_wit : (((dblmacro_m b (n + 1) - 1 : ℕ) : ℝ)) ≤
        (dblmacro_witness b (n + 1) (s - dblmacro_T b (n + 1)) : ℝ) := by
      exact_mod_cast hnat1
    have hm_ge_one : 1 ≤ dblmacro_m b (n + 1) := le_trans (by decide) hm_ge_two
    have hcast_sub : (((dblmacro_m b (n + 1) - 1 : ℕ) : ℝ)) = (dblmacro_m b (n + 1) : ℝ) - 1 := by
      simpa using (Nat.cast_sub (R := ℝ) hm_ge_one)
    have hwit_ge_half : (dblmacro_m b (n + 1) : ℝ) / 2 ≤
        (dblmacro_witness b (n + 1) (s - dblmacro_T b (n + 1)) : ℝ) := by
      rw [hcast_sub] at hmsub1_le_wit
      have hm_ge_two_real : (2 : ℝ) ≤ dblmacro_m b (n + 1) := by
        exact_mod_cast hm_ge_two
      nlinarith
    have hα_nonneg : 0 ≤ α := by
      dsimp [α]
      have hb1 : (1 : ℝ) < (b : ℝ) := by
        exact_mod_cast (show 1 < b by omega)
      have hbm1_pos : 0 < (b : ℝ) - 1 := by
        linarith
      exact div_nonneg (by positivity) hbm1_pos.le
    have hstep_rpow : Real.rpow (dblmacro_step b n : ℝ) α = dblmacro_m b (n + 1) := by
      simpa [α] using dblmacro_step_rpow_alpha_eq_m_succ b hb n
    have hpow : Real.rpow (s : ℝ) α ≤ Real.rpow (4 : ℝ) α * dblmacro_m b (n + 1) := by
      calc
        Real.rpow (s : ℝ) α ≤ Real.rpow (4 * dblmacro_step b n : ℝ) α := by
          exact Real.rpow_le_rpow hs_nonneg hs_le_4step hα_nonneg
        _ = Real.rpow (4 : ℝ) α * Real.rpow (dblmacro_step b n : ℝ) α := by
          simpa [Nat.cast_mul] using
            (Real.mul_rpow (x := (4 : ℝ)) (y := (dblmacro_step b n : ℝ)) (z := α) (by norm_num) (by positivity))
        _ = Real.rpow (4 : ℝ) α * dblmacro_m b (n + 1) := by
          rw [hstep_rpow]
    have hpow4_pos : 0 < Real.rpow (4 : ℝ) α := by
      exact Real.rpow_pos_of_pos (by norm_num) α
    have hC1_nonneg : 0 ≤ (2 * Real.rpow (4 : ℝ) α)⁻¹ := by
      exact le_of_lt (inv_pos.mpr (by positivity))
    have htmp : (2 * Real.rpow (4 : ℝ) α)⁻¹ * Real.rpow (s : ℝ) α ≤
        (2 * Real.rpow (4 : ℝ) α)⁻¹ * (Real.rpow (4 : ℝ) α * dblmacro_m b (n + 1)) := by
      exact mul_le_mul_of_nonneg_left hpow hC1_nonneg
    have hC1mul : (2 * Real.rpow (4 : ℝ) α)⁻¹ * Real.rpow (4 : ℝ) α = (1 : ℝ) / 2 := by
      field_simp [hpow4_pos.ne']
    have hmain : (2 * Real.rpow (4 : ℝ) α)⁻¹ * Real.rpow (s : ℝ) α ≤
        (dblmacro_m b (n + 1) : ℝ) / 2 := by
      calc
        (2 * Real.rpow (4 : ℝ) α)⁻¹ * Real.rpow (s : ℝ) α
            ≤ (2 * Real.rpow (4 : ℝ) α)⁻¹ * (Real.rpow (4 : ℝ) α * dblmacro_m b (n + 1)) := htmp
        _ = ((2 * Real.rpow (4 : ℝ) α)⁻¹ * Real.rpow (4 : ℝ) α) * dblmacro_m b (n + 1) := by
              ring
        _ = ((1 : ℝ) / 2) * dblmacro_m b (n + 1) := by
              rw [hC1mul]
        _ = (dblmacro_m b (n + 1) : ℝ) / 2 := by
              ring
    simpa [α] using le_trans hmain hwit_ge_half

theorem dblmacro_interval_lower_witness_bound (b : ℕ) (hb : 2 ≤ b) : ∃ C₁ : ℝ, 0 < C₁ ∧ ∀ {s k : ℕ}, dblmacro_T b k ≤ s → s < dblmacro_T b (k + 1) → Int.toNat (Int.ceil (C₁ * Real.rpow s ((b : ℝ) / (b - 1)))) ≤ dblmacro_witness b k (s - dblmacro_T b k) := by
  rcases dblmacro_interval_lower_real_base b hb with ⟨C0, hC0pos, h0⟩
  rcases dblmacro_interval_lower_real_near b hb with ⟨C1, hC1pos, h1⟩
  rcases dblmacro_interval_lower_real_far b hb with ⟨C2, hC2pos, h2⟩
  refine ⟨min C0 (min C1 C2), ?_, ?_⟩
  · positivity
  · intro s k hks hsk
    rw [Int.ceil_toNat]
    rw [Nat.ceil_le]
    cases k with
    | zero =>
        have hmin : min C0 (min C1 C2) ≤ C0 := min_le_left _ _
        have hpow : 0 ≤ Real.rpow s ((b : ℝ) / (b - 1)) := by
          apply Real.rpow_nonneg
          positivity
        have hmul : min C0 (min C1 C2) * Real.rpow s ((b : ℝ) / (b - 1)) ≤ C0 * Real.rpow s ((b : ℝ) / (b - 1)) := by
          exact mul_le_mul_of_nonneg_right hmin hpow
        exact le_trans hmul (h0 hks hsk)
    | succ n =>
        by_cases hs : s ≤ 2 * dblmacro_T b (n + 1)
        · have hmin : min C0 (min C1 C2) ≤ C1 := by
            exact le_trans (min_le_right _ _) (min_le_left _ _)
          have hpow : 0 ≤ Real.rpow s ((b : ℝ) / (b - 1)) := by
            apply Real.rpow_nonneg
            positivity
          have hmul : min C0 (min C1 C2) * Real.rpow s ((b : ℝ) / (b - 1)) ≤ C1 * Real.rpow s ((b : ℝ) / (b - 1)) := by
            exact mul_le_mul_of_nonneg_right hmin hpow
          exact le_trans hmul (h1 hks hsk hs)
        · have hs' : 2 * dblmacro_T b (n + 1) < s := by
            exact lt_of_not_ge hs
          have hmin : min C0 (min C1 C2) ≤ C2 := by
            exact le_trans (min_le_right _ _) (min_le_right _ _)
          have hpow : 0 ≤ Real.rpow s ((b : ℝ) / (b - 1)) := by
            apply Real.rpow_nonneg
            positivity
          have hmul : min C0 (min C1 C2) * Real.rpow s ((b : ℝ) / (b - 1)) ≤ C2 * Real.rpow s ((b : ℝ) / (b - 1)) := by
            exact mul_le_mul_of_nonneg_right hmin hpow
          exact le_trans hmul (h2 hks hsk hs')

theorem dblmacro_witness_add_one (b : ℕ) (hb : 2 ≤ b) (k q : ℕ) : dblmacro_witness b k q + 1 = (q + 1) * dblmacro_m b k := by
  dsimp [dblmacro_witness, dblmacro_m]
  have hm : 1 ≤ b ^ b ^ k := by
    apply Nat.succ_le_of_lt
    exact pow_pos (lt_of_lt_of_le (by decide : 0 < 2) hb) _
  rw [Nat.add_assoc]
  rw [Nat.sub_add_cancel hm]
  exact (Nat.succ_mul q (b ^ b ^ k)).symm

theorem dblmacro_interval_upper_witness_bound (b : ℕ) (hb : 2 ≤ b) : ∃ C₂ : ℝ, 0 < C₂ ∧ ∀ {s k : ℕ}, dblmacro_T b k ≤ s → s < dblmacro_T b (k + 1) → dblmacro_witness b k (s - dblmacro_T b k + 1) ≤ 1 + Int.toNat (Int.floor (C₂ * Real.rpow s (((2 * (b : ℝ) - 1) / (b - 1))))) := by
  let α : ℝ := (b : ℝ) / (b - 1)
  let β : ℝ := ((2 * (b : ℝ) - 1) / (b - 1))
  let C₂ : ℝ := 2 * (b : ℝ) + (2 : ℝ) ^ β
  refine ⟨C₂, ?_, ?_⟩
  · dsimp [C₂]
    positivity
  · intro s k hsk hslt
    rw [Int.floor_toNat]
    set q : ℕ := s - dblmacro_T b k + 1
    have hTbase : ∀ k : ℕ, b - 1 ≤ dblmacro_T b k := by
      intro k
      induction k with
      | zero => simp [dblmacro_T]
      | succ k ih =>
          simp [dblmacro_T]
          omega
    have hb1_nat : 1 ≤ b - 1 := by
      omega
    have hs1_nat : 1 ≤ s := by
      exact le_trans hb1_nat (le_trans (hTbase k) hsk)
    have hs1 : (1 : ℝ) ≤ s := by
      exact_mod_cast hs1_nat
    have hden_pos : (0 : ℝ) < (b : ℝ) - 1 := by
      have : (2 : ℝ) ≤ b := by
        exact_mod_cast hb
      linarith
    have hβ_eq : β = 1 + α := by
      dsimp [β, α]
      field_simp [show ((b : ℝ) - 1) ≠ 0 by linarith]
      ring
    have hα_nonneg : 0 ≤ α := by
      dsimp [α]
      exact div_nonneg (by positivity) (le_of_lt hden_pos)
    have hβ_nonneg : 0 ≤ β := by
      rw [hβ_eq]
      linarith
    have hβ_ge_one : (1 : ℝ) ≤ β := by
      rw [hβ_eq]
      linarith
    have hq1_le : q + 1 ≤ s + 1 := by
      dsimp [q]
      have hTk1 : 1 ≤ dblmacro_T b k := le_trans hb1_nat (hTbase k)
      omega
    have hw_nat : dblmacro_witness b k q ≤ (q + 1) * dblmacro_m b k := by
      have hwadd := dblmacro_witness_add_one b hb k q
      omega
    have hsp1_le_2s : (s + 1 : ℝ) ≤ 2 * s := by
      nlinarith
    have hs_le_rpow : (s : ℝ) ≤ Real.rpow s β := by
      calc
        (s : ℝ) = Real.rpow s 1 := by simp
        _ ≤ Real.rpow s β := by
          exact Real.rpow_le_rpow_of_exponent_le hs1 hβ_ge_one
    have h2s_pow : Real.rpow (2 * s : ℝ) β = (2 : ℝ) ^ β * Real.rpow s β := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using
        (Real.mul_rpow (show (0 : ℝ) ≤ 2 by positivity) (show (0 : ℝ) ≤ s by positivity) :
          ((2 : ℝ) * s) ^ β = (2 : ℝ) ^ β * s ^ β)
    have hgoal : (dblmacro_witness b k q : ℝ) ≤ C₂ * Real.rpow s β := by
      cases k with
      | zero =>
          have hw0_nat : dblmacro_witness b 0 q ≤ (s + 1) * b := by
            have hmul : (q + 1) * dblmacro_m b 0 ≤ (s + 1) * b := by
              have hmul' : (q + 1) * dblmacro_m b 0 ≤ (s + 1) * dblmacro_m b 0 :=
                Nat.mul_le_mul_right (dblmacro_m b 0) hq1_le
              simpa [dblmacro_m] using hmul'
            exact le_trans hw_nat hmul
          have hw0_real : (dblmacro_witness b 0 q : ℝ) ≤ (2 * (b : ℝ)) * Real.rpow s β := by
            have hw0_real' : (dblmacro_witness b 0 q : ℝ) ≤ (s + 1 : ℝ) * b := by
              exact_mod_cast hw0_nat
            calc
              (dblmacro_witness b 0 q : ℝ) ≤ (s + 1 : ℝ) * b := hw0_real'
              _ ≤ (2 * s : ℝ) * b := by
                exact mul_le_mul_of_nonneg_right hsp1_le_2s (by positivity)
              _ = (2 * (b : ℝ)) * s := by ring
              _ ≤ (2 * (b : ℝ)) * Real.rpow s β := by
                exact mul_le_mul_of_nonneg_left hs_le_rpow (by positivity)
          have hC : 2 * (b : ℝ) ≤ C₂ := by
            dsimp [C₂]
            have hnonneg : 0 ≤ (2 : ℝ) ^ β := by positivity
            linarith
          have hsβ_nonneg : 0 ≤ Real.rpow s β := Real.rpow_nonneg (by positivity) β
          exact le_trans hw0_real (mul_le_mul_of_nonneg_right hC hsβ_nonneg)
      | succ n =>
          have hgrowth := dblmacro_T_growth b hb (n + 1) (by omega)
          have hstep_le : dblmacro_step b n ≤ s + 1 := by
            rcases hgrowth with ⟨h1, h2⟩
            exact le_trans h1 (Nat.succ_le_succ hsk)
          have hm_real : (dblmacro_m b (n + 1) : ℝ) ≤ Real.rpow (s + 1) α := by
            calc
              (dblmacro_m b (n + 1) : ℝ) = Real.rpow (dblmacro_step b n) α := by
                dsimp [α]
                simpa [α] using (dblmacro_step_rpow_alpha_eq_m_succ b hb n).symm
              _ ≤ Real.rpow (s + 1) α := by
                apply Real.rpow_le_rpow
                · positivity
                · exact_mod_cast hstep_le
                · exact hα_nonneg
          have hw1_nat : dblmacro_witness b (n + 1) q ≤ (s + 1) * dblmacro_m b (n + 1) := by
            have hmul : (q + 1) * dblmacro_m b (n + 1) ≤ (s + 1) * dblmacro_m b (n + 1) :=
              Nat.mul_le_mul_right (dblmacro_m b (n + 1)) hq1_le
            exact le_trans hw_nat hmul
          have hs1p_pos : (0 : ℝ) < s + 1 := by
            positivity
          have hpow_eq : (s + 1 : ℝ) * Real.rpow (s + 1) α = Real.rpow (s + 1) β := by
            rw [hβ_eq]
            simpa only [Real.rpow_one] using (Real.rpow_add hs1p_pos (1 : ℝ) α).symm
          have hw1_real : (dblmacro_witness b (n + 1) q : ℝ) ≤ (2 : ℝ) ^ β * Real.rpow s β := by
            have hw1_real' : (dblmacro_witness b (n + 1) q : ℝ) ≤ (s + 1 : ℝ) * dblmacro_m b (n + 1) := by
              exact_mod_cast hw1_nat
            calc
              (dblmacro_witness b (n + 1) q : ℝ) ≤ (s + 1 : ℝ) * dblmacro_m b (n + 1) := hw1_real'
              _ ≤ (s + 1 : ℝ) * Real.rpow (s + 1) α := by
                exact mul_le_mul_of_nonneg_left hm_real (by positivity)
              _ = Real.rpow (s + 1) β := hpow_eq
              _ ≤ Real.rpow (2 * s) β := by
                apply Real.rpow_le_rpow
                · positivity
                · exact hsp1_le_2s
                · exact hβ_nonneg
              _ = (2 : ℝ) ^ β * Real.rpow s β := h2s_pow
          have hC : (2 : ℝ) ^ β ≤ C₂ := by
            dsimp [C₂]
            have hnonneg : 0 ≤ 2 * (b : ℝ) := by positivity
            linarith
          have hsβ_nonneg : 0 ≤ Real.rpow s β := Real.rpow_nonneg (by positivity) β
          exact le_trans hw1_real (mul_le_mul_of_nonneg_right hC hsβ_nonneg)
    have hfloor : dblmacro_witness b k q ≤ ⌊C₂ * Real.rpow s β⌋₊ := by
      exact Nat.le_floor hgoal
    have hfloor' : dblmacro_witness b k q ≤ ⌊C₂ * Real.rpow s (((2 * (b : ℝ) - 1) / (b - 1)))⌋₊ := by
      simpa [β] using hfloor
    omega

theorem dblmacro_witness_lt_m_succ (b : ℕ) (hb : 2 ≤ b) (k q : ℕ) : q < dblmacro_step b k → dblmacro_witness b k q < dblmacro_m b (k + 1) := by
  intro hq
  let m := dblmacro_m b k
  have hb0 : 0 < b := lt_of_lt_of_le (by decide : 0 < 2) hb
  have hmpos : 0 < m := by
    dsimp [m, dblmacro_m]
    exact pow_pos hb0 _
  have hsub : m - 1 < m := by
    exact Nat.sub_lt hmpos (by decide)
  have hlt : dblmacro_witness b k q < (q + 1) * m := by
    dsimp [dblmacro_witness]
    have hadd := Nat.add_lt_add_left hsub (q * m)
    simpa [m, Nat.succ_mul, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
      using hadd
  have hq' : q + 1 ≤ dblmacro_step b k := Nat.succ_le_of_lt hq
  have hmul : (q + 1) * m ≤ dblmacro_step b k * m := Nat.mul_le_mul_right m hq'
  have hfinal : dblmacro_witness b k q < dblmacro_step b k * m := lt_of_lt_of_le hlt hmul
  simpa [m, dblmacro_m_succ b hb k] using hfinal

theorem dblmacro_witness_succ (b : ℕ) (hb : 2 ≤ b) (k q : ℕ) : dblmacro_witness b (k + 1) q = dblmacro_witness b k (((q + 1) * dblmacro_step b k) - 1) := by
  have hb0 : 0 < b := by omega
  have hm : 0 < dblmacro_m b k := by
    unfold dblmacro_m
    exact pow_pos hb0 _
  have hs : 0 < dblmacro_step b k := by
    unfold dblmacro_step
    exact pow_pos hb0 _
  unfold dblmacro_witness
  rw [dblmacro_m_succ b hb k]
  calc
    q * (dblmacro_step b k * dblmacro_m b k) + (dblmacro_step b k * dblmacro_m b k - 1)
        = (q + 1) * (dblmacro_step b k * dblmacro_m b k) - 1 := by
            rw [← Nat.add_sub_assoc (Nat.succ_le_of_lt (Nat.mul_pos hs hm))
              (q * (dblmacro_step b k * dblmacro_m b k))]
            rw [Nat.add_one_mul]
    _ = ((q + 1) * dblmacro_step b k) * dblmacro_m b k - 1 := by
            rw [Nat.mul_assoc]
    _ = (((q + 1) * dblmacro_step b k - 1) * dblmacro_m b k + (dblmacro_m b k - 1)) := by
            rw [← Nat.add_sub_assoc (Nat.succ_le_of_lt hm)
              (((q + 1) * dblmacro_step b k - 1) * dblmacro_m b k)]
            rw [← Nat.add_one_mul]
            rw [Nat.sub_add_cancel (Nat.succ_le_of_lt (Nat.mul_pos (Nat.succ_pos q) hs))]

theorem theorem6_ball_A_card_le (n R : ℕ) (m : FreeAbelianMonoid n) : m ∈ Ball R (A n) ↔ m.card ≤ R := by
  constructor
  · rintro ⟨l, hlR, hA, rfl⟩
    have hcard : ∀ l : List (FreeAbelianMonoid n), (∀ x, x ∈ l → x ∈ A n) → l.sum.card = l.length := by
      intro l
      induction l with
      | nil =>
          intro hA
          simp
      | cons x xs ih =>
          intro hA
          have hx1 : x.card = 1 := by
            have hxA : x ∈ A n := hA x (by simp)
            simp [A] at hxA
            rcases hxA with ⟨i, rfl⟩
            simp
          have hxsA : ∀ y, y ∈ xs → y ∈ A n := by
            intro y hy
            exact hA y (by simp [hy])
          simpa [List.sum_cons, Multiset.card_add, hx1, ih hxsA, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
    rw [hcard l hA]
    exact hlR
  · intro hm
    refine ⟨m.toList.map (fun i => ({i} : FreeAbelianMonoid n)), ?_, ?_, ?_⟩
    · simpa using hm
    · intro x hx
      rcases List.mem_map.mp hx with ⟨i, hi, rfl⟩
      simp [A]
    · calc
        (m.toList.map fun i => ({i} : FreeAbelianMonoid n)).sum =
            (m.map fun i => ({i} : FreeAbelianMonoid n)).sum := by
              simpa using (Multiset.sum_map_toList m (fun i => ({i} : FreeAbelianMonoid n)))
        _ = m := by
              simpa using (Multiset.sum_map_singleton m)

theorem dblmacro_density_exact_count (b x : ℕ) (hb : 2 ≤ b) (hx : b ^ b ≤ x) : (DoublyMacroSet b ∩ Ball x (A 1)).ncard = Nat.log b (Nat.log b x) + 1 := by
  have hb1 : 1 < b := lt_of_lt_of_le (by decide : 1 < 2) hb
  have hbpos : 0 < b := lt_of_lt_of_le (by decide : 0 < 2) hb
  have hxpos : 0 < x :=
    lt_of_lt_of_le (show 0 < b ^ b from Nat.pow_pos hbpos) hx
  have hxne : x ≠ 0 := Nat.ne_of_gt hxpos
  have hblogx : b ≤ Nat.log b x := Nat.le_log_of_pow_le hb1 hx
  have hlogxpos : 0 < Nat.log b x := lt_of_lt_of_le hbpos hblogx
  have hlogxne : Nat.log b x ≠ 0 := Nat.ne_of_gt hlogxpos
  have h_eq :
      DoublyMacroSet b ∩ Ball x (A 1) =
        (fun j : ℕ => Multiset.replicate (b ^ (b ^ j)) (0 : Fin 1)) ''
          Set.Iic (Nat.log b (Nat.log b x)) := by
    ext m
    constructor
    · intro hm
      rcases hm with ⟨hmM, hmB⟩
      rcases hmM with ⟨i, j, rfl⟩
      have hcard : (Multiset.replicate (b ^ (b ^ j)) i).card ≤ x :=
        (theorem6_ball_A_card_le 1 x _).1 hmB
      have hpowx : b ^ (b ^ j) ≤ x := by
        simpa using hcard
      have hj1 : b ^ j ≤ Nat.log b x := Nat.le_log_of_pow_le hb1 hpowx
      have hj : j ≤ Nat.log b (Nat.log b x) := Nat.le_log_of_pow_le hb1 hj1
      refine ⟨j, ?_, ?_⟩
      · simpa using hj
      · have hi : i = 0 := by
          fin_cases i
          rfl
        simpa [hi]
    · rintro ⟨j, hj, rfl⟩
      have hj' : j ≤ Nat.log b (Nat.log b x) := by
        simpa using hj
      have hj1 : b ^ j ≤ Nat.log b x := Nat.pow_le_of_le_log hlogxne hj'
      have hcard : (Multiset.replicate (b ^ (b ^ j)) (0 : Fin 1)).card ≤ x := by
        simpa using (Nat.pow_le_of_le_log hxne hj1 : b ^ (b ^ j) ≤ x)
      refine ⟨?_, (theorem6_ball_A_card_le 1 x _).2 hcard⟩
      exact ⟨0, j, rfl⟩
  have hinj :
      Function.Injective (fun j : ℕ => Multiset.replicate (b ^ (b ^ j)) (0 : Fin 1)) := by
    intro j k h
    apply Nat.pow_right_injective hb
    apply Nat.pow_right_injective hb
    exact (Multiset.replicate_left_injective (0 : Fin 1)) h
  rw [h_eq, Set.ncard_image_of_injective (Set.Iic (Nat.log b (Nat.log b x))) hinj,
    Set.ncard_eq_toFinset_card']
  simp

theorem dblmacro_density_real_bounds (b : ℕ) (hb : 2 ≤ b) : ∃ d1 d2 : ℝ, ∀ x : ℕ, x ≥ b ^ b → 0 < d1 ∧ 0 < d2 ∧ d1 * (Real.log (Real.log x)) ≤ (DoublyMacroSet b ∩ Ball x (A 1)).ncard ∧ (DoublyMacroSet b ∩ Ball x (A 1)).ncard ≤ d2 * (Real.log (Real.log x)) := by
  refine ⟨(1 : ℝ) / (2 * Real.log b), (8 : ℝ) / (Real.log b), ?_⟩
  intro x hx
  have hb1 : 1 < b := by omega
  have hbpos : 0 < b := by omega
  have hbR : (1 : ℝ) < (b : ℝ) := by exact_mod_cast hb1
  have hbposR : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hbpos
  have hlogb : 0 < Real.log (b : ℝ) := Real.log_pos hbR
  let y : ℕ := Nat.log b x
  let k : ℕ := Nat.log b y
  have hy_ge_b : b ≤ y := by
    dsimp [y]
    exact Nat.le_log_of_pow_le hb1 hx
  have hy_pos : 0 < y := by
    exact lt_of_lt_of_le (by omega) hy_ge_b
  have hy_ne : y ≠ 0 := Nat.ne_of_gt hy_pos
  have hk_pos : 0 < k := by
    dsimp [k]
    exact Nat.log_pos hb1 hy_ge_b
  have hk_one : 1 ≤ k := Nat.succ_le_of_lt hk_pos
  have hcount : (DoublyMacroSet b ∩ Ball x (A 1)).ncard = k + 1 := by
    dsimp [k, y]
    simpa using dblmacro_density_exact_count b x hb hx
  have hxpos : 0 < x := by
    exact lt_of_lt_of_le (Nat.pow_pos hbpos) hx
  have hx_ne : x ≠ 0 := Nat.ne_of_gt hxpos
  have hxposR : (0 : ℝ) < (x : ℝ) := by exact_mod_cast hxpos
  have hpow_le : b ^ y ≤ x := by
    dsimp [y]
    exact Nat.pow_log_le_self b hx_ne
  have hpowk : b ^ k ≤ y := by
    dsimp [k]
    exact Nat.pow_log_le_self b hy_ne
  have hy_lt_pow : y < b ^ (k + 1) := by
    dsimp [k]
    simpa using Nat.lt_pow_succ_log_self hb1 y
  have hx_lt_pow : x < b ^ (y + 1) := by
    dsimp [y]
    simpa using Nat.lt_pow_succ_log_self hb1 x
  have hlog_two_half : (1 / 2 : ℝ) ≤ Real.log (2 : ℝ) := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h ⊢
    linarith
  have hlog2_le_logb : Real.log (2 : ℝ) ≤ Real.log (b : ℝ) := by
    exact Real.log_le_log (by norm_num) (by exact_mod_cast hb)
  have hhalf_le_logb : (1 / 2 : ℝ) ≤ Real.log (b : ℝ) := le_trans hlog_two_half hlog2_le_logb
  have hd1pos : 0 < (1 : ℝ) / (2 * Real.log b) := by
    have h2logb : 0 < (2 : ℝ) * Real.log (b : ℝ) := by positivity
    exact one_div_pos.mpr h2logb
  have hd2pos : 0 < (8 : ℝ) / Real.log b := by
    exact div_pos (by norm_num) hlogb
  have hx_gt_one : (1 : ℝ) < (x : ℝ) := by
    have h2le : (2 : ℝ) ≤ (x : ℝ) := by
      have hble : (b : ℕ) ≤ b ^ b := by
        exact Nat.le_pow (a := b) (by omega)
      exact_mod_cast (le_trans hb (le_trans hble hx))
    linarith
  have hlogx_pos : 0 < Real.log (x : ℝ) := Real.log_pos hx_gt_one
  have hlogx_le : (y : ℝ) * Real.log (b : ℝ) ≤ Real.log (x : ℝ) := by
    have hpow_leR : ((b : ℝ) ^ y) ≤ (x : ℝ) := by
      exact_mod_cast hpow_le
    simpa using (Real.le_log_of_pow_le hbposR hpow_leR)
  have hy_le_logdiv : (y : ℝ) ≤ Real.log (x : ℝ) / Real.log (b : ℝ) := by
    exact (le_div_iff₀ hlogb).2 hlogx_le
  have h_inv_logb_le_two : (Real.log (b : ℝ))⁻¹ ≤ (2 : ℝ) := by
    field_simp [hlogb.ne']
    nlinarith
  have hy_le_two_logx : (y : ℝ) ≤ 2 * Real.log (x : ℝ) := by
    calc
      (y : ℝ) ≤ Real.log (x : ℝ) * (Real.log (b : ℝ))⁻¹ := by
        simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hy_le_logdiv
      _ ≤ Real.log (x : ℝ) * 2 := by
        exact mul_le_mul_of_nonneg_left h_inv_logb_le_two hlogx_pos.le
      _ = 2 * Real.log (x : ℝ) := by ring
  have hyR_pos : (0 : ℝ) < (y : ℝ) := by exact_mod_cast hy_pos
  have hyR_ne : (y : ℝ) ≠ 0 := ne_of_gt hyR_pos
  have hzpos : 0 < (2 : ℝ) * Real.log (b : ℝ) := by positivity
  have hz_ne : (2 : ℝ) * Real.log (b : ℝ) ≠ 0 := ne_of_gt hzpos
  have hlogy_lt : Real.log (y : ℝ) < ((k + 1 : ℕ) : ℝ) * Real.log (b : ℝ) := by
    have hy_lt_powR : (y : ℝ) < ((b ^ (k + 1) : ℕ) : ℝ) := by
      exact_mod_cast hy_lt_pow
    calc
      Real.log (y : ℝ) < Real.log ((b ^ (k + 1) : ℕ) : ℝ) := by
        exact Real.log_lt_log hyR_pos hy_lt_powR
      _ = ((k + 1 : ℕ) : ℝ) * Real.log (b : ℝ) := by
        rw [Nat.cast_pow, Real.log_pow]
  have hlogx_lt2 : Real.log (x : ℝ) < ((2 * y : ℕ) : ℝ) * Real.log (b : ℝ) := by
    have hx_lt_powR : (x : ℝ) < ((b ^ (y + 1) : ℕ) : ℝ) := by
      exact_mod_cast hx_lt_pow
    have h1 : Real.log (x : ℝ) < ((y + 1 : ℕ) : ℝ) * Real.log (b : ℝ) := by
      calc
        Real.log (x : ℝ) < Real.log ((b ^ (y + 1) : ℕ) : ℝ) := by
          exact Real.log_lt_log hxposR hx_lt_powR
        _ = ((y + 1 : ℕ) : ℝ) * Real.log (b : ℝ) := by
          rw [Nat.cast_pow, Real.log_pow]
    have hy1le2y : y + 1 ≤ 2 * y := by omega
    have hy1le2yR : ((y + 1 : ℕ) : ℝ) ≤ ((2 * y : ℕ) : ℝ) := by exact_mod_cast hy1le2y
    exact lt_of_lt_of_le h1 (mul_le_mul_of_nonneg_right hy1le2yR hlogb.le)
  have hloglogx_lt_sum : Real.log (Real.log (x : ℝ)) < Real.log (y : ℝ) + Real.log ((2 : ℝ) * Real.log (b : ℝ)) := by
    have h1 : Real.log (x : ℝ) < (y : ℝ) * ((2 : ℝ) * Real.log (b : ℝ)) := by
      simpa [Nat.cast_mul, mul_assoc, mul_left_comm, mul_comm] using hlogx_lt2
    have h2 : Real.log (Real.log (x : ℝ)) < Real.log ((y : ℝ) * ((2 : ℝ) * Real.log (b : ℝ))) := by
      exact Real.log_lt_log hlogx_pos h1
    simpa [Real.log_mul hyR_ne hz_ne] using h2
  have hlog2logb_le : Real.log ((2 : ℝ) * Real.log (b : ℝ)) ≤ 2 * Real.log (b : ℝ) := by
    have h1 : Real.log ((2 : ℝ) * Real.log (b : ℝ)) ≤ (2 : ℝ) * Real.log (b : ℝ) - 1 := by
      exact Real.log_le_sub_one_of_pos hzpos
    linarith
  have hloglogx_lt_bound : Real.log (Real.log (x : ℝ)) < (2 * ((k + 1 : ℕ) : ℝ)) * Real.log (b : ℝ) := by
    have h2 : Real.log (Real.log (x : ℝ)) < ((k + 1 : ℕ) : ℝ) * Real.log (b : ℝ) + 2 * Real.log (b : ℝ) := by
      exact lt_of_lt_of_le hloglogx_lt_sum (by linarith [hlogy_lt.le, hlog2logb_le])
    have hk2 : (2 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by
      exact_mod_cast (show 2 ≤ k + 1 by omega)
    have hk2log : (2 : ℝ) * Real.log (b : ℝ) ≤ ((k + 1 : ℕ) : ℝ) * Real.log (b : ℝ) := by
      exact mul_le_mul_of_nonneg_right hk2 hlogb.le
    have hkbound : ((k + 1 : ℕ) : ℝ) * Real.log (b : ℝ) + 2 * Real.log (b : ℝ) ≤ (2 * ((k + 1 : ℕ) : ℝ)) * Real.log (b : ℝ) := by
      nlinarith
    exact lt_of_lt_of_le h2 hkbound
  have hlogy_ge : (k : ℝ) * Real.log (b : ℝ) ≤ Real.log (y : ℝ) := by
    have hpowkR : ((b : ℝ) ^ k) ≤ (y : ℝ) := by
      exact_mod_cast hpowk
    simpa using (Real.le_log_of_pow_le hbposR hpowkR)
  have hk_le_logy : (k : ℝ) ≤ Real.log (y : ℝ) / Real.log (b : ℝ) := by
    exact (le_div_iff₀ hlogb).2 hlogy_ge
  have hlogb_le_logy : Real.log (b : ℝ) ≤ Real.log (y : ℝ) := by
    have hy_ge_bR : (b : ℝ) ≤ (y : ℝ) := by exact_mod_cast hy_ge_b
    exact Real.log_le_log hbposR hy_ge_bR
  have hone_le_logy : (1 : ℝ) ≤ Real.log (y : ℝ) / Real.log (b : ℝ) := by
    exact (le_div_iff₀ hlogb).2 (by simpa [one_mul] using hlogb_le_logy)
  have hupper1 : (k + 1 : ℝ) ≤ 2 * (Real.log (y : ℝ) / Real.log (b : ℝ)) := by
    have htmp : (k : ℝ) + 1 ≤ Real.log (y : ℝ) / Real.log (b : ℝ) + Real.log (y : ℝ) / Real.log (b : ℝ) := by
      exact add_le_add hk_le_logy hone_le_logy
    simpa [two_mul, Nat.cast_add, add_assoc, add_left_comm, add_comm] using htmp
  have hlog_two_thirds : (2 / 3 : ℝ) ≤ Real.log (2 : ℝ) := by
    have h := Real.le_log_one_add_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)
    norm_num at h ⊢
    simpa using h
  have hlogx_ge_4thirds : (4 / 3 : ℝ) ≤ Real.log (x : ℝ) := by
    have h2log2_le : (2 : ℝ) * Real.log (2 : ℝ) ≤ Real.log (x : ℝ) := by
      have h2logb_le : (2 : ℝ) * Real.log (b : ℝ) ≤ Real.log (x : ℝ) := by
        have h2le_y : (2 : ℝ) ≤ (y : ℝ) := by
          exact_mod_cast (le_trans hb hy_ge_b)
        have htmp : (2 : ℝ) * Real.log (b : ℝ) ≤ (y : ℝ) * Real.log (b : ℝ) := by
          exact mul_le_mul_of_nonneg_right h2le_y hlogb.le
        exact le_trans htmp hlogx_le
      have h2log2_le_logb : (2 : ℝ) * Real.log (2 : ℝ) ≤ (2 : ℝ) * Real.log (b : ℝ) := by
        exact mul_le_mul_of_nonneg_left hlog2_le_logb (by norm_num : (0 : ℝ) ≤ 2)
      exact le_trans h2log2_le_logb h2logb_le
    have h43le : (4 / 3 : ℝ) ≤ (2 : ℝ) * Real.log (2 : ℝ) := by
      nlinarith [hlog_two_thirds]
    exact le_trans h43le h2log2_le
  have htwo_le_logx3 : (2 : ℝ) ≤ (Real.log (x : ℝ)) ^ 3 := by
    have hpow : (4 / 3 : ℝ) ^ 3 ≤ (Real.log (x : ℝ)) ^ 3 := by
      exact pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ 4 / 3) hlogx_ge_4thirds 3
    have hbase : (2 : ℝ) ≤ (4 / 3 : ℝ) ^ 3 := by norm_num
    exact le_trans hbase hpow
  have h2logx_le_pow4 : (2 : ℝ) * Real.log (x : ℝ) ≤ (Real.log (x : ℝ)) ^ 4 := by
    have hmul : (2 : ℝ) * Real.log (x : ℝ) ≤ (Real.log (x : ℝ)) ^ 3 * Real.log (x : ℝ) := by
      exact mul_le_mul_of_nonneg_right htwo_le_logx3 hlogx_pos.le
    simpa [pow_succ, mul_assoc, mul_left_comm, mul_comm] using hmul
  have hlog2logx_le : Real.log (2 * Real.log (x : ℝ)) ≤ 4 * Real.log (Real.log (x : ℝ)) := by
    calc
      Real.log (2 * Real.log (x : ℝ)) ≤ Real.log ((Real.log (x : ℝ)) ^ 4) := by
        have h2logx_pos : 0 < 2 * Real.log (x : ℝ) := by positivity
        exact Real.log_le_log h2logx_pos h2logx_le_pow4
      _ = 4 * Real.log (Real.log (x : ℝ)) := by
        rw [Real.log_pow]
        ring
  have hlogy_le_four : Real.log (y : ℝ) ≤ 4 * Real.log (Real.log (x : ℝ)) := by
    have h1 : Real.log (y : ℝ) ≤ Real.log (2 * Real.log (x : ℝ)) := by
      exact Real.log_le_log hyR_pos hy_le_two_logx
    exact le_trans h1 hlog2logx_le
  have hupper : (k + 1 : ℝ) ≤ (8 / Real.log (b : ℝ)) * Real.log (Real.log (x : ℝ)) := by
    calc
      (k + 1 : ℝ) ≤ 2 * (Real.log (y : ℝ) / Real.log (b : ℝ)) := hupper1
      _ = (2 / Real.log (b : ℝ)) * Real.log (y : ℝ) := by ring
      _ ≤ (2 / Real.log (b : ℝ)) * (4 * Real.log (Real.log (x : ℝ))) := by
        exact mul_le_mul_of_nonneg_left hlogy_le_four (by positivity)
      _ = (8 / Real.log (b : ℝ)) * Real.log (Real.log (x : ℝ)) := by ring
  have hlower : ((1 : ℝ) / (2 * Real.log (b : ℝ))) * Real.log (Real.log (x : ℝ)) ≤ (k + 1 : ℝ) := by
    have h2logb : 0 < (2 : ℝ) * Real.log (b : ℝ) := by positivity
    have htmp : Real.log (Real.log (x : ℝ)) ≤ (k + 1 : ℝ) * ((2 : ℝ) * Real.log (b : ℝ)) := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using hloglogx_lt_bound.le
    have htmp' : Real.log (Real.log (x : ℝ)) / ((2 : ℝ) * Real.log (b : ℝ)) ≤ (k + 1 : ℝ) := by
      exact (div_le_iff₀ h2logb).2 (by simpa [mul_assoc, mul_left_comm, mul_comm] using htmp)
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using htmp'
  refine ⟨hd1pos, hd2pos, ?_, ?_⟩
  · simpa [hcount] using hlower
  · simpa [hcount] using hupper

theorem dblmacro_expansion_upper_large (b : ℕ) (hb : 2 ≤ b) : ∃ C₂ : ℝ, 0 < C₂ ∧ ∀ s : ℕ, b - 1 ≤ s → let ub := Real.rpow s (((2 * (b : ℝ) - 1) / (b - 1))) ; ¬ (Ball (1 + Int.toNat <| Int.floor <| C₂ * ub) (A 1) ⊆ Ball s (DoublyMacroSet b ∪ A 1)) := by
  rcases dblmacro_interval_upper_witness_bound b hb with ⟨C₂, hC₂pos, hC₂bound⟩
  refine ⟨C₂, hC₂pos, ?_⟩
  intro s hs
  dsimp
  intro hsubset
  rcases dblmacro_T_interval b hb s hs with ⟨k, hk_le, hk_lt⟩
  let q : ℕ := s - dblmacro_T b k + 1
  let w : FreeAbelianMonoid 1 := Multiset.replicate (dblmacro_witness b k q) (0 : Fin 1)
  have hk_lt' : s < dblmacro_step b k - 1 + dblmacro_T b k := by
    simpa [dblmacro_T] using hk_lt
  have hstep_pos : 0 < dblmacro_step b k := by
    unfold dblmacro_step
    positivity
  have hq_lt : q < dblmacro_step b k := by
    dsimp [q]
    omega
  have hw_lt : dblmacro_witness b k q < dblmacro_m b (k + 1) := by
    exact dblmacro_witness_lt_m_succ b hb k q hq_lt
  have hs_eq : q + dblmacro_T b k - 1 = s := by
    dsimp [q]
    omega
  have hw_not_prefix : w ∉ Ball s (dblmacro_prefix b k ∪ A 1) := by
    have hhard := dblmacro_hard_prefix b hb k q
    simpa [w, hs_eq] using hhard
  have hw_not_big : w ∉ Ball s (DoublyMacroSet b ∪ A 1) := by
    intro hw_big
    have hw_prefix : w ∈ Ball s (dblmacro_prefix b k ∪ A 1) := by
      apply dblmacro_small_ball_restrict_prefix b hb k s (dblmacro_witness b k q)
      · exact hw_lt
      · simpa [w] using hw_big
    exact hw_not_prefix hw_prefix
  have hw_bound : dblmacro_witness b k q ≤ 1 + Int.toNat (Int.floor (C₂ * Real.rpow s (((2 * (b : ℝ) - 1) / (b - 1))))) := by
    exact hC₂bound hk_le hk_lt
  have hwA : w ∈ Ball (1 + Int.toNat (Int.floor (C₂ * Real.rpow s (((2 * (b : ℝ) - 1) / (b - 1))))) ) (A 1) := by
    rw [theorem6_ball_A_card_le]
    dsimp [w]
    simpa using hw_bound
  exact hw_not_big (hsubset hwA)

theorem dblmacro_prefix_cover (b : ℕ) (hb : 2 ≤ b) : ∀ k q, Ball (dblmacro_witness b k q) (A 1) ⊆ Ball (q + dblmacro_T b k) (dblmacro_prefix b k ∪ A 1) := by
  intro k q m hm
  have hmcard : m.card ≤ dblmacro_witness b k q :=
    (theorem6_ball_A_card_le 1 (dblmacro_witness b k q) m).1 hm
  have hbpos : 0 < b := by
    omega
  have hmkpos : 0 < dblmacro_m b k := by
    simpa [dblmacro_m] using (Nat.pow_pos (n := b ^ k) hbpos : 0 < b ^ (b ^ k))
  have hq : m.card / dblmacro_m b k ≤ q := by
    rw [Nat.div_le_iff_le_mul_add_pred hmkpos]
    simpa [dblmacro_witness, Nat.mul_comm] using hmcard
  have hr : m.card % dblmacro_m b k < dblmacro_m b k :=
    Nat.mod_lt _ hmkpos
  rw [a1_normal_form m]
  rcases dblmacro_cover_below_mk b hb k (m.card % dblmacro_m b k) hr with ⟨l, hl_len, hl_mem, hl_sum⟩
  refine ⟨List.replicate (m.card / dblmacro_m b k) (Multiset.replicate (dblmacro_m b k) (0 : Fin 1)) ++ l, ?_, ?_, ?_⟩
  · simp only [List.length_append, List.length_replicate]
    omega
  · intro x hx
    rw [List.mem_append] at hx
    rcases hx with hx | hx
    · have hx' : x = Multiset.replicate (dblmacro_m b k) (0 : Fin 1) :=
        List.eq_of_mem_replicate hx
      subst hx'
      exact Or.inl ⟨k, le_rfl, rfl⟩
    · exact hl_mem x hx
  · rw [List.sum_append, List.sum_replicate, hl_sum, Multiset.nsmul_replicate, ← Multiset.replicate_add]
    rw [Nat.div_add_mod']

theorem theorem6_ball_mono_R: ∀ {n : ℕ} {R R' : ℕ} {X : Set (FreeAbelianMonoid n)}, R ≤ R' → Ball R X ⊆ Ball R' X := by
  intro n R R' X hRR' x hx
  rcases hx with ⟨l, hlR, hx⟩
  exact ⟨l, le_trans hlR hRR', hx⟩

theorem dblmacro_expansion_upper_small (b : ℕ) (hb : 2 ≤ b) : ∃ C₂ : ℝ, 0 < C₂ ∧ ∀ s : ℕ, 1 ≤ s → s < b - 1 → let ub := Real.rpow s (((2 * (b : ℝ) - 1) / (b - 1))) ; ¬ (Ball (1 + Int.toNat <| Int.floor <| C₂ * ub) (A 1) ⊆ Ball s (DoublyMacroSet b ∪ A 1)) := by
  refine ⟨(b : ℝ), ?_, ?_⟩
  · positivity
  · intro s hs hsb
    dsimp
    let w0 : FreeAbelianMonoid 1 := Multiset.replicate (dblmacro_witness b 0 0) (0 : Fin 1)
    have hsle : s ≤ b - 2 := by
      omega
    have hw0_not_prefix : w0 ∉ Ball s (dblmacro_prefix b 0 ∪ A 1) := by
      have hhard : w0 ∉ Ball (dblmacro_T b 0 - 1) (dblmacro_prefix b 0 ∪ A 1) := by
        simpa [w0, dblmacro_T] using dblmacro_hard_prefix b hb 0 0
      have hmono : Ball s (dblmacro_prefix b 0 ∪ A 1) ⊆ Ball (dblmacro_T b 0 - 1) (dblmacro_prefix b 0 ∪ A 1) := by
        apply theorem6_ball_mono_R
        simpa [dblmacro_T] using hsle
      exact fun hw => hhard (hmono hw)
    have hw0_not_big : w0 ∉ Ball s (DoublyMacroSet b ∪ A 1) := by
      intro hw
      have hwlt : dblmacro_witness b 0 0 < dblmacro_m b (0 + 1) := by
        apply dblmacro_witness_lt_m_succ b hb 0 0
        rw [dblmacro_step]
        exact Nat.pow_pos (by omega)
      have hw_prefix : w0 ∈ Ball s (dblmacro_prefix b 0 ∪ A 1) := by
        exact dblmacro_small_ball_restrict_prefix b hb 0 s (dblmacro_witness b 0 0) hwlt (by simpa [w0] using hw)
      exact hw0_not_prefix hw_prefix
    refine fun hsubset => hw0_not_big ?_
    apply hsubset
    rw [theorem6_ball_A_card_le]
    have hExp_nonneg : 0 ≤ ((2 * (b : ℝ) - 1) / (b - 1)) := by
      have hb_real : (2 : ℝ) ≤ b := by
        exact_mod_cast hb
      have hnum : 0 ≤ 2 * (b : ℝ) - 1 := by
        linarith
      have hden : 0 ≤ (b : ℝ) - 1 := by
        linarith
      exact div_nonneg hnum hden
    have hub_ge_one : (1 : ℝ) ≤ Real.rpow (s : ℝ) ((2 * (b : ℝ) - 1) / (b - 1)) := by
      apply Real.one_le_rpow
      · exact_mod_cast hs
      · exact hExp_nonneg
    have hb_nonneg : (0 : ℝ) ≤ b := by
      positivity
    have hb_le : (b : ℝ) ≤ (b : ℝ) * Real.rpow (s : ℝ) ((2 * (b : ℝ) - 1) / (b - 1)) := by
      nlinarith
    have hb_nat : b ≤ Int.toNat (Int.floor ((b : ℝ) * Real.rpow (s : ℝ) ((2 * (b : ℝ) - 1) / (b - 1)))) := by
      rw [Int.floor_toNat]
      exact Nat.le_floor hb_le
    have hb_nat' : b ≤ Int.toNat (Int.floor ((b : ℝ) * ((s : ℝ) ^ (((2 * (b : ℝ) - 1) / (b - 1)))))) := by
      simpa using hb_nat
    have hw0_card : w0.card = dblmacro_witness b 0 0 := by
      simp [w0]
    have hw0_val : dblmacro_witness b 0 0 = b - 1 := by
      simp [dblmacro_witness, dblmacro_m]
    rw [hw0_card, hw0_val]
    omega

theorem dblmacro_expansion_upper (b : ℕ) (hb : 2 ≤ b) : ∃ C₂ : ℝ, 0 < C₂ ∧ ∀ s : ℕ, s ≥ 1 → let ub := Real.rpow s ((2 * (b : ℝ) - 1) / (b - 1)) ; ¬ (Ball (1 + Int.toNat <| Int.floor <| C₂ * ub) (A 1) ⊆ Ball s (DoublyMacroSet b ∪ A 1)) := by
  classical
  obtain ⟨Csmall, hCsmall_pos, hsmall⟩ := dblmacro_expansion_upper_small b hb
  obtain ⟨Clarge, hClarge_pos, hlarge⟩ := dblmacro_expansion_upper_large b hb
  refine ⟨max Csmall Clarge, lt_of_lt_of_le hCsmall_pos (le_max_left _ _), ?_⟩
  intro s hs
  dsimp
  by_cases hslt : s < b - 1
  · have hsmall_forbid := hsmall s hs hslt
    intro hsub
    have hs_nonneg : 0 ≤ (s : ℝ) := by
      exact_mod_cast Nat.zero_le s
    have hub_nonneg : 0 ≤ Real.rpow s ((2 * (b : ℝ) - 1) / (b - 1)) := by
      exact Real.rpow_nonneg hs_nonneg _
    have hC_le : Csmall ≤ max Csmall Clarge := le_max_left _ _
    have hmul : Csmall * Real.rpow s ((2 * (b : ℝ) - 1) / (b - 1)) ≤
        max Csmall Clarge * Real.rpow s ((2 * (b : ℝ) - 1) / (b - 1)) := by
      exact mul_le_mul_of_nonneg_right hC_le hub_nonneg
    have hfloor : Int.toNat (Int.floor (Csmall * Real.rpow s ((2 * (b : ℝ) - 1) / (b - 1)))) ≤
        Int.toNat (Int.floor (max Csmall Clarge * Real.rpow s ((2 * (b : ℝ) - 1) / (b - 1)))) := by
      rw [Int.floor_toNat, Int.floor_toNat]
      exact Nat.floor_mono hmul
    have hrad : 1 + Int.toNat (Int.floor (Csmall * Real.rpow s ((2 * (b : ℝ) - 1) / (b - 1)))) ≤
        1 + Int.toNat (Int.floor (max Csmall Clarge * Real.rpow s ((2 * (b : ℝ) - 1) / (b - 1)))) := by
      exact Nat.add_le_add_left hfloor 1
    have hmono :
        Ball (1 + Int.toNat (Int.floor (Csmall * Real.rpow s ((2 * (b : ℝ) - 1) / (b - 1))))) (A 1) ⊆
        Ball (1 + Int.toNat (Int.floor (max Csmall Clarge * Real.rpow s ((2 * (b : ℝ) - 1) / (b - 1))))) (A 1) := by
      exact theorem6_ball_mono_R hrad
    have hcontra :
        Ball (1 + Int.toNat (Int.floor (Csmall * Real.rpow s ((2 * (b : ℝ) - 1) / (b - 1))))) (A 1) ⊆
        Ball s (DoublyMacroSet b ∪ A 1) := by
      exact Set.Subset.trans hmono hsub
    exact hsmall_forbid hcontra
  · have hsge : b - 1 ≤ s := le_of_not_gt hslt
    have hlarge_forbid := hlarge s hsge
    intro hsub
    have hs_nonneg : 0 ≤ (s : ℝ) := by
      exact_mod_cast Nat.zero_le s
    have hub_nonneg : 0 ≤ Real.rpow s ((2 * (b : ℝ) - 1) / (b - 1)) := by
      exact Real.rpow_nonneg hs_nonneg _
    have hC_le : Clarge ≤ max Csmall Clarge := le_max_right _ _
    have hmul : Clarge * Real.rpow s ((2 * (b : ℝ) - 1) / (b - 1)) ≤
        max Csmall Clarge * Real.rpow s ((2 * (b : ℝ) - 1) / (b - 1)) := by
      exact mul_le_mul_of_nonneg_right hC_le hub_nonneg
    have hfloor : Int.toNat (Int.floor (Clarge * Real.rpow s ((2 * (b : ℝ) - 1) / (b - 1)))) ≤
        Int.toNat (Int.floor (max Csmall Clarge * Real.rpow s ((2 * (b : ℝ) - 1) / (b - 1)))) := by
      rw [Int.floor_toNat, Int.floor_toNat]
      exact Nat.floor_mono hmul
    have hrad : 1 + Int.toNat (Int.floor (Clarge * Real.rpow s ((2 * (b : ℝ) - 1) / (b - 1)))) ≤
        1 + Int.toNat (Int.floor (max Csmall Clarge * Real.rpow s ((2 * (b : ℝ) - 1) / (b - 1)))) := by
      exact Nat.add_le_add_left hfloor 1
    have hmono :
        Ball (1 + Int.toNat (Int.floor (Clarge * Real.rpow s ((2 * (b : ℝ) - 1) / (b - 1))))) (A 1) ⊆
        Ball (1 + Int.toNat (Int.floor (max Csmall Clarge * Real.rpow s ((2 * (b : ℝ) - 1) / (b - 1))))) (A 1) := by
      exact theorem6_ball_mono_R hrad
    have hcontra :
        Ball (1 + Int.toNat (Int.floor (Clarge * Real.rpow s ((2 * (b : ℝ) - 1) / (b - 1))))) (A 1) ⊆
        Ball s (DoublyMacroSet b ∪ A 1) := by
      exact Set.Subset.trans hmono hsub
    exact hlarge_forbid hcontra

theorem theorem6_ball_mono_X: ∀ {n : ℕ} {R : ℕ} {X Y : Set (FreeAbelianMonoid n)}, X ⊆ Y → Ball R X ⊆ Ball R Y := by
  intro n R X Y hXY x hx
  rcases hx with ⟨L, hL1, hL2, hL3⟩
  exact ⟨L, hL1, fun y hy => hXY (hL2 y hy), hL3⟩

theorem dblmacro_expansion_lower_large (b : ℕ) (hb : 2 ≤ b) : ∃ C₁ : ℝ, 0 < C₁ ∧ ∀ s : ℕ, b - 1 ≤ s → let lb := Real.rpow s ((b : ℝ) / (b - 1)) ; Ball (Int.toNat <| Int.ceil <| C₁ * lb) (A 1) ⊆ Ball s (DoublyMacroSet b ∪ A 1) := by
  rcases dblmacro_interval_lower_witness_bound b hb with ⟨C₁, hC₁pos, hbound⟩
  refine ⟨C₁, hC₁pos, ?_⟩
  intro s hs
  dsimp
  rcases dblmacro_T_interval b hb s hs with ⟨k, hk_le, hk_lt⟩
  let q : ℕ := s - dblmacro_T b k
  have hqeq : q + dblmacro_T b k = s := by
    dsimp [q]
    omega
  have hrad : Int.toNat (Int.ceil (C₁ * Real.rpow s ((b : ℝ) / (b - 1)))) ≤ dblmacro_witness b k q := by
    dsimp [q]
    exact hbound hk_le hk_lt
  have h1 : Ball (Int.toNat <| Int.ceil <| C₁ * Real.rpow s ((b : ℝ) / (b - 1))) (A 1) ⊆ Ball (dblmacro_witness b k q) (A 1) :=
    theorem6_ball_mono_R hrad
  have h2 : Ball (dblmacro_witness b k q) (A 1) ⊆ Ball (q + dblmacro_T b k) (dblmacro_prefix b k ∪ A 1) :=
    dblmacro_prefix_cover b hb k q
  have h3 : Ball (q + dblmacro_T b k) (dblmacro_prefix b k ∪ A 1) ⊆ Ball s (dblmacro_prefix b k ∪ A 1) := by
    rw [hqeq]
  have h4 : Ball s (dblmacro_prefix b k ∪ A 1) ⊆ Ball s (DoublyMacroSet b ∪ A 1) :=
    theorem6_ball_mono_X (dblmacro_prefix_union_subset_full b k)
  exact Set.Subset.trans h1 (Set.Subset.trans h2 (Set.Subset.trans h3 h4))

theorem dblmacro_expansion_lower_small (b : ℕ) (hb : 2 ≤ b) : ∃ C₁ : ℝ, 0 < C₁ ∧ ∀ s : ℕ, 1 ≤ s → s < b - 1 → let lb := Real.rpow s ((b : ℝ) / (b - 1)) ; Ball (Int.toNat <| Int.ceil <| C₁ * lb) (A 1) ⊆ Ball s (DoublyMacroSet b ∪ A 1) := by
  let a : ℝ := (b : ℝ) / (((b - 1 : ℕ) : ℝ))
  let R0 : ℝ := Real.rpow (((b - 1 : ℕ) : ℝ)) a
  refine ⟨(R0 + 1)⁻¹, ?_, ?_⟩
  · have hR0_nonneg : 0 ≤ R0 := by
      dsimp [R0]
      exact Real.rpow_nonneg (by positivity) a
    have hR0p1 : 0 < R0 + 1 := by
      linarith
    exact inv_pos.mpr hR0p1
  · intro s hs1 hslt
    have hb_ge1 : 1 ≤ b := by
      omega
    have hb1 : 0 < b - 1 := by
      omega
    have hb1R : (0 : ℝ) < (((b - 1 : ℕ) : ℝ)) := by
      exact_mod_cast hb1
    have hsleR : (s : ℝ) ≤ (((b - 1 : ℕ) : ℝ)) := by
      exact_mod_cast hslt.le
    have ha_nonneg : 0 ≤ a := by
      dsimp [a]
      exact div_nonneg (by positivity) (le_of_lt hb1R)
    have h_lb_le_R0 : Real.rpow s a ≤ R0 := by
      dsimp [R0]
      exact Real.rpow_le_rpow (by positivity) hsleR ha_nonneg
    have hR0_nonneg : 0 ≤ R0 := by
      dsimp [R0]
      exact Real.rpow_nonneg (by positivity) a
    have hR0p1 : 0 < R0 + 1 := by
      linarith
    have hC1_nonneg : 0 ≤ (R0 + 1)⁻¹ := by
      exact inv_nonneg.mpr (le_of_lt hR0p1)
    have hmain :
        Ball (Int.toNat <| Int.ceil <| (R0 + 1)⁻¹ * Real.rpow s a) (A 1) ⊆
          Ball s (DoublyMacroSet b ∪ A 1) := by
      have hmul_le : (R0 + 1)⁻¹ * Real.rpow s a ≤ (R0 + 1)⁻¹ * R0 := by
        gcongr
      have hR0_le : (R0 + 1)⁻¹ * R0 ≤ ((1 : ℕ) : ℝ) := by
        have hstep : (R0 + 1)⁻¹ * R0 ≤ (R0 + 1)⁻¹ * (R0 + 1) := by
          gcongr
          linarith
        calc
          (R0 + 1)⁻¹ * R0 ≤ (R0 + 1)⁻¹ * (R0 + 1) := hstep
          _ = ((1 : ℕ) : ℝ) := by
            simpa using inv_mul_cancel₀ hR0p1.ne'
      have hrad_le_one : (R0 + 1)⁻¹ * Real.rpow s a ≤ ((1 : ℕ) : ℝ) := by
        exact hmul_le.trans hR0_le
      have hceil : Int.toNat (Int.ceil ((R0 + 1)⁻¹ * Real.rpow s a)) ≤ 1 := by
        rw [Int.ceil_toNat]
        exact Nat.ceil_le.2 hrad_le_one
      calc
        Ball (Int.toNat <| Int.ceil <| (R0 + 1)⁻¹ * Real.rpow s a) (A 1)
            ⊆ Ball 1 (A 1) := theorem6_ball_mono_R hceil
        _ ⊆ Ball s (A 1) := theorem6_ball_mono_R hs1
        _ ⊆ Ball s (DoublyMacroSet b ∪ A 1) := theorem6_ball_mono_X (by
          intro x hx
          exact Or.inr hx)
    simpa [a, Nat.cast_sub hb_ge1] using hmain

theorem dblmacro_expansion_lower (b : ℕ) (hb : 2 ≤ b) : ∃ C₁ : ℝ, 0 < C₁ ∧ ∀ s : ℕ, s ≥ 1 → let lb := Real.rpow s ((b : ℝ) / (b - 1)) ; Ball (Int.toNat <| Int.ceil <| C₁ * lb) (A 1) ⊆ Ball s (DoublyMacroSet b ∪ A 1) := by
  rcases dblmacro_expansion_lower_small b hb with ⟨Csmall, hCsmall_pos, hsmall⟩
  rcases dblmacro_expansion_lower_large b hb with ⟨Clarge, hClarge_pos, hlarge⟩
  refine ⟨min Csmall Clarge, lt_min hCsmall_pos hClarge_pos, ?_⟩
  intro s hs
  dsimp
  let lb : ℝ := Real.rpow s ((b : ℝ) / (b - 1))
  have hlb_nonneg : 0 ≤ lb := by
    dsimp [lb]
    positivity
  by_cases hlt : s < b - 1
  · have hbase : Ball (Int.toNat <| Int.ceil <| Csmall * lb) (A 1) ⊆ Ball s (DoublyMacroSet b ∪ A 1) := by
      simpa [lb] using hsmall s hs hlt
    have hmono : Ball (Int.toNat <| Int.ceil <| min Csmall Clarge * lb) (A 1) ⊆ Ball (Int.toNat <| Int.ceil <| Csmall * lb) (A 1) := by
      apply theorem6_ball_mono_R
      exact Int.toNat_le_toNat <| Int.ceil_mono <| mul_le_mul_of_nonneg_right (min_le_left _ _) hlb_nonneg
    exact Set.Subset.trans hmono hbase
  · have hsge : b - 1 ≤ s := le_of_not_gt hlt
    have hbase : Ball (Int.toNat <| Int.ceil <| Clarge * lb) (A 1) ⊆ Ball s (DoublyMacroSet b ∪ A 1) := by
      simpa [lb] using hlarge s hsge
    have hmono : Ball (Int.toNat <| Int.ceil <| min Csmall Clarge * lb) (A 1) ⊆ Ball (Int.toNat <| Int.ceil <| Clarge * lb) (A 1) := by
      apply theorem6_ball_mono_R
      exact Int.toNat_le_toNat <| Int.ceil_mono <| mul_le_mul_of_nonneg_right (min_le_right _ _) hlb_nonneg
    exact Set.Subset.trans hmono hbase

theorem theorem6 (b : ℕ) (hb : 2 ≤ b) : let M := DoublyMacroSet b
  (∃ (d1 d2 : ℝ), ∀ (x : ℕ), (x ≥ b ^ b) → 0 < d1 ∧ 0 < d2
      ∧ d1 * (Real.log (Real.log x)) ≤ (M ∩ (Ball x (A 1))).ncard
      ∧ (M ∩ (Ball x (A 1))).ncard ≤ d2 * (Real.log (Real.log x))) ∧
  (∃ C₁ C₂ : ℝ,
    0 < C₁ ∧ 0 < C₂ ∧
    (∀ (s : ℕ), (s ≥ 1) →
      let lb := Real.rpow s ((b : ℝ) / (b - 1))
      (Ball (Int.toNat <| Int.ceil <| C₁ * lb) (A 1) ⊆ Ball s (M ∪ (A 1))) ∧
        let ub := Real.rpow s ((2 * (b : ℝ) - 1) / (b - 1))
        ¬ (Ball (1 + Int.toNat <| Int.floor <| C₂ * ub) (A 1) ⊆ Ball s (M ∪ (A 1))))) := by
  dsimp
  constructor
  · exact dblmacro_density_real_bounds b hb
  · rcases dblmacro_expansion_lower b hb with ⟨C₁, hC₁pos, hlower⟩
    rcases dblmacro_expansion_upper b hb with ⟨C₂, hC₂pos, hupper⟩
    refine ⟨C₁, C₂, hC₁pos, hC₂pos, ?_⟩
    intro s hs
    constructor
    · exact hlower s hs
    · exact hupper s hs
