import LeanFun.Definitions
import Mathlib

open abelian

def thm2RelevantGenerators (n : ℕ) (M : Set (FreeAbelianMonoid n)) (r : ℕ) : Set (FreeAbelianMonoid n) :=
  (M ∩ Ball r (A n)) ∪ A n

theorem thm2_A_finite (n : ℕ) : (A n).Finite := by
  classical
  have hA : A n = Set.range (fun i : Fin n => ({i} : FreeAbelianMonoid n)) := by
    ext m
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨i, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨i, rfl⟩
  simpa [hA] using (Set.finite_range (fun i : Fin n => ({i} : FreeAbelianMonoid n)))

theorem thm2_ball_ncard_upper_bound {n : ℕ} (s : ℕ) (X : Set (FreeAbelianMonoid n)) (hX : X.Finite) :
  (Ball s X).ncard ≤ (s + 1) * (X.ncard + 1) ^ s := by
  classical
  letI : Fintype X := hX.fintype

  -- lists over X of length ≤ s
  let L : Set (List X) := {l | l.length ≤ s}
  have hLfin : L.Finite := by
    simpa [L] using (List.finite_length_le (α := X) s)

  -- sum in the ambient monoid
  let f : List X → FreeAbelianMonoid n := fun l => l.unattach.sum

  -- helper: unattach after pmap-subtype is the identity
  have unattach_pmap_eq (l : List (FreeAbelianMonoid n)) (H : ∀ x ∈ l, x ∈ X) :
      (List.pmap (fun x hx => (⟨x, hx⟩ : X)) l H).unattach = l := by
    induction l with
    | nil =>
        simp
    | cons a t ih =>
        simp [List.pmap, ih]

  have hBall : Ball s X = f '' L := by
    ext m
    constructor
    · intro hm
      rcases hm with ⟨l, hl_len, hl_mem, hl_sum⟩
      have H : ∀ x ∈ l, x ∈ X := by
        intro x hx
        exact hl_mem x hx
      let lX : List X := List.pmap (fun x hx => (⟨x, hx⟩ : X)) l H
      have hlX_len : lX.length ≤ s := by
        simpa [lX] using hl_len
      have hlX_sum : f lX = m := by
        have hunattach : lX.unattach = l := by
          simpa [lX] using unattach_pmap_eq (l := l) (H := H)
        simpa [f, hunattach] using hl_sum
      exact ⟨lX, hlX_len, hlX_sum⟩
    · rintro ⟨lX, hlX_len, hm⟩
      refine ⟨lX.unattach, ?_, ?_, ?_⟩
      · simpa using hlX_len
      · intro x hx
        change x ∈ lX.map Subtype.val at hx
        rcases List.mem_map.1 hx with ⟨y, hy, rfl⟩
        exact y.property
      · simpa [f] using hm

  have hBall_ncard : (Ball s X).ncard ≤ L.ncard := by
    simpa [hBall] using (Set.ncard_image_le (f := f) (s := L) (hs := hLfin))

  -- encode a list by its length and padded entries
  let encode : L → Fin (s + 1) × (Fin s → Option X) := fun l =>
    (⟨l.1.length, Nat.lt_succ_of_le l.2⟩,
      fun i => if h : i.1 < l.1.length then some (l.1.get ⟨i.1, h⟩) else none)

  have hencode_inj : Function.Injective encode := by
    intro l1 l2 h
    apply Subtype.ext
    have hlen : l1.1.length = l2.1.length := by
      have hfst : (⟨l1.1.length, Nat.lt_succ_of_le l1.2⟩ : Fin (s + 1)) =
          ⟨l2.1.length, Nat.lt_succ_of_le l2.2⟩ := by
        simpa [encode] using congrArg Prod.fst h
      exact congrArg Fin.val hfst

    refine (List.ext_get_iff).2 ?_
    refine ⟨hlen, ?_⟩
    intro n hn1 hn2
    have hn_lt_s : n < s := lt_of_lt_of_le hn1 l1.2
    let i : Fin s := ⟨n, hn_lt_s⟩
    have hval : (if h' : i.1 < l1.1.length then some (l1.1.get ⟨i.1, h'⟩) else none) =
        (if h' : i.1 < l2.1.length then some (l2.1.get ⟨i.1, h'⟩) else none) := by
      have hfun : (fun i : Fin s => if h' : i.1 < l1.1.length then some (l1.1.get ⟨i.1, h'⟩) else none) =
          (fun i : Fin s => if h' : i.1 < l2.1.length then some (l2.1.get ⟨i.1, h'⟩) else none) := by
        simpa [encode] using congrArg Prod.snd h
      simpa using congrArg (fun g => g i) hfun

    have hi1 : i.1 < l1.1.length := by
      simpa [i] using hn1
    have hi2 : i.1 < l2.1.length := by
      simpa [i] using hn2

    have hsome : some (l1.1.get ⟨i.1, hi1⟩) = some (l2.1.get ⟨i.1, hi2⟩) := by
      simpa [hi1, hi2] using hval

    have hget : l1.1.get ⟨i.1, hi1⟩ = l2.1.get ⟨i.1, hi2⟩ :=
      Option.some.inj hsome

    have hget1 : l1.1.get ⟨n, hn1⟩ = l1.1.get ⟨i.1, hi1⟩ := by
      simpa [i] using congrArg (fun j : Fin l1.1.length => l1.1.get j)
        (by
          apply Fin.ext
          simp [i])
    have hget2 : l2.1.get ⟨i.1, hi2⟩ = l2.1.get ⟨n, hn2⟩ := by
      simpa [i] using congrArg (fun j : Fin l2.1.length => l2.1.get j)
        (by
          apply Fin.ext
          simp [i])

    exact hget1.trans (hget.trans hget2)

  have hcardX : Fintype.card X = X.ncard := by
    simpa [Nat.card_eq_fintype_card] using (Nat.card_coe_set_eq (s := X))

  have hL_ncard : L.ncard ≤ (s + 1) * (X.ncard + 1) ^ s := by
    have hcard : Nat.card L ≤ Nat.card (Fin (s + 1) × (Fin s → Option X)) := by
      exact Nat.card_le_card_of_injective encode hencode_inj
    have hcard' : L.ncard ≤ (s + 1) * (Fintype.card X + 1) ^ s := by
      simpa [Nat.card_coe_set_eq] using hcard
    simpa [hcardX] using hcard'

  exact le_trans hBall_ncard hL_ncard

theorem thm2_cancel_two_pow (n m K : ℕ) (c : ℝ)
  (hc : 0 < c) (hKm : 2 * m + 2 ≤ K)
  (hK : (2:ℝ)^K ≥ ((2*n : ℝ) + c * ((1 + (Real.log (Real.exp 1 + 2)) / (2 * Real.log 2)) ^ m)) * (K:ℝ)^m * (2:ℝ)^(2*m+1)) :
  ((2*n : ℝ) + c * ((1 + (Real.log (Real.exp 1 + 2)) / (2 * Real.log 2)) ^ m)) * (K:ℝ)^m * (2:ℝ)
    ≤ (2:ℝ) ^ (K - 2*m) := by
  classical
  set B : ℝ := (2 * n : ℝ) + c * ((1 + Real.log (Real.exp 1 + 2) / (2 * Real.log 2)) ^ m)
  have h2mK : 2 * m ≤ K := by
    omega
  have hpos : 0 < (2 : ℝ) ^ (2 * m) := by
    have h2 : (0 : ℝ) < (2 : ℝ) := by
      norm_num
    exact pow_pos h2 (2 * m)
  have hK' : (B * (K : ℝ) ^ m * (2 : ℝ)) * (2 : ℝ) ^ (2 * m)
      ≤ (2 : ℝ) ^ (K - 2 * m) * (2 : ℝ) ^ (2 * m) := by
    have hK0 : B * (K : ℝ) ^ m * (2 : ℝ) ^ (2 * m + 1) ≤ (2 : ℝ) ^ K := by
      simpa [B, mul_assoc, mul_left_comm, mul_comm] using hK
    have hK1 : B * (K : ℝ) ^ m * (2 : ℝ) ^ (2 * m + 1)
        ≤ (2 : ℝ) ^ ((K - 2 * m) + 2 * m) := by
      -- rewrite the exponent K as (K - 2*m) + 2*m
      simpa [Nat.sub_add_cancel h2mK] using (show B * (K : ℝ) ^ m * (2 : ℝ) ^ (2 * m + 1) ≤ (2 : ℝ) ^ K from hK0)
    -- expand both powers and reassociate
    simpa [pow_succ, pow_add, mul_assoc, mul_left_comm, mul_comm] using hK1
  have hcancel : B * (K : ℝ) ^ m * (2 : ℝ) ≤ (2 : ℝ) ^ (K - 2 * m) := by
    exact le_of_mul_le_mul_right hK' hpos
  simpa [B, mul_assoc, mul_left_comm, mul_comm] using hcancel


theorem thm2_exists_nat_two_pow_gt_poly (m T : ℕ) (B : ℝ) (hB : 0 < B) :
  ∃ K : ℕ, T ≤ K ∧ (2:ℝ)^K > B * (K:ℝ)^m := by
  classical
  -- Limit of (n^m) / 2^n is 0
  have hlim :
      Filter.Tendsto (fun n : ℕ => (n : ℝ) ^ m / (2 : ℝ) ^ n) Filter.atTop (nhds (0 : ℝ)) := by
    simpa using
      (tendsto_pow_const_div_const_pow_of_one_lt m (r := (2 : ℝ)) (by norm_num))
  -- Multiply by constant B
  have hlimB :
      Filter.Tendsto (fun n : ℕ => B * ((n : ℝ) ^ m / (2 : ℝ) ^ n)) Filter.atTop (nhds (0 : ℝ)) := by
    simpa using (hlim.const_mul B)
  -- Eventually the ratio is < 1
  have hlt : ∀ᶠ n : ℕ in Filter.atTop, B * ((n : ℝ) ^ m / (2 : ℝ) ^ n) < (1 : ℝ) := by
    exact
      (Filter.Tendsto.eventually_lt_const (u := (1 : ℝ)) (v := (0 : ℝ)) (by norm_num) hlimB)
  -- Convert to B*(n^m) < 2^n
  have hlt' : ∀ᶠ n : ℕ in Filter.atTop, B * (n : ℝ) ^ m < (2 : ℝ) ^ n := by
    refine hlt.mono ?_
    intro n hn
    have hpos : (0 : ℝ) < (2 : ℝ) ^ n := by
      have h2 : (0 : ℝ) < (2 : ℝ) := by norm_num
      exact pow_pos h2 n
    have hn' : (B * (n : ℝ) ^ m) / (2 : ℝ) ^ n < (1 : ℝ) := by
      simpa [mul_div_assoc'] using hn
    have : B * (n : ℝ) ^ m < (2 : ℝ) ^ n := (div_lt_one hpos).1 hn'
    simpa [mul_assoc] using this
  -- Extract a witness N
  rcases (Filter.eventually_atTop.1 hlt') with ⟨N, hN⟩
  refine ⟨max N T, ?_, ?_⟩
  · exact le_max_right N T
  · have hge : N ≤ max N T := le_max_left N T
    have hineq : B * ((max N T : ℕ) : ℝ) ^ m < (2 : ℝ) ^ (max N T) := hN (max N T) hge
    -- Goal is 2^K > B*K^m
    simpa [gt_iff_lt, mul_comm, mul_left_comm, mul_assoc] using hineq

theorem thm2_exp_Kslog_eq_pow (K s : ℕ) (hs : s ≥ 1) : Real.exp (K * s * Real.log s) = (s : ℝ) ^ (K * s) := by
  classical
  -- show positivity of s as a real number
  have hspos : (0 : ℝ) < (s : ℝ) := by
    have hs0 : 0 < s := Nat.succ_le_iff.mp hs
    exact_mod_cast hs0
  -- rewrite the exponent as a natural multiple
  have hrew : (K : ℝ) * (s : ℝ) * Real.log (s : ℝ) = (K * s : ℕ) * Real.log (s : ℝ) := by
    -- `simp` changes `(K : ℝ) * (s : ℝ)` to `(K * s : ℕ)`
    simp [mul_assoc]
  -- use `Real.exp_nat_mul` and `Real.exp_log`
  -- First, put the exponent in the form `n * x`
  -- then apply `Real.exp_nat_mul`
  --
  -- start from the left hand side
  calc
    Real.exp (K * s * Real.log s) = Real.exp ((K * s : ℕ) * Real.log (s : ℝ)) := by
      -- coe s to ℝ in the log
      -- and use the rewrite lemma above
      -- note that the lhs is already over ℝ
      simpa [mul_assoc] using congrArg Real.exp (by
        -- prove the equality of exponents
        --
        -- `simp` should coerce naturals appropriately
        simpa [mul_assoc] )
    _ = (Real.exp (Real.log (s : ℝ))) ^ (K * s) := by
      simpa using (Real.exp_nat_mul (Real.log (s : ℝ)) (K * s))
    _ = (s : ℝ) ^ (K * s) := by
      simp [Real.exp_log hspos]


theorem thm2_mem_ball_A_iff_card_le {n : ℕ} (r : ℕ) (m : FreeAbelianMonoid n) : m ∈ Ball r (A n) ↔ m.card ≤ r := by
  constructor
  · intro hm
    rcases hm with ⟨l, hlr, hlA, hsum⟩
    -- show `m.card ≤ r`
    have hcard_sum : ∀ l : List (FreeAbelianMonoid n),
        (∀ x, x ∈ l → x ∈ A n) → (l.sum).card = l.length := by
      intro l hmem
      induction l with
      | nil =>
          simp
      | cons a t ih =>
          have ha : a ∈ A n := hmem a (by simp)
          have ht : ∀ x, x ∈ t → x ∈ A n := by
            intro x hx
            exact hmem x (by simp [hx])
          rcases (by simpa [A] using ha) with ⟨i, rfl⟩
          simp [List.sum_cons, Multiset.card_add, ih ht]
    have hmcard : m.card = l.length := by
      have := hcard_sum l hlA
      -- rewrite `l.sum = m`
      simpa [hsum] using this
    -- conclude
    simpa [hmcard] using hlr
  · intro hmcard
    classical
    let l : List (FreeAbelianMonoid n) := m.toList.map (fun i : Fin n => ({i} : Multiset (Fin n)))
    refine ⟨l, ?_, ?_, ?_⟩
    · -- length bound
      simpa [l, Multiset.length_toList] using hmcard
    · -- elements are in A n
      intro x hx
      rcases (List.mem_map.1 hx) with ⟨i, hi, rfl⟩
      simpa [A]
    · -- sum equals m
      have hsum_singleton : ∀ t : List (Fin n),
          (t.map (fun i : Fin n => ({i} : Multiset (Fin n)))).sum = (t : Multiset (Fin n)) := by
        intro t
        induction t with
        | nil =>
            simp
        | cons a t ih =>
            simp [List.sum_cons, ih, Multiset.singleton_add]
      -- apply to `m.toList`
      have : l.sum = (m.toList : Multiset (Fin n)) := by
        simpa [l] using hsum_singleton (m.toList)
      -- coe_toList
      simpa [this] using (Multiset.coe_toList m).symm

theorem thm2_ball_restrict_macros {n : ℕ} {M : Set (FreeAbelianMonoid n)} {r s : ℕ} :
  Ball r (A n) ⊆ Ball s (M ∪ A n) →
    Ball r (A n) ⊆ Ball s (thm2RelevantGenerators n M r) := by
  intro h
  intro w hw
  have hw' : w ∈ Ball s (M ∪ A n) := h hw
  rcases hw' with ⟨l, hl_len, hl_mem, hl_sum⟩
  refine ⟨l, hl_len, ?_, hl_sum⟩
  intro x hx
  have hx' : x ∈ M ∪ A n := hl_mem x hx
  rcases hx' with hxM | hxA
  · have hwcard : w.card ≤ r := (thm2_mem_ball_A_iff_card_le (n:=n) r w).1 hw
    have hsumcard : (l.map (fun m : FreeAbelianMonoid n => m.card)).sum = w.card := by
      have h1 : Multiset.cardHom (l.sum) = Multiset.cardHom w := congrArg Multiset.cardHom hl_sum
      have h2 : Multiset.cardHom (l.sum) = (l.map fun m => Multiset.cardHom m).sum := by
        simpa using (Multiset.cardHom.map_list_sum l)
      have h3 : (l.map fun m => Multiset.cardHom m).sum = Multiset.cardHom w := h2.symm.trans h1
      simpa using h3
    have hxcard_mem : x.card ∈ l.map (fun m : FreeAbelianMonoid n => m.card) := by
      exact (List.mem_map.2 ⟨x, hx, rfl⟩)
    have hxle_sum : x.card ≤ (l.map (fun m : FreeAbelianMonoid n => m.card)).sum := by
      exact List.le_sum_of_mem hxcard_mem
    have hxcard : x.card ≤ r := by
      have hxle_w : x.card ≤ w.card := by
        simpa [hsumcard] using hxle_sum
      exact le_trans hxle_w hwcard
    have hxBall : x ∈ Ball r (A n) := (thm2_mem_ball_A_iff_card_le (n:=n) r x).2 hxcard
    exact Or.inl ⟨hxM, hxBall⟩
  · exact Or.inr hxA


theorem thm2_ncard_A (n : ℕ) : (A n).ncard = n := by
  classical
  -- Let f be the singleton map.
  let f : Fin n → Multiset (Fin n) := fun i => ({i} : Multiset (Fin n))
  have hf : Function.Injective f := by
    intro i j hij
    have : ({i} : Multiset (Fin n)) = {j} := by
      simpa [f] using hij
    exact (Multiset.singleton_inj.mp this)
  -- Rewrite `A n` as the image of `f` on `Set.univ` and compute the cardinality.
  calc
    (A n).ncard = (f '' (Set.univ : Set (Fin n))).ncard := by
      simp [abelian.A, f, Set.image_univ]
      rfl
    _ = (Set.univ : Set (Fin n)).ncard := by
      simpa using (Set.ncard_image_of_injective (s := (Set.univ : Set (Fin n))) (f := f) hf)
    _ = Nat.card (Fin n) := by
      simpa using (Set.ncard_univ (α := Fin n))
    _ = n := by
      simpa using (Nat.card_fin n)


theorem thm2RelevantGenerators_ncard_le {n : ℕ} (M : Set (FreeAbelianMonoid n)) (r : ℕ) :
  (thm2RelevantGenerators n M r).ncard ≤ (M ∩ Ball r (A n)).ncard + n := by
  classical
  -- Apply the general bound on the ncard of a union, then rewrite `(A n).ncard`.
  simpa [thm2RelevantGenerators, thm2_ncard_A n] using
    (Set.ncard_union_le (M ∩ Ball r (A n)) (A n))

theorem thm2_pmap_subtype_unattach {α : Type*} {X : Set α} (l : List α) (H : ∀ x ∈ l, x ∈ X) :
  (List.pmap (fun x hx => (⟨x, hx⟩ : X)) l H).unattach = l := by
  induction l with
  | nil =>
      simp
  | cons a t ih =>
      simp [List.pmap, ih]

theorem thm2_ball_finite {n : ℕ} (R : ℕ) (X : Set (FreeAbelianMonoid n)) (hX : X.Finite) : (Ball R X).Finite := by
  classical
  haveI : Fintype X := hX.fintype
  let L : Set (List X) := {l | l.length ≤ R}
  have hL : L.Finite := by
    simpa [L] using (List.finite_length_le (α := X) R)
  let f : List X → FreeAbelianMonoid n := fun l => (l.map Subtype.val).sum
  have hf : (f '' L).Finite := hL.image f
  refine hf.subset ?_
  intro m hm
  rcases hm with ⟨l, hlR, hlX, rfl⟩
  let l' : List X :=
    l.pmap (fun x hx => (⟨x, hx⟩ : X)) (by
      intro x hx
      exact hlX x hx)
  refine ⟨l', ?_, ?_⟩
  · simpa [L, l'] using hlR
  ·
    have : l'.unattach = l := by
      simpa [l'] using
        thm2_pmap_subtype_unattach (l := l) (X := X)
          (H := by
            intro x hx
            exact hlX x hx)
    simpa [f, this, l']

theorem thm2RelevantGenerators_finite {n : ℕ} (M : Set (FreeAbelianMonoid n)) (r : ℕ) : (thm2RelevantGenerators n M r).Finite := by
  classical
  unfold thm2RelevantGenerators
  have hA : (A n).Finite := thm2_A_finite n
  have hBall : (Ball r (A n)).Finite := thm2_ball_finite r (A n) hA
  have hInter : (M ∩ Ball r (A n)).Finite := by
    refine hBall.subset ?_
    intro x hx
    exact hx.2
  exact hInter.union hA


theorem thm2_ballA_ncard_lower_bound (n r : ℕ) (hn : 1 ≤ n) : (r + 1) ≤ (Ball r (A n)).ncard := by
  classical
  -- choose a generator in `Fin n`
  have hn' : 0 < n := Nat.succ_le_iff.mp hn
  let i0 : Fin n := ⟨0, hn'⟩
  -- define the family of multisets `k ↦ {i0, ..., i0}`
  let f : ℕ → FreeAbelianMonoid n := fun k => Multiset.replicate k i0

  -- `Ball r (A n)` is finite (needed because `Set.ncard` is junk on infinite sets)
  have hs : (Ball r (A n) : Set (FreeAbelianMonoid n)).Finite := by
    -- show `Ball r (A n)` is exactly the multisets of cardinality `≤ r`
    have hBall : (Ball r (A n) : Set (FreeAbelianMonoid n)) = {m | m.card ≤ r} := by
      ext m
      simpa using (thm2_mem_ball_A_iff_card_le (n := n) r m)

    -- enumerate all multisets of size `≤ r` using symmetric powers
    let g : (Σ k : Fin (r + 1), Sym (Fin n) (k : ℕ)) → FreeAbelianMonoid n := fun x => (x.2 : _)

    have hrange : (Set.range g : Set (FreeAbelianMonoid n)) = {m | m.card ≤ r} := by
      ext m
      constructor
      · rintro ⟨x, rfl⟩
        -- `x.2 : Sym (Fin n) k` has cardinality `k`
        have hk : (x.2 : Multiset (Fin n)).card = (x.1 : ℕ) := by
          simpa using (x.2.property)
        -- and `k < r+1`
        have hk' : (x.1 : ℕ) ≤ r := Nat.lt_succ_iff.mp x.1.is_lt
        simpa [g, hk] using hk'
      · intro hm
        -- pick `k = m.card`, which lies in `Fin (r+1)` since `m.card ≤ r`
        let k : Fin (r + 1) := ⟨m.card, Nat.lt_succ_of_le hm⟩
        refine ⟨⟨k, ?_⟩, ?_⟩
        · -- `m` is an element of `Sym (Fin n) k`
          refine ⟨m, ?_⟩
          rfl
        · -- and `g` maps it back to `m`
          rfl

    -- conclude finiteness
    -- (range of a function from a finite type is finite)
    have : (Set.range g : Set (FreeAbelianMonoid n)).Finite := by
      simpa using (Set.finite_range g)
    -- rewrite the goal set using `hBall` and `hrange`
    simpa [hBall, hrange] using this

  -- membership of the first `r+1` terms
  have hf : ∀ i < r + 1, f i ∈ Ball r (A n) := by
    intro i hi
    have hle : (f i).card ≤ r := by
      -- `card (replicate i i0) = i` and `i < r+1` gives `i ≤ r`
      simpa [f, Multiset.card_replicate] using (Nat.lt_succ_iff.mp hi)
    exact (thm2_mem_ball_A_iff_card_le (n := n) r (f i)).2 hle

  -- injectivity on the first `r+1` terms
  have hinj : ∀ i < r + 1, ∀ j < r + 1, f i = f j → i = j := by
    intro i hi j hj hij
    exact (Multiset.replicate_left_injective i0) hij

  -- apply the general lower bound lemma
  simpa using (Set.le_ncard_of_inj_on_range (s := Ball r (A n)) (n := r + 1) f hf hinj hs)


theorem thm2_r_add_one_gt_exp (K s : ℕ) :
  let r : ℕ := 1 + Int.toNat (Int.floor (Real.exp (K * s * Real.log s)))
  Real.exp (K * s * Real.log s) < (r + 1 : ℝ) := by
  classical
  -- unfold the definition of `r` and rewrite `Int.toNat (Int.floor _)` as `⌊_⌋₊`
  simp [Int.floor_toNat, Nat.cast_add, Nat.cast_one, add_assoc, add_left_comm, add_comm]
  -- set `a := Real.exp ...`
  have hlt : Real.exp (↑K * ↑s * Real.log ↑s) < (⌊Real.exp (↑K * ↑s * Real.log ↑s)⌋₊ : ℝ) + 1 := by
    simpa using (Nat.lt_floor_add_one (Real.exp (↑K * ↑s * Real.log ↑s)))
  have hle : (⌊Real.exp (↑K * ↑s * Real.log ↑s)⌋₊ : ℝ) + 1 ≤ 1 + (1 + (⌊Real.exp (↑K * ↑s * Real.log ↑s)⌋₊ : ℝ)) := by
    linarith
  exact lt_of_lt_of_le hlt hle

theorem thm2_r_le_exp_add_one (K s : ℕ) :
  let r : ℕ := 1 + Int.toNat (Int.floor (Real.exp (K * s * Real.log s)))
  (r : ℝ) ≤ Real.exp (K * s * Real.log s) + 1 := by
  classical
  -- unfold the `let r := ...` and rewrite `Int.toNat (Int.floor x)` as `⌊x⌋₊`
  simp [Int.floor_toNat]
  
  have hfloor : ((⌊Real.exp (↑K * ↑s * Real.log ↑s)⌋₊ : ℝ) ≤ Real.exp (↑K * ↑s * Real.log ↑s)) := by
    exact Nat.floor_le (by positivity)
  
  linarith [hfloor]


theorem thm2_log_exp1_add_r_le (K s : ℕ) (hs : s ≥ 2) :
  let r : ℕ := 1 + Int.toNat (Int.floor (Real.exp (K * s * Real.log s)))
  Real.log (Real.exp 1 + r) ≤ Real.log (Real.exp 1 + 2) + K * s * Real.log s := by
  classical
  dsimp
  set r : ℕ := 1 + Int.toNat (Int.floor (Real.exp (K * s * Real.log s))) with hr
  have hrle : (r : ℝ) ≤ Real.exp (K * s * Real.log s) + 1 := by
    simpa [hr] using (thm2_r_le_exp_add_one K s)

  let A : ℝ := K * s * Real.log s

  have hs1n : 1 ≤ s := by
    exact le_trans (by decide : 1 ≤ 2) hs
  have hs1 : (1 : ℝ) ≤ (s : ℝ) := by
    exact_mod_cast hs1n
  have hlognonneg : 0 ≤ Real.log (s : ℝ) := by
    simpa using (Real.log_nonneg hs1)

  have hA_nonneg : 0 ≤ A := by
    dsimp [A]
    have hKs_nonneg : 0 ≤ (K : ℝ) * (s : ℝ) := by positivity
    nlinarith [hKs_nonneg, hlognonneg]

  have hExpA : (1 : ℝ) ≤ Real.exp A := by
    exact Real.one_le_exp hA_nonneg

  have hrleA : (r : ℝ) ≤ Real.exp A + 1 := by
    simpa [A] using hrle

  have hArg : Real.exp 1 + (r : ℝ) ≤ (Real.exp 1 + 2) * Real.exp A := by
    have h1 : Real.exp 1 ≤ Real.exp 1 * Real.exp A := by
      have hExp1_nonneg : 0 ≤ Real.exp (1 : ℝ) := by positivity
      have := mul_le_mul_of_nonneg_left hExpA hExp1_nonneg
      simpa [mul_assoc] using this
    have h2 : Real.exp A + 1 ≤ 2 * Real.exp A := by
      nlinarith [hExpA]
    have h3 : Real.exp 1 + (Real.exp A + 1) ≤ Real.exp 1 * Real.exp A + 2 * Real.exp A := by
      have := add_le_add h1 h2
      simpa [add_assoc] using this
    have h4 : Real.exp 1 + (r : ℝ) ≤ Real.exp 1 + (Real.exp A + 1) := by
      linarith [hrleA]
    have h5 : Real.exp 1 + (r : ℝ) ≤ Real.exp 1 * Real.exp A + 2 * Real.exp A := by
      exact le_trans h4 h3
    have hrewrite : Real.exp 1 * Real.exp A + 2 * Real.exp A = (Real.exp 1 + 2) * Real.exp A := by
      ring
    -- rewrite the RHS
    simpa [hrewrite] using h5

  have hx : 0 < Real.exp 1 + (r : ℝ) := by positivity

  have hlog : Real.log (Real.exp 1 + (r : ℝ)) ≤ Real.log ((Real.exp 1 + 2) * Real.exp A) := by
    exact Real.log_le_log hx hArg

  have hne1 : (Real.exp 1 + 2) ≠ 0 := by
    have : 0 < Real.exp 1 + (2 : ℝ) := by positivity
    exact ne_of_gt this
  have hne2 : Real.exp A ≠ 0 := by
    exact ne_of_gt (Real.exp_pos A)

  have hlogrhs : Real.log ((Real.exp 1 + 2) * Real.exp A) = Real.log (Real.exp 1 + 2) + A := by
    calc
      Real.log ((Real.exp 1 + 2) * Real.exp A)
          = Real.log (Real.exp 1 + 2) + Real.log (Real.exp A) := by
              simpa using (Real.log_mul hne1 hne2)
      _ = Real.log (Real.exp 1 + 2) + A := by
              simp [Real.log_exp]

  have hfinal : Real.log (Real.exp 1 + (r : ℝ)) ≤ Real.log (Real.exp 1 + 2) + A := by
    simpa [hlogrhs] using hlog

  simpa [A] using hfinal


theorem thm2_rpow_log_bound (q : ℝ) (m K s : ℕ) (hKpos : 0 < K) (hs : s ≥ 2) (hq : q ≤ (m : ℝ)) :
  let r : ℕ := 1 + Int.toNat (Int.floor (Real.exp (K * s * Real.log s)))
  Real.rpow (Real.log (Real.exp 1 + r)) q ≤
    ((1 + (Real.log (Real.exp 1 + 2)) / (2 * Real.log 2)) ^ m) * (K:ℝ)^m * (s:ℝ)^(2*m) := by
  classical
  dsimp
  set r : ℕ := 1 + Int.toNat (Int.floor (Real.exp (↑K * ↑s * Real.log ↑s))) with hr
  set A : ℝ := (K : ℝ) * (s : ℝ) * Real.log (s : ℝ)
  set C1 : ℝ := 1 + (Real.log (Real.exp 1 + 2)) / (2 * Real.log 2)
  have hlog : Real.log (Real.exp 1 + (r : ℝ)) ≤ Real.log (Real.exp 1 + 2) + A := by
    have := thm2_log_exp1_add_r_le K s hs
    simpa [hr, A, mul_assoc, mul_left_comm, mul_comm] using this
  have hbase1 : (1 : ℝ) ≤ Real.log (Real.exp 1 + (r : ℝ)) := by
    have hle : Real.exp 1 ≤ Real.exp 1 + (r : ℝ) := by
      have : (0 : ℝ) ≤ (r : ℝ) := by positivity
      linarith
    have hpos1 : (0 : ℝ) < Real.exp 1 := by positivity
    have hlogle : Real.log (Real.exp 1) ≤ Real.log (Real.exp 1 + (r : ℝ)) :=
      Real.log_le_log hpos1 hle
    simpa using (show (Real.log (Real.exp 1) : ℝ) ≤ Real.log (Real.exp 1 + (r : ℝ)) from hlogle)
  have hq_to_m : Real.rpow (Real.log (Real.exp 1 + (r : ℝ))) q ≤
      Real.rpow (Real.log (Real.exp 1 + (r : ℝ))) (m : ℝ) := by
    simpa [Real.rpow_eq_pow] using
      (Real.rpow_le_rpow_of_exponent_le (x := Real.log (Real.exp 1 + (r : ℝ))) (y := q)
        (z := (m : ℝ)) hbase1 hq)
  have hA_ge : (2 * Real.log 2) ≤ A := by
    have hK1 : 1 ≤ K := Nat.succ_le_iff.mp hKpos
    have hKs_ge2_nat : 2 ≤ K * s := by
      have hs2_nat : 2 ≤ s := hs
      have : 2 ≤ (1:ℕ) * s := by simpa using hs2_nat
      have hmul : (1:ℕ) * s ≤ K * s := by
        exact Nat.mul_le_mul_right s hK1
      exact le_trans this hmul
    have hKs_ge2 : (2 : ℝ) ≤ (K : ℝ) * (s : ℝ) := by
      have : (2 : ℝ) ≤ ((K * s : ℕ) : ℝ) := by exact_mod_cast hKs_ge2_nat
      simpa [Nat.cast_mul] using this
    have hlog2_le : Real.log 2 ≤ Real.log (s : ℝ) := by
      have hs2 : (2 : ℝ) ≤ (s : ℝ) := by exact_mod_cast hs
      have hpos2 : (0 : ℝ) < 2 := by norm_num
      exact Real.log_le_log hpos2 hs2
    have hlog2_nonneg : (0 : ℝ) ≤ Real.log 2 := by
      have h : (1 : ℝ) < (2 : ℝ) := by norm_num
      exact le_of_lt (Real.log_pos h)
    have : (2 : ℝ) * Real.log 2 ≤ ((K : ℝ) * (s : ℝ)) * Real.log (s : ℝ) := by
      exact mul_le_mul hKs_ge2 hlog2_le hlog2_nonneg (by positivity : (0:ℝ) ≤ (K:ℝ) * (s:ℝ))
    simpa [A, mul_assoc, mul_left_comm, mul_comm] using this
  have hlog_add_le : Real.log (Real.exp 1 + 2) + A ≤ C1 * A := by
    set B : ℝ := Real.log (Real.exp 1 + 2)
    set d : ℝ := 2 * Real.log 2
    have hd_pos : (0 : ℝ) < d := by
      have hlog2pos : (0 : ℝ) < Real.log 2 := by
        have : (1 : ℝ) < (2 : ℝ) := by norm_num
        exact Real.log_pos this
      nlinarith [d, hlog2pos]
    have hd_ne : d ≠ 0 := ne_of_gt hd_pos
    have hB_nonneg : (0 : ℝ) ≤ B := by
      have hpos : (1 : ℝ) < Real.exp 1 + 2 := by
        have : (0 : ℝ) < Real.exp 1 := by positivity
        linarith
      exact le_of_lt (Real.log_pos hpos)
    have hratio_nonneg : (0 : ℝ) ≤ B / d := by
      exact div_nonneg hB_nonneg (le_of_lt hd_pos)
    have hmul_le : B / d * d ≤ B / d * A := by
      have : d ≤ A := by simpa [d] using hA_ge
      exact mul_le_mul_of_nonneg_left this hratio_nonneg
    have hB_le : B ≤ B / d * A := by
      have hcancel : B / d * d = B := by
        simpa [d] using (div_mul_cancel₀ B hd_ne)
      simpa [hcancel] using hmul_le
    have hsum_le : B + A ≤ B / d * A + A := by
      linarith [hB_le]
    have hrewrite : B / d * A + A = C1 * A := by
      simp [C1, B, d, add_mul, mul_add, mul_assoc, mul_left_comm, mul_comm, add_comm, add_left_comm,
        add_assoc]
    simpa [B, hrewrite] using hsum_le
  -- main inequality
  have hlog_le_C1A : Real.log (Real.exp 1 + (r : ℝ)) ≤ C1 * A :=
    le_trans hlog hlog_add_le
  have hlog_nonneg : (0 : ℝ) ≤ Real.log (Real.exp 1 + (r : ℝ)) := by
    linarith [hbase1]
  have hm_nonneg : (0 : ℝ) ≤ (m : ℝ) := by
    exact_mod_cast (Nat.zero_le m)
  have hm_le : Real.rpow (Real.log (Real.exp 1 + (r : ℝ))) (m : ℝ) ≤
      Real.rpow (C1 * A) (m : ℝ) := by
    simpa [Real.rpow_eq_pow] using
      (Real.rpow_le_rpow (x := Real.log (Real.exp 1 + (r : ℝ))) (y := C1 * A) (z := (m : ℝ))
        hlog_nonneg hlog_le_C1A hm_nonneg)
  have hq_le : Real.rpow (Real.log (Real.exp 1 + (r : ℝ))) q ≤
      Real.rpow (C1 * A) (m : ℝ) := by
    exact le_trans hq_to_m hm_le
  have hq_le_pow : Real.rpow (Real.log (Real.exp 1 + (r : ℝ))) q ≤ (C1 * A) ^ m := by
    have : Real.rpow (C1 * A) (m : ℝ) = (C1 * A) ^ m := by
      simpa [Real.rpow_eq_pow] using (Real.rpow_natCast (C1 * A) m)
    simpa [this] using hq_le
  have hpow : (C1 * A) ^ m = (C1 ^ m) * (A ^ m) := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using (mul_pow C1 A m)
  have hA_pow : A ^ m ≤ (K : ℝ) ^ m * (s : ℝ) ^ (2 * m) := by
    -- bound log s ≤ s
    have hlog_le_s : Real.log (s : ℝ) ≤ (s : ℝ) := by
      simpa using (Real.log_le_self (by positivity : (0 : ℝ) ≤ (s : ℝ)))
    have hA_le : A ≤ (K : ℝ) * (s : ℝ) ^ 2 := by
      have hs_nonneg : (0 : ℝ) ≤ (s : ℝ) := by positivity
      have hK_nonneg : (0 : ℝ) ≤ (K : ℝ) := by positivity
      have hmul1 : (s : ℝ) * Real.log (s : ℝ) ≤ (s : ℝ) * (s : ℝ) :=
        mul_le_mul_of_nonneg_left hlog_le_s hs_nonneg
      have hmul2 : (K : ℝ) * ((s : ℝ) * Real.log (s : ℝ)) ≤ (K : ℝ) * ((s : ℝ) * (s : ℝ)) :=
        mul_le_mul_of_nonneg_left hmul1 hK_nonneg
      simpa [A, pow_two, mul_assoc, mul_left_comm, mul_comm] using hmul2
    have hA_nonneg : (0 : ℝ) ≤ A := by
      have h : (0 : ℝ) ≤ 2 * Real.log 2 := by
        have hlog2pos : (0 : ℝ) < Real.log 2 := by
          have : (1 : ℝ) < (2 : ℝ) := by norm_num
          exact Real.log_pos this
        nlinarith
      exact le_trans h hA_ge
    -- use rpow monotonicity with exponent m and then convert to nat pow
    have hpow_le_rpow : (A : ℝ) ^ (m : ℝ) ≤ ((K : ℝ) * (s : ℝ) ^ 2) ^ (m : ℝ) := by
      exact Real.rpow_le_rpow hA_nonneg hA_le hm_nonneg
    have hpow_le : A ^ m ≤ ((K : ℝ) * (s : ℝ) ^ 2) ^ m := by
      -- rewrite both sides with `Real.rpow_natCast`
      simpa [Real.rpow_natCast] using hpow_le_rpow
    -- expand RHS
    calc
      A ^ m ≤ ((K : ℝ) * (s : ℝ) ^ 2) ^ m := hpow_le
      _ = (K : ℝ) ^ m * ((s : ℝ) ^ 2) ^ m := by
        simpa using (mul_pow (K : ℝ) ((s : ℝ) ^ 2) m)
      _ = (K : ℝ) ^ m * (s : ℝ) ^ (2 * m) := by
        -- (s^2)^m = s^(2*m)
        simpa using congrArg (fun t => (K : ℝ) ^ m * t) ((pow_mul (s : ℝ) 2 m).symm)
  -- final assembly
  calc
    Real.rpow (Real.log (Real.exp 1 + (r : ℝ))) q ≤ (C1 * A) ^ m := hq_le_pow
    _ = (C1 ^ m) * (A ^ m) := hpow
    _ ≤ (C1 ^ m) * ((K : ℝ) ^ m * (s : ℝ) ^ (2 * m)) := by
      have hC1_nonneg : (0 : ℝ) ≤ C1 ^ m := by
        have hlogexp_nonneg : (0 : ℝ) ≤ Real.log (Real.exp 1 + 2) := by
          have hpos : (1 : ℝ) < Real.exp 1 + 2 := by
            have : (0 : ℝ) < Real.exp 1 := by positivity
            linarith
          exact le_of_lt (Real.log_pos hpos)
        have hden_pos : (0 : ℝ) < 2 * Real.log 2 := by
          have hlog2pos : (0 : ℝ) < Real.log 2 := by
            have : (1 : ℝ) < (2 : ℝ) := by norm_num
            exact Real.log_pos this
          nlinarith
        have hfrac_nonneg : (0 : ℝ) ≤ Real.log (Real.exp 1 + 2) / (2 * Real.log 2) := by
          exact div_nonneg hlogexp_nonneg (le_of_lt hden_pos)
        have hC1_nonneg' : (0 : ℝ) ≤ C1 := by
          nlinarith [C1, hfrac_nonneg]
        exact pow_nonneg hC1_nonneg' m
      exact mul_le_mul_of_nonneg_left hA_pow hC1_nonneg
    _ = (C1 ^ m) * (K : ℝ) ^ m * (s : ℝ) ^ (2 * m) := by
      simp [mul_assoc]
    _ = ((1 + Real.log (Real.exp 1 + 2) / (2 * Real.log 2)) ^ m) * (K : ℝ) ^ m * (s : ℝ) ^ (2 * m) := by
      simp [C1]


theorem thm2_succ_le_two_pow (s : ℕ) (hs : s ≥ 1) : (s + 1 : ℝ) ≤ (2 : ℝ) ^ s := by
  have hnat : s + 1 ≤ 2 ^ s := by
    simpa [Nat.choose_one_right] using (Nat.choose_succ_le_two_pow s 1)
  exact_mod_cast hnat

theorem thm2_power_compare_core (K s : ℕ) (X : ℝ)
  (hs : s ≥ 2)
  (hX0 : 0 ≤ X)
  (hXs : (2:ℝ) * X ≤ (s : ℝ) ^ K) :
  (s + 1 : ℝ) * X ^ s ≤ (s : ℝ) ^ (K * s) := by
  classical
  have hs1 : s ≥ 1 := by
    omega
  have hsucc : (s + 1 : ℝ) ≤ (2 : ℝ) ^ s := thm2_succ_le_two_pow s hs1
  have hXpow : 0 ≤ X ^ s := by
    exact pow_nonneg hX0 s
  have hmul1 : (s + 1 : ℝ) * X ^ s ≤ (2 : ℝ) ^ s * X ^ s := by
    exact mul_le_mul_of_nonneg_right hsucc hXpow
  have hmulpow : (2 : ℝ) ^ s * X ^ s = (2 * X) ^ s := by
    simpa using (mul_pow (2 : ℝ) X s).symm
  have h0 : 0 ≤ (2 : ℝ) * X := by
    nlinarith
  have hpow : ((2 : ℝ) * X) ^ s ≤ ((s : ℝ) ^ K) ^ s := by
    exact (pow_le_pow_left₀ h0 hXs s)
  have hpow' : ((s : ℝ) ^ K) ^ s = (s : ℝ) ^ (K * s) := by
    simpa [pow_mul, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using (pow_mul (s : ℝ) K s).symm
  calc
    (s + 1 : ℝ) * X ^ s ≤ (2 : ℝ) ^ s * X ^ s := hmul1
    _ = ((2 : ℝ) * X) ^ s := hmulpow
    _ ≤ ((s : ℝ) ^ K) ^ s := hpow
    _ = (s : ℝ) ^ (K * s) := hpow'


theorem thm2_s_le_two_pow (s : ℕ) (hs : s ≥ 1) : (s : ℝ) ≤ (2 : ℝ) ^ s := by
  have h := thm2_succ_le_two_pow s hs
  -- h : (s + 1 : ℝ) ≤ (2 : ℝ) ^ s
  linarith

theorem thm2_two_pow_le_s_pow (s t : ℕ) (hs : s ≥ 2) : (2:ℝ) ^ t ≤ (s:ℝ) ^ t := by
  have hs2 : (2 : ℝ) ≤ (s : ℝ) := by
    exact_mod_cast hs
  have h0 : (0 : ℝ) ≤ (2 : ℝ) := by
    norm_num
  simpa using (pow_le_pow_left₀ h0 hs2 t)


theorem thm2_two_mul_X_le_s_pow_K (n m K s : ℕ) (c : ℝ)
  (hc : 0 < c) (hs : s ≥ 2) (hKm : 2 * m + 2 ≤ K)
  (hK : (2:ℝ)^K ≥ ((2*n : ℝ) + c * ((1 + (Real.log (Real.exp 1 + 2)) / (2 * Real.log 2)) ^ m)) * (K:ℝ)^m * (2:ℝ)^(2*m+1)) :
  (2:ℝ) * (((2*n : ℝ) + c * ((1 + (Real.log (Real.exp 1 + 2)) / (2 * Real.log 2)) ^ m)) * (K:ℝ)^m * (s:ℝ)^(2*m)) ≤ (s : ℝ) ^ K := by
  classical
  set B : ℝ :=
    (2 * n : ℝ) + c * ((1 + Real.log (Real.exp 1 + 2) / (2 * Real.log 2)) ^ m)
  have h2mK : 2 * m ≤ K := by
    exact Nat.le_trans (Nat.le_add_right (2 * m) 2) hKm
  have hs2 : (2 : ℝ) ≤ (s : ℝ) := by
    exact_mod_cast hs

  have hK' : B * (K : ℝ) ^ m * (2 : ℝ) ^ (2 * m + 1) ≤ (2 : ℝ) ^ K := by
    simpa [B] using hK

  have hpow2m1 : (2 : ℝ) ^ (2 * m + 1) = (2 : ℝ) * (2 : ℝ) ^ (2 * m) := by
    calc
      (2 : ℝ) ^ (2 * m + 1) = (2 : ℝ) ^ (1 + 2 * m) := by
        simpa using congrArg (fun t : ℕ => (2 : ℝ) ^ t) (Nat.add_comm (2 * m) 1)
      _ = (2 : ℝ) ^ 1 * (2 : ℝ) ^ (2 * m) := by
        simpa [pow_add]
      _ = (2 : ℝ) * (2 : ℝ) ^ (2 * m) := by
        simp

  have hKfac : (B * (K : ℝ) ^ m * (2 : ℝ)) * (2 : ℝ) ^ (2 * m) ≤
      (2 : ℝ) ^ (K - 2 * m) * (2 : ℝ) ^ (2 * m) := by
    -- Start from hK'
    have h0 : B * (K : ℝ) ^ m * ((2 : ℝ) * (2 : ℝ) ^ (2 * m)) ≤ (2 : ℝ) ^ K := by
      simpa [hpow2m1, mul_assoc] using hK'
    have h1 : (B * (K : ℝ) ^ m * (2 : ℝ)) * (2 : ℝ) ^ (2 * m) ≤ (2 : ℝ) ^ K := by
      simpa [mul_assoc] using h0
    -- Rewrite RHS exponent only
    have h1' : (B * (K : ℝ) ^ m * (2 : ℝ)) * (2 : ℝ) ^ (2 * m) ≤ (2 : ℝ) ^ ((K - 2 * m) + 2 * m) := by
      -- rewrite only the RHS
      -- (Nat.sub_add_cancel h2mK) : K - 2*m + 2*m = K
      -- so rewrite K as (K - 2*m) + 2*m
      simpa using (by
        -- use rw at the RHS of the inequality
        -- Note: rw rewrites all occurrences, but K occurs only in the exponent on RHS
        -- in this inequality
        -- We'll use `nth_rw` to be safe
        nth_rewrite 2 [show K = (K - 2 * m) + 2 * m from (Nat.sub_add_cancel h2mK).symm] at h1
        exact h1)
    -- Expand pow_add
    simpa [pow_add] using h1'

  have hpos : 0 < (2 : ℝ) ^ (2 * m) := by
    have h2 : (0 : ℝ) < (2 : ℝ) := by norm_num
    exact pow_pos h2 (2 * m)

  have hcancel : B * (K : ℝ) ^ m * (2 : ℝ) ≤ (2 : ℝ) ^ (K - 2 * m) := by
    exact le_of_mul_le_mul_right hKfac hpos

  have hpow_up : (2 : ℝ) ^ (K - 2 * m) ≤ (s : ℝ) ^ (K - 2 * m) := by
    have h2nonneg : (0 : ℝ) ≤ (2 : ℝ) := by norm_num
    exact pow_le_pow_left₀ h2nonneg hs2 (K - 2 * m)

  have hmain : B * (K : ℝ) ^ m * (2 : ℝ) ≤ (s : ℝ) ^ (K - 2 * m) :=
    le_trans hcancel hpow_up

  have hs_nonneg : (0 : ℝ) ≤ (s : ℝ) := by positivity
  have hmul : (B * (K : ℝ) ^ m * (2 : ℝ)) * (s : ℝ) ^ (2 * m) ≤
      (s : ℝ) ^ (K - 2 * m) * (s : ℝ) ^ (2 * m) := by
    exact mul_le_mul_of_nonneg_right hmain (pow_nonneg hs_nonneg (2 * m))

  calc
    (2 : ℝ) * (B * (K : ℝ) ^ m * (s : ℝ) ^ (2 * m)) =
        (B * (K : ℝ) ^ m * (2 : ℝ)) * (s : ℝ) ^ (2 * m) := by
          ac_rfl
    _ ≤ (s : ℝ) ^ (K - 2 * m) * (s : ℝ) ^ (2 * m) := hmul
    _ = (s : ℝ) ^ K := by
          simpa [Nat.sub_add_cancel h2mK, pow_add, mul_assoc] using
            (pow_add (s : ℝ) (K - 2 * m) (2 * m)).symm

theorem thm2_power_compare (n m K s : ℕ) (c : ℝ)
  (hc : 0 < c) (hs : s ≥ 2) (hKm : 2 * m + 2 ≤ K)
  (hK : (2:ℝ)^K ≥ ((2*n : ℝ) + c * ((1 + (Real.log (Real.exp 1 + 2)) / (2 * Real.log 2)) ^ m)) * (K:ℝ)^m * (2:ℝ)^(2*m+1)) :
  (s + 1) * (((2*n : ℝ) + c * ((1 + (Real.log (Real.exp 1 + 2)) / (2 * Real.log 2)) ^ m)) * (K:ℝ)^m * (s:ℝ)^(2*m)) ^ s
    ≤ Real.exp (K * s * Real.log s) := by
  classical
  -- shorthand for the constant appearing in the statement
  set B : ℝ := (1 + (Real.log (Real.exp 1 + 2)) / (2 * Real.log 2))

  have hB0 : 0 ≤ B := by
    have h1 : (1 : ℝ) ≤ Real.exp 1 + 2 := by
      nlinarith [Real.exp_pos 1]
    have hlog : 0 ≤ Real.log (Real.exp 1 + 2) := by
      exact Real.log_nonneg h1
    have hlog2pos : 0 < Real.log 2 := by
      have : (1 : ℝ) < (2 : ℝ) := by
        norm_num
      exact Real.log_pos this
    have hdenpos : 0 < (2 * Real.log 2) := by
      nlinarith
    have hfrac : 0 ≤ Real.log (Real.exp 1 + 2) / (2 * Real.log 2) := by
      exact div_nonneg hlog (le_of_lt hdenpos)
    have : (0 : ℝ) ≤ 1 + Real.log (Real.exp 1 + 2) / (2 * Real.log 2) := by
      nlinarith
    simpa [B] using this

  -- Define X as in the informal proof
  set X : ℝ :=
    ((2 * n : ℝ) + c * B ^ m) * (K : ℝ) ^ m * (s : ℝ) ^ (2 * m)

  have hX0 : 0 ≤ X := by
    have hc0 : 0 ≤ c := le_of_lt hc
    have hBpow : 0 ≤ B ^ m := by
      exact pow_nonneg hB0 m
    have hsum : 0 ≤ (2 * n : ℝ) + c * B ^ m := by
      have : 0 ≤ (2 * n : ℝ) := by positivity
      have : 0 ≤ c * B ^ m := by
        exact mul_nonneg hc0 hBpow
      nlinarith
    have hKpow : 0 ≤ (K : ℝ) ^ m := by
      exact pow_nonneg (by positivity : (0 : ℝ) ≤ (K : ℝ)) m
    have hspow : 0 ≤ (s : ℝ) ^ (2 * m) := by
      exact pow_nonneg (by positivity : (0 : ℝ) ≤ (s : ℝ)) (2 * m)
    -- assemble
    exact mul_nonneg (mul_nonneg hsum hKpow) hspow

  have hs1 : s ≥ 1 := by
    omega

  have hXs : (2 : ℝ) * X ≤ (s : ℝ) ^ K := by
    simpa [X, B] using
      thm2_two_mul_X_le_s_pow_K (n := n) (m := m) (K := K) (s := s) (c := c) hc hs hKm hK

  -- Convert the RHS exponential into a power
  rw [thm2_exp_Kslog_eq_pow K s hs1]

  -- Apply the core comparison lemma
  simpa [X, B] using (thm2_power_compare_core (K := K) (s := s) (X := X) hs hX0 hXs)


theorem thm2_rhs_le_exp (n : ℕ) (c q : ℝ) (m K s : ℕ)
  (hc : 0 < c) (hs : s ≥ 2) (hq : q ≤ (m : ℝ)) (hKm : 2 * m + 2 ≤ K)
  (hK : (2:ℝ)^K > ((2*n : ℝ) + c * ((1 + (Real.log (Real.exp 1 + 2)) / (2 * Real.log 2)) ^ m)) * (K:ℝ)^m * (2:ℝ)^(2*m+1)) :
  let r : ℕ := 1 + Int.toNat (Int.floor (Real.exp (K * s * Real.log s)))
  (s + 1) * ((n : ℝ) + c * Real.rpow (Real.log (Real.exp 1 + r)) q + n) ^ s
    ≤ Real.exp (K * s * Real.log s) := by
  classical
  let r : ℕ := 1 + Int.toNat (Int.floor (Real.exp (K * s * Real.log s)))
  have hKpos : 0 < K := by omega
  have hrpow : Real.rpow (Real.log (Real.exp 1 + r)) q ≤
      ((1 + (Real.log (Real.exp 1 + 2)) / (2 * Real.log 2)) ^ m) * (K : ℝ) ^ m * (s : ℝ) ^ (2 * m) := by
    simpa [r] using (thm2_rpow_log_bound q m K s hKpos hs hq)
  set B : ℝ := (1 + (Real.log (Real.exp 1 + 2)) / (2 * Real.log 2)) ^ m
  set P : ℝ := (K : ℝ) ^ m * (s : ℝ) ^ (2 * m)

  have hrpowc : c * Real.rpow (Real.log (Real.exp 1 + r)) q ≤ c * (B * P) := by
    have := mul_le_mul_of_nonneg_left hrpow (le_of_lt hc)
    simpa [B, P, mul_assoc, mul_left_comm, mul_comm] using this
  have hsum : (2 * n : ℝ) + c * Real.rpow (Real.log (Real.exp 1 + r)) q ≤ (2 * n : ℝ) + c * (B * P) := by
    simpa [add_assoc, add_comm, add_left_comm] using (add_le_add_left hrpowc (2 * n : ℝ))
  have hrewrite : (n : ℝ) + c * Real.rpow (Real.log (Real.exp 1 + r)) q + n = (2 * n : ℝ) + c * Real.rpow (Real.log (Real.exp 1 + r)) q := by
    ring
  have hinner1 : (n : ℝ) + c * Real.rpow (Real.log (Real.exp 1 + r)) q + n ≤ (2 * n : ℝ) + c * (B * P) := by
    rw [hrewrite]
    exact hsum

  have hK1Nat : (1 : ℕ) ≤ K := by omega
  have hs1Nat : (1 : ℕ) ≤ s := by omega
  have hK1 : (1 : ℝ) ≤ (K : ℝ) ^ m := by
    have hKbase : (1 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK1Nat
    simpa using (one_le_pow₀ hKbase (n := m))
  have hs1 : (1 : ℝ) ≤ (s : ℝ) ^ (2 * m) := by
    have hsbase : (1 : ℝ) ≤ (s : ℝ) := by exact_mod_cast hs1Nat
    simpa using (one_le_pow₀ hsbase (n := 2 * m))
  have hP1 : (1 : ℝ) ≤ P := by
    simpa [P] using (one_le_mul_of_one_le_of_one_le hK1 hs1)
  have h2n_nonneg : 0 ≤ (2 * n : ℝ) := by positivity
  have h2n_le : (2 * n : ℝ) ≤ (2 * n : ℝ) * P := by
    have := mul_le_mul_of_nonneg_left hP1 h2n_nonneg
    simpa [mul_one, mul_assoc, mul_left_comm, mul_comm] using this
  have hbound2 : (2 * n : ℝ) + c * (B * P) ≤ ((2 * n : ℝ) + c * B) * P := by
    have hstep : (2 * n : ℝ) + c * (B * P) ≤ (2 * n : ℝ) * P + c * (B * P) := by
      simpa [add_comm, add_left_comm, add_assoc] using (add_le_add_right h2n_le (c * (B * P)))
    have hring : (2 * n : ℝ) * P + c * (B * P) = ((2 * n : ℝ) + c * B) * P := by
      ring
    exact le_trans hstep (le_of_eq hring)

  have hinner_le : (n : ℝ) + c * Real.rpow (Real.log (Real.exp 1 + r)) q + n ≤
      ((2 * n : ℝ) + c * B) * P := by
    exact le_trans hinner1 hbound2

  -- prepare to apply thm2_power_compare
  have hK' : (2 : ℝ) ^ K ≥ ((2 * n : ℝ) + c * B) * (K : ℝ) ^ m * (2 : ℝ) ^ (2 * m + 1) := by
    have := le_of_lt hK
    simpa [B, mul_assoc, mul_left_comm, mul_comm, add_assoc, add_left_comm, add_comm] using this

  have hmain : (s + 1) * (((2 * n : ℝ) + c * B) * (K : ℝ) ^ m * (s : ℝ) ^ (2 * m)) ^ s ≤
      Real.exp (K * s * Real.log s) := by
    simpa [B, mul_assoc, mul_left_comm, mul_comm] using
      (thm2_power_compare n m K s c hc hs hKm (by
        simpa [B, mul_assoc, mul_left_comm, mul_comm] using hK'))

  -- show the inside is nonnegative
  have hnonneg_inner : 0 ≤ (n : ℝ) + c * Real.rpow (Real.log (Real.exp 1 + r)) q + n := by
    have hn : 0 ≤ (n : ℝ) := by positivity
    have hc0 : 0 ≤ c := le_of_lt hc
    have h1exp : (1 : ℝ) ≤ Real.exp 1 := by
      have : (0 : ℝ) ≤ (1 : ℝ) := by norm_num
      simpa using (Real.one_le_exp_iff.2 this)
    have hr0 : (0 : ℝ) ≤ r := by positivity
    have h1 : (1 : ℝ) ≤ Real.exp 1 + r := by linarith
    have hlog0 : 0 ≤ Real.log (Real.exp 1 + r) := Real.log_nonneg h1
    have hrpow0 : 0 ≤ Real.rpow (Real.log (Real.exp 1 + r)) q := by
      simpa using (Real.rpow_nonneg hlog0 q)
    have hcmul0 : 0 ≤ c * Real.rpow (Real.log (Real.exp 1 + r)) q := by
      exact mul_nonneg hc0 hrpow0
    have hsum0 : 0 ≤ (n : ℝ) + c * Real.rpow (Real.log (Real.exp 1 + r)) q := by
      exact add_nonneg hn hcmul0
    exact add_nonneg hsum0 hn

  have hinner_le' : (n : ℝ) + c * Real.rpow (Real.log (Real.exp 1 + r)) q + n ≤
      ((2 * n : ℝ) + c * B) * (K : ℝ) ^ m * (s : ℝ) ^ (2 * m) := by
    -- rewrite RHS using P
    simpa [P, mul_assoc] using hinner_le

  have hpow : ((n : ℝ) + c * Real.rpow (Real.log (Real.exp 1 + r)) q + n) ^ s ≤
      (((2 * n : ℝ) + c * B) * (K : ℝ) ^ m * (s : ℝ) ^ (2 * m)) ^ s := by
    have := pow_le_pow_left₀ hnonneg_inner hinner_le' s
    simpa using this

  have hmul : (s + 1) * ((n : ℝ) + c * Real.rpow (Real.log (Real.exp 1 + r)) q + n) ^ s ≤
      (s + 1) * (((2 * n : ℝ) + c * B) * (K : ℝ) ^ m * (s : ℝ) ^ (2 * m)) ^ s := by
    have hsnonneg : 0 ≤ (s + 1 : ℝ) := by positivity
    exact mul_le_mul_of_nonneg_left hpow hsnonneg

  have hfinal : (s + 1) * ((n : ℝ) + c * Real.rpow (Real.log (Real.exp 1 + r)) q + n) ^ s ≤
      Real.exp (K * s * Real.log s) := by
    exact le_trans hmul hmain

  simpa [r] using hfinal

theorem thm2_growth_lemma_choose_K (n : ℕ) (c q : ℝ) (hc : 0 < c) (hq : 0 < q) :
  ∃ K : ℕ, 0 < K ∧
    ∀ s : ℕ, s ≥ 2 →
      let r : ℕ := 1 + Int.toNat (Int.floor (Real.exp (K * s * Real.log s)))
      (r + 1 : ℝ) > (s + 1) * ((n : ℝ) + c * (Real.rpow (Real.log ((Real.exp 1) + r)) q) + n) ^ s := by
  classical
  let m : ℕ := Nat.ceil q
  have hm : q ≤ (m : ℝ) := by
    simpa [m] using (Nat.le_ceil q)
  let C1 : ℝ := 1 + Real.log (Real.exp 1 + 2) / (2 * Real.log 2)
  let B0 : ℝ := ((2 * n : ℝ) + c * (C1 ^ m)) * (2 : ℝ) ^ (2 * m + 1)
  let B : ℝ := |B0| + 1
  have hB : 0 < B := by
    have : (0 : ℝ) < |B0| + 1 := by
      linarith [abs_nonneg B0]
    simpa [B] using this
  rcases thm2_exists_nat_two_pow_gt_poly m (2 * m + 2) B hB with ⟨K, hKm, hKbig⟩
  have hKpos : 0 < K := by
    have hT : 0 < 2 * m + 2 := by
      omega
    exact lt_of_lt_of_le hT hKm
  refine ⟨K, hKpos, ?_⟩
  intro s hs
  have hpow_nonneg : (0 : ℝ) ≤ (K : ℝ) ^ m := by
    exact pow_nonneg (by positivity : (0 : ℝ) ≤ (K : ℝ)) m
  have hB0_le_B : B0 ≤ B := by
    have h1 : B0 ≤ |B0| := le_abs_self B0
    have h2 : (|B0| : ℝ) ≤ |B0| + 1 := by
      linarith
    have h3 : B0 ≤ |B0| + 1 := le_trans h1 h2
    simpa [B] using h3
  have hmul_le : B0 * (K : ℝ) ^ m ≤ B * (K : ℝ) ^ m := by
    exact mul_le_mul_of_nonneg_right hB0_le_B hpow_nonneg
  have hKreq : (2 : ℝ) ^ K > B0 * (K : ℝ) ^ m := by
    exact lt_of_le_of_lt hmul_le hKbig
  have hK_for_rhs :
      (2 : ℝ) ^ K >
        ((2 * n : ℝ) + c * ((1 + Real.log (Real.exp 1 + 2) / (2 * Real.log 2)) ^ m)) *
            (K : ℝ) ^ m * (2 : ℝ) ^ (2 * m + 1) := by
    -- rewrite hKreq using B0's definition and swap the last two factors
    have hKreq' :
        (2 : ℝ) ^ K >
          ((2 * n : ℝ) + c * ((1 + Real.log (Real.exp 1 + 2) / (2 * Real.log 2)) ^ m)) *
              (2 : ℝ) ^ (2 * m + 1) * (K : ℝ) ^ m := by
      simpa [B0, C1, mul_assoc] using hKreq
    -- now commute (2^...) and (K^m)
    simpa [mul_right_comm, mul_assoc] using hKreq'
  have hle_exp := thm2_rhs_le_exp n c q m K s hc hs hm hKm hK_for_rhs
  have h_exp_lt := thm2_r_add_one_gt_exp K s
  dsimp at hle_exp h_exp_lt ⊢
  exact lt_of_le_of_lt hle_exp h_exp_lt

theorem theorem_2_quasi_exponential_expansion (n : ℕ)
  (h1 : 1 ≤ n)
  (M : Set (FreeAbelianMonoid n))
  (c q : ℝ) (hc : 0 < c) (hq : 0 < q):
  (∀ (r : ℕ), (M ∩ (Ball r (A n))).ncard ≤ c * (Real.rpow (Real.log ((Real.exp 1) + r)) q)) →
    (∃ (K : ℕ), ∀ (s : ℕ), (s ≥ 2) → ((K > 0) ∧
      let r := 1 + Int.toNat <| Int.floor <| Real.exp (K * s * (Real.log s))
      ¬ (Ball r (A n) ⊆ Ball s (M ∪ (A n))))) := by
  intro hM
  classical
  rcases thm2_growth_lemma_choose_K n c q hc hq with ⟨K, hKpos, hKgrowth⟩
  refine ⟨K, ?_⟩
  intro s hs
  refine ⟨hKpos, ?_⟩
  dsimp
  set r : ℕ := 1 + Int.toNat (Int.floor (Real.exp (K * s * Real.log s))) with hr
  have hgrow : (r + 1 : ℝ) > (s + 1) * ((n : ℝ) + c * (Real.rpow (Real.log (Real.exp 1 + r)) q) + n) ^ s := by
    simpa [r, hr] using (hKgrowth s hs)
  intro hsub
  have hsub' : Ball r (A n) ⊆ Ball s (thm2RelevantGenerators n M r) :=
    thm2_ball_restrict_macros (n := n) (M := M) (r := r) (s := s) hsub
  have hlower : r + 1 ≤ (Ball r (A n)).ncard := thm2_ballA_ncard_lower_bound n r h1
  have hRel_finite : (thm2RelevantGenerators n M r).Finite := thm2RelevantGenerators_finite (n := n) M r
  have hBallS_finite : (Ball s (thm2RelevantGenerators n M r)).Finite :=
    thm2_ball_finite (n := n) s (thm2RelevantGenerators n M r) hRel_finite
  have hcard_le : (Ball r (A n)).ncard ≤ (Ball s (thm2RelevantGenerators n M r)).ncard :=
    Set.ncard_le_ncard hsub' hBallS_finite
  have hub : (Ball s (thm2RelevantGenerators n M r)).ncard ≤ (s + 1) * ((thm2RelevantGenerators n M r).ncard + 1) ^ s :=
    thm2_ball_ncard_upper_bound (n := n) s (thm2RelevantGenerators n M r) hRel_finite
  have hnat : r + 1 ≤ (s + 1) * ((thm2RelevantGenerators n M r).ncard + 1) ^ s := by
    exact le_trans hlower (le_trans hcard_le hub)
  have hnatR : (r + 1 : ℝ) ≤ ((s + 1) * ((thm2RelevantGenerators n M r).ncard + 1) ^ s : ℕ) := by
    exact_mod_cast hnat
  have hnatR' : (r + 1 : ℝ) ≤ (s + 1 : ℝ) * (((thm2RelevantGenerators n M r).ncard + 1 : ℕ) : ℝ) ^ s := by
    simpa [Nat.cast_mul, Nat.cast_pow] using hnatR
  -- bound the relevant generators
  have hRel_ncard_le : (thm2RelevantGenerators n M r).ncard ≤ (M ∩ Ball r (A n)).ncard + n :=
    thm2RelevantGenerators_ncard_le (n := n) M r
  have hRel_succ_le_nat : (thm2RelevantGenerators n M r).ncard + 1 ≤ (M ∩ Ball r (A n)).ncard + n + 1 :=
    Nat.succ_le_succ hRel_ncard_le
  have hRel_succ_le_R : (((thm2RelevantGenerators n M r).ncard + 1 : ℕ) : ℝ) ≤ ((M ∩ Ball r (A n)).ncard + n + 1 : ℕ) := by
    exact_mod_cast hRel_succ_le_nat
  have hRel_succ_le_R' : (((thm2RelevantGenerators n M r).ncard + 1 : ℕ) : ℝ) ≤ ((M ∩ Ball r (A n)).ncard : ℝ) + n + 1 := by
    simpa [Nat.cast_add, add_assoc] using hRel_succ_le_R
  have hM_r : ((M ∩ Ball r (A n)).ncard : ℝ) ≤ c * Real.rpow (Real.log (Real.exp 1 + r)) q := hM r
  have hRel_succ_le_R2 : (((thm2RelevantGenerators n M r).ncard + 1 : ℕ) : ℝ) ≤ c * Real.rpow (Real.log (Real.exp 1 + r)) q + n + 1 := by
    have hM_r' : ((M ∩ Ball r (A n)).ncard : ℝ) + n + 1 ≤ c * Real.rpow (Real.log (Real.exp 1 + r)) q + n + 1 := by
      have h1' := add_le_add_right hM_r (n : ℝ)
      have h2' := add_le_add_right h1' (1 : ℝ)
      simpa [add_assoc, add_left_comm, add_comm] using h2'
    exact le_trans hRel_succ_le_R' hM_r'
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast h1
  have hRel_succ_le_base : (((thm2RelevantGenerators n M r).ncard + 1 : ℕ) : ℝ) ≤ (n : ℝ) + c * Real.rpow (Real.log (Real.exp 1 + r)) q + n := by
    have hn_add : (n : ℝ) + 1 ≤ (n : ℝ) + (n : ℝ) := by
      have htemp := add_le_add_left hn1 (n : ℝ)
      -- htemp has the left term as `1 + n`; commute it
      simpa [add_assoc, add_left_comm, add_comm] using htemp
    have hadd : c * Real.rpow (Real.log (Real.exp 1 + r)) q + n + 1 ≤
        c * Real.rpow (Real.log (Real.exp 1 + r)) q + n + n := by
      have := add_le_add_left hn_add (c * Real.rpow (Real.log (Real.exp 1 + r)) q)
      simpa [add_assoc] using this
    have htmp : (((thm2RelevantGenerators n M r).ncard + 1 : ℕ) : ℝ) ≤
        c * Real.rpow (Real.log (Real.exp 1 + r)) q + n + n :=
      le_trans hRel_succ_le_R2 hadd
    simpa [add_assoc, add_left_comm, add_comm] using htmp
  -- raise to the power `s`
  have hpow : (((thm2RelevantGenerators n M r).ncard + 1 : ℕ) : ℝ) ^ s ≤
      ((n : ℝ) + c * Real.rpow (Real.log (Real.exp 1 + r)) q + n) ^ s := by
    have ha0 : (0 : ℝ) ≤ (((thm2RelevantGenerators n M r).ncard + 1 : ℕ) : ℝ) := by
      positivity
    simpa using (pow_le_pow_left₀ ha0 hRel_succ_le_base s)
  have hmul : (s + 1 : ℝ) * (((thm2RelevantGenerators n M r).ncard + 1 : ℕ) : ℝ) ^ s ≤
      (s + 1 : ℝ) * ((n : ℝ) + c * Real.rpow (Real.log (Real.exp 1 + r)) q + n) ^ s := by
    have hs0 : (0 : ℝ) ≤ (s + 1 : ℝ) := by positivity
    exact mul_le_mul_of_nonneg_left hpow hs0
  have hfinal : (r + 1 : ℝ) ≤ (s + 1 : ℝ) * ((n : ℝ) + c * Real.rpow (Real.log (Real.exp 1 + r)) q + n) ^ s :=
    le_trans hnatR' hmul
  exact (not_lt_of_ge hfinal) hgrow


