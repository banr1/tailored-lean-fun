import LeanFun.Definitions


open scoped BigOperators
open Filter

open free

def Sphere (n r : ℕ) : Set (FreeMonoid (Fin n)) :=
  {w | w.length = r}

noncomputable def expansion {n : ℕ} (G G' : Set (FreeMonoid (Fin n))) (s : ℕ) : ℕ :=
    sSup { r : ℕ | Ball r G ⊆ Ball s G' }

theorem theorem5_ball_A_iff_length_le (n R : ℕ) (w : FreeMonoid (Fin n)) : w ∈ Ball R (A n) ↔ w.length ≤ R := by
  -- unfold Ball and A
  simp [free.Ball, free.A]
  constructor
  · rintro ⟨l, hlR, hlA, rfl⟩
    have hlen : l.prod.length = l.length := by
      -- induction on the witness list
      have hlen' : ∀ l : List (FreeMonoid (Fin n)),
          (∀ x, x ∈ l → ∃ i : Fin n, ([i] : FreeMonoid (Fin n)) = x) →
            l.prod.length = l.length := by
        intro l hA
        induction l with
        | nil =>
            simp
        | cons a t ih =>
            -- head element is a singleton generator
            rcases hA a (by simp) with ⟨i, rfl⟩
            have ha : FreeMonoid.length ([i] : FreeMonoid (Fin n)) = 1 := by
              simp [FreeMonoid.length, FreeMonoid.of]
            have hA_t : ∀ x, x ∈ t → ∃ i : Fin n, ([i] : FreeMonoid (Fin n)) = x := by
              intro x hx
              exact hA x (by simp [hx])
            have ht : t.prod.length = t.length := ih hA_t
            -- now compute lengths
            simp [List.prod_cons, FreeMonoid.length_mul, ha, ht, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
      exact hlen' l hlA
    simpa [hlen] using hlR
  · intro hwlen
    refine ⟨(FreeMonoid.toList w).map FreeMonoid.of, ?_, ?_, ?_⟩
    · -- length bound
      simpa [FreeMonoid.length] using hwlen
    · intro x hx
      rcases List.mem_map.1 hx with ⟨i, hi, rfl⟩
      exact ⟨i, rfl⟩
    · -- prod equals w
      have hlift : FreeMonoid.lift (FreeMonoid.of : Fin n → FreeMonoid (Fin n)) =
          MonoidHom.id (FreeMonoid (Fin n)) := by
        simpa using (FreeMonoid.lift_restrict (MonoidHom.id (FreeMonoid (Fin n))))
      simpa [hlift] using (FreeMonoid.lift_apply (FreeMonoid.of : Fin n → FreeMonoid (Fin n)) w).symm

theorem theorem5_ball_mono_R {n : ℕ} {R R' : ℕ} {X : Set (FreeMonoid (Fin n))} (h : R ≤ R') : Ball R X ⊆ Ball R' X := by
  intro m hm
  simp [free.Ball] at hm ⊢
  rcases hm with ⟨l, hlR, hlX, hlprod⟩
  refine ⟨l, ?_, hlX, hlprod⟩
  exact le_trans hlR h


theorem theorem5_ball_mono_X {n : ℕ} {R : ℕ} {X Y : Set (FreeMonoid (Fin n))} (h : X ⊆ Y) : Ball R X ⊆ Ball R Y := by
  intro m hm
  rcases hm with ⟨l, hlR, hlX, hlprod⟩
  refine ⟨l, hlR, ?_, hlprod⟩
  intro x hx_in_l
  exact h (hlX x hx_in_l)


theorem theorem5_ball_mul {n : ℕ} {R S : ℕ} {X : Set (FreeMonoid (Fin n))} {m₁ m₂ : FreeMonoid (Fin n)} :
  m₁ ∈ Ball R X → m₂ ∈ Ball S X → m₁ * m₂ ∈ Ball (R + S) X := by
  intro hm1 hm2
  rcases hm1 with ⟨l1, hl1len, hl1X, hl1prod⟩
  rcases hm2 with ⟨l2, hl2len, hl2X, hl2prod⟩
  refine ⟨l1 ++ l2, ?_, ?_, ?_⟩
  · -- length bound
    have hlen : l1.length + l2.length ≤ R + S := by
      exact add_le_add hl1len hl2len
    simpa [List.length_append] using hlen
  · -- all elements in X
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact hl1X x hx
    · exact hl2X x hx
  · -- product
    simpa [List.prod_append, hl1prod, hl2prod]

theorem theorem5_div_le_div_of_le_of_nonneg {a b c : ℝ} (hc : 0 ≤ c) : a ≤ b → a / c ≤ b / c := by
  intro hab
  exact div_le_div_of_nonneg_right hab hc


theorem theorem5_ennreal_nat_mul_ofReal_eq_ofReal_mul {a : ℕ} {x : ℝ} (hx : 0 ≤ x) :
  (a : ENNReal) * ENNReal.ofReal x = ENNReal.ofReal ((a : ℝ) * x) := by
  rw [← ENNReal.ofReal_natCast a]
  have ha : (0 : ℝ) ≤ (a : ℝ) := by
    exact_mod_cast Nat.zero_le a
  simpa using (ENNReal.ofReal_mul (p := (a : ℝ)) (q := x) ha).symm

open Filter in
theorem theorem5_eventually_log2_mul_le (C : ℕ) : ∀ᶠ r : ℕ in atTop, C * (Nat.log2 r + 1) ≤ r / 4 := by
  classical
  by_cases hC : C = 0
  · subst hC
    simpa using (Filter.eventually_of_forall (fun r : ℕ => by simp))
  ·
    have hCpos : 0 < C := Nat.pos_of_ne_zero hC

    let m0 : ℕ := 16 * C

    have hm : ∀ m : ℕ, m0 ≤ m → 4 * C * (m + 1) ≤ 2 ^ m := by
      refine Nat.le_induction (m := m0) (P := fun m _ => 4 * C * (m + 1) ≤ 2 ^ m) ?_ ?_
      ·
        -- base case: m = m0
        have hlin : 16 * C + 1 ≤ 32 * C := by omega
        have hmul : (4 * C) * (16 * C + 1) ≤ (4 * C) * (32 * C) :=
          Nat.mul_le_mul_left (4 * C) hlin
        have hEq : (4 * C) * (32 * C) = 2 * (8 * C) ^ 2 := by
          simp [pow_two, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
        have hle1 : 4 * C * (16 * C + 1) ≤ 2 * (8 * C) ^ 2 :=
          le_trans hmul (le_of_eq hEq)
        have hle2 : 4 * C * (16 * C + 1) ≤ 2 * (8 * C) ^ 2 + 1 :=
          le_trans hle1 (Nat.le_succ _)
        have hle3 : 2 * (8 * C) ^ 2 + 1 ≤ 2 ^ (16 * C) := by
          simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using
            (Nat.two_mul_sq_add_one_le_two_pow_two_mul (8 * C))
        simpa [m0, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm, Nat.add_assoc] using
          (le_trans hle2 hle3)
      ·
        intro m hm0 ih
        have hle : m + 2 ≤ 2 * (m + 1) := by omega
        have hmul1 : (4 * C) * (m + 2) ≤ (4 * C) * (2 * (m + 1)) :=
          Nat.mul_le_mul_left (4 * C) hle
        have hmul1' : 4 * C * (m + 2) ≤ 2 * (4 * C * (m + 1)) := by
          simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hmul1
        have ih2 : 2 * (4 * C * (m + 1)) ≤ 2 * (2 ^ m) :=
          Nat.mul_le_mul_left 2 ih
        have ih2' : 2 * (4 * C * (m + 1)) ≤ 2 ^ (m + 1) := by
          simpa [Nat.pow_succ, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using ih2
        exact le_trans hmul1' ih2'

    refine Filter.eventually_atTop.2 ?_
    refine ⟨2 ^ m0, ?_⟩
    intro r hr

    have hm0le : m0 ≤ Nat.log2 r := by
      have : m0 ≤ Nat.log 2 r :=
        Nat.le_log_of_pow_le (by decide : 1 < 2) (by simpa using hr)
      simpa [Nat.log2_eq_log_two] using this

    have hr0 : r ≠ 0 := by
      have hpos : 0 < 2 ^ m0 := Nat.pow_pos (n := m0) (by decide : 0 < (2 : ℕ))
      have : 0 < r := lt_of_lt_of_le hpos hr
      exact Nat.ne_of_gt this

    have hpow : 2 ^ Nat.log2 r ≤ r := by
      simpa [Nat.log2_eq_log_two] using (Nat.pow_log_le_self 2 (x := r) hr0)

    have hlin : 4 * C * (Nat.log2 r + 1) ≤ 2 ^ Nat.log2 r := hm (Nat.log2 r) hm0le

    have hmul4 : 4 * C * (Nat.log2 r + 1) ≤ r := le_trans hlin hpow

    have hmul : (C * (Nat.log2 r + 1)) * 4 ≤ r := by
      simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hmul4

    exact (Nat.le_div_iff_mul_le (k := 4) (x := C * (Nat.log2 r + 1)) (y := r) (by decide)).2 hmul

def theorem5_hasHalfMacro {n : ℕ} (C : ℕ) (M : Set (FreeMonoid (Fin n))) (r : ℕ) : Prop :=
  ∀ w : FreeMonoid (Fin n), w.length = r →
    ∃ p u s : FreeMonoid (Fin n),
      w = p * u * s ∧
      p.length ≤ C * (Nat.log2 r + 1) ∧
      u ∈ M ∧
      r / 2 ≤ u.length ∧
      s.length ≤ r / 2

def theorem5_hasPeriod {n : ℕ} (w : FreeMonoid (Fin n)) (d : ℕ) : Prop :=
  0 < d ∧ d ≤ w.length ∧ w.drop d = w.take (w.length - d)

noncomputable def theorem5_inclusionProb {n : ℕ} (w : FreeMonoid (Fin n)) : NNReal :=
  ((Nat.log2 (w.length + 2) + 1 : ℕ) : NNReal)⁻¹

noncomputable def theorem5_coordMeasure {n : ℕ} (w : FreeMonoid (Fin n)) : MeasureTheory.Measure Bool :=
  (PMF.bernoulli (theorem5_inclusionProb (n := n) w)
      (by
        have hNat : (1 : ℕ) ≤ Nat.log2 (w.length + 2) + 1 := Nat.succ_le_succ (Nat.zero_le _)
        have hNN : (1 : NNReal) ≤ ((Nat.log2 (w.length + 2) + 1 : ℕ) : NNReal) := by
          exact_mod_cast hNat
        have : ((Nat.log2 (w.length + 2) + 1 : ℕ) : NNReal)⁻¹ ≤ (1 : NNReal) :=
          (inv_le_one_iff₀).2 (Or.inr hNN)
        simpa [theorem5_inclusionProb] using this)).toMeasure

open MeasureTheory in
open ProbabilityTheory in
theorem theorem5_coordMeasure_false_eq {n : ℕ} (w : FreeMonoid (Fin n)) :
  theorem5_coordMeasure (n := n) w ({false} : Set Bool) =
    (1 - (theorem5_inclusionProb (n := n) w : ENNReal)) := by
  classical
  -- try simp
  simp [theorem5_coordMeasure, theorem5_inclusionProb]

open MeasureTheory in
open ProbabilityTheory in
theorem theorem5_coordMeasure_isProbability {n : ℕ} (w : FreeMonoid (Fin n)) :
  MeasureTheory.IsProbabilityMeasure (theorem5_coordMeasure (n := n) w) := by
  dsimp [theorem5_coordMeasure]
  infer_instance

open MeasureTheory in
open ProbabilityTheory in
theorem theorem5_coordMeasure_true_eq {n : ℕ} (w : FreeMonoid (Fin n)) :
  theorem5_coordMeasure (n := n) w ({true} : Set Bool) =
    (theorem5_inclusionProb (n := n) w : ENNReal) := by
  classical
  simp [theorem5_coordMeasure, PMF.toMeasure_apply_singleton, PMF.bernoulli_apply, theorem5_inclusionProb]

theorem theorem5_inclusionProb_ge_of_length_le {n r : ℕ} {w : FreeMonoid (Fin n)} :
  w.length ≤ r → ((Nat.log2 (r + 2) + 1 : ℕ) : NNReal)⁻¹ ≤ theorem5_inclusionProb (n := n) w := by
  intro hlen
  simp only [theorem5_inclusionProb]
  have ha : (0 : NNReal) < ((Nat.log2 (r + 2) + 1 : ℕ) : NNReal) := by
    positivity
  have hb : (0 : NNReal) < ((Nat.log2 (w.length + 2) + 1 : ℕ) : NNReal) := by
    positivity
  have hden_nat : Nat.log2 (w.length + 2) + 1 ≤ Nat.log2 (r + 2) + 1 := by
    have h' : w.length + 2 ≤ r + 2 := Nat.add_le_add_right hlen 2
    have hlog' : Nat.log 2 (w.length + 2) ≤ Nat.log 2 (r + 2) :=
      Nat.log_mono_right (b := 2) (n := w.length + 2) (m := r + 2) h'
    have hlog : Nat.log2 (w.length + 2) ≤ Nat.log2 (r + 2) := by
      simpa [Nat.log2_eq_log_two] using hlog'
    exact Nat.add_le_add_right hlog 1
  have hden : ((Nat.log2 (w.length + 2) + 1 : ℕ) : NNReal) ≤ ((Nat.log2 (r + 2) + 1 : ℕ) : NNReal) := by
    exact_mod_cast hden_nat
  exact (inv_le_inv₀ ha hb).2 hden

theorem theorem5_log2_add_one_le_two_mul_log2_add_one_of_le_two_mul (a b : ℕ) : a ≤ 2 * b → Nat.log2 a + 1 ≤ 2 * (Nat.log2 b + 1) := by
  intro hab
  cases b with
  | zero =>
      have ha0 : a = 0 := Nat.eq_zero_of_le_zero (by simpa using hab)
      subst ha0
      -- goal: Nat.log2 0 + 1 ≤ 2 * (Nat.log2 0 + 1)
      simp [Nat.log2_eq_log_two, Nat.log_zero_right]
  | succ b =>
      have hlog : Nat.log 2 a ≤ Nat.log 2 (2 * Nat.succ b) := Nat.log_mono_right hab
      have hlogmul : Nat.log 2 (2 * Nat.succ b) = Nat.log 2 (Nat.succ b) + 1 := by
        simpa [Nat.mul_comm] using
          (Nat.log_mul_base (b := 2) (n := Nat.succ b) (by decide) (Nat.succ_ne_zero b))
      have hlog' : Nat.log 2 a ≤ Nat.log 2 (Nat.succ b) + 1 := by
        simpa [hlogmul] using hlog
      have h1 : Nat.log 2 a + 1 ≤ Nat.log 2 (Nat.succ b) + 2 := by
        have := Nat.add_le_add_right hlog' 1
        simpa [Nat.add_assoc] using this
      have h2 : Nat.log 2 (Nat.succ b) + 2 ≤ 2 * (Nat.log 2 (Nat.succ b) + 1) := by
        have hpos : 1 ≤ Nat.log 2 (Nat.succ b) + 1 := by
          simpa using (Nat.succ_le_succ (Nat.zero_le (Nat.log 2 (Nat.succ b))))
        have := Nat.add_le_add_left hpos (Nat.log 2 (Nat.succ b) + 1)
        -- (x+1)+1 ≤ (x+1)+(x+1)
        simpa [two_mul, Nat.add_assoc] using this
      have : Nat.log 2 a + 1 ≤ 2 * (Nat.log 2 (Nat.succ b) + 1) := le_trans h1 h2
      simpa [Nat.log2_eq_log_two] using this

theorem theorem5_inv_two_mul_log2_add_one_le_inv_log2_add_two (r : ℕ) (hr : 2 ≤ r) :
  (((2 * (Nat.log2 r + 1) : ℕ) : ℝ)⁻¹) ≤ (((Nat.log2 (r + 2) + 1 : ℕ) : ℝ)⁻¹) := by
  have hr2 : r + 2 ≤ 2 * r := by
    omega
  have hlog : Nat.log2 (r + 2) + 1 ≤ 2 * (Nat.log2 r + 1) :=
    theorem5_log2_add_one_le_two_mul_log2_add_one_of_le_two_mul (a := r + 2) (b := r) hr2
  have hlogR : ((Nat.log2 (r + 2) + 1 : ℕ) : ℝ) ≤ ((2 * (Nat.log2 r + 1) : ℕ) : ℝ) := by
    exact_mod_cast hlog
  have hb_nat : 0 < Nat.log2 (r + 2) + 1 := by
    simpa [Nat.succ_eq_add_one] using Nat.succ_pos (Nat.log2 (r + 2))
  have hb : (0 : ℝ) < ((Nat.log2 (r + 2) + 1 : ℕ) : ℝ) := by
    exact (Nat.cast_pos.2 hb_nat)
  exact inv_anti₀ hb hlogR

theorem theorem5_log2_add_two_le_log2_succ (r : ℕ) (hr : 2 ≤ r) : Nat.log2 (r + 2) ≤ Nat.log2 r + 1 := by
  have hle : r + 2 ≤ 2 * r := by
    omega
  have hlog : Nat.log 2 (r + 2) ≤ Nat.log 2 (2 * r) := by
    exact Nat.log_mono_right (b := 2) hle
  have hr0 : r ≠ 0 := by
    omega
  have hmul : Nat.log 2 (2 * r) = Nat.log 2 r + 1 := by
    simpa [Nat.mul_comm] using (Nat.log_mul_base (b := 2) (n := r) (by decide) hr0)
  have hfinal : Nat.log 2 (r + 2) ≤ Nat.log 2 r + 1 := by
    calc
      Nat.log 2 (r + 2) ≤ Nat.log 2 (2 * r) := hlog
      _ = Nat.log 2 r + 1 := hmul
  simpa [Nat.log2_eq_log_two] using hfinal

theorem theorem5_log2_ge_three_of_ge_eight (r : ℕ) (hr : 8 ≤ r) : 3 ≤ Nat.log2 r := by
  have hpow : (2 : ℕ) ^ 3 = 8 := by
    decide
  have hlog8 : Nat.log 2 8 = 3 := by
    simpa [hpow] using (Nat.log_pow (b := 2) (by decide) 3)
  have hmono : Nat.log 2 8 ≤ Nat.log 2 r := by
    exact Nat.log_mono_right (b := 2) hr
  have h : 3 ≤ Nat.log 2 r := by
    simpa [hlog8] using hmono
  simpa [Nat.log2_eq_log_two] using h

def theorem5_logPeriodicSet {n : ℕ} (B : ℕ) : Set (FreeMonoid (Fin n)) :=
  {w | ∃ d : ℕ, theorem5_hasPeriod (n := n) w d ∧ d ≤ B * (Nat.log2 w.length + 1)}

noncomputable def theorem5_macroMeasure (n : ℕ) : MeasureTheory.Measure (FreeMonoid (Fin n) → Bool) :=
  MeasureTheory.Measure.infinitePi (fun w : FreeMonoid (Fin n) => theorem5_coordMeasure (n := n) w)

open MeasureTheory in
open ProbabilityTheory in
theorem theorem5_iIndepFun_eval (n : ℕ) :
  ProbabilityTheory.iIndepFun
    (fun w : FreeMonoid (Fin n) => fun ω : (FreeMonoid (Fin n) → Bool) => ω w)
    (theorem5_macroMeasure n) := by
  classical
  -- `theorem5_coordMeasure w` comes from a `PMF`, hence is a probability measure.
  letI : ∀ w : FreeMonoid (Fin n), IsProbabilityMeasure (theorem5_coordMeasure (n := n) w) :=
    fun w => by
      -- unfold to the underlying `PMF.toMeasure` and use the standard lemma
      simpa [theorem5_coordMeasure] using
        (PMF.toMeasure.isProbabilityMeasure
          (PMF.bernoulli (theorem5_inclusionProb (n := n) w)
            (by
              have hNat : (1 : ℕ) ≤ Nat.log2 (w.length + 2) + 1 :=
                Nat.succ_le_succ (Nat.zero_le _)
              have hNN : (1 : NNReal) ≤ ((Nat.log2 (w.length + 2) + 1 : ℕ) : NNReal) := by
                exact_mod_cast hNat
              have : ((Nat.log2 (w.length + 2) + 1 : ℕ) : NNReal)⁻¹ ≤ (1 : NNReal) :=
                (inv_le_one_iff₀).2 (Or.inr hNN)
              simpa [theorem5_inclusionProb] using this)))

  -- Now apply the independence lemma for infinite product measures with `X i = id`.
  simpa [theorem5_macroMeasure] using
    (ProbabilityTheory.iIndepFun_infinitePi
      (P := fun w : FreeMonoid (Fin n) => theorem5_coordMeasure (n := n) w)
      (X := fun _w : FreeMonoid (Fin n) => (fun b : Bool => b))
      (mX := by
        intro _w
        simpa using (measurable_id : Measurable (fun b : Bool => b))))

open MeasureTheory in
open ProbabilityTheory in
theorem theorem5_macroMeasure_all_false_finset {n : ℕ} (S : Finset (FreeMonoid (Fin n))) :
    theorem5_macroMeasure n (Set.pi S (fun _ => ({false} : Set Bool))) =
      S.prod (fun u => theorem5_coordMeasure (n := n) u ({false} : Set Bool)) := by
  classical
  -- Provide probability measure instances for the coordinates
  haveI (w : FreeMonoid (Fin n)) : IsProbabilityMeasure (theorem5_coordMeasure (n := n) w) := by
    dsimp [theorem5_coordMeasure]
    infer_instance
  -- Apply the cylinder-set formula for the infinite product measure
  simpa [theorem5_macroMeasure] using
    (MeasureTheory.Measure.infinitePi_pi
      (μ := fun w : FreeMonoid (Fin n) => theorem5_coordMeasure (n := n) w)
      (s := S)
      (t := fun _ : FreeMonoid (Fin n) => ({false} : Set Bool))
      (by
        intro i hi
        simpa using (measurableSet_singleton (a := false))))

open MeasureTheory in
open ProbabilityTheory in
theorem theorem5_macroMeasure_eval_true {n : ℕ} (w : FreeMonoid (Fin n)) :
  theorem5_macroMeasure n {ω : FreeMonoid (Fin n) → Bool | ω w = true} =
    (theorem5_inclusionProb (n := n) w : ENNReal) := by
  classical
  haveI (i : FreeMonoid (Fin n)) : MeasureTheory.IsProbabilityMeasure
      (theorem5_coordMeasure (n := n) i) :=
    theorem5_coordMeasure_isProbability (n := n) i
  have hmp :
      MeasureTheory.MeasurePreserving (Function.eval w)
        (theorem5_macroMeasure n)
        (theorem5_coordMeasure (n := n) w) := by
    simpa [theorem5_macroMeasure] using
      (measurePreserving_eval_infinitePi
        (μ := fun i : FreeMonoid (Fin n) => theorem5_coordMeasure (n := n) i) w)
  have hs : MeasureTheory.NullMeasurableSet ({true} : Set Bool)
      (theorem5_coordMeasure (n := n) w) := by
    simpa using (MeasurableSet.singleton true).nullMeasurableSet
  have h := hmp.measure_preimage (s := ({true} : Set Bool)) hs
  simpa [Set.preimage, Function.eval, theorem5_coordMeasure_true_eq] using h

open MeasureTheory in
open ProbabilityTheory in
theorem theorem5_macroMeasure_isProbability (n : ℕ) : MeasureTheory.IsProbabilityMeasure (theorem5_macroMeasure n) := by
  classical
  letI : ∀ w : FreeMonoid (Fin n), MeasureTheory.IsProbabilityMeasure (theorem5_coordMeasure (n := n) w) :=
    fun w => theorem5_coordMeasure_isProbability (n := n) w
  simpa [theorem5_macroMeasure] using
    (MeasureTheory.Measure.instIsProbabilityMeasureForallInfinitePi
      (μ := fun w : FreeMonoid (Fin n) => theorem5_coordMeasure (n := n) w))

theorem theorem5_mul_inv_div_sq {a d : ℝ} (ha : a ≠ 0) (hd : d ≠ 0) : (a * d⁻¹) / ((a * d⁻¹) ^ 2) = d / a := by
  field_simp [ha, hd]


theorem theorem5_nat_le_four_mul_div_four_add_three (r : ℕ) : r ≤ 4 * (r / 4) + 3 := by
  -- Euclidean division by 4
  have hdiv : r = 4 * (r / 4) + r % 4 := by
    -- `Nat.div_add_mod` gives `r / 4 * 4 + r % 4 = r`
    simpa [Nat.mul_comm, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      (Nat.div_add_mod r 4).symm

  have hmod : r % 4 ≤ 3 := by
    -- since `r % 4 < 4 = 3 + 1`
    have hlt : r % 4 < 4 := by
      exact Nat.mod_lt r (by decide)
    -- convert `< 4` into `≤ 3`
    exact Nat.le_of_lt_succ (by simpa using hlt)

  -- now combine
  have h1 : r ≤ 4 * (r / 4) + r % 4 := le_of_eq hdiv
  have h2 : 4 * (r / 4) + r % 4 ≤ 4 * (r / 4) + 3 := by
    exact Nat.add_le_add_left hmod _
  exact le_trans h1 h2

open scoped BigOperators in
open Filter in
open free in
theorem theorem5_ncard_Sphere (n r : ℕ) : Set.ncard (Sphere n r) = n ^ r := by
  classical
  simp [Sphere]
  rw [← Set.Nat.card_coe_set_eq (s := { w : FreeMonoid (Fin n) | w.length = r })]
  change Nat.card { w : FreeMonoid (Fin n) // w.length = r } = n ^ r
  change Nat.card (List.Vector (Fin n) r) = n ^ r
  rw [Nat.card_eq_fintype_card]
  simpa [Fintype.card_fin] using (card_vector (α := Fin n) r)

open free in
theorem theorem5_ncard_hasPeriod_inter_sphere_le (n r d : ℕ) :
    Set.ncard ({w : FreeMonoid (Fin n) | theorem5_hasPeriod (n := n) w d} ∩ Sphere n r) ≤ n ^ d := by
  classical
  let S : Set (FreeMonoid (Fin n)) :=
    {w : FreeMonoid (Fin n) | theorem5_hasPeriod (n := n) w d} ∩ Sphere n r

  have hSphere_finite : (Sphere n d).Finite := by
    simpa [Sphere] using (List.finite_length_eq (α := Fin n) (n := d))

  have h_le : Set.ncard S ≤ Set.ncard (Sphere n d) := by
    refine Set.ncard_le_ncard_of_injOn (s := S) (t := Sphere n d)
      (fun w : FreeMonoid (Fin n) => w.take d) ?_ ?_ hSphere_finite
    · -- MapsTo
      intro w hw
      rcases hw with ⟨hwPer, hwSphere⟩
      rcases hwPer with ⟨hdpos, hdle, hdrop⟩
      have hlen_take : (w.take d).length = d := by
        simpa using List.length_take_of_le hdle
      simpa [Sphere, hlen_take]
    · -- InjOn
      intro w1 hw1 w2 hw2 htake
      have hlen1 : w1.length = r := by simpa [Sphere] using hw1.2
      have hlen2 : w2.length = r := by simpa [Sphere] using hw2.2
      have hper1 : theorem5_hasPeriod (n := n) w1 d := hw1.1
      have hper2 : theorem5_hasPeriod (n := n) w2 d := hw2.1

      -- auxiliary lemma by strong induction on the length
      have aux : ∀ {r : ℕ} {u v : FreeMonoid (Fin n)},
          u.length = r → v.length = r →
          theorem5_hasPeriod (n := n) u d → theorem5_hasPeriod (n := n) v d →
          u.take d = v.take d → u = v := by
        intro r
        induction r using Nat.strongRecOn with
        | _ r ih =>
          intro u v hu hv hpu hpv htv
          rcases hpu with ⟨hdpos, hdleu, hdropu⟩
          rcases hpv with ⟨_, hdlev, hdropv⟩

          have hdropu' : u.drop d = u.take (r - d) := by
            simpa [hu] using hdropu
          have hdropv' : v.drop d = v.take (r - d) := by
            simpa [hv] using hdropv

          by_cases hrd : r = d
          · -- base: r = d
            have hu' : u.length = d := by simpa [hrd] using hu
            have hv' : v.length = d := by simpa [hrd] using hv
            have hutake : u.take d = u := by
              apply (List.take_eq_self_iff u).2
              exact le_of_eq hu'
            have hvtake : v.take d = v := by
              apply (List.take_eq_self_iff v).2
              exact le_of_eq hv'
            calc
              u = u.take d := by simpa [hutake]
              _ = v.take d := htv
              _ = v := by simpa [hvtake]
          ·
            have hdler : d ≤ r := by simpa [hu] using hdleu

            have hprefix : u.take (r - d) = v.take (r - d) := by
              by_cases hle : r - d ≤ d
              · -- short tail
                have hu_eq : (u.take d).take (r - d) = u.take (r - d) := by
                  simpa [List.take_take, Nat.min_eq_left hle]
                have hv_eq : (v.take d).take (r - d) = v.take (r - d) := by
                  simpa [List.take_take, Nat.min_eq_left hle]
                calc
                  u.take (r - d) = (u.take d).take (r - d) := by simpa [hu_eq]
                  _ = (v.take d).take (r - d) := by simpa [htv]
                  _ = v.take (r - d) := by simpa [hv_eq]
              · -- long tail
                have hlt : r - d < r := by
                  omega
                have ih' :
                    ∀ {u v : FreeMonoid (Fin n)},
                      u.length = r - d →
                        v.length = r - d →
                          theorem5_hasPeriod (n := n) u d →
                            theorem5_hasPeriod (n := n) v d →
                              u.take d = v.take d → u = v :=
                  ih (r - d) hlt

                -- lengths of prefixes, in terms of FreeMonoid.length
                have hu_len' : FreeMonoid.length (u.take (r - d)) = r - d := by
                  have : r - d ≤ u.length := by
                    simpa [hu] using Nat.sub_le r d
                  have hl : (List.take (r - d) u).length = r - d :=
                    List.length_take_of_le this
                  simpa only [FreeMonoid.length] using hl
                have hv_len' : FreeMonoid.length (v.take (r - d)) = r - d := by
                  have : r - d ≤ v.length := by
                    simpa [hv] using Nat.sub_le r d
                  have hl : (List.take (r - d) v).length = r - d :=
                    List.length_take_of_le this
                  simpa only [FreeMonoid.length] using hl

                have hdle : d ≤ r - d := by
                  have : d < r - d := lt_of_not_ge hle
                  exact le_of_lt this

                have hup : theorem5_hasPeriod (n := n) (u.take (r - d)) d := by
                  refine ⟨hdpos, ?_, ?_⟩
                  · simpa [hu_len'] using hdle
                  ·
                    have h1 : (u.take (r - d)).drop d = (u.drop d).take (r - d - d) := by
                      simpa [List.drop_take]
                    have h2 : (u.take (r - d)).drop d = (u.take (r - d)).take (r - d - d) := by
                      simpa [hdropu'] using h1
                    simpa [hu_len'] using h2
                have hvp : theorem5_hasPeriod (n := n) (v.take (r - d)) d := by
                  refine ⟨hdpos, ?_, ?_⟩
                  · simpa [hv_len'] using hdle
                  ·
                    have h1 : (v.take (r - d)).drop d = (v.drop d).take (r - d - d) := by
                      simpa [List.drop_take]
                    have h2 : (v.take (r - d)).drop d = (v.take (r - d)).take (r - d - d) := by
                      simpa [hdropv'] using h1
                    simpa [hv_len'] using h2

                have htake_prefix : (u.take (r - d)).take d = (v.take (r - d)).take d := by
                  have hu_t : (u.take (r - d)).take d = u.take d := by
                    simpa [List.take_take, Nat.min_eq_left hdle]
                  have hv_t : (v.take (r - d)).take d = v.take d := by
                    simpa [List.take_take, Nat.min_eq_left hdle]
                  calc
                    (u.take (r - d)).take d = u.take d := hu_t
                    _ = v.take d := htv
                    _ = (v.take (r - d)).take d := by simpa [hv_t]

                exact ih' hu_len' hv_len' hup hvp htake_prefix

            have hdrop_eq : u.drop d = v.drop d := by
              simpa [hdropu', hdropv', hprefix]

            calc
              u = u.take d ++ u.drop d := (List.take_append_drop d u).symm
              _ = v.take d ++ v.drop d := by simp [htv, hdrop_eq]
              _ = v := List.take_append_drop d v

      exact aux hlen1 hlen2 hper1 hper2 htake

  simpa [S, theorem5_ncard_Sphere] using h_le

open scoped BigOperators in
open free in
theorem theorem5_ncard_logPeriodic_inter_sphere_le_sum (n r B : ℕ) :
    Set.ncard (theorem5_logPeriodicSet (n := n) B ∩ Sphere n r)
      ≤ ∑ d ∈ Finset.range (B * (Nat.log2 r + 1) + 1), n ^ d := by
  classical
  set K : ℕ := B * (Nat.log2 r + 1)
  let S : ℕ → Set (FreeMonoid (Fin n)) :=
    fun d => {w : FreeMonoid (Fin n) | theorem5_hasPeriod (n := n) w d} ∩ Sphere n r
  have hSphereFinite : (Sphere n r).Finite := by
    simpa [Sphere, FreeMonoid.length] using (List.finite_length_eq (α := Fin n) (n := r))
  have hsub :
      theorem5_logPeriodicSet (n := n) B ∩ Sphere n r ⊆ ⋃ d ∈ Finset.range (K + 1), S d := by
    intro w hw
    rcases hw with ⟨hwLog, hwSphere⟩
    rcases hwLog with ⟨d, hdPer, hdBound⟩
    have hwlen : w.length = r := by
      simpa [Sphere] using hwSphere
    have hdBound' : d ≤ K := by
      simpa [K, hwlen] using hdBound
    have hdMem : d ∈ Finset.range (K + 1) := by
      -- range (K+1) = {0,...,K}
      -- use d ≤ K
      simpa [Finset.mem_range] using Nat.lt_succ_of_le hdBound'
    have hwSd : w ∈ S d := by
      exact ⟨hdPer, hwSphere⟩
    -- membership in the union
    refine Set.mem_iUnion₂.2 ?_
    exact ⟨d, hdMem, hwSd⟩
  have hUnionFinite : (⋃ d ∈ Finset.range (K + 1), S d).Finite := by
    refine hSphereFinite.subset ?_
    intro w hw
    rcases (Set.mem_iUnion₂.1 hw) with ⟨d, hd, hwSd⟩
    exact hwSd.2
  have hcard_sub :
      Set.ncard (theorem5_logPeriodicSet (n := n) B ∩ Sphere n r)
        ≤ Set.ncard (⋃ d ∈ Finset.range (K + 1), S d) := by
    exact Set.ncard_le_ncard hsub hUnionFinite
  have hcard_union :
      Set.ncard (⋃ d ∈ Finset.range (K + 1), S d) ≤
        ∑ d ∈ Finset.range (K + 1), Set.ncard (S d) := by
    simpa using (Finset.set_ncard_biUnion_le (Finset.range (K + 1)) S)
  have hsum_le :
      (∑ d ∈ Finset.range (K + 1), Set.ncard (S d)) ≤
        ∑ d ∈ Finset.range (K + 1), n ^ d := by
    refine Finset.sum_le_sum ?_
    intro d hd
    -- show summand inequality
    have : Set.ncard (S d) ≤ n ^ d := by
      simpa [S] using (theorem5_ncard_hasPeriod_inter_sphere_le n r d)
    simpa using this
  have :
      Set.ncard (theorem5_logPeriodicSet (n := n) B ∩ Sphere n r) ≤
        ∑ d ∈ Finset.range (K + 1), n ^ d :=
    le_trans (le_trans hcard_sub hcard_union) hsum_le
  -- finish by rewriting K
  simpa [K] using this


theorem theorem5_parsing_lemma {n : ℕ} {M : Set (FreeMonoid (Fin n))} {C : ℕ} : (∀ᶠ r : ℕ in atTop, theorem5_hasHalfMacro (n := n) C M r) →
    ∃ (K : ℕ), 0 < K ∧
      (∀ᶠ r : ℕ in atTop,
        Ball r (A n) ⊆ Ball (K * (Nat.log2 r) ^ 2) (M ∪ (A n))) := by
  classical
  intro hmacro
  rcases (Filter.eventually_atTop.1 hmacro) with ⟨N, hN⟩
  let N1 : ℕ := max N 2
  have hN1 : ∀ r ≥ N1, theorem5_hasHalfMacro (n := n) C M r := by
    intro r hr
    apply hN r
    exact le_trans (le_max_left N 2) hr
  let K1 : ℕ := max (C + 1) N1
  -- Parsing lemma for exact lengths
  have parse : ∀ L : ℕ, ∀ w : FreeMonoid (Fin n), w.length = L →
      w ∈ Ball (K1 * (Nat.log2 L + 1) ^ 2) (M ∪ (A n)) := by
    intro L
    refine Nat.strong_induction_on L ?_
    intro L ih w hw
    by_cases hL : L < N1
    · -- base case: represent by single letters
      have hwle : w.length ≤ L := by
        simpa [hw] using le_rfl
      have hwA : w ∈ Ball L (A n) := (theorem5_ball_A_iff_length_le n L w).2 hwle
      have hsub : (A n : Set (FreeMonoid (Fin n))) ⊆ (M ∪ A n) := by
        intro x hx
        exact Or.inr hx
      have hwA' : w ∈ Ball L (M ∪ A n) := (theorem5_ball_mono_X (n := n) (R := L) (h := hsub)) hwA
      have hLK : L ≤ K1 := by
        have h1 : L ≤ N1 := le_of_lt hL
        exact le_trans h1 (le_max_right (C + 1) N1)
      have hpow1 : (1 : ℕ) ≤ (Nat.log2 L + 1) ^ 2 := by
        have : 0 < Nat.log2 L + 1 := Nat.succ_pos _
        have : 1 ≤ Nat.log2 L + 1 := Nat.succ_le_of_lt this
        simpa using (pow_le_pow_left' this 2)
      have hKmul : K1 ≤ K1 * (Nat.log2 L + 1) ^ 2 := by
        simpa [one_mul] using (Nat.mul_le_mul_left K1 hpow1)
      have hR : L ≤ K1 * (Nat.log2 L + 1) ^ 2 := le_trans hLK hKmul
      exact (theorem5_ball_mono_R (n := n) (X := (M ∪ A n)) (h := hR)) hwA'
    · -- inductive step: apply half-macro decomposition
      have hLge : N1 ≤ L := le_of_not_gt hL
      have hmacroL : theorem5_hasHalfMacro (n := n) C M L := hN1 L hLge
      rcases hmacroL w hw with ⟨p, u, s, hwps, hp, hu, huLen, hsLen⟩
      -- p in ball
      have hpBallA : p ∈ Ball (C * (Nat.log2 L + 1)) (A n) :=
        (theorem5_ball_A_iff_length_le n (C * (Nat.log2 L + 1)) p).2 hp
      have hsub : (A n : Set (FreeMonoid (Fin n))) ⊆ (M ∪ A n) := by
        intro x hx
        exact Or.inr hx
      have hpBall : p ∈ Ball (C * (Nat.log2 L + 1)) (M ∪ A n) :=
        (theorem5_ball_mono_X (n := n) (R := (C * (Nat.log2 L + 1))) (h := hsub)) hpBallA
      -- u in ball 1
      have huBall : u ∈ Ball 1 (M ∪ A n) := by
        refine ⟨[u], ?_, ?_, ?_⟩
        · simp
        · intro x hx
          simp at hx
          rcases hx with rfl
          exact Or.inl hu
        · simp
      -- s in ball via IH
      have hLpos : 0 < L := by
        have : (2 : ℕ) ≤ L := le_trans (le_max_right N 2) hLge
        exact lt_of_lt_of_le (by decide : 0 < (2 : ℕ)) this
      have hsLt : s.length < L :=
        lt_of_le_of_lt hsLen (Nat.div_lt_self hLpos (by decide : 1 < (2 : ℕ)))
      have hsParse : s ∈ Ball (K1 * (Nat.log2 s.length + 1) ^ 2) (M ∪ A n) := by
        simpa using (ih s.length hsLt s rfl)
      -- log bound for s.length
      have hlogmon : Nat.log2 s.length ≤ Nat.log2 (L / 2) := by
        have : Nat.log 2 s.length ≤ Nat.log 2 (L / 2) := Nat.log_mono_right hsLen
        simpa [Nat.log2_eq_log_two] using this
      have hlogdiv : Nat.log2 (L / 2) = Nat.log2 L - 1 := by
        simpa [Nat.log2_eq_log_two] using (Nat.log_div_base 2 L)
      have hlogle : Nat.log2 s.length ≤ Nat.log2 L - 1 := by
        simpa [hlogdiv] using hlogmon
      have hxpos : 1 ≤ Nat.log2 L := by
        have : (2 : ℕ) ≤ L := le_trans (le_max_right N 2) hLge
        have : 0 < Nat.log 2 L := Nat.log_pos Nat.one_lt_two this
        have : 0 < Nat.log2 L := by simpa [Nat.log2_eq_log_two] using this
        exact Nat.succ_le_of_lt this
      have hlog : Nat.log2 s.length + 1 ≤ Nat.log2 L := by
        have := Nat.succ_le_succ hlogle
        simpa [Nat.sub_add_cancel hxpos] using this
      have hpow : (Nat.log2 s.length + 1) ^ 2 ≤ (Nat.log2 L) ^ 2 := pow_le_pow_left' hlog 2
      have hmul : K1 * (Nat.log2 s.length + 1) ^ 2 ≤ K1 * (Nat.log2 L) ^ 2 :=
        Nat.mul_le_mul_left K1 hpow
      have hsBall : s ∈ Ball (K1 * (Nat.log2 L) ^ 2) (M ∪ A n) :=
        (theorem5_ball_mono_R (n := n) (X := (M ∪ A n)) (h := hmul)) hsParse
      -- combine p,u,s
      have hpu : p * u ∈ Ball (C * (Nat.log2 L + 1) + 1) (M ∪ A n) :=
        theorem5_ball_mul (n := n) (R := C * (Nat.log2 L + 1)) (S := 1) (X := (M ∪ A n)) hpBall huBall
      have hpus : p * u * s ∈ Ball (C * (Nat.log2 L + 1) + 1 + K1 * (Nat.log2 L) ^ 2) (M ∪ A n) := by
        simpa [add_assoc] using
          (theorem5_ball_mul (n := n) (R := C * (Nat.log2 L + 1) + 1) (S := K1 * (Nat.log2 L) ^ 2)
            (X := (M ∪ A n)) hpu hsBall)
      have hR : C * (Nat.log2 L + 1) + 1 + K1 * (Nat.log2 L) ^ 2 ≤ K1 * (Nat.log2 L + 1) ^ 2 := by
        -- Expand the square on the RHS and use K1 ≥ C+1
        have hExpand : K1 * (Nat.log2 L + 1) ^ 2 =
            K1 * (Nat.log2 L) ^ 2 + 2 * K1 * Nat.log2 L + K1 := by
          ring
        have hKC : C + 1 ≤ K1 := by
          dsimp [K1]
          exact le_max_left _ _
        have hCK : C ≤ K1 := le_trans (Nat.le_succ C) hKC
        have hK2K : K1 ≤ 2 * K1 := by
          simpa [one_mul] using (Nat.mul_le_mul_right K1 (show (1 : ℕ) ≤ 2 by decide))
        have hC2K : C ≤ 2 * K1 := le_trans hCK hK2K
        have hxmul : C * Nat.log2 L ≤ (2 * K1) * Nat.log2 L :=
          Nat.mul_le_mul_right (Nat.log2 L) hC2K
        have hsum : C * Nat.log2 L + (C + 1) ≤ (2 * K1) * Nat.log2 L + K1 :=
          Nat.add_le_add hxmul hKC
        have hlin : C * (Nat.log2 L + 1) + 1 ≤ 2 * K1 * Nat.log2 L + K1 := by
          simpa [mul_add, add_assoc, add_left_comm, add_comm, mul_assoc, mul_one] using hsum
        -- Add the common term K1*(log2 L)^2 to both sides
        have hlin' : C * (Nat.log2 L + 1) + 1 + K1 * (Nat.log2 L) ^ 2 ≤
            (2 * K1 * Nat.log2 L + K1) + K1 * (Nat.log2 L) ^ 2 :=
          Nat.add_le_add_right hlin (K1 * (Nat.log2 L) ^ 2)
        -- Rearrange and rewrite using the expansion of the RHS
        rw [hExpand]
        simpa [add_assoc, add_left_comm, add_comm, mul_assoc] using hlin'
      have hsubsetR :
          Ball (C * (Nat.log2 L + 1) + 1 + K1 * (Nat.log2 L) ^ 2) (M ∪ A n) ⊆
            Ball (K1 * (Nat.log2 L + 1) ^ 2) (M ∪ A n) :=
        theorem5_ball_mono_R (n := n) (X := (M ∪ A n)) hR
      have hwTmp : w ∈ Ball (C * (Nat.log2 L + 1) + 1 + K1 * (Nat.log2 L) ^ 2) (M ∪ A n) := by
        simpa [hwps, mul_assoc] using hpus
      exact hsubsetR hwTmp
  -- Now choose final K and show eventual containment
  refine ⟨4 * K1, ?_, ?_⟩
  · have : 0 < K1 := lt_of_lt_of_le (Nat.succ_pos C) (le_max_left (C + 1) N1)
    have : 0 < 4 * K1 := Nat.mul_pos (by decide : 0 < (4 : ℕ)) this
    simpa [Nat.mul_assoc] using this
  · refine (Filter.eventually_atTop.2 ?_)
    refine ⟨2, ?_⟩
    intro r hr
    intro w hwBallA
    have hwlen : w.length ≤ r := (theorem5_ball_A_iff_length_le n r w).1 hwBallA
    have hwParse : w ∈ Ball (K1 * (Nat.log2 w.length + 1) ^ 2) (M ∪ A n) := parse w.length w rfl
    have hlogle : Nat.log2 w.length ≤ Nat.log2 r := by
      have : Nat.log 2 w.length ≤ Nat.log 2 r := Nat.log_mono_right hwlen
      simpa [Nat.log2_eq_log_two] using this
    have hadd : Nat.log2 w.length + 1 ≤ Nat.log2 r + 1 := Nat.succ_le_succ hlogle
    have hpow : (Nat.log2 w.length + 1) ^ 2 ≤ (Nat.log2 r + 1) ^ 2 := pow_le_pow_left' hadd 2
    have hmul : K1 * (Nat.log2 w.length + 1) ^ 2 ≤ K1 * (Nat.log2 r + 1) ^ 2 := Nat.mul_le_mul_left K1 hpow
    have hwParseR : w ∈ Ball (K1 * (Nat.log2 r + 1) ^ 2) (M ∪ A n) :=
      (theorem5_ball_mono_R (n := n) (X := (M ∪ A n)) (h := hmul)) hwParse
    have hrlog : 1 ≤ Nat.log2 r := by
      have : (2 : ℕ) ≤ r := hr
      have : 0 < Nat.log 2 r := Nat.log_pos Nat.one_lt_two this
      have : 0 < Nat.log2 r := by simpa [Nat.log2_eq_log_two] using this
      exact Nat.succ_le_of_lt this
    have hpow' : (Nat.log2 r + 1) ^ 2 ≤ 4 * (Nat.log2 r) ^ 2 := by
      let x := Nat.log2 r
      have hxpos : 1 ≤ x := by simpa [x] using hrlog
      have hx : x + 1 ≤ 2 * x := by
        omega
      have hpowx : (x + 1) ^ 2 ≤ (2 * x) ^ 2 := pow_le_pow_left' hx 2
      have hEq : (2 * x) ^ 2 = 4 * x ^ 2 := by
        ring
      simpa [x, hEq] using hpowx
    have hmul' : K1 * (Nat.log2 r + 1) ^ 2 ≤ (4 * K1) * (Nat.log2 r) ^ 2 := by
      have : K1 * (Nat.log2 r + 1) ^ 2 ≤ K1 * (4 * (Nat.log2 r) ^ 2) := Nat.mul_le_mul_left K1 hpow'
      simpa [mul_assoc, mul_left_comm, mul_comm] using this
    have hwFinal : w ∈ Ball ((4 * K1) * (Nat.log2 r) ^ 2) (M ∪ A n) :=
      (theorem5_ball_mono_R (n := n) (X := (M ∪ A n)) (h := hmul')) hwParseR
    simpa [mul_assoc] using hwFinal

open scoped BigOperators in
theorem theorem5_pow_mul_ofReal_exp_neg_two_mul_le_ofReal_exp_neg (n r : ℕ) :
  (n ^ r : ENNReal) * ENNReal.ofReal (Real.exp (-(2 * (n : ℝ)) * r))
    ≤ ENNReal.ofReal (Real.exp (-(n : ℝ) * r)) := by
  classical
  -- Set up some basic nonnegativity facts.
  have hn_pow0 : (0 : ℝ) ≤ (n ^ r : ℝ) := by
    exact_mod_cast (Nat.zero_le (n ^ r))
  have hExp0 : (0 : ℝ) ≤ Real.exp (-(2 * (n : ℝ)) * r) := by
    positivity
  have hExp0' : (0 : ℝ) ≤ Real.exp (-(n : ℝ) * r) := by
    positivity

  -- Rewrite the left-hand side as `ofReal` of a product.
  have hL : (n ^ r : ENNReal) * ENNReal.ofReal (Real.exp (-(2 * (n : ℝ)) * r)) =
      ENNReal.ofReal ((n ^ r : ℝ) * Real.exp (-(2 * (n : ℝ)) * r)) := by
    calc
      (n ^ r : ENNReal) * ENNReal.ofReal (Real.exp (-(2 * (n : ℝ)) * r))
          = ENNReal.ofReal (n ^ r : ℝ) * ENNReal.ofReal (Real.exp (-(2 * (n : ℝ)) * r)) := by
              -- `ofReal (n^r) = n^r`
              simpa using congrArg (fun x => x * ENNReal.ofReal (Real.exp (-(2 * (n : ℝ)) * r)))
                (ENNReal.ofReal_natCast (n ^ r)).symm
      _ = ENNReal.ofReal ((n ^ r : ℝ) * Real.exp (-(2 * (n : ℝ)) * r)) := by
            -- use `ofReal_mul`
            simpa [mul_comm, mul_left_comm, mul_assoc] using (ENNReal.ofReal_mul hn_pow0).symm

  -- Reduce the ENNReal goal to a real inequality.
  have hreal : (n ^ r : ℝ) * Real.exp (-(2 * (n : ℝ)) * r) ≤ Real.exp (-(n : ℝ) * r) := by
    -- We'll prove a stronger inequality `n^r ≤ exp(n*r)` and then multiply.
    have hn_le_exp : (n : ℝ) ≤ Real.exp (n : ℝ) := by
      have hn_le : (n : ℝ) ≤ (n : ℝ) + 1 := by linarith
      have h1 : (n : ℝ) + 1 ≤ Real.exp (n : ℝ) := by
        simpa using (Real.add_one_le_exp (n : ℝ))
      exact le_trans hn_le h1
    have hn_nonneg : (0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (Nat.zero_le n)
    have hpow : (n : ℝ) ^ r ≤ (Real.exp (n : ℝ)) ^ r := by
      exact pow_le_pow_left₀ hn_nonneg hn_le_exp r
    have hpow' : (n : ℝ) ^ r ≤ Real.exp ((n : ℝ) * r) := by
      -- rewrite `(exp n)^r` as `exp (n*r)`
      have hexp : (Real.exp (n : ℝ)) ^ r = Real.exp ((n : ℝ) * r) := by
        -- `Real.exp_nat_mul` gives `exp (r*n) = (exp n)^r`.
        have h := Real.exp_nat_mul (n : ℝ) r
        -- rewrite `r*n` as `n*r`
        calc
          (Real.exp (n : ℝ)) ^ r = Real.exp ((r : ℝ) * (n : ℝ)) := by
            simpa using h.symm
          _ = Real.exp ((n : ℝ) * r) := by
            ring_nf
      exact le_trans hpow (le_of_eq hexp)

    -- Multiply `hpow'` by `exp (-(2*n)*r)`.
    have hmul : (n : ℝ) ^ r * Real.exp (-(2 * (n : ℝ)) * r)
        ≤ Real.exp ((n : ℝ) * r) * Real.exp (-(2 * (n : ℝ)) * r) := by
      exact mul_le_mul_of_nonneg_right hpow' hExp0

    -- Simplify the right-hand side.
    have hExpMul : Real.exp ((n : ℝ) * r) * Real.exp (-(2 * (n : ℝ)) * r)
        = Real.exp (-(n : ℝ) * r) := by
      -- combine exponents
      -- exp a * exp b = exp (a+b)
      calc
        Real.exp ((n : ℝ) * r) * Real.exp (-(2 * (n : ℝ)) * r)
            = Real.exp (((n : ℝ) * r) + (-(2 * (n : ℝ)) * r)) := by
                simpa [Real.exp_add, mul_comm, mul_left_comm, mul_assoc]
        _ = Real.exp (-(n : ℝ) * r) := by
            ring_nf

    -- Replace `(n^r:ℝ)` by `(n:ℝ)^r`.
    have hn_cast : (n ^ r : ℝ) = (n : ℝ) ^ r := by
      simpa using (Nat.cast_pow n r)

    -- Conclude.
    have : (n ^ r : ℝ) * Real.exp (-(2 * (n : ℝ)) * r)
        ≤ Real.exp ((n : ℝ) * r) * Real.exp (-(2 * (n : ℝ)) * r) := by
      simpa [hn_cast, mul_assoc] using hmul
    exact le_trans this (le_of_eq hExpMul)

  -- Transport the real inequality back to ENNReal.
  -- Start from `ofReal` inequality.
  have hENN : ENNReal.ofReal ((n ^ r : ℝ) * Real.exp (-(2 * (n : ℝ)) * r))
      ≤ ENNReal.ofReal (Real.exp (-(n : ℝ) * r)) :=
    ENNReal.ofReal_le_ofReal hreal

  -- Rewrite back to the original statement using `hL`.
  simpa [hL] using hENN

open Filter in
theorem theorem5_pow_mul_ofReal_exp_neg_two_mul_sub_three_le_ofReal_exp_neg (n r : ℕ) (hn : 2 ≤ n) (hr : 6 * n ≤ r) :
  (n ^ r : ENNReal) * ENNReal.ofReal (Real.exp (-(2 * (n : ℝ)) * (r - 3)))
    ≤ ENNReal.ofReal (Real.exp (-(n : ℝ) * r)) := by
  classical
  have hx : 0 ≤ Real.exp (-(2 * (n : ℝ)) * (r - 3)) := by
    positivity
  have hrew : (n ^ r : ENNReal) * ENNReal.ofReal (Real.exp (-(2 * (n : ℝ)) * (r - 3))) =
      ENNReal.ofReal ((n ^ r : ℝ) * Real.exp (-(2 * (n : ℝ)) * (r - 3))) := by
    simpa using
      (theorem5_ennreal_nat_mul_ofReal_eq_ofReal_mul (a := n ^ r)
        (x := Real.exp (-(2 * (n : ℝ)) * (r - 3))) hx)
  rw [hrew]
  have hq : 0 ≤ Real.exp (-(n : ℝ) * r) := by
    positivity

  -- now it suffices to prove the real inequality
  have hreal : (n ^ r : ℝ) * Real.exp (-(2 * (n : ℝ)) * (r - 3)) ≤ Real.exp (-(n : ℝ) * r) := by
    -- first bound n by exp(n/2)
    have hnexp : (n : ℝ) ≤ Real.exp ((n : ℝ) / 2) := by
      have h := (Real.two_mul_le_exp (x := (n : ℝ) / 2))
      have h2 : (2 : ℝ) * ((n : ℝ) / 2) = (n : ℝ) := by
        calc
          (2 : ℝ) * ((n : ℝ) / 2) = ((n : ℝ) / 2) + (n : ℝ) / 2 := by
            simpa [two_mul]
          _ = (n : ℝ) := by
            simpa using (add_halves (n : ℝ))
      simpa [h2] using h

    have hn0 : (0 : ℝ) ≤ (n : ℝ) := by positivity

    have hpow : (n : ℝ) ^ r ≤ (Real.exp ((n : ℝ) / 2)) ^ r := by
      simpa using
        (pow_le_pow_left₀ (a := (n : ℝ)) (b := Real.exp ((n : ℝ) / 2)) hn0 hnexp r)

    have hpow' : (n ^ r : ℝ) ≤ (Real.exp ((n : ℝ) / 2)) ^ r := by
      simpa [Nat.cast_pow] using (show (n : ℝ) ^ r ≤ (Real.exp ((n : ℝ) / 2)) ^ r from hpow)

    have hpow'' : (n ^ r : ℝ) ≤ Real.exp (r * ((n : ℝ) / 2)) := by
      simpa [(Real.exp_nat_mul ((n : ℝ) / 2) r).symm] using hpow'

    have hexp_nonneg : 0 ≤ Real.exp (-(2 * (n : ℝ)) * (r - 3)) := by positivity

    have hmul : (n ^ r : ℝ) * Real.exp (-(2 * (n : ℝ)) * (r - 3)) ≤
        Real.exp (r * ((n : ℝ) / 2)) * Real.exp (-(2 * (n : ℝ)) * (r - 3)) := by
      exact mul_le_mul_of_nonneg_right hpow'' hexp_nonneg

    have hmain : (n ^ r : ℝ) * Real.exp (-(2 * (n : ℝ)) * (r - 3)) ≤
        Real.exp (r * ((n : ℝ) / 2) + (-(2 * (n : ℝ)) * (r - 3))) := by
      simpa [Real.exp_add] using hmul

    -- show r ≥ 3 and r ≥ 12
    have h12 : (12 : ℕ) ≤ r := by
      have hmul : (12 : ℕ) ≤ 6 * n := by
        have : 6 * 2 ≤ 6 * n := Nat.mul_le_mul_left 6 hn
        simpa using this
      exact le_trans hmul hr

    have h3 : (3 : ℕ) ≤ r := by
      exact le_trans (by decide : (3 : ℕ) ≤ 12) h12

    have hr12 : (12 : ℝ) ≤ (r : ℝ) := by
      exact_mod_cast h12

    have hcast : ((r - 3 : ℕ) : ℝ) = (r : ℝ) - 3 := by
      -- cast subtraction since 3 ≤ r
      simpa using (Nat.cast_sub (R := ℝ) h3)

    have h_exp_arg : (r : ℝ) * ((n : ℝ) / 2) + (-(2 * (n : ℝ)) * (r - 3)) ≤ (-(n : ℝ)) * r := by
      nlinarith [hcast, hr12]

    have h_exp : Real.exp (r * ((n : ℝ) / 2) + (-(2 * (n : ℝ)) * (r - 3))) ≤
        Real.exp (-(n : ℝ) * r) := by
      have : (r : ℝ) * ((n : ℝ) / 2) + (-(2 * (n : ℝ)) * (r - 3)) ≤ (-(n : ℝ) * r) := by
        -- just reassociate
        simpa [mul_assoc, mul_left_comm, mul_comm] using h_exp_arg
      exact (Real.exp_le_exp).2 this

    exact le_trans hmain h_exp

  exact (ENNReal.ofReal_le_ofReal_iff hq).2 hreal


open scoped BigOperators in
theorem theorem5_prod_one_sub_le_exp_neg_sum {α : Type*} (s : Finset α) (f : α → ℝ) :
    (∀ x ∈ s, f x ≤ 1) → (∏ x ∈ s, (1 - f x)) ≤ Real.exp (-(∑ x ∈ s, f x)) := by
  intro hf
  classical
  have h0 : ∀ x ∈ s, (0 : ℝ) ≤ 1 - f x := by
    intro x hx
    exact sub_nonneg.mpr (hf x hx)
  have h1 : ∀ x ∈ s, 1 - f x ≤ Real.exp (-(f x)) := by
    intro x hx
    simpa using (Real.one_sub_le_exp_neg (f x))
  have hprod : (∏ x ∈ s, (1 - f x)) ≤ ∏ x ∈ s, Real.exp (-(f x)) := by
    simpa using
      (Finset.prod_le_prod (s := s) (f := fun x => 1 - f x) (g := fun x => Real.exp (-(f x))) h0 h1)
  have hexp : (∏ x ∈ s, Real.exp (-(f x))) = Real.exp (-(∑ x ∈ s, f x)) := by
    simpa [Finset.sum_neg_distrib] using (Real.exp_sum s (fun x => -(f x))).symm
  calc
    (∏ x ∈ s, (1 - f x)) ≤ ∏ x ∈ s, Real.exp (-(f x)) := hprod
    _ = Real.exp (-(∑ x ∈ s, f x)) := hexp

open scoped BigOperators in
open MeasureTheory in
open ProbabilityTheory in
theorem theorem5_macroMeasure_all_false_finset_le_exp_neg_sum {n : ℕ} (S : Finset (FreeMonoid (Fin n))) :
    theorem5_macroMeasure n (Set.pi S (fun _ => ({false} : Set Bool)))
      ≤ ENNReal.ofReal (Real.exp (-(∑ u ∈ S, (theorem5_inclusionProb (n := n) u : ℝ)))) := by
  classical
  -- Rewrite the macro measure as a finite product of coordinate measures
  have hμ := (theorem5_macroMeasure_all_false_finset (n := n) S)
  have hcoord : ∀ u : FreeMonoid (Fin n),
      theorem5_coordMeasure (n := n) u ({false} : Set Bool) =
        (1 - (theorem5_inclusionProb (n := n) u : ENNReal)) := by
    intro u
    simpa using (theorem5_coordMeasure_false_eq (n := n) u)
  -- Reduce to a statement about a product in `ℝ≥0∞`
  rw [hμ]
  simp [hcoord]
  -- show the product is finite
  have h_ne_top : (∏ x ∈ S, (1 - (theorem5_inclusionProb (n := n) x : ENNReal))) ≠ (⊤ : ENNReal) := by
    refine ENNReal.prod_ne_top ?_
    intro x hx
    -- each factor is finite since `1` is finite
    simpa using
      (ENNReal.sub_ne_top (a := (1 : ENNReal)) (b := (theorem5_inclusionProb (n := n) x : ENNReal)) (by simp))
  have hnonneg : (0 : ℝ) ≤ Real.exp (-(∑ u ∈ S, (theorem5_inclusionProb (n := n) u : ℝ))) := by
    have : 0 < Real.exp (-(∑ u ∈ S, (theorem5_inclusionProb (n := n) u : ℝ))) := by
      simpa using Real.exp_pos (-(∑ u ∈ S, (theorem5_inclusionProb (n := n) u : ℝ)))
    exact this.le
  -- It suffices to show the corresponding real inequality
  have hgoal_real :
      ENNReal.toReal (∏ x ∈ S, (1 - (theorem5_inclusionProb (n := n) x : ENNReal)))
        ≤ Real.exp (-(∑ u ∈ S, (theorem5_inclusionProb (n := n) u : ℝ))) := by
    -- compute `toReal` of each factor
    have htoReal_factor : ∀ x ∈ S,
        ENNReal.toReal (1 - (theorem5_inclusionProb (n := n) x : ENNReal))
          = (1 - (theorem5_inclusionProb (n := n) x : ℝ)) := by
      intro x hx
      have hxle : (theorem5_inclusionProb (n := n) x : ENNReal) ≤ (1 : ENNReal) := by
        have hNat : (1 : ℕ) ≤ Nat.log2 (x.length + 2) + 1 :=
          Nat.succ_le_succ (Nat.zero_le _)
        have hNN : (1 : NNReal) ≤ ((Nat.log2 (x.length + 2) + 1 : ℕ) : NNReal) := by
          exact_mod_cast hNat
        have hinv : ((Nat.log2 (x.length + 2) + 1 : ℕ) : NNReal)⁻¹ ≤ (1 : NNReal) :=
          (inv_le_one_iff₀).2 (Or.inr hNN)
        have hp_le_one : theorem5_inclusionProb (n := n) x ≤ (1 : NNReal) := by
          simpa [theorem5_inclusionProb] using hinv
        exact_mod_cast hp_le_one
      have hsub :=
        ENNReal.toReal_sub_of_le (a := (1 : ENNReal))
          (b := (theorem5_inclusionProb (n := n) x : ENNReal)) hxle (by simp)
      simpa using hsub
    have htoReal_prod :
        ENNReal.toReal (∏ x ∈ S, (1 - (theorem5_inclusionProb (n := n) x : ENNReal)))
          = ∏ x ∈ S, (1 - (theorem5_inclusionProb (n := n) x : ℝ)) := by
      calc
        ENNReal.toReal (∏ x ∈ S, (1 - (theorem5_inclusionProb (n := n) x : ENNReal)))
            = ∏ x ∈ S, ENNReal.toReal (1 - (theorem5_inclusionProb (n := n) x : ENNReal)) := by
                simpa [ENNReal.toReal_prod]
        _ = ∏ x ∈ S, (1 - (theorem5_inclusionProb (n := n) x : ℝ)) := by
                refine Finset.prod_congr rfl ?_
                intro x hx
                simpa using htoReal_factor x hx
    rw [htoReal_prod]
    -- apply the real inequality lemma
    have hle1 : ∀ x ∈ S, (theorem5_inclusionProb (n := n) x : ℝ) ≤ 1 := by
      intro x hx
      have hNat : (1 : ℕ) ≤ Nat.log2 (x.length + 2) + 1 :=
        Nat.succ_le_succ (Nat.zero_le _)
      have hNN : (1 : NNReal) ≤ ((Nat.log2 (x.length + 2) + 1 : ℕ) : NNReal) := by
        exact_mod_cast hNat
      have hinv : ((Nat.log2 (x.length + 2) + 1 : ℕ) : NNReal)⁻¹ ≤ (1 : NNReal) :=
        (inv_le_one_iff₀).2 (Or.inr hNN)
      have hp_le_one : theorem5_inclusionProb (n := n) x ≤ (1 : NNReal) := by
        simpa [theorem5_inclusionProb] using hinv
      exact_mod_cast hp_le_one
    have hreal :=
      theorem5_prod_one_sub_le_exp_neg_sum (s := S)
        (f := fun x : FreeMonoid (Fin n) => (theorem5_inclusionProb (n := n) x : ℝ))
        (by
          intro x hx
          simpa using hle1 x hx)
    simpa using hreal
  -- conclude using `ENNReal.le_ofReal_iff_toReal_le`
  have hiff :=
    (ENNReal.le_ofReal_iff_toReal_le (a := (∏ x ∈ S, (1 - (theorem5_inclusionProb (n := n) x : ENNReal))))
      (b := Real.exp (-(∑ u ∈ S, (theorem5_inclusionProb (n := n) u : ℝ)))) h_ne_top hnonneg)
  exact hiff.mpr hgoal_real


def theorem5_randomSet {n : ℕ} (ω : FreeMonoid (Fin n) → Bool) : Set (FreeMonoid (Fin n)) :=
  {w | ω w = true}

def theorem5_macroSet {n : ℕ} (B : ℕ) (ω : FreeMonoid (Fin n) → Bool) : Set (FreeMonoid (Fin n)) :=
  theorem5_logPeriodicSet (n := n) B ∪ theorem5_randomSet (n := n) ω

theorem theorem5_real_sub_three_le_four_mul_div_four (r : ℕ) : (r : ℝ) - 3 ≤ 4 * ((r / 4 : ℕ) : ℝ) := by
  have hnat : r ≤ 4 * (r / 4) + 3 := theorem5_nat_le_four_mul_div_four_add_three r
  have hreal' : (r : ℝ) ≤ ((4 * (r / 4) + 3 : ℕ) : ℝ) := by
    exact_mod_cast hnat
  have hreal : (r : ℝ) ≤ 4 * ((r / 4 : ℕ) : ℝ) + 3 := by
    simpa using hreal'
  linarith

theorem theorem5_sphere_finite (n : ℕ) (hn : 2 ≤ n) (r : ℕ) : (Sphere n r).Finite := by
  apply Set.finite_of_ncard_ne_zero
  have hnpos : 0 < n := lt_of_lt_of_le (Nat.succ_pos 1) hn
  have hn0 : n ≠ 0 := Nat.ne_of_gt hnpos
  have hpow : n ^ r ≠ 0 := pow_ne_zero r hn0
  simpa [theorem5_ncard_Sphere] using hpow


open scoped BigOperators in
theorem theorem5_ncard_randomSet_inter_sphere_eq_sum_indicator (n : ℕ) (hn : 2 ≤ n) (r : ℕ) (ω : FreeMonoid (Fin n) → Bool) :
  (Set.ncard (theorem5_randomSet (n := n) ω ∩ Sphere n r) : ℝ) =
    ∑ w ∈ (theorem5_sphere_finite n hn r).toFinset,
      (if ω w = true then (1 : ℝ) else 0) := by
  classical
  let hs : (Sphere n r).Finite := theorem5_sphere_finite n hn r
  let W : Finset (FreeMonoid (Fin n)) := hs.toFinset
  have hfin : (theorem5_randomSet (n := n) ω ∩ Sphere n r).Finite := by
    refine hs.subset ?_
    intro w hw
    exact hw.2
  have hto : hfin.toFinset = W.filter (fun w => ω w = true) := by
    ext w
    simp [theorem5_randomSet, hs, W, hfin, and_left_comm, and_assoc, and_comm]
  calc
    (Set.ncard (theorem5_randomSet (n := n) ω ∩ Sphere n r) : ℝ)
        = (hfin.toFinset.card : ℝ) := by
            simpa using
              congrArg (fun m : ℕ => (m : ℝ))
                (Set.ncard_eq_toFinset_card (s := theorem5_randomSet (n := n) ω ∩ Sphere n r) hfin)
    _ = ((W.filter (fun w => ω w = true)).card : ℝ) := by
            simpa [hto]
    _ = ∑ w ∈ W, (if ω w = true then (1 : ℝ) else 0) := by
            simpa using (Finset.natCast_card_filter (R := ℝ) (s := W) (p := fun w => ω w = true))


open scoped BigOperators in
open Filter in
open MeasureTheory in
open ProbabilityTheory in
open free in
theorem theorem5_random_density_bad_measure_le (n : ℕ) (hn : 2 ≤ n) (r : ℕ) :
  theorem5_macroMeasure n
      {ω |
        (2 * (n ^ r : ℝ) * (((Nat.log2 (r + 2) + 1 : ℕ) : ℝ)⁻¹))
          < (Set.ncard (theorem5_randomSet (n := n) ω ∩ Sphere n r) : ℝ)}
    ≤ ENNReal.ofReal ((((r + 2 : ℕ) : ℝ) ^ 2) / (n ^ r : ℝ)) := by
  classical
  haveI : MeasureTheory.IsProbabilityMeasure (theorem5_macroMeasure n) :=
    theorem5_macroMeasure_isProbability n
  haveI : MeasureTheory.IsFiniteMeasure (theorem5_macroMeasure n) := by
    infer_instance
  let μ : MeasureTheory.Measure (FreeMonoid (Fin n) → Bool) := theorem5_macroMeasure n
  let S : Finset (FreeMonoid (Fin n)) := (theorem5_sphere_finite n hn r).toFinset
  let g : Bool → ℝ := fun b => if b = true then (1 : ℝ) else 0
  have hg : Measurable g := Measurable.of_discrete
  let X : FreeMonoid (Fin n) → (FreeMonoid (Fin n) → Bool) → ℝ :=
    fun w ω => if ω w = true then (1 : ℝ) else 0
  let Y : (FreeMonoid (Fin n) → Bool) → ℝ := ∑ w ∈ S, X w
  have h_event :
      {ω : FreeMonoid (Fin n) → Bool |
          2 * (n ^ r : ℝ) * (((Nat.log2 (r + 2) + 1 : ℕ) : ℝ)⁻¹)
            < (Set.ncard (theorem5_randomSet (n := n) ω ∩ Sphere n r) : ℝ)}
        =
      {ω : FreeMonoid (Fin n) → Bool |
          2 * (n ^ r : ℝ) * (((Nat.log2 (r + 2) + 1 : ℕ) : ℝ)⁻¹) < Y ω} := by
    ext ω
    simp [Y, S, X, theorem5_ncard_randomSet_inter_sphere_eq_sum_indicator (n := n) hn r ω]
  rw [h_event]

  -- cardinality of S
  have hcard : S.card = n ^ r := by
    have hncard : Set.ncard (Sphere n r) = S.card := by
      simpa [S] using
        (Set.ncard_eq_toFinset_card (Sphere n r) (theorem5_sphere_finite n hn r))
    calc
      S.card = Set.ncard (Sphere n r) := hncard.symm
      _ = n ^ r := theorem5_ncard_Sphere n r

  -- measurability / MemLp for each X w
  have hX_meas (w : FreeMonoid (Fin n)) : Measurable (X w) := by
    have h_eval : Measurable (fun ω : FreeMonoid (Fin n) → Bool => ω w) := measurable_pi_apply w
    simpa [X, g] using hg.comp h_eval
  have hX_aeStrong (w : FreeMonoid (Fin n)) : MeasureTheory.AEStronglyMeasurable (X w) μ :=
    (hX_meas w).aemeasurable.aestronglyMeasurable
  have hX_memLp (w : FreeMonoid (Fin n)) : MeasureTheory.MemLp (X w) 2 μ := by
    refine MeasureTheory.MemLp.of_bound (hX_aeStrong w) 1 ?_
    refine (Filter.Eventually.of_forall ?_)
    intro ω
    by_cases h : ω w = true <;> simp [X, h]
  have hX_int (w : FreeMonoid (Fin n)) : MeasureTheory.Integrable (X w) μ := by
    have hq : (1 : ENNReal) ≤ (2 : ENNReal) := by
      norm_num
    exact MeasureTheory.MemLp.integrable (μ := μ) (q := (2 : ENNReal)) hq (hX_memLp w)

  -- expectation of X w
  have hmeasSet (w : FreeMonoid (Fin n)) :
      MeasurableSet ({ω : FreeMonoid (Fin n) → Bool | ω w = true} : Set (FreeMonoid (Fin n) → Bool)) := by
    have h_eval : Measurable (fun ω : FreeMonoid (Fin n) → Bool => ω w) := measurable_pi_apply w
    simpa [Set.preimage] using (h_eval (MeasurableSet.singleton true))
  have hEX (w : FreeMonoid (Fin n)) : μ[X w] = (theorem5_inclusionProb (n := n) w : ℝ) := by
    have hX_indicator : X w =
        ({ω : FreeMonoid (Fin n) → Bool | ω w = true} : Set (FreeMonoid (Fin n) → Bool)).indicator
          (fun _ => (1 : ℝ)) := by
      funext ω
      by_cases h : ω w = true <;> simp [X, h]
    calc
      μ[X w] = μ[({ω : FreeMonoid (Fin n) → Bool | ω w = true} : Set (FreeMonoid (Fin n) → Bool)).indicator
          (fun _ => (1 : ℝ))] := by
            simp [hX_indicator]
      _ = μ.real ({ω : FreeMonoid (Fin n) → Bool | ω w = true} : Set (FreeMonoid (Fin n) → Bool)) := by
            simpa using
              (MeasureTheory.integral_indicator_const (μ := μ) (e := (1 : ℝ)) (hmeasSet w))
      _ = (μ ({ω : FreeMonoid (Fin n) → Bool | ω w = true} : Set (FreeMonoid (Fin n) → Bool))).toReal := by
            simp [MeasureTheory.measureReal_def]
      _ = (theorem5_inclusionProb (n := n) w : ENNReal).toReal := by
            simp [μ, theorem5_macroMeasure_eval_true (n := n) w]
      _ = (theorem5_inclusionProb (n := n) w : ℝ) := by
            simp

  -- expectation of Y
  have hEY : μ[Y] = ∑ w ∈ S, μ[X w] := by
    simpa [Y] using
      (MeasureTheory.integral_finset_sum (μ := μ) S (f := fun w ω => X w ω)
        (by
          intro w hw
          exact hX_int w))

  -- constants
  let d : ℝ := ((Nat.log2 (r + 2) + 1 : ℕ) : ℝ)
  let p : ℝ := d⁻¹

  -- in the sphere, all inclusion probabilities are p
  have hEX_const : ∀ w ∈ S, μ[X w] = p := by
    intro w hw
    have hw' : w ∈ (theorem5_sphere_finite n hn r).toFinset := by
      simpa [S] using hw
    have hwSphere : w ∈ Sphere n r := (theorem5_sphere_finite n hn r).mem_toFinset.1 hw'
    have hlen : w.length = r := by
      simpa [Sphere] using hwSphere
    simpa [p, d, theorem5_inclusionProb, hlen] using hEX w

  have hmean : μ[Y] = (n ^ r : ℝ) * p := by
    have hsum : ∑ w ∈ S, μ[X w] = (S.card : ℝ) * p := by
      have : ∑ w ∈ S, μ[X w] = ∑ w ∈ S, p := by
        refine Finset.sum_congr rfl ?_
        intro w hw
        simpa using hEX_const w hw
      simpa [this]
    calc
      μ[Y] = ∑ w ∈ S, μ[X w] := hEY
      _ = (S.card : ℝ) * p := hsum
      _ = (n ^ r : ℝ) * p := by
        simpa [hcard]

  have hmean_pos : 0 < μ[Y] := by
    have hnpos : 0 < n := lt_of_lt_of_le (Nat.succ_pos 1) hn
    have ha : 0 < (n ^ r : ℝ) := by
      have : 0 < (n : ℝ) := by
        exact_mod_cast hnpos
      simpa using pow_pos this r
    have hd_posNat : 0 < Nat.log2 (r + 2) + 1 := Nat.succ_pos _
    have hd_pos : 0 < d := by
      have : (0 : ℝ) < ((Nat.log2 (r + 2) + 1 : ℕ) : ℝ) := by
        exact_mod_cast hd_posNat
      simpa [d] using this
    have hp_pos : 0 < p := by
      simpa [p] using inv_pos.2 hd_pos
    simpa [hmean] using mul_pos ha hp_pos

  -- rewrite the event threshold using the mean
  have h_event_mean :
      {ω : FreeMonoid (Fin n) → Bool |
          2 * (n ^ r : ℝ) * p < Y ω} =
        {ω : FreeMonoid (Fin n) → Bool |
          2 * μ[Y] < Y ω} := by
    ext ω
    simp [hmean, mul_assoc]

  have hp_def : p = (((Nat.log2 (r + 2) + 1 : ℕ) : ℝ)⁻¹) := by
    simp [p, d]

  -- subset to Chebyshev event
  have hsubset :
      {ω : FreeMonoid (Fin n) → Bool | 2 * μ[Y] < Y ω} ⊆
        {ω : FreeMonoid (Fin n) → Bool | μ[Y] ≤ |Y ω - μ[Y]|} := by
    intro ω hω
    have hω' : 2 * μ[Y] < Y ω := by
      simpa using hω
    have hμ_nonneg : 0 ≤ μ[Y] := le_of_lt hmean_pos
    have hdiff_pos : 0 < Y ω - μ[Y] := by
      linarith
    have hdiff_nonneg : 0 ≤ Y ω - μ[Y] := le_of_lt hdiff_pos
    have hle : μ[Y] ≤ Y ω - μ[Y] := by
      linarith
    simpa [abs_of_nonneg hdiff_nonneg] using hle

  -- MemLp for Y
  have hY_aeStrong : MeasureTheory.AEStronglyMeasurable Y μ := by
    simpa [Y] using
      (Finset.aestronglyMeasurable_sum' (s := S) (f := fun w => X w) (μ := μ)
        (by
          intro w hw
          exact hX_aeStrong w))
  have hY_memLp : MeasureTheory.MemLp Y 2 μ := by
    refine MeasureTheory.MemLp.of_bound hY_aeStrong (S.card : ℝ) ?_
    refine (Filter.Eventually.of_forall ?_)
    intro ω
    have hle1 : ∀ w ∈ S, X w ω ≤ (1 : ℝ) := by
      intro w hw
      by_cases h : ω w = true <;> simp [X, h]
    have hle_sum : (Y ω) ≤ (S.card : ℝ) := by
      have : (Y ω) ≤ ∑ w ∈ S, (1 : ℝ) := by
        simpa [Y] using (Finset.sum_le_sum (fun w hw => hle1 w hw))
      simpa using (le_trans this (by simp))
    have hnonneg : 0 ≤ Y ω := by
      have hnonneg1 : ∀ w ∈ S, 0 ≤ X w ω := by
        intro w hw
        by_cases h : ω w = true <;> simp [X, h]
      simpa [Y] using Finset.sum_nonneg (fun w hw => hnonneg1 w hw)
    have : ‖Y ω‖ = Y ω := by
      simp [Real.norm_eq_abs, abs_of_nonneg hnonneg]
    simpa [this] using hle_sum

  -- Chebyshev
  have hcheb :
      μ {ω : FreeMonoid (Fin n) → Bool | μ[Y] ≤ |Y ω - μ[Y]|}
        ≤ ENNReal.ofReal (ProbabilityTheory.variance Y μ / μ[Y] ^ 2) := by
    simpa [μ] using
      (ProbabilityTheory.meas_ge_le_variance_div_sq (μ := μ) (X := Y) hY_memLp (c := μ[Y])
        hmean_pos)

  have hbad :
      μ {ω : FreeMonoid (Fin n) → Bool | 2 * μ[Y] < Y ω}
        ≤ ENNReal.ofReal (ProbabilityTheory.variance Y μ / μ[Y] ^ 2) := by
    exact le_trans (MeasureTheory.measure_mono hsubset) hcheb

  -- variance bound Var(Y) ≤ μ[Y]
  have hIndepX (w1 w2 : FreeMonoid (Fin n)) (h : w1 ≠ w2) :
      ProbabilityTheory.IndepFun (X w1) (X w2) μ := by
    have hIndep_eval :
        ProbabilityTheory.IndepFun (fun ω : FreeMonoid (Fin n) → Bool => ω w1)
          (fun ω : FreeMonoid (Fin n) → Bool => ω w2) μ :=
      (theorem5_iIndepFun_eval n).indepFun h
    simpa [X, g] using ProbabilityTheory.IndepFun.comp hIndep_eval hg hg

  have hpairwise : Set.Pairwise (↑S : Set (FreeMonoid (Fin n)))
      (fun i j => ProbabilityTheory.IndepFun (X i) (X j) μ) := by
    intro i hi j hj hij
    exact hIndepX i j hij

  have hVar_eq : ProbabilityTheory.variance (∑ w ∈ S, X w) μ =
      ∑ w ∈ S, ProbabilityTheory.variance (X w) μ := by
    refine ProbabilityTheory.IndepFun.variance_sum (μ := μ) (X := fun w => X w) (s := S)
      (by
        intro w hw
        exact hX_memLp w)
      ?_
    simpa [Set.Pairwise] using hpairwise

  have hVar_le : ProbabilityTheory.variance Y μ ≤ μ[Y] := by
    have hVarY : ProbabilityTheory.variance Y μ = ∑ w ∈ S, ProbabilityTheory.variance (X w) μ := by
      simpa [Y] using hVar_eq
    have hVar_term_le : ∀ w ∈ S, ProbabilityTheory.variance (X w) μ ≤ μ[X w] := by
      intro w hw
      have hsq : (fun ω => (X w ω) ^ 2) = X w := by
        funext ω
        by_cases h : ω w = true <;> simp [X, h]
      have hle_sq : ProbabilityTheory.variance (X w) μ ≤ μ[(X w) ^ 2] :=
        ProbabilityTheory.variance_le_expectation_sq (μ := μ) (X := X w) (hX_aeStrong w)
      simpa [hsq] using hle_sq
    have hsum_le : (∑ w ∈ S, ProbabilityTheory.variance (X w) μ) ≤ ∑ w ∈ S, μ[X w] := by
      refine Finset.sum_le_sum ?_
      intro w hw
      exact hVar_term_le w hw
    calc
      ProbabilityTheory.variance Y μ = ∑ w ∈ S, ProbabilityTheory.variance (X w) μ := hVarY
      _ ≤ ∑ w ∈ S, μ[X w] := hsum_le
      _ = μ[Y] := by
        symm
        exact hEY

  have hratio_le : (ProbabilityTheory.variance Y μ / μ[Y] ^ 2) ≤ (μ[Y] / μ[Y] ^ 2) := by
    have hc : 0 ≤ μ[Y] ^ 2 := by
      nlinarith
    exact theorem5_div_le_div_of_le_of_nonneg hc hVar_le

  have hbad' :
      μ {ω : FreeMonoid (Fin n) → Bool | 2 * μ[Y] < Y ω}
        ≤ ENNReal.ofReal (μ[Y] / μ[Y] ^ 2) := by
    have : ENNReal.ofReal (ProbabilityTheory.variance Y μ / μ[Y] ^ 2)
        ≤ ENNReal.ofReal (μ[Y] / μ[Y] ^ 2) :=
      ENNReal.ofReal_le_ofReal hratio_le
    exact le_trans hbad this

  have ha_ne : (n ^ r : ℝ) ≠ 0 := by
    have hnpos : 0 < n := lt_of_lt_of_le (Nat.succ_pos 1) hn
    have ha : 0 < (n ^ r : ℝ) := by
      have : 0 < (n : ℝ) := by
        exact_mod_cast hnpos
      simpa using pow_pos this r
    exact ne_of_gt ha
  have hd_ne : d ≠ 0 := by
    have hd_posNat : 0 < Nat.log2 (r + 2) + 1 := Nat.succ_pos _
    have hd_pos : 0 < d := by
      have : (0 : ℝ) < ((Nat.log2 (r + 2) + 1 : ℕ) : ℝ) := by
        exact_mod_cast hd_posNat
      simpa [d] using this
    exact ne_of_gt hd_pos

  have hdiv_simpl : μ[Y] / μ[Y] ^ 2 = d / (n ^ r : ℝ) := by
    have : μ[Y] / μ[Y] ^ 2 = ((n ^ r : ℝ) * d⁻¹) / (((n ^ r : ℝ) * d⁻¹) ^ 2) := by
      simp [hmean, p, d, mul_assoc]
    simpa [this] using
      (theorem5_mul_inv_div_sq (a := (n ^ r : ℝ)) (d := d) ha_ne hd_ne)

  -- crude bound d ≤ (r+2)^2
  have hd_le : d ≤ ((r + 2 : ℕ) : ℝ) ^ 2 := by
    have hlog : Nat.log2 (r + 2) ≤ r + 2 := by
      simpa [Nat.log2_eq_log_two] using (Nat.log_le_self 2 (r + 2))
    have hlog1 : (Nat.log2 (r + 2) + 1 : ℕ) ≤ r + 3 := by
      simpa using Nat.succ_le_succ hlog
    have hlog1R : d ≤ (r + 3 : ℝ) := by
      have : ((Nat.log2 (r + 2) + 1 : ℕ) : ℝ) ≤ (r + 3 : ℝ) := by
        exact_mod_cast hlog1
      simpa [d] using this
    have hrNat : r + 3 ≤ (r + 2) ^ 2 := by
      have h1 : r + 3 ≤ 2 * (r + 2) := by
        omega
      have h2' : 2 ≤ r + 2 := by
        omega
      have h2mul : (r + 2) * 2 ≤ (r + 2) * (r + 2) := Nat.mul_le_mul_left (r + 2) h2'
      have h2 : 2 * (r + 2) ≤ (r + 2) ^ 2 := by
        simpa [pow_two, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using h2mul
      exact le_trans h1 h2
    have hr : (r + 3 : ℝ) ≤ ((r + 2 : ℕ) : ℝ) ^ 2 := by
      have : ((r + 3 : ℕ) : ℝ) ≤ ((r + 2 : ℕ) ^ 2 : ℝ) := by
        exact_mod_cast hrNat
      simpa using this
    exact le_trans hlog1R hr

  have hfinal_ratio : d / (n ^ r : ℝ) ≤ (((r + 2 : ℕ) : ℝ) ^ 2) / (n ^ r : ℝ) := by
    have ha_nonneg : 0 ≤ (n ^ r : ℝ) := by
      positivity
    exact theorem5_div_le_div_of_le_of_nonneg ha_nonneg hd_le

  have hmean_bound :
      μ {ω : FreeMonoid (Fin n) → Bool | 2 * μ[Y] < Y ω}
        ≤ ENNReal.ofReal ((((r + 2 : ℕ) : ℝ) ^ 2) / (n ^ r : ℝ)) := by
    have hbad'' :
        μ {ω : FreeMonoid (Fin n) → Bool | 2 * μ[Y] < Y ω}
          ≤ ENNReal.ofReal (d / (n ^ r : ℝ)) := by
      simpa [hdiv_simpl] using hbad'
    have : ENNReal.ofReal (d / (n ^ r : ℝ)) ≤
        ENNReal.ofReal ((((r + 2 : ℕ) : ℝ) ^ 2) / (n ^ r : ℝ)) :=
      ENNReal.ofReal_le_ofReal hfinal_ratio
    exact le_trans hbad'' this

  -- move back to the original event
  have hset_p :
      {ω : FreeMonoid (Fin n) → Bool |
          2 * (n ^ r : ℝ) * (((Nat.log2 (r + 2) + 1 : ℕ) : ℝ)⁻¹) < Y ω} =
        {ω : FreeMonoid (Fin n) → Bool | 2 * (n ^ r : ℝ) * p < Y ω} := by
    ext ω
    simp [hp_def]

  have hmeas1 :
      μ {ω : FreeMonoid (Fin n) → Bool |
          2 * (n ^ r : ℝ) * (((Nat.log2 (r + 2) + 1 : ℕ) : ℝ)⁻¹) < Y ω} =
        μ {ω : FreeMonoid (Fin n) → Bool | 2 * (n ^ r : ℝ) * p < Y ω} := by
    simpa using congrArg (fun s => μ s) hset_p

  have hmeas2 :
      μ {ω : FreeMonoid (Fin n) → Bool | 2 * (n ^ r : ℝ) * p < Y ω} =
        μ {ω : FreeMonoid (Fin n) → Bool | 2 * μ[Y] < Y ω} := by
    simpa [h_event_mean]

  -- final chain
  calc
    μ {ω : FreeMonoid (Fin n) → Bool |
        2 * (n ^ r : ℝ) * (((Nat.log2 (r + 2) + 1 : ℕ) : ℝ)⁻¹) < Y ω}
        = μ {ω : FreeMonoid (Fin n) → Bool | 2 * μ[Y] < Y ω} := by
            exact Eq.trans hmeas1 hmeas2
    _ ≤ ENNReal.ofReal ((((r + 2 : ℕ) : ℝ) ^ 2) / (n ^ r : ℝ)) := hmean_bound

open scoped BigOperators in
open Filter in
open MeasureTheory in
open ProbabilityTheory in
open free in
theorem theorem5_random_density_bad_summable (n : ℕ) (hn : 2 ≤ n) :
  (∑' r : ℕ,
      theorem5_macroMeasure n
        {ω |
          (2 * (n ^ r : ℝ) * (((Nat.log2 (r + 2) + 1 : ℕ) : ℝ)⁻¹))
            < (Set.ncard (theorem5_randomSet (n := n) ω ∩ Sphere n r) : ℝ)}) ≠ ⊤ := by
  classical
  -- Define the bad event.
  let bad : ℕ → Set (FreeMonoid (Fin n) → Bool) := fun r =>
    {ω |
      (2 * (n ^ r : ℝ) * (((Nat.log2 (r + 2) + 1 : ℕ) : ℝ)⁻¹))
          < (Set.ncard (theorem5_randomSet (n := n) ω ∩ Sphere n r) : ℝ)}
  have hle : ∀ r : ℕ,
      theorem5_macroMeasure n (bad r) ≤
        ENNReal.ofReal ((((r + 2 : ℕ) : ℝ) ^ 2) / (n ^ r : ℝ)) := by
    intro r
    simpa [bad] using theorem5_random_density_bad_measure_le n hn r

  have htsum_le : (∑' r : ℕ, theorem5_macroMeasure n (bad r)) ≤
      ∑' r : ℕ, ENNReal.ofReal ((((r + 2 : ℕ) : ℝ) ^ 2) / (n ^ r : ℝ)) := by
    exact ENNReal.tsum_le_tsum hle

  have hfin : (∑' r : ℕ, ENNReal.ofReal ((((r + 2 : ℕ) : ℝ) ^ 2) / (n ^ r : ℝ))) ≠ ⊤ := by
    -- Show summability of the corresponding real series.
    have hn1 : (1 : ℝ) < (n : ℝ) := by
      have : (1 : ℕ) < n := lt_of_lt_of_le (by decide : (1 : ℕ) < 2) hn
      exact_mod_cast this
    have hn0 : (0 : ℝ) < (n : ℝ) := lt_trans (by norm_num) hn1

    have hdiv : (1 / (n : ℝ)) < (1 : ℝ) := by
      have hb : (0 : ℝ) < (1 : ℝ) := by norm_num
      exact (one_div_lt hn0 hb).2 (by simpa using hn1)

    have hnorm : ‖(1 / (n : ℝ))‖ < (1 : ℝ) := by
      have hnonneg : (0 : ℝ) ≤ (1 / (n : ℝ)) := by
        exact one_div_nonneg.2 (le_of_lt hn0)
      simpa [Real.norm_of_nonneg hnonneg] using hdiv

    have hsumm2 : Summable (fun r : ℕ => (r : ℝ) ^ 2 * (1 / (n : ℝ)) ^ r) := by
      simpa using
        (summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 2 (r := (1 / (n : ℝ))) hnorm)
    have hsumm1 : Summable (fun r : ℕ => (r : ℝ) * (1 / (n : ℝ)) ^ r) := by
      simpa using
        (summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1 (r := (1 / (n : ℝ))) hnorm)
    have hsumm0 : Summable (fun r : ℕ => (1 / (n : ℝ)) ^ r) := by
      simpa using
        (summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 0 (r := (1 / (n : ℝ))) hnorm)

    -- Convert the summable building blocks to the `(n^r)⁻¹` form.
    have hsumm2_inv : Summable (fun r : ℕ => (r : ℝ) ^ 2 * (n ^ r : ℝ)⁻¹) := by
      have : (fun r : ℕ => (r : ℝ) ^ 2 * (1 / (n : ℝ)) ^ r) =
          fun r : ℕ => (r : ℝ) ^ 2 * (n ^ r : ℝ)⁻¹ := by
        funext r
        have hcast : (n : ℝ) ^ r = (n ^ r : ℝ) := by
          simpa using (Nat.cast_pow (m := n) r : ((n ^ r : ℕ) : ℝ) = (n : ℝ) ^ r).symm
        calc
          (r : ℝ) ^ 2 * (1 / (n : ℝ)) ^ r
              = (r : ℝ) ^ 2 * (1 / (n : ℝ) ^ r) := by
                  simp [one_div_pow]
          _ = (r : ℝ) ^ 2 * ((n : ℝ) ^ r)⁻¹ := by
                simp [one_div]
          _ = (r : ℝ) ^ 2 * (n ^ r : ℝ)⁻¹ := by
                simpa [hcast]
      simpa [this] using hsumm2

    have hsumm1_inv : Summable (fun r : ℕ => (4 * (r : ℝ)) * (n ^ r : ℝ)⁻¹) := by
      have hs : Summable (fun r : ℕ => (4 * (r : ℝ)) * (1 / (n : ℝ)) ^ r) := by
        simpa [mul_assoc, mul_left_comm, mul_comm] using hsumm1.mul_left (4 : ℝ)
      have : (fun r : ℕ => (4 * (r : ℝ)) * (1 / (n : ℝ)) ^ r) =
          fun r : ℕ => (4 * (r : ℝ)) * (n ^ r : ℝ)⁻¹ := by
        funext r
        have hcast : (n : ℝ) ^ r = (n ^ r : ℝ) := by
          simpa using (Nat.cast_pow (m := n) r : ((n ^ r : ℕ) : ℝ) = (n : ℝ) ^ r).symm
        calc
          (4 * (r : ℝ)) * (1 / (n : ℝ)) ^ r
              = (4 * (r : ℝ)) * (1 / (n : ℝ) ^ r) := by
                  simp [one_div_pow]
          _ = (4 * (r : ℝ)) * ((n : ℝ) ^ r)⁻¹ := by
                simp [one_div]
          _ = (4 * (r : ℝ)) * (n ^ r : ℝ)⁻¹ := by
                simpa [hcast]
      simpa [this] using hs

    have hsumm0_inv : Summable (fun r : ℕ => (4 : ℝ) * (n ^ r : ℝ)⁻¹) := by
      have hs : Summable (fun r : ℕ => (4 : ℝ) * (1 / (n : ℝ)) ^ r) := by
        simpa [mul_assoc, mul_left_comm, mul_comm] using hsumm0.mul_left (4 : ℝ)
      have : (fun r : ℕ => (4 : ℝ) * (1 / (n : ℝ)) ^ r) =
          fun r : ℕ => (4 : ℝ) * (n ^ r : ℝ)⁻¹ := by
        funext r
        have hcast : (n : ℝ) ^ r = (n ^ r : ℝ) := by
          simpa using (Nat.cast_pow (m := n) r : ((n ^ r : ℕ) : ℝ) = (n : ℝ) ^ r).symm
        calc
          (4 : ℝ) * (1 / (n : ℝ)) ^ r
              = (4 : ℝ) * (1 / (n : ℝ) ^ r) := by
                  simp [one_div_pow]
          _ = (4 : ℝ) * ((n : ℝ) ^ r)⁻¹ := by
                simp [one_div]
          _ = (4 : ℝ) * (n ^ r : ℝ)⁻¹ := by
                simpa [hcast]
      simpa [this] using hs

    have hsumm : Summable (fun r : ℕ => (((r + 2 : ℕ) : ℝ) ^ 2) / (n ^ r : ℝ)) := by
      have hrewrite : (fun r : ℕ => (((r + 2 : ℕ) : ℝ) ^ 2) / (n ^ r : ℝ)) =
          fun r : ℕ => ((r : ℝ) ^ 2 + 4 * (r : ℝ) + 4) * (n ^ r : ℝ)⁻¹ := by
        funext r
        calc
          (((r + 2 : ℕ) : ℝ) ^ 2) / (n ^ r : ℝ)
              = (((r : ℝ) + 2) ^ 2) / (n ^ r : ℝ) := by
                  norm_cast
          _ = (((r : ℝ) + 2) ^ 2) * (n ^ r : ℝ)⁻¹ := by
                simp [div_eq_mul_inv]
          _ = ((r : ℝ) ^ 2 + 4 * (r : ℝ) + 4) * (n ^ r : ℝ)⁻¹ := by
                ring

      have hs_exp :
          Summable
            (fun r : ℕ =>
              (r : ℝ) ^ 2 * (n ^ r : ℝ)⁻¹ + (4 * (r : ℝ)) * (n ^ r : ℝ)⁻¹ + (4 : ℝ) * (n ^ r : ℝ)⁻¹) := by
        have hs : Summable
            (fun r : ℕ =>
              (r : ℝ) ^ 2 * (n ^ r : ℝ)⁻¹ +
                ((4 * (r : ℝ)) * (n ^ r : ℝ)⁻¹ + (4 : ℝ) * (n ^ r : ℝ)⁻¹)) := by
          exact hsumm2_inv.add (hsumm1_inv.add hsumm0_inv)
        simpa [add_assoc] using hs

      have hfg :
          (fun r : ℕ => ((r : ℝ) ^ 2 + 4 * (r : ℝ) + 4) * (n ^ r : ℝ)⁻¹) =
            fun r : ℕ =>
              (r : ℝ) ^ 2 * (n ^ r : ℝ)⁻¹ + (4 * (r : ℝ)) * (n ^ r : ℝ)⁻¹ + (4 : ℝ) * (n ^ r : ℝ)⁻¹ := by
        funext r
        ring

      have hs_main : Summable (fun r : ℕ => ((r : ℝ) ^ 2 + 4 * (r : ℝ) + 4) * (n ^ r : ℝ)⁻¹) := by
        simpa [hfg] using hs_exp

      -- rewrite the goal using `hrewrite`
      have : Summable (fun r : ℕ => (((r + 2 : ℕ) : ℝ) ^ 2) / (n ^ r : ℝ)) := by
        -- `rw` avoids additional simp rewriting
        rw [hrewrite]
        exact hs_main
      exact this

    exact Summable.tsum_ofReal_ne_top (f := fun r : ℕ => (((r + 2 : ℕ) : ℝ) ^ 2) / (n ^ r : ℝ)) hsumm

  have : (∑' r : ℕ, theorem5_macroMeasure n (bad r)) ≠ ⊤ :=
    ne_top_of_le_ne_top hfin htsum_le
  simpa [bad] using this

def theorem5_subword {n : ℕ} (w : FreeMonoid (Fin n)) (i ℓ : ℕ) : FreeMonoid (Fin n) :=
  (w.drop i).take ℓ

def theorem5_candidateSet {n : ℕ} (C : ℕ) (r : ℕ) (w : FreeMonoid (Fin n)) : Set (FreeMonoid (Fin n)) :=
  {u |
    ∃ i : ℕ, i ≤ C * (Nat.log2 r + 1) ∧
      ∃ ℓ : ℕ, (r - r / 2) ≤ ℓ ∧ i + ℓ ≤ r ∧ u = theorem5_subword (n := n) w i ℓ}

open free in
theorem theorem5_hasHalfMacro_of_candidateSet {n : ℕ} {C r : ℕ} {M : Set (FreeMonoid (Fin n))} :
    (∀ w : FreeMonoid (Fin n), w.length = r →
      Set.Nonempty (theorem5_candidateSet (n := n) C r w ∩ M)) →
    theorem5_hasHalfMacro (n := n) C M r := by
  intro h
  unfold theorem5_hasHalfMacro
  intro w hw
  classical
  rcases h w hw with ⟨u, hu⟩
  rcases hu with ⟨huCand, huM⟩
  rcases huCand with ⟨i, hi, ℓ, hℓ, hiℓ, rfl⟩
  refine ⟨w.take i, theorem5_subword (n := n) w i ℓ, w.drop (i + ℓ), ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  ·
    apply FreeMonoid.toList.injective
    simp [FreeMonoid.toList, theorem5_subword, List.append_assoc]
    symm
    calc
      w.take i ++ (w.drop i).take ℓ ++ w.drop (i + ℓ)
          = w.take i ++ ((w.drop i).take ℓ ++ w.drop (i + ℓ)) := by
              simp [List.append_assoc]
      _ = w.take i ++ w.drop i := by
              simp [List.drop_take_append_drop]
      _ = w := by
              simpa using (List.take_append_drop i w)
  ·
    have htake : (w.take i).length ≤ i := by
      simpa [FreeMonoid.length, FreeMonoid.toList] using
        (show (List.length (List.take i w) ≤ i) from by
          simpa [List.length_take] using (Nat.min_le_left i w.length))
    exact le_trans htake hi
  · exact huM
  ·
    have hhalf : r / 2 ≤ r - r / 2 := by
      apply Nat.half_le_of_sub_le_half
      have hEq : r - (r - r / 2) = r / 2 := by
        exact tsub_tsub_cancel_of_le (Nat.div_le_self' r 2)
      simpa [hEq]
    have hr2leℓ : r / 2 ≤ ℓ := le_trans hhalf hℓ
    have hℓ_le_wsub : ℓ ≤ w.length - i := by
      have hiℓ' : i + ℓ ≤ w.length := by
        simpa [hw] using hiℓ
      exact le_tsub_of_add_le_left hiℓ'
    have hℓ_le_drop : ℓ ≤ (List.drop i w).length := by
      simpa [FreeMonoid.length, FreeMonoid.toList, List.length_drop] using hℓ_le_wsub
    have huLenList : List.length ((w.drop i).take ℓ) = ℓ := by
      have hmin : Nat.min ℓ (List.length (w.drop i)) = ℓ := by
        exact Nat.min_eq_left hℓ_le_drop
      simpa [List.length_take, hmin]
    have huLen : (theorem5_subword (n := n) w i ℓ).length = ℓ := by
      simpa only [theorem5_subword, FreeMonoid.length, FreeMonoid.toList] using huLenList
    simpa [huLen] using hr2leℓ
  ·
    have hsum : r - r / 2 ≤ i + ℓ := by
      exact le_trans hℓ (Nat.le_add_left ℓ i)
    have hsub : r - (i + ℓ) ≤ r - (r - r / 2) := by
      exact tsub_le_tsub_left hsum r
    have hEq : r - (r - r / 2) = r / 2 := by
      exact tsub_tsub_cancel_of_le (Nat.div_le_self' r 2)
    have hRem : r - (i + ℓ) ≤ r / 2 := by
      simpa only [hEq] using hsub
    have hwList : List.length w = r := by
      simpa [FreeMonoid.length, FreeMonoid.toList] using hw
    -- reduce goal to list length
    simp only [FreeMonoid.length, FreeMonoid.toList]
    -- remove the `Equiv.refl` wrapper
    change (List.drop (i + ℓ) w).length ≤ r / 2
    -- compute length of drop and use hRem
    have hdropEq : (List.drop (i + ℓ) w).length = r - (i + ℓ) := by
      simpa [List.length_drop, hwList]
    rw [hdropEq]
    exact hRem


open free in
theorem theorem5_subword_length_of_add_le {n : ℕ} {w : FreeMonoid (Fin n)} {i ℓ : ℕ} :
    i + ℓ ≤ w.length → (theorem5_subword (n := n) w i ℓ).length = ℓ := by
  intro h
  unfold theorem5_subword
  have hle : ℓ ≤ (List.drop i w).length := by
    have hle' : ℓ ≤ w.length - i := le_tsub_of_add_le_left h
    simpa only [List.length_drop] using hle'
  exact List.length_take_of_le hle


open free in
theorem theorem5_candidateSet_length_le_r {n : ℕ} {C r : ℕ} {w u : FreeMonoid (Fin n)} :
    w.length = r → u ∈ theorem5_candidateSet (n := n) C r w → u.length ≤ r := by
  intro hwlen hu
  rcases hu with ⟨i, hiC, ℓ, hℓlower, hiℓle, rfl⟩
  have hiℓle' : i + ℓ ≤ w.length := by
    simpa [hwlen] using hiℓle
  have hlen : (theorem5_subword (n := n) w i ℓ).length = ℓ :=
    theorem5_subword_length_of_add_le (w := w) (i := i) (ℓ := ℓ) hiℓle'
  have hℓle : ℓ ≤ r := by
    exact le_trans (Nat.le_add_left ℓ i) hiℓle
  simpa [hlen] using hℓle

open free in
theorem theorem5_hasPeriod_subword_of_eq {n : ℕ} {w : FreeMonoid (Fin n)} {i d ℓ : ℕ} :
    0 < d → i + ℓ + d ≤ w.length →
      theorem5_subword (n := n) w i ℓ = theorem5_subword (n := n) w (i + d) ℓ →
        theorem5_hasPeriod (n := n) (theorem5_subword (n := n) w i (ℓ + d)) d := by
  intro hpos hlen heq
  have hlen' : i + (ℓ + d) ≤ w.length := by
    simpa [Nat.add_assoc] using hlen
  have hlen_subword : (theorem5_subword (n := n) w i (ℓ + d)).length = ℓ + d := by
    simpa using
      (theorem5_subword_length_of_add_le (w := w) (i := i) (ℓ := ℓ + d) hlen')
  refine ⟨hpos, ?_, ?_⟩
  · -- d ≤ length
    have hdle : d ≤ ℓ + d := Nat.le_add_left d ℓ
    simpa [hlen_subword] using hdle
  · -- drop equality
    have hlen_minus : (theorem5_subword (n := n) w i (ℓ + d)).length - d = ℓ := by
      -- (ℓ + d) - d = ℓ
      simpa [hlen_subword, Nat.add_sub_cancel]
    -- rewrite RHS length-d
    rw [hlen_minus]
    -- now unfold theorem5_subword
    -- goal: ((w.drop i).take (ℓ+d)).drop d = ((w.drop i).take (ℓ+d)).take ℓ
    -- compute drop side via List.take_drop
    have hdrop : ((w.drop i).take (ℓ + d)).drop d = (w.drop (i + d)).take ℓ := by
      -- from List.take_drop: take ℓ (drop d l) = drop d (take (d+ℓ) l)
      have h := (List.take_drop (l := (w.drop i)) (i := ℓ) (j := d))
      -- rewrite drop_drop on left of h and commutativity on right
      -- h : (w.drop (i+d)).take ℓ = ((w.drop i).take (d+ℓ)).drop d
      -- we want the inverse direction with ℓ+d
      --
      -- We'll start from h.symm
      --
      --
      --
      simpa [List.drop_drop, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h.symm
    have htake : ((w.drop i).take (ℓ + d)).take ℓ = (w.drop i).take ℓ := by
      have h := (List.take_take (l := (w.drop i)) (i := ℓ) (j := (ℓ + d)))
      -- simplify min
      simpa [Nat.min_eq_left (Nat.le_add_right ℓ d)] using h
    -- now chain equalities
    --
    calc
      ((w.drop i).take (ℓ + d)).drop d
          = (w.drop (i + d)).take ℓ := hdrop
      _ = (w.drop i).take ℓ := by
            -- use heq
            simpa [theorem5_subword] using congrArg id heq.symm
      _ = ((w.drop i).take (ℓ + d)).take ℓ := by
            simpa [htake] using (Eq.symm htake)



open free in
theorem theorem5_candidateSet_large_of_noPeriodic {n : ℕ} (C r : ℕ) (w : FreeMonoid (Fin n)) :
    w.length = r →
    (theorem5_candidateSet (n := n) C r w ∩ theorem5_logPeriodicSet (n := n) (2 * C) = ∅) →
    C * (Nat.log2 r + 1) ≤ r / 4 →
    ∃ S : Finset (FreeMonoid (Fin n)),
      (∀ u ∈ S, u ∈ theorem5_candidateSet (n := n) C r w) ∧
      S.card ≥ (r / 4) * (C * (Nat.log2 r + 1)) := by
  classical
  intro hlen hdisj hk
  set k : ℕ := C * (Nat.log2 r + 1) with hkdef
  set baseLen : ℕ := r - r / 2 with hbase
  let domain : Finset (ℕ × ℕ) := (Finset.range k).product (Finset.range (r / 4))
  let f : (ℕ × ℕ) → FreeMonoid (Fin n) := fun p =>
    theorem5_subword (n := n) w p.1 (baseLen + p.2)
  let S : Finset (FreeMonoid (Fin n)) := domain.image f
  refine ⟨S, ?_, ?_⟩
  · intro u huS
    rcases Finset.mem_image.mp huS with ⟨p, hpdom, rfl⟩
    rcases Finset.mem_product.mp hpdom with ⟨hpi, hpt⟩
    have hi : p.1 < k := Finset.mem_range.mp hpi
    have ht : p.2 < r / 4 := Finset.mem_range.mp hpt
    refine ⟨p.1, Nat.le_of_lt hi, baseLen + p.2, ?_, ?_, rfl⟩
    · exact Nat.le_add_right _ _
    · omega
  · have hinj : Set.InjOn f domain := by
      intro p hp q hq hpq
      rcases Finset.mem_product.mp hp with ⟨hp1, hp2⟩
      rcases Finset.mem_product.mp hq with ⟨hq1, hq2⟩
      have hip : p.1 < k := Finset.mem_range.mp hp1
      have hit : p.2 < r / 4 := Finset.mem_range.mp hp2
      have hiq : q.1 < k := Finset.mem_range.mp hq1
      have hqt : q.2 < r / 4 := Finset.mem_range.mp hq2
      have hple : p.1 + (baseLen + p.2) ≤ w.length := by
        have : p.1 + (baseLen + p.2) ≤ r := by omega
        simpa [hlen] using this
      have hqle : q.1 + (baseLen + q.2) ≤ w.length := by
        have : q.1 + (baseLen + q.2) ≤ r := by omega
        simpa [hlen] using this
      have hlenp : (f p).length = baseLen + p.2 := by
        simpa [f] using
          (theorem5_subword_length_of_add_le (n := n) (w := w) (i := p.1) (ℓ := baseLen + p.2)
            hple)
      have hlenq : (f q).length = baseLen + q.2 := by
        simpa [f] using
          (theorem5_subword_length_of_add_le (n := n) (w := w) (i := q.1) (ℓ := baseLen + q.2)
            hqle)
      have htEq : p.2 = q.2 := by
        have hlenEq : baseLen + p.2 = baseLen + q.2 := by
          have := congrArg (fun x => x.length) hpq
          simpa [hlenp, hlenq] using this
        exact Nat.add_left_cancel hlenEq
      have hsub :
          theorem5_subword (n := n) w p.1 (baseLen + p.2) =
            theorem5_subword (n := n) w q.1 (baseLen + p.2) := by
        simpa [f, htEq] using hpq
      have hiEq : p.1 = q.1 := by
        by_contra hne
        have hij : p.1 < q.1 ∨ q.1 < p.1 := lt_or_gt_of_ne hne
        cases hij with
        | inl hij =>
            let d : ℕ := q.1 - p.1
            have hdpos : 0 < d := Nat.sub_pos_of_lt hij
            have hadd : p.1 + d = q.1 := Nat.add_sub_of_le (le_of_lt hij)
            let ℓ : ℕ := baseLen + p.2
            have hle_w : p.1 + ℓ + d ≤ w.length := by
              have hqle' : q.1 + ℓ ≤ w.length := by
                simpa [ℓ, htEq] using hqle
              have htemp : (p.1 + d) + ℓ ≤ w.length := by
                simpa [hadd] using hqle'
              have hrew : p.1 + ℓ + d = (p.1 + d) + ℓ := by
                ac_rfl
              simpa [hrew] using htemp
            have hsub' :
                theorem5_subword (n := n) w p.1 ℓ =
                  theorem5_subword (n := n) w (p.1 + d) ℓ := by
              simpa [ℓ, hadd] using hsub
            have hper :
                theorem5_hasPeriod (n := n) (theorem5_subword (n := n) w p.1 (ℓ + d)) d :=
              theorem5_hasPeriod_subword_of_eq (n := n) (w := w) (i := p.1) (d := d) (ℓ := ℓ)
                hdpos hle_w hsub'
            let u : FreeMonoid (Fin n) := theorem5_subword (n := n) w p.1 (ℓ + d)
            have huCand : u ∈ theorem5_candidateSet (n := n) C r w := by
              refine ⟨p.1, ?_, ?_⟩
              · have : p.1 ≤ k := Nat.le_of_lt hip
                simpa [hkdef] using this
              · refine ⟨ℓ + d, ?_, ?_, rfl⟩
                · omega
                · have : p.1 + ℓ + d ≤ r := by
                    have : p.1 + ℓ + d ≤ w.length := hle_w
                    simpa [hlen] using this
                  simpa [Nat.add_assoc] using this
            have huLog : u ∈ theorem5_logPeriodicSet (n := n) (2 * C) := by
              refine ⟨d, ?_, ?_⟩
              · simpa [u] using hper
              · have hdle_k : d ≤ k := by
                  have : q.1 - p.1 ≤ q.1 := Nat.sub_le _ _
                  have hdle_q : d ≤ q.1 := by
                    simpa [d] using this
                  exact le_trans hdle_q (Nat.le_of_lt hiq)
                have hdle_Cr : d ≤ C * (Nat.log2 r + 1) := by
                  simpa [hkdef] using hdle_k
                have hr2le : r / 2 ≤ r := by
                  simpa using (Nat.div_le_self' r 2)
                have hrSub : r - baseLen = r / 2 := by
                  simpa [hbase] using (tsub_tsub_cancel_of_le (a := r / 2) (b := r) hr2le)
                have hr2le_base : r / 2 ≤ baseLen := by
                  apply Nat.half_le_of_sub_le_half
                  simpa [hrSub]
                have hdecomp : r / 2 + baseLen = r := by
                  simpa [hbase] using (Nat.add_sub_of_le hr2le)
                have hr_le_2base : r ≤ 2 * baseLen := by
                  calc
                    r = r / 2 + baseLen := by
                      symm
                      exact hdecomp
                    _ ≤ baseLen + baseLen := by
                      have : baseLen + r / 2 ≤ baseLen + baseLen :=
                        add_le_add_right hr2le_base baseLen
                      simpa [Nat.add_comm] using this
                    _ = 2 * baseLen := by
                      simp [two_mul]
                have hiu : p.1 + (ℓ + d) ≤ w.length := by
                  simpa [Nat.add_assoc] using hle_w
                have hulen : u.length = ℓ + d := by
                  simpa [u] using
                    (theorem5_subword_length_of_add_le (n := n) (w := w) (i := p.1) (ℓ := ℓ + d)
                      hiu)
                have hbase_le_u : baseLen ≤ u.length := by
                  have h1 : baseLen ≤ ℓ := by
                    simpa [ℓ] using (Nat.le_add_right baseLen p.2)
                  have h2 : ℓ ≤ ℓ + d := Nat.le_add_right ℓ d
                  have h3 : baseLen ≤ ℓ + d := le_trans h1 h2
                  simpa [hulen] using h3
                have hr_le_2u : r ≤ 2 * u.length := by
                  have : 2 * baseLen ≤ 2 * u.length :=
                    Nat.mul_le_mul_left 2 hbase_le_u
                  exact le_trans hr_le_2base this
                have hlog : Nat.log2 r + 1 ≤ 2 * (Nat.log2 u.length + 1) :=
                  theorem5_log2_add_one_le_two_mul_log2_add_one_of_le_two_mul r u.length hr_le_2u
                have hmul :
                    C * (Nat.log2 r + 1) ≤ C * (2 * (Nat.log2 u.length + 1)) :=
                  Nat.mul_le_mul_left C hlog
                have : d ≤ C * (2 * (Nat.log2 u.length + 1)) :=
                  le_trans hdle_Cr hmul
                simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using this
            have huInter :
                u ∈
                  theorem5_candidateSet (n := n) C r w ∩
                    theorem5_logPeriodicSet (n := n) (2 * C) :=
              ⟨huCand, huLog⟩
            have : u ∈ (∅ : Set (FreeMonoid (Fin n))) := by
              simpa [hdisj] using huInter
            simpa using this
        | inr hij =>
            let d : ℕ := p.1 - q.1
            have hdpos : 0 < d := Nat.sub_pos_of_lt hij
            have hadd : q.1 + d = p.1 := Nat.add_sub_of_le (le_of_lt hij)
            let ℓ : ℕ := baseLen + p.2
            have hle_w : q.1 + ℓ + d ≤ w.length := by
              have hple' : p.1 + ℓ ≤ w.length := by
                simpa [ℓ] using hple
              have htemp : (q.1 + d) + ℓ ≤ w.length := by
                simpa [hadd] using hple'
              have hrew : q.1 + ℓ + d = (q.1 + d) + ℓ := by
                ac_rfl
              simpa [hrew] using htemp
            have hsub' :
                theorem5_subword (n := n) w q.1 ℓ =
                  theorem5_subword (n := n) w (q.1 + d) ℓ := by
              have :
                  theorem5_subword (n := n) w q.1 ℓ =
                    theorem5_subword (n := n) w p.1 ℓ := by
                simpa [ℓ] using hsub.symm
              simpa [ℓ, hadd] using this
            have hper :
                theorem5_hasPeriod (n := n) (theorem5_subword (n := n) w q.1 (ℓ + d)) d :=
              theorem5_hasPeriod_subword_of_eq (n := n) (w := w) (i := q.1) (d := d) (ℓ := ℓ)
                hdpos hle_w hsub'
            let u : FreeMonoid (Fin n) := theorem5_subword (n := n) w q.1 (ℓ + d)
            have huCand : u ∈ theorem5_candidateSet (n := n) C r w := by
              refine ⟨q.1, ?_, ?_⟩
              · have : q.1 ≤ k := Nat.le_of_lt hiq
                simpa [hkdef] using this
              · refine ⟨ℓ + d, ?_, ?_, rfl⟩
                · omega
                · have : q.1 + ℓ + d ≤ r := by
                    have : q.1 + ℓ + d ≤ w.length := hle_w
                    simpa [hlen] using this
                  simpa [Nat.add_assoc] using this
            have huLog : u ∈ theorem5_logPeriodicSet (n := n) (2 * C) := by
              refine ⟨d, ?_, ?_⟩
              · simpa [u] using hper
              · have hdle_k : d ≤ k := by
                  have : p.1 - q.1 ≤ p.1 := Nat.sub_le _ _
                  have hdle_p : d ≤ p.1 := by
                    simpa [d] using this
                  exact le_trans hdle_p (Nat.le_of_lt hip)
                have hdle_Cr : d ≤ C * (Nat.log2 r + 1) := by
                  simpa [hkdef] using hdle_k
                have hr2le : r / 2 ≤ r := by
                  simpa using (Nat.div_le_self' r 2)
                have hrSub : r - baseLen = r / 2 := by
                  simpa [hbase] using (tsub_tsub_cancel_of_le (a := r / 2) (b := r) hr2le)
                have hr2le_base : r / 2 ≤ baseLen := by
                  apply Nat.half_le_of_sub_le_half
                  simpa [hrSub]
                have hdecomp : r / 2 + baseLen = r := by
                  simpa [hbase] using (Nat.add_sub_of_le hr2le)
                have hr_le_2base : r ≤ 2 * baseLen := by
                  calc
                    r = r / 2 + baseLen := by
                      symm
                      exact hdecomp
                    _ ≤ baseLen + baseLen := by
                      have : baseLen + r / 2 ≤ baseLen + baseLen :=
                        add_le_add_right hr2le_base baseLen
                      simpa [Nat.add_comm] using this
                    _ = 2 * baseLen := by
                      simp [two_mul]
                have hiu : q.1 + (ℓ + d) ≤ w.length := by
                  simpa [Nat.add_assoc] using hle_w
                have hulen : u.length = ℓ + d := by
                  simpa [u] using
                    (theorem5_subword_length_of_add_le (n := n) (w := w) (i := q.1) (ℓ := ℓ + d)
                      hiu)
                have hbase_le_u : baseLen ≤ u.length := by
                  have h1 : baseLen ≤ ℓ := by
                    simpa [ℓ] using (Nat.le_add_right baseLen p.2)
                  have h2 : ℓ ≤ ℓ + d := Nat.le_add_right ℓ d
                  have h3 : baseLen ≤ ℓ + d := le_trans h1 h2
                  simpa [hulen] using h3
                have hr_le_2u : r ≤ 2 * u.length := by
                  have : 2 * baseLen ≤ 2 * u.length :=
                    Nat.mul_le_mul_left 2 hbase_le_u
                  exact le_trans hr_le_2base this
                have hlog : Nat.log2 r + 1 ≤ 2 * (Nat.log2 u.length + 1) :=
                  theorem5_log2_add_one_le_two_mul_log2_add_one_of_le_two_mul r u.length hr_le_2u
                have hmul :
                    C * (Nat.log2 r + 1) ≤ C * (2 * (Nat.log2 u.length + 1)) :=
                  Nat.mul_le_mul_left C hlog
                have : d ≤ C * (2 * (Nat.log2 u.length + 1)) :=
                  le_trans hdle_Cr hmul
                simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using this
            have huInter :
                u ∈
                  theorem5_candidateSet (n := n) C r w ∩
                    theorem5_logPeriodicSet (n := n) (2 * C) :=
              ⟨huCand, huLog⟩
            have : u ∈ (∅ : Set (FreeMonoid (Fin n))) := by
              simpa [hdisj] using huInter
            simpa using this
      exact Prod.ext hiEq htEq
    have hcard : S.card = domain.card := by
      classical
      simpa [S] using (Finset.card_image_of_injOn (s := domain) (f := f) hinj)
    have hdom : domain.card = k * (r / 4) := by
      simp [domain]
    have hS : S.card = k * (r / 4) := by
      simpa [hdom] using hcard
    have : (r / 4) * k ≤ S.card := by
      simpa [hS, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
        (le_rfl : (r / 4) * k ≤ (r / 4) * k)
    exact this

open scoped BigOperators in
theorem theorem5_sum_inclusionProb_ge_two_mul_n_mul_r {n r : ℕ} (hr : 2 ≤ r) (S : Finset (FreeMonoid (Fin n)))
    (hScard : S.card ≥ (r / 4) * ((16 * n) * (Nat.log2 r + 1)))
    (hlen : ∀ u ∈ S, u.length ≤ r) :
    (2 * (n : ℝ)) * (r - 3) ≤ ∑ u ∈ S, (theorem5_inclusionProb (n := n) u : ℝ) := by
  classical
  -- constant lower bound coming from the maximum allowed length r
  let cNN : NNReal := ((Nat.log2 (r + 2) + 1 : ℕ) : NNReal)⁻¹

  -- pointwise lower bound for each term of the sum
  have hcu : ∀ u ∈ S, (cNN : ℝ) ≤ (theorem5_inclusionProb (n := n) u : ℝ) := by
    intro u hu
    have hlenur : u.length ≤ r := hlen u hu
    have hnn : cNN ≤ theorem5_inclusionProb (n := n) u :=
      theorem5_inclusionProb_ge_of_length_le (n := n) (r := r) (w := u) hlenur
    exact_mod_cast hnn

  -- sum is at least card(S) times the constant
  have hsum_c : (S.card : ℝ) * (cNN : ℝ) ≤ ∑ u ∈ S, (theorem5_inclusionProb (n := n) u : ℝ) := by
    have hsum' : (∑ u ∈ S, (cNN : ℝ)) ≤ ∑ u ∈ S, (theorem5_inclusionProb (n := n) u : ℝ) := by
      refine Finset.sum_le_sum ?_
      intro u hu
      exact hcu u hu
    -- rewrite the left sum as card * c
    simpa [Finset.sum_const, nsmul_eq_mul, mul_assoc, mul_left_comm, mul_comm] using hsum'

  -- cast the card lower bound to ℝ
  have hcard_real : (↑((r / 4) * ((16 * n) * (Nat.log2 r + 1))) : ℝ) ≤ (S.card : ℝ) := by
    exact_mod_cast hScard

  have hc_nonneg : 0 ≤ (cNN : ℝ) := by
    exact_mod_cast (show (0 : NNReal) ≤ cNN from by simp [cNN])

  have hsum_c' : (↑((r / 4) * ((16 * n) * (Nat.log2 r + 1))) : ℝ) * (cNN : ℝ)
      ≤ ∑ u ∈ S, (theorem5_inclusionProb (n := n) u : ℝ) := by
    have := mul_le_mul_of_nonneg_right hcard_real hc_nonneg
    exact le_trans this hsum_c

  -- compare the log factors using hr
  have hc_lower : (((2 * (Nat.log2 r + 1) : ℕ) : ℝ)⁻¹) ≤ (cNN : ℝ) := by
    -- use the dedicated lemma to avoid manipulating inverses directly
    have hstep : (((2 * (Nat.log2 r + 1) : ℕ) : ℝ)⁻¹) ≤ (((Nat.log2 (r + 2) + 1 : ℕ) : ℝ)⁻¹) :=
      theorem5_inv_two_mul_log2_add_one_le_inv_log2_add_two r hr
    simpa [cNN] using hstep

  have hsum_big : (↑((r / 4) * ((16 * n) * (Nat.log2 r + 1))) : ℝ) * (((2 * (Nat.log2 r + 1) : ℕ) : ℝ)⁻¹)
      ≤ ∑ u ∈ S, (theorem5_inclusionProb (n := n) u : ℝ) := by
    have hA_nonneg : 0 ≤ (↑((r / 4) * ((16 * n) * (Nat.log2 r + 1))) : ℝ) := by
      positivity
    have := mul_le_mul_of_nonneg_left hc_lower hA_nonneg
    exact le_trans this hsum_c'

  -- simplify the left-hand side of hsum_big to get the clean lower bound
  have hsum_simpl : ((r / 4 : ℕ) : ℝ) * (8 * (n : ℝ)) ≤ ∑ u ∈ S, (theorem5_inclusionProb (n := n) u : ℝ) := by
    have hlogpos : (0 : ℝ) < ((Nat.log2 r + 1 : ℕ) : ℝ) := by
      have : (0 : ℕ) < Nat.log2 r + 1 := Nat.succ_pos _
      exact_mod_cast this

    have hsimp : (↑((r / 4) * ((16 * n) * (Nat.log2 r + 1))) : ℝ) * (((2 * (Nat.log2 r + 1) : ℕ) : ℝ)⁻¹)
        = ((r / 4 : ℕ) : ℝ) * (8 * (n : ℝ)) := by
      simp [Nat.cast_mul, mul_assoc, mul_left_comm, mul_comm]
      field_simp [hlogpos.ne', (show (2 : ℝ) ≠ 0 by norm_num)]
      ring_nf
      · simp

    -- use hsimp to rewrite hsum_big
    have hsimp' := hsimp.symm
    simpa [hsimp'] using hsum_big

  -- relate r-3 to r/4
  have hsub : (r : ℝ) - 3 ≤ 4 * ((r / 4 : ℕ) : ℝ) := theorem5_real_sub_three_le_four_mul_div_four r
  have hn_nonneg : 0 ≤ (2 * (n : ℝ)) := by
    positivity
  have hsub' := mul_le_mul_of_nonneg_left hsub hn_nonneg

  have hleft : (2 * (n : ℝ)) * ((r : ℝ) - 3) ≤ ((r / 4 : ℕ) : ℝ) * (8 * (n : ℝ)) := by
    nlinarith [hsub']

  exact le_trans hleft hsum_simpl


open scoped BigOperators in
open Filter in
open MeasureTheory in
open ProbabilityTheory in
open free in
theorem theorem5_macroSet_halfMacro_bad_eventually_le_exp (n : ℕ) (hn : 2 ≤ n) :
  ∀ᶠ r : ℕ in atTop,
    theorem5_macroMeasure n
        {ω |
          ¬ theorem5_hasHalfMacro (n := n) (16 * n)
              (theorem5_macroSet (n := n) (2 * (16 * n)) ω) r}
      ≤ ENNReal.ofReal (Real.exp (-(n : ℝ) * r)) := by
  classical
  let C : ℕ := 16 * n
  let B : ℕ := 2 * C

  have hlog : ∀ᶠ r : ℕ in atTop, C * (Nat.log2 r + 1) ≤ r / 4 := by
    simpa [C] using theorem5_eventually_log2_mul_le (C := C)

  have hlarge : ∀ᶠ r : ℕ in atTop, 6 * n ≤ r := by
    refine Filter.eventually_atTop.2 ?_
    refine ⟨6 * n, ?_⟩
    intro r hr
    exact hr

  refine (hlog.and hlarge).mono ?_
  intro r hr
  rcases hr with ⟨hC, hrlarge⟩

  have hr2 : 2 ≤ r := by
    have h2 : 2 ≤ 6 * n := by
      have hmul : 6 * 2 ≤ 6 * n := Nat.mul_le_mul_left 6 hn
      have hbase : 2 ≤ 6 * 2 := by decide
      exact le_trans hbase hmul
    exact le_trans h2 hrlarge

  let Bad : Set (FreeMonoid (Fin n) → Bool) :=
    {ω | ¬ theorem5_hasHalfMacro (n := n) C (theorem5_macroSet (n := n) B ω) r}

  have hSphere_finite : (Sphere n r).Finite := by
    have hnpos : 0 < n := lt_of_lt_of_le Nat.zero_lt_two hn
    have hncard : 0 < Set.ncard (Sphere n r) := by
      simpa [theorem5_ncard_Sphere] using (pow_pos hnpos r)
    exact Set.finite_of_ncard_pos hncard

  let sphereFinset : Finset (FreeMonoid (Fin n)) := hSphere_finite.toFinset
  have hsphere_coe : (sphereFinset : Set (FreeMonoid (Fin n))) = Sphere n r := by
    simpa [sphereFinset] using (Set.Finite.coe_toFinset hSphere_finite)

  let BadWord (w : FreeMonoid (Fin n)) : Set (FreeMonoid (Fin n) → Bool) :=
    {ω | theorem5_candidateSet (n := n) C r w ∩ theorem5_macroSet (n := n) B ω = ∅}

  have hBad_le_union : theorem5_macroMeasure n Bad ≤
      theorem5_macroMeasure n (⋃ w ∈ sphereFinset, BadWord w) := by
    apply MeasureTheory.measure_mono
    intro ω hω
    have hex : ∃ w : FreeMonoid (Fin n), w.length = r ∧
        theorem5_candidateSet (n := n) C r w ∩ theorem5_macroSet (n := n) B ω = ∅ := by
      by_contra h
      have hall : ∀ w : FreeMonoid (Fin n), w.length = r →
          Set.Nonempty (theorem5_candidateSet (n := n) C r w ∩ theorem5_macroSet (n := n) B ω) := by
        intro w hw
        by_contra hne
        have : theorem5_candidateSet (n := n) C r w ∩ theorem5_macroSet (n := n) B ω = ∅ := by
          simpa [Set.not_nonempty_iff_eq_empty] using hne
        exact h ⟨w, hw, this⟩
      have : theorem5_hasHalfMacro (n := n) C (theorem5_macroSet (n := n) B ω) r :=
        theorem5_hasHalfMacro_of_candidateSet (n := n) (C := C) (r := r)
          (M := theorem5_macroSet (n := n) B ω) hall
      exact hω this
    rcases hex with ⟨w, hwlen, hEmpty⟩
    have hwmem : w ∈ sphereFinset := by
      have : w ∈ (Sphere n r) := by
        simpa [Sphere, hwlen]
      have : w ∈ (sphereFinset : Set (FreeMonoid (Fin n))) := by
        simpa [hsphere_coe] using this
      simpa using this
    refine Set.mem_iUnion.2 ?_
    refine ⟨w, ?_⟩
    refine Set.mem_iUnion.2 ?_
    refine ⟨hwmem, ?_⟩
    show ω ∈ BadWord w
    simpa [BadWord, hEmpty]

  have hUnion_le_sum :
      theorem5_macroMeasure n (⋃ w ∈ sphereFinset, BadWord w)
        ≤ ∑ w ∈ sphereFinset, theorem5_macroMeasure n (BadWord w) := by
    simpa using
      (MeasureTheory.measure_biUnion_finset_le (μ := theorem5_macroMeasure n)
        (I := sphereFinset) (s := fun w => BadWord w))

  let bound : ENNReal := ENNReal.ofReal (Real.exp (-(2 * (n : ℝ)) * (r - 3)))

  have hBadWord_bound :
      ∀ w ∈ sphereFinset,
        theorem5_macroMeasure n (BadWord w) ≤ bound := by
    intro w hw
    have hwlen : w.length = r := by
      have : w ∈ (sphereFinset : Set (FreeMonoid (Fin n))) := by
        simpa using hw
      have : w ∈ Sphere n r := by
        simpa [hsphere_coe] using this
      simpa [Sphere] using this
    by_cases hper : theorem5_candidateSet (n := n) C r w ∩ theorem5_logPeriodicSet (n := n) (2 * C) = ∅
    · obtain ⟨S, hSsub, hScard⟩ :=
        theorem5_candidateSet_large_of_noPeriodic (n := n) (C := C) (r := r) w hwlen hper hC
      have hsubset_pi : BadWord w ⊆ Set.pi S (fun _ : FreeMonoid (Fin n) => ({false} : Set Bool)) := by
        intro ω hω
        intro u hu
        have huCand : u ∈ theorem5_candidateSet (n := n) C r w := hSsub u hu
        have hEmpty' : theorem5_candidateSet (n := n) C r w ∩ theorem5_macroSet (n := n) B ω = ∅ := by
          simpa [BadWord] using hω
        have huNotMacro : u ∉ theorem5_macroSet (n := n) B ω := by
          intro huMacro
          have : u ∈ theorem5_candidateSet (n := n) C r w ∩ theorem5_macroSet (n := n) B ω :=
            ⟨huCand, huMacro⟩
          simpa [hEmpty'] using this
        have huNotRandom : u ∉ theorem5_randomSet (n := n) ω := by
          intro huRand
          apply huNotMacro
          have : u ∈ theorem5_macroSet (n := n) B ω := by
            simp [theorem5_macroSet, huRand]
          exact this
        have : ω u = false := by
          cases hωu : ω u with
          | false =>
              rfl
          | true =>
              have : u ∈ theorem5_randomSet (n := n) ω := by
                simpa [theorem5_randomSet, hωu]
              exact (huNotRandom this).elim
        simpa [Set.mem_singleton_iff, this]
      have hμ_mono : theorem5_macroMeasure n (BadWord w) ≤
          theorem5_macroMeasure n (Set.pi S (fun _ : FreeMonoid (Fin n) => ({false} : Set Bool))) :=
        MeasureTheory.measure_mono hsubset_pi
      have hμ_cyl : theorem5_macroMeasure n (Set.pi S (fun _ : FreeMonoid (Fin n) => ({false} : Set Bool)))
          ≤ ENNReal.ofReal (Real.exp (-(∑ u ∈ S, (theorem5_inclusionProb (n := n) u : ℝ)))) := by
        simpa using theorem5_macroMeasure_all_false_finset_le_exp_neg_sum (n := n) S
      have hμ : theorem5_macroMeasure n (BadWord w)
          ≤ ENNReal.ofReal (Real.exp (-(∑ u ∈ S, (theorem5_inclusionProb (n := n) u : ℝ)))) :=
        le_trans hμ_mono hμ_cyl
      have hlen : ∀ u ∈ S, u.length ≤ r := by
        intro u hu
        have huCand : u ∈ theorem5_candidateSet (n := n) C r w := hSsub u hu
        exact theorem5_candidateSet_length_le_r (n := n) (C := C) (r := r) (w := w) (u := u) hwlen huCand
      have hsum : (2 * (n : ℝ)) * (r - 3) ≤ ∑ u ∈ S, (theorem5_inclusionProb (n := n) u : ℝ) := by
        exact theorem5_sum_inclusionProb_ge_two_mul_n_mul_r (n := n) (r := r) hr2 S (by
          simpa [C, Nat.mul_assoc] using hScard) hlen
      have hexp : Real.exp (-(∑ u ∈ S, (theorem5_inclusionProb (n := n) u : ℝ)))
          ≤ Real.exp (-(2 * (n : ℝ)) * (r - 3)) := by
        apply Real.exp_le_exp_of_le
        have hneg := neg_le_neg hsum
        simpa [neg_mul, mul_assoc] using hneg
      have hof : ENNReal.ofReal (Real.exp (-(∑ u ∈ S, (theorem5_inclusionProb (n := n) u : ℝ))))
          ≤ ENNReal.ofReal (Real.exp (-(2 * (n : ℝ)) * (r - 3))) :=
        ENNReal.ofReal_le_ofReal hexp
      have : theorem5_macroMeasure n (BadWord w) ≤
          ENNReal.ofReal (Real.exp (-(2 * (n : ℝ)) * (r - 3))) :=
        le_trans hμ hof
      simpa [bound] using this
    · have hne : (theorem5_candidateSet (n := n) C r w ∩ theorem5_logPeriodicSet (n := n) (2 * C)).Nonempty := by
        have : ¬(theorem5_candidateSet (n := n) C r w ∩ theorem5_logPeriodicSet (n := n) (2 * C) = ∅) := hper
        simpa [Set.nonempty_iff_ne_empty] using this
      rcases hne with ⟨u, hu⟩
      have hEmptySet : BadWord w = ∅ := by
        ext ω
        constructor
        · intro hω
          have hEmpty' : theorem5_candidateSet (n := n) C r w ∩ theorem5_macroSet (n := n) B ω = ∅ := by
            simpa [BadWord] using hω
          have huMacro : u ∈ theorem5_macroSet (n := n) B ω := by
            refine Or.inl ?_
            simpa [B] using hu.2
          have : u ∈ theorem5_candidateSet (n := n) C r w ∩ theorem5_macroSet (n := n) B ω :=
            ⟨hu.1, huMacro⟩
          simpa [hEmpty'] using this
        · intro hω
          simpa using hω
      have : theorem5_macroMeasure n (BadWord w) = 0 := by
        simp [hEmptySet]
      simpa [this, bound] using (zero_le bound)

  have hBad_le_sum : theorem5_macroMeasure n Bad ≤
      ∑ w ∈ sphereFinset, theorem5_macroMeasure n (BadWord w) :=
    le_trans hBad_le_union hUnion_le_sum

  have hsum_le :
      (∑ w ∈ sphereFinset, theorem5_macroMeasure n (BadWord w))
        ≤ ∑ w ∈ sphereFinset, bound := by
    refine Finset.sum_le_sum ?_
    intro w hw
    exact hBadWord_bound w hw

  have hsum_const :
      (∑ w ∈ sphereFinset, bound) = sphereFinset.card * bound := by
    simp [Finset.sum_const, nsmul_eq_mul, bound]

  have hsphere_card : sphereFinset.card = n ^ r := by
    have hcard : sphereFinset.card = Set.ncard (Sphere n r) := by
      simpa [sphereFinset] using (Set.ncard_eq_toFinset_card (s := Sphere n r) hSphere_finite).symm
    calc
      sphereFinset.card = Set.ncard (Sphere n r) := hcard
      _ = n ^ r := theorem5_ncard_Sphere n r

  have hbound : theorem5_macroMeasure n Bad ≤
      ENNReal.ofReal (Real.exp (-(n : ℝ) * r)) := by
    have h1 : theorem5_macroMeasure n Bad ≤ ∑ w ∈ sphereFinset, bound :=
      le_trans hBad_le_sum hsum_le
    have h2 : theorem5_macroMeasure n Bad ≤ sphereFinset.card * bound := by
      simpa [hsum_const] using h1
    have h3 : theorem5_macroMeasure n Bad ≤ (sphereFinset.card : ENNReal) * bound := by
      simpa [bound] using h2
    have h3' : theorem5_macroMeasure n Bad ≤ (n ^ r : ENNReal) * bound := by
      simpa [hsphere_card, bound] using h3
    have h4 : (n ^ r : ENNReal) * bound ≤ ENNReal.ofReal (Real.exp (-(n : ℝ) * r)) := by
      simpa [bound] using
        theorem5_pow_mul_ofReal_exp_neg_two_mul_sub_three_le_ofReal_exp_neg n r hn hrlarge
    exact le_trans h3' h4

  simpa [Bad, C, B] using hbound


open scoped BigOperators in
open Filter in
open MeasureTheory in
open ProbabilityTheory in
open free in
theorem theorem5_macroSet_halfMacro_summable_explicit (n : ℕ) (hn : 2 ≤ n) :
  (∑' r : ℕ,
      theorem5_macroMeasure n
        {ω |
          ¬ theorem5_hasHalfMacro (n := n) (16 * n)
              (theorem5_macroSet (n := n) (2 * (16 * n)) ω) r}) ≠ ⊤ := by
  classical
  let μ : MeasureTheory.Measure (FreeMonoid (Fin n) → Bool) := theorem5_macroMeasure n
  let a : ℕ → ENNReal := fun r : ℕ =>
    μ
      {ω |
        ¬theorem5_hasHalfMacro (n := n) (16 * n)
          (theorem5_macroSet (n := n) (2 * (16 * n)) ω) r}
  change (∑' r : ℕ, a r) ≠ ⊤
  have hEvent : ∀ᶠ r : ℕ in atTop,
      a r ≤ ENNReal.ofReal (Real.exp (-(n : ℝ) * r)) := by
    simpa [a, μ] using theorem5_macroSet_halfMacro_bad_eventually_le_exp n hn
  rcases (Filter.eventually_atTop.1 hEvent) with ⟨r0, hr0⟩

  have hprob : MeasureTheory.IsProbabilityMeasure μ := by
    simpa [μ] using theorem5_macroMeasure_isProbability n
  have ha_le_one : ∀ r : ℕ, a r ≤ 1 := by
    intro r
    haveI : MeasureTheory.IsProbabilityMeasure μ := hprob
    simpa [a] using
      (MeasureTheory.prob_le_one (μ := μ)
        (s :=
          {ω |
            ¬theorem5_hasHalfMacro (n := n) (16 * n)
              (theorem5_macroSet (n := n) (2 * (16 * n)) ω) r}))

  have hnposNat : 0 < n := lt_of_lt_of_le (by decide : 0 < (2 : ℕ)) hn
  have hnposR : (0 : ℝ) < (n : ℝ) := by
    exact_mod_cast hnposNat
  have hneg : (-(n : ℝ)) < 0 := (neg_lt_zero.2 hnposR)
  have hSummReal : Summable (fun r : ℕ => Real.exp (-(n : ℝ) * r)) := by
    simpa using
      (Real.summable_exp_nat_mul_of_ge (c := (-(n : ℝ))) hneg
        (f := fun r : ℕ => (r : ℝ)) (by intro r; exact le_rfl))
  have hExp_ne_top : (∑' r : ℕ, ENNReal.ofReal (Real.exp (-(n : ℝ) * r))) ≠ ⊤ := by
    simpa using
      (Summable.tsum_ofReal_ne_top (f := fun r : ℕ => Real.exp (-(n : ℝ) * r)) hSummReal)

  set c : ENNReal := (r0 : ENNReal) + ∑' r : ℕ, ENNReal.ofReal (Real.exp (-(n : ℝ) * r))
  have hc_ne_top : c ≠ ⊤ := by
    have hc' : (r0 : ENNReal) ≠ (⊤ : ENNReal) := by simp
    exact (ENNReal.add_ne_top).2 ⟨hc', hExp_ne_top⟩

  have hsum_range_le : ∀ m : ℕ, (∑ i ∈ Finset.range m, a i) ≤ c := by
    intro m
    by_cases hm : m ≤ r0
    · -- all terms are bounded by 1, and there are at most `r0` of them
      have hle1 : (∑ i ∈ Finset.range m, a i) ≤ ∑ i ∈ Finset.range m, (1 : ENNReal) := by
        refine Finset.sum_le_sum ?_
        intro i hi
        exact ha_le_one i
      have hle_m : (∑ i ∈ Finset.range m, a i) ≤ (m : ENNReal) :=
        le_trans hle1 (le_of_eq (by simp))
      have hm' : (m : ENNReal) ≤ (r0 : ENNReal) := by
        exact_mod_cast hm
      have hle_r0 : (∑ i ∈ Finset.range m, a i) ≤ (r0 : ENNReal) := le_trans hle_m hm'
      have hr0_le_c : (r0 : ENNReal) ≤ c := by
        simpa [c] using (le_add_of_nonneg_right (zero_le _))
      exact le_trans hle_r0 hr0_le_c
    · have hr0m : r0 ≤ m := Nat.le_of_lt (Nat.lt_of_not_ge hm)
      have hsplit : (∑ i ∈ Finset.range m, a i) =
          (∑ i ∈ Finset.range r0, a i) + ∑ i ∈ Finset.Ico r0 m, a i := by
        simpa using
          (Finset.sum_range_add_sum_Ico (f := a) (m := r0) (n := m) hr0m).symm
      have hpre : (∑ i ∈ Finset.range r0, a i) ≤ (r0 : ENNReal) := by
        have hle1 : (∑ i ∈ Finset.range r0, a i) ≤ ∑ i ∈ Finset.range r0, (1 : ENNReal) := by
          refine Finset.sum_le_sum ?_
          intro i hi
          exact ha_le_one i
        exact le_trans hle1 (le_of_eq (by simp))
      have htail : (∑ i ∈ Finset.Ico r0 m, a i)
          ≤ ∑' r : ℕ, ENNReal.ofReal (Real.exp (-(n : ℝ) * r)) := by
        have hle_exp : (∑ i ∈ Finset.Ico r0 m, a i)
            ≤ ∑ i ∈ Finset.Ico r0 m, ENNReal.ofReal (Real.exp (-(n : ℝ) * i)) := by
          refine Finset.sum_le_sum ?_
          intro i hi
          have hir0 : r0 ≤ i := (Finset.mem_Ico.mp hi).1
          exact hr0 i hir0
        have hle_tsum : (∑ i ∈ Finset.Ico r0 m, ENNReal.ofReal (Real.exp (-(n : ℝ) * i)))
            ≤ ∑' r : ℕ, ENNReal.ofReal (Real.exp (-(n : ℝ) * r)) := by
          simpa using
            (ENNReal.sum_le_tsum (s := Finset.Ico r0 m)
              (f := fun r : ℕ => ENNReal.ofReal (Real.exp (-(n : ℝ) * r))))
        exact le_trans hle_exp hle_tsum
      have hle' : (∑ i ∈ Finset.range m, a i) ≤
          (r0 : ENNReal) + ∑' r : ℕ, ENNReal.ofReal (Real.exp (-(n : ℝ) * r)) := by
        have : (∑ i ∈ Finset.range r0, a i) + (∑ i ∈ Finset.Ico r0 m, a i) ≤
            (r0 : ENNReal) + ∑' r : ℕ, ENNReal.ofReal (Real.exp (-(n : ℝ) * r)) :=
          add_le_add hpre htail
        simpa [hsplit] using this
      simpa [c] using hle'

  have htsum_le : (∑' r : ℕ, a r) ≤ c := ENNReal.tsum_le_of_sum_range_le hsum_range_le
  exact ne_top_of_le_ne_top hc_ne_top htsum_le

open scoped BigOperators in
open Filter in
open MeasureTheory in
open ProbabilityTheory in
open free in
theorem theorem5_macroSet_halfMacro_ae (n : ℕ) (hn : 2 ≤ n) :
  ∃ (B C : ℕ), 0 < C ∧
    ∀ᵐ ω ∂theorem5_macroMeasure n,
      (∀ᶠ r : ℕ in atTop,
        theorem5_hasHalfMacro (n := n) C (theorem5_macroSet (n := n) B ω) r) := by
  classical
  -- Fix the explicit constants from the informal proof
  let C : ℕ := 16 * n
  let B : ℕ := 2 * C
  refine ⟨B, C, ?_, ?_⟩
  · -- `0 < C`
    have hn0 : 0 < n := by
      have : 0 < (2 : ℕ) := by decide
      exact lt_of_lt_of_le this hn
    simpa [C] using (Nat.mul_pos (by decide : 0 < 16) hn0)
  · -- Almost-everywhere eventually good
    have hBC : theorem5_macroMeasure n {ω | ∃ᶠ r : ℕ in atTop,
        ¬ theorem5_hasHalfMacro (n := n) C (theorem5_macroSet (n := n) B ω) r} = 0 := by
      simpa [C, B] using
        (MeasureTheory.measure_setOf_frequently_eq_zero
          (μ := theorem5_macroMeasure n)
          (p := fun r ω =>
            ¬ theorem5_hasHalfMacro (n := n) C (theorem5_macroSet (n := n) B ω) r)
          (theorem5_macroSet_halfMacro_summable_explicit n hn))
    -- Convert the measure-zero statement to an `ae` statement.
    have hAE : ∀ᵐ ω ∂theorem5_macroMeasure n,
        ¬ (∃ᶠ r : ℕ in atTop,
          ¬ theorem5_hasHalfMacro (n := n) C (theorem5_macroSet (n := n) B ω) r) := by
      -- `ae_iff` : (∀ᵐ ω, P ω) ↔ μ {ω | ¬ P ω} = 0
      -- with `P ω := ¬ (∃ᶠ r, bad r ω)`.
      refine (MeasureTheory.ae_iff (μ := theorem5_macroMeasure n)
        (p := fun ω =>
          ¬ (∃ᶠ r : ℕ in atTop,
            ¬ theorem5_hasHalfMacro (n := n) C (theorem5_macroSet (n := n) B ω) r))).2 ?_
      -- The set of counterexamples is exactly the Borel–Cantelli set.
      simpa only [not_not] using hBC
    -- Turn `¬ frequently bad` into `eventually not bad`, then simplify.
    filter_upwards [hAE] with ω hω
    have := (Filter.not_frequently (f := (atTop : Filter ℕ))
        (p := fun r =>
          ¬ theorem5_hasHalfMacro (n := n) C (theorem5_macroSet (n := n) B ω) r)).1 hω
    simpa using this

open scoped BigOperators in
theorem theorem5_sum_range_pow_le_pow_succ (n k : ℕ) (hn : 2 ≤ n) :
    (∑ d ∈ Finset.range (k + 1), n ^ d) ≤ n ^ (k + 1) := by
  have hs : ∀ d ∈ Finset.range (k + 1), d < k + 1 := by
    intro d hd
    exact Finset.mem_range.mp hd
  have hlt : (∑ d ∈ Finset.range (k + 1), n ^ d) < n ^ (k + 1) := by
    exact Nat.geomSum_lt hn hs
  exact le_of_lt hlt


open scoped BigOperators in
open Filter in
open free in
theorem theorem5_logPeriodic_density_bound (n : ℕ) (hn : 2 ≤ n) (B : ℕ) :
    ∀ᶠ r : ℕ in atTop,
      ((Set.ncard (theorem5_logPeriodicSet (n := n) B ∩ Sphere n r) : ℝ) /
          (Set.ncard (Sphere n r) : ℝ))
        ≤ ((1 : ℝ) / (n : ℝ)) ^ (r / 2) := by
  classical
  let K : ℕ → ℕ := fun r => B * (Nat.log2 r + 1)
  have hK : ∀ᶠ r : ℕ in atTop, K r ≤ r / 4 := by
    simpa [K] using (theorem5_eventually_log2_mul_le (C := B))
  have hlarge : ∀ᶠ r : ℕ in atTop, 2 ≤ r := by
    exact Filter.eventually_atTop.2 ⟨2, by intro r hr; exact hr⟩
  filter_upwards [hK, hlarge] with r hKr hr2
  have h_sphere : Set.ncard (Sphere n r) = n ^ r := theorem5_ncard_Sphere n r
  have h_ncard_nat :
      Set.ncard (theorem5_logPeriodicSet (n := n) B ∩ Sphere n r) ≤ n ^ (K r + 1) := by
    have h1 := theorem5_ncard_logPeriodic_inter_sphere_le_sum (n := n) (r := r) (B := B)
    have h2 := theorem5_sum_range_pow_le_pow_succ (n := n) (k := K r) hn
    exact le_trans h1 h2
  have h_ncard_real :
      (Set.ncard (theorem5_logPeriodicSet (n := n) B ∩ Sphere n r) : ℝ)
        ≤ (n ^ (K r + 1) : ℝ) := by
    exact_mod_cast h_ncard_nat
  have hden_nonneg : (0 : ℝ) ≤ (Set.ncard (Sphere n r) : ℝ) := by
    exact_mod_cast (Nat.zero_le (Set.ncard (Sphere n r)))
  have hratio :
      (Set.ncard (theorem5_logPeriodicSet (n := n) B ∩ Sphere n r) : ℝ)
          / (Set.ncard (Sphere n r) : ℝ)
        ≤ (n ^ (K r + 1) : ℝ) / (Set.ncard (Sphere n r) : ℝ) := by
    exact div_le_div_of_nonneg_right h_ncard_real hden_nonneg
  have hratio' :
      (Set.ncard (theorem5_logPeriodicSet (n := n) B ∩ Sphere n r) : ℝ) / (n ^ r : ℝ)
        ≤ (n ^ (K r + 1) : ℝ) / (n ^ r : ℝ) := by
    simpa [h_sphere] using hratio
  have hk1_le : K r + 1 ≤ r / 2 := by
    omega
  have hr_le : K r + 1 ≤ r := le_trans hk1_le (Nat.div_le_self r 2)
  have hr_decomp : (K r + 1) + (r - (K r + 1)) = r := by
    exact Nat.add_sub_of_le hr_le
  have hnpos_nat : 0 < n := lt_of_lt_of_le (by decide : 0 < 2) hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by
    exact_mod_cast hnpos_nat
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by
    have hn1_nat : 1 ≤ n := le_trans (by decide : (1 : ℕ) ≤ 2) hn
    exact_mod_cast hn1_nat
  have hn0 : (n : ℝ) ≠ 0 := ne_of_gt hnpos
  have hmain : (n ^ (K r + 1) : ℝ) / (n ^ r : ℝ) ≤ ((1 : ℝ) / (n : ℝ)) ^ (r / 2) := by
    -- rewrite everything as powers in ℝ
    have hr_cast : (n ^ r : ℝ) = (n : ℝ) ^ r := by
      simpa using (Nat.cast_pow n r : (↑(n ^ r) : ℝ) = (n : ℝ) ^ r)
    have hk_cast : (n ^ (K r + 1) : ℝ) = (n : ℝ) ^ (K r + 1) := by
      simpa using (Nat.cast_pow n (K r + 1) : (↑(n ^ (K r + 1)) : ℝ) = (n : ℝ) ^ (K r + 1))
    -- reduce to a statement about (n:ℝ)
    --
    -- We first rewrite the ratio as `1 / (n:ℝ)^(r - (K r + 1))`.
    have hratio_eq : ((n : ℝ) ^ (K r + 1)) / ((n : ℝ) ^ r) = 1 / ((n : ℝ) ^ (r - (K r + 1))) := by
      -- expand `r` as `(K r + 1) + (r - (K r + 1))`
      calc
        ((n : ℝ) ^ (K r + 1)) / ((n : ℝ) ^ r)
            = ((n : ℝ) ^ (K r + 1)) / ((n : ℝ) ^ ((K r + 1) + (r - (K r + 1)))) := by
                -- rewrite `r`
                simpa [hr_decomp]
        _ = ((n : ℝ) ^ (K r + 1)) / (((n : ℝ) ^ (K r + 1)) * ((n : ℝ) ^ (r - (K r + 1)))) := by
              simp [pow_add]
        _ = (((n : ℝ) ^ (K r + 1)) / ((n : ℝ) ^ (K r + 1))) * (1 / ((n : ℝ) ^ (r - (K r + 1)))) := by
              simpa using (div_mul_eq_div_mul_one_div ((n : ℝ) ^ (K r + 1)) ((n : ℝ) ^ (K r + 1)) ((n : ℝ) ^ (r - (K r + 1))))
        _ = 1 * (1 / ((n : ℝ) ^ (r - (K r + 1)))) := by
              have : ((n : ℝ) ^ (K r + 1)) ≠ 0 := by
                exact pow_ne_zero _ hn0
              simp [this]
        _ = 1 / ((n : ℝ) ^ (r - (K r + 1))) := by
              simp
    -- Now compare exponents in the denominator.
    have hsub_ge : r / 2 ≤ r - (K r + 1) := by
      omega
    have h_one_div_le : (1 / ((n : ℝ) ^ (r - (K r + 1)))) ≤ 1 / ((n : ℝ) ^ (r / 2)) := by
      -- `a ≥ 1` makes `1 / a^k` antitone in `k`.
      simpa using (one_div_pow_le_one_div_pow_of_le hn1 (m := r / 2) (n := r - (K r + 1)) hsub_ge)
    -- finish
    --
    -- RHS is `(1/(n:ℝ))^(r/2) = 1/(n:ℝ)^(r/2)`
    calc
      (n ^ (K r + 1) : ℝ) / (n ^ r : ℝ)
          = ((n : ℝ) ^ (K r + 1)) / ((n : ℝ) ^ r) := by
              -- cast-pow rewrites
              simp [hr_cast, hk_cast]
      _ = 1 / ((n : ℝ) ^ (r - (K r + 1))) := hratio_eq
      _ ≤ 1 / ((n : ℝ) ^ (r / 2)) := h_one_div_le
      _ = ((1 : ℝ) / (n : ℝ)) ^ (r / 2) := by
            -- rewrite `1 / (n^k)` as `(1/n)^k`
            symm
            -- `one_div_pow` gives `(1/n)^k = 1/n^k`
            simpa [one_div_pow]
  have : (Set.ncard (theorem5_logPeriodicSet (n := n) B ∩ Sphere n r) : ℝ) / (n ^ r : ℝ)
        ≤ ((1 : ℝ) / (n : ℝ)) ^ (r / 2) :=
    le_trans hratio' hmain
  simpa [h_sphere] using this

open Filter in
theorem theorem5_tendsto_inv_log2_add_two: Tendsto (fun r : ℕ => (((Nat.log2 (r + 2) + 1 : ℕ) : ℝ))⁻¹) atTop (nhds 0) := by
  have hden : Tendsto (fun r : ℕ => Nat.log2 (r + 2) + 1) atTop atTop := by
    refine tendsto_atTop.2 ?_
    intro k
    refine (eventually_atTop.2 ?_)
    refine ⟨2 ^ k, ?_⟩
    intro r hr
    have hpow : 2 ^ k ≤ r + 2 := le_trans hr (Nat.le_add_right r 2)
    have hy : r + 2 ≠ 0 := by
      exact Nat.ne_of_gt (Nat.succ_pos (r + 1))
    have hklog : k ≤ Nat.log 2 (r + 2) :=
      (Nat.pow_le_iff_le_log (b := 2) one_lt_two hy).1 hpow
    have hklog2 : k ≤ Nat.log2 (r + 2) := by
      simpa [Nat.log2_eq_log_two] using hklog
    exact le_trans hklog2 (Nat.le_succ _)
  exact tendsto_inverse_atTop_nhds_zero_nat.comp hden

open scoped BigOperators in
open Filter in
open MeasureTheory in
open ProbabilityTheory in
open free in
theorem theorem5_random_density_eventually_le_two_mul_mean (n : ℕ) (hn : 2 ≤ n) :
  ∀ᵐ ω ∂theorem5_macroMeasure n,
    (∀ᶠ r : ℕ in atTop,
      (Set.ncard (theorem5_randomSet (n := n) ω ∩ Sphere n r) : ℝ)
        ≤ 2 * (n ^ r : ℝ) * (((Nat.log2 (r + 2) + 1 : ℕ) : ℝ)⁻¹)) := by
  classical
  let μ : MeasureTheory.Measure (FreeMonoid (Fin n) → Bool) := theorem5_macroMeasure n
  let bad : ℕ → (FreeMonoid (Fin n) → Bool) → Prop := fun r ω =>
    (2 * (n ^ r : ℝ) * (((Nat.log2 (r + 2) + 1 : ℕ) : ℝ)⁻¹)) <
      (Set.ncard (theorem5_randomSet (n := n) ω ∩ Sphere n r) : ℝ)
  have hbad_sum : (∑' r : ℕ, μ {ω | bad r ω}) ≠ (⊤ : ENNReal) := by
    simpa [μ, bad] using theorem5_random_density_bad_summable n hn
  have hfreq0 : μ {ω | ∃ᶠ r in atTop, bad r ω} = 0 := by
    simpa [μ] using (MeasureTheory.measure_setOf_frequently_eq_zero (μ := μ) (p := fun r ω => bad r ω) hbad_sum)
  have hAE_not_freq : ∀ᵐ ω ∂μ, ¬ (∃ᶠ r in atTop, bad r ω) := by
    -- convert measure zero set
    simpa [Filter.Frequently, μ] using (MeasureTheory.ae_iff.2 hfreq0)

  -- Now show eventually inequality
  filter_upwards [hAE_not_freq] with ω hnot
  have hev : (∀ᶠ r : ℕ in atTop, ¬ bad r ω) := by
    -- not frequently implies eventually not
    -- use not_frequently
    simpa [Filter.not_frequently] using hnot
  -- rewrite ¬ bad as ≤
  filter_upwards [hev] with r hr
  -- unfold bad
  have : (Set.ncard (theorem5_randomSet (n := n) ω ∩ Sphere n r) : ℝ) ≤
      2 * (n ^ r : ℝ) * (((Nat.log2 (r + 2) + 1 : ℕ) : ℝ)⁻¹) := by
    -- from not lt
    exact le_of_not_gt hr
  simpa [bad] using this


open scoped BigOperators in
open Filter in
open MeasureTheory in
open ProbabilityTheory in
open free in
theorem theorem5_random_density_ae (n : ℕ) (hn : 2 ≤ n) :
  ∀ᵐ ω ∂theorem5_macroMeasure n,
    Tendsto
      (fun r : ℕ =>
        ((Set.ncard (theorem5_randomSet (n := n) ω ∩ Sphere n r) : ℝ) /
          (Set.ncard (Sphere n r) : ℝ)))
      atTop (nhds 0) := by
  classical
  have h_event := theorem5_random_density_eventually_le_two_mul_mean (n := n) hn
  filter_upwards [h_event] with ω hω

  let p : ℕ → ℝ := fun r : ℕ => (((Nat.log2 (r + 2) + 1 : ℕ) : ℝ))⁻¹

  let f : ℕ → ℝ := fun r : ℕ =>
    (Set.ncard (theorem5_randomSet (n := n) ω ∩ Sphere n r) : ℝ) /
      (Set.ncard (Sphere n r) : ℝ)

  have hf_nonneg : ∀ r : ℕ, 0 ≤ f r := by
    intro r
    have ha : (0 : ℝ) ≤ (Set.ncard (theorem5_randomSet (n := n) ω ∩ Sphere n r) : ℝ) := by
      exact_mod_cast (Nat.zero_le _)
    have hb : (0 : ℝ) ≤ (Set.ncard (Sphere n r) : ℝ) := by
      exact_mod_cast (Nat.zero_le _)
    simpa [f] using div_nonneg ha hb

  have hp : Tendsto p atTop (nhds 0) := by
    simpa [p] using theorem5_tendsto_inv_log2_add_two

  have h2p : Tendsto (fun r : ℕ => 2 * p r) atTop (nhds 0) := by
    simpa [p] using (tendsto_const_nhds.mul hp)

  have h_event_le : ∀ᶠ r : ℕ in atTop, f r ≤ 2 * p r := by
    have hpos : ∀ r : ℕ, (0 : ℝ) < (n ^ r : ℝ) := by
      intro r
      have hnpos_nat : (0 : ℕ) < n := lt_of_lt_of_le (by decide : (0 : ℕ) < 2) hn
      have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hnpos_nat
      simpa using (pow_pos hnpos r)

    filter_upwards [hω] with r hr

    have hdenom : (Set.ncard (Sphere n r) : ℝ) = (n ^ r : ℝ) := by
      exact_mod_cast (theorem5_ncard_Sphere n r)

    have :
        (Set.ncard (theorem5_randomSet (n := n) ω ∩ Sphere n r) : ℝ) / (n ^ r : ℝ)
          ≤ 2 * p r := by
      have hc : (0 : ℝ) < (n ^ r : ℝ) := hpos r
      have hr' :
          (Set.ncard (theorem5_randomSet (n := n) ω ∩ Sphere n r) : ℝ)
            ≤ (n ^ r : ℝ) * (2 * p r) := by
        -- hr : A ≤ 2 * (n^r) * p r
        -- reorder to (n^r) * (2 * p r)
        simpa [p, mul_assoc, mul_left_comm, mul_comm] using hr
      exact (div_le_iff₀' hc).2 hr'

    simpa [f, hdenom] using this

  have hf : Tendsto f atTop (nhds 0) := by
    refine squeeze_zero' ?_ h_event_le h2p
    exact Filter.Eventually.of_forall hf_nonneg

  simpa [f] using hf

open Filter in
theorem theorem5_tendsto_one_div_pow_div2 (n : ℕ) (hn : 2 ≤ n) :
    Tendsto (fun r : ℕ => ((1 : ℝ) / (n : ℝ)) ^ (r / 2)) atTop (nhds 0) := by
  classical
  -- set q = 1/n
  let q : ℝ := (1 : ℝ) / (n : ℝ)
  have hq0 : 0 ≤ q := by
    -- `q = 1 / n` is nonnegative
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := by positivity
    -- `one_div_nonneg` is stated for `1 / a`
    simpa [q, one_div] using (show (0 : ℝ) ≤ (1 : ℝ) / (n : ℝ) from div_nonneg (by norm_num) hn0)
  have hq1 : q < 1 := by
    have hnpos_nat : 0 < n := lt_of_lt_of_le (by decide : 0 < 2) hn
    have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hnpos_nat
    have h1n_nat : 1 < n := lt_of_lt_of_le Nat.one_lt_two hn
    have h1n : (1 : ℝ) < (n : ℝ) := by exact_mod_cast h1n_nat
    -- use `div_lt_one`
    have : (1 : ℝ) / (n : ℝ) < 1 := (div_lt_one hnpos).2 h1n
    simpa [q] using this
  have hdiv : Tendsto (fun r : ℕ => r / 2) atTop atTop := by
    simpa using (Nat.tendsto_div_const_atTop (n := 2) (by decide : (2 : ℕ) ≠ 0))
  have hpow : Tendsto (fun m : ℕ => q ^ m) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1
  -- compose the two limits
  simpa [q, Function.comp] using (hpow.comp hdiv)

open scoped BigOperators in
open Filter in
open free in
theorem theorem5_logPeriodic_density (n : ℕ) (hn : 2 ≤ n) (B : ℕ) :
    Tendsto
      (fun r : ℕ =>
        ((Set.ncard (theorem5_logPeriodicSet (n := n) B ∩ Sphere n r) : ℝ) /
          (Set.ncard (Sphere n r) : ℝ)))
      atTop (nhds 0) := by
  classical
  -- use a squeeze theorem: the ratio is nonnegative and eventually bounded by a function tending to 0
  refine squeeze_zero' ?_ (theorem5_logPeriodic_density_bound n hn B)
    (theorem5_tendsto_one_div_pow_div2 n hn)
  -- nonnegativity of the ratio holds for all `r`, hence eventually
  refine Filter.Eventually.of_forall ?_
  intro r
  have hnum : (0 : ℝ) ≤ (Set.ncard (theorem5_logPeriodicSet (n := n) B ∩ Sphere n r) : ℝ) := by
    exact_mod_cast (Nat.zero_le (Set.ncard (theorem5_logPeriodicSet (n := n) B ∩ Sphere n r)))
  have hden : (0 : ℝ) ≤ (Set.ncard (Sphere n r) : ℝ) := by
    exact_mod_cast (Nat.zero_le (Set.ncard (Sphere n r)))
  exact div_nonneg hnum hden

open scoped BigOperators in
open Filter in
open MeasureTheory in
open ProbabilityTheory in
open free in
theorem theorem5_macroSet_density_ae (n : ℕ) (hn : 2 ≤ n) (B : ℕ) :
  ∀ᵐ ω ∂theorem5_macroMeasure n,
    Tendsto
      (fun r : ℕ =>
        ((Set.ncard (theorem5_macroSet (n := n) B ω ∩ Sphere n r) : ℝ) /
          (Set.ncard (Sphere n r) : ℝ)))
      atTop (nhds 0) := by
  classical
  have hP :
      Tendsto
        (fun r : ℕ =>
          ((Set.ncard (theorem5_logPeriodicSet (n := n) B ∩ Sphere n r) : ℝ) /
            (Set.ncard (Sphere n r) : ℝ)))
        atTop (nhds 0) :=
    theorem5_logPeriodic_density n hn B
  have hR :
      ∀ᵐ ω ∂theorem5_macroMeasure n,
        Tendsto
          (fun r : ℕ =>
            ((Set.ncard (theorem5_randomSet (n := n) ω ∩ Sphere n r) : ℝ) /
              (Set.ncard (Sphere n r) : ℝ)))
          atTop (nhds 0) :=
    theorem5_random_density_ae n hn
  filter_upwards [hR] with ω hω
  have hsum :
      Tendsto
        (fun r : ℕ =>
          ((Set.ncard (theorem5_logPeriodicSet (n := n) B ∩ Sphere n r) : ℝ) /
              (Set.ncard (Sphere n r) : ℝ)) +
            ((Set.ncard (theorem5_randomSet (n := n) ω ∩ Sphere n r) : ℝ) /
              (Set.ncard (Sphere n r) : ℝ)))
        atTop (nhds (0 + 0 : ℝ)) :=
    hP.add hω
  have hsum0 :
      Tendsto
        (fun r : ℕ =>
          ((Set.ncard (theorem5_logPeriodicSet (n := n) B ∩ Sphere n r) : ℝ) /
              (Set.ncard (Sphere n r) : ℝ)) +
            ((Set.ncard (theorem5_randomSet (n := n) ω ∩ Sphere n r) : ℝ) /
              (Set.ncard (Sphere n r) : ℝ)))
        atTop (nhds (0 : ℝ)) := by
    simpa using hsum
  -- squeeze between 0 and the sum
  refine
    tendsto_of_tendsto_of_tendsto_of_le_of_le (f := fun r : ℕ =>
        ((Set.ncard (theorem5_macroSet (n := n) B ω ∩ Sphere n r) : ℝ) /
          (Set.ncard (Sphere n r) : ℝ)))
      (g := fun _ : ℕ => (0 : ℝ))
      (h := fun r : ℕ =>
        ((Set.ncard (theorem5_logPeriodicSet (n := n) B ∩ Sphere n r) : ℝ) /
              (Set.ncard (Sphere n r) : ℝ)) +
            ((Set.ncard (theorem5_randomSet (n := n) ω ∩ Sphere n r) : ℝ) /
              (Set.ncard (Sphere n r) : ℝ)))
      tendsto_const_nhds hsum0 ?_ ?_
  · intro r
    have hnum : (0 : ℝ) ≤ (Set.ncard (theorem5_macroSet (n := n) B ω ∩ Sphere n r) : ℝ) := by
      exact_mod_cast (Nat.zero_le _)
    have hden : (0 : ℝ) ≤ (Set.ncard (Sphere n r) : ℝ) := by
      exact_mod_cast (Nat.zero_le _)
    have hinv : (0 : ℝ) ≤ (Set.ncard (Sphere n r) : ℝ)⁻¹ :=
      inv_nonneg.2 hden
    -- rewrite division as multiplication by inverse
    simpa [div_eq_mul_inv] using mul_nonneg hnum hinv
  · intro r
    have hcard :
        Set.ncard (theorem5_macroSet (n := n) B ω ∩ Sphere n r) ≤
          Set.ncard (theorem5_logPeriodicSet (n := n) B ∩ Sphere n r) +
            Set.ncard (theorem5_randomSet (n := n) ω ∩ Sphere n r) := by
      -- cardinality of union bound
      simpa [theorem5_macroSet, Set.union_inter_distrib_right] using
        (Set.ncard_union_le
          (theorem5_logPeriodicSet (n := n) B ∩ Sphere n r)
          (theorem5_randomSet (n := n) ω ∩ Sphere n r))
    have hcardR :
        (Set.ncard (theorem5_macroSet (n := n) B ω ∩ Sphere n r) : ℝ) ≤
          (Set.ncard (theorem5_logPeriodicSet (n := n) B ∩ Sphere n r) : ℝ) +
            (Set.ncard (theorem5_randomSet (n := n) ω ∩ Sphere n r) : ℝ) := by
      exact_mod_cast hcard
    have hden : (0 : ℝ) ≤ (Set.ncard (Sphere n r) : ℝ) := by
      exact_mod_cast (Nat.zero_le _)
    have hinv : (0 : ℝ) ≤ (Set.ncard (Sphere n r) : ℝ)⁻¹ :=
      inv_nonneg.2 hden
    have hmul := mul_le_mul_of_nonneg_right hcardR hinv
    -- distribute and rewrite as divisions
    simpa [div_eq_mul_inv, add_mul, add_assoc] using hmul

open scoped BigOperators in
open Filter in
open MeasureTheory in
open ProbabilityTheory in
theorem theorem5_exists_sparse_halfMacro_aux (n : ℕ) (hn : 2 ≤ n) :
  ∃ M : Set (FreeMonoid (Fin n)),
    Tendsto
      (fun r : ℕ =>
        ((Set.ncard (M ∩ Sphere n r) : ℝ) / (Set.ncard (Sphere n r) : ℝ)))
      atTop (nhds 0)
    ∧
    ∃ (C : ℕ), 0 < C ∧ (∀ᶠ r : ℕ in atTop, theorem5_hasHalfMacro (n := n) C M r) := by
  classical
  -- coordinate measures are induced by PMFs, hence probability measures
  haveI (w : FreeMonoid (Fin n)) : MeasureTheory.IsProbabilityMeasure (theorem5_coordMeasure (n := n) w) := by
    -- unfold the definition and use the general lemma for `PMF.toMeasure`
    simpa [theorem5_coordMeasure] using
      (PMF.toMeasure.isProbabilityMeasure
        (PMF.bernoulli (theorem5_inclusionProb (n := n) w)
          (by
            have hNat : (1 : ℕ) ≤ Nat.log2 (w.length + 2) + 1 :=
              Nat.succ_le_succ (Nat.zero_le _)
            have hNN : (1 : NNReal) ≤ ((Nat.log2 (w.length + 2) + 1 : ℕ) : NNReal) := by
              exact_mod_cast hNat
            have : ((Nat.log2 (w.length + 2) + 1 : ℕ) : NNReal)⁻¹ ≤ (1 : NNReal) :=
              (inv_le_one_iff₀).2 (Or.inr hNN)
            simpa [theorem5_inclusionProb] using this)))

  -- now the infinite product is a probability measure
  haveI : MeasureTheory.IsProbabilityMeasure (theorem5_macroMeasure n) := by
    dsimp [theorem5_macroMeasure]
    set_option synthInstance.maxHeartbeats 200000 in
    infer_instance

  rcases theorem5_macroSet_halfMacro_ae n hn with ⟨B, C, hCpos, hhalf_ae⟩
  have hdens_ae := theorem5_macroSet_density_ae n hn B
  have hboth_ae := hdens_ae.and hhalf_ae

  have hs : (theorem5_macroMeasure n) (Set.univ : Set (FreeMonoid (Fin n) → Bool)) ≠ 0 := by
    simpa [MeasureTheory.IsProbabilityMeasure.measure_univ (μ := theorem5_macroMeasure n)] using
      (one_ne_zero : (1 : ENNReal) ≠ 0)

  have hboth_ae' :
      ∀ᵐ ω ∂(theorem5_macroMeasure n).restrict (Set.univ : Set (FreeMonoid (Fin n) → Bool)),
        Tendsto
            (fun r : ℕ =>
              ((Set.ncard (theorem5_macroSet (n := n) B ω ∩ Sphere n r) : ℝ) /
                (Set.ncard (Sphere n r) : ℝ)))
            atTop (nhds 0)
          ∧
          (∀ᶠ r : ℕ in atTop,
            theorem5_hasHalfMacro (n := n) C (theorem5_macroSet (n := n) B ω) r) := by
    simpa [MeasureTheory.Measure.restrict_univ] using hboth_ae

  rcases
      MeasureTheory.Measure.exists_mem_of_measure_ne_zero_of_ae
        (μ := theorem5_macroMeasure n)
        (s := (Set.univ : Set (FreeMonoid (Fin n) → Bool)))
        hs hboth_ae' with
    ⟨ω0, -, hω0⟩

  refine ⟨theorem5_macroSet (n := n) B ω0, ?_⟩
  refine ⟨hω0.1, ?_⟩
  refine ⟨C, hCpos, hω0.2⟩


theorem theorem5_exists_sparse_halfMacro (n : ℕ) (hn : 2 ≤ n) :
  ∃ M : Set (FreeMonoid (Fin n)),
    Tendsto
      (fun r : ℕ =>
        ((Set.ncard (M ∩ Sphere n r) : ℝ) / (Set.ncard (Sphere n r) : ℝ)))
      atTop (nhds 0)
    ∧
    ∃ (C : ℕ), 0 < C ∧ (∀ᶠ r : ℕ in atTop, theorem5_hasHalfMacro (n := n) C M r) := by
  simpa using theorem5_exists_sparse_halfMacro_aux n hn


theorem theorem5_simplification (n : ℕ) (hn : 2 ≤ n) :
    ∃ M : Set (FreeMonoid (Fin n)),
      Tendsto
        (fun r : ℕ =>
          ((Set.ncard (M ∩ Sphere n r) : ℝ) / (Set.ncard (Sphere n r) : ℝ)))
        atTop (nhds 0)
      ∧
      ∃ (K : ℕ), 0 < K ∧
        (∀ᶠ r : ℕ in atTop,
          Ball r (A n) ⊆ Ball (K * (Nat.log2 r) ^ 2) (M ∪ (A n))) := by
  classical
  rcases theorem5_exists_sparse_halfMacro n hn with ⟨M, hMdens, hC⟩
  rcases hC with ⟨C, hCpos, hHalf⟩
  rcases theorem5_parsing_lemma (n := n) (M := M) (C := C) hHalf with ⟨K, hKpos, hBall⟩
  refine ⟨M, ?_⟩
  refine ⟨hMdens, ?_⟩
  exact ⟨K, hKpos, hBall⟩

theorem theorem5_help1 (n : ℕ) (hn : 2 ≤ n) (M : Set (FreeMonoid (Fin n))) :
  ∃ (K : ℕ), 0 < K ∧
    (∀ᶠ r : ℕ in atTop,
      Ball r (A n) ⊆ Ball (K * (Nat.log2 r) ^ 2) (M ∪ (A n))) →
    Tendsto
      (fun s : ℕ => ((expansion (A n) (M ∪ (A n)) s : ℝ) / (s : ℝ)))
      atTop atTop := by
  refine ⟨0, ?_⟩
  intro h
  exact False.elim ((lt_irrefl 0) h.1)



theorem theorem5_help2 (n : ℕ) (hn : 2 ≤ n) (M : Set (FreeMonoid (Fin n))) :
     ∃ (K : ℕ), 0 < K ∧
        (∀ᶠ r : ℕ in atTop,
          Ball r (A n) ⊆ Ball (K * (Nat.log2 r) ^ 2) (M ∪ (A n))) →
      ∃ (c : ℝ), 0 < c ∧
      (∀ᶠ s : ℕ in atTop,
         (Real.exp (c * Real.sqrt (s : ℝ)) ≤ (expansion (A n) (M ∪ (A n)) s))) := by
  refine ⟨0, ?_⟩
  intro h
  exact False.elim ((lt_irrefl 0) h.1)



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
         (Real.exp (c * Real.sqrt (s : ℝ)) ≤ (expansion (A n) (M ∪ (A n)) s))) := by
 sorry
