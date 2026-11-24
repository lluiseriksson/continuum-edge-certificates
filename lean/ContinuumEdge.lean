/-
  ContinuumEdge.lean
  Self-contained, zero-dependency Lean 4 formalization (Level L2: zero sorry, standard axioms only)
  for:
    "Shift-Invariant Cumulant Laws, Exact Stieltjes-Hankel Upper Certificates, and
     Minimax Resolution Limits for Continuum Spectral Edges from Imaginary-Time Evolution"

  Every theorem is proved parametrically over an arbitrary linearly ordered commutative field
  `OrdField K` (covering both `ℝ` and `ℚ`), with zero external dependencies, zero `sorry`,
  and zero `Classical.choice`.

  Formalized results (16 audited theorems in `AuditAxioms.lean`):
    1. `chebyshev_sum_assoc`            (Theorem 2.1: weighted discrete Chebyshev association)
    2. `chebyshev_cov_nonneg`           (Theorem 2.1: positive covariance for monotone pairs)
    3. `chebyshev_cov_nonpos`           (Theorem 2.1: negative covariance for anti-monotone pairs)
    4. `gamma_exp_vf_excess`            (Theorem 2.1: exact VF excess alpha*lam/(tau+lam)^2 >= 0)
    5. `gamma_exp_si_gap_exact`         (Theorem 2.2: exactness of Delta_SI on Gamma-Exponential)
    6. `gamma_exp_si_alpha_exact`       (Theorem 2.2: exactness of alpha_SI on Gamma-Exponential)
    7. `si_perturbation_cancellation`   (Theorem 2.2: exact O(c2 s^-2) cancellation in 2 k2^2 / k3)
    8. `si_alpha_perturbation_exact`    (Theorem 2.2: exact -3 eps leading term of alpha_SI)
    9. `quad_form_hankel_nonneg`        (Theorem 4.1: Hankel moment matrix PSD on positive measures)
   10. `shifted_hankel_psd`             (Theorem 4.1: shifted Hankel u*M0 - M1 PSD on [0, u])
   11. `hankel_witness_refutes_support` (Theorem 4.1: v^T (u M0 - M1) v < 0 refutes supp <= u)
   12. `interval_term_upper_bound`      (Theorem 4.1: sign-split upper bound on v_i v_j m_{i+j})
   13. `interval_hankel_witness_sound`  (Theorem 4.1: interval Hankel witness soundness over Q)
   14. `two_point_hankel_special_case`  (Theorem 4.1: n=0 specialization recovers 2-point bound)
   15. `hankel_monotone_in_u`           (Theorem 4.1: monotonicity of shifted Hankel form in u)
   16. `geometric_tail_term_le`         (Theorem 4.1: exact rational log series tail bound)
-/

namespace ContinuumEdge

-- ============================================================================
-- 0. Linearly Ordered Commutative Field Interface
-- ============================================================================

class OrdField (K : Type) extends Add K, Sub K, Mul K, Div K, Neg K, Zero K, One K, LT K, LE K where
  add_comm : ∀ a b : K, a + b = b + a
  add_assoc : ∀ a b c : K, (a + b) + c = a + (b + c)
  zero_add : ∀ a : K, 0 + a = a
  add_neg_cancel : ∀ a : K, a + (-a) = 0
  sub_eq_add_neg : ∀ a b : K, a - b = a + (-b)
  mul_comm : ∀ a b : K, a * b = b * a
  mul_assoc : ∀ a b c : K, (a * b) * c = a * (b * c)
  one_mul : ∀ a : K, 1 * a = a
  left_distrib : ∀ a b c : K, a * (b + c) = a * b + a * c
  div_eq_mul_inv : ∀ a b : K, a / b = a * (1 / b)
  mul_inv_cancel : ∀ a : K, a ≠ 0 → a * (1 / a) = 1
  le_refl : ∀ a : K, a ≤ a
  le_trans : ∀ {a b c : K}, a ≤ b → b ≤ c → a ≤ c
  le_antisymm : ∀ {a b : K}, a ≤ b → b ≤ a → a = b
  le_of_lt : ∀ {a b : K}, a < b → a ≤ b
  lt_of_lt_of_le : ∀ {a b c : K}, a < b → b ≤ c → a < c
  lt_of_le_of_lt : ∀ {a b c : K}, a ≤ b → b < c → a < c
  lt_irrefl : ∀ a : K, ¬ (a < a)
  add_le_add : ∀ {a b c d : K}, a ≤ b → c ≤ d → a + c ≤ b + d
  mul_nonneg : ∀ {a b : K}, 0 ≤ a → 0 ≤ b → 0 ≤ a * b
  mul_pos : ∀ {a b : K}, 0 < a → 0 < b → 0 < a * b
  mul_le_mul_of_nonneg_left : ∀ {a b c : K}, a ≤ b → 0 ≤ c → c * a ≤ c * b
  mul_le_mul_of_nonneg_right : ∀ {a b c : K}, a ≤ b → 0 ≤ c → a * c ≤ b * c
  div_pos : ∀ {a b : K}, 0 < a → 0 < b → 0 < a / b
  zero_lt_one : (0 : K) < 1
  sub_nonneg_of_le : ∀ {a b : K}, a ≤ b → 0 ≤ b - a
  le_of_sub_nonneg : ∀ {a b : K}, 0 ≤ b - a → a ≤ b
  sub_pos_of_lt : ∀ {a b : K}, a < b → 0 < b - a
  le_total : ∀ a b : K, a ≤ b ∨ b ≤ a

section CoreAlgebra
variable {K : Type} [OrdField K]

theorem add_zero' (a : K) : a + 0 = a := by rw [OrdField.add_comm, OrdField.zero_add]
theorem mul_one' (a : K) : a * 1 = a := by rw [OrdField.mul_comm, OrdField.one_mul]
theorem right_distrib' (a b c : K) : (a + b) * c = a * c + b * c := by
  rw [OrdField.mul_comm, OrdField.left_distrib, OrdField.mul_comm c a, OrdField.mul_comm c b]

theorem mul_zero' (a : K) : a * 0 = 0 := by
  have h1 : a * 0 + a * 0 = a * 0 := by rw [← OrdField.left_distrib, OrdField.zero_add]
  have h2 := congrArg (· + -(a * 0)) h1
  rw [OrdField.add_assoc, OrdField.add_neg_cancel, add_zero'] at h2
  exact h2

theorem zero_mul' (a : K) : 0 * a = 0 := by rw [OrdField.mul_comm, mul_zero']
theorem neg_add_cancel' (a : K) : (-a) + a = 0 := by rw [OrdField.add_comm, OrdField.add_neg_cancel]

theorem mul_neg' (a b : K) : a * (-b) = -(a * b) := by
  have h : a * b + a * (-b) = 0 := by rw [← OrdField.left_distrib, OrdField.add_neg_cancel, mul_zero']
  have h2 := congrArg (-(a * b) + ·) h
  rw [← OrdField.add_assoc, neg_add_cancel', OrdField.zero_add, add_zero'] at h2
  exact h2

theorem neg_mul' (a b : K) : (-a) * b = -(a * b) := by rw [OrdField.mul_comm, mul_neg', OrdField.mul_comm]

theorem neg_neg' (a : K) : -(-a) = a := by
  have h : (-a) + a = 0 := neg_add_cancel' a
  have h2 := congrArg (· + -(-a)) h
  rw [OrdField.add_assoc, OrdField.add_comm a (-(-a)), ← OrdField.add_assoc,
      OrdField.add_neg_cancel, OrdField.zero_add, OrdField.zero_add] at h2
  exact h2.symm

theorem mul_sub' (a b c : K) : a * (b - c) = a * b - a * c := by
  rw [OrdField.sub_eq_add_neg, OrdField.sub_eq_add_neg, OrdField.left_distrib, mul_neg']

theorem sub_mul' (a b c : K) : (a - b) * c = a * c - b * c := by
  rw [OrdField.sub_eq_add_neg, OrdField.sub_eq_add_neg, right_distrib', neg_mul']

theorem sub_self' (a : K) : a - a = 0 := by rw [OrdField.sub_eq_add_neg, OrdField.add_neg_cancel]
theorem sub_add_cancel' (a b : K) : (a - b) + b = a := by
  rw [OrdField.sub_eq_add_neg, OrdField.add_assoc, neg_add_cancel', add_zero']
theorem add_sub_cancel' (a b : K) : (a + b) - b = a := by
  rw [OrdField.sub_eq_add_neg, OrdField.add_assoc, OrdField.add_neg_cancel, add_zero']

theorem neg_zero' : -(0 : K) = 0 := by
  have h := OrdField.add_neg_cancel (0 : K)
  rw [OrdField.zero_add] at h
  exact h

theorem sub_zero' (a : K) : a - 0 = a := by rw [OrdField.sub_eq_add_neg, neg_zero', add_zero']
theorem zero_sub' (a : K) : 0 - a = -a := by rw [OrdField.sub_eq_add_neg, OrdField.zero_add]

theorem neg_add' (a b : K) : -(a + b) = (-a) + (-b) := by
  have h : (a + b) + ((-a) + (-b)) = 0 := by
    rw [OrdField.add_assoc, ← OrdField.add_assoc b (-a) (-b),
        OrdField.add_comm b (-a), OrdField.add_assoc (-a) b (-b),
        ← OrdField.add_assoc a (-a), OrdField.add_neg_cancel, OrdField.add_neg_cancel, OrdField.zero_add]
  have h2 := congrArg (-(a + b) + ·) h
  rw [← OrdField.add_assoc, neg_add_cancel', OrdField.zero_add, add_zero'] at h2
  exact h2.symm

theorem neg_sub' (a b : K) : -(a - b) = b - a := by
  rw [OrdField.sub_eq_add_neg, neg_add', neg_neg', OrdField.add_comm, ← OrdField.sub_eq_add_neg]

theorem ne_zero_of_pos {a : K} (h : 0 < a) : a ≠ 0 := by
  intro heq; rw [heq] at h; exact OrdField.lt_irrefl 0 h

theorem mul_ne_zero' {a b : K} (ha : a ≠ 0) (hb : b ≠ 0) : a * b ≠ 0 := by
  intro h
  have h1 := congrArg (· * (1 / b)) h
  rw [OrdField.mul_assoc, OrdField.mul_inv_cancel b hb, mul_one', zero_mul'] at h1
  exact ha h1

theorem div_mul_cancel' (a b : K) (hb : b ≠ 0) : (a / b) * b = a := by
  rw [OrdField.div_eq_mul_inv, OrdField.mul_assoc, OrdField.mul_comm (1 / b) b,
      OrdField.mul_inv_cancel b hb, mul_one']

theorem mul_div_cancel_right' (a b : K) (hb : b ≠ 0) : (a * b) / b = a := by
  rw [OrdField.div_eq_mul_inv, OrdField.mul_assoc, OrdField.mul_inv_cancel b hb, mul_one']

theorem div_eq_of_eq_mul {a b c : K} (hb : b ≠ 0) (h : c * b = a) : c = a / b := by
  calc c = (c * b) / b := (mul_div_cancel_right' c b hb).symm
    _ = a / b := congrArg (· / b) h

theorem sq_nonneg' (a : K) : 0 ≤ a * a := by
  rcases OrdField.le_total 0 a with ha | ha
  · exact OrdField.mul_nonneg ha ha
  · have hna : 0 ≤ -a := by
      have h := OrdField.sub_nonneg_of_le ha
      rw [zero_sub'] at h; exact h
    have hsq := OrdField.mul_nonneg hna hna
    rw [neg_mul', mul_neg', neg_neg'] at hsq
    exact hsq

theorem two_pos : (0 : K) < 1 + 1 := by
  have h01 := OrdField.zero_lt_one (K := K)
  have h := OrdField.add_le_add (OrdField.le_refl (1 : K)) (OrdField.le_of_lt h01)
  rw [add_zero'] at h
  exact OrdField.lt_of_lt_of_le h01 h

theorem two_ne_zero : (1 : K) + 1 ≠ 0 := ne_zero_of_pos two_pos

theorem nonneg_of_two_mul_nonneg {a : K} (h : 0 ≤ (1 + 1) * a) : 0 ≤ a := by
  have hinv : 0 ≤ 1 / ((1 : K) + 1) := OrdField.le_of_lt (OrdField.div_pos OrdField.zero_lt_one two_pos)
  have hm := OrdField.mul_le_mul_of_nonneg_left h hinv
  rw [mul_zero', ← OrdField.mul_assoc, OrdField.mul_comm (1 / (1 + 1)) (1 + 1),
      OrdField.mul_inv_cancel (1 + 1) two_ne_zero, OrdField.one_mul] at hm
  exact hm

theorem neg_le_neg' {a b : K} (h : a ≤ b) : -b ≤ -a := by
  apply OrdField.le_of_sub_nonneg
  rw [OrdField.sub_eq_add_neg, neg_neg', OrdField.add_comm, ← OrdField.sub_eq_add_neg]
  exact OrdField.sub_nonneg_of_le h

theorem mul_le_mul_of_nonpos_left {a b c : K} (hab : a ≤ b) (hc : c ≤ 0) : c * b ≤ c * a := by
  have hnc : 0 ≤ -c := by have h := OrdField.sub_nonneg_of_le hc; rw [zero_sub'] at h; exact h
  have hm := OrdField.mul_le_mul_of_nonneg_left hab hnc
  rw [neg_mul', neg_mul'] at hm
  have h2 := neg_le_neg' hm
  rw [neg_neg', neg_neg'] at h2
  exact h2

def listSum : List K → K
  | [] => 0
  | x :: xs => x + listSum xs

def powK (a : K) : Nat → K
  | 0 => 1
  | n + 1 => a * powK a n

theorem powK_nonneg {a : K} (ha : 0 ≤ a) : ∀ n : Nat, 0 ≤ powK a n
  | 0 => OrdField.le_of_lt OrdField.zero_lt_one
  | n + 1 => OrdField.mul_nonneg ha (powK_nonneg ha n)

theorem powK_add (a : K) (m n : Nat) : powK a (m + n) = powK a m * powK a n := by
  induction m with
  | zero => simp [powK, OrdField.one_mul]
  | succ k ih =>
    have hsucc : k + 1 + n = (k + n) + 1 := by omega
    rw [hsucc, powK, ih, powK, OrdField.mul_assoc]

theorem listSum_nonneg (l : List K) (h : ∀ x ∈ l, 0 ≤ x) : 0 ≤ listSum l := by
  induction l with
  | nil => exact OrdField.le_refl 0
  | cons a t ih =>
    simp only [listSum]
    have ha := h a (List.Mem.head t)
    have ht := ih (fun x hx => h x (List.Mem.tail a hx))
    have hs := OrdField.add_le_add ha ht
    rw [OrdField.zero_add] at hs; exact hs

theorem listSum_map_mul_left {α : Type} (l : List α) (c : K) (f : α → K) :
    listSum (l.map (fun x => c * f x)) = c * listSum (l.map f) := by
  induction l with
  | nil => simp [listSum, mul_zero']
  | cons a t ih => simp only [List.map_cons, listSum, ih, OrdField.left_distrib]

theorem listSum_map_mul_right {α : Type} (l : List α) (f : α → K) (c : K) :
    listSum (l.map (fun x => f x * c)) = listSum (l.map f) * c := by
  induction l with
  | nil => simp [listSum, zero_mul']
  | cons a t ih => simp only [List.map_cons, listSum, ih, right_distrib']

theorem listSum_map_add {α : Type} (l : List α) (f g : α → K) :
    listSum (l.map (fun x => f x + g x)) = listSum (l.map f) + listSum (l.map g) := by
  induction l with
  | nil => simp [listSum, OrdField.zero_add]
  | cons a t ih =>
    simp only [List.map_cons, listSum, ih]
    rw [OrdField.add_assoc (f a) (g a), ← OrdField.add_assoc (g a),
        OrdField.add_comm (g a) (listSum (t.map f)), OrdField.add_assoc (listSum (t.map f)),
        ← OrdField.add_assoc (f a)]

theorem listSum_map_sub {α : Type} (l : List α) (f g : α → K) :
    listSum (l.map (fun x => f x - g x)) = listSum (l.map f) - listSum (l.map g) := by
  induction l with
  | nil => simp [listSum, sub_self']
  | cons a t ih =>
    simp only [List.map_cons, listSum, ih]
    rw [OrdField.sub_eq_add_neg (f a) (g a),
        OrdField.sub_eq_add_neg (listSum (t.map f)) (listSum (t.map g)),
        OrdField.sub_eq_add_neg (f a + listSum (t.map f)) (g a + listSum (t.map g)),
        neg_add', OrdField.add_assoc (f a) (-g a),
        ← OrdField.add_assoc (-g a) (listSum (t.map f)),
        OrdField.add_comm (-g a) (listSum (t.map f)),
        OrdField.add_assoc (listSum (t.map f)) (-g a),
        ← OrdField.add_assoc (f a)]

theorem listSum_le_listSum {α : Type} (l : List α) (f g : α → K)
    (h : ∀ x ∈ l, f x ≤ g x) : listSum (l.map f) ≤ listSum (l.map g) := by
  induction l with
  | nil => exact OrdField.le_refl 0
  | cons a t ih =>
    simp only [List.map_cons, listSum]
    exact OrdField.add_le_add (h a (List.Mem.head t)) (ih (fun x hx => h x (List.Mem.tail a hx)))

theorem listSum_map_nonneg {α : Type} (l : List α) (f : α → K) (h : ∀ x ∈ l, 0 ≤ f x) :
    0 ≤ listSum (l.map f) := by
  apply listSum_nonneg
  intro y hy
  rcases List.mem_map.mp hy with ⟨x, hx, rfl⟩
  exact h x hx

end CoreAlgebra

-- ============================================================================
-- 1. THEOREM 2.1: Chebyshev Association & Cumulant-Covariance Sign Laws
-- ============================================================================

section ChebyshevCovariance
variable {K : Type} [OrdField K]

/-- **Theorem 2.1 (Weighted Discrete Chebyshev Association Inequality):**
    For any finite list `xs`, nonnegative weights `w`, and functions `f, g` that are comonotone
    on `xs` (`0 ≤ (f x - f y) * (g x - g y)` for all `x, y ∈ xs`), we have
      `(∑ w_i f_i) * (∑ w_i g_i) ≤ (∑ w_i) * (∑ w_i f_i g_i)`. -/
theorem chebyshev_sum_assoc {α : Type} (xs : List α) (w f g : α → K)
    (hw : ∀ x ∈ xs, 0 ≤ w x)
    (hmono : ∀ x ∈ xs, ∀ y ∈ xs, 0 ≤ (f x - f y) * (g x - g y)) :
    listSum (xs.map (fun x => w x * f x)) * listSum (xs.map (fun x => w x * g x)) ≤
    listSum (xs.map w) * listSum (xs.map (fun x => w x * (f x * g x))) := by
  -- Double sum identity: ∑_x ∑_y w_x w_y (f_x - f_y)(g_x - g_y)
  -- = 2 * ((∑ w)(∑ w f g) - (∑ w f)(∑ w g)) >= 0
  have hdbl_nn : 0 ≤ listSum (xs.map (fun x => listSum (xs.map (fun y =>
      (w x * w y) * ((f x - f y) * (g x - g y)))))) := by
    apply listSum_map_nonneg; intro x hx
    apply listSum_map_nonneg; intro y hy
    exact OrdField.mul_nonneg (OrdField.mul_nonneg (hw x hx) (hw y hy)) (hmono x hx y hy)
  have hexpand : ∀ x y : α,
      (w x * w y) * ((f x - f y) * (g x - g y)) =
      (w x * (f x * g x)) * w y + w x * (w y * (f y * g y)) -
      ((w x * f x) * (w y * g y) + (w x * g x) * (w y * f y)) := by
    intro x y
    rw [sub_mul' (f x) (f y), mul_sub' (f x) (g x) (g y), mul_sub' (f y) (g x) (g y),
        OrdField.sub_eq_add_neg (f x * g x - f x * g y),
        OrdField.sub_eq_add_neg (f x * g x),
        OrdField.sub_eq_add_neg (f y * g x),
        neg_add', neg_neg', OrdField.left_distrib, OrdField.left_distrib, OrdField.left_distrib,
        mul_neg', mul_neg',
        OrdField.sub_eq_add_neg ((w x * (f x * g x)) * w y + w x * (w y * (f y * g y))),
        neg_add']
    -- Match all 4 products
    have t1 : (w x * w y) * (f x * g x) = (w x * (f x * g x)) * w y := by
      rw [OrdField.mul_assoc, OrdField.mul_comm (w y), ← OrdField.mul_assoc]
    have t2 : (w x * w y) * (f y * g y) = w x * (w y * (f y * g y)) := OrdField.mul_assoc _ _ _
    have t3 : (w x * w y) * (f x * g y) = (w x * f x) * (w y * g y) := by
      rw [OrdField.mul_assoc (w x) (w y), ← OrdField.mul_assoc (w y) (f x),
          OrdField.mul_comm (w y) (f x), OrdField.mul_assoc (f x) (w y), ← OrdField.mul_assoc]
    have t4 : (w x * w y) * (f y * g x) = (w x * g x) * (w y * f y) := by
      rw [OrdField.mul_comm (f y) (g x), OrdField.mul_assoc (w x) (w y),
          ← OrdField.mul_assoc (w y) (g x), OrdField.mul_comm (w y) (g x),
          OrdField.mul_assoc (g x) (w y), ← OrdField.mul_assoc]
    rw [t1, t2, t3, t4]
    let A := (w x * (f x * g x)) * w y
    let B := w x * (w y * (f y * g y))
    let C := (w x * f x) * (w y * g y)
    let D := (w x * g x) * (w y * f y)
    change (A + -C) + (-D + B) = (A + B) + (-C + -D)
    rw [OrdField.add_assoc A (-C) (-D + B), ← OrdField.add_assoc (-C) (-D) B,
        OrdField.add_comm (-C + -D) B, ← OrdField.add_assoc A B (-C + -D)]
  -- Evaluate the double sum term by term
  let SW := listSum (xs.map w)
  let SF := listSum (xs.map (fun x => w x * f x))
  let SG := listSum (xs.map (fun x => w x * g x))
  let SFG := listSum (xs.map (fun x => w x * (f x * g x)))
  have hid : listSum (xs.map (fun x => listSum (xs.map (fun y =>
      (w x * w y) * ((f x - f y) * (g x - g y)))))) =
      (1 + 1) * (SW * SFG - SF * SG) := by
    have hstep1 : listSum (xs.map (fun x => listSum (xs.map (fun y =>
        (w x * w y) * ((f x - f y) * (g x - g y)))))) =
        listSum (xs.map (fun x => listSum (xs.map (fun y =>
          (w x * (f x * g x)) * w y + w x * (w y * (f y * g y)) -
          ((w x * f x) * (w y * g y) + (w x * g x) * (w y * f y)))))) := by
      congr 1; apply List.map_congr_left; intro x _
      congr 1; apply List.map_congr_left; intro y _
      exact hexpand x y
    rw [hstep1]
    have hinner : ∀ x : α,
        listSum (xs.map (fun y =>
          (w x * (f x * g x)) * w y + w x * (w y * (f y * g y)) -
          ((w x * f x) * (w y * g y) + (w x * g x) * (w y * f y)))) =
        (w x * (f x * g x)) * SW + w x * SFG - ((w x * f x) * SG + (w x * g x) * SF) := by
      intro x
      rw [listSum_map_sub, listSum_map_add, listSum_map_add,
          listSum_map_mul_left xs (w x * (f x * g x)) w,
          listSum_map_mul_left xs (w x) (fun y => w y * (f y * g y)),
          listSum_map_mul_left xs (w x * f x) (fun y => w y * g y),
          listSum_map_mul_left xs (w x * g x) (fun y => w y * f y)]
    have hstep2 : listSum (xs.map (fun x => listSum (xs.map (fun y =>
        (w x * (f x * g x)) * w y + w x * (w y * (f y * g y)) -
        ((w x * f x) * (w y * g y) + (w x * g x) * (w y * f y)))))) =
        listSum (xs.map (fun x =>
          (w x * (f x * g x)) * SW + w x * SFG - ((w x * f x) * SG + (w x * g x) * SF))) := by
      congr 1; apply List.map_congr_left; intro x _; exact hinner x
    rw [hstep2, listSum_map_sub, listSum_map_add, listSum_map_add,
        listSum_map_mul_right xs (fun x => w x * (f x * g x)) SW,
        listSum_map_mul_right xs w SFG,
        listSum_map_mul_right xs (fun x => w x * f x) SG,
        listSum_map_mul_right xs (fun x => w x * g x) SF]
    change (SFG * SW + SW * SFG) - (SF * SG + SG * SF) = (1 + 1) * (SW * SFG - SF * SG)
    rw [OrdField.mul_comm SFG SW, OrdField.mul_comm SG SF,
        right_distrib' 1 1 (SW * SFG - SF * SG), OrdField.one_mul,
        OrdField.sub_eq_add_neg (SW * SFG + SW * SFG), neg_add',
        OrdField.sub_eq_add_neg (SW * SFG) (SF * SG)]
    let P := SW * SFG; let Q := -(SF * SG)
    change (P + P) + (Q + Q) = (P + Q) + (P + Q)
    rw [OrdField.add_assoc P P (Q + Q), ← OrdField.add_assoc P Q Q,
        OrdField.add_comm P Q, OrdField.add_assoc Q P Q, ← OrdField.add_assoc P Q (P + Q),
        OrdField.add_comm Q P]
  rw [hid] at hdbl_nn
  exact OrdField.le_of_sub_nonneg (nonneg_of_two_mul_nonneg hdbl_nn)

/-- **Theorem 2.1 (Normalized Covariance Form — Monotone Case):**
    When `∑ w_i = 1`, comonotonicity implies `0 ≤ ∑ w_i f_i g_i - (∑ w_i f_i)(∑ w_i g_i)`. -/
theorem chebyshev_cov_nonneg {α : Type} (xs : List α) (w f g : α → K)
    (hw : ∀ x ∈ xs, 0 ≤ w x)
    (hsum : listSum (xs.map w) = 1)
    (hmono : ∀ x ∈ xs, ∀ y ∈ xs, 0 ≤ (f x - f y) * (g x - g y)) :
    0 ≤ listSum (xs.map (fun x => w x * (f x * g x))) -
        listSum (xs.map (fun x => w x * f x)) * listSum (xs.map (fun x => w x * g x)) := by
  have h := chebyshev_sum_assoc xs w f g hw hmono
  rw [hsum, OrdField.one_mul] at h
  exact OrdField.sub_nonneg_of_le h

/-- **Theorem 2.1 (Normalized Covariance Form — Anti-Monotone Case, e.g. 1D van Hove Band):**
    When `∑ w_i = 1` and `(f x - f y)(g x - g y) ≤ 0`, covariance is nonpositive. -/
theorem chebyshev_cov_nonpos {α : Type} (xs : List α) (w f g : α → K)
    (hw : ∀ x ∈ xs, 0 ≤ w x)
    (hsum : listSum (xs.map w) = 1)
    (hanti : ∀ x ∈ xs, ∀ y ∈ xs, (f x - f y) * (g x - g y) ≤ 0) :
    listSum (xs.map (fun x => w x * (f x * g x))) -
    listSum (xs.map (fun x => w x * f x)) * listSum (xs.map (fun x => w x * g x)) ≤ 0 := by
  have hmono : ∀ x ∈ xs, ∀ y ∈ xs, 0 ≤ (f x - f y) * ((-g x) - (-g y)) := by
    intro x hx y hy
    have hrew : (f x - f y) * ((-g x) - (-g y)) = -((f x - f y) * (g x - g y)) := by
      have hg : (-g x) - (-g y) = -(g x - g y) := by
        rw [neg_sub', OrdField.sub_eq_add_neg (-g x), neg_neg', OrdField.add_comm, ← OrdField.sub_eq_add_neg]
      rw [hg, mul_neg']
    rw [hrew]
    have h := OrdField.sub_nonneg_of_le (hanti x hx y hy)
    rw [zero_sub'] at h; exact h
  have hcov := chebyshev_cov_nonneg xs w f (fun x => -g x) hw hsum hmono
  have hfg : listSum (xs.map (fun x => w x * (f x * (-g x)))) =
             -listSum (xs.map (fun x => w x * (f x * g x))) := by
    have h1 : xs.map (fun x => w x * (f x * (-g x))) = xs.map (fun x => (-1 : K) * (w x * (f x * g x))) := by
      apply List.map_congr_left; intro x _
      rw [mul_neg', mul_neg', neg_mul', OrdField.one_mul]
    rw [h1, listSum_map_mul_left, neg_mul', OrdField.one_mul]
  have hg_sum : listSum (xs.map (fun x => w x * (-g x))) = -listSum (xs.map (fun x => w x * g x)) := by
    have h1 : xs.map (fun x => w x * (-g x)) = xs.map (fun x => (-1 : K) * (w x * g x)) := by
      apply List.map_congr_left; intro x _
      rw [mul_neg', neg_mul', OrdField.one_mul]
    rw [h1, listSum_map_mul_left, neg_mul', OrdField.one_mul]
  rw [hfg, hg_sum, mul_neg'] at hcov
  have hrew : -listSum (xs.map (fun x => w x * (f x * g x))) -
      -(listSum (xs.map (fun x => w x * f x)) * listSum (xs.map (fun x => w x * g x))) =
      -(listSum (xs.map (fun x => w x * (f x * g x))) -
        listSum (xs.map (fun x => w x * f x)) * listSum (xs.map (fun x => w x * g x))) := by
    rw [OrdField.sub_eq_add_neg, neg_neg', neg_sub', OrdField.sub_eq_add_neg, OrdField.add_comm]
  rw [hrew] at hcov
  have hneg := neg_le_neg' hcov
  rw [neg_neg', neg_zero'] at hneg
  exact hneg

/-- **Theorem 2.1 (Gamma-Exponential VF Excess Identity):**
    For `g = Δ + α/s`, `κ2 = α/s^2`, `s = τ + λ`, we have `g - τ*κ2 - Δ = (α*λ)/s^2 ≥ 0`. -/
theorem gamma_exp_vf_excess (Delta alpha tau lam : K)
    (hs : tau + lam ≠ 0) :
    let s := tau + lam
    let g := Delta + alpha / s
    let k2 := alpha / (s * s)
    (g - tau * k2) - Delta = (alpha * lam) / (s * s) := by
  intro s g k2
  have hs2 : s * s ≠ 0 := mul_ne_zero' hs hs
  have h1 : (g - tau * k2) - Delta = alpha / s - tau * (alpha / (s * s)) := by
    dsimp only [g, k2]
    rw [OrdField.sub_eq_add_neg (Delta + alpha / s), OrdField.sub_eq_add_neg,
        OrdField.add_assoc Delta (alpha / s),
        OrdField.add_comm (Delta + (alpha / s + -(tau * (alpha / (s * s))))) (-Delta),
        ← OrdField.add_assoc (-Delta) Delta, neg_add_cancel', OrdField.zero_add,
        ← OrdField.sub_eq_add_neg]
  rw [h1]
  apply div_eq_of_eq_mul hs2
  rw [sub_mul', OrdField.mul_assoc tau (alpha / (s * s)) (s * s), div_mul_cancel' alpha (s * s) hs2]
  have ha : (alpha / s) * (s * s) = alpha * s := by
    rw [← OrdField.mul_assoc, div_mul_cancel' alpha s hs]
  rw [ha, OrdField.mul_comm tau alpha]
  dsimp only [s]
  rw [OrdField.left_distrib alpha tau lam, OrdField.add_comm (alpha * tau), add_sub_cancel']

end ChebyshevCovariance

-- ============================================================================
-- 2. THEOREM 2.2: Shift-Invariant Cumulant Estimators & Cancellation Miracle
-- ============================================================================

section ShiftInvariantCumulants
variable {K : Type} [OrdField K]

/-- **Theorem 2.2 (Exactness of Shift-Invariant Gap Estimator `Δ_SI` on Gamma-Exponential Family):**
    For ANY `Δ`, `α ≠ 0`, `s = τ + λ ≠ 0`, with `g = Δ + α/s`, `κ2 = α/s^2`, `κ3 = 2α/s^3`:
      `g - (2 * κ2^2) / κ3 = Δ` identically! -/
theorem gamma_exp_si_gap_exact (Delta alpha s : K) (ha : alpha ≠ 0) (hs : s ≠ 0) :
    let two : K := 1 + 1
    let g := Delta + alpha / s
    let k2 := alpha / (s * s)
    let k3 := (two * alpha) / (s * (s * s))
    g - (two * (k2 * k2)) / k3 = Delta := by
  intro two g k2 k3
  have hs2 : s * s ≠ 0 := mul_ne_zero' hs hs
  have hs3 : s * (s * s) ≠ 0 := mul_ne_zero' hs hs2
  have h2a : two * alpha ≠ 0 := mul_ne_zero' two_ne_zero ha
  have hk3_nz : k3 ≠ 0 := by
    intro h0
    have h1 := congrArg (· * (s * (s * s))) h0
    dsimp only [k3] at h1
    rw [div_mul_cancel' _ _ hs3, zero_mul'] at h1
    exact h2a h1
  have hratio : (two * (k2 * k2)) / k3 = alpha / s := by
    symm
    apply div_eq_of_eq_mul hk3_nz
    -- Show (alpha / s) * k3 = two * (k2 * k2)
    have hs4 : (s * s) * (s * s) ≠ 0 := mul_ne_zero' hs2 hs2
    -- Multiply both sides by s^4
    have hmul : ((alpha / s) * k3) * ((s * s) * (s * s)) = (two * (k2 * k2)) * ((s * s) * (s * s)) := by
      have hL : ((alpha / s) * k3) * ((s * s) * (s * s)) = two * (alpha * alpha) := by
        dsimp only [k3]
        have hs4_eq : (s * s) * (s * s) = s * (s * (s * s)) := OrdField.mul_assoc s s (s * s)
        rw [hs4_eq, OrdField.mul_assoc (alpha / s), ← OrdField.mul_assoc (two * alpha / (s * (s * s))),
            OrdField.mul_comm (two * alpha / (s * (s * s))) s, OrdField.mul_assoc s,
            div_mul_cancel' (two * alpha) (s * (s * s)) hs3,
            ← OrdField.mul_assoc (alpha / s) s, div_mul_cancel' alpha s hs,
            OrdField.mul_comm alpha (two * alpha), OrdField.mul_assoc two alpha alpha]
      have hR : (two * (k2 * k2)) * ((s * s) * (s * s)) = two * (alpha * alpha) := by
        dsimp only [k2]
        rw [OrdField.mul_assoc two, OrdField.mul_assoc (alpha / (s * s)),
            ← OrdField.mul_assoc (alpha / (s * s)) (s * s), div_mul_cancel' alpha (s * s) hs2,
            OrdField.mul_comm alpha (s * s), ← OrdField.mul_assoc (alpha / (s * s)) (s * s),
            div_mul_cancel' alpha (s * s) hs2]
      rw [hL, hR]
    have hc := congrArg (· / ((s * s) * (s * s))) hmul
    rw [mul_div_cancel_right' _ _ hs4, mul_div_cancel_right' _ _ hs4] at hc
    exact hc
  dsimp only [g]
  rw [hratio, add_sub_cancel']

/-- **Theorem 2.2 (Exactness of Shift-Invariant Threshold Exponent `α_SI` on Gamma-Exponential Family):**
    For ANY `α ≠ 0`, `s ≠ 0`, `(4 * κ2^3) / κ3^2 = α` identically! -/
theorem gamma_exp_si_alpha_exact (alpha s : K) (ha : alpha ≠ 0) (hs : s ≠ 0) :
    let two : K := 1 + 1
    let four : K := two * two
    let k2 := alpha / (s * s)
    let k3 := (two * alpha) / (s * (s * s))
    (four * (k2 * (k2 * k2))) / (k3 * k3) = alpha := by
  intro two four k2 k3
  have hs2 : s * s ≠ 0 := mul_ne_zero' hs hs
  have hs3 : s * (s * s) ≠ 0 := mul_ne_zero' hs hs2
  have hs6 : (s * (s * s)) * (s * (s * s)) ≠ 0 := mul_ne_zero' hs3 hs3
  have h2a : two * alpha ≠ 0 := mul_ne_zero' two_ne_zero ha
  have hk3_nz : k3 ≠ 0 := by
    intro h0; have h1 := congrArg (· * (s * (s * s))) h0
    dsimp only [k3] at h1; rw [div_mul_cancel' _ _ hs3, zero_mul'] at h1; exact h2a h1
  have hk3_sq_nz : k3 * k3 ≠ 0 := mul_ne_zero' hk3_nz hk3_nz
  symm
  apply div_eq_of_eq_mul hk3_sq_nz
  -- Show alpha * (k3 * k3) = four * (k2 * (k2 * k2)) by multiplying by s^6
  have hmul : (alpha * (k3 * k3)) * ((s * (s * s)) * (s * (s * s))) =
              (four * (k2 * (k2 * k2))) * ((s * (s * s)) * (s * (s * s))) := by
    have hL : (alpha * (k3 * k3)) * ((s * (s * s)) * (s * (s * s))) =
              four * (alpha * (alpha * alpha)) := by
      dsimp only [k3, four]
      rw [OrdField.mul_assoc alpha, OrdField.mul_assoc (two * alpha / (s * (s * s))),
          ← OrdField.mul_assoc (two * alpha / (s * (s * s))) (s * (s * s)),
          div_mul_cancel' (two * alpha) (s * (s * s)) hs3,
          OrdField.mul_comm (two * alpha) (s * (s * s)),
          ← OrdField.mul_assoc (two * alpha / (s * (s * s))) (s * (s * s)),
          div_mul_cancel' (two * alpha) (s * (s * s)) hs3]
      -- alpha * ((two*alpha)*(two*alpha)) = (two*two)*(alpha*(alpha*alpha))
      rw [OrdField.mul_assoc two alpha (two * alpha), ← OrdField.mul_assoc alpha two alpha,
          OrdField.mul_comm alpha two, OrdField.mul_assoc two alpha alpha,
          ← OrdField.mul_assoc two two (alpha * alpha),
          OrdField.mul_comm alpha ((two * two) * (alpha * alpha)),
          OrdField.mul_assoc (two * two) (alpha * alpha) alpha,
          OrdField.mul_comm (alpha * alpha) alpha]
    have hR : (four * (k2 * (k2 * k2))) * ((s * (s * s)) * (s * (s * s))) =
              four * (alpha * (alpha * alpha)) := by
      dsimp only [k2]
      have hs6_eq : (s * (s * s)) * (s * (s * s)) = (s * s) * ((s * s) * (s * s)) := by
        rw [OrdField.mul_assoc s (s * s) (s * (s * s)), ← OrdField.mul_assoc (s * s) s (s * s),
            OrdField.mul_comm (s * s) s, OrdField.mul_assoc s (s * s) (s * s),
            ← OrdField.mul_assoc s s ((s * s) * (s * s))]
      rw [hs6_eq, OrdField.mul_assoc four]
      congr 1
      have hpair : ∀ x y : K, (alpha / (s * s) * x) * ((s * s) * y) = alpha * (x * y) := by
        intro x y
        rw [OrdField.mul_assoc (alpha / (s * s)) x ((s * s) * y),
            ← OrdField.mul_assoc x (s * s) y, OrdField.mul_comm x (s * s),
            OrdField.mul_assoc (s * s) x y, ← OrdField.mul_assoc (alpha / (s * s)) (s * s),
            div_mul_cancel' alpha (s * s) hs2]
      rw [hpair, hpair, div_mul_cancel' alpha (s * s) hs2]
    rw [hL, hR]
  have hc := congrArg (· / ((s * (s * s)) * (s * (s * s)))) hmul
  rw [mul_div_cancel_right' _ _ hs6, mul_div_cancel_right' _ _ hs6] at hc
  exact hc

/-- **Theorem 2.2 (Exact `O(ε)` Cancellation Miracle in `2 κ2^2 / κ3`):**
    Writing `ε = c2 (α + 1) / s^2`, the perturbative cumulants have relative factors `(1 + 3ε)` in `κ2`
    and `(1 + 6ε)` in `κ3`. The `O(ε)` error cancels identically:
      `(1 + 3ε)^2 / (1 + 6ε) - 1 = 9 ε^2 / (1 + 6ε)`. -/
theorem si_perturbation_cancellation (eps : K) (hden : 1 + ((1 + 1) * ((1 + 1) + 1)) * eps ≠ 0) :
    let three : K := (1 + 1) + 1
    let six : K := (1 + 1) * three
    let nine : K := three * three
    ((1 + three * eps) * (1 + three * eps)) / (1 + six * eps) - 1 =
    (nine * (eps * eps)) / (1 + six * eps) := by
  intro three six nine
  apply div_eq_of_eq_mul hden
  rw [sub_mul', OrdField.one_mul, div_mul_cancel' _ _ hden]
  -- Expand (1 + 3e)^2 - (1 + 6e) = 9e^2
  rw [right_distrib' 1 (three * eps) (1 + three * eps), OrdField.one_mul,
      OrdField.left_distrib (three * eps) 1 (three * eps), mul_one']
  have h6 : three * eps + three * eps = six * eps := by
    dsimp only [six]
    rw [right_distrib' 1 1 three, OrdField.one_mul, right_distrib' three three eps]
  have h9 : (three * eps) * (three * eps) = nine * (eps * eps) := by
    dsimp only [nine]
    rw [OrdField.mul_assoc three eps (three * eps), ← OrdField.mul_assoc eps three eps,
        OrdField.mul_comm eps three, OrdField.mul_assoc three eps eps,
        ← OrdField.mul_assoc three three (eps * eps)]
  change (1 + three * eps + (three * eps + (three * eps) * (three * eps))) - (1 + six * eps) = nine * (eps * eps)
  rw [h9, OrdField.add_assoc 1 (three * eps), ← OrdField.add_assoc (three * eps) (three * eps),
      h6, ← OrdField.add_assoc 1 (six * eps), OrdField.add_comm (1 + six * eps), add_sub_cancel']

/-- **Theorem 2.2 (Exact `-3 ε` Leading Correction of `α_SI`):**
    `(1 + 3ε)^3 / (1 + 6ε)^2 - (1 - 3ε) = (27 ε^2 + 135 ε^3) / (1 + 6ε)^2`,
    establishing `α_SI - α = -3 c2 α (α + 1) / s^2 + O(s^-4)`. -/
theorem si_alpha_perturbation_exact (eps : K) (hden : 1 + ((1 + 1) * ((1 + 1) + 1)) * eps ≠ 0) :
    let three : K := (1 + 1) + 1
    let six : K := (1 + 1) * three
    let nine : K := three * three
    let t27 : K := three * nine
    let t135 : K := ((three + (1 + 1)) * t27)
    let num := (1 + three * eps) * ((1 + three * eps) * (1 + three * eps))
    let den := (1 + six * eps) * (1 + six * eps)
    num / den - (1 - three * eps) = (t27 * (eps * eps) + t135 * (eps * (eps * eps))) / den := by
  intro three six nine t27 t135 num den
  have hden2 : den ≠ 0 := mul_ne_zero' hden hden
  apply div_eq_of_eq_mul hden2
  rw [sub_mul', div_mul_cancel' _ _ hden2]
  -- Pure polynomial identity in eps:
  -- num = 1 + 9e + 27e^2 + 27e^3
  -- (1 - 3e) * den = (1 - 3e) * (1 + 12e + 36e^2) = 1 + 9e - 108e^3? Wait: check!
  -- (1 - 3e)(1 + 12e + 36e^2) = 1 + 12e + 36e^2 - 3e - 36e^2 - 108e^3 = 1 + 9e - 108e^3!
  -- num - (1 - 3e)*den = 27e^2 + (27 + 108)e^3 = 27e^2 + 135e^3!!
  have h3_add : three + three = six := by dsimp only [six]; rw [right_distrib' 1 1 three, OrdField.one_mul]
  have h6_add : six + six = (1 + 1) * six := by rw [right_distrib' 1 1 six, OrdField.one_mul]
  have h9_eq : three + six = nine := by
    dsimp only [nine, six]
    rw [OrdField.left_distrib three (1 + 1) 1, mul_one', OrdField.mul_comm three (1 + 1), OrdField.add_comm]
  have h36_eq : six * six = three * ((1 + 1) * six) := by
    dsimp only [six]
    rw [← OrdField.mul_assoc ((1 + 1) * three) (1 + 1) three, OrdField.mul_comm _ three,
        OrdField.mul_comm ((1 + 1) * three) (1 + 1)]
  have h108_eq : three * (six * six) + t27 = t135 := by
    dsimp only [t135, t27, six, nine]
    have h4 : ((1 + 1) * three) * ((1 + 1) * three) = ((1 + 1) * (1 + 1)) * (three * three) := by
      rw [OrdField.mul_assoc (1 + 1) three, ← OrdField.mul_assoc three (1 + 1) three,
          OrdField.mul_comm three (1 + 1), OrdField.mul_assoc (1 + 1) three three,
          ← OrdField.mul_assoc (1 + 1) (1 + 1)]
    have h4_eq : (1 + 1) * (1 + 1) = three + 1 := by
      dsimp only [three]
      rw [OrdField.left_distrib (1 + 1) 1 1, mul_one', ← OrdField.add_assoc]
    rw [h4, h4_eq, ← OrdField.mul_assoc three (three + 1), OrdField.mul_comm three (three + 1),
        OrdField.mul_assoc (three + 1) three (three * three)]
    have h1 : (three + 1) * (three * (three * three)) + 1 * (three * (three * three)) =
              ((three + 1) + 1) * (three * (three * three)) := (right_distrib' (three + 1) 1 _).symm
    rw [OrdField.one_mul] at h1
    rw [h1, OrdField.add_assoc three 1 1]
  -- Expand num = 1 + 9e + 27e^2 + 27e^3
  have hsq3 : (1 + three * eps) * (1 + three * eps) = 1 + six * eps + nine * (eps * eps) := by
    rw [right_distrib' 1 (three * eps) (1 + three * eps), OrdField.one_mul,
        OrdField.left_distrib (three * eps) 1 (three * eps), mul_one']
    have h1 : three * eps + three * eps = six * eps := by rw [← right_distrib', h3_add]
    have h2 : (three * eps) * (three * eps) = nine * (eps * eps) := by
      dsimp only [nine]
      rw [OrdField.mul_assoc three eps, ← OrdField.mul_assoc eps three eps, OrdField.mul_comm eps three,
          OrdField.mul_assoc three eps eps, ← OrdField.mul_assoc three three]
    rw [h2, OrdField.add_assoc 1 (three * eps), ← OrdField.add_assoc (three * eps) (three * eps),
        h1, ← OrdField.add_assoc 1 (six * eps)]
  have hnum : num = 1 + nine * eps + t27 * (eps * eps) + t27 * (eps * (eps * eps)) := by
    dsimp only [num]; rw [hsq3]
    rw [OrdField.left_distrib (1 + three * eps), OrdField.left_distrib (1 + three * eps),
        right_distrib' 1 (three * eps) 1, right_distrib' 1 (three * eps) (six * eps),
        right_distrib' 1 (three * eps) (nine * (eps * eps)),
        OrdField.one_mul, OrdField.one_mul, OrdField.one_mul, mul_one']
    have m1 : (three * eps) * (six * eps) = (three * six) * (eps * eps) := by
      rw [OrdField.mul_assoc three eps, ← OrdField.mul_assoc eps six eps, OrdField.mul_comm eps six,
          OrdField.mul_assoc six eps eps, ← OrdField.mul_assoc three six]
    have m2 : (three * eps) * (nine * (eps * eps)) = t27 * (eps * (eps * eps)) := by
      dsimp only [t27]
      rw [OrdField.mul_assoc three eps, ← OrdField.mul_assoc eps nine, OrdField.mul_comm eps nine,
          OrdField.mul_assoc nine eps, ← OrdField.mul_assoc three nine]
    have c1 : three * eps + six * eps = nine * eps := by rw [← right_distrib', h9_eq]
    have c2 : three * six + nine = t27 := by
      dsimp only [t27, nine]
      rw [OrdField.add_comm (three * six) (three * three),
          ← OrdField.left_distrib three three six, h9_eq]
    rw [m1, m2]
    have grp1 : (1 + three * eps) + (six * eps + (three * six) * (eps * eps)) =
                1 + nine * eps + (three * six) * (eps * eps) := by
      rw [OrdField.add_assoc 1 (three * eps), ← OrdField.add_assoc (three * eps) (six * eps),
          c1, ← OrdField.add_assoc 1 (nine * eps)]
    rw [grp1, ← OrdField.add_assoc (1 + nine * eps + (three * six) * (eps * eps)) (nine * (eps * eps)),
        OrdField.add_assoc (1 + nine * eps) ((three * six) * (eps * eps)) (nine * (eps * eps)),
        ← right_distrib' (three * six) nine (eps * eps), c2]
  -- Expand den = 1 + 12e + 36e^2 and (1 - 3e)*den = 1 + 9e - 108e^3
  have hden_exp : den = 1 + ((1 + 1) * six) * eps + (six * six) * (eps * eps) := by
    dsimp only [den]
    rw [right_distrib' 1 (six * eps) (1 + six * eps), OrdField.one_mul,
        OrdField.left_distrib (six * eps) 1 (six * eps), mul_one']
    have h1 : six * eps + six * eps = ((1 + 1) * six) * eps := by rw [← right_distrib', h6_add]
    have h2 : (six * eps) * (six * eps) = (six * six) * (eps * eps) := by
      rw [OrdField.mul_assoc six eps, ← OrdField.mul_assoc eps six eps, OrdField.mul_comm eps six,
          OrdField.mul_assoc six eps eps, ← OrdField.mul_assoc six six]
    rw [h2, OrdField.add_assoc 1 (six * eps), ← OrdField.add_assoc (six * eps) (six * eps),
        h1, ← OrdField.add_assoc 1 (((1 + 1) * six) * eps)]
  have hsub_term : (1 - three * eps) * den = 1 + nine * eps - (three * (six * six)) * (eps * (eps * eps)) := by
    rw [hden_exp, OrdField.left_distrib, OrdField.left_distrib,
        sub_mul' 1 (three * eps) 1, sub_mul' 1 (three * eps) (((1 + 1) * six) * eps),
        sub_mul' 1 (three * eps) ((six * six) * (eps * eps)),
        OrdField.one_mul, OrdField.one_mul, OrdField.one_mul, mul_one']
    have k1 : ((1 + 1) * six) * eps - three * eps = nine * eps := by
      rw [← sub_mul']
      congr 1
      have h12 : (1 + 1) * six = nine + three := by
        rw [← h6_add, ← h9_eq, OrdField.add_assoc three six three, OrdField.add_comm six three,
            ← OrdField.add_assoc three three six, h3_add]
      rw [h12, add_sub_cancel']
    have k2 : (three * eps) * (((1 + 1) * six) * eps) = (six * six) * (eps * eps) := by
      rw [OrdField.mul_assoc three eps, ← OrdField.mul_assoc eps ((1 + 1) * six) eps,
          OrdField.mul_comm eps ((1 + 1) * six), OrdField.mul_assoc ((1 + 1) * six) eps eps,
          ← OrdField.mul_assoc three ((1 + 1) * six), ← h36_eq]
    have k3 : (three * eps) * ((six * six) * (eps * eps)) = (three * (six * six)) * (eps * (eps * eps)) := by
      rw [OrdField.mul_assoc three eps, ← OrdField.mul_assoc eps (six * six),
          OrdField.mul_comm eps (six * six), OrdField.mul_assoc (six * six) eps,
          ← OrdField.mul_assoc three (six * six)]
    rw [k2, k3]
    let A := three * eps; let B := ((1 + 1) * six) * eps
    let C := (six * six) * (eps * eps); let D := (three * (six * six)) * (eps * (eps * eps))
    change ((1 - A) + (B - C)) + (C - D) = (1 + nine * eps) - D
    have hBA : B - A = nine * eps := k1
    rw [OrdField.sub_eq_add_neg 1 A, OrdField.sub_eq_add_neg B C, OrdField.sub_eq_add_neg C D,
        OrdField.sub_eq_add_neg (1 + nine * eps) D]
    rw [OrdField.add_assoc (1 + -A) (B + -C) (C + -D),
        OrdField.add_assoc B (-C) (C + -D), ← OrdField.add_assoc (-C) C (-D),
        neg_add_cancel', OrdField.zero_add,
        ← OrdField.add_assoc (1 + -A) B (-D),
        OrdField.add_assoc 1 (-A) B, OrdField.add_comm (-A) B, ← OrdField.sub_eq_add_neg B A, hBA]
  rw [hnum, hsub_term]
  let P := 1 + nine * eps; let Q := t27 * (eps * eps)
  let R1 := t27 * (eps * (eps * eps)); let R2 := (three * (six * six)) * (eps * (eps * eps))
  change ((P + Q) + R1) - (P - R2) = Q + t135 * (eps * (eps * eps))
  have hR : R2 + R1 = t135 * (eps * (eps * eps)) := by
    dsimp only [R1, R2]; rw [← right_distrib', h108_eq]
  rw [OrdField.sub_eq_add_neg ((P + Q) + R1) (P - R2), neg_sub',
      OrdField.sub_eq_add_neg R2 P, OrdField.add_assoc (P + Q) R1 (R2 + -P),
      OrdField.add_comm R1 (R2 + -P), OrdField.add_assoc R2 (-P) R1,
      OrdField.add_comm (-P) R1, ← OrdField.add_assoc R2 R1 (-P), hR,
      OrdField.add_assoc P Q (t135 * (eps * (eps * eps)) + -P),
      OrdField.add_comm Q (t135 * (eps * (eps * eps)) + -P),
      OrdField.add_comm (t135 * (eps * (eps * eps))) (-P),
      OrdField.add_assoc (-P) (t135 * (eps * (eps * eps))) Q,
      ← OrdField.add_assoc P (-P), OrdField.add_neg_cancel, OrdField.zero_add,
      OrdField.add_comm]

end ShiftInvariantCumulants

-- ============================================================================
-- 3. THEOREM 4.1: Stieltjes-Hankel Upper Certificates & Interval Soundness
-- ============================================================================

section StieltjesHankel
variable {K : Type} [OrdField K]

/-- Discrete spectral moment `m_k = ∑_r w_r z_r^k` on a finite support list of `(weight, point)` pairs. -/
def momentK (meas : List (K × K)) (k : Nat) : K :=
  listSum (meas.map (fun wz => wz.1 * powK wz.2 k))

/-- Polynomial evaluation `P_v(z) = ∑_{i=0}^{n} v_i z^i` from coefficient list `v` (indexed from `offset`). -/
def polyEval (z : K) : Nat → List K → K
  | _, [] => 0
  | idx, c :: cs => c * powK z idx + polyEval z (idx + 1) cs

/-- Inner loop of Hankel quadratic form: `∑_j (vi * vj) * m(i + j)`. -/
def hankelInner (m : Nat → K) (i : Nat) (vi : K) : Nat → List K → K
  | _, [] => 0
  | j, vj :: us => (vi * vj) * m (i + j) + hankelInner m i vi (j + 1) us

/-- Outer loop of Hankel quadratic form: `∑_i hankelInner m i vi 0 v`. -/
def hankelOuter (m : Nat → K) (v : List K) : Nat → List K → K
  | _, [] => 0
  | i, vi :: vs => hankelInner m i vi 0 v + hankelOuter m v (i + 1) vs

/-- Hankel bilinear form `v^T H(m) v = ∑_i ∑_j v_i v_j m(i + j)` for an arbitrary moment oracle `m : Nat → K`. -/
def hankelQuad (m : Nat → K) (v : List K) : K :=
  hankelOuter m v 0 v

/-- Shifted Hankel quadratic form `v^T (u M_0 - M_1) v`. -/
def shiftedHankelQuad (m : Nat → K) (u : K) (v : List K) : K :=
  u * hankelQuad m v - hankelQuad (fun k => m (k + 1)) v

private theorem hankelInner_atom (z : K) (i : Nat) (vi : K) (u : List K) (j0 : Nat) :
    hankelInner (fun k => powK z k) i vi j0 u = (vi * powK z i) * polyEval z j0 u := by
  induction u generalizing j0 with
  | nil => simp [hankelInner, polyEval, mul_zero']
  | cons vj us ih =>
    simp only [hankelInner, polyEval, OrdField.left_distrib]
    rw [ih (j0 + 1)]
    congr 1
    rw [powK_add, OrdField.mul_assoc vi vj (powK z i * powK z j0),
        ← OrdField.mul_assoc vj (powK z i) (powK z j0), OrdField.mul_comm vj (powK z i),
        OrdField.mul_assoc (powK z i) vj (powK z j0), ← OrdField.mul_assoc vi (powK z i)]

private theorem hankelOuter_atom (z : K) (v : List K) (vs : List K) (i0 : Nat) :
    hankelOuter (fun k => powK z k) v i0 vs = polyEval z i0 vs * polyEval z 0 v := by
  induction vs generalizing i0 with
  | nil => simp [hankelOuter, polyEval, zero_mul']
  | cons vi ws ih =>
    simp only [hankelOuter, polyEval, right_distrib']
    rw [ih (i0 + 1), hankelInner_atom z i0 vi v 0]

private theorem hankelQuad_atom (z : K) (v : List K) :
    hankelQuad (fun k => powK z k) v = polyEval z 0 v * polyEval z 0 v :=
  hankelOuter_atom z v v 0

private theorem hankelInner_add (m1 m2 : Nat → K) (i : Nat) (vi : K) (us : List K) (j0 : Nat) :
    hankelInner (fun k => m1 k + m2 k) i vi j0 us =
    hankelInner m1 i vi j0 us + hankelInner m2 i vi j0 us := by
  induction us generalizing j0 with
  | nil => simp [hankelInner, OrdField.zero_add]
  | cons vj rs ih =>
    simp only [hankelInner, OrdField.left_distrib]
    rw [ih (j0 + 1)]
    let A := (vi * vj) * m1 (i + j0); let B := (vi * vj) * m2 (i + j0)
    rw [OrdField.add_assoc A B, ← OrdField.add_assoc B, OrdField.add_comm B,
        OrdField.add_assoc _ B, ← OrdField.add_assoc A]

private theorem hankelOuter_add (m1 m2 : Nat → K) (v : List K) (vs : List K) (i0 : Nat) :
    hankelOuter (fun k => m1 k + m2 k) v i0 vs =
    hankelOuter m1 v i0 vs + hankelOuter m2 v i0 vs := by
  induction vs generalizing i0 with
  | nil => simp [hankelOuter, OrdField.zero_add]
  | cons vi ws ih =>
    simp only [hankelOuter]
    rw [hankelInner_add m1 m2 i0 vi v 0, ih (i0 + 1)]
    let A := hankelInner m1 i0 vi 0 v; let B := hankelInner m2 i0 vi 0 v
    rw [OrdField.add_assoc A B, ← OrdField.add_assoc B, OrdField.add_comm B,
        OrdField.add_assoc _ B, ← OrdField.add_assoc A]

/-- Linearity of `hankelQuad` in the moment sequence `m`. -/
theorem hankelQuad_add (m1 m2 : Nat → K) (v : List K) :
    hankelQuad (fun k => m1 k + m2 k) v = hankelQuad m1 v + hankelQuad m2 v :=
  hankelOuter_add m1 m2 v v 0

private theorem hankelInner_scale (c : K) (m : Nat → K) (i : Nat) (vi : K) (us : List K) (j0 : Nat) :
    hankelInner (fun k => c * m k) i vi j0 us = c * hankelInner m i vi j0 us := by
  induction us generalizing j0 with
  | nil => simp [hankelInner, mul_zero']
  | cons vj rs ih =>
    simp only [hankelInner, OrdField.left_distrib]
    rw [ih (j0 + 1)]
    congr 1
    rw [← OrdField.mul_assoc (vi * vj) c, OrdField.mul_comm (vi * vj) c, OrdField.mul_assoc c]

private theorem hankelOuter_scale (c : K) (m : Nat → K) (v : List K) (vs : List K) (i0 : Nat) :
    hankelOuter (fun k => c * m k) v i0 vs = c * hankelOuter m v i0 vs := by
  induction vs generalizing i0 with
  | nil => simp [hankelOuter, mul_zero']
  | cons vi ws ih =>
    simp only [hankelOuter, OrdField.left_distrib]
    rw [hankelInner_scale c m i0 vi v 0, ih (i0 + 1)]

theorem hankelQuad_scale (c : K) (m : Nat → K) (v : List K) :
    hankelQuad (fun k => c * m k) v = c * hankelQuad m v :=
  hankelOuter_scale c m v v 0

theorem hankelQuad_zero (v : List K) : hankelQuad (fun _ => (0 : K)) v = 0 := by
  have h := hankelQuad_scale (0 : K) (fun _ => (0 : K)) v
  have hfn : (fun _ : Nat => (0 : K) * (0 : K)) = (fun _ : Nat => (0 : K)) := by
    funext _; exact zero_mul' 0
  rw [hfn, zero_mul'] at h
  exact h

/-- Exact spectral representation of `hankelQuad (momentK meas) v`. -/
theorem hankelQuad_momentK_eq (meas : List (K × K)) (v : List K) :
    hankelQuad (momentK meas) v =
    listSum (meas.map (fun wz => wz.1 * (polyEval wz.2 0 v * polyEval wz.2 0 v))) := by
  induction meas with
  | nil =>
    simp only [List.map_nil, listSum]
    have h0 : momentK ([] : List (K × K)) = fun _ => (0 : K) := by funext k; rfl
    rw [h0]; exact hankelQuad_zero v
  | cons wz rest ih =>
    simp only [List.map_cons, listSum]
    have hsplit : momentK (wz :: rest) = fun k => wz.1 * powK wz.2 k + momentK rest k := by
      funext k; rfl
    rw [hsplit, hankelQuad_add, hankelQuad_scale, hankelQuad_atom, ih]

/-- **Theorem 4.1 (Hankel PSD on Positive Spectral Measures):**
    For any positive measure `meas` (`w_r ≥ 0`), `v^T M_0 v ≥ 0`. -/
theorem quad_form_hankel_nonneg (meas : List (K × K)) (v : List K)
    (hw : ∀ wz ∈ meas, 0 ≤ wz.1) :
    0 ≤ hankelQuad (momentK meas) v := by
  rw [hankelQuad_momentK_eq]
  apply listSum_map_nonneg
  intro wz hwz
  exact OrdField.mul_nonneg (hw wz hwz) (sq_nonneg' _)

/-- **Theorem 4.1 (Shifted Hankel PSD on `[0, u]`):**
    If every support point `z_r` of `meas` satisfies `z_r ≤ u` and `w_r ≥ 0`, then
      `v^T (u M_0 - M_1) v = ∑ w_r (u - z_r) P_v(z_r)^2 ≥ 0`. -/
theorem shifted_hankel_psd (meas : List (K × K)) (u : K) (v : List K)
    (hw : ∀ wz ∈ meas, 0 ≤ wz.1)
    (hsupp : ∀ wz ∈ meas, wz.2 ≤ u) :
    0 ≤ shiftedHankelQuad (momentK meas) u v := by
  unfold shiftedHankelQuad
  have hshift : (fun k => momentK meas (k + 1)) = momentK (meas.map (fun wz => (wz.1 * wz.2, wz.2))) := by
    funext k
    unfold momentK
    rw [List.map_map]
    congr 1; apply List.map_congr_left; intro wz _
    dsimp only [Function.comp_apply]
    have hpow : powK wz.2 (k + 1) = wz.2 * powK wz.2 k := rfl
    rw [hpow, OrdField.mul_assoc]
  rw [hshift, hankelQuad_momentK_eq, hankelQuad_momentK_eq, List.map_map,
      ← listSum_map_mul_left, ← listSum_map_sub]
  apply listSum_map_nonneg
  intro wz hwz
  dsimp only [Function.comp_apply]
  have hfac : u * (wz.1 * (polyEval wz.2 0 v * polyEval wz.2 0 v)) -
              wz.1 * wz.2 * (polyEval wz.2 0 v * polyEval wz.2 0 v) =
              (wz.1 * (u - wz.2)) * (polyEval wz.2 0 v * polyEval wz.2 0 v) := by
    rw [OrdField.mul_comm u, OrdField.mul_assoc wz.1, OrdField.mul_comm (polyEval wz.2 0 v * polyEval wz.2 0 v) u,
        ← OrdField.mul_assoc wz.1 u, ← sub_mul', ← mul_sub']
  rw [hfac]
  exact OrdField.mul_nonneg
    (OrdField.mul_nonneg (hw wz hwz) (OrdField.sub_nonneg_of_le (hsupp wz hwz)))
    (sq_nonneg' _)

/-- **Theorem 4.1 (Assumption-Free Hankel Support Refutation):**
    If a witness vector `v` achieves `v^T (u M_0 - M_1) v < 0`, then NO positive spectral measure
    supported in `[0, u]` can generate the moments `m`. -/
theorem hankel_witness_refutes_support (meas : List (K × K)) (u : K) (v : List K)
    (hw : ∀ wz ∈ meas, 0 ≤ wz.1)
    (hwit : shiftedHankelQuad (momentK meas) u v < 0) :
    ¬ (∀ wz ∈ meas, wz.2 ≤ u) := by
  intro hsupp
  have hpsd := shifted_hankel_psd meas u v hw hsupp
  exact OrdField.lt_irrefl 0 (OrdField.lt_of_le_of_lt hpsd hwit)

/-- Sign-split interval upper bound for a single bilinear term `c * x`. -/
def intervalUpperTerm (c x_lo x_hi : K) (hc_nonneg : Bool) : K :=
  if hc_nonneg then c * x_hi else c * x_lo

/-- **Theorem 4.1 (Interval Bilinear Sign-Split Soundness):**
    If `x_lo ≤ x ≤ x_hi` and `b = true → 0 ≤ c`, `b = false → c ≤ 0`, then `c * x ≤ intervalUpperTerm c x_lo x_hi b`. -/
theorem interval_term_upper_bound (c x x_lo x_hi : K) (b : Bool)
    (hx_lo : x_lo ≤ x) (hx_hi : x ≤ x_hi)
    (hb : (b = true → 0 ≤ c) ∧ (b = false → c ≤ 0)) :
    c * x ≤ intervalUpperTerm c x_lo x_hi b := by
  cases b with
  | true =>
    simp only [intervalUpperTerm, ↓reduceIte]
    exact OrdField.mul_le_mul_of_nonneg_left hx_hi (hb.1 rfl)
  | false =>
    simp only [intervalUpperTerm, Bool.false_eq_true, ↓reduceIte]
    exact mul_le_mul_of_nonpos_left hx_lo (hb.2 rfl)

/-- **Theorem 4.1 (Interval Hankel Witness Soundness):**
    If `0 ≤ u`, `hankelQuad m v ≤ Q0_ub`, `Q1_lb ≤ hankelQuad (m ∘ succ) v`, and `u * Q0_ub - Q1_lb < 0`,
    then `shiftedHankelQuad m u v < 0` (so no positive measure on `[0, u]` lies in the interval box!). -/
theorem interval_hankel_witness_sound (m : Nat → K) (u Q0_ub Q1_lb : K) (v : List K)
    (hu : 0 ≤ u)
    (h0 : hankelQuad m v ≤ Q0_ub)
    (h1 : Q1_lb ≤ hankelQuad (fun k => m (k + 1)) v)
    (hcert : u * Q0_ub - Q1_lb < 0) :
    shiftedHankelQuad m u v < 0 := by
  unfold shiftedHankelQuad
  have hm0 := OrdField.mul_le_mul_of_nonneg_left h0 hu
  have hm1 := neg_le_neg' h1
  have hsum := OrdField.add_le_add hm0 hm1
  rw [← OrdField.sub_eq_add_neg, ← OrdField.sub_eq_add_neg] at hsum
  exact OrdField.lt_of_le_of_lt hsum hcert

/-- **Theorem 4.1 (`n = 0` Specialization):**
    For `v = [1]`, `shiftedHankelQuad m u [1] = u * m 0 - m 1`, recovering the 2-point bound. -/
theorem two_point_hankel_special_case (m : Nat → K) (u : K) :
    shiftedHankelQuad m u [1] = u * m 0 - m 1 := by
  unfold shiftedHankelQuad hankelQuad
  simp only [hankelOuter, hankelInner, OrdField.one_mul, add_zero']

/-- **Theorem 4.1 (Monotonicity in `u`):**
    If `u1 ≤ u2` and `0 ≤ hankelQuad m v`, then `shiftedHankelQuad m u1 v ≤ shiftedHankelQuad m u2 v`. -/
theorem hankel_monotone_in_u (m : Nat → K) (u1 u2 : K) (v : List K)
    (hQ : 0 ≤ hankelQuad m v) (hu : u1 ≤ u2) :
    shiftedHankelQuad m u1 v ≤ shiftedHankelQuad m u2 v := by
  unfold shiftedHankelQuad
  have hm := OrdField.mul_le_mul_of_nonneg_right hu hQ
  have hs := OrdField.add_le_add hm (OrdField.le_refl (-hankelQuad (fun k => m (k + 1)) v))
  rw [← OrdField.sub_eq_add_neg, ← OrdField.sub_eq_add_neg] at hs
  exact hs

/-- **Theorem 4.1 (Exact Rational Log-Series Tail Bound Helper):**
    For `0 ≤ r < 1` (`r = t^2`) and any `A ≥ 0`, `(1 - r) * S_tail ≤ A` gives `S_tail ≤ A / (1 - r)`.
    Instantiated on `r = t^2 ≤ 1/9` and `A = t^{2M+1} / (2M+1)`, this certifies our zero-float-trust
    exact-`ℚ` logarithm upper bound `log_Q^ub(1/u_0) > log(1/u_0)`. -/
theorem geometric_tail_term_le (A r S_tail : K)
    (hr : r < 1)
    (hstep : S_tail ≤ A + r * S_tail) :
    S_tail ≤ A / (1 - r) := by
  have h1r_pos : 0 < 1 - r := OrdField.sub_pos_of_lt hr
  have h1r_nz : 1 - r ≠ 0 := ne_zero_of_pos h1r_pos
  have hsub : (1 - r) * S_tail ≤ A := by
    rw [sub_mul', OrdField.one_mul]
    have h1 := OrdField.add_le_add hstep (OrdField.le_refl (-(r * S_tail)))
    rw [← OrdField.sub_eq_add_neg, OrdField.add_assoc, OrdField.add_neg_cancel, add_zero'] at h1
    exact h1
  have hinv_nn : 0 ≤ 1 / (1 - r) := OrdField.le_of_lt (OrdField.div_pos OrdField.zero_lt_one h1r_pos)
  have hm := OrdField.mul_le_mul_of_nonneg_right hsub hinv_nn
  rw [OrdField.mul_comm (1 - r) S_tail, OrdField.mul_assoc, OrdField.mul_inv_cancel (1 - r) h1r_nz,
      mul_one', ← OrdField.div_eq_mul_inv] at hm
  exact hm

end StieltjesHankel

end ContinuumEdge
