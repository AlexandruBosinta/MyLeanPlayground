--import tactic.finish

namespace Three 

open classical

variables p q r s : Prop

-- commutativity of ∧ and ∨
example : p ∧ q ↔ q ∧ p := begin
  split,
  intro hpq, 
    split, 
      exact hpq.right,
    exact hpq.left,
  intro hqp, 
    split, 
      exact hqp.right,
    exact hqp.left,
end
example : p ∨ q ↔ q ∨ p := begin
  split,
    intro hpq, 
    cases hpq with hp hq,
      right, exact hp,
    left, exact hq,
  intro hqp, 
    cases hqp with hq hp,
      right, exact hq,
    left, exact hp
end

example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) := begin
  split,
    intro h,
    split, 
      exact h.left.left,
    split, 
      exact h.left.right,
    exact h.right,
  intro h,
  split, 
    split, 
      exact h.left,
    exact h.right.left,
  exact h.right.right
end
example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) := begin
  split,
    intro h,
    cases h with hpq hr,
      cases hpq with hp hq,
        left, exact hp,
      right, left, exact hq,
    right, right, exact hr,
  intro h,
  cases h with hp hqr,
    left, left, exact hp,
  cases hqr with hq hr,
    left, right, exact hq,
  right, exact hr
end

-- distributivity
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := begin
  split,
    intro h,
    cases h with hp hqr,
    cases hqr with hq hr,
      left,
      split, 
        exact hp,
      exact hq,
    right,
    split,
      exact hp,
    exact hr,
  intro h,
  cases h with hpq hpr,
    cases hpq with hp hq,
    split,
      exact hp,
    left, exact hq,
  cases hpr with hp hr,
  split,
    exact hp,
  right, exact hr
end
example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) := begin
  split,
    intro h,
    cases h with hp hqr,
      split; {left, exact hp},
    cases hqr with hq hr,
    split; right, exact hq, exact hr,
  intro h,
  cases h with hpq hpr,
  cases hpq with hp hq, 
    left, exact hp,
  cases hpr with hp hr,
    left, exact hp,
  right, split, exact hq, exact hr
end

-- other properties
example : (p → (q → r)) ↔ (p ∧ q → r) := begin
  split, 
    intros, 
      apply a, 
        exact a_1.left,
      exact a_1.right,
  intros,
    apply a,
    split,
      exact a_1,
    exact a_2
end
example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) := begin
  split,
    intros, 
    split,
      intros, 
      apply a,
      exact or.intro_left q a_1,
    intros,
    apply a,
      exact or.intro_right p a_1,
  intros,
  cases a, cases a_1,
  exact a_left a_1,
  exact a_right a_1
end
example : ¬(p ∨ q) ↔ ¬p ∧ ¬q := begin
  split,
    intros,
    split,
      intro hp, 
      exact a (or.intro_left q hp),
    intro hq, 
    exact a (or.intro_right p hq),
  intros, 
  intro hpq,
  cases hpq,
    exact a.left hpq,
  exact a.right hpq
end
example : ¬p ∨ ¬q → ¬(p ∧ q) := begin
  intros,
  intro h,
  cases a,
    exact a h.left,
  exact a h.right,
end
example : ¬(p ∧ ¬p) := begin
  intro h,
  exact h.right h.left
end
example : p ∧ ¬q → ¬(p → q) := begin
  intros a h, 
  exact a.right (h a.left)
end
example : ¬p → (p → q) := begin
  intros, 
  exact absurd a_1 a
end
example : (¬p ∨ q) → (p → q) := begin
  intros,
  cases a, 
    exact absurd a_1 a,
  exact a
end
example : p ∨ false ↔ p := begin
  split,
    intros,
    cases a,
      exact a,
    exact false.elim a,
  intros,
  left, exact a
end
example : p ∧ false ↔ false := begin
  split,
    intros,
    exact a.right,
  intros, 
  exact false.elim a
end
example : ¬(p ↔ ¬p) := begin
  intro h, 
  cases h, 
  have hnp : ¬p, from begin
    intro hp,
    exact (h_mp hp) hp,
  end,
  exact hnp (h_mpr hnp)
end
example : (p → q) → (¬q → ¬p) := begin
  intros, intro hp,
  exact a_1 (a hp)
end

-- these require classical reasoning
example : (p → r ∨ s) → ((p → r) ∨ (p → s)) := begin
  intros,
  cases (em p),
    cases a h,
      left, intro h, exact h_1,
    right, intro h, exact h_1,
  left,
  intros,
  exact absurd a_1 h
end
example : ¬(p ∧ q) → ¬p ∨ ¬q := begin
  intros, 
  cases (em p); cases (em q),
        exact absurd (and.intro h h_1) a,
      right, exact h_1,
    left, exact h,
  left, exact h
end
example : ¬(p → q) → p ∧ ¬q := begin
  intros,
  cases (em p); cases (em q),
        have hpq : p → q, from begin intros, exact h_1 end,
        exact absurd hpq a,
      split, exact h, exact h_1,
    have hpq : p → q, from begin intros, exact h_1 end,
    exact absurd hpq a,
  have hpq : p → q, from begin intros, exact absurd a_1 h end,
  exact absurd hpq a
end
example : (p → q) → (¬p ∨ q) := begin
  intros,
  cases (em p),
    right, exact a h,
  left, exact h,
end
example : (¬q → ¬p) → (p → q) := begin
  intros,
  cases (em q), 
    exact h,
  exact absurd a_1 (a h)
end
example : p ∨ ¬p := begin
  cases (em p), left, assumption,
  right, assumption
end

example : (((p → q) → p) → p) := begin
  intros,
  apply classical.by_contradiction, 
  intros, 
  apply a_1, apply a,
  intros,
  exact absurd a_2 a_1
end


end Three

namespace Four

variables (α : Type) (p q : α → Prop)

example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) := begin
  split,
    intros,
    split,
      intros,
      exact (a x).left,
    intros,
    exact (a x).right,
  intros,
  split,
    exact a.left x,
  exact a.right x
end
example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) := begin
  intros,
  exact (a x) (a_1 x)
end
example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x := begin
  intros,
  cases a,
    left, exact a x,
  right, exact a x
end

variable r : Prop

example : α → ((∀ x : α, r) ↔ r) := begin
  intros,
  split, 
    intros,
    exact a_1 a,
  intros,
  exact a_1
end

open classical

example : (∀ x, p x ∨ r) ↔ (∀ x, p x) ∨ r := begin
  split,
    intros,
    cases (em r),
    right, exact h,
    left, intros, 
    cases a x, 
    exact h_1,
    exact absurd h_1 h,
  intros,
  cases a,
  left, exact a x,
  right,
  exact a
end

example : (∀ x, r → p x) ↔ (r → ∀ x, p x) := begin
  split,
    intros,
    exact (a x) a_1,
  intros,
  exact (a a_1) x
end

variables (men : Type) (barber : men)
variable  (shaves : men → men → Prop)

example (h : ∀ x : men, shaves barber x ↔ ¬ shaves x x) : false := begin
  have h0 : ∀ (p : Prop), ¬(p ↔ ¬p), from begin
    intros p h,
    cases h, 
    have hnp : ¬p, from begin
      intro hp,
      exact (h_mp hp) hp,
    end,
    exact hnp (h_mpr hnp)
  end,
  exact (h0 (shaves barber barber)) (h barber)
end

namespace hidden

def divides (m n : ℕ) : Prop := ∃ k, m * k = n

instance : has_dvd nat := ⟨divides⟩

def even (n : ℕ) : Prop := 2 ∣ n

def prime (n : ℕ) : Prop := ∀ (a b : ℕ), a * b = n → (a = 1 ∨ b = 1)

def infinitely_many_primes : Prop := ∀ (n : ℕ), ∃ (p : ℕ), (n < p) ∧ (prime p)

def Fermat_prime (n : ℕ) : Prop := (prime n) ∧ (∃ (k : ℕ), n = 2 ^ k + 1)

def infinitely_many_Fermat_primes : Prop := 
∀ (n : ℕ), ∃ (p : ℕ), (n < p) ∧ (Fermat_prime p)

def goldbach_conjecture : Prop := 
∀ (n : ℕ), (even n) → (n > 2) → (∃ (p q : ℕ), (prime p) → (prime q) → n = p + q)

def Goldbach's_weak_conjecture : Prop := 
∀ (n : ℕ), (¬ (even n)) → (n > 5) → (∃ (p q r : ℕ), 
(prime p) → (prime q) → (prime r) → n = p + q + r)

def Fermat's_last_theorem : Prop := 
∀ (n : ℕ), (n > 2) → (¬ (∃ (a b c : ℕ), a ^ n + b ^ n = c ^ n))

end hidden

end Four

open classical

variables (α : Type) (p q : α → Prop)
variable a : α
variable r : Prop


include a
example : (∃ x : α, r) → r := begin
  intro h,
  cases h,
    exact h_h
end
example : r → (∃ x : α, r) := begin
  intros,
  apply exists.intro,
    exact a, exact a_1
end
example : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r := begin
  split,
    intros,
    split,
      cases a_1, 
      apply exists.intro,
      exact a_1_h.left,
    cases a_1,
    exact a_1_h.right,
  intros,
  cases a_1.left,
  apply exists.intro,
  split,
    exact h,
  exact a_1.right
end
example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) := begin
  split,
    intros,
    cases a_1,
    cases a_1_h,
      left, 
      apply exists.intro,
      exact a_1_h,
    right,
    apply exists.intro,
    exact a_1_h,
  intros,
  cases a_1,
    cases a_1,
    apply exists.intro,
    left, exact a_1_h,
  cases a_1,
  apply exists.intro,
  right,
  exact a_1_h
end

example : (∀ x, p x) ↔ ¬ (∃ x, ¬ p x) := begin
  split,
    intros h1 h2,
    cases h2 with a h,
    exact h (h1 a),
  intros h x,
  apply by_contradiction,
  intros,
  have h0 : ∃ (x : α), ¬p x, 
    apply exists.intro,
    exact a_1,
  exact h h0
end

example : (∃ x, p x) ↔ ¬ (∀ x, ¬ p x) := begin
  split,
    intros h h1,
    cases h with x h,
    exact (h1 x) h,
  intros,
  apply by_contradiction,
  intros,
  have h2 : ∀ (x : α), ¬p x, 
    intros x hpx,
    exact a_2 (begin apply exists.intro, exact hpx end),
  exact a_1 h2
end
example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) := begin
  split,
    intros h x hpx, 
    exact h (begin apply exists.intro, exact hpx end),
  intros h h0,
  cases h0,
  exact (h h0_w) h0_h
end
example : (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) := begin
  split,
    intros h, 
    apply by_contradiction,
    intros h1,
    have h2 : ∀ x, p x, 
      intro x,
      apply by_contradiction,
      intro hnp, 
      exact h1 (begin apply exists.intro, exact hnp end),
    exact h h2,
  intros h h0,
  cases h, 
  exact h_h (h0 h_w)
end

example : (∀ x, p x → r) ↔ (∃ x, p x) → r := begin
  split,
    intros, 
    cases a_2,
    exact (a_1 a_2_w) a_2_h,
  intros,
  apply a_1,
  apply exists.intro, 
  exact a_2
end
example : (∃ x, p x → r) ↔ (∀ x, p x) → r := begin
  split,
    intros,
    cases a_1,
    exact a_1_h (a_2 a_1_w),
  intros,
  cases (em (∀ (x : α), p x)),
    apply exists.intro,
      intro hp,
      exact a_1 h,
    exact a,
  apply by_contradiction,
  intro h1,
  have h2 : ∀ (x : α), p x, 
    intro x,
    apply by_contradiction,
    intro npx,
    exact h1 (begin fapply exists.intro,
    exact x,
    intro hpx,
    exact absurd hpx npx end),
  exact h h2
end
example : (∃ x, r → p x) ↔ (r → ∃ x, p x) := begin
  split,
    intros,
    cases a_1,
    apply exists.intro,
    exact a_1_h a_2,
  intros,
  cases (em r),
  cases a_1 h,
  apply exists.intro,
    intro h,
    exact h_1,
  apply exists.intro,
    intro hr,
    exact absurd hr h,
  exact a,
end

example (p q r : Prop) (hp : p) :
(p ∨ q ∨ r) ∧ (q ∨ p ∨ r) ∧ (q ∨ r ∨ p) :=
by {split, all_goals { try {split} }, 
repeat {{left, assumption} <|> right <|> assumption}}