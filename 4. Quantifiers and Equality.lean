universe u
--variables (α : Type u) (p q : α → Prop) (r : α → α → Prop)

--example : (∀ x : α, p x ∧ q x) → ∀ y : α, p y := λ h x, (h x).left

--variable refl_r : ∀ x, r x x
--variable symm_r : ∀ {x y}, r x y → r y x 
--variable trans_r : ∀ {x y z}, r x y → r y z → r x z

--variables a b c : α
--variables (hab : r a b) (hbc : r b c)

--example (a b c d : α) (hab : r a b) (hcb : r c b) (hcd : r c d) :
 -- r a d := trans_r hab (trans_r (symm_r hcb) hcd)

--#check eq.refl    -- ∀ (a : ?M_1), a = a
--#check eq.symm    -- ?M_2 = ?M_3 → ?M_3 = ?M_2
--#check eq.trans

example (α : Type u) (a b : α) (p : α → Prop)
  (h1 : a = b) (h2 : p a) : p b := h1 ▸ h2

--variables f g : α → ℕ
--variable h₁ : a = b
--variable h₂ : f = g

--example : f a = f b := congr_arg f h₁  
--example : f a = g a := congr_fun h₂ a
--example : f a = g b := congr h₂ h₁

example (x y : ℕ) :
  (x + y) * (x + y) = x * x + 2 * x * y + y * y := 
calc
    (x + y) * (x + y) = x * (x + y) + y * (x + y) : by rw add_mul
    ... = x * x + x * y + y * (x + y) : by rw mul_add
    ... = (x * x + x * y) + (y * x + y * y) : by rw mul_add
    ... = x * x + x * y + y * x + y * y : by rw ←add_assoc
    ... = x * x + (x * y + y * x) + y * y : by rw ←add_assoc
    ... = x * x + (1 * (x * y) + y * x) + y * y : by rw one_mul
    ... = x * x + (1 * (x * y) + 1 * (y * x)) + y * y : by rw one_mul (y * x)
    ... = x * x + (1 * (x * y) + 1 * (x * y)) + y * y : by rw mul_comm y x
    ... = x * x + (1 + 1) * (x * y) + y * y : by rw ←add_mul
    ... = x * x + 2 * (x * y) + y * y : rfl
    ... = x * x + 2 * x * y + y * y : by rw mul_assoc

--variable h1 : a = b
--variable h2 : b = c + 1
--variable h3 : c = d
--variable h4 : e = 1 + d

--include h1 h2 h3 h4
--theorem T : a = e := by simp [h1, h2, h3, h4]

theorem T2 (a b c d : ℕ)
  (h1 : a = b) (h2 : b ≤ c) (h3 : c + 1 < d) : a < d :=
calc 
    a = b : h1
    ... ≤ c : h2
    ... < c + 1 : nat.lt_succ_self c
    ... < d : h3

open nat

example : ∃ x : ℕ, x > 0 := ⟨1, zero_lt_succ 0⟩

example (x : ℕ) (h : x > 0) : ∃ y, y < x := ⟨0, h⟩ 

example (x y z : ℕ) (hxy : x < y) (hyz : y < z) :
  ∃ w, x < w ∧ w < z := ⟨y, hxy, hyz⟩         

--example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x := 
--exists.elim h (λ w hw, ⟨w, hw.right, hw.left⟩)

def is_even (a : nat) := ∃ b, a = 2 * b

theorem even_plus_even {a b : nat} (h1 : is_even a) (h2 : is_even b) : is_even (a + b) := 
exists.elim h1(λ a0 ha, exists.elim h2(λ b0 hb, ⟨a0+b0, by rw [ha, hb, ←mul_add]⟩))

open classical

variables (α : Type) (p q : α → Prop)

example (h : ¬ ∀ x, ¬ p x) : ∃ x, p x := by_contradiction 
(λ h0, (λ (h1 : (∀ x, ¬ p x)), h h1) (λ x hpx, h0 ⟨x, hpx⟩))

open classical

variable a : α
variable r : Prop

example : (∃ x : α, r) → r := λ h, exists.elim h (λ x hr, hr)
example : r → (∃ x : α, r) := λ hr, ⟨a, hr⟩
example : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r := iff.intro 
(λ h, exists.elim h (λ x hpr, ⟨⟨x, hpr.left⟩,hpr.right⟩))
(λ h, exists.elim h.left (λ x hpx, ⟨x, hpx, h.right⟩))
example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) := iff.intro
(λ h, exists.elim h (λ x hpq, hpq.elim (λ hpx, or.inl ⟨x, hpx⟩) (λ hqx, or.inr ⟨x, hqx⟩)))
(λ h, or.elim h (λ hpx, exists.elim hpx (λ x hpx, ⟨x, or.intro_left (q x) hpx⟩))
(λ hqx, exists.elim hqx (λ x hqx, ⟨x, or.intro_right (p x) hqx⟩)))

example : (∀ x, p x) ↔ ¬ (∃ x, ¬ p x) := iff.intro 
(λ hpx hnpx, exists.elim hnpx (λ x hnpx, hnpx (hpx x)))
(λ hnnpx x, by_contradiction (λ hnpx, hnnpx ⟨x, hnpx⟩))
example : (∃ x, p x) ↔ ¬ (∀ x, ¬ p x) := iff.intro
(λ hpx h, exists.elim hpx (λ x hpx, (h x) hpx))
(λ h, by_contradiction (λ hnpx, (λ (h0 : ∀ x, ¬ p x), h h0) 
(λ x, (em (p x)).elim (λ hpx, absurd (exists.intro x hpx) hnpx) id)))
example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) := iff.intro 
(λ h x hpx, h ⟨x, hpx⟩)
(λ h h0, exists.elim h0 (λ x hpx, h x hpx))
example : (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) := iff.intro 
(λ hnapx, by_contradiction (λ hnenpx, (λ (h : ∀ x, p x), hnapx h) 
(λ x, by_contradiction (λ hnpx, hnenpx ⟨x, hnpx⟩))))
(λ henpx hapx, exists.elim henpx (λ x hnpx, hnpx (hapx x)))
example : (∀ x, p x → r) ↔ (∃ x, p x) → r := iff.intro 
(λ hapxr hepx, exists.elim hepx (λ x hpx, hapxr x hpx))
(λ hexpxr x px, hexpxr ⟨x,px⟩)
example : (∃ x, p x → r) ↔ (∀ x, p x) → r := iff.intro 
(λ he ha, exists.elim he (λ x hr, hr (ha x)))
(λ h, (em (∀ x, p x)).elim (λ hpx, ⟨a, λ pa, h hpx⟩) (λ hnpx, by_contradiction 
(λ h0, absurd (λ x, by_contradiction (λ npx, h0 ⟨x, λ hpx, absurd hpx npx⟩)) hnpx)))
example : (∃ x, r → p x) ↔ (r → ∃ x, p x) := iff.intro
(λ h hr, exists.elim h (λ x hpx, ⟨x, hpx hr⟩))
(λ h, (em r).elim (λ hr, exists.elim (h hr) (λ x px, ⟨x, λ hr, px⟩))
(λ hnr, ⟨a, λ hr, absurd hr hnr⟩))

example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) := iff.intro
(λ h, ⟨(λ x, (h x).left), (λ x, (h x).right)⟩) 
(λ h x, ⟨h.left x, h.right x⟩)
example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) := λ hpq hp x, hpq x (hp x)
example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x := λ h, h.elim (λ h x, or.inl (h x)) 
(λ h x, or.inr (h x))

example : α → ((∀ x : α, r) ↔ r) := λ x, iff.intro (λ f, f x) (λ hr x, hr)
example : (∀ x, p x ∨ r) ↔ (∀ x, p x) ∨ r := iff.intro
(λ h, (em r).elim or.inr (λ hnr, or.inl (λ x, (h x).elim id (λ hr, absurd hr hnr))))
(λ h x, h.elim (λ h0, or.inl (h0 x)) or.inr)
example : (∀ x, r → p x) ↔ (r → ∀ x, p x) := iff.intro 
(λ h hr x, h x hr)
(λ h x hr, h hr x)

variables (men : Type) (barber : men)
variable  (shaves : men → men → Prop)

example (h : ∀ x : men, shaves barber x ↔ ¬ shaves x x) : false :=
(λ (hnp : ¬(shaves barber barber)), hnp ((h barber).elim_right hnp)) 
(λ hp, (h barber).elim_left hp hp)

example (p : Prop) : ¬(p ↔ ¬p) := 
λ h, (λ (hnp : ¬p), hnp (h.elim_right hnp)) (λ hp, h.elim_left hp hp)

namespace hidden

def divides (m n : ℕ) : Prop := ∃ k, m * k = n

instance : has_dvd nat := ⟨divides⟩

def even (n : ℕ) : Prop := 2 ∣ n

section
  variables m n : ℕ

  --#check m ∣ n
  --#check m^n
  --#check even (m^n +3)
end

def prime (n : ℕ) : Prop := ∀ (m : ℕ), (m ∣ n) → (m = 1 ∨ m = n)

def infinitely_many_primes : Prop := ∀ (n : ℕ), ∃ (p : ℕ), (prime p) → n < p

def Fermat_prime (n : ℕ) : Prop := ∃ (k : ℕ), n = 2 ^ k + 1

def infinitely_many_Fermat_primes : Prop := ∀ (n : ℕ), ∃ (p : ℕ), (Fermat_prime p) → n < p

def goldbach_conjecture : Prop := 
∀ (n : ℕ), n > 2 → even n → ∃ (p q : ℕ), prime p → prime q → n = p + q

def Goldbach's_weak_conjecture : Prop := 
∀ (n : ℕ), n > 5 → (¬ even n) → ∃ (p q r : ℕ), prime p → prime q → prime r → n = p + q + r

def Fermat's_last_theorem : Prop := 
∀ (n : ℕ), n > 2 → ¬ (∃ (a b c : ℕ), a ≠ 0 → b ≠ 0 → c ≠ 0 → a ^ n + b ^ n = c ^ n)

end hidden

variables (real : Type) [ordered_ring real]
variables (log exp : real → real)
variable  log_exp_eq : ∀ x, log (exp x) = x
variable  exp_log_eq : ∀ {x}, x > 0 → exp (log x) = x
variable  exp_pos    : ∀ x, exp x > 0
variable  exp_add    : ∀ x y, exp (x + y) = exp x * exp y

-- this ensures the assumptions are available in tactic proofs
include log_exp_eq exp_log_eq exp_pos exp_add

example (x y z : real) :
  exp (x + y + z) = exp x * exp y * exp z :=
by rw [exp_add, exp_add]

example (y : real) (h : y > 0)  : exp (log y) = y := exp_log_eq h

theorem log_mul {x y : real} (hx : x > 0) (hy : y > 0) :
  log (x * y) = log x + log y :=
calc 
    log (x * y) = log (exp (log x) * exp (log y)) : by rw [exp_log_eq hx, exp_log_eq hy]
    ... = log (exp (log x + log y)) : by rw exp_add (log x) (log y)
    ... = log x + log y : by rw log_exp_eq

--#check sub_self

example (x : ℤ) : x * 0 = 0 := calc
    x * 0 = x * (x - x) : by rw sub_self x
    ... = x * x - x * x : mul_sub x x x
    ... = 0 : sub_self (x * x)