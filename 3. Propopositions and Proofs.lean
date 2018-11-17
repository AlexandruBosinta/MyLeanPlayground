
variables p q r s : Prop
theorem t1 : p → q → p := λ hp, λ hq, hp

theorem t2 : ∀ (p q : Prop), p → q → p := λ (p q), λ hp, λ hq, hp

theorem t3 (h₁ : q → r) (h₂ : p → q) : p → r := λ hp, h₁ (h₂ hp)

example (h : p ∧ q) : p := and.elim_left h

variables  (hp : p) (hq : q)

#check (⟨hp, hq⟩ : p ∧ q)

example (h : p ∧ q) : q ∧ p ∧ q := ⟨h.right, h.left, h.right⟩

example (hp : p) : p ∨ q := or.intro_left q hp

example (hq : q) : p ∨ q := or.intro_right p hq

example (h : p ∨ q) : q ∨ p := or.elim h (λ hp, or.inr hp) (λ hq, or.inl hq)

example (hnp : ¬p) (hq : q) (hqp : q → p) : r := absurd (hqp hq) hnp

theorem and_swap : p ∧ q ↔ q ∧ p := iff.intro 
(λ hpq, and.intro (and.right hpq) (and.left hpq)) 
(λ hqp, and.intro (and.right hqp) (and.left hqp))

example (h : p ∧ q) : q ∧ p :=
have hp : p, from and.left h,
have hq : q, from and.right h,
show q ∧ p, from and.intro hq hp

example (h : p ∧ q) : q ∧ p := 
(λ (hp : p), (λ (hq : q), and.intro hq hp) (and.right h)) (and.left h)

open classical

example (h : ¬¬p) : p :=
by_cases
  (assume h1 : p, h1)
  (assume h1 : ¬p, absurd h1 h)

example (h : ¬¬p) : p :=
by_cases (λ hp : p, hp) (λ hnp : ¬p, absurd hnp h)

example (h : ¬¬p) : p :=
by_contradiction
  (assume h1 : ¬p,
    show false, from h h1)

example (h : ¬¬p) : p :=
by_contradiction (λ hnp : ¬p, absurd hnp h)

example (h : ¬(p ∧ q)) : ¬p ∨ ¬q := 
or.elim (em p)
(λ hp : p, or.inr (λ hq : q, h ⟨hp, hq⟩)) 
(λ hnp : ¬p, or.inl hnp)

example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := 
iff.intro 
(λ h, or.elim h.right (λ hq, or.inl ⟨h.left, hq⟩) (λ hr, or.inr ⟨h.left, hr⟩))
(λ h, or.elim h (λ h0, ⟨h0.left, or.inl h0.right⟩) (λ h0, ⟨h0.left, or.inr h0.right⟩))

example : ¬(p ∧ ¬q) → (p → q) := λ h hp, 
or.elim (em q) (λ hq, hq) (λ hnq, absurd (and.intro hp hnq) h)


-- commutativity of ∧ and ∨
example : p ∧ q ↔ q ∧ p := 
iff.intro (λ h, ⟨h.right, h.left⟩) (λ h, ⟨h.right, h.left⟩)
example : p ∨ q ↔ q ∨ p := 
iff.intro (λ h, or.elim h or.inr or.inl) 
(λ h, or.elim h or.inr or.inl)

-- associativity of ∧ and ∨
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) := 
iff.intro (λ h, ⟨h.left.left, ⟨h.left.right, h.right⟩⟩)
(λ h, ⟨⟨h.left, h.right.left⟩, h.right.right⟩)
example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) := 
iff.intro (λ h, or.elim h 
(λ h, or.elim h or.inl (λ hq, or.inr (or.inl hq))) 
(λ h, or.inr (or.inr h)))
(λ h, or.elim h 
(λ hp, or.inl (or.inl hp)) 
(λ h, or.elim h (λ hq, or.inl (or.inr hq)) or.inr))

-- distributivity
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := iff.intro 
(λ h, or.elim h.right (λ hq, or.inl ⟨h.left, hq⟩) (λ hr, or.inr ⟨h.left, hr⟩))
(λ h, or.elim h (λ h0, ⟨h0.left, or.inl h0.right⟩) (λ h0, ⟨h0.left, or.inr h0.right⟩))
example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) := iff.intro 
(λ h, or.elim h (λ hp, ⟨or.intro_left q hp, or.intro_left r hp⟩) 
(λ h, ⟨or.intro_right p h.left, or.intro_right p h.right⟩))
(λ h, or.elim (em p) or.inl 
(λ hnp, or.elim h.left (λ hp, absurd hp hnp) 
(λ hq, or.elim h.right (λ hp, absurd hp hnp) (λ hr, or.inr ⟨hq, hr⟩))))

-- other properties
example : (p → (q → r)) ↔ (p ∧ q → r) := iff.intro (λ hpqr hpq, (hpqr hpq.left hpq.right)) 
(λ hpqr hp hq, hpqr ⟨hp, hq⟩)
example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) := iff.intro (λ h, 
⟨(λ hp, h (@or.intro_left p q hp)), (λ hq, h (@or.intro_right p q hq))⟩) 
(λ h hpq, or.elim hpq (λ hp, h.left hp) (λ hq, h.right hq))
example : ¬(p ∨ q) ↔ ¬p ∧ ¬q := iff.intro 
(λ h, ⟨(λ hp, h ((or.intro_left q) hp)), (λ hq, h ((or.intro_right p) hq))⟩)
(λ h hpq, hpq.elim h.left h.right)
example : ¬p ∨ ¬q → ¬(p ∧ q) := λ h hpq, or.elim h (λ hnp, absurd hpq.left hnp) 
(λ hnq, absurd hpq.right hnq)
example : ¬(p ∧ ¬p) := λ h, h.right h.left
example : p ∧ ¬q → ¬(p → q) := λ h hpq, h.right (hpq h.left)
example : ¬p → (p → q) := λ hnp hp, absurd hp hnp
example : (¬p ∨ q) → (p → q) := λ h hp, or.elim h (absurd hp) (λ hq, hq)
example : p ∨ false ↔ p := iff.intro (λ h, or.elim h (λ hp, hp) false.elim) 
(λ hp, or.intro_left false hp)
example : p ∧ false ↔ false := iff.intro (λ h, h.right.elim) false.elim
example : ¬(p ↔ ¬p) := λ h, (λ (hnp : ¬p), hnp (h.elim_right hnp)) (λ hp, h.elim_left hp hp)
example : (p → q) → (¬q → ¬p) := λ hpq hnq hp, hnq (hpq hp)

-- these require classical reasoning
example : (p → r ∨ s) → ((p → r) ∨ (p → s)) := λ h, (em p).elim 
(λ hp, (h hp).elim (λ hr, or.inl (λ hp, hr)) (λ hs, or.inr (λ hp, hs))) 
(λ hnp, or.inl (λ hp, absurd hp hnp))
example : ¬(p ∧ q) → ¬p ∨ ¬q := λ h, (em p).elim (λ hp, (em q).elim 
(λ hq, absurd (and.intro hp hq) h) or.inr) or.inl
example : ¬(p → q) → p ∧ ¬q := λ h, and.intro ((em p).elim id (λ hnp, absurd 
(λ hp : p, false.elim (hnp hp)) h)) ((em q).elim (λ hq, absurd (λ hp : p, hq) h) id)
example : (p → q) → (¬p ∨ q) := λ h, or.elim (em p) (λ hp, or.inr (h hp)) or.inl
example : (¬q → ¬p) → (p → q) := λ h hp, by_contradiction (λ hnq, absurd hp (h hnq))
example : p ∨ ¬p := em p
example : ((p → q) → p) → p := λ h, or.elim (em p) id
(λ hnp, by_contradiction (λ hnp, hnp (h (λ hp, absurd hp hnp))))