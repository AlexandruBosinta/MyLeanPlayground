definition cong_mod_n (n a b : ℤ) := ∃ k : ℤ, n * k = a - b

theorem cong_mod_n_equiv : ∀ (n : ℕ), equivalence (cong_mod_n n) := λ n,
⟨λ a, ⟨0, by rw [mul_zero, sub_eq_add_neg, add_neg_self]⟩, λ x y h, exists.elim h 
(λ a cong, ⟨-a, by rw [←neg_mul_eq_mul_neg, cong, neg_sub]⟩), λ x y z hxy hyz, exists.elim hxy
(λ k congxy, exists.elim hyz (λ t congyz, ⟨k+t, by rw [mul_add, congxy, congyz, 
sub_eq_add_neg y z, ←add_assoc, sub_add_cancel, sub_eq_add_neg]⟩))⟩