import data.real.basic
import tactic.ring

structure complex : Type := (re : ℝ) (im : ℝ)

notation `ℂ` := complex

def z : ℂ := ⟨5,6⟩ 

namespace complex

theorem ext (z w : ℂ) : z.re = w.re ∧ z.im = w.im → z = w := begin
    cases z,
    cases w, 
    intros,
    simp * at *
end

instance : has_coe ℝ ℂ := ⟨λ x, {re := x, im := 0}⟩ 

def I : ℂ := ⟨0, 1⟩

def add : ℂ → ℂ → ℂ := λ z w, {re := z.re + w.re, im := z.im + w.im}

instance : has_add ℂ := ⟨complex.add⟩

@[simp] theorem add_re : ∀ z w : ℂ, (z + w).re = z.re + w.re := λ z w, rfl
@[simp] theorem add_im : ∀ z w : ℂ, (z + w).im = z.im + w.im := λ z w, rfl

theorem add_comm : ∀ z w : ℂ, z + w = w + z := begin
    intros,
    apply ext, 
    split; simp
end

theorem add_assoc : ∀ a b c : ℂ, a + (b + c) = (a + b) + c := begin
    intros, 
    apply ext, 
    split; simp
end

def neg : ℂ → ℂ := λ z, ⟨-z.re,z.im⟩

instance : has_neg ℂ := ⟨complex.neg⟩

@[simp] theorem neg_re (z : ℂ) : (-z).re = -z.re := _
@[simp] theorem neg_im (z : ℂ) : (-z).im = -z.im := rfl




end complex