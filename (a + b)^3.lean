import data.real.basic

variables (a b : ℝ)

include a b
example : (a + b) ^ 3 = a ^ 3 + 3 * (a ^ 2) * b + 3 * a * b ^ 2 + b ^ 3 := 
by calc
    (a + b) ^ 3 = (a + b) ^ (2 + 1) : rfl
    ... = (a + b) ^ 2 * (a + b) : by rw pow_succ'
    ... = (a + b) * (a + b) * (a + b) : by rw pow_two
    ... = ((a + b) * a + (a + b) * b) * (a + b) : by rw mul_add (a + b) a b
    ... = ((a * a + b * a) + (a * b + b * b)) * (a + b) : 
    by rw [add_mul a b a, add_mul a b b]
    ... = (a * a + b * a + a * b + b * b) * (a + b) : 
    by rw [add_assoc (a * a + b * a) (a * b) (b * b)]
    ... = (a ^ 2 + a * b + a * b + b ^ 2) * (a + b) : 
    by rw [mul_comm b a, pow_two, pow_two]
    ... = (a ^ 2 + 1 * a * b + 1 * a * b + b ^ 2) * (a + b) : by rw one_mul
    ... = (a ^ 2 + (1 * a * b + 1 * a * b) + b ^ 2) * (a + b) : 
    by rw add_assoc (a ^ 2) (1 * a * b) (1 * a * b)
    ... = (a ^ 2 + (1 * (a * b) + 1 * (a * b)) + b ^ 2) * (a + b) : 
    by rw mul_assoc
    ... = (a ^ 2 + (1 + 1) * (a * b) + b ^ 2) * (a + b) : by rw add_mul 1 1 (a * b)
    ... = (a ^ 2 + 2 * (a * b) + b ^ 2) * (a + b) : rfl
    ... = (a ^ 2 + 2 * a * b + b ^ 2) * (a + b) : by rw mul_assoc
    ... = (a ^ 2 + 2 * a * b + b ^ 2) * a + (a ^ 2 + 2 * a * b + b ^ 2) * b : 
    by rw mul_add    
    ... = (a ^ 2 + 2 * a * b) * a + b ^ 2 * a + 
    ((a ^ 2 + 2 * a * b) * b + b ^ 2 * b) : 
    by rw [add_mul (a ^ 2 + 2 * a * b) (b ^ 2) a, 
    add_mul (a ^ 2 + 2 * a * b) (b ^ 2) b]
    ... = a ^ 2 * a + 2 * a * b * a + a * b ^ 2 + 
    (a ^ 2 * b + 2 * a * b * b + b ^ 3) : 
    by rw [add_mul, add_mul, mul_comm (b ^ 2) a, pow_succ' b 2]
    ... = a ^ 3 + 2 * a * (b * a) + a * b ^ 2 + 
    (a ^ 2 * b + 2 * a * (b * b) + b ^ 3) : 
    by rw [pow_succ' a 2, mul_assoc, mul_assoc (2 * a) b b]
    ... = a ^ 3 + 2 * a * (a * b) + a * b ^ 2 + 
    (a ^ 2 * b + 2 * a * b ^ 2 + b ^ 3) : 
    by rw [mul_comm b a, pow_two]
    ... = a ^ 3 + 2 * a * a * b + a * b ^ 2 + 
    (a ^ 2 * b + 2 * a * b ^ 2 + b ^ 3) : 
    by rw [mul_assoc (2 * a) a b]
    ... = a ^ 3 + 2 * (a * a) * b + 1 * a * b ^ 2 + 
    (1 * a ^ 2 * b + 2 * a * b ^ 2 + b ^ 3) : 
    by rw [mul_assoc 2 a a, one_mul, one_mul]
    ... = a ^ 3 + 2 * a ^ 2 * b + 1 * a * b ^ 2 + 
    (1 * a ^ 2 * b + 2 * a * b ^ 2 + b ^ 3) : 
    by rw [pow_two a]
    ... = a ^ 3 + 2 * a ^ 2 * b + 1 * a * b ^ 2 + 
    (1 * a ^ 2 * b + 2 * a * b ^ 2) + b ^ 3 : 
    by rw [add_assoc (a ^ 3 + 2 * a ^ 2 * b + 1 * a * b ^ 2) 
    (1 * a ^ 2 * b + 2 * a * b ^ 2) (b ^ 3)]
    ... = a ^ 3 + 2 * a ^ 2 * b + 1 * a * b ^ 2 + 
    1 * a ^ 2 * b + 2 * a * b ^ 2 + b ^ 3 : 
    by rw [add_assoc (a ^ 3 + 2 * a ^ 2 * b + 1 * a * b ^ 2) (1 * a ^ 2 * b)
    (2 * a * b ^ 2)]
    ... = a ^ 3 + 2 * a ^ 2 * b + (1 * a * b ^ 2 + 
    1 * a ^ 2 * b) + 2 * a * b ^ 2 + b ^ 3 : 
    by rw [add_assoc (a ^ 3 + 2 * a ^ 2 * b) (1 * a * b ^ 2) (1 * a ^ 2 * b)]
    ... = a ^ 3 + 2 * a ^ 2 * b + (1 * a ^ 2 * b + 1 * a * b ^ 2) +
    2 * a * b ^ 2 + b ^ 3 : 
    by rw [add_comm (1 * a ^ 2 * b) (1 * a * b ^ 2)]
    ... = a ^ 3 + 2 * a ^ 2 * b + 1 * a ^ 2 * b + 1 * a * b ^ 2 +
    2 * a * b ^ 2 + b ^ 3 : 
    by rw [add_assoc (a ^ 3 + 2 * a ^ 2 * b) (1 * a ^ 2 * b) (1 * a * b ^ 2)]
    ... = a ^ 3 + (2 * a ^ 2 * b + 1 * a ^ 2 * b) + (1 * a * b ^ 2 +
    2 * a * b ^ 2) + b ^ 3 : 
    by rw [add_assoc (a ^ 3) (2 * a ^ 2 * b) (1 * a ^ 2 * b), 
    add_assoc (a ^ 3 + (2 * a ^ 2 * b + 1 * a ^ 2 * b)) (1 * a * b ^ 2) 
    (2 * a * b ^ 2)]
    ... = a ^ 3 + (2 + 1) * (a ^ 2 * b) + (1 + 2) * (a * b ^ 2) + b ^ 3 : 
    by rw [mul_assoc 2 (a ^ 2) b, mul_assoc 1 (a ^ 2) b, mul_assoc 1 a (b ^ 2),
    mul_assoc 2 a (b ^ 2), add_mul 2 1 (a ^ 2 * b), add_mul 1 2 (a * b ^ 2)]
    ... = a ^ 3 + 3 * (a ^ 2 * b) + 3 * (a * b ^ 2) + b ^ 3 : rfl
    ... = a ^ 3 + 3 * a ^ 2 * b + 3 * a * b ^ 2 + b ^ 3 : 
    by rw [mul_assoc 3 (a ^ 2) b, mul_assoc 3 a (b ^ 2)]