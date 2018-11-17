namespace xena

inductive xnat
| zero : xnat
| succ : xnat → xnat

open xnat

definition lt : xnat → xnat → Prop 
| zero zero := false
| (succ m) zero := false
| zero (succ p) := true 
| (succ m) (succ p) := lt m p

notation a < b := lt a b

#print int



theorem inequality_A2 (a b c : xnat) : a < b → b < c → a < c := λ hab hbc, sorry

end xena

#print prod