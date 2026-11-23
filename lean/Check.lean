-- Axiom audit: every key theorem must depend only on the standard axioms.
-- CI fails if `sorryAx` appears or the count of audited theorems changes.
import RRPF

#print axioms BoundedNum.sub_valid
#print axioms BoundedNum.div_valid
#print axioms BoundedNum.div_exact
#print axioms BoundedNum.mul_valid
#print axioms BoundedNum.add_valid
#print axioms BoundedNum.add_exact
#print axioms BoundedNum.mul_exact
#print axioms BoundedNum.add_mono_bound
#print axioms RRPF.RInterval.mem_iff
#print axioms RRPF.RInterval.toBN_gap
#print axioms RRPF.RInterval.toBN_add
#print axioms RRPF.RInterval.toBN_sub
#print axioms RRPF.RInterval.mul_hull_sound
#print axioms RRPF.RInterval.div_hull_sound
