import Mathlib

open Real Filter Topology

#check HasDerivAt

#check HasDerivWithinAt

#check HasDerivAt.add

#check HasDerivAt.comp

#check Real.hasDerivAt_cos

#check Real.hasDerivWithinAt_arccos_Ici

example : HasDerivAt (fun x : ℝ => x ^ x) 1 1 := by
  have claim1 : HasDerivAt (fun x : ℝ => rexp (x * log x)) 1 1 := by
    have d0 : HasDerivAt log 1 1 := by simpa using Real.hasDerivAt_log (x := 1) (by simp)
    have d1 : HasDerivAt (fun x : ℝ => x) 1 1 := hasDerivAt_id' 1
    have d1 : HasDerivAt (fun x : ℝ => x * log x) 1 1 := by simpa using d1.mul d0

    simpa using Real.hasDerivAt_exp _ |>.comp 1 d1

  refine claim1.congr_of_eventuallyEq ?_
  refine eventually_of_mem (U := Set.Ioo 0 2) (Ioo_mem_nhds (by simp) (by simp)) ?_
  simp only [Set.mem_Ioo, and_imp]
  intro x hx0 hx1
  rw [mul_comm, exp_mul, exp_log hx0]
