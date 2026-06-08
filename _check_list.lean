import Mathlib.Data.List.Basic

#check @List.ext
#check @List.eq_iff_forall_mem
#check @List.mem_filter

example (c : List ℕ) (k : ℕ) (hk : k ∈ c) :
    (c.filter fun k' => decide (k' = k)) = [k] := by
  simp [List.mem_filter, List.mem_singleton, decide_eq_true_iff, hk]
