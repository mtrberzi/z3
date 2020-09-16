; invalid model

(set-logic QF_SLIA)
(set-option :model_validate true)
(set-option :smt.string_solver z3str3)
(declare-const Str16 String)
(assert (>= (str.len (str.substr Str16 0 14)) 446))
(check-sat)
