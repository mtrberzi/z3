(set-logic QF_S)
(declare-const key String)
(declare-const val String)
(assert (str.in.re key (re.* (re.range "J" "W"))))
(assert (<= 7 (str.to.int key)))
(assert (>= 13 (str.to.int key)))

(check-sat)
