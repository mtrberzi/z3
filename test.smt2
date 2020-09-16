(declare-const X String)
(declare-const i1 Int)
(declare-const i2 Int)
(declare-const i3 Int)
(declare-const i4 Int)
(declare-const i5 Int)

(assert (= "efg" (str.substr X i1 i2)))
(assert (= "bef" (str.substr X i3 i4)))
(assert (= "-v-" (str.substr X i5 3)))
(assert (<= (str.len X) 9))

(check-sat)
(get-model)