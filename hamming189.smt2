(set-logic QF_S)

;(declare-fun var_0 () String)
;(declare-fun var_1 () String)
;(declare-fun var_2 () String)
(declare-fun var_3 () String)
(declare-fun var_4 () String)
;(declare-fun var_5 () String)
;(declare-fun var_6 () String)
;(declare-fun var_7 () String)
;(declare-fun var_8 () String)
;(declare-fun var_9 () String)
;(declare-fun var_10 () String)
;(declare-fun var_11 () String)
;(declare-fun var_12 () String)

(declare-const X String)

;(assert (= X (str.++ var_3 "z" var_4 )))
(assert (str.in.re
         (str.++ var_3 "z" var_4 )
         
         (re.++ (re.* (re.union (str.to.re "z") (re.++ (re.union (str.to.re "b") (str.to.re "a")) (re.union (str.to.re "z") (str.to.re "b"))))) (re.union (str.to.re "b") (str.to.re "a")))
        ))

;(assert (str.in.re var_4 (re.* (re.range "a" "u"))))
;(assert (str.in.re var_4 (re.* (str.to.re "b"))))
;(assert (str.in.re var_3 (re.* (re.range "a" "u"))))
;(assert (str.in.re var_3 (re.* (str.to.re "a"))))
;(assert (<= 0  (str.len var_4)))

(check-sat)
(get-model)

;(model
;  (define-fun var_4 () String
;    "b")
;  (define-fun var_3 () String
;    "")
;  (define-fun var_8 () String
;    "")
;  (define-fun var_11 () String
;   "")
;  (define-fun var_6 () String
;    "")
;  (define-fun var_10 () String
;    "")
;  (define-fun var_5 () String
;    "")
;  (define-fun var_0 () String
;    "")
;  (define-fun var_2 () String
;    "")
;  (define-fun var_1 () String
;    "")
;  (define-fun var_7 () String
;    "")
;  (define-fun var_9 () String
;    "")
;  (define-fun var_12 () String
;    "")
;)
