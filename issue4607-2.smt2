; timeout

(declare-fun IP () String)
(assert (not (= (str.at (str.substr IP 0 (- (str.indexof IP ".") 0)) 0) "0")))
(assert (not (> (ite (str.prefixof "-" (str.substr IP 0 0)) 0 (str.to_int (str.substr IP 0 (- (str.indexof IP ".") 0)))) 255)))
(assert (ite (str.prefixof "-" (str.substr IP 0 (- 0))) (and (> 0 1)) (ite (= (- 1) (str.to_int (str.substr IP 0 (- (str.indexof IP ".") 0)))) false true)))
(assert (str.in_re (str.substr IP 0 (- (str.indexof IP ".") 0)) (re.+ (re.range "0" "9"))))
(assert (not (str.in_re (str.substr (str.substr IP (+ (str.indexof IP ".") 1) (- (str.len IP) 0)) 0 (- (str.indexof (str.substr IP (+ (str.indexof IP ".") 1) (- (str.len IP) (+ 1))) ".") 0)) (re.+ (re.range "0" "9")))))
(check-sat)