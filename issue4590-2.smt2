(declare-fun a () String)
(assert (not (and 
    (str.in_re a (re.opt re.allchar)) 
    (not (str.in_re a (re.opt re.allchar)))
)))
(check-sat)