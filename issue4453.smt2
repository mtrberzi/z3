(declare-fun a () Int)
(declare-fun b () Int)
(declare-fun c () String)
(declare-fun d () String)
(declare-fun e () String)
(declare-fun f () String)
(declare-fun g () String)
(declare-fun h () String)
(declare-fun i () String)
(declare-fun j () String)
(declare-fun k () String)
(declare-fun l () String)
(declare-fun m () String)
(declare-fun n () String)
(declare-fun o () String)
(declare-fun p () String)
(declare-fun q () Bool)
(declare-fun r () String)
(assert
 (ite q
 (and (= b a) (= r (str.++ d m)) (= a (str.len n)) (= 0 (str.len d))
  (= m (str.++ h k)) (= h (str.++ n p)) (= p "zzaaaaaaaaaaaaaac"))
 (= b 0)))
(assert (< 0 b))
(assert (= r (str.++ f c i)))
(assert (= (+ b 7) (str.len f)))
(assert (= (= r (str.++ g j l o) "zzaaabaaaaaaaaaac")
     (not (str.in_re e (str.to_re "c")))))
(check-sat)