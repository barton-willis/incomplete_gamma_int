
(in-package :maxima)

(defun log-derivative (e x)
   "Return the partial faction decomposition of the logarithmic derivative of the expression 'e' with respect to 'x'"
   ($partfrac (div ($diff e x) e) x))

;; Maxima's pattern `m2` pattern matcher is a quick way to add integration facts, but it
;; misses lots of cases. Example: the integral integrate((1+ d*x)^a*exp(x),x) is caught
;; by the pattern matcher, but it fails to match the integrand (1+ x/d)^a*exp(x). At a 
;; cost of more complexity, almost surely another rule can be appended to catch this case, 
;; but 

;; Match an expression `expr` to `m*(a+x)^b*(c+x)^d` where `a`,`b`,`c`,and `d`
;; are freeof `x`.
(defun match-f21(expr x)
  (let ((q (log-derivative expr x)) (nn) (dd) (a0) (a1) (a2) (b0) (b1) (qq)
        (a) (b) (c) (d) (m))
   (setq q (sratsimp q))
   (setq nn ($expand ($num q))) ; let's hope that degree isn't huge!
   (setq dd ($expand ($denom q)))

   (mtell "dd = ~M ~%" dd)
   (cond ((and ($polynomialp nn (ftake 'mlist x) 
                       #'(lambda (s) (freeof x s))
                       #'(lambda (s) (or (eql s 0) (eql s 1))))
               ($polynomialp dd (ftake 'mlist x) 
                       #'(lambda (s) (freeof x s))
                       #'(lambda (s) (or (eql s 0) (eql s 1) (eql s 2)))))

         (setq a0 ($coeff dd x 0)
               a1 ($coeff dd x 1)  
               a2 ($coeff dd x 2)
               b0 ($coeff nn x 0) 
               b1 ($coeff nn x 1))

         (setq a0 (div a0 a2)
               a1 (div a1 a2)
               b0 (div b0 a2)
               b1 (div b1 a2)
               a2 1)

         (setq q ($factor (sub (mul a1 a1) (mul 4 a0)))) ;a1^2-4*a0

         ;; Set qq to a (not the) square root of q; when `q` is a perfect square,
         ;; say `w^2`, set qq to w. This can be done by setting `radexpand` to `all`
         (setq qq (let (($radexpand '$all)) (ftake 'mexpt q (div 1 2))))

         (setq 
             a (div (add qq a1) 2) 
             b (div (add (mul b1 q) (mul (sub (mul a1 b1) (mul 2 b0)) qq)) (mul 2 q)) 
             c (div (add a1 (neg qq)) 2) 
             d (div (add (mul b1 q) (neg (mul (sub (mul a1 b1) (mul 2 b0)) qq))) (mul 2 q)))
            
         (setq a (sratsimp a)
              b (sratsimp b)
              c (sratsimp c)
              d (sratsimp d))

        ;; Find m; when it doesn't appear that m is free of `x`, return nil;
        ;; otherwise, return the values of `m,a,b,c,d`.
        ;; m*(a+x)^b*(c+x)^d
        (setq m (sratsimp (div expr (mul (power (add a x) b) (power (add c x) d)))))
        (setq m (let (($rootsconmode '$all)) ($rootscontract m)))
        (if (freeof x m)
            (values m a b c d) 
            nil)))))

(defmfun $f21_integrate (expr x)
   (let (m a b c d disc)
    (multiple-value-setq (m a b c d) (match-f21 expr x))
    ;; We have matched expr to m (a + x)^b * (c + x)^d. But when b = -1, we switch
    ;; the two terms; after the switch either both b & d are -1 or b isn't -1.
    (when (or (eq t (meqp b -1)) (eq t (meqp b -2)) (and (integerp (add b 2)) (eq t (mgrp -2 b))))
            (rotatef b d)
            (rotatef a c))
    ;; disc = a -c. Let's not do arithmetic with nil, so we check if a & c are non null
    (setq disc 
      (if (and a c) (sub a c) 0))

   ;; Return ans = integrate((a + x)^b*(c + x)^d, x).  The non-hypergeometric
   ;; cases are:

   ;;   (a) when either b = -1, ans is non-hypergeometric
   ;;   (b) when disc = 0, ans is non hypergeometric

   ;; Return nil for the non-hypergeometric cases, as these cases should be
   ;; caught by other methods (integration of a rational function, for example).
   ;; This code assumes that if an expression isn't meqp equal to zero, it is nonzero.
   (cond 
      ;; the match failed, so return nil
      ((not (and m a b c d)) nil)
      ;; non-hypergeometric cases, return nil
      ((or (eq t (meqp b -1)) (eq t (meqp disc 0))) nil)
      ;; hypergeometric case!
      (t            
         (ftake 'mtimes
                  m 
                  (power (add a x) (add 1 b))
                  (neg disc)
                  (ftake '%hypergeometric 
                             (ftake 'mlist (add 1 b) (neg d))
                             (ftake 'mlist (add 2 b)) 
                             (div (add a  x) disc)))))))
   
          