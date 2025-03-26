#| 
  Barton Willis
  Common Lisp code for integration of some functions whose antiderivative involves 
  the Gauss hypergeometric function.

 License: CC0 1.0 Universal (https://creativecommons.org/publicdomain/zero/1.0/) |#

(in-package :maxima)

;; Give %integrate a 'msimpind property
(setf (get '%integrate 'msimpind) (list '%integrate 'simp))

(defun nonnegative-integer-p (n)
  "Predicate that determines if the input is an explicit nonnegative integer."
   (and (integerp n) (> n -1)))

(defun log-derivative (e x)
   "Return the partial faction decomposition of the logarithmic derivative of the expression 'e' with respect to 'x'"
   ($partfrac (div ($diff e x) e) x))

;; Return true if the expression 'e' is piecewise constant expression in x. Let's try 
;; something really simple--return true when diff(e,x) = 0. This catches some non constant 
;; but piecewise constant cases such as x -> |x|/x and x -> (1-x)^q/(x-1)^q for example. 
;; We could try more simplification functions, such as `radcan` or `trigreduce`.
(defun piecewise-constant-p (e x) 
  "This predicate attempts to determine if the expression `e` is piecewise constant (that is,
  free of 'x') with respect to the variable `x`. This function simplifies the expression `e`, 
  then  and checks if its derivative with respect to `x` is zero. When Maxima doesn't 
  determine that the derivative vanishes, it prints an informational message."  
  (setq e (sratsimp e))
  (setq e (let (($rootsconmode '$all)) ($rootscontract e)))
  (setq e ($factor ($diff e x)))
  (if (eq t (meqp e 0))
      t
      (mtell "Info: unable to show that ~M is piecewise constant ~%" e)))

;; We'll apply `final-simplification` to each antiderivative. 
(defun final-simplification (e)
  "Apply a standard simplification of the expression `e`. We apply this to all antiderivative"
  (setq e (let (($rootsconmode '$all)) ($rootscontract e)))
  (mfuncall '$scanmap '$factor e))

;; Maybe this function should return a set of the subexpressions.
(defun gather-subexpressions (e x)
  "Return a CL list of the subexpressions of `e` that contain the variable 'x'." 
  (let ((f nil))
      (cond (($mapatom e) 
             (if (among x e)  (list e) nil))
            (t
              (when (among x e)
                  (push e f))
              (dolist (ek (cdr e))
                  (setq f (append f (gather-subexpressions ek x))))
              f))))

;; Maxima's `m2` pattern matcher is a quick way to add integration facts, but our `m2` based code
;; misses lots of cases. Example: the integral integrate((1+ d*x)^a*exp(x),x) is caught
;; by the pattern matcher, but it fails to match the integrand (1+ x/d)^a*exp(x). At a 
;; cost of more complexity, almost surely another rule can be appended to catch this case, 
;; but surely there is a better way.

(defun constant-integrate (expr x)
  (if (piecewise-constant-p expr x)
      (mul expr x)
      nil))

;; We have integrate(m * (x+a)^b * exp(-c*x),x) =  -(gamma_incomplete(b+1,c*x+a*c)*c^(-b-1)*%e^(a*c)*m).
;; The logarithmic derivative of the integrand is b/(x+a)-c. This function matches the logarithmic  
;; derivative of and integrand to b/(x+a)-c. When that match is successful, it find the value of m.
(defun match-incomplete-gamma (expr x)
"Attempts to match 'expr' to `m * (x+a)^b * exp(-c*x)` where `m`, `a`, `b1, and `c` are freeof `x`. If a match is 
found, return the multiple values of 'm', 'a', 'b', and 'c'; when a match isn't found, return nil."

  (let ((q (log-derivative expr x)) (nn) (dd) (a0) (a1) (b0) (b1) (a) (b) (c) (m))
   (setq q (sratsimp q))

   (setq nn ($expand ($num q))) ; let's hope that degree isn't huge!
   (setq dd ($expand ($denom q)))

   (cond ((and ($polynomialp nn (ftake 'mlist x) 
                       #'(lambda (s) (freeof x s))
                       #'(lambda (s) (or (eql s 0) (eql s 1))))
               (eql 1 ($hipow dd x))
               ($polynomialp dd (ftake 'mlist x) 
                       #'(lambda (s) (freeof x s))
                       #'(lambda (s) (or (eql s 0) (eql s 1)))))

         (setq a0 ($coeff dd x 0)
               a1 ($coeff dd x 1)  
               b0 ($coeff nn x 0) 
               b1 ($coeff nn x 1))

         (setq a0 (div a0 a1)
               b0 (div b0 a1)
               b1 (div b1 a1)
               a1 1)
         ;;a=a0,b=b0-a0*b1,c=-b1
         (setq 
             a a0
             b (sub b0 (mul a0 b1)) ;b0-a0*b1
             c (neg b1))
            
         (setq a (sratsimp a)
               b (sratsimp b)
               c (sratsimp c))

        ;; Find m; when it doesn't appear that m is free of `x`, return nil;
        ;; otherwise, return the values of `m,a,b,c,d`. (x+a)^b * exp(c*x)
        (setq m (div expr (mul (power (add a x) b) (power '$%e (neg (mul c x))))))
        (if (piecewise-constant-p m x)
            (values m a b c) 
            nil))
      (t nil))))

(defun incomplete-gamma-integrate (expr x)
   (let (m a b c)
     (multiple-value-setq (m a b c) (match-incomplete-gamma expr x))
     (if (and m a b c (not (eq t (meqp c 0))))
      (div  (mul -1 
                m
                (power '$%e (mul a c))
                (ftake '%gamma_incomplete (add 1 b) (neg (mul c (add a x)))))
            (power c (add b 1))))))

;; Match an expression `expr` to `m*(a+x)^b*(c+x)^d` where `a`,`b`,`c`,and `d`
;; are freeof `x`. This function works by matching the logarithmic derivative of 
;; the integrand to a rational function. Matching to a rational function is more
;; straightforward than matching to `m*(a+x)^b*(c+x)^d`.
(defun match-f21 (expr x)
"Attempts to match 'expr' to `m*(a+x)^b*(c+x)^d` where `a`,`b`,`c`, and `d`
 are freeof `x`. If a match is found, the multiple values of 'm', 'a', 'b', 'c', and 'd';
 when a match isn't found, return nil."

  (let ((q (log-derivative expr x)) (nn) (dd) (a0) (a1) (a2) (b0) (b1) (qq)
        (a) (b) (c) (d) (m))
   (setq q (sratsimp q))
   (setq nn ($expand ($num q))) ; let's hope that degree isn't huge!
   (setq dd ($expand ($denom q)))

   (cond ((and ($polynomialp nn (ftake 'mlist x) 
                       #'(lambda (s) (freeof x s))
                       #'(lambda (s) (or (eql s 0) (eql s 1))))
               (eql 2 ($hipow dd x))
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
         ;; say `w^2`, set qq to w. This can be accomplished by setting `radexpand` to `all`
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
        (setq m (div expr (mul (power (add a x) b) (power (add c x) d))))
        (if (piecewise-constant-p m x)
            (values m a b c d) 
            nil)))))

(defun match-appell (expr x)
"Attempts to match 'expr' to `m*(a+x)^b*(c+x)^d*(e+x)^f` where `a`,`b`,`c`, `d` and `f`
 are freeof `x`. If a match is found, the multiple values of 'm', 'a', 'b', 'c', 'd', and 'f';
 when a match isn't found, return nil."

  (let ((q (log-derivative expr x)) (nn) (dd) (a0) (a1) (a2) (a3) (b0) (b1) (b2) (ans)
        (a) (b) (c) (d) (e) (f) (m))
   (setq q (sratsimp q))
   (setq nn ($expand ($num q))) ; let's hope that degree isn't huge!
   (setq dd ($expand ($denom q)))

   (cond ((and ($polynomialp nn (ftake 'mlist x) 
                       #'(lambda (s) (freeof x s))
                       #'(lambda (s) (or (eql s 0) (eql s 1) (eql s 2))))
               (eql 3 ($hipow dd x))
               ($polynomialp dd (ftake 'mlist x) 
                       #'(lambda (s) (freeof x s))
                       #'(lambda (s) (or (eql s 0) (eql s 1) (eql s 2) (eql s 3)))))
         (setq a0 ($coeff dd x 0)
               a1 ($coeff dd x 1)  
               a2 ($coeff dd x 2)
               a3 ($coeff dd x 3)
               b0 ($coeff nn x 0) 
               b1 ($coeff nn x 1)
               b2 ($coeff nn x 2))

         (setq a0 (div a0 a3)
               a1 (div a1 a3)
               a2 (div a2 a3)
               b0 (div b0 a3)
               b1 (div b1 a3)
               b2 (div b2 a3)
               a3 1)

         ;; the roots of the denominator are the values of a, c, and e.
         ;; Maybe need to define a proper environment for $solve?
         (setq ans (let (($radexpand '$all)) ($solve ($factor dd))))
         (setq ans (mapcar #'$rhs (cdr ans)))  
         (setq a (resimplify (neg (first ans)))
               c (resimplify (neg (second ans)))
               e (resimplify (neg (third ans))))
         ;; (b,d,f) = (a^2*b2-a*b1+b0)/((c-a)*(e-a)),-((b2*c^2-b1*c+b0)/((c-a)*(e-c))),(b2*e^2-b1*e+b0)/((e-a)*(e-c))
         (setq b (div 
                   (add (mul b2 a a) (mul -1 a b1) b0)
                   (mul (sub c a) (sub e a))))

         (setq d (div 
                   (neg (add (mul b2 c c) (mul -1 b1 c) b0))
                   (mul (sub c a) (sub e c))))

         (setq f (div 
                  (add (mul b2 e e) (mul -1 b1 e) b0)
                  (mul (sub e a) (sub e c))))

         (setq a (sratsimp a)
               b (sratsimp b)
               c (sratsimp c)
               d (sratsimp d)
               e (sratsimp e)
               f (sratsimp f))

        ;; Find m; when it doesn't appear that m is free of `x`, return nil;
        ;; otherwise, return the values of `m,a,b,c,d`.

        (setq m (div expr (mul (power (add a x) b) (power (add c x) d) (power (add e x) f))))
        (if (piecewise-constant-p m x)
            (values m a b c d e f) 
            nil))
      (t nil))))

(defun appell-integrate (expr x)
 (let (m a b c d e f)
    (multiple-value-setq (m a b c d e f) (match-appell expr x))

    (when (eql b -1)
       (rotatef a b)
       (rotatef b c)
       (rotatef d e)
       (rotatef e f))

    (when (eql b -1)
       (rotatef a b)
       (rotatef b c)
       (rotatef d e)
       (rotatef e f))

    (when (eql b -1)
       (rotatef a b)
       (rotatef b c)
       (rotatef d e)
       (rotatef e f))


    (cond ((eql b -1) nil) ; this means expr is a rational function
          (t
            (div 
               (mul (power (add a x) (add 1 b))
                    (power (sub c a) d)
                    (power (sub e a) f)
                    (ftake '%appell_f1 (add 1 b) (neg d) (neg f) (add 2 b)
                                       (div (add a x) (sub a c)) 
                                       (div (add a x) (sub a e))))
              (add 1 b))))))

(defun f21-integrate (expr x)
   "Integrate 'expr' with respect to 'x' by attempting to match`expr` to 
     m * (a + x)^b * (c + x)^d. When a match is found and both `b` and `d` are not 
     equal to -1 and `a =/= c`, an integrand that involves the Gauss hypergeometric function; 
     otherwise, return nil. The cases `a=-1` and `b=-1` as well as a=c are best handled by
     other methods. Limitations:

    - Assumes that if an expression isn't 'meqp' equal to zero, it is nonzero.
    - Non-hypergeometric cases should be caught by other methods."

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
                  (power -1 (neg d))
                  (power disc d)
                  (power (add 1 b) -1)
                  (ftake '%hypergeometric 
                             (ftake 'mlist (add 1 b) (neg d))
                             (ftake 'mlist (add 2 b)) 
                             (div (add a  x) disc)))))))

;; If you don't like returning a sum of nounform integrals and explicit integrals, locally remove
;; `nounform-integrate` from `*integration-methods*`.    
(defun additive-integrate (e x)
  "When 'e' is a 'mplus' expression, integrate it with respect to 'x'. When Maxima is able to find an 
   antiderivative (including a nounform), return an antiderivative of 'e'; otherwise return nil"
   (let ((ee nil))
     (cond ((mplusp e)
              (setq ee (mapcar #'(lambda (q) ($my_int q x)) (cdr e)))
               (if (every #'(lambda(q) q) ee)
                  (fapply 'mplus ee)
                   nil))
           (t nil))))

(defun nounform-integrate (e x)
   "Return a nounform integral of 'e' with respect to 'x'"
   (list (get '%integrate 'msimpind) e x))

(defun my-change-var (e x ker g)
  "For an integrand `e`, change the variable `x = ker` for the integrand `e`. The new integration 
   variable is `g`."
   ;; Although ker depends on x, it can happen that diff(ker,x) vanishes. An example is
   ;; ker = log(x^2) - 2 log(x) when the domain is complex.
   (let ((ee) (dker ($diff ker x)))
      (cond ((eq t (meqp dker 0)) nil)
            (t
               (setq ee ($ratsubst g ker (div e dker)))
               (setq ee (resimplify ee))
               (if ($freeof x ee) ee nil)))))

;; This is a list integration methods. Each method must be function of two variables.
;; When the method fails to find an antiderivative, it must return nil.
(defvar *integration-methods* (list 'diffdiv 
                                    'ratint 
                                    'rischint
                                    'integrate-exp-special 
                                    'incomplete-gamma-integrate 
                                    'f21-integrate 
                                    'appell-integrate
                                    'additive-integrate 
                                    'nounform-integrate))

(defmfun $my_int (e x)
   (let ((xi (gather-subexpressions e x)) (g (gensym)) (ans) (ee))
      ;; remove repeated members of `xi` and sort `xi` according to the complexity function.
      (setq xi (fapply '$set xi))
      (setq xi ($adjoin x xi))
      (setq xi (sort (cdr xi) #'(lambda (a b) (< (complexity a) (complexity b)))))
      (catch 'done ans
        (dolist (fn *integration-methods*)
           (dolist (ker xi) 
             (setq ee (my-change-var e x ker g)) ; the variable change can fail!
             (when ee
                (setq ans (funcall fn ee g))
                (when ans
                  (setq ans ($substitute ker g ans))
                  (setq ans (final-simplification ans))
                  (throw 'done ans)))))))) 


(defun integrate-by-log-diff-dispatch (e x) 
  "This function either returns integrate(e,x) or it returns nil. It works by examining the logarithmic 
   derivative of the integrand and dispatching special cases based on the degree of the numerator and
   denominator. " 
  (let ((q (log-derivative e x)) (nq) (dq))
      (setq q (sratsimp ($partfrac q x)))
      (setq nq ($num q))
      (setq dq ($denom q))
      (cond ((and 
              ($polynomialp nq (ftake 'mlist x) #'(lambda (s) (freeof x s)) #'nonnegative-integer-p)
              ($polynomialp dq (ftake 'mlist x) #'(lambda (s) (freeof x s)) #'nonnegative-integer-p))
            
            (setq deg-num ($hipow nq x))
            (setq deg-denom ($hipow dq x))

            (cond ((and (eql 1 deg-num) (eql 1 deg-denom))
                    (incomplete-gamma-integrate e x))
                  ((and (eql 1 deg-num) (eql 2 deg-denom))
                    (f21-integrate e x))
                  ((and (eql 2 deg-num) (eql 3 deg-denom))
                    (appell-integrate e x))
                  (t nil))))))  
                    