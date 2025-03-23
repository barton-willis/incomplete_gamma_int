#| 
  Barton Willis
  Common Lisp code for integration by dispatch from the logarithmic derivative of the
  integrand.

 License: CC0 1.0 Universal (https://creativecommons.org/publicdomain/zero/1.0/) |#

(in-package :maxima)

;; Give %integrate a 'msimpind property
(setf (get '%integrate 'msimpind) (list '%integrate 'simp))

(defun nonnegative-integer-p (n)
  "Predicate that determines if the input is an explicit nonnegative integer. Symbols that have been
   declared to be integers and nonnegative do not qualify as being explicit."
   (and (integerp n) (> n -1)))

(defun log-derivative (e x)
   "Return the partial faction decomposition of the logarithmic derivative of the expression 'e' with respect to 'x'"
   ($partfrac (div ($diff e x) e) x))

;; Return true if the expression 'e' is piecewise constant expression in x. Let's try 
;; something really simple--return true when diff(e,x) = 0. This catches some non constant 
;; but piecewise constant cases such as 'x -> |x|/x' and 'x -> (1-x)^q/(x-1)^q', for example. 
;; We could try more simplification functions, such as 'radcan' or 'trigreduce'.
(defun piecewise-constant-p (e x) 
  "This predicate attempts to determine if the expression `e` is piecewise constant (that is,
  free of 'x') with respect to the variable `x`. This function simplifies the expression `e`, 
  then and checks if its derivative with respect to `x` is zero."
  (setq e (sratsimp e))
  (setq e (let (($rootsconmode '$all)) ($rootscontract e)))
  (setq e ($factor ($diff e x)))
  (eq t (meqp e 0)))

;; We'll apply `final-simplification` to each antiderivative. Currently not used.
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

(defun operator-among (e x funlist)
 "A predicate that determines if the expression 'e' has a subexpresion of the form ((fn ...) args),
 where fn is a member of the CL list `funlist` and one of more members of `args` depends on the variable `x`."
  (cond ((or (null e) ($mapatom e)) nil)
        ((and (member (mop e) funlist) (not (freeof x e))) t)
        (t (some #'(lambda (q) (operator-among q x funlist)) (cdr e)))))

;; We have expr'/expr = p/q, where p/q is free of x. So expr = m exp(p x/q) and 
;; integrate(expr,x) = m q exp(p x /q)/p, provided p =/= 0.
(defun integrate-degree-0-0 (expr p q x)
  "Return integrate(expr,x), where the logarithmic derivative of expr is p/q and p and q are both zero degree
   polynomials in x. Thus, 'p/q' is free of 'x', and expr = m exp(p x /q). Limitation: We assume that if
   meqp tests p as nonvanishing, it is nonvanishing."
  (let ((m) (ans))
    (cond ((eq t (meqp p 0)) 
           (mul expr x))
          (t 
           (setq ans (ftake 'mexpt '$%e (div (mul p x) q)))
           (setq m (div expr ans))
           (if (piecewise-constant-p m x)
               (div (mul m q ans) p)
             nil)))))

(defun integrate-degree-1-0 (expr p q x)
  "Return integrate(expr,x), where the logarithmic derivative of expr is p/q and p is a first degree polynomial
   in x and q is a degree zero polynomial."
  (let ((a ($coeff p x 0))
        (b ($coeff p x 1))
        (c ($coeff q x 0))
        (m))
    (cond ((eq t (meqp c 0)) nil) ; likely should never happen
          ;; When b = 0, the polynomial isn't degree one, so some other case should catch this--so return nil
          ((eq t (meqp b 0)) nil) 
          (t
           ;; To simplify, let's divide a and b by c. But first, we use meqp to check if c vanishes. 
           ;; If meqp is unable to determine that c vanishes, we assume notequal(c,0) and we go ahead and
           ;; divide by c. This function is called in its own context, so this assumption eventually is removed.
           (assume (ftake '$notequal c 0))
           (assume (ftake '$notequal b 0))
           (setq a (sratsimp (div a c))
                 b (sratsimp (div b c))
                 c 1)
           ;; Find m; when it doesn't appear that m is free of `x`, return nil;
           (setq m (div expr (ftake 'mexpt '$%e (add (mul a x) (div (mul b x x) 2)))))
           ;; I think that erfi(%i*x) should automatically simplify to %i erf(x). I could put in
           ;; a workaround here, but let's not do that.
           (cond ((piecewise-constant-p m x)
                  (mul m
                       (ftake 'mexpt '$%e (div (mul -1 a a) (mul 2 b)))
                       (ftake 'mexpt (div '$%pi (mul 2 b)) (div 1 2))
                       (ftake '%erfi (div (add a (mul b x)) (ftake 'mexpt (mul 2 b) (div 1 2))))))
                 (t nil))))))
             
(defun integrate-degree-1-1 (expr p q x)
  "Return integrate(expr,x), where the logarithmic derivative of expr is p/q and p & q are first
   degree polynomials in x."

  ;; To start, we express p/q = (a + bx)/(c + dx). Presumably, d =/= 0, but we'll check that.
  (let ((m) 
        (a ($coeff p x 0)) 
        (b ($coeff p x 1)) 
        (c ($coeff q x 0)) 
        (d ($coeff q x 1)))
    ;; To simplify, let's divide a, b, and c by d. But first, we use meqp to check if d vanishes. 
    ;; If meqp is unable to determine that d vanishes, we assume notequal(d,0) and we go ahead and
    ;; divide by d. This function is called in its own context, so this assumption eventually is removed.
    (cond ((eq t (meqp d 0)) nil)
          (t (assume (ftake '$notequal d 0))
             (setq a (sratsimp (div a d))
                   b (sratsimp (div b d))
                   c (sratsimp (div c d))
                   d 1)
    
             ;; We now have exp(integrate(p/q,x)) = (x+c)^(a-b*c)*%e^(b*x), so now we need to 
             ;; find m such that expr = m * (x+c)^(a-b*c)*%e^(b*x). When it doesn't appear that 
             ;; m is free of `x`, return nil; otherwise, return integrate(expr,x
             (setq m (div expr (mul (power '$%e (mul b x)) 
                                    (power (add c x) (sub a (mul b c))))))

             ;; We require that m be piecewise constant; if not, return nil; maybe when Maxima
             ;; is unable to determine if m is piecewise constant, it should print an informational
             ;; message?
             (cond ((piecewise-constant-p m x)
                    (mul -1 
                         m
                         (power (neg b) (add (mul b c) (neg a) -1))
                         (ftake '%gamma_incomplete (add 1 a (mul -1 b c)) (neg (mul b (add c x))))))
                   (t nil))))))

;; Match an expression `expr` to `m*(a+x)^b*(c+x)^d` where `a`,`b`,`c`,and `d`
;; are freeof `x`. This function works by matching the logarithmic derivative of 
;; the integrand to a rational function. Matching to a rational function is more
;; straightforward than matching to `m*(a+x)^b*(c+x)^d`.
(defun integrate-degree-1-2 (expr p q x)
"Return integrate(expr,x), where the logarithmic derivative of expr is p/q where degree(p) = 1 & 
 degree(q) = 2."
  (let ((roots) (a) (c) (b) (d) (m) (disc))
     ;; We need to express p/q as d/(x+c)+b/(x+a). If q nicely factors, it's just a pfd, but
     ;; if not, the matching takes more effort. First, we set a & c to the roots of q.
     (setq roots ($solve q x))
     (setq roots (mapcar #'$rhs (cdr roots)))
     (setq a (neg (first roots))
           c (neg (second roots)))

     ;; next, we find b & d
     (setq b ($residue (div p q) x (neg a))
           d ($residue (div p q) x (neg c)))
    
     ;; when both b = -1 and d = -1, its a non hypergeometric case, so return nil
     (when (or (eq t (meqp b -1)) (eq t (meqp b -2)) (and (integerp (add b 2)) (eq t (mgrp -2 b))))
               (rotatef b d)
               (rotatef a c))
     ;; Find m; when it doesn't appear that m is free of `x`, return nil;
     (setq m (div expr (mul (power (add a x) b) (power (add c x) d))))

     (setq disc (if (and a c) (sub a c) 0))
     
     (cond ((piecewise-constant-p m x)
            (ftake 'mtimes
                  m 
                  (power (add a x) (add 1 b))
                  (power -1 (neg d))
                  (power disc d)
                  (power (add 1 b) -1)
                  (ftake '%hypergeometric 
                             (ftake 'mlist (add 1 b) (neg d))
                             (ftake 'mlist (add 2 b)) 
                             (div (add a  x) disc))))
           (t nil))))

(defun integrate-degree-2-3 (expr p q x)
"Attempts to match 'expr' to `m*(a+x)^b*(c+x)^d*(e+x)^f` where `a`,`b`,`c`, `d` and `f`
 are freeof `x`. If a match is found, the multiple values of 'm', 'a', 'b', 'c', 'd', and 'f';
 when a match isn't found, return nil."

  (let ((a0) (a1) (a2) (a3) (b0) (b1) (b2) (ans) (a) (b) (c) (d) (e) (f) (m))
  
  (setq a0 ($coeff q x 0)
        a1 ($coeff q x 1)  
        a2 ($coeff q x 2)
        a3 ($coeff q x 3)
        b0 ($coeff p x 0) 
        b1 ($coeff p x 1)
        b2 ($coeff p x 2))

  (setq a0 (div a0 a3)
        a1 (div a1 a3)
        a2 (div a2 a3)
        b0 (div b0 a3)
        b1 (div b1 a3)
        b2 (div b2 a3)
        a3 1)
 
   ;; the roots of the denominator are the values of a, c, and e.
   ;; Maybe need to define a proper environment for $solve?
   (setq ans (let (($radexpand '$all)) ($solve ($factor q) x)))
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
            (appell-integrate m a b c d e f x) 
            nil)))

(defun appell-integrate (m a b c d e f x)
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
               (mul m 
                    (power (add a x) (add 1 b))
                    (power (sub c a) d)
                    (power (sub e a) f)
                    (ftake '%appell_f1 (add 1 b) (neg d) (neg f) (add 2 b)
                                       (div (add a x) (sub a c)) 
                                       (div (add a x) (sub a e))))
              (add 1 b)))))

;(defun integrate-degree-2-1 (expr p q x)
;; We could use a more powerful subsitition method that calls solve. But let's try this approach.
(defun derivative-divides-subst (e x ker g)
  "When e = ker'(x) F(ker(x)), return F(g); otherwise return nil"
  (let ((dker (sdiff ker x)))
    (cond 
      ((eq t (meqp dker 0)) ;could use a more powerful test for a vanishing kernel
       nil)
      (t
       (assume (ftake '$notequal dker 0)) ;unlikely this ever makes a difference, but OK
       (setq e (sratsimp (div e dker)))
       (setq e (resimplify (let (($radsubstflag t)) ($ratsubst g ker e)))) ;possibly ratsubst can return an unsimplified result
       (if ($freeof x e) 
           e 
           nil)))))

;; For testing only--integrate-by-log-diff-dispatch isn't intended to be a user-level function.
(defmfun $my_int (expr x)
    (integrate-by-log-diff-dispatch expr x))

(defun integrate-by-log-diff-dispatch (expr x &optional (recurse t))
  "This function returns either `integrate(expr, x)` or nil. When the logarithmic derivative of the
   intergrand 'expr' is a rational function, based on the degrees of the rational function, it dispatches 
   special cases. When the degree dispatch fails, it uses a hurestic to attempt to find a derivative 
   divides substition that makes the logarithmic derivative rational and when successful, it then recursively 
   calls `integrate-by-log-diff-dispatch`. When the recursion depth exceeds the optional argument `depth`, the 
   recursion stops and the funtion returns nil. 

   This function defines its own supercontext, allowing the function to make assumptions that will be removed on
   exit."

  (mtell "expr = ~M ~%" expr)
  (let ((dq (log-derivative expr x))
        (p) (q) (xi) 
        (g (gensym)) 
        (ans nil)
        (deg-p nil) 
        (deg-q nil) 
        (eexpr)
        (cntx ($supcontext)))
    
    ;; Prevent Maxima from asking about 'g' by giving it the internal property.
    (putprop g t 'internal)
    (flet ((poly-p (p x)
             ($polynomialp p (ftake 'mlist x)
                          #'(lambda (s) (freeof x s))
                          #'nonnegative-integer-p)))
      
      (setq dq (sratsimp ($partfrac dq x)))
      (setq p ($num dq))
      (setq q ($denom dq))
      (when (and (poly-p p x) (poly-p q x))
        (setq deg-p ($hipow p x))
        (setq deg-q ($hipow q x)))

      ;; Work in a super context for local assumptions.
      (unwind-protect
            (cond
              ((operator-among expr x '(mabs %signum $conjugate %realpart 
                  $sum $product %sum %product %imagpart %integrate %derivative)) nil)
              ((and (eql 0 deg-p) (eql 0 deg-q))
               (integrate-degree-0-0 expr p q x))
              ((and (eql 1 deg-p) (eql 1 deg-q))
               (integrate-degree-1-1 expr p q x))
              ((and (eql 1 deg-p) (eql 0 deg-q))
               (integrate-degree-1-0 expr p q x))
              ((and (eql 1 deg-p) (eql 2 deg-q))
               (integrate-degree-1-2 expr p q x))
              ((and (eql 2 deg-p) (eql 3 deg-q))
               (integrate-degree-2-3 expr p q x))
              ((and (eql 2 deg-p) (eql 1 deg-q))
                (integrate-degree-2-1 expr p q x))
              (recurse
               (setq xi (gather-subexpressions expr x))
               (setq xi (fapply '$set xi))
               (setq xi ($disjoin x xi)) ; Changing x -> g does nothing, so don't do it.
               (setq xi ($disjoin expr xi))
               ;; sort members from least to greatest complexity
               (setq xi (sort (cdr xi) #'(lambda (a b) (< (complexity a) (complexity b)))))
               (setq xi nil)
               (catch 'done ans
                 (dolist (ker xi)
                   (setq eexpr (derivative-divides-subst expr x ker g)) ; The variable change can fail!
                   (setq eexpr ($radcan eexpr))
                   (when eexpr
                     (setq ans (integrate-by-log-diff-dispatch eexpr g nil))
                     (when ans
                       (setq ans ($substitute ker g ans))
                       (throw 'done ans))))))
              (t nil))
          ($killcontext cntx)))))
