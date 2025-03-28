#| Author: Barton Willis
   March 2025

Maxima code for integration of expressions of the form:

(a) cnst sin\cos(xi)^m / q^n with respect to x, where xi and q are affine functions of x, m and n are 
    positive integers, and cnst is free of x. The antiderivative is expressed in terms of Maxima's 
    expintegral_si and expintegral_ci functions.

(b) cnst x^m sin\cos(a + bx + cx^2)^n with respect to x, where a,b,c, and cnst are free of x and m is a 
    positive integer. The antiderivative is expressed in terms of Maxima's fresnel_si and fresnel_ci functions.

(c) cnst cos(a*x)^m sin(a*x)^n with respect to x, where a,m, and n are free of x (and m and n needn't be integers).

The functions in this package use the m2 pattern matcher, and that makes it sensitive to changes in
the way that Maxima orders terms in sums and products. If the function 'great' is changed, it can break
this code. 
|#

(in-package :maxima)

;; I should use m2-b*x+a (defined in sin.lisp), but older Maxima versions used a global for
;; the second argument of this function, so I'll supply a version of this function with a 
;; different name--this should allow older Maxima versions to use this code.
;; Pattern to match b*x + a
(defun m2-linear (expr var2)
  "Match an expression `expr` to `a + b*var`, where `a` and `b` are free of `var2`. Return an 
  association list for the values of `a`,`b`, and `var2`."
  (setq expr ($expand expr)) ; needed for expressions such as (4*x + 5)/7
  (m2 expr
      `((mplus)
        ((coeffpt) (b freevar2 ,var2) (x varp2 ,var2))
        ((coeffpt) (a freevar2 ,var2)))))

;; Only for testing--not intended to be a user level function
(defmfun $integrate_by_matching (e x)
   (setq e ($factor e))
  (or 
    (sinc-integrate e x)
    (cosc-integrate e x)
    (fresnel-sin-integrate e x)
    (fresnel-cos-integrate e x)
    (powers-sin-cos-integrate e x)))

(defun sinc-cosc-integrate (e x)
 " When `e` has the form `cnst cos\sin(xi)^m / q^n`, where `m` & `n` are positive integers and `xi` 
   and `q` are affine functions of `x`, return an antiderivative of `e` with respect to `x`; otherwise, 
   return nil"
  (setq e ($factor e))
  (or 
    (sinc-integrate e x)
    (cosc-integrate e x)))

(defun sinc-integrate (e x)
"When `e` has the form `cnst sin(a + bx)^m / (c + dx)^n`, where `m` & `n` are positive integers and `xi` 
 and `q` are affine functions of `x`, return an antiderivative of `e` with respect to `x`; otherwise, 
 return nil"
  (let ((disc nil) (ee) (xi) (q))
    ;; Match and extract parameters
    (multiple-value-bind (cnst a b c d m n) (match-sinc-cosc e '%sin x)

    (setq n (neg n))
    (setq xi (add a (mul b x)))
    (setq q (add c (mul d x)))
    ;; Antiderivative calculation
    (cond
     ((eql m 0) (let (($logabs nil)) ($integrate e x)))
     ((null cnst) nil)
     ((or (not (integerp m)) (not (integerp n))) nil)

     ((or (not (integer-length m)) (not (integer-length n))) nil)
     ((or (not cnst) (not m) (not n)) nil)
     ((or (< m 0) (< n 0)) nil)  ; Give up for invalid cases
     ((>= m 2)
      (setq ee ($expand (mfuncall '$trigrat e)))
      (mul cnst (fapply 'mplus
                        (mapcar #'(lambda (s) (sinc-cosc-integrate s x))
                                (cdr ee)))))

     ;; Downward recursion of exponent of denominator
     ((> n 1)
      (mul cnst
           (sub (div (ftake '%sin xi)
                     (mul d (sub 1 n) (ftake 'mexpt q (sub n 1))))
                (mul (div b (mul d (sub 1 n)))
                     (sinc-cosc-integrate (div (ftake '%cos xi)
                                               (ftake 'mexpt q (sub n 1))) x)))))

     (t
      (setq disc (div (sub (mul a d) (mul b c)) d))
      (cond
       ((eq t (meqp disc 0))
        (div (mul cnst (ftake '%expintegral_si
                              (add (div (mul b c) d) (mul b x))))
             d))
       (t
        (mul (div cnst d)
             (add (mul (ftake '%sin disc)
                       (ftake '%expintegral_ci
                              (add (div (mul b c) d) (mul b x))))
                  (mul (ftake '%cos disc)
                       (ftake '%expintegral_si
                              (add (div (mul b c) d) (mul b x)))))))))))))

(defun cosc-integrate (e x)
"When `e` has the form `cnst cos(a+bx)^m / (c+dx)^n`, where `m` & `n` are positive integers and `xi` 
 and `q` are affine functions of `x`, return an antiderivative of `e` with respect to `x`; otherwise, 
 return nil"
  (let ((disc nil) (ee) (xi) (q))
    ;; Match and extract parameters
    (multiple-value-bind (cnst a b c d m n) (match-sinc-cosc e '%cos x)
    (setq n (neg n))

    (setq xi (add a (mul b x)))
    (setq q (add c (mul d x)))
    ;; Compute the antiderivative for the integrand
    (cond
     ((eql m 0) (let (($logabs nil)) ($integrate e x))) ; Handle the case where m = 0
     ((null cnst) nil)
     ((or (not (integerp m)) (not (integerp n))) nil)
     ((eql m 0) ($integrate e x)) ; Handle the case where m = 0
      ((or (not (integer-length m)) (not (integer-length n))) nil)
     ((or (not cnst) (not m) (not n)) nil) ; Exit if invalid
     ((or (< m 0) (< n 0)) nil) ; Invalid values for m or n
     ((>= m 2)
      (setq ee ($expand (mfuncall '$trigrat e)))
      (fapply 'mplus
              (mapcar #'(lambda (s) (sinc-cosc-integrate s x))
                      (cdr ee))))
     ;; Downward recursion on the exponent of the denominator
     ((> n 1) 
      (mul cnst
           (add (div (ftake '%cos xi)
                     (mul d (sub 1 n) (ftake 'mexpt q (sub n 1))))
                (mul (div b (mul d (sub 1 n)))
                     (sinc-integrate
                      (div (ftake '%sin xi) (ftake 'mexpt q (sub n 1)))
                      x)))))
     (t
      (setq disc (div (sub (mul a d) (mul b c)) d))
      (cond
       ((eq t (meqp disc 0))
        (div (mul cnst (ftake '%expintegral_ci
                              (add (div (mul b c) d)
                                   (mul b x))))
             d))
       (t
        (mul (div cnst d)
             (sub (mul (ftake '%cos disc)
                       (ftake '%expintegral_ci
                              (add (div (mul b c) d)
                                   (mul b x))))
                  (mul (ftake '%sin disc)
                       (ftake '%expintegral_si
                              (add (div (mul b c) d)
                                   (mul b x)))))))))))))

(defun myfreeof (e x)
"If the expression `e` is free of `x`, return true; otherwise, false."
  (freeof x e))

(defun notfreeof (e x)
"If the expression `e` is not free of `x`, return true; otherwise, false."
  (not (freeof x e)))

(defun nonnegative-integer-p (n)
"If the expression `n` is an explicit integer that is greater than or equal to zero, return true; otherwise, false.
A symbol that has been declared to be an integer is not an explicit integer."
  (and (integerp n) (>= n 0)))

(defun $match_fresnel (e x)
  (multiple-value-bind (cnst a b c m n) (match-fresnel e '%sin x)
    (ftake 'mlist cnst a b c m n)))
     
(defun match-fresnel (e fn x)
  "Match `e` to `cnst * x^m fn(a+bx+cx^2)^n`, where `cnst`,`a`,`b`, and `c` are free of `x`, 
   and `m` and `n` are an explicit nonnegative integers. For the Fresnel functions, `fn` should 
   be either  `cos` or `sin`.  Return a values list of (cnst a b c m n)"
  (let ((match (m2 e `((mtimes)
                      ((coefftt) (cnst myfreeof ,x))
                      ((mexpt) ,x (m nonnegative-integer-p))
                      ((mexpt) ((,fn) 
                                 ((mplus)
                                   ((coeffpt) (c freevar2 ,x) ((mexpt) (x varp2 ,x) 2)) ; check c =/= 0 later
                                   ((coeffpt) (b freevar2 ,x) (z varp2 ,x))
                                   ((coeffpt) (a freevar2 ,x))))
                                (n nonnegative-integer-p))))))

    (if (and match (eq t (mnqp 0 (cdr (assoc 'c match)))))
        (values (cdr (assoc 'cnst match))
                (cdr (assoc 'a match))
                (cdr (assoc 'b match))
                (cdr (assoc 'c match))
                (cdr (assoc 'm match))
                (cdr (assoc 'n match)))
      nil)))

(defun fresnel-integrate (e x)
  (or
    (fresnel-sin-integrate e x)
    (fresnel-cos-integrate e x)))

(defmfun $fresnel_integrate (e x)
  (fresnel-integrate e x))

(defun fresnel-sin-integrate (e x)
  "Return an antiderivative of x -> cnst x^m sin(a + bx + cx^2)^n, where m and n are nonnegative integers and
   c is nonzero. When successful, the antiderivative is expressed in terms of Maxima's fresnel_si and fresnel_ci
   functions; when not successful, return nil."
  (let ((disc) (theta))
    (multiple-value-bind (cnst a b c m n) (match-fresnel e '%sin x)
      (cond
        ;; Didn't match, return nil
        ((null cnst) nil)

        ;; Antiderivative of cnst x^m; for this case, call sinint
        ((eql n 0) (sinint e x))

        ;; If n > 1, expand and using trigrat and call fresnel-integrate
        ((> n 1) 
          (setq e ($expand (fresnel-integrate (mfuncall '$trigrat e) x)))
          (setq e (if (mplusp e) (cdr e) (list e)))
          (fapply 'mplus (mapcar #'(lambda (q) (fresnel-integrate q x)) e)))

        ;; If m >= 1, use recursion (to be implemented, for now nil)
        ((>= m 1) nil)

        ;; If n = 1, handle cnst sin(a + bx + c x^2)
        ((eql n 1)
         (setq disc (div (sub (mul 4 a c) (mul b b)) (mul 4 c))) ; (4ac - b^2)/(4c)
         (setq theta (div (add b (mul 2 c x)) 
                            (ftake 'mexpt (mul 2 '$%pi c) (div 1 2)))) ; (b + 2 cx)/sqrt(2 %pi c)
           (mul
            cnst
            (ftake 'mexpt (div '$%pi (mul 2 c)) (div 1 2))
            (add
             (mul
              (ftake '%cos disc)
              (ftake '%fresnel_s theta))
             (mul
              (ftake '%sin disc)
              (ftake '%fresnel_c theta)))))

        ;; Otherwise, return nil
        (t nil)))))

(defun fresnel-cos-integrate (e x)
  "Return an antiderivative of x -> cnst x^m cos(a + bx + cx^2)^n, where m and n are nonnegative integers and
   c is nonzero. When successful, the antiderivative is expressed in terms of Maxima's fresnel_si and fresnel_ci
   functions; when not successful, return nil."
  (let ((disc) (theta))
    (multiple-value-bind (cnst a b c m n) (match-fresnel e '%cos x)
      (cond
        ;; Didn't match, so return nil
        ((null cnst)  nil)

        ;; Antiderivative of cnst x^m; for this case, call sinint
        ((eql n 0) (sinint e x))

        ;; If n > 1, expand and using trigrat and call fresnel-integrate
        ((> n 1) 
          (setq e ($expand (fresnel-integrate (mfuncall '$trigrat e) x)))
          (setq e (if (mplusp e) (cdr e) (list e)))
          (fapply 'mplus (mapcar #'(lambda (q) (fresnel-integrate q x)) e)))

        ;; If m >= 1, use recursion (to be implemented, for now nil)
        ((>= m 1)  nil)

        ;; If n = 1, handle cnst cos(a + bx + c x^2)
        ((eql n 1)
         (setq disc (div (sub (mul 4 a c) (mul b b)) (mul 4 c))) ; (4ac - b^2)/(4c)
         (setq theta (div (add b (mul 2 c x)) 
                            (ftake 'mexpt (mul 2 '$%pi c) (div 1 2)))) ; (b + 2 cx)/sqrt(2 %pi c)
           (mul
            cnst
            (ftake 'mexpt (div '$%pi (mul 2 c)) (div 1 2))
            (sub
             (mul
              (ftake '%cos disc)
              (ftake '%fresnel_c theta))
             (mul
              (ftake '%sin disc)
              (ftake '%fresnel_s theta)))))

        ;; Otherwise, return nil
        (t nil)))))

(defun match-sinc-cosc (e fn x)
  "Match `e` to `cnst * sin(a + bx)^m / (c + dx)^n`, where `cnst`, `a`, `b`, `c`, and `d` are
  free of `x` and  and `m` and `n` are integers. When the match is successful, return a values 
  list (cnst a b c d m n)"

  ;; To start, match to `cnst sin(xi)^m / q^n, where xi and q depend on x. We do the match in 
  ;; two stages because, for example,  xi might be 2*(3 + 4x), and to match that to a linear
  ;; expression, it must first be expanded.

  ;; To match both sin(1+x)/(1+x) and sin(1-x)/(1-x), both of the following two patterns 
  ;; are needed; similarlyfor m2-cosc.  Possibly this function should be rewritten to make 
  ;; it less dependent on term ordering, but until it is shown to be broken, let's let it be.
  (let ((cnst nil) (xi nil) (m nil) (q nil) (n nil) (a nil) (b nil) (c nil) (d nil) (w nil)
        (match
         (or (m2 e `((mtimes)
                     ((coefftt) (cnst myfreeof ,x))
                     ((mexpt) (q notfreeof ,x) (n integerp))
                     ((mexpt) ((,fn) (xi notfreeof ,x)) (m integerp))))
             (m2 e `((mtimes)
                     ((coefftt) (cnst myfreeof ,x))
                     ((mexpt) ((,fn) (xi notfreeof ,x)) (m integerp))
                     ((mexpt) (q notfreeof ,x) (n integerp)))))))

    (when match
      (setq cnst (cdr (assoc 'cnst match))
            xi   (cdr (assoc 'xi match))
            m    (cdr (assoc 'm match))
            q    (cdr (assoc 'q match))
            n    (cdr (assoc 'n match)))

      (when (null q)
        (setq q 1)
        (setq n 0))

      (when (null xi)
        (setq xi 1)
        (setq m 0))
      
      ;; Now match xi and q to linear expressions--the function m2-linear expands its first argument
      (setq w (m2-linear xi x))
      (when w
        (setq a (cdr (assoc 'a w))
              b (cdr (assoc 'b w))))

      (setq w (m2-linear q x))
      (when w
        (setq c (cdr (assoc 'a w))
              d (cdr (assoc 'b w))))

    (values cnst a b c d m n))))

(defun positive-integerp (n)
  (and (integerp n) (> n 0)))

(defun negative-integerp (n)
  (and (integerp n) (< n 0)))

(defun match-cos^m-sin^n (e x)
"Attempt to match expression `e` to the form cnst cos(a x)^mc * sin(a x)^ms,
where `const`, `a`, `b`, `mc` and `ms` are free of `x`. When successful,
return (values cnst a mc ms); otherwise return nil."
  (let ((cnst) (a) (b) (mc) (ms)
        (match (or (m2 e 
                     `((mtimes)
                       ((coefftt) (cnst myfreeof ,x))
                       ((mexpt)
                        ((%cos) ((mtimes) ((coefft) (a myfreeof ,x)) ,x))
                        (mc myfreeof ,x))
                       ((mexpt)
                        ((%sin) ((mtimes) ((coefft) (b myfreeof ,x)) ,x))
                        (ms myfreeof ,x)))))))
    (cond
      (match
       (setq cnst (cdr (assoc 'cnst match))
             a    (cdr (assoc 'a match))
             b    (cdr (assoc 'b match))
             mc   (cdr (assoc 'mc match))
             ms   (cdr (assoc 'ms match)))
       (when (eql 0 ms)
         (setq b a))
       (when (eql 0 mc)
         (setq a b))
       (if (or (alike1 a b) (eq t (meqp a 0)))
           (values cnst a mc ms)
           nil))
      (t nil))))

(defun powers-sin-cos-integrate (e x)
  (multiple-value-bind (cnst a mc ms) (match-cos^m-sin^n e x)
 
    (cond
       ((null cnst) nil)

       ((eq t (meqp a 0)) nil) ;impossible?
    
       ((and (eql mc -1) (eql ms -1)) 
           (div (mul -1 cnst (ftake '%atanh (ftake '%cos (mul 2 a x)))) a))

          ((eq ms -1)
           (div (mul 
                  cnst
                  -1 
                 (ftake 'mexpt (ftake '%cos (mul a x)) (add 1 mc))
                  (ftake '%hypergeometric (ftake 'mlist 1 (div (add 1 mc) 2))
                                          (ftake 'mlist (div (add 3 mc) 2))
                                          x))
                (mul a (add 1 mc))))
          (t 
            (div (mul 
                   cnst
                   (ftake 'mexpt (ftake '%sin (mul a x)) (add 1 ms))
                   (ftake '%hypergeometric (ftake 'mlist (div (sub 1 mc) 2) (div (add 1 ms) 2))
                                           (ftake 'mlist (div (add 3 ms) 2))
                                           (ftake 'mexpt (ftake '%sin (mul a x)) 2)))
                 (mul a (add 1 ms)))))))
