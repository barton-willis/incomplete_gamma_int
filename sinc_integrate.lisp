#| Author: Barton Willis
   March 2025

Maxima code for integration of expressions of the form cnst sin\cos(xi)^m / q^n with respect to x, 
where xi and q are affine functions of x, m and n are positive integers, and cnst is free of x. The
antiderivative is expressed in terms of Maxima's expintegral_si and expintegral_ci functions.

And support for expressions of the form cnst x^m sin\cos(a + bx + cx^2)^n with respect to x, where a,b,c, 
and cnst are free of x and m is a positive integer. The antiderivative is expressed in terms of Maxima's 
fresnel_si and fresnel_ci functions.
|#

(in-package :maxima)

;; I should use m2-b*x+a (defined in sin.lisp), but older Maxima versions used a global for
;; the second argument of this function, so I'll supply a version of this function with a 
;; different name--this should allow older Maxima versions to use this code.
;; Pattern to match b*x + a
(defun m2-linear (expr var2)
  (setq expr ($expand expr)) ; needed for things like (4*x + 5)/7
  (m2 expr
      `((mplus)
        ((coeffpt) (b freevar2 ,var2) (x varp2 ,var2))
        ((coeffpt) (a freevar2 ,var2)))))

;; Only for testing--not intended to be a user level function
(defmfun $sinc_integrate (e x)
  (sinc-cosc-integrate e x))

(defun sinc-cosc-integrate (e x)
 " When `e` has the form `cnst cos\sin(xi)^m / q^n`, where `m` & `n` are positive integers and `xi` 
   and `q` are affine functions of `x`, return an antiderivative of `e` with respect to `x`; otherwise, 
   return nil"
  (setq e ($factor e))
  (or 
    (sinc-integrate e x)
    (cosc-integrate e x)))

(defun sinc-integrate (e x)
"When `e` has the form `cnst sin(xi)^m / q^n`, where `m` & `n` are positive integers and `xi` 
 and `q` are affine functions of `x`, return an antiderivative of `e` with respect to `x`; otherwise, 
 return nil"
  (let ((match nil) (a nil) (b nil) (c nil) (d nil) (disc nil) (ee))
    ;; Match and extract parameters
    (multiple-value-bind (cnst xi m q n) (match-sinc-cosc e '%sin x)

    (setq n (neg n))
    ;; Check if both xi and q are linear
    (setq match (if cnst (m2-linear xi x) nil))
    (when match
      (setq a (cdr (assoc 'a match :test #'eq)))
      (setq b (cdr (assoc 'b match :test #'eq)))
      (setq match (m2-linear q x))
      (when match
        (setq c (cdr (assoc 'a match :test #'eq)))
        (setq d (cdr (assoc 'b match :test #'eq)))))

    ;; Antiderivative calculation
    (cond
     ((and match (eql m 0)) (let (($logabs nil)) ($integrate e x)))
     ((null match) nil)
     ((or (not (integerp m)) (not (integerp n))) nil)

     ((or (not (integer-length m)) (not (integer-length n))) nil)
     ((or (not match) (not m) (not n)) nil)
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
"When `e` has the form `cnst cos(xi)^m / q^n`, where `m` & `n` are positive integers and `xi` 
 and `q` are affine functions of `x`, return an antiderivative of `e` with respect to `x`; otherwise, 
 return nil"
  (let ((match nil) (a nil) (b nil) (c nil) (d nil) (disc nil) (ee))
    ;; Match and extract parameters
    (multiple-value-bind (cnst xi m q n) (match-sinc-cosc e '%cos x)
      (setq n (neg n))
    ;; Extract parameters if match is found
    (when match
      (setq cnst (cdr (assoc 'cnst match :test #'eq))
            n (mul -1 (cdr (assoc 'n match :test #'eq)))
            q (cdr (assoc 'q match :test #'eq))
            xi (cdr (assoc 'xi match :test #'eq))
            m (cdr (assoc 'm match :test #'eq))))

    ;; Check if both `xi` and `q` are linear
    (setq match (if (and xi q) (m2-linear xi x) nil))
    (when match
      (setq a (cdr (assoc 'a match :test #'eq)))
      (setq b (cdr (assoc 'b match :test #'eq)))
      (setq match (m2-linear q x))
      (when match
        (setq c (cdr (assoc 'a match :test #'eq)))
        (setq d (cdr (assoc 'b match :test #'eq)))))

    ;; Compute the antiderivative for the integrand
    (cond
     ((and match (eql m 0)) (let (($logabs nil)) ($integrate e x))) ; Handle the case where m = 0
     ((null match) nil)
     ((or (not (integerp m)) (not (integerp n))) nil)
     ((eql m 0) ($integrate e x)) ; Handle the case where m = 0
      ((or (not (integer-length m)) (not (integer-length n))) nil)
     ((or (not match) (not m) (not n)) nil) ; Exit if invalid
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
  (freeof x e))

(defun notfreeof (e x)
  (not (freeof x e)))

(defun nonnegative-integer-p (n)
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
                                   ((coeffpt) (c freevar2 ,x) ((mexpt) (x varp2 ,x) 2))
                                   ((coeffpt) (b freevar2 ,x) (z varp2 ,x))
                                   ((coeffpt) (a freevar2 ,x))))
                                (n nonnegative-integer-p))))))
    (if match
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

;; To match both sin(1+x)/(1+x) and sin(1-x)/(1-x), both patterns are needed; similarly
;; for m2-cosc.  Possibly this function should be rewritten to make it less dependent 
;;on term ordering, but until it is shown to be broken, let's let it be.

(defun match-sinc-cosc (e fn x)
  "Match `e` to `cnst * sin(xi)^m / q^n`, where `cnst` is free of `x`,
   both `xi` and `q` depend on `x`, and `m` and `n` are integers."
  (let ((cnst) (xi) (m) (q) (n)
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
            n    (cdr (assoc 'n match))))

    (when (null q)
      (setq q 1))

    (when (null xi)
      (setq xi (div '$%pi 2))
      (setq m 0))

    (values cnst xi m q n)))