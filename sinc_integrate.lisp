#| Author: Barton Willis
   March 2025

Maxima code for integration of expressions of the form cnst sin\cos(xi)^m / q^n with respect to x, where
xi and q are affine functions of x, m and n are positive integers, and cnst is free of x. |#

(in-package :maxima)

;; Only for testing--not intended to be a user level function
(defmfun $sinc_integrate (e x)
  (sinc-cosc-integrate e x))

(defun sinc-cosc-integrate (e x)
 " When `e` has the form `cnst cos\sin(xi)^m / q^n`, where `m` & `n` are positive integers and `xi` 
   and `q` are affine functions of `x`, return an antiderivative of `e` with respect to `x`; otherwise, 
   return nil"
  (or 
    (sinc-integrate e x)
    (cosc-integrate e x)))

(defun sinc-integrate (e x)
"When `e` has the form `cnst sin(xi)^m / q^n`, where `m` & `n` are positive integers and `xi` 
 and `q` are affine functions of `x`, return an antiderivative of `e` with respect to `x`; otherwise, 
 return nil"
  (let ((match (m2-sinc e x))
        (cnst) (n) (q) (xi) (m)
        (a nil) (b nil) (c nil) (d nil)
        (disc nil) (ee))
    
    ;; Match and extract parameters
    (when match
      (setq cnst (cdr (assoc 'cnst match :test #'eq))
            n (mul -1 (cdr (assoc 'n match :test #'eq)))
            q (cdr (assoc 'q match :test #'eq))
            xi (cdr (assoc 'xi match :test #'eq))
            m (cdr (assoc 'm match :test #'eq))))

    ;; Check if both xi and q are linear
    (setq match (if (and xi q) (m2-b*x+a xi x) nil))
    (when match
      (setq a (cdr (assoc 'a match :test #'eq)))
      (setq b (cdr (assoc 'b match :test #'eq)))
      (setq match (m2-b*x+a q x))
      (when match
        (setq c (cdr (assoc 'a match :test #'eq)))
        (setq d (cdr (assoc 'b match :test #'eq)))))

    ;; Antiderivative calculation
    (cond
     ((eql m 0) ($integrate e x))
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
                              (add (div (mul b c) d) (mul b x))))))))))))

(defun cosc-integrate (e x)
"When `e` has the form `cnst cos(xi)^m / q^n`, where `m` & `n` are positive integers and `xi` 
 and `q` are affine functions of `x`, return an antiderivative of `e` with respect to `x`; otherwise, 
 return nil"
  (let ((match (m2-cosc e x))
        (cnst) (n) (q) (xi) (m)
        (a nil) (b nil) (c nil) (d nil)
        (disc nil) (ee))

    ;; Extract parameters if match is found
    (when match
      (setq cnst (cdr (assoc 'cnst match :test #'eq))
            n (mul -1 (cdr (assoc 'n match :test #'eq)))
            q (cdr (assoc 'q match :test #'eq))
            xi (cdr (assoc 'xi match :test #'eq))
            m (cdr (assoc 'm match :test #'eq))))

    ;; Check if both `xi` and `q` are linear
    (setq match (if (and xi q) (m2-b*x+a xi x) nil))
    (when match
      (setq a (cdr (assoc 'a match :test #'eq)))
      (setq b (cdr (assoc 'b match :test #'eq)))
      (setq match (m2-b*x+a q x))
      (when match
        (setq c (cdr (assoc 'a match :test #'eq)))
        (setq d (cdr (assoc 'b match :test #'eq)))))

    ;; Compute the antiderivative for the integrand
    (cond
     ((eql m 0) ($integrate e x)) ; Handle the case where m = 0
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
                                   (mul b x))))))))))))

(defun myfreeof (e x)
  "Checks whether the expression `e` is free of the variable `x`."
  (freeof x e))

(defun notfreeof (e x)
  "Checks whether the expression `e` does not contain the variable `x`."
  (not (freeof x e)))

(defun m2-sinc (e x)
  "Match `e` to `cnst * sin(xi)^m / q^n`, where `cnst` is free of `x`, 
   both `xi` and `q` depend on `x`, and `m` and `n` are integers."
  (or (m2 e `((mtimes)
              ((coefftt) (cnst myfreeof ,x))
              ((mexpt) (q notfreeof ,x) (n integerp))
              ((mexpt) ((%sin) (xi notfreeof ,x)) (m integerp))))
      (m2 e `((mtimes)
              ((coefftt) (cnst myfreeof ,x))
              ((mexpt) ((%sin) (xi notfreeof ,x)) (m integerp))
              ((mexpt) (q notfreeof ,x) (n integerp))))))

(defun m2-cosc (e x)
  "Match `e` to `cnst * cos(xi)^m / q^n`, where `cnst` is free of `x`, 
   both `xi` and `q` depend on `x`, and `m` and `n` are integers."
  (or (m2 e `((mtimes)
              ((coefftt) (cnst myfreeof ,x))
              ((mexpt) (q notfreeof ,x) (n integerp))
              ((mexpt) ((%cos) (xi notfreeof ,x)) (m integerp))))
      (m2 e `((mtimes)
              ((coefftt) (cnst myfreeof ,x))
              ((mexpt) ((%cos) (xi notfreeof ,x)) (m integerp))
              ((mexpt) (q notfreeof ,x) (n integerp))))))

   