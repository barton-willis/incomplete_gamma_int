(in-package :maxima)

(defmvar $use_appell_f1_integral_rep nil)

(def-simplifier appell_f1 (a b1 b2 c x y)
  (cond
    ((eql 0 y)
     (ftake '%hypergeometric (ftake 'mlist a b1) (ftake 'mlist c) x))

    ((eql 0 x)
     (ftake '%hypergeometric (ftake 'mlist a b2) (ftake 'mlist c) y))

    ((alike1 x y)
     (ftake '%hypergeometric (ftake 'mlist a (add b1 b2)) (ftake 'mlist c) x))

    ((alike1 (add a b1 b2) c)
     (ftake 'mexpt (sub 1 (add x y)) (mul -1 a)))

    ;; When all arguments are numbers and at least one is a binary64, use numerical evaluation.
    ((and (every #'mnump (list a b1 b2 c x y)) 
          (some #'floatp (list a b1 b2 c x y))
          (appell-f1-float a b1 b2 c x y)))
      
    ((great x y)
     (ftake '%appell_1 a b2 b1 c y x))

    ((alike1 y 1)
     (mul (ftake '%hypergeometric (ftake 'mlist a b2) (ftake 'mlist c) 1)
          (ftake '%hypergeometric (ftake 'mlist a b1) (ftake 'mlist (sub c b1)) x)))

    ((alike1 x (mul -1 x))
     (ftake '%hypergeometric
            (ftake (div (add a 1) 2) (div a 2) b1)
            (ftake 'mlist (add (add c 1) 2) (div c 2))
            (mul x x)))

    ;; http://dlmf.nist.gov/16.16.E1
    ((alike1 c (add b1 b2))
     (mul (ftake 'mexpt (sub 1 y) (mul -1 a))
          (ftake '%hypergeometric (ftake 'mlist a b1) (ftake 'mlist (add b1 b2))
                 (div (sub x y) (sub 1 y)))))

    ((and $use_appell_f1_integral_rep 
          (or (not (integerp c)) (< 0 c))
          (or (not (integerp a)) (< 0 a))
          (or (not (integerp (sub c a))) (< 0 (- c a))))
      (integral-rep-appell-f1 a b1 b2 c x y))

    (t (give-up))))

;; Integral representation
(defun integral-rep-appell-f1 (a b1 b2 c x y)
  (let ((z ($gensym)))
    (mul (div (ftake '%gamma c)
              (mul (ftake '%gamma a) (ftake '%gamma (sub c a))))
         (ftake '%integrate
                (mul (ftake 'mexpt z (sub a 1))
                     (ftake 'mexpt (sub 1 z) (add c (mul -1 a) -1))
                     (ftake 'mexpt (sub 1 (mul x z)) (mul -1 b1))
                     (ftake 'mexpt (sub 1 (mul y z)) (mul -1 b2)))
                z 0 1))))

;; Derivatives--we'll not attempt the derivatives with respect to the first four
;; arguments.
(defun diff-appell-f1-x (a b1 b2 c x y)
  (if (eql c 0)
      nil
      (div (mul a b1 (ftake '%appell_f1 (add 1 a) (add 1 b1) b2 (add 1 c) x y)) c)))

(defun diff-appell-f1-y (a b1 b2 c x y)
  (if (eql c 0)
      nil
      (div (mul a b2 (ftake '%appell_f1 (add 1 a) b1 (add 1 b2) (add 1 c) x y)) c)))

(defprop %appell_f1
  ((a b1 b2 c x y)
   nil
   nil
   nil
   nil
   diff-appell-f1-x
   diff-appell-f1-y)
  grad)

;; Antiderivatives
(defun integrate-appell-f1-x (a b1 b2 c x y)
  (div (mul (sub c 1) (ftake '%appell_f1 (sub a 1) (sub b1 1) b2 (sub c 1) x y))
       (mul (sub a 1) (sub b1 1))))

(defun integrate-appell-f1-y (a b1 b2 c x y)
  (div (mul (sub c 1) (ftake '%appell_f1 (sub a 1) b1 (sub b2 1) (sub c 1) x y))
       (mul (sub a 1) (sub b2 1))))

(defprop %appell_f1
  ((a b1 b2 c x y)
   nil
   nil
   nil
   nil
   integrate-appell-f1-x
   integrate-appell-f1-y)
  integral)

;; Use quad_qaws for floating point evaluation. 
(defun appell-f1-float (a b1 b2 c x y)
  (let ((s (gensym)) (g))
    (setq a ($float a)
          b1 ($float b1)
          b2 ($float b2)
          c ($float c)
          x ($float x)
          y ($float y))

    (setq g (errcatch ($quad_qaws (div 1 (mul (ftake 'mexpt (sub 1 (mul x s)) b1) (ftake 'mexpt (sub 1 (mul y s)) b2))) 
                s 0 1 (- a 1) (- c (+ a 1)) 1)))

     (setq g (first g))
    (if (eql 0 (fifth g))
       (div (mul (ftake '%gamma c) (second g)) 
          (mul (ftake '%gamma a) (ftake '%gamma (- c a))))
       nil)))
             