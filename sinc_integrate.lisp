(in-package :maxima)

(defmfun $sinc_integrate (e x)
  (sinc-cosc-integrate e x))

(defun sinc-cosc-integrate (e x)
  (or 
    (sinc-integrate e x)
    (cosc-integrate e x)))

(defun sinc-integrate (e x)
    (let ((match (m2-sinc e x)) (cnst) (n) (q) (xi) (m) (a nil) (b nil) 
          (c nil) (d nil) (disc nil) (ee))
        
        (when match
           (setq cnst (cdr (assoc 'cnst match :test #'eq))
                 n (mul -1 (cdr (assoc 'n match :test #'eq)))
                 q (cdr (assoc 'q match :test #'eq))   
                 xi (cdr (assoc 'xi match :test #'eq))
                 m (cdr (assoc 'm match :test #'eq))))
        ;; Are both xi and q linear ?
        (setq match (if (and xi q) (m2-b*x+a xi x) nil))
        (when match
          (setq a (cdr (assoc 'a match :test #'eq)))
          (setq b (cdr (assoc 'b match :test #'eq)))
          (setq match (m2-b*x+a q x))
          (when match
            (setq c (cdr (assoc 'a match :test #'eq)))
            (setq d (cdr (assoc 'b match :test #'eq)))))

        ;; We need an antiderivative of 
        ;;   cnst sin(a + b x)^n / (c + d x)^m
        ;; Here it is
        (cond 
              ((eql m 0) ($integrate e x))
              ((or (not match) (not m) (not n)) nil)
              ((or (< m 0) (< n 0)) nil) ;give up
              ((>= m 2) 
                (setq ee ($expand (mfuncall '$trigrat e)))
                (mul cnst (fapply 'mplus (mapcar #'(lambda (s) (sinc-cosc-integrate s x)) (cdr ee)))))
              
              ((> n 1)
                (mul cnst 
                     (sub (div (ftake '%sin xi) (mul d (sub 1 n) (ftake 'mexpt q (sub n 1))))
                          (mul (div b (mul d (sub 1 n))) 
                             (sinc-cosc-integrate (div (ftake '%cos xi) (ftake 'mexpt q (sub n 1))) x)))))
 
              (t
                (setq disc (div (sub (mul a d) (mul b c)) d))
                (cond ((eq t (meqp disc 0))
                         ;SinIntegral[(b c)/d + b x]/d
                      (div 
                         (mul cnst (ftake '%expintegral_si (add (div (mul b c) d) (mul b x))))
                         d))
                      (t
                (mul 
                   (div cnst d)
                   (add 
                      (mul 
                        (ftake '%sin disc)
                        (ftake '%expintegral_ci (add (div (mul b c) d) (mul b x))))
                      (mul 
                        (ftake '%cos disc)
                        (ftake '%expintegral_si (add (div (mul b c) d) (mul b x))))))))))))  

(defun cosc-integrate (e x)
    (let ((match (m2-cosc e x)) (cnst) (n) (q) (xi) (m) (a nil) (b nil) 
          (c nil) (d nil) (disc nil) (ee))
        
        (when match
           (setq cnst (cdr (assoc 'cnst match :test #'eq))
                 n (mul -1 (cdr (assoc 'n match :test #'eq)))
                 q (cdr (assoc 'q match :test #'eq))   
                 xi (cdr (assoc 'xi match :test #'eq))
                 m (cdr (assoc 'm match :test #'eq))))
        ;; Are both xi and q linear ?
        (setq match (if (and xi q) (m2-b*x+a xi x) nil))
        (when match
          (setq a (cdr (assoc 'a match :test #'eq)))
          (setq b (cdr (assoc 'b match :test #'eq)))
          (setq match (m2-b*x+a q x))
          (when match
            (setq c (cdr (assoc 'a match :test #'eq)))
            (setq d (cdr (assoc 'b match :test #'eq)))))

        ;; We need an antiderivative of 
        ;;   cnst cos(a + b x)^n / (c + d x)^m
        ;; Here it is
        (cond 
              ((eql m 0) ($integrate e x))
              ((or (not match) (not m) (not n)) nil)
              ((or (< m 0) (< n 0)) nil) ;give up
              ((eql m 0) ($integrate e x))
              ((>= m 2) 
                (setq ee ($expand (mfuncall '$trigrat e)))
                (fapply 'mplus (mapcar #'(lambda (s) (sinc-cosc-integrate s x)) (cdr ee))))
              
              ((> n 1) ;; recursion!
                (mul cnst 
                     (add (div (ftake '%cos xi) (mul d (sub 1 n) (ftake 'mexpt q (sub n 1))))
                          (mul (div b (mul d (sub 1 n))) 
                             (sinc-integrate (div (ftake '%sin xi) (ftake 'mexpt q (sub n 1))) x)))))
 
              (t
                (setq disc (div (sub (mul a d) (mul b c)) d))

                ;(CosIntegral[(b c)/d + b x] Sin[a - (b c)/d] + 
                ;Cos[a - (b c)/d] SinIntegral[(b c)/d + b x])/d
                (cond ((eq t (meqp disc 0))
                         ;CosIntegral[(b c)/d + b x]/d
                      (div 
                         (mul cnst (ftake '%expintegral_ci (add (div (mul b c) d) (mul b x))))
                         d))
                      (t

                ;; (Cos[a - (b c)/d] CosIntegral[(b c)/d + b x] - Sin[a - (b c)/d] SinIntegral[(b c)/d + b x])/d
                (mul 
                   (div cnst d)
                   (sub
                      (mul 
                        (ftake '%cos disc)
                        (ftake '%expintegral_ci (add (div (mul b c) d) (mul b x))))
                      (mul 
                        (ftake '%sin disc)
                        (ftake '%expintegral_si (add (div (mul b c) d) (mul b x)))))))))))) 

(defun myfreeof (e x)
    (freeof x e))

(defun notfreeof (e x)
  (not (freeof x e)))

(defun m2-sinc (e x)
  "Match e to cnst * sin(xi)^m / q^n, where cnst is free of x, both xi and q depend on x,
  and m and n are integers."
  (or (m2 e `((mtimes) ((coefftt) (cnst myfreeof ,x)) 
                   ((mexpt) (q notfreeof ,x) (n integerp))
                   ((mexpt) ((%sin) (xi notfreeof ,x)) (m integerp))))
      (m2 e `((mtimes) ((coefftt) (cnst myfreeof ,x)) 
                   ((mexpt) ((%sin) (xi notfreeof ,x)) (m integerp))
                   ((mexpt) (q notfreeof ,x) (n integerp))))))
 
(defun m2-cosc (e x)
  "Match e to cnst * cos(xi)^m / q^n, where cnst is free of x, both xi and q depend on x,
  and m and n are integers."
  (or (m2 e `((mtimes) ((coefftt) (cnst myfreeof ,x)) 
                   ((mexpt) (q notfreeof ,x) (n integerp))
                   ((mexpt) ((%cos) (xi notfreeof ,x)) (m integerp))))                   
      (m2 e `((mtimes) ((coefftt) (cnst myfreeof ,x))                
                   ((mexpt) ((%cos) (xi notfreeof ,x)) (m integerp))
                   ((mexpt) (q notfreeof ,x) (n integerp))))))

   