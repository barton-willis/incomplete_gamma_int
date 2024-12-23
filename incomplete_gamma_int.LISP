;;; -*- Mode: Lisp; package:maxima; syntax:common-lisp ;Base: 10 -*- ;;;

; Translated on: 2024-12-14 04:12:48-06:00
; Maxima version: 5.47.0
; Lisp implementation: SBCL
; Lisp version: 2.3.2
;
; Translator state vars:
;
;   translate_fast_arrays: false;
;   tr_function_call_default: general;
;   tr_bound_function_applyp: true;
;   tr_array_as_ref: true;
;   tr_numer: false;
;   tr_float_can_branch_complex: true;
;   define_variable: false;

(in-package :maxima)

(SIMPLIFY ($LOAD (TRD-MSYMEVAL $RATPOW '$RATPOW)))
(PROGN
 (DEFPROP $MY_INT T TRANSLATED)
 (ADD2LNC '$MY_INT $PROPS)
 (DEFMTRFUN ($MY_INT $ANY MDEFINE NIL NIL)
      ($E $X)
    (DECLARE (SPECIAL $X $E))
    ((LAMBDA ($ANTID $METHODS)
       (DECLARE (SPECIAL $METHODS $ANTID))
       (LET ()
         (DECLARE (SPECIAL $METHODS))
         (IF (NOT (BOUNDP '$METHODS))
             (ADD2LNC '$METHODS $VALUES))
         (SETQ $METHODS
                 (LIST '(MLIST) '$INCOMPLETE_GAMMA_INT '$HYPERGEOMETRIC_INT)))
       (MEVAL
        '((MDOIN) $FN $METHODS NIL NIL NIL
          ((MNOT
            (12.
             #A((107.) BASE-CHAR
                . "C:/Users/barto/OneDrive/Documents/GitHub/incomplete_gamma_int/incomplete_gamma_int/incomplete_gamma_int.mac")
             SRC))
           ((MEQUAL
             (12.
              #A((107.) BASE-CHAR
                 . "C:/Users/barto/OneDrive/Documents/GitHub/incomplete_gamma_int/incomplete_gamma_int/incomplete_gamma_int.mac")
              SRC))
            $ANTID NIL))
          ((MSETQ
            (13.
             #A((107.) BASE-CHAR
                . "C:/Users/barto/OneDrive/Documents/GitHub/incomplete_gamma_int/incomplete_gamma_int/incomplete_gamma_int.mac")
             SRC))
           $ANTID
           (($FN
             (13.
              #A((107.) BASE-CHAR
                 . "C:/Users/barto/OneDrive/Documents/GitHub/incomplete_gamma_int/incomplete_gamma_int/incomplete_gamma_int.mac")
              SRC))
            $E $X))))
       $ANTID)
     NIL '$METHODS)
    ))
(PROGN
 (DEFPROP $SOLVE_SPECIAL_ENVIRONMENT T TRANSLATED)
 (ADD2LNC '$SOLVE_SPECIAL_ENVIRONMENT $PROPS)
 (DEFMTRFUN ($SOLVE_SPECIAL_ENVIRONMENT $ANY MDEFINE NIL NIL)
      ($E $X)
    (DECLARE (SPECIAL $X $E))
    ((LAMBDA
         ($PROGRAMMODE $BACKSUBST $REALONLY $BREAKUP $SOLVEEXPLICIT
          $SOLVENULLWARN $SOLVEFACTORS $SOLVERADCAN $SOLVETRIGWARN
          $SOLVEDECOMPOSES $GLOBALSOLVE)
       (DECLARE
        (SPECIAL $GLOBALSOLVE $SOLVEDECOMPOSES $SOLVETRIGWARN $SOLVERADCAN
         $SOLVEFACTORS $SOLVENULLWARN $SOLVEEXPLICIT $BREAKUP $REALONLY
         $BACKSUBST $PROGRAMMODE))
       (SIMPLIFY ($SOLVE $E $X)))
     T T NIL T T NIL T T NIL T NIL)
    ))
(PROGN
 (DEFPROP $SAFE_OP T TRANSLATED)
 (ADD2LNC '$SAFE_OP $PROPS)
 (DEFMTRFUN ($SAFE_OP $ANY MDEFINE NIL NIL)
      ($E)
    (DECLARE (SPECIAL $E))
    ((LAMBDA ($INFLAG)
       (DECLARE (SPECIAL $INFLAG))
       (COND (($MAPATOM $E) NIL) (T (SIMPLIFY ($OP $E)))))
     T)
    ))
(PROGN
 (DEFPROP $LOGDIFF T TRANSLATED)
 (ADD2LNC '$LOGDIFF $PROPS)
 (DEFMTRFUN ($LOGDIFF $ANY MDEFINE NIL NIL)
      ($E $X)
    (DECLARE (SPECIAL $X $E))
    (DIV (SIMPLIFY ($DIFF $E $X)) $E)
    ))
(PROGN
 (DEFPROP $POLE_ORDER T TRANSLATED)
 (ADD2LNC '$POLE_ORDER $PROPS)
 (DEFMTRFUN ($POLE_ORDER $ANY MDEFINE NIL NIL)
      ($R $X)
    (DECLARE (SPECIAL $X $R))
    (ADD*
     (SIMPLIFY ($HIPOW (SIMPLIFY ($RATEXPAND (SIMPLIFY ($RATDENOM $R)))) $X))
     (*MMINUS
      (SIMPLIFY
       ($HIPOW (SIMPLIFY ($RATEXPAND (SIMPLIFY ($RATNUMER $R)))) $X))))
    ))
(PROGN
 (DEFPROP $DIGITS T TRANSLATED)
 (ADD2LNC '$DIGITS $PROPS)
 (DEFMTRFUN ($DIGITS $ANY MDEFINE NIL NIL)
      ($N $M $BASE)
    (DECLARE (SPECIAL $BASE $M $N))
    ((LAMBDA ($D)
       (DECLARE (SPECIAL $D))
       (DO (($K 1. (+ 1. $K)))
           ((LET (($PREDERROR T))
              ($IS-BOOLE-EVAL (SIMPLIFY (LIST '(MGREATERP) $K $M))))
            '$DONE)
         (DECLARE (SPECIAL $K))
         (LET ()
           (DECLARE (SPECIAL $N))
           (IF (NOT (BOUNDP '$N))
               (ADD2LNC '$N $VALUES))
           (SETQ $N (SIMPLIFY ($DIVIDE $N $BASE))))
         (MEVAL
          '(($PUSH
             (41.
              #A((107.) BASE-CHAR
                 . "C:/Users/barto/OneDrive/Documents/GitHub/incomplete_gamma_int/incomplete_gamma_int/incomplete_gamma_int.mac")
              SRC))
            (($SECOND
              (41.
               #A((107.) BASE-CHAR
                  . "C:/Users/barto/OneDrive/Documents/GitHub/incomplete_gamma_int/incomplete_gamma_int/incomplete_gamma_int.mac")
               SRC))
             $N)
            $D))
         (LET ()
           (DECLARE (SPECIAL $N))
           (IF (NOT (BOUNDP '$N))
               (ADD2LNC '$N $VALUES))
           (SETQ $N (SIMPLIFY ($FIRST $N)))))
       $D)
     '((MLIST)))
    ))
(PROGN
 (DEFPROP $INCOMPLETE_GAMMA_INT T TRANSLATED)
 (ADD2LNC '$INCOMPLETE_GAMMA_INT $PROPS)
 (DEFMTRFUN ($INCOMPLETE_GAMMA_INT $ANY MDEFINE NIL NIL)
      ($E $X)
    (DECLARE (SPECIAL $X $E))
    ((LAMBDA
         ($SIGMA $MU $KERNS $N |$n| $RESFUN $A $DE $EQS $SOL $Α $F $K $ANTID
          $ERRORMSG)
       (DECLARE
        (SPECIAL $ERRORMSG $ANTID $K $F $Α $SOL $EQS $DE $A $RESFUN |$n| $N
         $KERNS $MU $SIGMA)
        (FIXNUM $K))
       (LET ()
         (DECLARE (SPECIAL $SIGMA))
         (IF (NOT (BOUNDP '$SIGMA))
             (ADD2LNC '$SIGMA $VALUES))
         (SETQ $SIGMA
                 (SIMPLIFY
                  ($PARTFRAC
                   (SIMPLIFY
                    ($GFACTOR
                     (SIMPLIFY ($RATSIMP (SIMPLIFY ($LOGDIFF $E $X))))))
                   $X))))
       (LET ()
         (DECLARE (SPECIAL $KERNS))
         (IF (NOT (BOUNDP '$KERNS))
             (ADD2LNC '$KERNS $VALUES))
         (SETQ $KERNS
                 (COND
                  ((LIKE (SIMPLIFY ($SAFE_OP $SIGMA)) "+")
                   (SIMPLIFY ($ARGS $SIGMA)))
                  (T (LIST '(MLIST) $SIGMA)))))
       (LET ()
         (DECLARE (SPECIAL $KERNS))
         (IF (NOT (BOUNDP '$KERNS))
             (ADD2LNC '$KERNS $VALUES))
         (SETQ $KERNS
                 (SIMPLIFY
                  ($SUBLIST $KERNS
                            (M-TLAMBDA&ENV (($S) ($X) NIL)
                                           (DECLARE (SPECIAL $S))
                                           (SIMPLIFY
                                            (LIST '(MEQUAL)
                                                  (SIMPLIFY
                                                   ($POLE_ORDER $S $X))
                                                  1.)))))))
       (LET ()
         (DECLARE (SPECIAL $RESFN))
         (IF (NOT (BOUNDP '$RESFN))
             (ADD2LNC '$RESFN $VALUES))
         (SETQ $RESFN
                 (M-TLAMBDA&ENV (($Z $K) ($A $X) NIL) (DECLARE (SPECIAL $K $Z))
                                (COND ((LIKE $K 0.) 0.)
                                      (T
                                       (DIV
                                        (ADD* $Z
                                              (*MMINUS
                                               (SIMPLIFY
                                                ($LOGDIFF
                                                 (DIV 1.
                                                      (SIMPLIFY
                                                       ($RATDENOM $Z)))
                                                 $X))))
                                        (ADD* $A 1.)))))))
       (LET ()
         (DECLARE (SPECIAL $N))
         (IF (NOT (BOUNDP '$N))
             (ADD2LNC '$N $VALUES))
         (SETQ $N ($LENGTH $KERNS)))
       (LET ()
         (DECLARE (SPECIAL |$n|))
         (IF (NOT (BOUNDP '|$n|))
             (ADD2LNC '|$n| $VALUES))
         (SETQ |$n| (POWER 2. $N)))
       (DO ((MDO 1. (+ 1. MDO)))
           ((LET (($PREDERROR T))
              ($IS-BOOLE-EVAL
               (MEVAL
                '((MNOT
                   (59.
                    #A((107.) BASE-CHAR
                       . "C:/Users/barto/OneDrive/Documents/GitHub/incomplete_gamma_int/incomplete_gamma_int/incomplete_gamma_int.mac")
                    SRC))
                  ((MAND
                    (59.
                     #A((107.) BASE-CHAR
                        . "C:/Users/barto/OneDrive/Documents/GitHub/incomplete_gamma_int/incomplete_gamma_int/incomplete_gamma_int.mac")
                     SRC))
                   ((MLEQP
                     (59.
                      #A((107.) BASE-CHAR
                         . "C:/Users/barto/OneDrive/Documents/GitHub/incomplete_gamma_int/incomplete_gamma_int/incomplete_gamma_int.mac")
                      SRC))
                    $K |$n|)
                   ((MEQUAL
                     (59.
                      #A((107.) BASE-CHAR
                         . "C:/Users/barto/OneDrive/Documents/GitHub/incomplete_gamma_int/incomplete_gamma_int/incomplete_gamma_int.mac")
                      SRC))
                    $ANTID NIL))))))
            '$DONE)
         (DECLARE (SPECIAL MDO))
         (LET ()
           (DECLARE (SPECIAL $MU))
           (IF (NOT (BOUNDP '$MU))
               (ADD2LNC '$MU $VALUES))
           (SETQ $MU
                   (SIMPLIFY
                    ($XREDUCE "+"
                              (SIMPLIFY
                               (MAP1 (GETOPR (TRD-MSYMEVAL $RESFN '$RESFN))
                                     $KERNS (SIMPLIFY ($DIGITS $K $N 2.))))))))
         (LET ()
           (DECLARE (SPECIAL $K))
           (IF (NOT (BOUNDP '$K))
               (ADD2LNC '$K $VALUES))
           (SETQ $K (+ $K 1.)))
         (LET ()
           (DECLARE (SPECIAL $DE))
           (IF (NOT (BOUNDP '$DE))
               (ADD2LNC '$DE $VALUES))
           (SETQ $DE
                   (ADD*
                    (MUL* (POWER $MU 2.)
                          (ADD* (SIMPLIFY ($DIFF $SIGMA $X))
                                (*MMINUS (MUL* $MU $SIGMA))
                                (MUL* (ADD* $A 1.) (POWER $MU 2.))))
                    (MUL* $MU (ADD* $MU (*MMINUS $SIGMA))
                          (SIMPLIFY ($DIFF $MU $X)))
                    (MUL* (*MMINUS $MU) (SIMPLIFY ($DIFF $MU $X 2.)))
                    (MUL* 2. (POWER (SIMPLIFY ($DIFF $MU $X)) 2.)))))
         (LET ()
           (DECLARE (SPECIAL $EQS))
           (IF (NOT (BOUNDP '$EQS))
               (ADD2LNC '$EQS $VALUES))
           (SETQ $EQS (SIMPLIFY (MFUNCTION-CALL $RATP_DENSE_COEFFS $DE $X))))
         (LET ()
           (DECLARE (SPECIAL $EQS))
           (IF (NOT (BOUNDP '$EQS))
               (ADD2LNC '$EQS $VALUES))
           (SETQ $EQS (SIMPLIFY ($GFACTOR $EQS))))
         (LET ()
           (DECLARE (SPECIAL $SOL))
           (IF (NOT (BOUNDP '$SOL))
               (ADD2LNC '$SOL $VALUES))
           (SETQ $SOL
                   (SIMPLIFY
                    ($SOLVE_SPECIAL_ENVIRONMENT $EQS (LIST '(MLIST) $A)))))
         (COND
          ((AND (NOT (LIKE $SOL '((MLIST)))) (NOT (LIKE $SOL '$ALL)))
           (LET ()
             (DECLARE (SPECIAL $SOL))
             (IF (NOT (BOUNDP '$SOL))
                 (ADD2LNC '$SOL $VALUES))
             (SETQ $SOL (SIMPLIFY ($FIRST $SOL))))
           (LET ()
             (DECLARE (SPECIAL $F))
             (IF (NOT (BOUNDP '$F))
                 (ADD2LNC '$F $VALUES))
             (SETQ $F
                     (ADD* (*MMINUS (DIV $SIGMA $MU))
                           (DIV (SIMPLIFY ($DIFF $MU $X 1.)) (POWER $MU 2.)) $A
                           1.)))
           (LET ()
             (DECLARE (SPECIAL $F))
             (IF (NOT (BOUNDP '$F))
                 (ADD2LNC '$F $VALUES))
             (SETQ $F
                     (CONS '(MLIST)
                           (ERRCATCH
                            (PROGN
                             (SIMPLIFY
                              ($RATSIMP (SIMPLIFY ($SUBSTITUTE $SOL $F)))))))))
           (COND
            ((NOT (LIKE $F '((MLIST))))
             (LET ()
               (DECLARE (SPECIAL $F))
               (IF (NOT (BOUNDP '$F))
                   (ADD2LNC '$F $VALUES))
               (SETQ $F (SIMPLIFY ($FIRST $F))))
             (LET ()
               (DECLARE (SPECIAL $Α))
               (IF (NOT (BOUNDP '$Α))
                   (ADD2LNC '$Α $VALUES))
               (SETQ $Α
                       (SIMPLIFY
                        ($SUBSTITUTE $SOL
                                     (SIMPLIFY
                                      ($RATSIMP
                                       (DIV $E
                                            (MUL* (SIMPLIFY ($DIFF $F $X))
                                                  (POWER $F $A)
                                                  (SIMPLIFY
                                                   (LIST '(%EXP)
                                                         (*MMINUS $F)))))))))))
             (LET ()
               (DECLARE (SPECIAL $Α))
               (IF (NOT (BOUNDP '$Α))
                   (ADD2LNC '$Α $VALUES))
               (SETQ $Α
                       ((LAMBDA ($ROOTSCONMODE)
                          (DECLARE (SPECIAL $ROOTSCONMODE))
                          (SIMPLIFY ($ROOTSCONTRACT $Α)))
                        '$ALL)))
             (COND
              ((NOT ($FREEOF $Α $X))
               ($PRINT "unable to show that " $Α " is piecewise constant")))
             (LET ()
               (DECLARE (SPECIAL $ANTID))
               (IF (NOT (BOUNDP '$ANTID))
                   (ADD2LNC '$ANTID $VALUES))
               (SETQ $ANTID
                       (SIMPLIFY
                        ($FACTOR
                         (MUL* (*MMINUS $Α)
                               (SIMPLIFY
                                (LIST '(%GAMMA_INCOMPLETE)
                                      (SIMPLIFY
                                       ($SUBSTITUTE $SOL (ADD* $A 1.)))
                                      $F))))))))))))
       $ANTID)
     '$SIGMA '$MU '$KERNS '$N '|$n| '$RESFUN (SIMPLIFY ($GENSYM)) '$DE '$EQS
     '$SOL '$Α '$F 1. NIL NIL)
    ))
(PROGN
 (DEFPROP $HYPERGEOMETRIC_INT T TRANSLATED)
 (ADD2LNC '$HYPERGEOMETRIC_INT $PROPS)
 (DEFMTRFUN ($HYPERGEOMETRIC_INT $ANY MDEFINE NIL NIL)
      ($E $X)
    (DECLARE (SPECIAL $X $E))
    ((LAMBDA
         ($SIGMA $MU $KERNS $N |$n| $RESFUN $A $B $DE $EQS $SOL $Α $F $K $ΑΑ
          $AA $BB $FF $ANTID $ERRORMSG)
       (DECLARE
        (SPECIAL $ERRORMSG $ANTID $FF $BB $AA $ΑΑ $K $F $Α $SOL $EQS $DE $B $A
         $RESFUN |$n| $N $KERNS $MU $SIGMA)
        (FIXNUM $K))
       (LET ()
         (DECLARE (SPECIAL $SIGMA))
         (IF (NOT (BOUNDP '$SIGMA))
             (ADD2LNC '$SIGMA $VALUES))
         (SETQ $SIGMA
                 (SIMPLIFY
                  ($PARTFRAC (SIMPLIFY ($GFACTOR (SIMPLIFY ($LOGDIFF $E $X))))
                             $X))))
       (LET ()
         (DECLARE (SPECIAL $KERNS))
         (IF (NOT (BOUNDP '$KERNS))
             (ADD2LNC '$KERNS $VALUES))
         (SETQ $KERNS
                 (COND
                  ((LIKE (SIMPLIFY ($SAFE_OP $SIGMA)) "+")
                   (SIMPLIFY ($ARGS $SIGMA)))
                  (T (LIST '(MLIST) $SIGMA)))))
       (LET ()
         (DECLARE (SPECIAL $KERNS))
         (IF (NOT (BOUNDP '$KERNS))
             (ADD2LNC '$KERNS $VALUES))
         (SETQ $KERNS
                 (SIMPLIFY
                  ($SUBLIST $KERNS
                            (M-TLAMBDA&ENV (($S) ($X) NIL)
                                           (DECLARE (SPECIAL $S))
                                           (SIMPLIFY
                                            (LIST '(MEQUAL)
                                                  (SIMPLIFY
                                                   ($POLE_ORDER $S $X))
                                                  1.)))))))
       (LET ()
         (DECLARE (SPECIAL $RESFN))
         (IF (NOT (BOUNDP '$RESFN))
             (ADD2LNC '$RESFN $VALUES))
         (SETQ $RESFN
                 (M-TLAMBDA&ENV (($Z $K) ($X $B $A) NIL)
                                (DECLARE (SPECIAL $K $Z))
                                (LET ()
                                  (DECLARE (SPECIAL $Z))
                                  (IF (NOT (BOUNDP '$Z))
                                      (ADD2LNC '$Z $VALUES))
                                  (SETQ $Z
                                          (ADD* $Z
                                                (*MMINUS
                                                 (SIMPLIFY
                                                  ($LOGDIFF $Z $X))))))
                                (COND ((LIKE $K 0.) 0.)
                                      ((LIKE $K 1.) (DIV $Z (ADD* $A 1.)))
                                      (T (DIV $Z (ADD* 1. $A $B)))))))
       (LET ()
         (DECLARE (SPECIAL $N))
         (IF (NOT (BOUNDP '$N))
             (ADD2LNC '$N $VALUES))
         (SETQ $N ($LENGTH $KERNS)))
       (LET ()
         (DECLARE (SPECIAL |$n|))
         (IF (NOT (BOUNDP '|$n|))
             (ADD2LNC '|$n| $VALUES))
         (SETQ |$n| (POWER 3. $N)))
       (DO ((MDO 1. (+ 1. MDO)))
           ((LET (($PREDERROR T))
              ($IS-BOOLE-EVAL
               (MEVAL
                '((MNOT
                   (92.
                    #A((107.) BASE-CHAR
                       . "C:/Users/barto/OneDrive/Documents/GitHub/incomplete_gamma_int/incomplete_gamma_int/incomplete_gamma_int.mac")
                    SRC))
                  ((MAND
                    (92.
                     #A((107.) BASE-CHAR
                        . "C:/Users/barto/OneDrive/Documents/GitHub/incomplete_gamma_int/incomplete_gamma_int/incomplete_gamma_int.mac")
                     SRC))
                   ((MLEQP
                     (92.
                      #A((107.) BASE-CHAR
                         . "C:/Users/barto/OneDrive/Documents/GitHub/incomplete_gamma_int/incomplete_gamma_int/incomplete_gamma_int.mac")
                      SRC))
                    $K |$n|)
                   ((MEQUAL
                     (92.
                      #A((107.) BASE-CHAR
                         . "C:/Users/barto/OneDrive/Documents/GitHub/incomplete_gamma_int/incomplete_gamma_int/incomplete_gamma_int.mac")
                      SRC))
                    $ANTID NIL))))))
            '$DONE)
         (DECLARE (SPECIAL MDO))
         (LET ()
           (DECLARE (SPECIAL $MU))
           (IF (NOT (BOUNDP '$MU))
               (ADD2LNC '$MU $VALUES))
           (SETQ $MU
                   (SIMPLIFY
                    ($XREDUCE "+"
                              (SIMPLIFY
                               (MAP1 (GETOPR (TRD-MSYMEVAL $RESFN '$RESFN))
                                     $KERNS (SIMPLIFY ($DIGITS $K $N 3.))))))))
         (LET ()
           (DECLARE (SPECIAL $K))
           (IF (NOT (BOUNDP '$K))
               (ADD2LNC '$K $VALUES))
           (SETQ $K (+ $K 1.)))
         (LET ()
           (DECLARE (SPECIAL $DE))
           (IF (NOT (BOUNDP '$DE))
               (ADD2LNC '$DE $VALUES))
           (SETQ $DE
                   (ADD*
                    (MUL* $B
                          (ADD*
                           (MUL* (POWER $MU 2.)
                                 (SIMPLIFY ($DIFF $SIGMA $X 1.)))
                           (*MMINUS
                            (MUL* $MU (SIMPLIFY ($DIFF $MU $X 1.)) $SIGMA))
                           (MUL* (*MMINUS $MU) (SIMPLIFY ($DIFF $MU $X 2.)))
                           (MUL* 2. (POWER (SIMPLIFY ($DIFF $MU $X 1.)) 2.))))
                    (MUL*
                     (ADD* (MUL* $MU $SIGMA)
                           (*MMINUS (SIMPLIFY ($DIFF $MU $X 1.)))
                           (MUL* (*MMINUS $A) (POWER $MU 2.))
                           (*MMINUS (POWER $MU 2.)))
                     (ADD* (MUL* $MU $SIGMA)
                           (*MMINUS (SIMPLIFY ($DIFF $MU $X 1.)))
                           (MUL* (*MMINUS $B) (POWER $MU 2.))
                           (MUL* (*MMINUS $A) (POWER $MU 2.))
                           (*MMINUS (POWER $MU 2.)))))))
         (LET ()
           (DECLARE (SPECIAL $DE))
           (IF (NOT (BOUNDP '$DE))
               (ADD2LNC '$DE $VALUES))
           (SETQ $DE (SIMPLIFY ($PARTFRAC (SIMPLIFY ($GFACTOR $DE)) $X))))
         (LET ()
           (DECLARE (SPECIAL $EQS))
           (IF (NOT (BOUNDP '$EQS))
               (ADD2LNC '$EQS $VALUES))
           (SETQ $EQS
                   (COND
                    ((LIKE (SIMPLIFY ($SAFE_OP $DE)) "+")
                     (SIMPLIFY ($ARGS $DE)))
                    (T (LIST '(MLIST) $DE)))))
         (LET ()
           (DECLARE (SPECIAL $EQS))
           (IF (NOT (BOUNDP '$EQS))
               (ADD2LNC '$EQS $VALUES))
           (SETQ $EQS
                   (SIMPLIFY
                    (MAP1 (GETOPR (TRD-MSYMEVAL $RATNUMER '$RATNUMER)) $EQS))))
         (LET ()
           (DECLARE (SPECIAL $EQS))
           (IF (NOT (BOUNDP '$EQS))
               (ADD2LNC '$EQS $VALUES))
           (SETQ $EQS
                   (SIMPLIFY
                    (MAP1
                     (GETOPR
                      (M-TLAMBDA&ENV (($S) ($X) NIL) (DECLARE (SPECIAL $S))
                                     (SIMPLIFY
                                      (MFUNCTION-CALL $RATP_DENSE_COEFFS $S
                                                      $X))))
                     $EQS))))
         (LET ()
           (DECLARE (SPECIAL $EQS))
           (IF (NOT (BOUNDP '$EQS))
               (ADD2LNC '$EQS $VALUES))
           (SETQ $EQS (SIMPLIFY ($XREDUCE '$APPEND $EQS))))
         (LET ()
           (DECLARE (SPECIAL $SOL))
           (IF (NOT (BOUNDP '$SOL))
               (ADD2LNC '$SOL $VALUES))
           (SETQ $SOL
                   (SIMPLIFY
                    ($SOLVE_SPECIAL_ENVIRONMENT $EQS (LIST '(MLIST) $A $B)))))
         (COND
          ((AND (NOT (LIKE $SOL '((MLIST)))) (NOT (LIKE $SOL '$ALL)))
           (LET ()
             (DECLARE (SPECIAL $SOL))
             (IF (NOT (BOUNDP '$SOL))
                 (ADD2LNC '$SOL $VALUES))
             (SETQ $SOL (SIMPLIFY ($FIRST $SOL))))
           (LET ()
             (DECLARE (SPECIAL $F))
             (IF (NOT (BOUNDP '$F))
                 (ADD2LNC '$F $VALUES))
             (SETQ $F
                     (DIV
                      (ADD* (MUL* $MU $SIGMA)
                            (*MMINUS (SIMPLIFY ($DIFF $MU $X 1.)))
                            (MUL* (ADD* (*MMINUS $A) -1.) (POWER $MU 2.)))
                      (ADD* (MUL* $MU $SIGMA)
                            (*MMINUS (SIMPLIFY ($DIFF $MU $X 1.)))
                            (MUL* (ADD* (*MMINUS $B) (*MMINUS $A) -1.)
                                  (POWER $MU 2.))))))
           (LET ()
             (DECLARE (SPECIAL $F))
             (IF (NOT (BOUNDP '$F))
                 (ADD2LNC '$F $VALUES))
             (SETQ $F
                     (CONS '(MLIST)
                           (ERRCATCH
                            (PROGN
                             (SIMPLIFY
                              ($RATSIMP (SIMPLIFY ($SUBSTITUTE $SOL $F)))))))))
           (COND
            ((NOT (LIKE $F '((MLIST))))
             (LET ()
               (DECLARE (SPECIAL $F))
               (IF (NOT (BOUNDP '$F))
                   (ADD2LNC '$F $VALUES))
               (SETQ $F (SIMPLIFY ($FIRST $F))))
             (LET ()
               (DECLARE (SPECIAL $Α))
               (IF (NOT (BOUNDP '$Α))
                   (ADD2LNC '$Α $VALUES))
               (SETQ $Α
                       (SIMPLIFY
                        ($SUBSTITUTE $SOL
                                     (SIMPLIFY
                                      ($RATSIMP
                                       (DIV $E
                                            (MUL* (SIMPLIFY ($DIFF $F $X))
                                                  (POWER $F $A)
                                                  (POWER (ADD* 1. (*MMINUS $F))
                                                         $B)))))))))
             (LET ()
               (DECLARE (SPECIAL $Α))
               (IF (NOT (BOUNDP '$Α))
                   (ADD2LNC '$Α $VALUES))
               (SETQ $Α
                       ((LAMBDA ($ROOTSCONMODE)
                          (DECLARE (SPECIAL $ROOTSCONMODE))
                          (SIMPLIFY ($ROOTSCONTRACT $Α)))
                        '$ALL)))
             (COND
              ((NOT ($FREEOF $Α $X))
               ($PRINT "unable to show that " $Α " is piecewise constant")))
             (MSET
              '((MLIST
                 (117.
                  #A((107.) BASE-CHAR
                     . "C:/Users/barto/OneDrive/Documents/GitHub/incomplete_gamma_int/incomplete_gamma_int/incomplete_gamma_int.mac")
                  SRC))
                $ΑΑ $AA $BB $FF)
              (SIMPLIFY ($SUBSTITUTE $SOL (LIST '(MLIST) $Α $A $B $F))))
             (LET (TR-GENSYM182)
               (COND
                ((EQ T
                     (SETQ TR-GENSYM182
                             (MCOND-BOOLE-VERIFY
                              (MNOT_TR
                               (MCOND-BOOLE-VERIFY
                                (MAND_TR ($INTEGERP $AA)
                                         (MCOND-BOOLE-VERIFY
                                          (MGQP 0. (ADD* 1. $AA)))))))))
                 (LET ()
                   (DECLARE (SPECIAL $ANTID))
                   (IF (NOT (BOUNDP '$ANTID))
                       (ADD2LNC '$ANTID $VALUES))
                   (SETQ $ANTID
                           (SIMPLIFY
                            ($FACTOR
                             (DIV
                              (MUL* $ΑΑ (POWER $F (ADD* 1. $AA))
                                    (SIMPLIFY
                                     (LIST '(%HYPERGEOMETRIC)
                                           (LIST '(MLIST) (ADD* 1. $AA)
                                                 (*MMINUS $BB))
                                           (LIST '(MLIST) (ADD* 2. $AA)) $F)))
                              (ADD* 1. $AA)))))))
                ((NOT (NULL TR-GENSYM182))
                 (LIST* '(MCOND) TR-GENSYM182
                        (MAPCAR #'MCOND-EVAL-SYMBOLS-TR
                                '(((MSETQ
                                    (120.
                                     #A((107.) BASE-CHAR
                                        . "C:/Users/barto/OneDrive/Documents/GitHub/incomplete_gamma_int/incomplete_gamma_int/incomplete_gamma_int.mac")
                                     SRC))
                                   $ANTID
                                   (($FACTOR
                                     (120.
                                      #A((107.) BASE-CHAR
                                         . "C:/Users/barto/OneDrive/Documents/GitHub/incomplete_gamma_int/incomplete_gamma_int/incomplete_gamma_int.mac")
                                      SRC))
                                    ((MQUOTIENT
                                      (120.
                                       #A((107.) BASE-CHAR
                                          . "C:/Users/barto/OneDrive/Documents/GitHub/incomplete_gamma_int/incomplete_gamma_int/incomplete_gamma_int.mac")
                                       SRC))
                                     ((MTIMES
                                       (120.
                                        #A((107.) BASE-CHAR
                                           . "C:/Users/barto/OneDrive/Documents/GitHub/incomplete_gamma_int/incomplete_gamma_int/incomplete_gamma_int.mac")
                                        SRC))
                                      $ΑΑ
                                      ((MEXPT
                                        (120.
                                         #A((107.) BASE-CHAR
                                            . "C:/Users/barto/OneDrive/Documents/GitHub/incomplete_gamma_int/incomplete_gamma_int/incomplete_gamma_int.mac")
                                         SRC))
                                       $F
                                       ((MPLUS
                                         (120.
                                          #A((107.) BASE-CHAR
                                             . "C:/Users/barto/OneDrive/Documents/GitHub/incomplete_gamma_int/incomplete_gamma_int/incomplete_gamma_int.mac")
                                          SRC))
                                        1. $AA))
                                      ((%HYPERGEOMETRIC
                                        (120.
                                         #A((107.) BASE-CHAR
                                            . "C:/Users/barto/OneDrive/Documents/GitHub/incomplete_gamma_int/incomplete_gamma_int/incomplete_gamma_int.mac")
                                         SRC))
                                       ((MLIST
                                         (120.
                                          #A((107.) BASE-CHAR
                                             . "C:/Users/barto/OneDrive/Documents/GitHub/incomplete_gamma_int/incomplete_gamma_int/incomplete_gamma_int.mac")
                                          SRC))
                                        ((MPLUS
                                          (120.
                                           #A((107.) BASE-CHAR
                                              . "C:/Users/barto/OneDrive/Documents/GitHub/incomplete_gamma_int/incomplete_gamma_int/incomplete_gamma_int.mac")
                                           SRC))
                                         1. $AA)
                                        ((MMINUS
                                          (120.
                                           #A((107.) BASE-CHAR
                                              . "C:/Users/barto/OneDrive/Documents/GitHub/incomplete_gamma_int/incomplete_gamma_int/incomplete_gamma_int.mac")
                                           SRC))
                                         $BB))
                                       ((MLIST
                                         (120.
                                          #A((107.) BASE-CHAR
                                             . "C:/Users/barto/OneDrive/Documents/GitHub/incomplete_gamma_int/incomplete_gamma_int/incomplete_gamma_int.mac")
                                          SRC))
                                        ((MPLUS
                                          (120.
                                           #A((107.) BASE-CHAR
                                              . "C:/Users/barto/OneDrive/Documents/GitHub/incomplete_gamma_int/incomplete_gamma_int/incomplete_gamma_int.mac")
                                           SRC))
                                         2. $AA))
                                       $F))
                                     ((MPLUS
                                       (120.
                                        #A((107.) BASE-CHAR
                                           . "C:/Users/barto/OneDrive/Documents/GitHub/incomplete_gamma_int/incomplete_gamma_int/incomplete_gamma_int.mac")
                                        SRC))
                                      1. $AA))))
                                  T $FALSE)))))))))))
       $ANTID)
     '$SIGMA '$MU '$KERNS '$N '|$n| '$RESFUN (SIMPLIFY ($GENSYM))
     (SIMPLIFY ($GENSYM)) '$DE '$EQS '$SOL '$Α '$F 1. '$ΑΑ '$AA '$BB '$FF NIL
     NIL)
    ))