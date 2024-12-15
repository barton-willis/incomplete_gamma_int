(defmfun $quotify (e &rest lst)
    (dolist (p lst)
        (setq e (maxima-substitute (ftake 'mquote p) p e)))
    e)

(defmfun $unquotify (e &rest lst)
    (dolist (p lst)
        (setq e (maxima-substitute p (ftake 'mquote p) e)))
    e)