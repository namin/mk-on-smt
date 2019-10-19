(define smt-cmd "z3 -in")

(define-values (smt-out smt-in smt-err smt-p)
  (open-process-ports smt-cmd 'block (native-transcoder)))
(define (smt-reset!)
  (let-values (((out in err p)
                (open-process-ports smt-cmd 'block (native-transcoder))))
    (set! smt-out out)
    (set! smt-in in)
    (set! smt-err err)
    (set! smt-p p)))

(define (smt-read-sat)
  (let ([r (read smt-in)])
    (cond
      ((eq? r 'sat)
       #t)
      ((eq? r 'unsat)
       #f)
      ((eq? r 'unknown)
       (begin
         (printf "read-sat: unknown\n")
         #f))
      (else (error 'read-sat (format "~a" r))))))

(define (smt-call xs)
  (for-each
    (lambda (x)
      (printf "~s\n" x)
      (fprintf smt-out "~s\n" x))
    xs)
  (flush-output-port smt-out))

(define empty-state '())

(define-structure (closure id body env))
(define smt/check
  (lambda (st)
    (smt-call '((reset)))
    (smt-call '((declare-datatypes
                  ((SExp 0))
                  (((sbool   (s-bool Bool))
                    (sint    (s-int Int))
                    (sreal   (s-real Real))
                    (ssymbol (s-symbol String))
                    (sclosure (s-clo-id SExp) (s-clo-body SExp) (s-clo-env SExp))
                    (snil)
                    (scons   (s-car SExp) (s-cdr SExp)))))))
    (smt-call '((define-fun-rec closure-absent ((e SExp)) Bool
                  (if ((_ is sclosure) e) false
                      (if ((_ is scons) e) (and (closure-absent (s-car e)) (closure-absent (s-cdr e)))
                          true)))))
    (smt-call (reverse st))
    (smt-call '((check-sat)))
    (if (smt-read-sat)
        st
        #f)))

(define (smt/declare x)
  (lambda (ctx)
    (lambda (st)
      (cons `(declare-const ,(var-name x) SExp) st))))

(define (smt/assert e)
  (lambda (ctx)
    (lambda (st)
      (smt/check
       (cons `(assert ,e) st)))))

(define smt/purge
  (lambda (ctx)
    smt/check))

(define (smt/reset!)
  (set! var-count 0))

(define (reify q)
  (lambda (st)
    (smt/check st)
    (smt-call '((get-model)))
    (let ((ms (cdr (read smt-in))))
      (let ((r (car (filter (lambda (x) (eq? (cadr x) (var-name q))) ms))))
        (sinv (cadddr (cdr r)) '())))))

(define var-count 0)

(define (var)
  (set! var-count (+ 1 var-count))
  (vector
   (string->symbol (format #f "_v~a" var-count))
   var-count))

(define (var? x)
  (vector? x))

(define (var-name v)
  (vector-ref v 0))

(define (var-id v)
  (vector-ref v 1))

(define (s x)
  (cond
    ((eq? x #f) '(sbool false))
    ((eq? x #t) '(sbool true))
    ((number? x)
     (if (exact? x)
         `(sint ,x)
         `(sreal ,x)))
    ((null? x) 'snil)
    ((symbol? x) `(ssymbol ,(symbol->string x)))
    ((pair? x) `(scons ,(s (car x)) ,(s (cdr x))))
    ((closure? x) `(sclosure ,(s (closure-id x)) ,(s (closure-body x)) ,(s (closure-env x))))
    ((var? x) (var-name x))
    (else (error 's (format #f "not supported: ~a" x)))))

(define (tagged-list? tag x)
  (and (pair? x) (eq? (car x) tag)))

(define (simplify-real x)
  (cond ((number? x) x)
        ((tagged-list? '/ x) (/ (cadr x) (caddr x)))
        (else (error 'simplify-real (format #f "unexpected real: ~a" x)))))

(define (sinv x env)
  (cond
    ((equal? x '(sbool false)) #f)
    ((equal? x '(sbool true)) #t)
    ((tagged-list? 'sint x) (cadr x))
    ((tagged-list? 'sreal x) (simplify-real (cadr x)))
    ((equal? x 'snil) '())
    ((tagged-list? 'ssymbol x) (string->symbol (cadr x)))
    ((tagged-list? 'scons x) `(,(sinv (cadr x) env) . ,(sinv (caddr x) env)))
    ((tagged-list? 'sclosure x) (make-closure (sinv (cadr x) env) (sinv (caddr x) env) (sinv (cadddr x) env)))
    ((tagged-list? 'let x)
     (let* ((binding (car (cadr x)))
            (lhs (car binding))
            (rhs (cadr binding))
            (body (caddr x)))
       (sinv body (cons (cons lhs (sinv rhs env)) env))))
    ((symbol? x) (let ((p (assq x env)))
                   (if p
                       (cdr p)
                       (error 'sinv (format #f "unknown symbol: ~a" x)))))
    (else (error 'sinv (format #f "not supported: ~a" x)))))

(define (symbolo x)
  (smt/assert `((_ is ssymbol) ,(s x))))

(define (numbero x)
  (smt/assert `(or ((_ is sint) ,(s x)) ((_ is sreal) ,(s x)))))

(define (closure-absento x)
  (smt/assert `(closure-absent ,(s x))))

(define (=/= x y)
  (smt/assert `(not (= ,(s x) ,(s y)))))

(define (== x y)
  (smt/assert `(= ,(s x) ,(s y))))

;Search

; SearchStream: #f | Procedure | State | (Pair State (-> SearchStream))

; SearchStream constructor types. Names inspired by the plus monad?

; -> SearchStream
(define mzero (lambda () #f))

; c: State
; -> SearchStream
(define unit (lambda (c) c))

; c: State
; f: (-> SearchStream)
; -> SearchStream
;
; f is a thunk to avoid unnecessary computation in the case that c is
; the last answer needed to satisfy the query.
(define choice (lambda (c f) (cons c f)))

; e: SearchStream
; -> (-> SearchStream)
(define-syntax inc
  (syntax-rules ()
    ((_ e) (lambda () e))))

; Goal: (State -> SearchStream)

; e: SearchStream
; -> Goal
(define-syntax lambdag@
  (syntax-rules ()
    ((_ (st) e) (lambda (st) e))))

; Match on search streams. The state type must not be a pair with a
; procedure in its cdr.
;
; (() e0)     failure
; ((f) e1)    inc for interleaving. separate from success or failure
;               to ensure it goes all the way to the top of the tree.
; ((c) e2)    single result. Used rather than (choice c (inc (mzero)))
;               to avoid returning to search a part of the tree that
;               will inevitably fail.
; ((c f) e3)  multiple results.
(define-syntax case-inf
  (syntax-rules ()
    ((_ e (() e0) ((f^) e1) ((c^) e2) ((c f) e3))
     (let ((c-inf e))
       (cond
         ((not c-inf) e0)
         ((procedure? c-inf)  (let ((f^ c-inf)) e1))
         ((not (and (pair? c-inf)
                 (procedure? (cdr c-inf))))
          (let ((c^ c-inf)) e2))
         (else (let ((c (car c-inf)) (f (cdr c-inf)))
                 e3)))))))

; c-inf: SearchStream
;     f: (-> SearchStream)
; -> SearchStream
;
; f is a thunk to avoid unnecesarry computation in the case that the
; first answer produced by c-inf is enough to satisfy the query.
(define mplus
  (lambda (c-inf f)
    (case-inf c-inf
      (() (f))
      ((f^) (inc (mplus (f) f^)))
      ((c) (choice c f))
      ((c f^) (choice c (inc (mplus (f) f^)))))))

; c-inf: SearchStream
;     g: Goal
; -> SearchStream
(define bind
  (lambda (c-inf g)
    (case-inf c-inf
      (() (mzero))
      ((f) (inc (bind (f) g)))
      ((c) (g c))
      ((c f) (mplus (g c) (inc (bind (f) g)))))))

; Int, SearchStream -> (ListOf SearchResult)
(define take
  (lambda (n f)
    (cond
      ((and n (zero? n)) '())
      (else
       (case-inf (f)
         (() '())
         ((f) (take n f))
         ((c) (cons c '()))
         ((c f) (cons c
                  (take (and n (- n 1)) f))))))))

; -> SearchStream
(define-syntax bind*
  (syntax-rules ()
    ((_ e) e)
    ((_ e g0 g ...) (bind* (bind e g0) g ...))))

; -> SearchStream
(define-syntax mplus*
  (syntax-rules ()
    ((_ e) e)
    ((_ e0 e ...) (mplus e0
                    (inc (mplus* e ...))))))

; -> Goal
(define (conj2 ig1 ig2)
  (lambda (ctx)
    (let ((g1 (ig1 (cons 'left ctx)))
          (g2 (ig2 (cons 'right ctx))))
      (lambdag@ (st)
        (bind*
         st
         g1
         g2)))))

(define-syntax conj*
  (syntax-rules ()
    ((_ ig) ig)
    ((_ ig0 ig1 ig ...) (conj* (conj2 ig0 ig1) ig ...))))

(define-syntax fresh
  (syntax-rules ()
    ((_ (x ...) ig0 ig ...)
     (lambda (ctx)
       (lambdag@ (st)
         (inc
          (let ((x (var)) ...)
            (((conj* (smt/declare x) ... ig0 ig ...) ctx) st))))))))
#;
(define-syntax fresh
  (syntax-rules ()
    ((_ (x ...) g0 g ...)
     (lambdag@ (st)
       (inc
         (let ((x (var)) ...)
           (bind* st (smt/declare x) ... g0 g ...)))))))


; -> Goal
(define (disj2 ig1 ig2)
  (lambda (ctx)
    (let ((g1 (ig1 (cons 'left ctx)))
          (g2 (ig2 (cons 'right ctx))))
      (lambdag@ (st)
        (inc
         (mplus*
          (g1 st)
          (g2 st)))))))

(define-syntax disj*
  (syntax-rules ()
    ((_ ig) ig)
    ((_ ig0 ig ...) (disj2 ig0 (disj* ig ...)))))

(define-syntax conde
  (syntax-rules ()
    ((_ (ig0 ig ...) (ig1 ig^ ...) ...)
     (disj*
      (conj* ig0 ig ...)
      (conj* ig1 ig^ ...) ...))))
#;
(define-syntax conde
  (syntax-rules ()
    ((_ (g0 g ...) (g1 g^ ...) ...)
     (lambdag@ (st)
       (inc
         (mplus*
          (bind* (g0 st) g ...)
          (bind* (g1 st) g^ ...) ...))))))

(define-syntax run
  (syntax-rules ()
    ((_ n (q) ig ...)
     (begin
       (smt/reset!)
       (let ((q (var)))
         (map (reify q)
              (take n
                    (inc
                     (((conj* (smt/declare q) ig ... smt/purge) '())
                      empty-state)))))))))
#;
(define-syntax run
  (syntax-rules ()
    ((_ n (q) g0 g ...)
     (begin
       (smt/reset!)
       (take n
             (inc
              ((fresh (q) g0 g ... smt/purge
                      (lambdag@ (st)
                        (let ((z ((reify q) st)))
                          (choice z (lambda () (lambda () #f))))))
               empty-state)))))
    ((_ n (q0 q1 q ...) g0 g ...)
     (run n (x)
       (fresh (q0 q1 q ...)
         g0 g ...
         (== `(,q0 ,q1 ,q ...) x))))))

(define-syntax run*
  (syntax-rules ()
    ((_ (q0 q ...) g0 g ...) (run #f (q0 q ...) g0 g ...))))
