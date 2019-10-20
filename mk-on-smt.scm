;;(define smt-cmd "cvc4 --lang=smt2.6 -m --incremental --fmf-fun")
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
    ;;(printf ">> ~a\n" r)
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
      ;;(printf "~s\n" x)
      (fprintf smt-out "~s\n" x))
    xs)
  (flush-output-port smt-out))

(define empty-state '())
;; a list of pairs of assumption variable id and z3 statements

;; a set of asserted assumption variable ids
(define empty-seen-assumptions '())
(define seen-assumptions empty-seen-assumptions)
(define (saw-assumption! id)
  (set! seen-assumptions (t:bind id #t seen-assumptions)))
(define (seen-assumption? id)
  (t:lookup id seen-assumptions))
(define (assumption-id->symbol id)
  (string->symbol (format #f "_a~a" id)))
(define assumption-count 0)
(define (fresh-assumption-id!)
  (set! assumption-count (+ 1 assumption-count))
  (smt-call `((declare-const ,(assumption-id->symbol assumption-count) Bool)))
  assumption-count)
(define empty-child-assumptions '())
(define child-assumptions empty-child-assumptions)
(define (get-child-assumptions! id)
  (let ((r (t:lookup id child-assumptions)))
    (if r
        (data-val r)
        (begin
          (let ((new-cs (cons (fresh-assumption-id!) (fresh-assumption-id!))))
            (set! child-assumptions (t:bind id new-cs child-assumptions))
            new-cs)))))
(define left car)
(define right cdr)

(define-structure (closure id body env))
(define (smt/add-if-new ctx stmt st)
  (unless (seen-assumption? ctx)
      (saw-assumption! ctx)
      (smt-call (list stmt)))
  (cons (cons ctx stmt) st))
(define smt/check
  (lambda (st)
    (smt-call `((check-sat-assuming
                 ,(map (lambda (x) (assumption-id->symbol (car x))) st))))
    (if (smt-read-sat)
        st
        #f)))

(define (smt/declare x)
  (lambda (ctx)
    (lambdag@ (st)
      (smt/add-if-new ctx `(declare-const ,(var-name x) SExp) st))))

(define (smt/assert e)
  (lambda (ctx)
    (lambda (st)
      (smt/check
       (smt/add-if-new ctx `(assert (= ,(assumption-id->symbol ctx) ,e)) st)))))

(define smt/purge
  (lambda (ctx)
    smt/check))

(define (smt/reset!)
  (set! assumption-count 0)
  (set! seen-assumptions empty-seen-assumptions)
  (set! child-assumptions empty-child-assumptions)
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
    #;
    (smt-call '((define-fun-rec closure-absent ((e SExp)) Bool ;
    (ite ((_ is sclosure) e) false      ;
    (ite ((_ is scons) e) (and (closure-absent (s-car e)) (closure-absent (s-cdr e))) ;
    true)))))
  )

(define (reify q)
  (lambda (st)
    (smt/check st)
    (smt-call '((get-model)))
    (let ((ms (cdr (read smt-in))))
      (let ((r (car (filter (lambda (x) (eq? (cadr x) (var-name q))) ms))))
        (sinv (cadddr (cdr r)) '())))))

(define (var x id)
  (vector
   (string->symbol (format #f "_v_~a_~a" x id))))

(define (var? x)
  (vector? x))

(define (var-name v)
  (vector-ref v 0))

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
     (let* ((bindings (cadr x))
            (lhss (map car bindings))
            (rhss (map (lambda (x) (sinv (cadr x) env)) bindings))
            (body (caddr x)))
       (sinv body (append (map cons lhss rhss) env))))
    ((symbol? x) (let ((p (assq x env)))
                   (if p
                       (cdr p)
                       (error 'sinv (format #f "unknown symbol: ~a" x)))))
    (else (error 'sinv (format #f "not supported: ~a" x)))))

(define (symbolo x)
  (smt/assert `((_ is ssymbol) ,(s x))))

(define (numbero x)
  (smt/assert `(or ((_ is sint) ,(s x)) ((_ is sreal) ,(s x)))))

#;
(define (closure-absento x)
  (smt/assert `(closure-absent ,(s x))))

(define (not-closureo x)
  (smt/assert `(not ((_ is sclosure) ,(s x)))))

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
    (let ((cs (get-child-assumptions! ctx)))
      (let ((ctx1 (left cs))
            (ctx2 (right cs)))
        (let ((g1 (ig1 ctx1))
              (g2 (ig2 ctx2)))
          (lambdag@ (st)
            (bind*
             st
             ((smt/assert `(and ,(assumption-id->symbol ctx1)
                                ,(assumption-id->symbol ctx2)))
              ctx)
             g1
             g2)))))))

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
          ;; this will break with macro-generated freshes
          (let ((x (var 'x ctx)) ...)
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
    (let ((cs (get-child-assumptions! ctx)))
      (let ((ctx1 (left cs))
            (ctx2 (right cs)))
        (let ((g1 (ig1 ctx1))
              (g2 (ig2 ctx2)))
          (lambdag@ (st)
            (inc
             (bind*
              (((smt/assert `(or ,(assumption-id->symbol ctx1)
                                 ,(assumption-id->symbol ctx2)))
                ctx)
               st)
              (lambdag@ (st)
                (mplus*
                 (g1 st)
                 (g2 st)))))))))))

(define-syntax disj*
  (syntax-rules ()
    ((_ ig) ig)
    ((_ ig0 ig ...) (disj2 ig0 (disj* ig ...)))))

(define-syntax conde
  (syntax-rules ()
    ((_ (ig0 ig ...) (ig1 ig^ ...) ...)
     (lambda (ctx)
       (lambdag@ (st)
         (inc
          (((disj*
              (conj* ig0 ig ...)
              (conj* ig1 ig^ ...) ...)
            ctx)
           st)))))))
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
       (let ((ctx (fresh-assumption-id!)))
         (let ((q (var 'q ctx)))
           (map (reify q)
                (take n
                      (inc
                       (((conj* (smt/declare q) ig ... smt/purge) ctx)

                        empty-state))))))))))
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
