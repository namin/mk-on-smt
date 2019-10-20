(load "helper.scm")
(load "mk-on-smt.scm")
(load "test-check.scm")

(test "nil-1"
  (run* (q) (== q '()))
  '(()))

(test "bool-1"
  (run* (q) (disj2 (== q #t) (== q #f)))
  '(#t #f))

(test "cons-1"
  (run* (q) (== q (cons 'a 'b)))
  '((a . b)))

(test "closure-1"
  (run* (q) (== q (make-closure 'x 'x '())))
  '(#(closure x x ())))

(test "int-1"
  (run* (q) (disj2 (== q 1) (== q 2)))
  '(1 2))

(test "real-1"
  (run* (q) (== q 2.5))
  '(2.5))

(test "conj-1"
  (run* (q) (conj2 (numbero q) (== q 1)))
  '(1))

(test "conj-2"
  (run* (q) (conj2 (numbero q) (== q 'hello)))
  '())

(test "fresh-1"
  (run* (q) (fresh (x y) (== x q) (== y q) (== x 1)))
  '(1))

(test "conde-1"
  (run* (q) (conde ((== q 1)) ((== q 2)) ((== q 3))))
  '(1 2 3))

(define (appendo l s out)
  (conde
    ((== l '()) (== s out))
    ((fresh (a d res)
       (== l (cons a d))
       (== out (cons a res))
       (appendo d s res)))))

(test "rec-1"
  (run 1 (q) (appendo '(a b) '(c d) q))
  '((a b c d)))

(test "rec-bwd-1"
  (run* (q) (fresh (x y) (appendo x y '(a b c d))
                   (== q (list x y))))
  '((() (a b c d))
    ((a) (b c d))
    ((a b) (c d))
    ((a b c) (d))
    ((a b c d) ())))

#;
(test "closure-absento-1"
  (run* (q) (closure-absento q) (== q 1))
  '(1))

#;
(test "closure-absento-2"
  (run* (q) (closure-absento q) (== q (make-closure 'x 'x '())))
  '())

(define (anyo out)
  (conde
    ((== 1 out))
    ((anyo out))))

(test "anyo-1"
  (run 1 (q) (anyo q))
  '(1))

(test "cdcl-1"
  (run* (q)
    (fresh (x y)
      (conde
        ((== x 1))
        ((== x 2)))
      (conde
        ((== y 1))
        ((== y 2)))
      (== q (cons x y))))
  '((1 . 1) (2 . 1) (1 . 2) (2 . 2)))

(test "cdcl-2"
  (run* (q)
    (fresh (x)
      (conde
        ((== x 1))
        ((== x 2)))
      (== q x)))
  '(1 2))

(test "cdcl-3"
  (run* (q)
    (fresh (x y)
      (== x 1)
      (anyo y)
      (== x 2)))
  '())

(test "cdcl-4"
  (run* (q)
    (fresh (x y)
      (== x 1)
      (anyo y)
      (conde
        ((== x 2))
        ((== x 3)))))
  '())

(define (many1o x n)
  (if (<= n 0)
      (== x 1)
      (conde
        ((== x 1))
        ((many1o x (- n 1))))))

(define (manyn1o x n)
  (if (<= n 0)
      (== x 2)
      (conde
        ((== x (+ n 10)))
        ((manyn1o x (- n 1))))))

#;
(test "cdcl-5"
  (run 1 (q)
    (fresh (x)
      (many1o x 10000)
      (manyn1o x 10000)))
  '())

(test "cdcl-6"
  (run 1 (q)
    (fresh (x y z)
      (anyo x)
      (== y 1)
      (anyo z)
      (manyn1o y 1000))) ;; slow
  '())

(test "cdcl-7"
  (run 1 (q)
    (fresh (x y z)
      (anyo x)
      (== y 2)
      (anyo z)
      (many1o y 1000)))
  '())
