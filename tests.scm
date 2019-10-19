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

