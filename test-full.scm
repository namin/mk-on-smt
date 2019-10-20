(load "helper.scm")
(load "mk-on-smt.scm")
(load "test-check.scm")
(load "full-interp.scm")


(time-test "I love you 1"
           (run 3 (q) (evalo q '(I love you)))
           '('(I love you) ((lambda () '(I love you))) (list 'I 'love 'you)))

;(time (run 4 (q) (evalo q q)))

(time
(run 1 (q)
       (== q 'l1)
     (evalo
       `(letrec ([append (lambda (l1 l2)
                           (if (null? ,q)
                             l2
                             (cons (car l1) (append (cdr l1) l2))))])
          (list
            (append '() '())
            (append '() '(4 5))
            (append '(1) '(4 5))
            (append '(1 2) '(4 5))
            (append '(1 2 3) '(4 5))
            ))
       '(()
         (4 5)
         (1 4 5)
         (1 2 4 5)
         (1 2 3 4 5)))))
