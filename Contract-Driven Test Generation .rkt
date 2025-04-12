#lang rosette

;; Step 1: Define symbolic variables
(define-symbolic a b c d e f g h i j k l m n o p q r s t u v w x y z integer?)

;; Step 2: Define utility functions for tokenization
(define (tokenize input)
  (filter (lambda (s) (not (string=? s "")))
          (regexp-split #px"[\\s(),]+" input)))

;; Step 3: Define a parser to convert tokenized input into constraints
(define var-map 
  (hash "a" a "b" b "c" c "d" d "e" e "f" f "g" g "h" h 
        "i" i "j" j "k" k "l" l "m" m "n" n "o" o "p" p 
        "q" q "r" r "s" s "t" t "u" u "v" v "w" w "x" x 
        "y" y "z" z))

(define (get-var var-name)
  (hash-ref var-map var-name (lambda () (error (format "Unknown variable: ~a" var-name)))))

;; Parses simple comparisons (e.g., x > 10, y != 5)
(define (parse-comparison tokens)
  (match tokens
    [(list var-name op val)
     (define var (get-var var-name))
     (define val-num (string->number val))
     (match op
       ["="  (= var val-num)]
       [">"  (> var val-num)]
       ["<"  (< var val-num)]
       ["!=" (not (= var val-num))]
       [_ (error "Unsupported operator")])]
    [_ (error "Invalid comparison format")]))

;; Parses logical expressions (AND, OR, NOT)
(define (parse-logic tokens)
  (cond
    [(equal? (car tokens) "not") (not (parse-logic (cdr tokens)))]
    [(member "or" tokens)
     (define idx (index-of tokens "or"))
     (or (parse-logic (take tokens idx)) (parse-logic (drop tokens (+ idx 1))))]
    [(member "and" tokens)
     (define idx (index-of tokens "and"))
     (and (parse-logic (take tokens idx)) (parse-logic (drop tokens (+ idx 1))))]
    [else (parse-comparison tokens)]))

;; Parses an entire contract string
(define (parse-contract contract-str)
  (parse-logic (tokenize contract-str)))

;; Step 4: Solve the contract constraints
(define (solve-contract contract)
  (define solution (solve (assert contract)))
  (if (sat? solution)
      (begin
        (printf "Solution found: ~a\n" solution)
        (list (evaluate x solution) (evaluate y solution)))
      "No solution exists"))

;; Step 5: Find min/max values for x and y
(define (find-min-max contract)
  (list
   (list "Min x" (let ([sol (optimize #:minimize (list x) #:guarantee (assert contract))])
                   (if (sat? sol) (evaluate x sol) "No solution"))
         "Max x" (let ([sol (optimize #:maximize (list x) #:guarantee (assert contract))])
                   (if (sat? sol) (evaluate x sol) "No solution"))
         "Min y" (let ([sol (optimize #:minimize (list y) #:guarantee (assert contract))])
                   (if (sat? sol) (evaluate y sol) "No solution"))
         "Max y" (let ([sol (optimize #:maximize (list y) #:guarantee (assert contract))])
                   (if (sat? sol) (evaluate y sol) "No solution")))))



(define (eval-expr expr env)
  (cond
    ;; Literal values (numbers, booleans)
    [(number? expr) expr]
    [(boolean? expr) expr]

    ;; Variable lookup with better error message
    [(symbol? expr) 
     (hash-ref env expr (λ () (error (format "Unknown variable: ~a" expr))))]

    ;; Quoted expressions (both 'quote and ' syntax)
    [(and (list? expr) (eq? (first expr) 'quote))
     (second expr)]

    ;; Arithmetic operations (addition, subtraction, etc.)
    [(and (list? expr) (eq? (first expr) '+))
     (+ (eval-expr (second expr) env) (eval-expr (third expr) env))]
    [(and (list? expr) (eq? (first expr) '-))
     (- (eval-expr (second expr) env) (eval-expr (third expr) env))]
    [(and (list? expr) (eq? (first expr) '*))
     (* (eval-expr (second expr) env) (eval-expr (third expr) env))]
    [(and (list? expr) (eq? (first expr) '/))
     (/ (eval-expr (second expr) env) (eval-expr (third expr) env))]

    ;; Comparisons (less than, greater than, etc.)
    [(and (list? expr) (eq? (first expr) '<))
     (< (eval-expr (second expr) env) (eval-expr (third expr) env))]
    [(and (list? expr) (eq? (first expr) '>))
     (> (eval-expr (second expr) env) (eval-expr (third expr) env))]
    [(and (list? expr) (eq? (first expr) '=))
     (= (eval-expr (second expr) env) (eval-expr (third expr) env))]
    [(and (list? expr) (eq? (first expr) '!=))
     (not (= (eval-expr (second expr) env) (eval-expr (third expr) env)))]

    ;; Boolean operations (and, or, not)
    [(and (list? expr) (eq? (first expr) 'not))
     (not (eval-expr (second expr) env))]
    [(and (list? expr) (eq? (first expr) 'and))
     (and (eval-expr (second expr) env) (eval-expr (third expr) env))]
    [(and (list? expr) (eq? (first expr) 'or))
     (or (eval-expr (second expr) env) (eval-expr (third expr) env))]

    ;; Conditional expressions (if)
    [(and (list? expr) (eq? (first expr) 'if))
     (if (eval-expr (second expr) env)
         (eval-expr (third expr) env)
         (eval-expr (fourth expr) env))]

    ;; Catch-all for unknown or unsupported expressions
    [else (error (format "Unknown expression type: ~a" expr))]))


;; Post-condition check function
(define (post-condition x-val y-val result)
  (and (>= result x-val)        ;; result should be at least x
       (>= result y-val)        ;; result should be at least y
       (= result (* x-val y-val)))) ;; result should be x * y


;; Example usage with a function containing loops

(define (multiply-using-loop x y)
  (define result 0)
  (for ([i (in-range 0 y)])
    (set! result (+ result x)))
  result)




;; Generate test cases using only pre-condition
(define (generate-test-cases-only-pre contract num-cases min-x max-x min-y max-y)
  (define test-cases '())
  (define seen-solutions '())

  (for ([x-val (in-range min-x (+ max-x 1))])
    (for ([y-val (in-range min-y (+ max-y 1))])
      (define solution (solve (assert (and contract
                                           (= x x-val)
                                           (= y y-val)))))
      (when (sat? solution)
        (define xy-pair (list x-val y-val))
        (unless (member xy-pair seen-solutions equal?)
          (set! seen-solutions (cons xy-pair seen-solutions))
          (set! test-cases (cons xy-pair test-cases))))))

  (if (null? test-cases)
      "No valid test cases found"
      (reverse (take test-cases (min num-cases (length test-cases))))))

;; Check post-condition after test case generation
(define (check-post-conditions test-cases)
  (for ([tc test-cases])
    (match tc
      [(list x-val y-val)
       (define result (multiply-using-loop x-val y-val))  ;; Use actual result of your function
       (define passed? (post-condition x-val y-val result))
       (displayln (format "Test case: x=~a, y=~a | Result: ~a | Post-condition passed? ~a"
                          x-val y-val result (if passed? "Yes" "No")))])))


;; Handle symbolic execution of loops (for and while)
(define (exec loop-body env)
  (match loop-body
    ;; For loop
    [(list 'for var start end body)
     (define var-val (eval-expr start env))  ;; Evaluate the start value
     (define end-val (eval-expr end env))    ;; Evaluate the end value
     (define (loop iter env)
       (if (< iter end-val)
           (let ([new-env (exec body env)])  ;; Execute the loop body
             (loop (+ iter 1) new-env))  ;; Continue recursion
           env))  ;; Return the final environment after loop ends
     (loop var-val env)]  ;; Start the loop with the initial value
    
    ;; While loop
    [(list 'while test body)
     (define test-val (eval-expr test env))  ;; Evaluate the test condition
     (define (loop env)
       (if test-val
           (let ([new-env (exec body env)])  ;; Execute the loop body
             (loop new-env))  ;; Continue recursion
           env))  ;; Return the final environment
     (loop env)]))  ;; Start the loop with the initial environment




;; Now, let's check if the function with loops satisfies the contract **** PRE_CONDITION ***

(define contract (parse-contract "x > 2 and y < 10"))

(printf "Checking contract satisfiability:\n")
(define solution (solve (assert contract)))
(if (sat? solution)
    (begin
      (printf "Contract is satisfiable\n\n")

      (printf "Generating test cases (pre-condition only):\n")
      (define test-cases (generate-test-cases-only-pre contract 30 1 20 1 20))
      (displayln test-cases)
      (newline)

      (printf "Finding min/max values:\n")
      (define min-max (find-min-max contract))
      (displayln min-max)
      (newline)

      (printf "Checking post-conditions on test cases:\n")
      (check-post-conditions test-cases)

      ;; Check if the loop function meets the contract:
      (define test-x 15)
      (define test-y 5)
      (define result (multiply-using-loop test-x test-y))
      (printf "Function result: ~a\n" result)
      (define passed-post-condition? (post-condition test-x test-y result))

      (printf "Post-condition passed? ~a\n" (if passed-post-condition? "Yes" "No")))
    (printf "Contract is unsatisfiable\n"))
