
#lang rosette

(require json)
(require racket/match)
 (require json/format/simple)

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






;; Debugging function to inspect hash contents (no change needed)
(define (debug-print-hash h)
  (printf "Hash contents:\n")
  (hash-for-each h (λ (k v) (printf "~a: ~a\n" k v))))

;; Safely get a hash value with error reporting (no change needed)
(define (safe-hash-ref h key [default #f])
  (unless (hash? h)
    (error (format "Expected hash but got: ~a" h)))
  (unless (hash-has-key? h key)
    (printf "Warning: Key '~a' not found in hash. Available keys: ~a\n"
            key
            (hash-keys h)))
  (hash-ref h key default))






;; Robust function name extraction
(define (get-function-name fn-str)
  (with-handlers ([exn:fail? (λ (e) #f)])
    (define expr (with-input-from-string fn-str read))
    (match expr
      [(list 'define (list name _ ...) _ ...) name]
      [(list 'define name _ ...) name]
      [_ #f])))

;; Enhanced function evaluation
(define (evaluate-fn fn-str x y)
  (with-handlers ([exn:fail? (λ (e) "evaluation-error")])
    (define fn-name (get-function-name fn-str))
    (unless fn-name (error "Could not extract function name"))
    
    (define ns (make-base-namespace))
    ;; Import required modules
    (eval '(require racket/list) ns)
    (eval '(require racket/math) ns)
    
    ;; First evaluate the function definition
    (eval (with-input-from-string fn-str read) ns)
    ;; Then call the function
    (eval (list fn-name x y) ns)))

;; Safe precondition checking
(define (check-precondition pre-str x y)
  (with-handlers ([exn:fail? (λ (e) #f)])
    (if (and (string? pre-str) (non-empty-string? pre-str))
        (let ([ns (make-base-namespace)])
          (eval '(require racket/list) ns)
          (eval '(require racket/math) ns)
          (eval `(let ([x ,x] [y ,y]) 
                  ,(with-input-from-string pre-str read))
                ns))
        #t)))

;; Robust postcondition checking
(define (check-postcondition post-str x y result)
  (with-handlers ([exn:fail? (λ (e) 
                              (printf "Postcondition error: ~a\n" (exn-message e))
                              #f)])
    (if (and (string? post-str) 
             (non-empty-string? post-str)
             (not (equal? result "evaluation-error")))
        (let ([ns (make-base-namespace)])
          (eval '(require racket/list) ns)
          (eval '(require racket/math) ns)
          (eval `(let ([x ,x] [y ,y] [result ,result]) 
                  ,(with-input-from-string post-str read))
                ns))
        #f)))

;; Test case generation with validation
(define (generate-test-cases bounds num-cases)
  (define min-x (safe-hash-ref bounds 'min_x))
  (define max-x (safe-hash-ref bounds 'max_x))
  (define min-y (safe-hash-ref bounds 'min_y))
  (define max-y (safe-hash-ref bounds 'max_y))
  
  (for/list ([i (in-range num-cases)])
    (list (random min-x (add1 max-x))
          (random min-y (add1 max-y)))))

;; Main processing function with comprehensive error handling
(define (process-contract contract)
  (with-handlers ([exn:fail? (λ (e) 
                              (printf "Processing error: ~a\n" (exn-message e))
                              (hasheq 'error (exn-message e)))])
    (define fn-str (safe-hash-ref contract 'function_body))
    (define pre-str (safe-hash-ref contract 'precondition ""))
    (define post-str (safe-hash-ref contract 'postcondition ""))
    (define bounds (safe-hash-ref contract 'test_bounds (hasheq)))
    (define num-cases (safe-hash-ref contract 'num_cases 5))
    
    (define test-cases (generate-test-cases bounds num-cases))
    
    (define results
      (for/list ([case test-cases])
        (match-define (list x y) case)
        (define pre-pass? (check-precondition pre-str x y))
        
        (define result
          (if pre-pass?
              (evaluate-fn fn-str x y)
              "precondition-failed"))
                
        (define passed? 
          (and (not (equal? result "precondition-failed"))
               (check-postcondition post-str x y result)))
        
        (hasheq 'x x 'y y 'result result 'pass passed?)))
    
    (hasheq 'function fn-str
            'tests results
            'stats (hasheq 'total_cases num-cases
                           'passed_cases (count (λ (r) (eq? #t (hash-ref r 'pass))) results)))))
;; Modified main function to add a newline between contract processing
(define (main)
  (define input-data (with-handlers ([exn:fail? (λ (e) (error "Failed to parse JSON"))])
                       (call-with-input-file "Leetcode.json" read-json)))

  (unless (list? input-data)
    (error "Input JSON did not parse to a list (expected an array of contracts)"))

(define all-results
  (for/list ([index (in-range (length input-data))]
             [contract (in-list input-data)])
    (unless (zero? index) (displayln "")) ; Print newline after the first element
    (unless (hash? contract)
      (error "Each element in the JSON array must be a contract object (hash map)"))
    (process-contract contract)))

  (call-with-output-file "leetCodeResults.json"
  (λ (out)
    (display (jsexpr->pretty-json all-results) out))
  #:exists 'replace))


;; Run the program
(main)