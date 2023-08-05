#lang racketscript/base

(require racket/match
         racket/stream
         racket/list
         racket/cmdline
         racketscript/interop
         racketscript/browser)

(define (cons-ints a b)
  (+ (* a 10) b))

(define (safe-div a b)
  (if (= b 0) +nan.f (/ a b)))

(define op->string (hash '+ "+"
                         '- "-"
                         '* "*"
                         '/ "/"
                         'cons ""))

(define op->proc (hash '+ +
                       '- -
                       '* *
                       '/ safe-div
                       'cons cons-ints))

(define op-precedence (hash '+ 1 '- 1
                            '* 2 '/ 2
                            'cons 3))

(define (compute source op-stack)
  (let loop ([op-stack op-stack] [compute-stack null] [source-stack source])
    (match (vector op-stack compute-stack source-stack)
      [(vector (list) (list* peek _) _) peek]
      [(vector (list* 'push op-stack) _ (list* item source-stack))
       (loop op-stack (cons item compute-stack) source-stack)]
      [(vector (list* op op-stack) (list* x y compute-stack) _)
       (loop op-stack (cons ((hash-ref op->proc op) x y) compute-stack) source-stack)])))

(define (->infix source op-stack)
  (let loop ([op-stack op-stack] [compute-stack null] [source-stack source])
    (match (vector op-stack compute-stack source-stack)
      [(vector (list) (list* (cons content _) _) _) content]
      [(vector (list* 'push op-stack) _ (list* item source-stack))
       (loop op-stack (cons (cons (number->string item) 4) compute-stack) source-stack)]
      [(vector (list* op op-stack) (list* (cons content1 pr1) (cons content2 pr2) compute-stack) _)
       (define prm (hash-ref op-precedence op))
       (define symbol (hash-ref op->string op))
       (define formatter (match (cons (< pr1 prm) (or (< pr2 prm) (and (= pr2 prm) (or (eq? op '-) (eq? op '/)))))
                           [(cons #f #f) "~a~a~a"]
                           [(cons #t #f) "(~a)~a~a"]
                           [(cons #f #t) "~a~a(~a)"]
                           [(cons #t #t) "(~a)~a(~a)"]))
       (loop op-stack (cons (cons (format formatter content1 symbol content2) prm) compute-stack) source-stack)])))

(define (prove-all source target)
  (define len (- (* (length source) 2) 1))
  (let loop ([a 0] [b 0] [op-stack null])
    (cond
      [(= (+ a b) len)
       (let* ([op-stack (reverse op-stack)]
              [result (compute source op-stack)])
         (if (= result target)
             (stream op-stack)
             empty-stream))]
      [else
       (let* ([return (if (<= a (/ len 2))
                          (stream-lazy (loop (+ a 1) b (cons 'push op-stack)))
                          empty-stream)]
              [return (if (> a (+ b 1))
                          (for/fold ([return return])
                                    ([op (in-list '(+ - * /))])
                            (stream-append (stream-lazy (loop a (+ b 1) (cons op op-stack))) return))
                          return)]
              [return (for/fold ([return return])
                                ([i (in-naturals)]
                                 #:break (or (> (+ a i 1) (quotient len 2)) (< a (- b 2))))
                        (stream-append (stream-lazy (loop (+ a i 2) (+ b i 1)
                                                          (append (build-list (+ i 1) (lambda (i) 'cons))
                                                                  (build-list (+ i 2) (lambda (i) 'push))
                                                                  op-stack))) return))])
         return)])))

(define (prove source target)
  (define result (prove-all source target))
  (if (stream-empty? result)
      #f
      (stream-first result)))

(define (get-ints s)
  (reverse (for/list ([c s]
                      #:when (char-numeric? c))
             (bitwise-xor (char->integer c) 48))))

(define (stream-append s1 s2)
  (if (stream-empty? s1)
    s2
    (stream-cons (stream-first s1) (stream-append (stream-rest s1) s2))))

(define Date ($ ($ 'window) 'Date))
(define (sexp->html sexp)
  (match sexp
    [(list tag-name (list [list attr-name attr-val] ...) children ...)
    (define node
      ($$ document.createElement (symbol->string tag-name)))
    (for-each (lambda (name val)
                ($$ node.setAttribute (symbol->string name) val))
              attr-name
              attr-val)
    (for-each (lambda (child)
                ($$ node.append child))
              (map sexp->html children))
    node]
    [(list tag-name children ...)
    (sexp->html `(,tag-name () ,@children))]
    [(? number? val) (number->string val)]
    [_ sexp]))

(define source-input (sexp->html '(input ([class "form-control"]
                                          [type "number"]
                                          [value 114514]))))
(define target-input (sexp->html '(input ([class "form-control"]
                                          [type "number"]
                                          [value 0]))))
(define all-input (sexp->html '(input ([class "form-check-input"]
                                      [type "checkbox"]))))
(define result-div (make-parameter (sexp->html '(div))))
(define start-prove (sexp->html '(button ([class "btn btn-primary"]
                                          [type "button"])
                                        "开始论证")))
(define bottom (sexp->html `(div ([class "d-grid gap-2 justify-content-sm-center"])
                                ,start-prove
                                ,(result-div))))

(define (replace-result new-node)
  ($$ bottom.removeChild (result-div))
  (result-div new-node)
  ($$ bottom.appendChild (result-div)))

(define container ($$ document.querySelector "div.container"))
(define main `(div ([class "px-4 py-5 my-5 text-center"])
                  (h1 ([class "display-5 fw-bold text-body-emphasis"]) "恶臭数字论证器")
                  (h3 (a ([href "https://github.com/zvmsbackend/homo.js"]) (i ([class "bi bi-github"]))))
                  (div ([class "col-lg-6 mx-auto"])
                        ,source-input
                        (h3 "=")
                        ,target-input
                        (div ([class "form-check form-switch"])
                            ,all-input
                            (label ([class "form-check-label"]
                                    [for "all"])
                                    "给出全部结果"))
                        ,bottom)))

($$ container.append (sexp->html main))

($$ start-prove.addEventListener "click"
    (lambda (e)
      (define source (get-ints (format "~a" ($ source-input 'value))))
      (define target (string->number (format "~a" ($ target-input 'value))))
      (define past ($$ Date.now))
      (cond
        [($ all-input 'checked)
        (define result (prove-all source target))
        (define-values (exprs. count)
          (for/fold ([exprs null]
                      [count 0])
                    ([r result])
            (values (cons (->infix source r) exprs) (+ count 1))))
        (define exprs (remove-duplicates exprs.))
        (replace-result (sexp->html
                          (if (= count 0)
                              "什么都没有(恼"
                              `(div
                                (h4 "共有" ,count "个结果")
                                (h6 "耗时" ,($/binop - ($$ Date.now) past) "毫秒")
                                (ul ([class "list-group"])
                                    ,@(for/list ([expr exprs])
                                        `(li ([class "list-group-item"])
                                            (pre ,(format "~a = ~a" target expr)))))))))]
        [else
        (define result (prove source target))
        (replace-result (sexp->html
                          (if result
                              `(div
                                (h6 "耗时" ,($/binop - ($$ Date.now) past) "毫秒")
                                (pre ,(format "~a = ~a" target (->infix source result))))
                              "什么都没有(恼")))])))