#lang racket
(require racket/generic)
(require math/base)

(define-generics GF
  (GF-+ GF o)
  (GF-* GF o)
  (GF-= GF o)
  (GF-inv GF)
  (GF-negate GF)
  (GF-from-number GF))
(define/contract (GF-/ u v)
  (-> GF? GF? GF?)
  (GF-* u (GF-inv v)))
(define GF-++
  (case-lambda
    [(x) x]
    [(x y) (GF-+ x y)]
    [(x y z . w) (apply GF-++ (GF-+ x y) z w)]))

(define-generics CV25519
  (CV-* CV25519 o)
  (CV-id CV25519)
  (CV-= CV25519 o))
(define/contract (CV-expt a b)
  (-> CV25519? integer? CV25519?)
  (do ([r (CV-id a)]
       [a a (CV-* a a)]
       [b b (quotient b 2)])
    ((= b 0) r)
    (when (odd? b)
      (set! r (CV-* r a)))))
(define/contract (generate-key)
  (-> (cons/c CV25519? integer?))
  (let* ((sk (random-natural Q))
         (pk (CV-expt base sk)))
    (cons pk sk)))
    
(define/contract (X25519 pk sk)
  (-> CV25519? integer? CV25519?)
  (CV-expt pk sk))

(define P (- (expt 2 255) 19))
(define Q (+ (expt 2 252) 27742317777372353535851937790883648493))

(struct naive-GF
  (n)
  #:transparent
  #:methods gen:GF
  [(define/contract (GF-= u v)
     (-> GF? GF? boolean?)
     (= (naive-GF-n u) (naive-GF-n v)))
   (define/contract (GF-* u v)
     (-> GF? GF? GF?)
     (naive-GF (modulo (* (naive-GF-n u) (naive-GF-n v)) P)))
   (define/contract (GF-+ u v)
     (-> GF? GF? GF?)
     (naive-GF (modulo (+ (naive-GF-n u) (naive-GF-n v)) P)))
   (define/contract (GF-negate x)
     (-> GF? GF?)
     (cond
       [(= 0 (naive-GF-n x)) x]
       [else (naive-GF (- P (naive-GF-n x)))]))
   (define/contract (GF-inv x)
     (-> GF? GF?)
     (letrec ([pow (lambda (a b [r 1])
                     (if (= b 0)
                         r
                         (let ((r (if (odd? b) (modulo (* r a) P) r)))
                           (pow (modulo (* a a) P) (quotient b 2) r))))])
       (naive-GF (pow (naive-GF-n x) (- P 2)))))]
  #:guard (λ (x name)
            (unless (and (<= 0 x) (< x P)) (error 'naive-GF "Expected 0 <= x < P, found ~a" x))
            x))

(define A (naive-GF 486662))
(define GF-1 (naive-GF 1))
(define GF-0 (naive-GF 0))

(struct naive-CV
  (x y is-id?)
  #:transparent
  #:methods gen:CV25519
  [(define/contract (CV-= u v)
     (-> CV25519? CV25519? boolean?)
     (let ([x1 (naive-CV-x u)]
           [y1 (naive-CV-y u)]
           [k1 (naive-CV-is-id? u)]
           [x2 (naive-CV-x v)]
           [y2 (naive-CV-y v)]
           [k2 (naive-CV-is-id? v)])
       (and (GF-= x1 x2)
            (GF-= y1 y2)
            (equal? k1 k2))))
   (define/contract (CV-id u)
     (-> CV25519? CV25519?)
     (naive-CV GF-0 GF-0 #t))
   (define/contract (CV-* u v)
     (-> CV25519? CV25519? CV25519?)
     (cond
       [(naive-CV-is-id? u) v]
       [(naive-CV-is-id? v) u]
       [(and
         (GF-= (naive-CV-x u) (naive-CV-x v))
         (GF-= (GF-+ (naive-CV-y u) (naive-CV-y v)) GF-0)) (naive-CV? 0) (CV-id u)]
       [else
        (let* ([x1 (naive-CV-x u)]
               [y1 (naive-CV-y u)]
               [x2 (naive-CV-x v)]
               [y2 (naive-CV-y v)]
               [s (GF-/
                  (GF-++ (GF-* x1 x1) (GF-* x1 x2) (GF-* x2 x2) (GF-* A (GF-+ x1 x2)) GF-1)
                  (GF-+ y1 y2))]
               [x (GF-+ (GF-* s s) (GF-negate (GF-++ A x1 x2)))]
               [y (GF-+ (GF-* s (GF-+ x (GF-negate x1))) y1)])
          (naive-CV x (GF-negate y) #f))
        ]))]
  #:guard (λ (x y k name)
            (unless (and (GF? x) (GF? y) (boolean? k)) (error 'naive-CV "Expected (GF? GF? boolean?), found (~a, ~a ~a)" x y k))
            (unless (or k
                        (GF-= (GF-* y y) (GF-++ (GF-* x (GF-* x x)) (GF-* A (GF-* x x)) x)))
              (printf "~a ~a\n" (GF-* y y) (GF-++ (GF-* x (GF-* x x)) (GF-* A (GF-* x x)) x))
              (error 'naive-CV "Point (~a ~a) is not on Curve25519" x y))
            (values x y k)))
(define (assert x)
  (unless x (error 'assertion-failed)))

(define base-x (naive-GF 9))
(define base-y (naive-GF 14781619447589544791020593568409986887264606134616475288964881837755586237401))
(define base (naive-CV base-x base-y #f))
(assert (CV-expt base Q))  ; the order of base is Q, which is a prime

(define (inverse a P)
  (let ([pow
         (λ (a b P)
           (do ([r 1]
                [a a (modulo (* a a) P)]
                [b b (quotient b 2)])
             ((= b 0) r)
             (when (odd? b)
               (set! r (modulo (* r a) P)))))])
    (pow a (- P 2) P)))

(define/contract (ED25519-sign h sk)
  (-> integer? integer? (cons/c integer? integer?))
  (let*
      ([k (random-natural Q)]
       [P (CV-expt base k)]
       [r (modulo (naive-GF-n (naive-CV-x P)) Q)]
       [s (modulo (* (inverse k Q) (+ h (* r sk))) Q)])
    (if (= r 0)
        (ED25519-sign h sk)  ; try again
        (cons r s))))
(define/contract (ED25519-verify h sign pk)
  (-> integer? (cons/c integer? integer?) CV25519? boolean?)
  (let*
      ([r (car sign)]
       [s (cdr sign)]
       [s_inv (inverse s Q)]
       [u1 (modulo (* s_inv h) Q)]
       [u2 (modulo (* s_inv r) Q)]
       [P (CV-* (CV-expt base u1) (CV-expt pk u2))])
    (= (modulo r Q) (modulo (naive-GF-n (naive-CV-x P)) Q))))


(let* ([u (generate-key)]
       [v (generate-key)]
       [k1 (X25519 (car u) (cdr v))]
       [k2 (X25519 (car v) (cdr u))])
  (assert (CV-= k1 k2))
  (printf "Established shared key ~a\n" k1))

(let* ([msg (random-natural Q)]
       [key (generate-key)]
       [sign (ED25519-sign msg (cdr key))]
       [success? (ED25519-verify msg sign (car key))])
  (assert success?)
  (display "Signature verified!\n"))