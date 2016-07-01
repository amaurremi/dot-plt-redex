#lang racket
(require redex/reduction-semantics)

;;;;;;;;;;;;;;
;;; SYNTAX ;;;
;;;;;;;;;;;;;;
(define-language dot
  [(x y z)
      (var s)]       ; variable
  [(a b c)
      (mem s)]       ; term member
  [(A B C)
      (tmem s)]      ; type member
  [(S T U)
      ⊤              ; top type
      ⊥              ; bottom type
      (: a T)        ; field declaration                  a: T
      (: A S T)      ; type declaration                   A: S..T
      (sel x A)      ; type projection                    x.A
      (∧ S T)        ; intersection type
      (μ x T)        ; recursive type                     μ(x: T)
      (∀ x S T)]     ; dependent function                 ∀(x: S)T
  [v
      (ν x T d)      ; new object                         ν(x: T)d
      (λ x T t)]     ; lambda                             λ(x: T)t
  [(t u)
      x              ; variable
      v              ; value
      (sel x a)      ; selection                          x.a
      (x y)          ; application
      (let x t u)]   ; let                                let x = t in u
  [d
      (= a t)        ; field def.
      (= A T)        ; type def.
      (∧ d_1 d_2)]   ; aggregate def.
  [s  variable-not-otherwise-mentioned]

  {Г ((x T) ...)}

  ; todo make those proper
  #:binding-forms
  (μ x T #:refers-to x)
  (∀ x S T #:refers-to x)
  (ν x T d #:refers-to x)
  (λ x T t #:refers-to x)
  (let x t u #:refers-to x))

;;; Examples
;;;;; IFT ≡ { if: ∀(x: {A: ⊥..⊤})∀(t: x.A)∀(f: x.A)x.A }
(define IFT (term
             (: (mem if)
                (∀ (var x) (: (tmem A) ⊥ ⊤)
                           (∀ (var t) (sel (var x) (tmem A))
                                      (∀ (var f) (sel (var x) (tmem A))
                                                 (sel (var x) (tmem A))))))))
;;;;; bool-impl ≡
;;;;;  ν (b: { Boolean: IFT..IFT } ∧ { true: IFT } ∧ { false: IFT })
;;;;;  { Boolean = IFT } ∧
;;;;;  { true = λ(x: {A: ⊥..⊤})λ(t: x.A)λ(f: x.A)t } ∧ { false = λ(x: {A: ⊥..⊤})λ(t: x.A)λ(f: x.A)f }
(define btype (term (: (mem f) (sel (var x) (tmem A)))))
(define boolImpl (term
                  (ν (var b)
                     (∧ (∧ (: (tmem Boolean) ,IFT ,IFT) (: (mem true) ,IFT)) (: (mem false) ,IFT))
                     (∧ (= (mem true)
                           (λ (var x) (: (tmem A) ⊥ ⊤)
                             (λ (var t) ,btype
                               (λ (var f) ,btype
                                 (var t)))))
                        (= (mem false)
                           (λ (var x) (: (tmem A) ⊥ ⊤)
                             (λ (var t) ,btype
                               (λ (var f) ,btype
                                 (var f)))))))))

(define gamma (term (((var x) ⊤) ((var y) ⊥))))
(define gamma-ext (term (((var z) ,IFT) ((var x) ⊤) ((var y) ⊥))))

(define t? (redex-match? dot t))
(define T? (redex-match? dot T))

(test-equal (T? IFT) #t)
(test-equal (T? btype) #t)
(test-equal (t? boolImpl) #t)
(test-equal (redex-match? dot Г gamma) #t)

;;;;;;;;;;;;;;;;;;;;;;
;;; META FUNCTIONS ;;;
;;;;;;;;;;;;;;;;;;;;;;

;;; free variables
(define-metafunction dot
  fv : T -> (x ...)
  [(fv ⊤) ()]
  [(fv ⊥) ()]
  [(fv (: a T)) (fv T)]
  [(fv (: A S T)) (append (fv S) (fv T))]
  [(fv (sel x A)) (x)]
  [(fv (∧ S T)) (append (fv S) (fv T))]
  [(fv (μ x T)) (subtract (fv T) x)]
  [(fv (∀ x S T)) (subtract (append (fv S) (fv T)) x)])

(test-equal (term (fv ,btype)) (term ((var x))))

(define-metafunction dot
  append : (any ...) (any ...) -> (any ...)
  [(append (any_1 ...) (any_2 ...)) (any_1 ... any_2 ...)])

(define-metafunction dot
  subtract : (x ...) x ... -> (x ...)
  [(subtract (x ...)) (x ...)]
  [(subtract (x ...) x_1 x_2 ...)
   (subtract (subtract1 (x ...) x_1) x_2 ...)])

;;; extending environment
(define-metafunction dot
  ; extend : Г (x T) -> Γ
  [(extend ((x_Г T_Г) ...) (x T)) ((x T) (x_Г T_Г) ...)])

(test-equal (term (extend ,gamma ((var z) ,IFT))) gamma-ext)

;;; environment lookup
(define-metafunction dot
  lookup : Г x -> T
  [(lookup ((x_1 T_1) ... (x T) (x_2 T_2) ...) x)
   T
   (side-condition (not (member (term x) (term (x_1 ...)))))]
  [(lookup _ x)
   (error '(x not contained in environment))])

(test-equal (term (lookup ,gamma (var x))) (term ⊤))
(test-equal (term (lookup ,gamma-ext (var z))) IFT)

;;; domain
(define-metafunction dot
  [(dom (= a _)) (a)]
  [(dom (= A _)) (A)]
  [(dom (∧ d_1 d_2)) (append (dom d_1) (dom d_2))])

(define a (term (= (mem ma) (var x))))
(define b (term (= (mem mb) (var y))))
(define c (term (= (tmem tmc) ⊤)))
(test-equal (term (dom ,a)) (term ((mem ma))))
(test-equal (term (dom (∧ ,c (∧ ,a ,b)))) (term ((tmem tmc) (mem ma) (mem mb))))

;;; disjoint lists
(define-metafunction dot
  disjoint : any ... -> boolean
  [(disjoint any_!_1 ...) #t]
  [(disjoint _ ...) #f])

(test-equal (term (disjoint x y)) #t)
(test-equal (term (disjoint x x)) #f)

;;;;;;;;;;;;;;;;;
;;; SUBTYPING ;;;
;;;;;;;;;;;;;;;;;

; todo add transitivity
(define-judgment-form dot
  #:mode (<: I I I)
  #:contract (<: Г T T)

  [
   ----------- "refl"
   (<: Г T T)]

  [
   ----------- "bot"
   (<: Г ⊥ T)]

  [
   ----------- "top"
   (<: Г T ⊤)]

  ;[(<: Г S T)
  ; (<: Г T U)
  ; ---------- "trans"
  ; (<: Г S U)
  
  [
   ----------------- "and1-<:"  ;;;;;;;;;;;;;;;;;;;;;; width
   (<: Г (∧ T U) T)]

  [
   ----------------- "and2-<:"  ;;;;;;;;;;;;;;;;;;;;;; width+perm
   (<: Г (∧ T U) U)]

  [(<: Г S T)
   (<: Г S U)
   --------------------- "and"  ;;;;;;;;;;;;;;;;;;;;;;
   (<: Г S (∧ T U))]

  [(⊢ Г x (: A S T))
   -------------------- "<:-sel"
   (<: Г S (sel x A))]

  [(⊢ Г x (: A S T))
   -------------------- "sel-<:"
   (<: Г (sel x A) T)]

  [(<: Г T U)
   --------------------- "(fld-<:-fld)"
   (<: Г (: a T) (: a U))]

  [(<: Г S_2 S_1)
   (<: Г T_1 T_2)
   ----------------------------------- "typ-<:-typ"
   (<: Г (: A S_1 T_1) (: A S_2 T_2))]

  [(<: Г S_2 S_1)
   (<: (extend Г (x S_2)) T_1 T_2)
   --------------------------------- "all-<:-all"
   (<: Г (∀ x S_1 T_1) (∀ x S_2 T_2))])


;;;;;;;;;;;;;;
;;; TYPING ;;;
;;;;;;;;;;;;;;

(define-judgment-form dot
  #:mode (⊢ I I O)
;  #:contract (⊢ Γ t T)

  [-------------------- "var"
   (⊢ Г x (lookup Г x))]

  [(⊢ Г t T)
   (⊢ (extend Г (x T)) u U)
   (side-condition (not (member (term x) (term (fv U)))))
   ------------------------------------------------------ "let"
   (⊢ Г (let x t u) U)]

  [(⊢ (extend Г (x T)) t U)
   ------------------------ "all-i"
   (⊢ Г (λ x T t) (∀ x T U))]

  ; todo recursion causes infinite loops
  ;[(⊢ Г x T)
  ; --------------- "rec-i"
  ; (⊢ Г x (μ x T))]

  [(⊢ Г x (∀ z S T))
   (⊢ Г y S)
   ----------------------------- "all-e"
   (⊢ Г (app x y) (substitute T z y))]

  ;[(⊢ Г x (μ x T))
  ; --------------- "rec-e"
  ; (⊢ Г x T)]

  [(⊢ (extend Г (x T)) d T)
   ------------------------ "{}-i"
   (⊢ Г (ν x T d) (μ x T))]

  ;[(⊢ Г x T)
  ; (⊢ Г x U)
  ; ------------------- "and-i"
  ; (⊢ Г x (∧ T U))]

  [(⊢ Г x (: a T))
   ----------------- "{}-e"
   (⊢ Г (sel x a) T)]

  ;[(⊢ Г t T)
  ; (<: Г T U)
  ; ------------------- "sub"
  ; (⊢ Г t U)]

  [(⊢ Г t T)
   ---------------------- "fld-i"
   (⊢ Г (= a t) (: a T))]

  [(⊢ Г d_1 T_1)
   (⊢ Г d_2 T_2)
   (side-condition (disjoint (append (dom d_1) (dom d_2))))
   -------------------------------------------------------- "and-def-i"
   (⊢ Г (∧ d_1 d_2) (∧ T_1 T_2))]

  [
   ------------------------- "typ-i"
   (⊢ Г (= A T) (: A T T))])

(define (⊢= t)
  (judgment-holds ((⊢ () ,t T) T))

(module+ test (test-results))