; CSC 335, Fall 2022
; Final Project
; Group Members: Luigi Otoya (Section M), Talike Bennett (Section R)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; GOAL: Develop and prove the correctness of a system that translates and evaluates
; expressions in propositional logic.

; DEFINITION OF PROPOSITIONS: Given a set V of variables, we define the class P_V of
; propositions over V as the least class containing T (true), F (false), and each
; variable v in V which is closed under the operations ∧ (and), ∨ (or), ¬ (not), and
; ⇒ (implies).

; EXAMPLES: Given p, q ∈ P_V:
;    (p ∧ q) ∈ P_V
;    (p ∨ q) ∈ P_V
;    ¬p ∈ P_V
;    (p ⇒ q) ∈ P_V

; NOTE: In the above examples, only p and q are proper components. The parentheses ()
; and the operations ∧, ∨, ¬, and ⇒ are not considered as proper components.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; ==================================================================================
; PART ONE: Using structural induction, prove that any proposition written using the
; operators ∧, ∨, ¬, and ⇒ is logically equivalent to a proposition which uses just
; ∨ and ¬.
; ==================================================================================
; ----- ANSWER STARTS HERE -----

; We need to prove that for any proposition P, that there exists a proposiition
; containing only {∨,¬}, say Q, that is logically equivalent to P.

; BASIS STEP:
; For a proposition v in the set of variables V, v does not use {∧,∨,¬,⇒}
; thus it is vacously true that v can be of {∨,¬}, because it cannot be proven
; otherwise. 

; INDUCTION HYPOTHESIS:
; For any proposition P, there exists a proposition using only {∨,¬} that is
; logically equivalent to P. 

; INDUCTION STEP:
; By the induction hypothesis there is a proposition, say Q, which uses only
; {∨,¬}, that is logically equivalent to P.
;
; ¬
; To prove there exists a logically equivalent proposition for the logical connective
; ¬, we can consider ¬P. Since Q <=> P, ¬Q uses only ¬ ∈ {∨,¬}, and ¬Q <=> ¬P. Thus,
; there exists a logically equivalent proposition for ¬P using only {∨,¬}.

; ∧
; To prove there exists a logically equivalent proposition for the logical connective
; ∧, we can consider (P1 ∧ P2). Since Q1 <=> P1 and Q2 <=> P2 by the IH, then using
; only connectives in {∨,¬} and applying De Morgan's Law: ¬(¬Q1 ∨ ¬Q2) <=> (Q1 ∧ Q2) 
; <=> (P1 ∧ P2). Thus, there exists a logically equivalent proposition for (P1 ∧ P2) 
; using only {∨,¬}.

; ∨
; To prove there exists a logically equivalent proposition for the logical connective
; ∨, we can consider (P1 ∨ P2). Since Q1 <=> P1 and Q2 <=> P2 by the IH, then using
; only connectives in {∨,¬}: (Q1 ∨ Q2) <=> (P1 ∨ P2). Thus, there exists a logically
; equivalent proposition for (P1 ∨ P2) using only {∨,¬}.

; ⇒
; To prove there exists a logically equivalent proposition for the logical connective
; ⇒, we can consider P1 ⇒ P2. Since Q1 <=> P1 and Q1 <=> P2 by the IH, then using
; only connectives in {∨,¬} and logical equivalencies for conditional statements:
; (¬Q1 ∨ Q2) <=> (Q1 ⇒ Q2) <=> (P1 ⇒ P2). Thus, there exists a logically equivalent
; proposition for (P1 ⇒ P2) using only {∨,¬}.

; ----- ANSWER ENDS HERE -----

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;===================================================================================
; PART TWO (A): Define a datatype for the class P_V of propositions.
;===================================================================================
; ----- ANSWER STARTS HERE -----
; p ::= any variable/clause
; P_V ::= p | (make-and P_V P_V) | (make-or P_V P_V) | (make-not P_V) | (make-implies P_V P_V)
; ----- ANSWER ENDS HERE -----

;===================================================================================
; PART TWO (B): Using this datatype, develop a purely functional R5RS program which
; inputs a proposition in P_V constructed using ∧, ∨, ¬, and ⇒ and which outputs a
; logically equivalent proposition which uses only ∨ and ¬. Prove the correctness of
; your program using the proof you gave in Part One.
;===================================================================================
; ----- ANSWER STARTS HERE -----
; ==============================
; Constructors
; ==============================
(define (make-and v1 v2)
  (list v1 '& v2))           ; returns (v1 & v2)

(define (make-or v1 v2)
  (list v1 '$ v2))           ; returns (v1 $ v2)

(define (make-not v)
  (list '! v))               ; returns (! v)

(define (make-implies v1 v2)
  (list v1 '=> v2))          ; returns (v1 => v2)

; ==============================
; Selectors
; ==============================
(define (first-operand p)
  (if (= (length p) 3)
      (car p)              ; v1 -> {&, $, =>} -> v2 -> () ==> v1
      (cadr p)))           ; ! -> v -> ()                 ==> v

(define (second-operand p)
  (if (= (length p) 3)
      (caddr p)            ; v1 -> {&, $, =>} -> v2 -> () ==> v2
      (cadr p)))           ; ! -> v -> ()                 ==> v

(define (operator p)
  (if (= (length p) 3)
      (cadr p)             ; v1 -> {&, $, =>} -> v2 -> () ==> {&, $, =>}
      (car p)))            ; ! -> v -> ()                 ==> !

; ==============================
; Classifiers
; ==============================
(define (and-prop? p)
  (equal? (operator p) '&))

(define (or-prop? p)
  (equal? (operator p) '$))

(define (not-prop? p)
  (equal? (operator p) '!))

(define (implies-prop? p)
  (equal? (operator p) '=>))

; ==============================
; Main program
; ==============================
(define (translate prop)
  (cond ((not (pair? prop)) prop)
        ((and-prop? prop) (make-not (make-or (make-not (translate (first-operand prop))) (make-not (translate (second-operand prop))))))
        ((or-prop? prop) (make-or (translate (first-operand prop)) (translate (second-operand prop))))
        ((not-prop? prop) (make-not (translate (first-operand prop))))
        ((implies-prop? prop) (make-or (make-not (translate (first-operand prop))) (translate (second-operand prop))))))

; PRECONDITION: The program accepts a logical proposition, prop, that consists
; of variables and the operation 

; POSTCONDITION: The program returns a logical proposition that consists of variables
; and the operations {∨,¬}.

; DESIGN IDEA: With the use of the constructors (which contain the list primitive)
; and the selectors (which contain the car and cdr primitives), we can build a
; program that constructs and returns a new list. Since the underlying list
; primitive is used to construct a list, it might be best to implement a
; recursive solution that unwinds the given proposition.

; BASIS STEP: Variables of the set V are considered to be proper components of the
; class P_V. Therefore, the base case of the program occurs when it encounters
; exactly one proper component (which can also be classified as not a pair). 

; INDUCTION HYPOTHESIS: Any use of the selectors first-operand and second-operand
; will either return a proposition in the class P_V or a variable in the set V.

; INDUCTION STEP: The logical propositions used in this program are represented
; as Scheme lists. Because of this, the base case can be reached if we "cdr down"
; the lists -- at least, this is the most reasonable way to do so. Each of the
; selector functions have an underlying car, cdr, or some combination of the two that
; implement this functionality. By using these selectors as arguments of each
; recursive call, we are essentially shrinking the size of the list and ultimately
; decreasing the number of proper components present in the list. Therefore, this
; shows that if the precondition is met, the postcondition can also be met
; with a recursive solution.

; QUESTION: Does the resulting proposition need to be simplified?
; NOTE: Translator does not change the initial variable set.
; NOTE (2): All acceptable propositions are in the following forms:
;    - single variable (ex. (x))
;    - basic proposition (ex. (x & y))
;    - complex/nested propositon (ex. ((z $ (x & y)) => w))
; ----- ANSWER ENDS HERE -----

;;==================================================================================
; PART TWO (C): Give a complete specification and development (including a proof)
; for an interpreter of propositions in your class P_V. The interpreter will input a
; proposition and a list of bindings of truth values for variables, and will return
; the computed value of the input proposition using these values for its variables.
;===================================================================================
; ----- ANSWER STARTS HERE -----
; ==============================
; Function (and, or, not, imply)
; ==============================
; or:
(define or-function
  (lambda (v1 v2) (cond (v1 v1)      ; if v1 is true return v1
                        (else v2)))) ; else return truth value of v2
; and:
(define and-function
  (lambda (v1 v2) (cond (v1 v2)      ; if v1 is true return v2
                        (else v1)))) ; else return truth value of v1
; not:
(define not-function
  (lambda (v1) (cond (v1 #f)         ; if v1 is true return false
                     (else #t))))    ; else return true
; implies:
(define implies-function
  (lambda (v1 v2) (cond ((eq? v1 v2) #t)
                        (else v2))))

; ==============================
; Helpers:
; ==============================
(define (truth-value var v-bindings)
  (define (iter acc rest)
    (let ((binding (car acc)))
      (cond ((eq? var (car binding)) (cadr binding))
            (else (iter (append (list(car rest)) acc) (cdr rest))))))
  (let ((first (list(car v-bindings))))
    (iter first (cdr v-bindings))))

; ==============================
; Proof for truth-value:
; ==============================
; Design Idea:
; truth-value has two parameters: a variable var, and a list of variable bindings
; v-bindings.The variable var must exist as a variable in the list of bindings along
; with its respective truth value. Every binding is a list and has the form (v TF),
; where v is a variable and TF is its truth value.
; Thus v-bindings is of the form ((v1 TF1) (v2 TF2) ... (vn TFn)), where n is the
; number of bindings in the list.
; We can use an accumulator variable call acc which will contain the list of
; processed and currently processing bindings. The currently processing binding will
; always be first in this list. We can check if the car of the current binding is
; equal to var, and if it is we return its truth value. Otherwise we move on to the
; next binding. The next binding will be the first binding in a variable called rest
; which contains all of the bindings remaining to be processed. We access this
; binding using (cdr rest) and append it to the accumulator variable to process it.

; pre-condition:
; ==============================
; var is a variable that exists in the list of bindings v-bindings.
; v-bindings is of the form ((v1 TF1) (v2 TF2) ... (vn TFn)), where v is
; a variable, and TF is its truth value.

; post-condition:
; ==============================
; returns the truth value of the variable var.

; Guess Invariant: v-bindings = (append (reverse acc) rest)

; Weak-Enough?:
; ==============================
; At initialization, acc contains the first bindings of v-bindings. That is
; acc = '((v1 TF1)). The variable rest at initizaliation contains all of the
; bindings aside from first, that is '((v2 TF2) (v3 TF3) ... (vn TFn)). Thus,
; v-bindings = (append (reverse acc) rest).

; Strong-Enough?:
; ==============================
; At termination, var has been found and thus its truth value is returned. The acc
; variable at this point contains every binding in v-bindings, but in reverse order,
; that is ((vn TFn) (vn-1 TFn-1) ... (v2 TF2) (v1 TF1)). The rest variable at this
; point is empty: '(). Thus if we append the reverse of acc with '(), we get back
; the original v-bindings.
;
; Preservable?:
; ==============================
; Yes, at any point in the program, acc = the reverse of the list of bindings present
; in v-bindings but not in rest, and in reverse order. Thus reversing acc and appending
; it to rest gives v-bindings.

; atom definition:
(define (atom? a)
  (and (not (null? a)) (not (pair? a))))

; ==============================
; INTERPRETER:
; ==============================
(define proposition
  (lambda (prop v-bindings)
    (cond ((atom? prop) (truth-value prop v-bindings))
          (else
           (cond ((and-prop? prop)
                  (and-function
                   (proposition (first-operand prop)  v-bindings)
                   (proposition (second-operand prop) v-bindings)))
                 ((or-prop? prop)
                  (or-function
                   (proposition (first-operand prop)  v-bindings)
                   (proposition (second-operand prop) v-bindings)))
                 ((implies-prop? prop)
                  (implies-function
                   (proposition (first-operand prop)  v-bindings)
                   (proposition (second-operand prop) v-bindings)))
                 ((not-prop? prop)
                  (not-function
                   (proposition (first-operand prop)  v-bindings))))
           ))
    ))

; ==============================
; Proof:
; ==============================
; DESIGN STRATEGY:
; The constructors build propositions in P_V. Each proposition in P_V is of the
; form: (v1 lc v2) and (lc v1)  where v1,v2 ∈ P_V, and
; lc is a logical connective ∈ {!, $, &, =>}. Thus since v1,v2 ∈ P_V, we can
; recursively process the proposition using our selectors first-operand and
; second-operand. If v1 or v2 are variables then they have no logical connectives
; and their truth value from the list of bindings can be returned. To defer the
; logical operations on the returned truth values, we guard the calls to the
; interpreter with our pre-defined functions for "and", "or", "not", and "implies".

; PRE-CONDITION:
; prop is a proposition in P_V, and v-bindings is a list of bindings of truth values
; for variables v in the proposition prop. Each binding is a list of 2-elements of the
; form: (v TF), where TF is the truth value (#t or #f) for a variable v in prop.

; POST-CONDITION:
; The interpreter returns the computed truth value:#t or #f, of the proposition prop.

; BASIS STEP:
; prop is variable, thus return its truth value.

; INDUCTION HYPOTHESIS:
; Let P be a proposition in P_V, and B be the list of bindings for the variables in P.
; We Assume that (proposition (first-operand P) B) and (proposition (second-operand P) B)
; return the correct truth values respectively.

; INDUCTION STEP:
; By our induction hypothesis (proposition (first-operand P) B) and
; (proposition (second-operand P) B) respectively return correct truth values for the
; first and second operand of P. We have two cases:

; Case (and, or, implies):
; Then (F (proposition (first-operand P) B) (proposition (second-operand P) B)), where
; F is a logical function of "or-function", "and-function", "implies-function", returns
; the correct truth value for (proposition P B).

; Case (not):
; Then (F (proposition (first-operand P) B)), where F is the defined logical
; function: "not-function", returns the correct truth value for (proposition P B).

; ----- ANSWER ENDS HERE -----

;===================================================================================
; PART TWO (D): Demonstrate your interpreter by combining it with the translator you
; constructed for (B).
;===================================================================================
;         proposition in full P_V ---------------(interpreter)------------- truth value
;                      |                                                         |
;                      |                                                         |
;                 (translator)                                              (indentical)
;                      |                                                         |
;                      |                                                         |
;    proposition in P_V with just ∨ and ¬ -------(interpreter)------------- truth value

; ----- ANSWER STARTS HERE -----
; ==============================
; simple:
; ==============================
(define p1 (make-and 'p 'q))
(define p2 (make-or 'p 'q))
(define p3 (make-not 'p))
(define p4 (make-implies 'p 'q))
; ==============================
; nested:
; ==============================
(define p5 (make-and p1 p2))
(define p6 (make-or p5 p4))
(define p7 (make-not p6))
(define p8 (make-implies p7 p6))
; ==============================
; bindings: 
; ==============================
(define b1 '((p #t) (q #t)))
(define b2 '((p #t) (q #f)))
(define b3 '((p #f) (q #t)))
(define b4 '((p #f) (q #f)))
(define b5 '((p #t)))
; ==============================
; TESTS:
; ==============================
(define (show P B)
  (display "Proposition: ") (display P)
  (display "\tBindings: ") (display B) (newline)
  (display "Translation: ") (display (translate P)) (newline))
; ------------------------------
(show p1 b1) (proposition p1 b1) (proposition (translate p1) b1)
(show p1 b2) (proposition p1 b2) (proposition (translate p1) b2)
(show p5 b1) (proposition p5 b1) (proposition (translate p5) b1)
(show p7 b3) (proposition p7 b3) (proposition (translate p7) b3)
;(proposition p1 b1)
;(proposition (translate p1) b1)
;(proposition p1 b2)
;(proposition (translate p1) b2)
;(proposition p1 b3)
;(proposition (translate p1) b3)
;(proposition p1 b4)
;(proposition (translate p1) b4)
;(proposition p5 b1)
;(proposition (translate p5) b1)
;(proposition p7 b3)
;(proposition (translate p7) b3)


; ----- ANSWER ENDS HERE -----

