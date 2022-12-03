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

; PART ONE: Using structural induction, prove that any proposition written using the
; operators ∧, ∨, ¬, and ⇒ is logically equivalent to a proposition which uses just
; ∨ and ¬.

; ----- ANSWER STARTS HERE -----

; We need to prove that for any proposition P, that there exists a proposiition
; containing only {∨,¬}, say Q, that is logically equivalent to P.

; Basis Step:
; For a proposition v in the set of variables V, v does not use {∧,∨,¬,⇒}
; thus it is vacously true that v can be of {∨,¬}, because it cannot be proven
; otherwise. 

; Inductive Hypothesis:
; For any proposition P, there exists a proposition using only {∨,¬} that is
; logically equivalent to P. 

; Inductive Step:
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

; PART TWO (A): Define a datatype for the class P_V of propositions.

; ----- ANSWER STARTS HERE -----
; p ::= any variable/clause
; P_V ::= p | (make-and P_V P_V) | (make-or P_V P_V) | (make-not P_V) | (make-implies P_V P_V)
; ----- ANSWER ENDS HERE -----

; PART TWO (B): Using this datatype, develop a purely functional R5RS program which
; inputs a proposition in P_V constructed using ∧, ∨, ¬, and ⇒ and which outputs a
; logically equivalent proposition which uses only ∨ and ¬. Prove the correctness of
; your program using the proof you gave in Part One.

; ----- ANSWER STARTS HERE -----
; Constructors
(define (make-and v1 v2)
  (list v1 '& v2))           ; returns (v1 & v2)

(define (make-or v1 v2)
  (list v1 '$ v2))           ; returns (v1 $ v2)

(define (make-not v)
  (list '! v))               ; returns (! v)

(define (make-implies v1 v2)
  (list v1 '=> v2))          ; returns (v1 => v2)

; Selectors
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

; Classifiers
(define (and-prop? p)
  (equal? (operator p) '&))

(define (or-prop? p)
  (equal? (operator p) '$))

(define (not-prop? p)
  (equal? (operator p) '!))

(define (implies-prop? p)
  (equal? (operator p) '=>))

; Main program
(define (translate prop)
  '())

; PRECONDITION: ...
; POSTCONDITION: ...
; DESIGN IDEA: ...

; QUESTION: Does the resulting proposition need to be simplified?
; NOTE: Translator does not change the initial variable set.
; ----- ANSWER ENDS HERE -----

; PART TWO (C): Give a complete specification and development (including a proof)
; for an interpreter of propositions in your class P_V. The interpreter will input a
; proposition and a list of bindings of truth values for variables, and will return
; the computed value of the input proposition using these values for its variables.

; ----- ANSWER STARTS HERE -----
; ----- ANSWER ENDS HERE -----

; PART TWO (D): Demonstrate your interpreter by combining it with the translator you
; constructed for (B).

;         proposition in full P_V ---------------(interpreter)------------- truth value
;                      |                                                         |
;                      |                                                         |
;                 (translator)                                              (indentical)
;                      |                                                         |
;                      |                                                         |
;    proposition in P_V with just ∨ and ¬ -------(interpreter)------------- truth value

; ----- ANSWER STARTS HERE -----
; ----- ANSWER ENDS HERE -----
