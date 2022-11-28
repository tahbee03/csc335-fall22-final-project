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
; {∨,¬}, that is logically equivalent to P. To prove there exists a logically
; equivalent proposition for the logical connective ¬, we can consider ¬P. Since
; Q <=> P, ¬Q uses only ¬ ∈ {∨,¬}, and ¬Q <=> ¬P. Thus, there exists a logically
; equivalent proposition for ¬P using only {∨,¬}.
;

; ----- ANSWER ENDS HERE -----

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; PART TWO (A): Define a datatype for the class P_V of propositions.

; PART TWO (B): Using this datatype, develop a purely functional R5RS program which
; inputs a proposition in P_V constructed using ∧, ∨, ¬, and ⇒ and which outputs a
; logically equivalent proposition which uses only ∨ and ¬. Prove the correctness of
; your program using the proof you gave in Part One.

; PART TWO (C): Give a complete specification and development (including a proof)
; for an interpreter of propositions in your class P_V. The interpreter will input a
; proposition and a list of bindings of truth values for variables, and will return
; the computed value of the input proposition using these values for its variables.

; PART TWO (D): Demonstrate your interpreter by combining it with the translator you
; constructed for (B).

;         proposition in full P_V ---------------(interpreter)------------- truth value
;                      |                                                         |
;                      |                                                         |
;                 (translator)                                              (indentical)
;                      |                                                         |
;                      |                                                         |
;    proposition in P_V with just ∨ and ¬ -------(interpreter)------------- truth value