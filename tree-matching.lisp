(defpackage #:tree-matching
  (:use #:cl
        #:trivia)
  )
(in-package #:tree-matching)

;; Initially working through
;; Flouri, Tomás and Janousek, Jan and Melichar, Bořivoj: "Subtree Matching by Pushdown Automata", 2010


;; Tree t1 = ({a2_1, a2_2, a0_3, a1_4, a0_5, a1_6, a0_7}, R)
;;      A = {a2, a1, a0}
;;      R is a set of the following ordered sequence of pairs
;;      ((a2_1, a2_2), (a2_1, a1_6)),
;;      ((a2_2, a0_3), (a2_2, a1_4)),
;;      ((a1_4, a0_5)),
;;      ((a1_6, a0_7))
;;
;;      pref(t1) = a2 a2 a0 a1 a0 a1 a0
;;      post(t1) = a0 a0 a1 a2 a0 a1 a2
;;
;;      Tree is
;;      (a2_1
;;        (a2_2
;;           a0_3
;;           (a1_4 a0_5))
;;        (a1_6 a0_7))
;; In the above, the suffixes are the unique node identities in the tree
;; We have arities
;;   a0 : 0
;;   a1 : 1
;;   a2 : 2
;;
;; This could be a haskell datatype
;;     data Tree = A0
;;               | A1 Tree
;;               | A2 Tree Tree

(defun t1_eg ()
  '(a2_1
    (a2_2
     a0_3
     (a1_4 a0_5))
    (a1_6 a0_7)))

;; Intuitively, a normal compiler AST is a "labelled, ordered, ranked and rooted tree"
;; p333
;;
;; And I guess a "label" is then a mapping from the node in the actual
;; AST to its type in the AST type definition.

(defun prefix (tree)
  (if (listp tree)
      (mapcan #'prefix tree)
      (list tree)))

;;                (A2_1 A2_2 A0_3 A1_4 A0_5 A1_6 A0_7)
;;      pref(t1) = a2   a2   a0   a1   a0   a1   a0

(defun postfix (tree)
  (if (listp tree)
      (append (mapcan #'postfix (cdr tree)) (list (car tree)))
      (list tree)))

;;      post(t1) = a0   a0   a1   a2   a0   a1   a2
;;                (A0_3 A0_5 A1_4 A2_2 A0_7 A1_6 A2_1)

;; ---------------------------------------------------------------------
;; p339
;; - Algorithm 1 :: Construction of a PDA accepting a tree t in prefix notation pref(t)
;;   Input: A tree t over a ranked alphabet A; pref(t) = a1 a2 .. an, n >= 1
;;   Output: PDA M_p(t) = ({0,1,2 .. n}, A, {S}, δ, 0 S {n})
;;
;;   Method: For each state i, where 1 <= i <= n, create a new transition
;;           δ(i-1, ai, S) = (i, S^Arity(ai)), where S^0 = ɛ.
;; -------------------------------------
;; Example 5 (p340)
;; The PDA constructed by Algorithm 1, accepting the prefix notation
;; pref(t1) = a2 a2 a0 a1 a0 a1 a0 of tree t, from Example 1, is the
;; DPDA M_p(t1) = ({0,1,2,3,4,5,6,7}, A, {S}, δ_1, 0, S, {7}),
;; where the mapping δ_1 is
;;
;;     δ1(0, a2, S) = (1, SS)
;;     δ1(1, a2, S) = (2, SS)
;;     δ1(2, a0, S) = (3, ɛ)
;;     δ1(3, a1, S) = (4, S)
;;     δ1(4, a0, S) = (5, ɛ)
;;     δ1(5, a1, S) = (6, S)
;;     δ1(6, a0, S) = (7, ɛ)
;; -------------------------------------
;; We have one more state than nodes in the prefix notation of the tree.

;; ---------------------------------------------------------------------
(defclass ranked-alphabet ()
  (alphabet
   arity)
  (:documentation "The labels and arity mapping that can apply to a tree."))
;; ---------------------------------------------------------------------

(defclass pda ()
  ((%alphabet :initarg :alphabet :accessor pda-alphabet)
   (%states :initarg :states :initform '() :accessor pda-states)
   (%initial-state :initarg :initial :initform nil :accessor pda-initial-state)
   (%final-states :initarg :final :initform nil :accessor pda-final-states)
   (%transitions :initarg :transitions  :initform (make-hash-table :test 'equal)
                 :accessor pda-transitions)))

(defclass pda-n (pda)
  ()
  (:documentation "Version of PDA allowing nondeterministic transitions"))

(defun pretty-print-pda (pda &optional (stream t))
  (format stream "PDA~%")
  (format stream "PDA-alphabet:~a~%" (pda-alphabet pda))
  (format stream "PDA-states:~a~%" (reverse (pda-states pda)))
  (format stream "PDA-initial-state:~a~%" (pda-initial-state pda))
  (format stream "PDA-final-states:~a~%" (reverse (pda-final-states pda)))
  (format stream "PDA-transitions:~%")
  (maphash (lambda (k v)
             (format stream "   (~S . ~S)~%" k v))
           (pda-transitions pda)))

(defun new-pda (alphabet)
  (make-instance 'pda :alphabet alphabet))

(defun new-pda-n (alphabet)
  (make-instance 'pda-n :alphabet alphabet))

;; ---------------------------------------------------------------------
(defmethod add-transition ((pda pda) symbol from-node to-node)
  (with-accessors ((alphabet pda-alphabet)
                   (states pda-states)
                   (transitions pda-transitions))
      pda
    (pushnew from-node states)
    (pushnew to-node states)
    (let ((key (list from-node symbol :s))
          (value (list to-node (cdr (assoc symbol alphabet)))))
      (setf (gethash key transitions) value))))

;; Add a transition to a non-deterministic pda
(defmethod add-transition ((pda pda-n) symbol from-node to-node)
  (format t "pda-n:add-transition ~a:~a->~a~%" symbol from-node to-node)
  (with-accessors ((alphabet pda-alphabet)
                   (states pda-states)
                   (transitions pda-transitions))
      pda
    (pushnew from-node states)
    (pushnew to-node states)
    (let ((key (list from-node symbol :s))
          (new-dest (list to-node (cdr (assoc symbol alphabet)))))
      (setf (gethash key transitions)
            (pushnew new-dest (gethash key transitions))))))

;; ---------------------------------------------------------------------

(defmethod get-transition ((pda pda) key)
  (with-accessors ((transitions pda-transitions))
      pda
      (gethash key transitions)))

;; ---------------------------------------------------------------------

(defun eg1-ranked-alphabet ()
  '((:a0 . 0) (:a1 . 1) (:a2 . 2)))

(defun algorithm-1 (ranked-alphabet prefix-tree)
  (let ((node-num 0)
        states)
    (let ((transitions (make-hash-table :test 'equal)))
      (mapc
       (lambda (node)
         (let ((start-node node-num))
           (setq node-num (+ node-num 1))
           (let ((key (list start-node node :s))
                 (value (list node-num (cdr (assoc node ranked-alphabet)))))
             (setf (gethash key transitions) value))))
       prefix-tree)
      (dotimes (state (+ node-num 1))
        (push state states))
      (make-instance 'pda :alphabet ranked-alphabet :states states :transitions transitions))))

(defun eg1-prefix-tree ()
  (list :a2 :a2 :a0 :a1 :a0 :a1 :a0))

(defun test-algorithm-1 ()
  (let ((pda (algorithm-1 (eg1-ranked-alphabet) (eg1-prefix-tree))))
    (pretty-print-pda pda)
    nil))

;; (((0 :A2 :S) (1 2))
;;  ((1 :A2 :S) (2 2))
;;  ((2 :A0 :S) (3 0))
;;  ((3 :A1 :S) (4 1))
;;  ((4 :A0 :S) (5 0))
;;  ((5 :A1 :S) (6 1))
;;  ((6 :A0 :S) (7 0)))

;; ---------------------------------------------------------------------
;; p341
;; Algorithm 2 :: construction of a nondeterministic subtree matching
;; pds for a tree t in prefix notation pref(t)
;; input: a tree t over a ranked alphabet a; pref(t) = a1 a2 .. an, n >= 1
;; output: nondeterministic subtree matching pda
;;    m_nps(t) = ({0,1,2 .. n}, a, {s}, δ, 0 s {n})
;;
;; method
;;   1. create pda m_nps(t) as pda m_p(t) by algorithm 1
;;   2. for each symbol a ∈ a, create a new transition
;;         δ(0, a, s) = (0, s^arity(a)), where s^0 = ɛ.

(defun algorithm-2 (ranked-alphabet prefix-tree)
  (let* ((machine (algorithm-1 ranked-alphabet prefix-tree))
         (transitions (pda-transitions machine)))
    (mapc (lambda (assoc-symbol)
            (let ((symbol (car assoc-symbol)))
              (setf (gethash (list 0 symbol :s) transitions)
                    (list 0 (cdr (assoc symbol ranked-alphabet))))))
          ranked-alphabet)
    (setf (pda-transitions machine) transitions)
    machine))

(defun test-algorithm-2 ()
  (let ((machine (algorithm-2 (eg1-ranked-alphabet) (eg1-prefix-tree))))
    (pretty-print-pda machine)
    nil))

;; ---------------------------------------------------------------------
;; p 343
;;
;; - Algorithm 3 :: transformation of an input-driven nondeterministic
;;   PDA to an equivalent deterministic PDA
;;
;;   Input: Input-driven nondeterministic PDA
;;      M_nx(t) = ({0,1,2 .. n}, A, {S}, δ, 0 S {n})
;;   Output: equivalent  deterministic PDA
;;      M_dx(t) = (Q', A, {S}, δ', q1 S F')
;;
;;   Method
;;     1. Initially, Q' = {{0}}, q1 = {0} and {0} is an unmarked state
;;     2.(a) Select an unmarked state q' from Q'
;;       (b) For each symbol a ∈ A:
;;          i. q'' = {q | δ(p,a,α) = (q,β) for all p ∈ q' }
;;          ii. Add transition δ'(q', a, S) = (q'', S^Arity(a))
;;          iii. If q'' not ∈ Q then add q'' to Q and set is as unmarked state
;;       (c) Set state q' as marked
;;     3. Repeat step 2 until all states in Q' are marked.
;;     4. F' = { q' | q' ∈ Q' and q' intersect F /= {} }

(defun algorithm-3 (pda-n)
  (let* ((big-q (pda-states pda-n))
         (big-q-prime (list (list 0)))
         (unmarked big-q-prime)
         ;; (q1 0)
         )
    (format t "alg3:big-q ~a~%" big-q)
    (loop while (not (null unmarked))
          do
             (progn
               (let ((q-prime (car unmarked)))
                 (setf unmarked (cdr unmarked))
                 (format t "alg3:unmarked ~a~%" unmarked)
                 (format t "alg3:q-prime ~a~%" q-prime)
                 (format t "alg3:transitions ~a~%" (pda-transitions pda-n))
                 (dolist (symbol (pda-alphabet pda-n))
                   ;; In section 2(b) here
                   (format t "alg3:symbol ~a~%" symbol)
                   ;; 2(b)i. q'' = {q | δ(p,a,α) = (q,β) for all p ∈ q' }
                   (let ((q-prime2 nil))
                     (maphash (lambda (k v)
                                (if (eq (car symbol) (cadr k))
                                    (format t " ~S,~S~%" k v)
                                    (let ((q (car v)))
                                      (if (member q q-prime)
                                          (pushnew (car v) q-prime2)))))
                              (pda-transitions pda-n))
                     (format t "q-prime2: ~a~%" q-prime2)
                     ;; 2(b)ii. Add transition δ'(q', a, S) = (q'', S^Arity(a))
                     (add-transition pda-n (car symbol) q-prime q-prime2)
                     ;;  2(b)iii. If q'' not ∈ Q then add q'' to Q and set is as unmarked state
                     ;; Note: must be Q' above, else does not make sense.
                     (format t "alg3:big-q-prime ~a~%" big-q-prime)
                     (format t "alg3:q-prime2 ~a~%" q-prime2)
                     (if (not (member q-prime2 big-q-prime :test 'equal))
                         (progn
                           (format t "oh shit~%")
                           (push q-prime2 big-q-prime)
                           (push q-prime2 unmarked)
                           (break)
                           )
                           (format t "ok~%")
                         )
                     ))))
             ;; (break)
          )
    (format t "alg3:big-q-prime ~a~%" big-q-prime)
    ))

(defun test-algorithm-3 ()
  (let ((pda-n (algorithm-2 (eg1-ranked-alphabet) (eg1-prefix-tree))))
    (algorithm-3 pda-n)))

;; ---------------------------------------------------------------------
;; p347

;; - Algorithm 4 :: Construction of a PDA accepting a set of trees
;;    P = {t1, t2, t3, ..., tm} in their prefix notation.
;;
;;   Input: A set of trees P = {t1, t2, t3, ..., tm} over a ranke alphabet A;
;;     prefix notation pref(ti) = a1 a2 .. an, 1 <= i <= m, ni >= 1.
;;   Output: PDA M_p(P) = ({0,1,2,...,q),A,{S}, δ, 0, S, F).
;;   Method:
;;    1. Let q <- 0 an F <- {}
;;    2. For each tree ti = a1_i a2_i, .. a|ti|_i, 1 <= i <= m do
;;       (a) Let l <- 0
;;       (b) For j = 1 to |ti| do
;;           i. If the transition δ(l, aj_i, S) is not defined then
;;              A. Let q <- q + 1
;;              B. Create a transition δ(l, aj_i, S) <- (q, S^Arity(aj_i))
;;              C. Let l <- q
;;           ii. Else if transition δ(l, aj_i, S) is defined
;;               A. l <- p where (p, γ) <- δ(l, aj, S)
;;       (c) F <- F union {l}


(defun algorithm-4 (pda alphabet trees)
  (format t "alphabet: ~a~%" alphabet)
  (format t "trees:~a~%" trees)
  (setf (pda-alphabet pda) alphabet)
  ;; 1. Let q <- 0 an F <- {}
  (let ((q 0)
        (big-f '())
        ;; (pda (new-pda alphabet))
        )
    ;; 2. For each tree ti = a1_i a2_i, .. a|ti|_i, 1 <= i <= m do
    (dolist (tree trees)
      ;; 2(a) Let l <- 0
      (let ((l 0))
        ;; 2(b) For j = 1 to |ti| do
        (dolist (symbol tree)
          ;; 2(b)i. If the transition δ(l, aj_i, S) is not defined then
          (let ((to (get-transition pda (list l symbol :s))))
            (cond
              ((null to)
               (progn
                 ;; A. Let q <- q + 1
                 (setf q (+ q 1))
                 ;; B. Create a transition δ(l, aj_i, S) <- (q, S^Arity(aj_i))
                 ;; C. Let l <- q
                 (add-transition pda symbol l q)
                 (setf l q)
                 ))
              (t
               ;; 2(b)ii. Else if transition δ(l, aj_i, S) is defined
               ;;  A. l <- p where (p, γ) <- δ(l, aj, S)
               (setf l (car to))))))
        ;; 2(c) F <- F union {l}
        (pushnew l big-f)))
    (setf (pda-initial-state pda) 0)
    (setf (pda-final-states pda) big-f)
    pda))


(defun eg8-ranked-alphabet ()
  '((:a0 . 0) (:a1 . 1) (:a2 . 2)
    (:b0 . 0) (:b1 . 1) ))

   ;; pref(t1) = a2 a2 a0 a0 b0,
   ;; pref(t2) = a2 b1 a0 a0 and
   ;; pref(t3) = a2 a0 a0.
(defun eg8-prefix-tree-1 ()
  (list :a2 :a2 :a0 :a0 :b0))

(defun eg8-prefix-tree-2 ()
  (list :a2 :b1 :a0 :a0))

(defun eg8-prefix-tree-3 ()
  (list :a2 :a0 :a0))

(defun test-algorithm-4 ()
  (let ((pda-p (algorithm-4 (new-pda (eg8-ranked-alphabet))
                            (eg8-ranked-alphabet)
                            (list (eg8-prefix-tree-1)
                                  (eg8-prefix-tree-2)
                                  (eg8-prefix-tree-3)))))
    (pretty-print-pda pda-p)))

;; ---------------------------------------------------------------------
;; p350

;; - Algorithm 5 :: Construction of a nondeterministic subtree matching PDA for a
;;   set of trees P = {t1, t2, t3, ..., tm} in their prefix notation
;;   Input: A tree t over a ranked alphabet A; prefix notation pref(t = a11 a2 .. an, n >= 1
;;   Output: Nondeterministic subtree matching PDA M_nps(t) = (Q,A,{S},δ,0,S,F).
;;   Method:
;;     1. Create PDA_nps(t) as PDA M_p(t) = (Q,A,{S},δ,0,S,F) by Algorithm 4.
;;     2. For each symbol a ∈ A create a new transition δ(0,a,S) = (0,S^Arity(a)),
;;        where S^0 = ε.

(defun algorithm-5 (alphabet trees)
  (let ((pda-n (algorithm-4 (new-pda-n alphabet) alphabet trees)))
    (dolist (symbol (pda-alphabet pda-n))
      (add-transition pda-n (car symbol) 0 0))
    pda-n))

(defun test-algorithm-5 ()
  (let ((pda-p (algorithm-5 (eg8-ranked-alphabet)
                            (list (eg8-prefix-tree-1)
                                  (eg8-prefix-tree-2)
                                  (eg8-prefix-tree-3)))))
    (pretty-print-pda pda-p)))
