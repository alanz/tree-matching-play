(defpackage #:tree-matching
  (:use #:cl
        #:trivia)
  )
(in-package #:tree-matching)

;; Initially working through
;; Flouri, Tomás and Janousek, Jan and Melichar, Bořivoj: "Subtree Matching by Pushdown Automata", 2010
;; DOI: 10.2298/CSIS1002331F


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

(defclass pda-t-n (pda)
  ()
  (:documentation "Version of PDA for templates allowing nondeterministic transitions"))

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

(defun new-pda-t-n (alphabet)
  (make-instance 'pda-t-n :alphabet alphabet))

;; ---------------------------------------------------------------------

;; Store the transition ready for use.
;; So a hashmap,
;;   key   is (list state symbol)
;;   value is (list match-arity to-state push-arity)
(defun make-transition-k-v (from-node symbol match-arity to-node push-arity)
    (let ((key (list from-node symbol))
          (value (list match-arity to-node push-arity)))
      (values key value)))

(defmethod add-transition ((pda pda) symbol from-node to-node match-arity &optional push-arity)
  (with-accessors ((alphabet pda-alphabet)
                   (states pda-states)
                   (transitions pda-transitions))
      pda
    (pushnew from-node states :test 'equal)
    (pushnew to-node states :test 'equal)
    (let ((key (list from-node symbol match-arity))
          (value (if push-arity
                     (list to-node push-arity)
                     (list to-node (cdr (assoc symbol alphabet))))))
      (setf (gethash key transitions) value))))

;; Add a transition to a non-deterministic pda
(defmethod add-transition ((pda pda-n) symbol from-node to-node match-arity &optional push-arity)
  (with-accessors ((alphabet pda-alphabet)
                   (states pda-states)
                   (transitions pda-transitions))
      pda
    (pushnew from-node states :test 'equal)
    (pushnew to-node states :test 'equal)
    (let ((key (list from-node symbol match-arity))
          (new-dest (if push-arity
                        (list to-node push-arity)
                        (list to-node (cdr (assoc symbol alphabet))))))
      (setf (gethash key transitions)
            (pushnew new-dest (gethash key transitions) :test 'equal)))))


(defmethod add-transition ((pda pda-t-n) symbol from-node to-node match-arity &optional push-arity)
  (with-accessors ((alphabet pda-alphabet)
                   (states pda-states)
                   (transitions pda-transitions))
      pda
    (pushnew from-node states :test 'equal)
    (pushnew to-node states :test 'equal)
    (let ((key (list from-node symbol match-arity))
          (new-dest (if push-arity
                        (list to-node push-arity)
                        (list to-node (cdr (assoc symbol alphabet))))))
      (setf (gethash key transitions)
            (pushnew new-dest (gethash key transitions) :test 'equal)))))

;; ---------------------------------------------------------------------

;; All transitions from a deterministic pda
(defmethod all-transitions ((pda pda))
  (with-accessors ((transitions pda-transitions))
      pda
    (let (res)
      (maphash (lambda (k v) (push (list k v) res))
               transitions)
      res)))

;; All transitions from a non-deterministic pda
(defmethod all-transitions ((pda pda-n))
  (with-accessors ((transitions pda-transitions))
      pda
    (let (res)
      (maphash (lambda (k vs)
                 (dolist (v vs)
                   (push (list k v) res)))
               transitions)
      ;; (format t "pda-n:alk-transitions~a~%" res)
      res)))

(defmethod all-transitions-sorted ((pda pda))
  (sort (all-transitions pda) (lambda (a b) (<= (caar a) (caar b)))))


(defun transition-sort-key (transition)
  (let ((state (caar transition)))
    (if (listp state)
               (car state)
               state)))

(defmethod all-transitions-sorted ((pda pda-n))
  (sort (all-transitions pda) (lambda (a b)
                                (<= (transition-sort-key a) (transition-sort-key b)))))

;; ---------------------------------------------------------------------

(defmethod get-transition ((pda pda) key)
  (with-accessors ((transitions pda-transitions))
      pda
      (gethash key transitions)))

;; ---------------------------------------------------------------------

;; - Alg 1 - 5 in Postfix :: From the above Theorems, we can easily
;;   transform Algorithms 1-5 to work with the postfix notation of trees.
;;   The only change required is in the pushdown operations.
;;   - All transitions of the form δ(q, a, S)           = (p, S^Arity(ai))
;;     must be changed to the form δ(q, a, S^Arity(ai)) = (p, S).
;;   - The subtree matching PDA also requires no initial pushdown store symbol,
;;     while after processing a valid tree in postfix notation, the pushdown store
;;     contains a single symbol ’S’.

(defmethod convert-to-postfix ((pda pda))
  "Convert a prefix string matcher to a postfix one.
Does so by swapping the arities in the source and dest of transitions.
Note: This like does the reverse too."
  (let ((transitions (all-transitions pda)))
    ;; Clear out existing transitions
    (setf (pda-transitions pda) (make-hash-table :test 'equal))
    (mapc (lambda (transition)
            (let* ((from (car transition))
                   (to (cadr transition))
                   (from-node (car from))
                   (from-symbol (cadr from))
                   (from-arity (caddr from))
                   (to-node (car to))
                   (to-arity (cadr to)))
            (add-transition pda from-symbol from-node to-node to-arity from-arity)))
          transitions)
    pda))

;; ---------------------------------------------------------------------

(defun eg1-ranked-alphabet ()
  '((:a0 . 0) (:a1 . 1) (:a2 . 2)))

(defun algorithm-1 (ranked-alphabet prefix-tree)
  (let ((pda (new-pda-n ranked-alphabet))
        (node-num 0))
    (mapc
     (lambda (symbol)
       (let ((start-node node-num))
         (setq node-num (+ node-num 1))
         (add-transition pda symbol start-node node-num 1)))
     prefix-tree)
    pda))

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
  (let* ((pda-n (algorithm-1 ranked-alphabet prefix-tree)))
    (mapc (lambda (assoc-symbol)
            (add-transition pda-n (car assoc-symbol) 0 0 1))
          ranked-alphabet)
    pda-n))

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
  ;; 1. Initially, Q' = {{0}}, q1 = {0} and {0} is an unmarked state
  (let* (;; (big-q (pda-states pda-n))
         (big-q-prime (list (list 0)))
         (unmarked big-q-prime)
         (pda-d (new-pda (pda-alphabet pda-n)))
         ;; (q1 0)
         )
    ;; 2.(a) Select an unmarked state q' from Q'
    (loop while (not (null unmarked))
          do
             (progn
               (let ((q-prime (car unmarked)))
                 (setf unmarked (cdr unmarked))
                 (dolist (symbol (pda-alphabet pda-n))
                   ;; 2.(b) For each symbol a ∈ A:
                   ;; 2(b)i. q'' = {q | δ(p,a,α) = (q,β) for all p ∈ q' }
                   (let ((q-prime2 nil))
                     (mapc (lambda (transition)
                             (let* ((k (car transition))
                                    (v (cadr transition))
                                    (p (car k))
                                    (q (car v)))
                               (if (eq (car symbol) (cadr k))
                                   (progn
                                     (if (member p q-prime :test 'equal)
                                         (pushnew q q-prime2 :test 'equal))))))
                           (all-transitions pda-n))
                     ;; 2(b)ii. Add transition δ'(q', a, S) = (q'', S^Arity(a))
                     (add-transition pda-d (car symbol) q-prime q-prime2 1)
                     ;; 2(b)iii. If q'' not ∈ Q then add q'' to Q and set is as unmarked state
                     ;; Note: must be Q' above, else does not make sense.
                     (if (not (member q-prime2 big-q-prime :test 'equal))
                         (progn
                           (push q-prime2 big-q-prime)
                           (push q-prime2 unmarked)))
                     ))))
          )
    (setf (pda-initial-state pda-d) (list 0))
    ;; 4. F' = { q' | (bif-f (pda-final-states pda-n)q' ∈ Q' and q' intersect F /= {} }
    (let ((big-f-prime)
          (big-f (pda-final-states pda-n)))
      (dolist (q-prime big-q-prime)
        (if (intersection q-prime big-f)
            (pushnew q-prime big-f-prime)))
      (setf (pda-final-states pda-d) big-f-prime))
    pda-d))


;; pda-n transitions, by symbol
;;  ((0 :A0 :S) . ((0 0)))
;;  ((2 :A0 :S) . ((3 0)))
;;  ((4 :A0 :S) . ((5 0)))
;;  ((6 :A0 :S) . ((7 0)))
;;
;;  ((0 :A1 :S) . ((0 1)))
;;  ((3 :A1 :S) . ((4 1)))
;;  ((5 :A1 :S) . ((6 1)))
;;
;;  ((0 :A2 :S) . ((0 2) (1 2)))
;;  ((1 :A2 :S) . ((2 2)))
;;
;; So,initial (0)
;;  :A0 -> (0)
;;  :A1 -> (0)
;;  :a2 -> (0 1)
;; Q' = ( (0) (0 1))
;; unmarked = (0 1)


(defun test-algorithm-3 ()
  (let* ((pda-n (algorithm-2 (eg1-ranked-alphabet) (eg1-prefix-tree)))
         (pda-d (algorithm-3 pda-n)))
    (format t "Non-Deterministic---------------------~%")
    (pretty-print-pda pda-n)
    (format t "Deterministic---------------------~%")
    (pretty-print-pda pda-d)))

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
        (big-f '()))
    ;; 2. For each tree ti = a1_i a2_i, .. a|ti|_i, 1 <= i <= m do
    (dolist (tree trees)
      ;; 2(a) Let l <- 0
      (let ((l 0))
        ;; 2(b) For j = 1 to |ti| do
        (dolist (symbol tree)
          ;; 2(b)i. If the transition δ(l, aj_i, S) is not defined then
          (let ((to (get-transition pda (list l symbol 1))))
            (cond
              ((null to)
               (progn
                 ;; A. Let q <- q + 1
                 (setf q (+ q 1))
                 ;; B. Create a transition δ(l, aj_i, S) <- (q, S^Arity(aj_i))
                 ;; C. Let l <- q
                 (add-transition pda symbol l q 1)
                 (setf l q)
                 ))
              (t
               ;; 2(b)ii. Else if transition δ(l, aj_i, S) is defined
               ;;  A. l <- p where (p, γ) <- δ(l, aj, S)
               (setf l (if (listp (car to))
                           ;; Deal with pda-n usage to
                           (caar to)
                           (car to)))))))
        ;; 2(c) F <- F union {l}
        (pushnew l big-f :test 'equal)))
    (setf (pda-initial-state pda) 0)
    (setf (pda-final-states pda) big-f)
    pda))


(defun eg8-ranked-alphabet ()
  '((:a0 . 0) (:a1 . 1) (:a2 . 2)
    (:b0 . 0) (:b1 . 1) ))

   ;; pref(t1) = a2 a2 a0 a0 b0,
   ;; pref(t2) = a2 b1 a0 a0 and
   ;; pref(t3) = a2 a0 a0.

;; -------------------------------------

;; (defun eg8-prefix-tree-1 ()
;;   (list :a2 :a2 :a0 :a0 :b0))

;; (defun eg8-prefix-tree-2 ()
;;   (list :a2 :b1 :a0 :a0))

;; (defun eg8-prefix-tree-3 ()
;;   (list :a2 :a0 :a0))

(defun eg8-tree-1 ()
  '(:a2
    (:a2 :a0 :a0)
    :b0))

(defun eg8-prefix-tree-1 ()
  (list :a2 :a2 :a0 :a0 :b0))
(defun eg8-postfix-tree-1 ()
  (list :a0 :a0 :a2 :b0 :a2))

;; -------------------------------------

(defun eg8-tree-2 ()
    '(:a2
      (:b1 :a0)
      :b0))

(defun eg8-prefix-tree-2 ()
  (list :a2 :b1 :a0 :a0))
(defun eg8-postfix-tree-2 ()
  (list :a0 :b1 :a0 :a2))

;; -------------------------------------

(defun eg8-tree-3 ()
  '(:a2 :a0 :a0))

(defun eg8-prefix-tree-3 ()
  (list :a2 :a0 :a0))

(defun eg8-postfix-tree-3 ()
  (list :a0 :a0 :a2))

;; -------------------------------------

(defun eg8-tree-main ()
  '(:a2
    (:a2
     (:a2 :a0 :a0)
     (:a2
      (:a2 :a0 :a0)
      :b0))
    (:a2
     (:b1 :a0)
     :a0)))

(defun eg8-prefix-tree-main ()
  (list :a2 :a2 :a2 :a0 :a0 :a2 :a2 :a0 :a0 :b0 :a2 :b1 :a0 :a0))

(defun eg8-postfix-tree-main ()
  (list :a0 :a0 :a2 :a0 :a0 :a2 :b0 :a2 :a2 :a0 :b1 :a0 :a2 :a2))

;; -------------------------------------
(defun test-algorithm-4 ()
  ;; (let ((pda-p (algorithm-4 (new-pda (eg8-ranked-alphabet))
  (let ((pda-p (algorithm-4 (new-pda-n (eg8-ranked-alphabet))
                            (eg8-ranked-alphabet)
                            (list (eg8-prefix-tree-1)
                                  (eg8-prefix-tree-2)
                                  (eg8-prefix-tree-3)))))
    (pretty-print-pda pda-p)
    ;; (format t "~S~%" (sort (all-transitions pda-p) (lambda (a b) (<= (caar a) (caar b)))))
    (format t "~S~%" (all-transitions-sorted pda-p))
    (assert
     (equal (all-transitions-sorted pda-p)
            '(((0 :a2 1) (1 2))
              ((1 :a2 1) (2 2))
              ((1 :b1 1) (6 1))
              ((1 :a0 1) (9 0))
              ((2 :a0 1) (3 0))
              ((3 :a0 1) (4 0))
              ((4 :b0 1) (5 0))
              ((6 :a0 1) (7 0))
              ((7 :a0 1) (8 0))
              ((9 :a0 1) (10 0)))))))

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
    (pretty-print-pda pda-n)
    (dolist (symbol (pda-alphabet pda-n))
      (add-transition pda-n (car symbol) 0 0 1))
    pda-n))

(defun test-algorithm-5 ()
  (let ((pda-p (algorithm-5 (eg8-ranked-alphabet)
                            (list (eg8-prefix-tree-1)
                                  (eg8-prefix-tree-2)
                                  (eg8-prefix-tree-3)))))
    (pretty-print-pda pda-p)
    (format t "~S~%" (all-transitions-sorted pda-p))
    (assert
     (equal (all-transitions-sorted pda-p)
            '(((0 :a2 1) (0 2))
              ((0 :a2 1) (1 2))
              ((0 :a0 1) (0 0))
              ((0 :a1 1) (0 1))
              ((0 :b0 1) (0 0))
              ((0 :b1 1) (0 1))
              ((1 :a2 1) (2 2))
              ((1 :b1 1) (6 1))
              ((1 :a0 1) (9 0))
              ((2 :a0 1) (3 0))
              ((3 :a0 1) (4 0))
              ((4 :b0 1) (5 0))
              ((6 :a0 1) (7 0))
              ((7 :a0 1) (8 0))
              ((9 :a0 1) (10 0)))))))

;; ---------------------------------------------------------------------

;; p351
;; - Example 10 :: The deterministic subtree matching PDA for the set of
;;   trees P from Example 8, constructed by Alg. 3 from the
;;   nondeterministic subtree matching PDA Mnps(P ) from Example 9, is

;;     Mdps(P ) =
;;       ({[0],[0,1],[0,1,2],[0,3,9],[0,4,10],[0,5],[0,6],[0,7],[0,8],[0,9],[0,10]}
;;         , A, {S}, δ3, [0], S, {[0,4,10], [0,5], [0 8], [0,10]}),
;;      with its transition diagram (in an actual diagram)

(defun algorithm-5-deterministic (alphabet trees)
  (let* ((pda-n (algorithm-5 alphabet trees))
         (pda-d (algorithm-3 pda-n)))
    pda-d))

(defun test-algorithm-5-deterministic ()
  (let* ((pda-d (algorithm-5-deterministic
                 (eg8-ranked-alphabet)
                 (list (eg8-prefix-tree-1)
                       (eg8-prefix-tree-2)
                       (eg8-prefix-tree-3)))))
    (pretty-print-pda pda-d)
    (format t "~S~%" (all-transitions-sorted pda-d))
    (assert
     (equal (all-transitions-sorted pda-d)
            '((((0) :A0 1) . ((0) 0))
              (((0) :A1 1) . ((0) 1))
              (((0) :A2 1) . ((0 1) 2))
              (((0) :B0 1) . ((0) 0))
              (((0 1) :A0 1) . ((0) 0))
              (((0 1) :A1 1) . ((0) 1))
              (((0 1) :A2 1) . ((0 1 2) 2))
              (((0 1) :B0 1) . ((0) 0))
              (((0 1) :B1 1) . ((0) 1))
              (((0 1 2) :A0 1) . ((3 0) 0))
              (((0 1 2) :A1 1) . ((0) 1))
              (((0 1 2) :A2 1) . ((0 1 2) 2))
              (((0 1 2) :B0 1) . ((0) 0))
              (((0 1 2) :B1 1) . ((0) 1))
              (((3 0) :A0 1) . ((4 0) 0))
              (((3 0) :A1 1) . ((0) 1))
              (((3 0) :A2 1) . ((0 1) 2))
              (((3 0) :B0 1) . ((0) 0))
              (((3 0) :B1 1) . ((0) 1))
              (((4 0) :A0 1) . ((0) 0))
              (((4 0) :A1 1) . ((0) 1))
              (((4 0) :A2 1) . ((0 1) 2))
              (((4 0) :B0 1) . ((5 0) 0))
              (((4 0) :B1 1) . ((0) 1))
              (((5 0) :A0 1) . ((0) 0))
              (((5 0) :A1 1) . ((0) 1))
              (((5 0) :A2 1) . ((0 1) 2))
              (((5 0) :B0 1) . ((0) 0))
              (((5 0) :B1 1) . ((0) 1))
              )))))

;; ---------------------------------------------------------------------
;; Postfix matching
;; p 354
;;
;; - Alg 1 - 5 in Postfix :: From the above Theorems, we can easily
;;   transform Algorithms 1-5 to work with the postfix notation of trees.
;;   The only change required is in the pushdown operations.
;;   - All transitions of the form δ(q, a, S)           = (p, S^Arity(ai))
;;     must be changed to the form δ(q, a, S^Arity(ai)) = (p, S).
;;   - The subtree matching PDA also requires no initial pushdown store symbol,
;;     while after processing a valid tree in postfix notation, the pushdown store
;;     contains a single symbol ’S’.

(defun test-convert-to-postfix ()
  (let* ((pda-d (algorithm-5-deterministic
                 (eg8-ranked-alphabet)
                 (list (eg8-prefix-tree-1)
                       (eg8-prefix-tree-2)
                       (eg8-prefix-tree-3))))
         (pda-post (convert-to-postfix pda-d)))
    (pretty-print-pda pda-d)
    (pretty-print-pda pda-post)))

;; ---------------------------------------------------------------------
;; Running a PDA
;; ---------------------------------------------------------------------

(defclass pda-run ()
  ((%pda :initarg :pda :accessor run-pda-pda)
   (%transitions :initform nil :accessor run-pda-transitions)
   (%state :initarg :state :accessor run-pda-state)
   (%stack :initarg :stack :initform (list 1) :accessor run-pda-stack)))

(defmethod initialize-instance :after ((run pda-run) &key)
  "Create a cache of transitions, in a form ready for quick use."
  (let ((transitions (make-hash-table :test 'equal))
        (pda-transitions (all-transitions (run-pda-pda run))))
    (dolist (transition pda-transitions)
      ;; e.g. ( ((7 0) B1 1) ((0) 1))
      (let* ((key (car transition))
             (value (cadr transition))
             (from-state (car key))
             (from-symbol (cadr key))
             (match-arity (caddr key))
             (to-state (car value))
             (push-arity (cadr value))
             (cache-key (list from-state from-symbol))
             (cache-value (list match-arity to-state push-arity)))
        (setf (gethash cache-key transitions) cache-value)))
    (setf (run-pda-transitions run) transitions)))


(defmethod in-final-state ((run pda-run))
  "If the current states is a final one, return it, else NIL."
  (if (member (run-pda-state run) (pda-final-states (run-pda-pda run)))
      (run-pda-state run)
      nil))

(defmethod transition ((run pda-run) symbol)
  "Given input SYMBOL, advance the PDA RUN.
The PDA is updated internally. Returns the state if it is accepting, else NIL."
  (format t "transition: ~a~%" symbol)
  (let* ((state (run-pda-state run))
         (value (gethash (list state symbol) (run-pda-transitions run)))
         (match-arity (car value))
         (to-state (cadr value))
         (push-arity (caddr value))
         (stack (run-pda-stack run)))
    ;; Check for valid stack match. In our degenerate case this is just a numeric check
    (if (>= stack match-arity)
        (progn
          ;; We're valid, pop match-arity and push push-arity, then change state
          (let ((new-stack (+ (- stack match-arity) push-arity)))
            (setf (run-pda-stack run) new-stack)
            (setf (run-pda-state run) to-state))
          (in-final-state run))
        (progn
          (format t "transition:could not match stack: stack, match-arity ~a, ~a~%" stack match-arity)
          nil))))


;; ---------------------------------------------------------------------
;;
;; - Trace Fig 15 :: Trace of deterministic subtree PDA Mdps(P ) from
;;   Example 10 for tree t2 in prefix notation
;;     pref(t) = a2 a2 a2 a0 a0 a2 a2 a0 a0 b0 a2 b1 a0 a0.
;;
;;   | State      | Input                                     | PDS  |   |
;;   |------------+-------------------------------------------+------+---|
;;   | {0}        | a2 a2 a2 a0 a0 a2 a2 a0 a0 b0 a2 b1 a0 a0 | S    |   |
;;   | {0, 1}     | a2 a2 a0 a0 a2 a2 a0 a0 b0 a2 b1 a0 a0    | SS   |   |
;;   | {0, 1, 2}  | a2 a0 a0 a2 a2 a0 a0 b0 a2 b1 a0 a0       | SSS  |   |
;;   | {0, 1, 2}  | a0 a0 a2 a2 a0 a0 b0 a2 b1 a0 a0          | SSSS |   |
;;   | {0, 3, 9}  | a0 a2 a2 a0 a0 b0 a2 b1 a0 a0             | SSS  |   |
;;   | {0, 4, 10} | a2 a2 a0 a0 b0 a2 b1 a0 a0          match | SS   |   |
;;   | {0, 1}     | a2 a0 a0 b0 a2 b1 a0 a0                   | SSS  |   |
;;   | {0, 1, 2}  | a0 a0 b0 a2 b1 a0 a0                      | SSSS |   |
;;   | {0, 3, 9}  | a0 b0 a2 b1 a0 a0                         | SSS  |   |
;;   | {0, 4, 10} | b0 a2 b1 a0 a0                      match | SS   |   |
;;   | {0, 5}     | a2 b1 a0 a0                         match | S    |   |
;;   | {0, 1}     | b1 a0 a0                                  | SS   |   |
;;   | {0, 6}     | a0 a0                                     | SS   |   |
;;   | {0, 7}     | a0                                        | S    |   |
;;   | {0, 8}     | ε                                   match | ε    |   |

(defun test-run-pda-1 ()
  (let* ((pda-d (algorithm-5-deterministic
                 (eg8-ranked-alphabet)
                 (list (eg8-prefix-tree-1)
                       (eg8-prefix-tree-2)
                       (eg8-prefix-tree-3))))
         (runner (make-instance 'pda-run :pda pda-d :state (list 0) :stack 1))
         (input (eg8-prefix-tree-main)))
    (pretty-print-pda pda-d)
    (let (res)
      (dolist (symbol input)
        (let ((accepting (transition runner symbol)))
          (if accepting
              (format t "match: ~a~%" accepting))
          (push (list (run-pda-state runner) accepting) res)))
      (format t "res: ~a~%" (reverse res))
      (assert (equal (reverse res)
                     '(((0 1) NIL)
                       ((0 1 2) NIL)
                       ((0 1 2) NIL)
                       ((3 9 0) NIL)
                       ((4 10 0) (4 10 0))
                       ((0 1) NIL)
                       ((0 1 2) NIL)
                       ((3 9 0) NIL)
                       ((4 10 0) (4 10 0))
                       ((5 0) (5 0))
                       ((0 1) NIL)
                       ((6 0) NIL)
                       ((7 0) NIL)
                       ((8 0) (8 0))))))))

;; ---------------------------------------------------------------------

;; Run a PDA in postfix


(defun test-run-pda-postfix-1 ()
  (let* ((pda-d (algorithm-5-deterministic
                 (eg8-ranked-alphabet)
                 ;; (list (eg8-prefix-tree-1)
                 ;;       (eg8-prefix-tree-2)
                 ;;       (eg8-prefix-tree-3))))
                 (list (eg8-postfix-tree-1)
                       (eg8-postfix-tree-2)
                       (eg8-postfix-tree-3))))
         (pda-post (convert-to-postfix pda-d))
         (runner (make-instance 'pda-run :pda pda-post :state (list 0) :stack 0))
         (input (eg8-postfix-tree-main)))
    (pretty-print-pda pda-post)
    (let (res)
      (dolist (symbol input)
        (let ((accepting (transition runner symbol)))
          (if accepting
              (format t "match: ~a~%" accepting))
          (push (list (run-pda-state runner) accepting) res)))
      (format t "res: ~a~%" (reverse res))
      (assert (equal (reverse res)
                     '(((0 1) NIL)
                       ((0 1 2) NIL)
                       ((3 0) (3 0)) ;;;;;;;;
                       ((0 1) NIL)
                       ((0 1 2) NIL)
                       ((3 0) (3 0)) ;;;;;;;;;;
                       ((4 0) NIL)
                       ((5 0) (5 0)) ;;;;;;;;;;
                       ((0) NIL)
                       ((0 1) NIL)
                       ((6 0) NIL)
                       ((0 1 7) NIL)
                       ((8 0) (8 0)) ;;;;;;;;;;;
                       ((0) NIL))
                       )))))

;; =====================================================================
;; ---------------------------------------------------------------------
;; =====================================================================
;; This part pased on
;; "Tree template matching in ranked ordered trees by pushdown automata" 2012 by Flouri et al
;; DOI: 10.1016/j.jda.2012.10.003


;; ---------------------------------------------------------------------
;; - Theorem 3 :: Let x be a factor of the postfix notation post(t) of
;;   some tree t over a ranked alphabet A = (Σ, φ).
;;   Then x is the postfix notation of a subtree of t,
;;   if and only
;;     if ac(x) = 0,and ac(y) >= 1 for each y,
;;      where x = zy, y, z ∈ Σ+.
;;
;; AZ Note: probably much simpler to just use the original tree.

;; (defun

;; ---------------------------------------------------------------------
;; - Definition 8 (Set of subtrees) :: Given a tree t formed over a
;;   ranked alphabet A_S = (Σ_S, φ_S) such that post(t) = x1x2 ...xm, the
;;   set of subtrees of t is the set Sub(t) consisting of the postfix
;;   notations of all subtrees of t, and is formally defined as:
;;
;;      Sub(t) = {x: post(t) = yxz, y,z ∈ Σ∗, x ∈ Σ+, x ≠ S}
;;                such that Theorem 3 holds for each x ∈ Sub(t).
(defun set-of-subtrees-worker (tree)
  (if (listp tree)
      (append (list tree) (mapcan #'set-of-subtrees-worker (cdr tree)) )
      (list tree)))

(defun set-of-subtrees (tree)
  "Sub(post)"
  (let ((all-trees (set-of-subtrees-worker tree))
        uniques)
    (dolist (subtree all-trees)
      (pushnew subtree uniques :test 'equal))
    (mapcar (lambda (subtree) (postfix subtree)) uniques)))


;; ---------------------------------------------------------------------
;; - Algorithm 1 :: Construction of a nondeterministic tree template matching PDA.
;;
;;   Input :Tree template post(P) = post(p1)post(p2)...post(p_φ(v))v over A
;;   Output: Nondeterministic PDA M = ({q_I, q_F}, A, Γ, δ,{q_I}, ε, {q_F})
;;
;;    1 Let Γ ← {{x}: x ∈ Sub(P)} ∪ {{S}}
;;
;;    2 For each x ∈ Σ,let q_I T^φ(x) x −→Mx  q_I T, where T ={S}
;;
;;    3 Let q_I X_φ(x) ... X_2 X_1 −→Mx  q_I X,
;;        where
;;          X_i ={post(t_i)},
;;          X ={post(t)},
;;            for each post(t) = post(t_1)post(t_2)... post(t_φ(x))x ∈ Sub(P ) \ {post(P)}
;;
;;    4 Let q_I X_φ(v) ... X2 X1 −→ Mv  q_F X, where X_i = {post(p_i)}, X = {post(P)}

;; We modify it to take in the original tree, and generate postfix as
;; needed. This is more true to the real world use case.
(defun algorithm-2-1 (alphabet tree)
   ;; 1. Let Γ ← {{x}: x ∈ Sub(P)} ∪ {{S}}
  (let* ((pda-n (new-pda-t-n alphabet))
         (subsets (set-of-subtrees tree))
         (gamma (pushnew (list :S) subsets :test 'equal))
         (q_initial (list 0))
         (q_final (list 1)))
    (format T "alg-2-1:gamma ~a~%" gamma)
    ;; 2 For each x ∈ Σ,let q_I T^φ(x) x −→Mx  q_I T, where T ={S}
    ;; For simplicity, in the rest of the text, we use the notation
    ;;      pα  −→Ma qβ
    ;;   when referring to the transition
    ;;      δ(p, a, α) = (q,β) of a PDA M.
    (dolist (symbol-assoc alphabet)
      ;; let q_I T^φ(x) x −→Mx  q_I T
      ;; i.e.  δ(q_I, T^φ(x), x) = (q_I,T)
      (let ((match-arity 0)
            (push-arity 0))
        (add-transition pda-n (car symbol-assoc) q_initial q_initial match-arity push-arity)))

   ;; 3 Let q_I X_φ(x) ... X_2 X_1 −→Mx  q_I X,
   ;;     where X_i ={post(t_i)}, X ={post(t)},for each post(t) = post(t_1)post(t_2)... post(t_φ(x))x ∈ Sub(P ) \{post(P)}

    pda-n))

(defun eg17-template-tree ()
  '(:a2
    (:a2
     (:a2 :a0 :S)
     (:a2 :S  :S))
    (:a2 :S :b0)))

(defun eg17-template ()
  (list :a0 :S :a2 :S :S :a2 :a2 :S :b0 :a2 :a2))

(defun test-set-of-subtrees ()
  (let ((subtrees (set-of-subtrees (eg17-template-tree))))
    (format t "~a~%" subtrees)
    (assert
     (equal subtrees
            '((:B0)
              (:S :B0 :A2)
              (:S :S :A2)
              (:S)
              (:A0)
              (:A0 :S :A2)
              (:A0 :S :A2 :S :S :A2 :A2)
              (:A0 :S :A2 :S :S :A2 :A2 :S :B0 :A2 :A2)
              )))))

;; Expecting
;; X2 → b0
;; X5 → S b0 a2
;; X4 → S S a2
;; T → S
;; X1 → a0
;; X3 → a0 S a2
;; X6 → a0 S a2 S S a2 a2
;; X7 → a0 S a2 S S a2 a2 S b0 a2 a2

(defun test-algorithm-2-1 ()
  (let ((pda (algorithm-2-1 (eg1-ranked-alphabet) (eg17-template-tree))))
    (pretty-print-pda pda)))



;; =====================================================================
;; Hoffmann and O'Donnell : Pattern Matching in Trees
;; https://dl.acm.org/doi/10.1145/322290.322295
;; =====================================================================

;; p73
;; - Example 3.1 :: Consider a matching problem in which the patterns
;;     p1 = a(a(v,v),b)
;;     p2 = a(b,v)
;;   are to be matched. Assume the alphabet Σ is {a,b,c}, where a is
;;   binary, and b and c are nullary symbols.

(defun eg-3.1-ranked-alphabet ()
  '((:a . 2) (:b . 0) (:c . 0)))

(defun eg-3.1-p1 ()
  "p1 = a(a(v,v),b)"
  '(:a
    (:a :v :v)
    :b))

(defun eg-3.1-p2 ()
  "p2 = a(b,v)"
  '(:a :b :v))

;; p74
;; - Definition 4.1 :: Let F = {p1, .., pk} be a set of patterns in S_v
;;   and *PF* the set of all subtrees of the pi. A subset M of PF is a
;;   *match set* for F if there exists a tree t in S such that every
;;   pattern in M matches t at the root and every pattern in PF - M does
;;   not match t at the root.

;; ---------------------------------------------------------------------
;; Tree Arena Start
;; ---------------------------------------------------------------------

;; AZ note: for a tree stored in an arena, each node is simply an arena index.
;; So mimic this one-way mapping.

(defclass tree-arena ()
  ((%trees :initarg :trees :initform '() :accessor ta-trees)
   (%ids :initarg :ids :initform (make-array 0 :fill-pointer t :adjustable t) :accessor ta-ids)
   (%last-index :initform 0 :accessor ta-last-index)))

(defun pretty-print-tree-arena (ta &optional (stream t))
  (format stream "Tree Arena~%")
  (format stream "ta-trees:~a~%" (ta-trees ta))
  (format stream "ta-ids:~a~%" (ta-ids ta))
  (format stream "ta-last-index:~a~%" (ta-last-index ta))
  (terpri stream))

(defmethod add-node ((tree-arena tree-arena) node)
  (with-accessors ((trees ta-trees)
                   (ids ta-ids))
      tree-arena
    (format t "add-node:node=~a~%" node)
    (let ((last-index (vector-push-extend node ids)))
      (format t "add-node:last-index=~a~%" last-index)
      (setf (ta-last-index tree-arena) last-index))))

(defmethod add-tree ((tree-arena tree-arena) tree)
  (with-accessors ((trees ta-trees)
                   (ids ta-ids))
      tree-arena
    (format t "add-tree:tree=~a~%" tree)
    ;; Add all the immediate subtrees
    (if (listp tree)
        (progn
          ;; For a tree, do the subtrees then the root
          (dolist (node (cdr tree))
            (add-tree tree-arena node))
          (add-node tree-arena tree))
        (add-node tree-arena tree))))

(defmethod map-subtrees ((tree-arena tree-arena) fun)
  "Iterate over all the subtrees, with a function taking its id and the subtree."
  (with-accessors ((trees ta-trees)
                   (ids ta-ids)
                   (last-index ta-last-index))
      tree-arena
    (dotimes (idx (+ 1 last-index))
      (apply fun idx  (list (aref ids idx))))))

(defun tree-height (tree)
  "Return the height of a TREE."
  (if (listp tree)
      (let ((sub-heights (mapcar 'tree-height (cdr tree) )))
        (+ 1 (reduce #'max sub-heights)))
      0 ;; leaf has height 0
      ))

(defmethod subtrees-by-height ((tree-arena tree-arena))
  "Return (HEIGHT IDX SUBTREE) for each subtree in a list."
  (with-accessors ((trees ta-trees)
                   (ids ta-ids)
                   (last-index ta-last-index))
      tree-arena
    (let (all-trees)
      (map-subtrees tree-arena
                    (lambda (idx tree)
                      (push (list (tree-height tree) idx tree) all-trees)))
      (let ((sorted (sort all-trees #'< :key #'car)))
        (format t "subtrees-by-height:all-trees: ~a~%" sorted)
        sorted
        )
      )))


(defun test-tree-arena ()
  (let ((ta (make-instance 'tree-arena)))
    (pretty-print-tree-arena ta)
    (add-tree ta (eg-3.1-p1))
    (add-tree ta (eg-3.1-p2))
    (pretty-print-tree-arena ta)
    (map-subtrees ta
                  (lambda (idx tree)
                    (format t "idx tree: ~a,~a~%" idx tree)))
    (terpri)
    (subtrees-by-height ta)
    ))

;; ---------------------------------------------------------------------
;; Tree Arena End
;; ---------------------------------------------------------------------

;; p75
;; - Definition 4.2 ::
;;   (1) if a is a nullary symbol, then
;;        Match(a) = {a,v} if a is in PF
;;                   {v} otherwise
;;
;;   (2) if a is q-ary, a>0 then
;;         Match(a(t1, .. tq)) = {v} ∪ { p' | p' has root a and is in PF, and for
;;                                            1 ≤ j ≤ q, son_j(p) is in Match(t_j)}

(defclass match-set ()
  ((%alphabet :initarg :alphabet :accessor pf-alphabet)
   (%pf :initarg :pf :initform '() :accessor pf)
   ))

(defmethod add-match ((match-set match-set) symbol)
  (with-accessors ((alphabet pf-alphabet)
                   (pf pf))
      match-set
    (let ((arity (cdr (assoc symbol alphabet))))
      (format t "add-match:arity: ~a~%" arity)
      (if (eq arity 0)
          (progn
            ;; nullary
            (if (member symbol pf)
                (progn
                  (format t "add-match:symbol ~a in pf ~a~%" symbol pf)
                  (pushnew (list symbol :v) pf :test 'equal)
                  )
                (progn
                  (pushnew (list :v) pf :test 'equal)
                  (format t "add-match:symbol ~a not in pf ~a~%" symbol pf))
                )
            )
          (progn
            ;; Not nullary
            )
        ))))

(defmethod make-pf ((match-set match-set) pattern-trees)
  (with-accessors ((alphabet pf-alphabet)
                   (pf pf))
      match-set
    ;; First process all the nullary symbols in the trees
    (dolist (symbol-assoc alphabet)
      (let ((symbol (car symbol-assoc))
            (arity (cdr symbol-assoc)))
        (format t "make-pf:symbol-assoc ~a~%" symbol-assoc)
        (format t "make-pf:symbol ~a~%" symbol)
        (format t "make-pf:arity ~a~%" arity)
        (if (eq arity 0)
            (add-match match-set symbol))
        ))
    ))

(defun test-match-set ()
  (let ((pf (make-instance 'match-set :alphabet (eg-3.1-ranked-alphabet))))
  (make-pf pf (list (eg-3.1-p1) (eg-3.1-p2)))))

;; Algorithm A, p80
;;   Input: Simple pattern forest F
;;   Output: Subsumption graph Gb_S for F
;;   Method:
;;   1. List the trees in PF by increasing height.
;;   2. Initialise Gb_S to the graph with vertices PF and no edges
;;   3. For each p = a(p1, .., pm), m ≥ 0, of height h, by increasing order of height, do
;;   4.   For each p' in PF of height ≤ h do
;;   5.     If p' = v or
;;             p' = a(p1', .., pm') where,
;;                for 1 ≤ j ≤ m, pi -> pi' is in Gb_S
;;          then
;;   6.        Add p -> p' to Gb_S

;; Algorithm A requires
;;   O(patsize^2 x rank) time
;;   O(patsize^2) space

(defun algorithm-a (trees)
  (let ((ta (make-instance 'tree-arena)))
    (pretty-print-tree-arena ta)
    (dolist (tree trees)
      (add-tree ta tree))
    (pretty-print-tree-arena ta)
    (terpri)
    (let ((subtrees-by-height (subtrees-by-height ta))
          gb-s
          edges)
      ;; 2. Initialise Gb_S to the graph with vertices PF and no edges
      (dolist (subtree-item subtrees-by-height)
        (let ((idx (cadr subtree-item)))
          (push idx gb-s)))
      ;; 3. For each p = a(p1, .., pm), m ≥ 0, of height h, by increasing order of height, do
      (dolist (subtree-item subtrees-by-height)
        (let ((height-p (car subtree-item))
              (idx-p (cadr subtree-item))
              (tree-p (caddr subtree-item)))
          (format t "alg-a:p: ~a ~a ~a~%" height-p idx-p tree-p)
          ;; 4.   For each p' in PF of height ≤ h do
          (dolist (subtree-item subtrees-by-height)
            (let ((height-p-prime (car subtree-item))
                  (idx-p-prime (cadr subtree-item))
                  (tree-p-prime (caddr subtree-item)))
              ;; (format t "alg-a:p' ~a ~a ~a~%" height-p-prime idx-p-prime tree-p-prime)
              (if (<  height-p-prime height-p)
                  (let ((is-in-gb-s nil))
                    (format t "alg-a:p' ~a ~a ~a~%" height-p-prime idx-p-prime tree-p-prime)
                    ;; 5. If p' = v or
                    ;;       p' = a(p1', .., pm') where,
                    ;;          for 1 ≤ j ≤ m, pi -> pi' is in Gb_S
                    (if (or (eq tree-p-prime :v)
                            is-in-gb-s)
                        (progn
                          (format t "alg-a:p' ~a~%" "eq")
                          ;; 6. Add p -> p' to Gb_S
                          (push (list idx-p idx-p-prime) edges))
                        )
                    )))
              ))
          (terpri)
        (format t "alg-a:gb-s ~a~%" gb-s)
        (format t "alg-a:edges ~a~%" edges)
          )))))

(defun test-algorithm-a ()
  (algorithm-a (list (eg-3.1-p1) (eg-3.1-p2))))
