(defpackage #:trie-map
  (:use #:cl
        #:trivia)
  )
(in-package #:trie-map)
;; (ql:quickload "tree-matching")
;; (in-package :trie-map)

;; ---------------------------------------------------------------------

;; Working through
;; [[id:20250619T194826.641663][Triemaps that match]]
;; [cite:@jonesTriemapsThatMatch2024]
;;
;; Accompanying code is at https://github.com/simonpj/triemap-paper

;; type Var = String
;; data Expr = App Expr Expr | Lam Var Expr | Var Var


;; ---------------------------------------------------------------------
;; Forward declaration from 3.6

(defclass trie-map ()
  ()
  (:documentation "Base class for TrieMap implementations."))

;; ---------------------------------------------------------------------
;; Forward declaration from 3.7

(defclass se-map (trie-map)
  ((%se-contents :accessor se-contents :initform 'se-empty)
   (%se-empty-contents :accessor se-empty-contents :initarg :se-empty-contents))
  (:documentation "SEMap tm v"))

(defun empty-sem (make-contents)
  (make-instance 'se-map :se-empty-contents make-contents))

(defun empty-em ()
  (empty-sem #'(lambda () (make-instance 'expr-map))))

;; ---------------------------------------------------------------------
;; 3.1 interface

(defclass expr-map (trie-map)
  ((%em-var :accessor em-var :initform (make-hash-table :test 'equal))
   ;; For the :app constructor, an expr-map for e1 containing an expr-map for e2
   (%em-app :accessor em-app :initform nil)
   (%em-app-v :accessor em-app-v :initform nil))
  (:documentation "ExprMap v"))



;; ---------------------------------------------------------------------

(defgeneric my-pretty-print (thing &optional (depth) (stream))
  (:documentation "Pretty print."))

(defmethod my-pretty-print ((obj t) &optional (depth 0) (stream t))
  "Default pretty print."
  (format stream "~v,t~a~%" depth obj))

(defmethod my-pretty-print ((hash-table hash-table) &optional (depth 0) (stream t))
  (format stream "~v,tHASH_MAP:~%" depth)
  (maphash (lambda (k v)
             (format stream "~v,t  (~S .~%" depth k)
             (my-pretty-print v (+ 4 depth) stream)
             (format stream "~v,t  )~%" depth))
           hash-table)
  )

(defmethod my-pretty-print ((expr-map expr-map) &optional (depth 0) (stream t))
  (format stream "~v,tEXPR-MAP:~a~%" depth expr-map)
  (let ((depth1 (+ 2 depth)))
    (format stream "~v,tEXPR-MAP-em-var:~%" depth1)
    (maphash (lambda (k v)
               (format stream "~v,t  (~S .~%" depth1 k)
               (my-pretty-print v (+ 4 depth1) stream)
               (format stream "~v,t  )~%" depth1))
             (em-var expr-map))
    (format stream "~v,tEXPR-MAP-em-app:~%" depth1)
    (if (not (null (em-app expr-map)))
        (my-pretty-print (em-app expr-map) (+ 2 depth1))
        (format stream "~v,t  NIL~%" depth1))
    (format stream "~v,tEXPR-MAP-em-app-v:~%" depth1)
    (if (not (null (em-app-v expr-map)))
        (my-pretty-print (em-app-v expr-map) (+ 2 depth1))
        (format stream "~v,t  NIL~%" depth1))
    ))

;; ---------------------------------------------------------------------

(defvar test-expr '(:app (:var "a") (:var "b")))
(defvar test-em (empty-em))

(defmethod lk-em (expr (expr-map expr-map))
  "Look up EXPR in EXPR-MAP."
  (format t "expr: ~a~%" expr)
  (format t "expr-map: ~a~%" expr-map)
  (with-accessors ((em-var em-var)
                   (em-app em-app)
                   (em-app-v em-app-v))
      expr-map
    (format t "em-var: ~a~%" em-var)
    (format t "em-app: ~a~%" em-app)
      (match expr
        ((list :var v) (gethash v em-var))
        ((list :app e1 e2)
         (if (not (null em-app))
             (let ((m1 (lk-em e1 em-app)))
               (format t "m1: ~a~%" m1)
               (cond
                 ((null m1) nil)
                 (t (lk-em e2 m1))))
             nil))
        ((list :app-v e1 e2)
         (if (not (null em-app-v))
             (let ((m1 (lk-em e1 em-app-v)))
               (format t "m1: ~a~%" m1)
               (cond
                 ((null m1) nil)
                 (t (lk-em e2 m1))))
             nil))
        (oops (error "match failed:~A ~%" oops)))))

(defun alter-map (f key map)
  "Apply F to the value in the hash-map MAP at KEY (or to nil if not found).
Store the result in the MAP."
  ;; (format t "alter-map:f: ~a~%" f)
  ;; (format t "alter-map:key: ~a~%" key)
  ;; (format t "alter-map:map: ~a~%" map)
  ;; (format t "alter-map:old-val1: ~a~%" (gethash key map))
  (setf (gethash key map) (funcall f (gethash key map))))


(defun lift-tf-em (f)
  "Take a function F which takes an expr-map as an argument and returns
one, turn it into  TF returning an expr-map."
  ;; type TF v = Maybe v → Maybe v
  ;; liftTF :: (ExprMap v → ExprMap v) → TF (ExprMap v)
  ;; liftTF f Nothing = Just (f emptyEM)
  ;; liftTF f (Just m) = Just (f m)
  (lambda (em)
    (declare (type (or null expr-map) em))
    (let ((em2 (if (null em) (empty-em) em)))
      (funcall f em2)
      em2)))

(defmethod at-em (expr tf (expr-map expr-map))
  "Alter EXPR-MAP at EXPR using update function TF."
  (with-accessors ((em-var em-var)
                   (em-app em-app)
                   (em-app-v em-app-v))
      expr-map
    (format t "at-em: entry:expr:~a~%" expr)
    (my-pretty-print expr-map 0)
    (format t "at-em: entry done~%")
    (match expr
      ((list :var v)
       (format t "at-em:var:v: ~a~%" v)
       (format t "at-em:var:em-var: ~a~%" em-var)
       (alter-map tf v em-var))
      ((list :app e1 e2)
       ;; App e1 e2 → m { em_app = atEM e1 (liftTF (atEM e2 tf )) app }
       (let ((em-app2 (if (null em-app) (empty-em) em-app)))
         (setf em-app (at-em e1 (lift-tf-em (lambda (em) (at-em e2 tf em))) em-app2))
         (my-pretty-print em-app 0)
         ))
      ;; ------------------------------
       ((list :app-v e1 e2)
        (format t "at-em:app-v:e1: ~a~%" e1)
        (format t "at-em:app-v:e2: ~a~%" e2)
        (let ((em-app-v2 (if (null em-app-v) (empty-em) em-app-v))
              (lm-proto (empty-lm #'empty-em))) ;; TODO: lm-proto should be a field if expr-map
          (setf em-app-v (at-tm e1 (lift-tf-lm lm-proto (lambda (em) (at-lm e2 tf em))) em-app-v2))
          (format t "at-em:app-v:em-app-v: ~a~%" em-app-v)
          (my-pretty-print em-app-v 0)
          ))
      ;; ------------------------------
      (oops (error "match failed:~a ~%" oops)))
    (format t "at-em: exiting~%")
    (my-pretty-print expr-map 0)
    (format t "at-em: exiting done~%")
    expr-map))

(defmethod insert-em (expr v (expr-map expr-map))
  "Insert V as the value for key EXPR in EXPR-MAP."
  (at-em expr (lambda (x)
                (declare (ignore x))
                v)
         expr-map))

(defmethod delete-em (expr (expr-map expr-map))
  "Delete the entry for EXPR in EXPR-MAP."
  (at-em expr #'(lambda (x)
                (declare (ignore x))
                nil)
         expr-map))


;; We can easily define insert-em and delete-em from at-em:
;;
;; insertEM :: Expr → v → ExprMap v → ExprMap v
;; insertEM e v = atEM e (\_ → Just v)
;;
;; deleteEM :: Expr → ExprMap v → ExprMap v
;; deleteEM e = atEM e (\_ → Nothing)


;; ---------------------------------------------------------------------

(defun t1 ()
  (lk-em test-expr test-em))

(defun t2 ()
  (setf test-em (empty-em))
  (insert-em '(:var "x") 'v test-em)
  (format t "test-em: ~a~%" test-em)
  (my-pretty-print test-em 0))

(defun t3 ()
  (setf test-em (empty-em))
  (insert-em '(:app (:var "x") (:var "y")) 'inserted-val test-em)
  (format t "test-em:--------------------~%")
  (format t "test-em: ~a~%" test-em)
  (my-pretty-print test-em 0)
  (format t "test-em:lkup--------------------~%")
  (lk-em '(:app (:var "x") (:var "y")) test-em)
  )

(defun t4 ()
  (setf test-em (empty-em))
  (insert-em '(:app (:var "x") (:var "y")) 'inserted-val test-em)
  (insert-em '(:app (:var "z") (:var "y")) 'other-val test-em)
  (insert-em '(:app (:app (:var "z1") (:var "z2")) (:var "z3")) 'z-val test-em)
  (format t "test-em:--------------------~%")
  (format t "test-em: ~a~%" test-em)
  (my-pretty-print test-em 0)
  (format t "test-em:lkup--------------------~%")
  (format t "first lookup:~a~%"
          (lk-em '(:app (:var "x") (:var "y")) test-em))
  (format t "second lookup:~a~%"
          (lk-em '(:app (:var "z") (:var "y")) test-em))
  (format t "third lookup:~a~%"
          (lk-em '(:app (:app (:var "z1") (:var "z2")) (:var "z3")) test-em))
  )

;; This reaches the end of section 3.3 of the paper.

;; ---------------------------------------------------------------------
;; Section 3.4 Unions of Maps
;; P4

;; Via local qwen3:14b 4k context
(defun hash-table-union (f ht1 ht2)
  (format t "hash-table-union:ht1: ~a~%" ht1)
  (my-pretty-print ht1)
  (format t "hash-table-union:ht2: ~a~%" ht2)
  (my-pretty-print ht2)
  (let ((result (make-hash-table :test (hash-table-test ht1))))
    ;; Copy values from ht1
    (maphash (lambda (k v) (setf (gethash k result) v)) ht1)
    ;; Copy values from ht2, using f to merge if key already exists
    (maphash (lambda (k v)
               (if (gethash k result)
                   (setf (gethash k result) (funcall f (gethash k result) v))
                   (setf (gethash k result) v)))
             ht2)
    (format t "hash-table-union:result: ~a~%" result)
    (my-pretty-print result)
    result))

(defun union-with-em (f expr-map-1 expr-map-2)
  "Make a union of EXPR-MAP-1 and EXPR-MAP-2.
When a key appears on both maps, use the combining function F to combine
the two corresponding values"
  ;; unionWithEM :: (v → v → v) → ExprMap v → ExprMap v → ExprMap v
  ;; When a key appears on both maps, the combining function
  ;; is used to combine the two corresponding values
  (with-accessors ((em-var-1 em-var)
                   (em-app-1 em-app)
                   (em-app-v-1 em-app-v))
      expr-map-1

    (my-pretty-print em-var-1)
    (with-accessors ((em-var-2 em-var)
                     (em-app-2 em-app)
                     (em-app-v-2 em-app-v))
        expr-map-2
      (let ((r (empty-em))
            (em-var-r (hash-table-union f em-var-1 em-var-2))
            (em-app-r
              (cond
                ((null em-app-1) em-app-2)
                ((null em-app-2) em-app-2)
                (t (union-with-em f em-app-1 em-app-2))))
            (em-app-v-r
              (cond
                ((null em-app-v-1) em-app-v-2)
                ((null em-app-v-2) em-app-v-2)
                (t (union-with-em f em-app-v-1 em-app-v-2)))))

        (format t "union-with-em:em-var-r: ~a~%" em-var-r)
        (my-pretty-print em-var-r)
        (format t "union-with-em:em-app-r: ~a~%" em-app-r)
        (my-pretty-print em-app-r)
        (format t "union-with-em:em-app-v-r: ~a~%" em-app-v-r)
        (my-pretty-print em-app-v-r)

        (setf (em-var r) em-var-r)
        (setf (em-app r) em-app-r)
        (setf (em-app-v r) em-app-v-r)
        (format t "union-with-em:r: ~a~%" r)
        (my-pretty-print r)
        r))))


(defun t5 ()
  (let ((em-1 (empty-em))
        (em-2 (empty-em)))
    (insert-em '(:app (:var "x") (:var "y")) 'v1 em-1)
    (insert-em '(:app (:var "x") (:var "z")) 'v2 em-2)
    (format t "-------------------------------~%")
    (format t "em-1: ~a~%" em-1)
    (my-pretty-print em-1 0)
    (format t "-------------------------------~%")
    (format t "em-2: ~a~%" em-2)
    (my-pretty-print em-2 0)
    (format t "-------------------------------~%")
    (let ((r (union-with-em (lambda (v1 v2)
                              (declare (ignore v1))
                              v2)
                            em-1 em-2)))
      (format t "r: ~a~%" r)
      (my-pretty-print r 0)
      )))

;; ---------------------------------------------------------------------
;; Section 3.5 Folds and the empty map
;; P4 (end)

(defun hash-table-foldr (k z hash-map)
  "Fold the values in HASH-MAP using the given right-associative binary operator K, with initial value Z.
This is such that foldr f z == foldr f z . elems."
;; O(n). Fold the values in the map using the given right-associative binary operator, such that foldr f z == foldr f z . elems.
;; > foldr k z []     = z
;; > foldr k z (x:xs) = x `k` foldr f z xs
  (format t "hash-table-foldr:hash-map: ~a~%" hash-map)
  (let ((r z))
    (format t "hash-table-foldr:r0: ~a~%" r)
    (maphash (lambda (key v)
               (declare (ignore key))
               (format t "hash-table-foldr:v: ~a~%" v)
               (format t "hash-table-foldr:r: ~a~%" r)
               (setf r (funcall k v r)))
             hash-map)
    (format t "hash-table-foldr:r1: ~a~%" r)
    r))

;; ---------------------------------------------------------------------
;; foldrLM:
;; fdList :: forall m a b. TrieMap m
;;        => (a -> b -> b) -> ListMap m a -> b -> b
;; fdList k m = foldMaybe k          (lm_nil m)
;;            . foldTM    (fdList k) (lm_cons m)

;; foldMaybe :: (a -> b -> b) -> Maybe a -> b -> b
;; foldMaybe _ Nothing  b = b
;; foldMaybe k (Just a) b = k a b

;; Method on trie-map
   ;; foldTM   :: (a -> b -> b) -> m a -> b -> b
   ;;    -- The unusual argument order here makes
   ;;    -- it easy to compose calls to foldTM;
   ;;    -- see for example fdE below

(defun foldr-lm (k z list-map)
  (format t "foldr-lm:list-map:~a~%" list-map)
  (if (null list-map)
      (progn
        (format t "foldr-lm:null list-map~%")
        z)
      (with-accessors ((lm-nil lm-nil)
                       (lm-cons lm-cons))
          list-map
        (format t "foldr-lm:lm-nil: ~a~%" lm-nil)
        (format t "foldr-lm:lm-cons: ~a~%" lm-cons)
        (labels ((kcons (m1 r)
                   (format t "foldr-lm:kcons:m1:~a~%" m1)
                   (format t "foldr-lm:kcons:r:~a~%" r)
                   (foldr-tm k r m1)))
          (let ((z1 (if (null lm-cons) z (foldr-tm #'kcons z lm-cons))))
            (format t "foldr-lm:z1: ~a~%" z1)
            (if (null lm-nil)
                z1
                (funcall k lm-nil z1))
            ;; (foldr-tm k z1 lm-nil)
            )))))

;; ---------------------------------------------------------------------

;; foldrEM :: ∀v. (v → r → r) → r → ExprMap v → r
;; foldrEM k z (EM { em_var = var, em_app = app })
;;   = Map.foldr k z1 var
;;   where
;;     z1 = foldrEM kapp z (app :: ExprMap (ExprMap v))
;;     kapp m1 r = foldrEM k r m1

(defun foldr-em (k z expr-map)
  (format t "foldr-em:expr-map:~a~%" expr-map)
  (if (null expr-map)
      (progn
        (format t "foldr-em:null expr-map~%")
        z)
      (with-accessors ((em-var em-var)
                       (em-app em-app)
                       (em-app-v em-app-v))
          expr-map
        (format t "foldr-em:em-app:~a~%" em-app)
        (format t "foldr-em:em-app-v:~a~%" em-app-v)
        (labels ((kapp (m1 r)
                   (format t "foldr-em:kapp:m1:~a~%" m1)
                   (format t "foldr-em:kapp:r:~a~%" r)
                   (foldr-tm k r m1))
                 (kappv (m1 r)
                   (format t "foldr-em:kappv:m1:~a~%" m1)
                   (format t "foldr-em:kappv:r:~a~%" r)
                   (foldr-tm k r m1)))
          (let* ((z1 (if (null em-app) z (foldr-tm #'kapp z em-app)))
                 (z2 (if (null em-app-v) z1 (foldr-tm #'kappv z1 em-app-v))))
            (format t "foldr-em:z1:~a~%" z1)
            (format t "foldr-em:z2:~a~%" z2)
            (hash-table-foldr k z2 em-var))))))

(defun size-tm (trie-map)
  (foldr-tm (lambda (v r)
              (declare (ignore v))
              (+ r 1))
            0 trie-map))

(defun elems-tm (trie-map)
  (foldr-tm (lambda (v r) (cons v r))
            nil trie-map))

(defun t6 ()
  (setf test-em (empty-em))
  (insert-em '(:app (:var "x") (:var "y")) 'v1 test-em)
  (insert-em '(:app (:var "z") (:var "y")) 'v2 test-em)
  (format t "test-em:--------------------~%")
  (format t "test-em: ~a~%" test-em)
  (my-pretty-print test-em 0)

  (format t "------------------------------------------~%")
  (format t "count:~a~%"
          (foldr-em (lambda (v r)
                      ;; (declare (ignore b))
                      (format t "t6:v:~a~%" v)
                      (format t "t6:r:~a~%" r)
                      (+ r 1))
                    0 test-em))

  (format t "elems:~a~%" (elems-tm test-em)))

;; ---------------------------------------------------------------------
;; Section 3.6 A type class for triemaps
;; P5

;; class Eq (Key tm) ⇒ TrieMap tm where
;;   type Key tm :: Type
;;   emptyTM :: tm a
;;   lkTM :: Key tm → tm a → Maybe a
;;   atTM :: Key tm → TF a → tm a → tm a
;;   foldrTM :: (a → b → b) → tm a → b → b
;;   unionWithTM :: (a → a → a) → tm a → tm a → tm a

(defclass trie-map ()
  ()
  (:documentation "Base class for TrieMap implementations."))

(defgeneric empty-tm (trie-map)
  (:documentation "Returns an empty TRIE-MAP instance for the given class."))

(defgeneric lk-tm (key trie-map)
  (:documentation "Looks up KEY in TRIE-MAP. Returns the value or NIL if not found."))

(defgeneric at-tm (key f trie-map)
  (:documentation "Alter the value at KEY in TRIE-MAP, by applying F to it."))

(defgeneric foldr-tm (k z trie-map)
  (:documentation "Fold over TRIE-MAP, with combining function K and initial value Z."))

(defgeneric lift-tf-tm (f trie-map)
  (:documentation "Take a function F which takes an TRIE-MAP as an argument and returns
one, turn it into  TF returning an TRIE-MAP."))

;; ---------------------------------------------------------------------
;; Utility functions on TRIE-MAP
;; P5

;; insertTM :: TrieMap tm ⇒ Key tm → v → tm v → tm v
;; insertTM k v = atTM k (\_ → Just v)

(defmethod insert-tm (key v (trie-map trie-map))
  "Insert V as the value for KEY in TM."
  (at-tm key (lambda (x)
                (declare (ignore x))
                v)
         trie-map))

;; deleteTM :: TrieMap tm ⇒ Key tm → tm v → tm v
;; deleteTM k = atTM k (\_ → Nothing)

(defmethod delete-tm (key v (trie-map trie-map))
  "Insert V as the value for KEY in TM."
  (at-tm key (lambda (x)
                (declare (ignore x))
                nil)
         trie-map))

;; ---------------------------------------------------------------------
;; trie-map generic methods for expr-map

(defmethod empty-tm ((expr-map expr-map))
  (empty-em))

(defmethod lk-tm (key (expr-map expr-map))
  (lk-em key expr-map))

(defmethod at-tm (key f (expr-map expr-map))
  (at-em key f expr-map))

;; foldrEM :: ∀v. (v → r → r) → r    → ExprMap v → r
;; foldrTM ::     (a → r → r) → tm a → r         → r
;; AZ: I think the latter signature has swapped the initial and item args
(defmethod foldr-tm (k z (expr-map expr-map))
  (foldr-em k z expr-map))

;; unionWithTM :: (a → a → a) → tm a → tm a → tm a

;; ---------------------------------------------------------------------

(defun t6c ()
  (let ((test-tm (empty-em)))
    (insert-tm '(:app (:var "x") (:var "y")) 'v1 test-tm)
    (insert-tm '(:app (:var "z") (:var "y")) 'v2 test-tm)
    (format t "test-tm:--------------------~%")
    (format t "test-tm: ~a~%" test-tm)
    (my-pretty-print test-tm 0)

    (format t "------------------------------------------~%")
    (format t "count:~a~%"
            (foldr-em (lambda (v r)
                        ;; (declare (ignore b))
                        (format t "t6:v:~a~%" v)
                        (format t "t6:r:~a~%" r)
                        (+ r 1))
                      0 test-tm))

    (format t "elems:~a~%" (elems-tm test-tm))))

;; ---------------------------------------------------------------------
;; ListMap
;; P5

;; data ListMap tm v = LM { lm_nil  :: Maybe v
;;                        , lm_cons :: tm (ListMap tm v) }

;; Key factor is that `lm_cons` has a trie-map of the enclosed
;; trie-map type, with its values being a list-map

(defclass list-map (trie-map)
  ((%lm-nil :accessor lm-nil :initform nil)
   (%lm-cons :accessor lm-cons :initform nil)
   (%empty-contents :accessor lm-empty-contents :initarg :lm-empty-contents)
   )
  (:documentation "ListMap tm v"))

(defmethod my-pretty-print ((list-map list-map) &optional (depth 0) (stream t))
  (format stream "~v,tLIST-MAP:~a~%" depth list-map)
  (let ((depth1 (+ 2 depth)))
    (format stream "~v,tLIST-MAP-lm-nil:~%" depth1)
    (format stream "~v,t~a ~%" (+ 1 depth1) (lm-nil list-map))
    (format stream "~v,tLIST-MAP-lm-cons:~%" depth1)
    (if (not (null (lm-cons list-map)))
        (my-pretty-print (lm-cons list-map) (+ 2 depth1))
        (format stream "~v,t  NIL~%" depth1)))
  )

;; lkLM :: TrieMap tm ⇒ [ Key tm] → ListMap tm v → Maybe v
;; lkLM [ ] = lm_nil
;; lkLM (k : ks) = lm_cons >>> lkTM k >=> lkLM ks

(defmethod lk-lm (key list-map)
  (with-accessors ((lm-nil lm-nil)
                   (lm-cons lm-cons))
      list-map
    (match key
      (nil lm-nil)
      ((cons k ks)
       (let ((lk (lk-tm key k)))
         (if (not (null lk))
             lk
             (lk-lm key ks)))))))

  ;; infixr 1 >=>
  ;; -- Kleisli composition
  ;; (>=>) :: Monad m ⇒ (a → m b) → (b → m c) → a → m c

  ;; infixr 1 >>>
  ;; -- Forward composition
  ;; (>>>) :: (a → b) → (b → c) → a → c

  ;; (|>) :: a -> (a->b) -> b     -- Reverse application
  ;; x |> f = f x

  ;; ----------------------
  ;; (|>>) :: TrieMap m2
  ;;       => (XT (m2 a) -> m1 (m2 a) -> m1 (m2 a))
  ;;       -> (m2 a -> m2 a)
  ;;       -> m1 (m2 a) -> m1 (m2 a)
  ;; (|>>) f g = f (Just . g . deMaybe)

  ;; deMaybe :: TrieMap m => Maybe (m a) -> m a
  ;; deMaybe Nothing  = emptyTM
  ;; deMaybe (Just m) = m

;; GHC TrieMap
;; alterTM  = xtList alterTM

;; xtList :: TrieMap m => (forall b. k -> XT b -> m b -> m b)
;;         -> [k] -> XT a -> ListMap m a -> ListMap m a
;; xtList _  []     f m = m { lm_nil  = f (lm_nil m) }
;; xtList tr (x:xs) f m = m { lm_cons = lm_cons m |> tr x |>> xtList tr xs f }

;; In above, m is ListMap m a
;;   tr is :: k -> XT (ListMap m a) -> m (ListMap m a) -> m (ListMap m a)
;;   b is ListMap m a

;; Key is the |>> operator, which is basically lift-tf

;; Implementation of (|>>)
(defun pipe->-> (f g tm tm-class)
  (let* ((tm2 (if (null tm) (empty-tm tm-class) tm))
        (r (funcall g tm2)))
    (funcall f r)))

;; retrie has same ListMap definition, but
  ;; mAlter :: AlphaEnv -> Quantifiers -> Key (ListMap m) -> A a -> ListMap m a -> ListMap m a
  ;; mAlter env vs []     f m = m { lmNil  = mAlter env vs () f (lmNil m) }
  ;; mAlter env vs (x:xs) f m = m { lmCons = mAlter env vs x (toA (mAlter env vs xs f)) (lmCons m) }
  ;; XT is A in retrie
  ;; toA :: PatternMap m => (m a -> m a) -> A (m a)
  ;; toA f = Just . f . fromMaybe mEmpty

(defun lift-tf-lm (list-map f)
  "Take a function F which takes an list-map as an argument and returns
one, turn it into  TF returning an expr-map."
  ;; type TF v = Maybe v → Maybe v
  ;; liftTF :: (ExprMap v → ExprMap v) → TF (ExprMap v)
  ;; liftTF f Nothing = Just (f emptyEM)
  ;; liftTF f (Just m) = Just (f m)
  (format t "lift-tf-lm: list-map: ~a~%" list-map)
  (lambda (tm)
    (declare (type (or null list-map) tm))
    (format t "lift-tf-lm:lambda:tm: ~a~%" tm)
    (let ((tm2 (if (null tm)
                   (empty-lm (lm-empty-contents list-map))
                   tm)))
      (format t "lift-tf-lm:lambda:tm2: ~a~%" tm2)
      (funcall f tm2)
      tm2)))

(defmethod at-lm (key tf (list-map list-map))
  "Alter LIST-MAP at KEY using update function TF."
  ;; (xt-list #'at-tm key tf list-map)
  (with-accessors ((lm-nil lm-nil)
                   (lm-cons lm-cons))
      list-map
    (format t "at-lm:key: ~a~%" key)
    (match key
      (nil
       (format t "at-lm:nil: ~%")
       (setf lm-nil (funcall tf lm-nil)))
      ((cons x xs)
       (format t "at-lm:cons: ~%")
       (format t "at-lm:lm-cons: ~a~%" lm-cons)
       (format t "at-lm:x: ~a~%" x)
       (format t "at-lm:xs: ~a~%" xs)
       (format t "at-lm:lm-empty-contents: ~a~%" (lm-empty-contents list-map))
       (let ((lm-cons2 (if (null lm-cons)
                           (funcall (lm-empty-contents list-map))
                           lm-cons)))
         (format t "at-lm:lm-cons2: ~a~%" lm-cons2)
         ;; Simplify on the retrie model, which is a variant on lift-tf
         ;; mAlter env vs (x:xs) f m = m { lmCons = mAlter env vs x (toA (mAlter env vs xs f)) (lmCons m) }

         ;; lm_cons is an expr-map, whose items are list-maps. So lm_nil in that case is an expr-map
         (setf lm-cons (at-tm x
                              (lift-tf-lm list-map (lambda (lm)
                                                     (format t "at-lm:lambda:lm: ~a~%" lm)
                                                     (at-tm xs tf lm)))
                              lm-cons2))
         (my-pretty-print lm-cons 0))))
    list-map))

;; -------------------------------------


(defun foldr-lm (k z list-map)
  (format t "foldr-lm:list-map:~a~%" list-map)
  (if (null list-map)
      (progn
        (format t "foldr-lm:null list-map~%")
        z)
      (with-accessors ((lm-nil lm-nil)
                       (lm-cons lm-cons))
          list-map
        (format t "foldr-lm:lm-nil: ~a~%" lm-nil)
        (format t "foldr-lm:lm-cons: ~a~%" lm-cons)
        (labels ((kcons (m1 r)
                   (format t "foldr-lm:kcons:m1:~a~%" m1)
                   (format t "foldr-lm:kcons:r:~a~%" r)
                   (foldr-tm k r m1)))
          (let ((z1 (if (null lm-cons)
                        z
                        (foldr-tm #'kcons z lm-cons))))
            (format t "foldr-lm:z1:~a~%" z1)
            (if (null lm-nil)
                z1
                (funcall k lm-nil z1)))))))

;; -------------------------------------
;; Generic methods
(defun empty-lm (make-contents)
  (make-instance 'list-map :lm-empty-contents make-contents))

(defmethod empty-tm ((list-map list-map))
  (funcall (lm-empty-contents list-map)))

(defmethod lk-tm (key (list-map list-map))
  (lk-lm key list-map))

(defmethod at-tm (key f (list-map list-map))
  (at-lm key f list-map))

(defmethod foldr-tm (k z (list-map list-map))
  (foldr-lm k z list-map))

;; ---------------------------------------------------------------------

;; Motivating example in the paper (P5) is
;; data Expr = ... | AppV Expr [Expr]

(defun t7 ()
  (let ((test-em (empty-em)))
    (format t "1------------------------------------------~%")
    (format t "test-em: ~a~%" test-em)
    (my-pretty-print test-em 0)
    ;; Motivating example in the paper
    (insert-tm '(:app-v (:var "f") ((:var "x") (:var "y"))) 'v1 test-em)

    (format t "2------------------------------------------~%")
    (format t "test-em:--------------------~%")
    (format t "test-em: ~a~%" test-em)
    (my-pretty-print test-em 0)
    (format t "3------------------------------------------~%")
    (insert-tm '(:app-v (:var "f") ((:var "x") (:var "z"))) 'vz test-em)
    (format t "test-em:--------------------~%")
    (format t "test-em: ~a~%" test-em)
    (my-pretty-print test-em 0)
    ))

;; ---------------------------------------------------------------------
;; 3.7 Singleton maps, and empty maps revisited
;; P6
;;
;; data SEMap tm v = EmptySEM
;;                 | SingleSEM (Key tm) v
;;                 | MultiSEM (tm v)



(defmethod my-pretty-print ((se-map se-map) &optional (depth 0) (stream t))
  (format stream "~v,tSE-MAP:~a~%" depth se-map)
  (let ((depth1 (+ 2 depth))
        (depth2 (+ 4 depth)))
    (format stream "~v,tSE-MAP-se-contents:~%" depth1)
    (match (se-contents se-map)
      ('se-empty (format stream "~v,tSE-EMPTY~%" depth2))

      ((list 'se-single k v)
       (format stream "~v,tSE-SINGLE:~%" depth2)
       (my-pretty-print k (+ 2 depth2) stream)
       (my-pretty-print v (+ 2 depth2) stream))

      ((list 'se-multi tm)
       (format stream "~v,tSE-MULTI:~%" depth2)
       (my-pretty-print tm (+ 2 depth2) stream))
      (oops (error "Unexpected se-map contents in pretty-print ~a" oops)))
    (format stream "~v,tSE-MAP-se-empty-contents:~a ~%" depth1 (se-empty-contents se-map))
    ))


;; ---------------------------------------------------------------------

;; P6
;; atSEM :: TrieMap tm ⇒ Key tm → TF v → SEMap tm v → SEMap tm v
;;
;; atSEM k tf EmptySEM = case tf Nothing of
;;   Nothing → EmptySEM
;;   Just v → SingleSEM k v
;;
;; atSEM k1 tf (SingleSEM k2 v2 ) = if k1 == k2
;;   then case tf (Just v2 ) of
;;          Nothing → EmptySEM
;;          Just v’ → SingleSEM k2 v’
;;   else case tf Nothing of
;;          Nothing → SingleSEM k2 v2
;;          Just v1 → MultiSEM (insertTM k1 v1 (insertTM k2 v2 emptyTM))
;;
;; atSEM k tf (MultiSEM tm) = MultiSEM (atTM k tf tm)

;; {-# INLINEABLE xtG #-}
;; xtG :: (Eq (Key m), TrieMap m) => Key m -> XT a -> GenMap m a -> GenMap m a
;; xtG k f EmptyMap
;;     = case f Nothing of
;;         Just v  -> SingletonMap k v
;;         Nothing -> EmptyMap
;; xtG k f m@(SingletonMap k' v')
;;     | k' == k
;;     -- The new key matches the (single) key already in the tree.  Hence,
;;     -- apply @f@ to @Just v'@ and build a singleton or empty map depending
;;     -- on the 'Just'/'Nothing' response respectively.
;;     = case f (Just v') of
;;         Just v'' -> SingletonMap k' v''
;;         Nothing  -> EmptyMap
;;     | otherwise
;;     -- We've hit a singleton tree for a different key than the one we are
;;     -- searching for. Hence apply @f@ to @Nothing@. If result is @Nothing@ then
;;     -- we can just return the old map. If not, we need a map with *two*
;;     -- entries. The easiest way to do that is to insert two items into an empty
;;     -- map of type @m a@.
;;     = case f Nothing of
;;         Nothing  -> m
;;         Just v   -> emptyTM |> alterTM k' (const (Just v'))
;;                            >.> alterTM k  (const (Just v))
;;                            >.> MultiMap
;; xtG k f (MultiMap m) = MultiMap (alterTM k f m)

(defun at-sem (key tf se-map)
  (format t "at-sem:se-map:~a~%" se-map)
  (format t "at-sem:key:~a~%" key)
  (format t "at-sem:contents:~a~%" (se-contents se-map))
  (with-accessors ((se-contents se-contents))
      se-map
    (match (se-contents se-map)
      ('se-empty
       (format t "at-sem:se-empty~%")
       (let ((val (funcall tf nil)))
         (format t "at-sem:se-empty:val:~a~%" val)
         (if (null val)
             (setf se-contents 'se-empty)
             (setf se-contents (list 'se-single key val)))))

      ((list 'se-single k2 v2)
       (format t "at-sem:se-single:k2:~a~%" k2)
       (format t "at-sem:se-single:v2:~a~%" v2)
       (if (equal key k2)
           ;; same keys
           (let ((v (funcall tf v2)))
             (format t "at-sem:se-single:same keys:v:~a~%" v)
             (if (null v)
                 (setf se-contents 'se-empty)
                 (setf se-contents (list 'se-single key v))))
           ;; different keys
           (let ((val (funcall tf nil)))
             (format t "at-sem:se-single:val:~a~%" val)
             (if (null val)
                 (setf se-contents (list 'se-single k2 v2))
                 ;; Else
                 (progn
                   (format t "at-sem:se-single:se-empty-contents:e:~a~%" (se-empty-contents se-map))
                   (let ((sem1 (funcall (se-empty-contents se-map))))
                     (format t "at-sem:se-single:sem1:e:~a~%" sem1)
                     (insert-tm k2 v2 sem1)
                     (format t "at-sem:se-single:sem1:a:~a~%" sem1)
                     (insert-tm key val sem1)
                     (format t "at-sem:se-single:sem1:b:~a~%" sem1)
                     (setf se-contents (list 'se-multi sem1))
                     (format t "at-sem:se-single:contents:0:~a~%" se-contents)
                     (format t "at-sem:se-single:contents:1:~a~%" (se-contents se-map))
                     ))))))

      ((list 'se-multi tm) (list 'se-multi (at-tm key tf tm)))
      (oops (error "Unexpected se-map contents: ~a" oops))))
  (format t "at-sem:done:final:~a~%" se-map)
  (format t "at-sem:done:final contents:~a~%" (se-contents se-map))
  se-map)

;; ---------------------------------------------------------------------

;; 5.5 Matchable class
;; p10

;; class Eq (Pat e) => Matchable e where
;;   type Pat e
;;   type Subst e
;;   match  :: Pat e -> e -> MatchM e ()

;; type MatchM e v = StateT (Subst e) [] v
(defgeneric matchable (pat e)
  (:documentation "match function from class Matchable e"))


;; ---------------------------------------------------------------------

;; lookupSEM :: TrieMap tm => TrieKey tm -> SEMap tm v -> Maybe v
;; lookupSEM !_  EmptySEM = Nothing
;; lookupSEM tk (SingleSEM pk v) | tk == pk  = Just v
;;                               | otherwise = Nothing
;; lookupSEM tk (MultiSEM tm) = lookupTM tk tm


;; lookupPatMSEM :: MTrieMap tm => MTrieKey tm -> MSEMap tm a
;;                              -> MatchM (MTrieKey tm) a
;; lookupPatMSEM k m = case m of
;;   EmptyMSEM        -> mzero
;;   MultiMSEM m      -> lookupPatMTM k m
;;   SingleMSEM pat v -> match pat k >> pure v


;; key is a PatExpr, so class pat-expr
(defun lk-sem (key se-map)
  (format t "lk-sem:se-map:~a~%" se-map)
  (format t "lk-sem:key:~a~%" key)
  (format t "lk-sem:contents:~a~%" (se-contents se-map))
  (with-accessors ((se-contents se-contents))
      se-map
    (match (se-contents se-map)
      ('se-empty
       (format t "lk-sem:se-empty~%")
       nil)

      ((list 'se-single k2 v2)
       (format t "lk-sem:se-single:v2:~a~%" v2)
       (format t "lk-sem:se-single:k2:~a~%" k2)
       (format t "lk-sem:se-single:key:~a~%" k2)
       (format t "lk-sem:se-single:(equal key k2):~a~%" (equal key k2))
       (if (matchable key k2)
           ;; same keys
           v2
           ;; different keys
           nil))

      ((list 'se-multi tm) (lk-tm key tm))
      (oops (error "Unexpected se-map contents: ~a" oops)))))

;; ---------------------------------------------------------------------

(defun foldr-sem (k z se-map)
  (format t "foldr-sem:se-map:~a~%" se-map)
  (format t "foldr-sem:se-map:contents:~a~%" (se-contents se-map))
  (match (se-contents se-map)
    ('se-empty z)

    ((list 'se-single _ v2)
     (funcall k v2 z))

    ((list 'se-multi tm) (foldr-tm k z tm))
    (oops (error "Unexpected se-map contents in foldr-sem: ~a" oops)))
  )

;; ---------------------------------------------------------------------

(defmethod empty-tm ((se-map se-map))
  (format t "empty-tm:se-map~%")
  (funcall (se-empty-contents se-map)))

(defmethod at-tm (key f (se-map se-map))
  (at-sem key f se-map))

(defmethod lk-tm (key (se-map se-map))
  (lk-sem key se-map))

(defmethod foldr-tm (k z (se-map se-map))
  (foldr-sem k z se-map))

;; ---------------------------------------------------------------------

(defun t8 ()
  (let ((test-em (empty-em)))
    (format t "1------------------------------------------~%")
    (format t "test-em: ~a~%" test-em)
    (my-pretty-print test-em 0)
    ;; Motivating example in the paper
    (insert-tm '(:app-v (:var "f") ((:var "x") (:var "y"))) 'v1 test-em)

    (format t "2------------------------------------------~%")
    (format t "test-em:--------------------~%")
    (format t "test-em: ~a~%" test-em)
    (my-pretty-print test-em 0)
    (format t "3------------------------------------------~%")
    (insert-tm '(:app-v (:var "f") ((:var "x") (:var "z"))) 'vz test-em)
    (format t "test-em:--------------------~%")
    (format t "test-em: ~a~%" test-em)
    (my-pretty-print test-em 0)
    (format t "4------------------------------------------~%")
    (format t "count:~a~%"
            (foldr-tm (lambda (v r)
                        (format t "t7:v:~a~%" v)
                        (format t "t7:r:~a~%" r)
                        (+ r 1))
                      0 test-em))
    (format t "5------------------------------------------~%")
    (format t "elems:~a~%" (elems-tm test-em))
    ))

;; ---------------------------------------------------------------------

;; 3.8 Generic Programming
;; P6

;; Left as an exercise to the reader. :)

;; ---------------------------------------------------------------------

;; 4 Keys with binders
;; P7

;; type DBNum = Int
;; data DBEnv = DBE { dbe_next :: DBNum, dbe_env :: Map Var DBNum }
;;
;; emptyDBE :: DBEnv
;; emptyDBE = DBE { dbe_next = 1, dbe_env = Map.empty }
;;
;; extendDBE :: Var → DBEnv → DBEnv
;; extendDBE v (DBE { dbe_next = n, dbe_env = dbe })
;;   = DBE { dbe_next = n + 1, dbe_env = Map.insert v n dbe }
;;
;; lookupDBE :: Var → DBEnv → Maybe DBNum
;; lookupDBE v (DBE { dbe_env = dbe }) = Map.lookup v dbe

(defclass db-env ()
  ((%dbe-next :accessor dbe-next :initform 0 :initarg :next)
   (%dbe-env :accessor dbe-env :initform (make-hash-table :test 'equal) :initarg :env))
  (:documentation "DBEnv"))

(defun empty-dbe ()
  (make-instance 'db-env))

;; Via Google search hence Gemini
(defun copy-hash-table (original-table)
  "Creates a shallow copy of a hash table."
  (let ((new-table (make-hash-table :test (hash-table-test original-table)
                                    :size (hash-table-size original-table)
                                    :rehash-size (hash-table-rehash-size original-table)
                                    :rehash-threshold (hash-table-rehash-threshold original-table))))
    (maphash #'(lambda (key value)
                 (setf (gethash key new-table) value))
             original-table)
    new-table))

(defmethod copy-db-env ((db-env db-env))
  (make-instance 'db-env
                 :next (dbe-next db-env)
                 :env (copy-hash-table (dbe-env db-env))))

(defmethod extend-dbe! (var (db-env db-env))
  (with-accessors ((dbe-next dbe-next)
                   (dbe-env dbe-env))
      db-env
    (setf (gethash var dbe-env) dbe-next)
    (setf dbe-next (+ 1 dbe-next)))
  db-env)

(defmethod extend-dbe-maybe! (var (db-env db-env))
  (if (not (lookup-dbe var db-env))
      (extend-dbe! var db-env)))

(defmethod extend-dbe (var (db-env db-env))
  (let ((new-db-env (copy-db-env db-env)))
    (extend-dbe! var new-db-env)
    new-db-env))

(defmethod lookup-dbe (var (db-env db-env))
  (gethash var (dbe-env db-env)))


;; ---------------------------------------------------------------------

(defmethod my-pretty-print ((db-env db-env) &optional (depth 0) (stream t))
  (format stream "~v,tDB-ENV:~a~%" depth db-env)
  (let ((depth1 (+ 2 depth)))
    (format stream "~v,tDB-ENV-dbe-next:~a ~%" depth1 (dbe-next db-env))

    (format stream "~v,tDB-ENV-dbe-env:~%" depth1)
    (if (equal 0 (hash-table-count (dbe-env db-env)))
        (format stream "~v,tEMPTY~%" (+ 2 depth1))
        (maphash (lambda (k v)
                   (format stream "~v,t  (~S . ~S)~%" depth1 k v))
                 (dbe-env db-env)))))

;; ---------------------------------------------------------------------

;; data ModAlpha a = A DBEnv a

(defclass mod-alpha ()
  ((%ma-dbenv :accessor ma-dbe :initform (make-instance 'db-env) :initarg :dbenv)
   (%ma-val :accessor ma-val :initform nil :initarg :val))
  (:documentation "ModAlpha"))

(defmethod my-pretty-print ((mod-alpha mod-alpha) &optional (depth 0) (stream t))
  (format stream "~v,tMOD-ALPHA:~a~%" depth mod-alpha)
  (let ((depth1 (+ 2 depth)))
    (format stream "~v,tMOD-ALPHA-ma-dbe:~a ~%" depth1 (ma-dbe mod-alpha))
    (my-pretty-print (ma-dbe mod-alpha) (+ 2 depth1) stream)
    (format stream "~v,tMOD-ALPHA-ma-val:~a ~%" depth1 (ma-val mod-alpha))
    (my-pretty-print (ma-val mod-alpha) (+ 2 depth1) stream)))

(defmethod ma-new (dbenv val)
  (make-instance 'mod-alpha :dbenv dbenv :val val))

(defmethod ma-val-new (val)
  (make-instance 'mod-alpha :val val))

;; type AlphaExpr = ModAlpha Expr
(defclass alpha-expr (mod-alpha)
  ()
  (:documentation "AlphaExpr"))

;; ---------------------------------------------------------------------

;; P7
;; ExprMap with binders and lambda's
;;
;; data Expr’ = App Expr Expr | Lam Expr | FVar Var | BVar BoundKey

(defclass expra-map (trie-map)
  (
   ;; em_fvar :: Map Var v -- Free vars
   (%ema-fvar :accessor ema-fvar :initform (make-hash-table :test 'equal))

   ;; em_bvar :: Map BoundKey v -- Lambda-bound vars
   (%ema-bvar :accessor ema-bvar :initform (make-hash-table :test 'equal))

   ;; em_app :: ExprMap (ExprMap v)
   (%ema-app :accessor ema-app :initform nil)

   ;; em_lam :: ExprMap v
   (%ema-lam :accessor ema-lam :initform nil))
  (:documentation "ExprMap with binders and lambda"))

(defun empty-ema ()
  (format t "empty-ema called~%")
  (empty-sem #'(lambda () (make-instance 'expra-map))))

;; ---------------------------------------------------------------------

(defmethod my-pretty-print ((expra-map expra-map) &optional (depth 0) (stream t))
  (format stream "~v,tEXPRA-MAP:~a~%" depth expra-map)
  (let ((depth1 (+ 2 depth)))
    (format stream "~v,tEXPRA-MAP-ema-fvar:~%" depth1)
    (maphash (lambda (k v)
               (format stream "~v,t  (~S .~%" depth1 k)
               (my-pretty-print v (+ 4 depth1) stream)
               (format stream "~v,t  )~%" depth1))
             (ema-fvar expra-map))
    (format stream "~v,tEXPRA-MAP-ema-bvar:~%" depth1)
    (maphash (lambda (k v)
               (format stream "~v,t  (~S .~%" depth1 k)
               (my-pretty-print v (+ 4 depth1) stream)
               (format stream "~v,t  )~%" depth1))
             (ema-bvar expra-map))
    (format stream "~v,tEXPRA-MAP-ema-app:~%" depth1)
    (if (not (null (ema-app expra-map)))
        (my-pretty-print (ema-app expra-map) (+ 2 depth1))
        (format stream "~v,t  NIL~%" depth1))
    (format stream "~v,tEXPRA-MAP-ema-lam:~%" depth1)
    (if (not (null (ema-lam expra-map)))
        (my-pretty-print (ema-lam expra-map) (+ 2 depth1))
        (format stream "~v,t  NIL~%" depth1))
    ))

;; ---------------------------------------------------------------------

;; type Var = String
;; data Expr = App Expr Expr | Lam Var Expr | Var Var
;;
;; data ModAlpha a = A DBEnv a
;; type AlphaExpr = ModAlpha Expr

;; lkEM :: AlphaExpr → ExprMap' v → Maybe v
(defmethod lk-ema (alpha-expr (expra-map expra-map))
  "Look up EXPR in EXPRA-MAP."
  (format t "alpha-expr: ~a~%" alpha-expr)
  (format t "expra-map: ~a~%" expra-map)
  (with-accessors ((ema-fvar ema-fvar)
                   (ema-bvar ema-bvar)
                   (ema-app ema-app)
                   (ema-lam ema-lam))
      expra-map
    (format t "ema-fvar: ~a~%" ema-fvar)
    (format t "ema-bvar: ~a~%" ema-bvar)
    (format t "ema-app: ~a~%" ema-app)
    (format t "ema-lam: ~a~%" ema-lam)

    (match (ma-val alpha-expr)
      ((list :var v)
       (let ((bv (lookup-dbe v (ma-dbe alpha-expr))))
         (if (null bv)
             (gethash v ema-fvar)
             (gethash bv ema-bvar))))

      ((list :app e1 e2)
       ;; App e1 e2 → em_app >>> lkTM (A bve e1 ) >=> lkTM (A bve e2 )
       (let ((ae1 (ma-new (ma-dbe alpha-expr) e1))
             (ae2 (ma-new (ma-dbe alpha-expr) e2)))
         (if (not (null ema-app))
             (let ((m1 (lk-tm ae1 ema-app)))
               (format t "m1: ~a~%" m1)
               (cond
                 ((null m1) nil)
                 (t (lk-tm ae2 m1))))
             nil)))

      ((list :lam v e)
       ;; Lam v e → em_lam >>> lkTM (A (extendDBE v bve) e)
       (if (not (null ema-lam))
           (let* ((bve2 (extend-dbe v (ma-dbe alpha-expr)))
                  (ae (ma-new bve2 e)))
             (lk-tm ae ema-lam))
           nil))

      (oops (error "match failed~a ~%" oops)))))


;; ---------------------------------------------------------------------

(defun lift-tf-ema (f)
  "Take a function F which takes an expra-map as an argument and returns
one, turn it into  TF returning an expra-map."
  (lambda (em)
    (declare (type (or null expr-map) em))
    (let ((em2 (if (null em) (empty-ema) em)))
      (funcall f em2)
      em2)))

(defmethod at-ema (alpha-expr tf (expra-map expra-map))
  "Alter EXPRA-MAP at ALPHA-EXPR using update function TF."
  (with-accessors ((ema-fvar ema-fvar)
                   (ema-bvar ema-bvar)
                   (ema-app ema-app)
                   (ema-lam ema-lam))
      expra-map
    (format t "at-ema: entry:alpha-expr:~a~%" alpha-expr)
    (format t "at-ema: entry:alpha-expr:val:~a~%" (ma-val alpha-expr))
    (my-pretty-print expra-map 0)
    (format t "at-ema: entry done~%")
    (match (ma-val alpha-expr)
      ((list :var v)
       (format t "at-ema:var:v: ~a~%" v)
       (format t "at-ema:var:ema-fvar: ~a~%" ema-fvar)
       (format t "at-ema:var:ema-bvar: ~a~%" ema-bvar)
       (let ((bv (lookup-dbe v (ma-dbe alpha-expr))))
         (if (null bv)
             (alter-map tf v ema-fvar)
             (alter-map tf v ema-bvar))))

      ((list :app e1 e2)
       (let ((ae1 (ma-new (ma-dbe alpha-expr) e1))
             (ae2 (ma-new (ma-dbe alpha-expr) e2)))

         (let ((ema-app2 (if (null ema-app) (empty-ema) ema-app)))
           (setf ema-app (at-tm ae1 (lift-tf-ema (lambda (em) (at-tm ae2 tf em))) ema-app2))
           (my-pretty-print ema-app 0)
           )))

      ((list :lam v e)
       (format t "at-ema:lam:v: ~a~%" v)
       (format t "at-ema:lam:e: ~a~%" e)
       (let* ((bve2 (extend-dbe v (ma-dbe alpha-expr)))
              (ae (ma-new bve2 e)))
         (format t "at-ema:lam:bve2: ~a~%" bve2)
         (my-pretty-print bve2)
         (let ((ema-lam2 (if (null ema-lam) (empty-ema) ema-lam)))
           (setf ema-lam (at-tm ae tf ema-lam2))
           (format t "at-ema:lam:ema-lam: ~a~%" ema-lam)
           (my-pretty-print ema-lam 0))))

      (oops (format t "at-ema:match failing:~a~%" oops)
            (error "match failed: ~a ~%" oops)))

    (format t "at-ema: exiting~%")
    (my-pretty-print expra-map 0)
    (format t "at-ema: exiting done~%")
    expra-map))

;; ---------------------------------------------------------------------

(defun foldr-ema (k z expra-map)
  (format t "foldr-ema:expra-map:~a~%" expra-map)
  (if (null expra-map)
      (progn
        (format t "foldr-ema:null expra-map~%")
        z)
      (with-accessors ((ema-fvar ema-fvar)
                       (ema-bvar ema-bvar)
                       (ema-app ema-app)
                       (ema-lam ema-lam))
          expra-map
        (format t "foldr-ema:em-app:~a~%" ema-app)
        (format t "foldr-ema:em-lam:~a~%" ema-lam)
        (format t "foldr-ema:em-fvar:~a~%" ema-fvar)
        (format t "foldr-ema:em-bvar:~a~%" ema-bvar)
        (my-pretty-print ema-lam)
        (labels ((kapp (m1 r)
                   (format t "foldr-ema:kapp:m1:~a~%" m1)
                   (format t "foldr-ema:kapp:r:~a~%" r)
                   (foldr-tm k r m1)))
          (let* ((z1 (if (null ema-app) z (foldr-tm #'kapp z ema-app)))
                 (z2 (if (null ema-lam) z1 (foldr-tm k z1 ema-lam)))
                 (z3 (if (null ema-fvar)
                         z2
                         (progn
                           (format t "foldr-ema:calc z3:z2:~a~%" z2)
                           (format t "foldr-ema:calc z3:ema-fvar:~a~%" ema-fvar)
                           (hash-table-foldr k z2 ema-fvar)))))
            (if (null ema-bvar) z3 (hash-table-foldr k z3 ema-bvar)))))))

;; ---------------------------------------------------------------------

;; trie-map generic methods for expra-map

;; (defmethod empty-tm ((expra-map expr-map))
;;   (empty-ema))

(defmethod lk-tm (key (expra-map expra-map))
  (lk-ema key expra-map))

(defmethod at-tm (key f (expra-map expra-map))
  (at-ema key f expra-map))

(defmethod foldr-tm (k z (expra-map expra-map))
  (foldr-ema k z expra-map))

;; ---------------------------------------------------------------------

(defun t9 ()
  (let ((test-em (empty-ema)))
    (format t "1------------------------------------------~%")
    (format t "test-em: ~a~%" test-em)
    (my-pretty-print test-em 0)

    (format t "2------------------------------------------~%")
    (insert-tm  (ma-val-new '(:lam "x" (:app (:var "fx") (:var "x")))) 'v1 test-em)
    (format t "test-em:--------------------~%")
    (format t "test-em: ~a~%" test-em)
    (my-pretty-print test-em 0)

    (format t "3------------------------------------------~%")
    (insert-tm (ma-val-new '(:lam "y" (:app (:var "fy") (:var "y")))) 'vz test-em)
    (format t "test-em:--------------------~%")
    (format t "test-em: ~a~%" test-em)
    (my-pretty-print test-em 0)

    ;; Note: if (2) and (3) above both use "f" instead of "fx", "fy", it collapses into a single entry.
    ;;       As expected, since then it is just alpha-renaming

    (format t "4------------------------------------------~%")
    (format t "count:~a~%"
            (foldr-tm (lambda (v r)
                        (format t "t7:v:~a~%" v)
                        (format t "t7:r:~a~%" r)
                        (+ r 1))
                      0 test-em))
    (format t "5------------------------------------------~%")
    (format t "elems:~a~%" (elems-tm test-em))
    ))

;; ---------------------------------------------------------------------
;;======================================================================
;; P7
;; 5. Tries that match

;; p8
;; 5.2 Matching Expressions

;; matchE :: PatExpr → AlphaExpr → MatchME ()

;; p8
;; 5.2.1 Patterns

;; data PatExpr = P PatKeys AlphaExpr
;; type PatKeys = Map PatVar PatKey
;; type PatVar = Var
;; type PatKey = DBNum

;; NOTE: Canonicalize DBNums by doing a left-to-right scan of the
;; AlphaExpr, numbering the vars in the order of occurrence.

;; In practical terms, input is the list of vars and the AlphaExpr,
;; calculate DBNums as pre-process

;; p8
;; 5.2.2 The matching monad

;; type MatchME v = StateT SubstE [] v
;; type SubstE = Map PatKey Expr

;; runMatchExpr :: MatchME v → [(SubstE, v)]
;;    runs a MatchME computation, starting with an empty SubstE,
;;    and returning a list of all the successful (SubstE, v) matches

;; liftMaybe :: Maybe v → MatchME v

;; refineMatch :: (SubstE → Maybe SubstE) → MatchME ()
;;    extends the current substitution by applying f to it;
;;    if the result is Nothing the match fails;
;;    otherwise it turns a single match with the new substitution

;; ---------------------------------------------------------------------
;; p8
;; 5.3 Matching tries for AlphaExpr

(defclass mexpr-map (m-trie-map)
  (
   ;; mm_fvar :: Map Var v -- Free vars
   (%mm-fvar :accessor mm-fvar :initform (make-hash-table :test 'equal))

   ;; mm_bvar :: Map BoundKey v -- Bound vars
   (%mm-bvar :accessor mm-bvar :initform (make-hash-table :test 'equal))

   ;; mm_pvar :: Map PatKey v -- Pattern vars
   (%mm-pvar :accessor mm-pvar :initform (make-hash-table :test 'equal))

   ;; mm_app :: MExprMap (MExprMap v)
   (%mm-app :accessor mm-app :initform nil)

   ;; mm_lam :: MExprMap v
   (%mm-lam :accessor mm-lam :initform nil))
  (:documentation "MExprMap for matching"))

(defun empty-mm ()
  (format t "empty-mm called~%")
  (make-instance 'mexpr-map))

;; ---------------------------------------------------------------------

(defmethod my-pretty-print ((mexpr-map mexpr-map) &optional (depth 0) (stream t))
  (format stream "~v,tMEXPR-MAP:~a~%" depth mexpr-map)
  (let ((depth1 (+ 2 depth)))
    (format stream "~v,tMEXPR-MAP-em-fvar:~%" depth1)
    (maphash (lambda (k v)
               (format stream "~v,t  (~S .~%" depth1 k)
               (my-pretty-print v (+ 4 depth1) stream)
               (format stream "~v,t  )~%" depth1))
             (mm-fvar mexpr-map))
    (format stream "~v,tMEXPR-MAP-em-bvar:~%" depth1)
    (maphash (lambda (k v)
               (format stream "~v,t  (~S .~%" depth1 k)
               (my-pretty-print v (+ 4 depth1) stream)
               (format stream "~v,t  )~%" depth1))
             (mm-bvar mexpr-map))
    (format stream "~v,tMEXPR-MAP-em-pvar:~%" depth1)
    (maphash (lambda (k v)
               (format stream "~v,t  (~S .~%" depth1 k)
               (my-pretty-print v (+ 4 depth1) stream)
               (format stream "~v,t  )~%" depth1))
             (mm-pvar mexpr-map))
    (format stream "~v,tMEXPR-MAP-mm-app:~%" depth1)
    (if (not (null (mm-app mexpr-map)))
        (my-pretty-print (mm-app mexpr-map) (+ 2 depth1))
        (format stream "~v,t  NIL~%" depth1))
    (format stream "~v,tMEXPR-MAP-mm-lam:~%" depth1)
    (if (not (null (mm-lam mexpr-map)))
        (my-pretty-print (mm-lam mexpr-map) (+ 2 depth1))
        (format stream "~v,t  NIL~%" depth1))
    ))

;; ---------------------------------------------------------------------
;; Forward declaration from 5.5 (p10)

(defclass m-trie-map ()
  ()
  (:documentation "Base class for MTrieMap implementations."))

(defgeneric lk-mtm (match-key m-trie-map)
  (:documentation "Looks up MATCH-KEY in M-TRIE-MAP. Returns the value or NIL if not found."))

(defgeneric at-mtm (pat-key tf m-trie-map)
  (:documentation "Alter the value at PAT-KEY in M-TRIE-MAP, by applying TF to it."))

;; AZ note: Need to fit Matchable class in somehow. Likely just with a
;; new generic function on m-trie-map

;; ---------------------------------------------------------------------

(defmethod insert-mtm (key v (m-trie-map m-trie-map))
  "Insert V as the value for KEY in TM."
  (at-mtm key (lambda (x)
                (declare (ignore x))
                v)
          m-trie-map))

;; ---------------------------------------------------------------------

;; lookupPatMM :: ∀v. AlphaExpr → MExprMap v → MatchME v
;; lookupPatMM ae@(A bve e) EmptyMEM = mzero
;; lookupPatMM ae@(A bve e) (SingleSEM pat val)
;;   = matchE pat ae >> pure val
;; lookupPatMM ae@(A bve e) (MultiMEM { .. })
;;   = rigid `mplus` flexi
;;   where
;;     rigid = case e of
;;       Var x → case lookupDBE x bve of
;;                 Just bv → mm_bvar ⊲ liftMaybe ◦ Map.lookup bv
;;                 Nothing → mm_fvar ⊲ liftMaybe ◦ Map.lookup x
;;       App e1 e2 → mm_app ⊲ lkMTM (A bve e1 )
;;                         >=> lkMTM (A bve e2 )
;;       Lam x e → mm_lam ⊲ lkMTM (A (extendDBE x bve) e)
;;
;;     flexi = mm_pvar ⊲ IntMap.toList ⊲ map match_one ⊲ msum
;;
;;     match_one :: (PatVar, v) → MatchME v
;;     match_one (pv, v) = matchPatVarE pv ae >> pure v

;; From the accompanying code
;; lookupPatMM :: AlphaExpr -> MExprMap' a -> MatchM AlphaExpr a
;; lookupPatMM ae@(A bve e) (MM { .. })
;;   = rigid `mplus` flexi
;;   where
;;     rigid = case e of
;;       Var x     -> case lookupDBE x bve of
;;         Just bv -> mm_bvar |> liftMaybe . lookupBoundVarOcc bv
;;         Nothing -> mm_fvar |> liftMaybe . lookupFreeVarOcc  x
;;       App e1 e2 -> mm_app  |>  lookupPatMTM (e1 <$ ae)
;;                            >=> lookupPatMTM (e2 <$ ae)
;;       Lam x e   -> mm_lam  |> lookupPatMTM (A (extendDBE x bve) e)

;;     flexi = mm_pvar |> IntMap.toList |> map match_one |> msum
;;     match_one (pv, x) = matchPatVarE pv ae >> pure x

(defun lookup-pat-mm (alpha-expr mexpr-map)
  "Look up ALPHA-EXPR in MEXPR-MAP."
  (format t "lookup-pat-mm:alpha-expr: ~a~%" alpha-expr)
  (format t "lookup-pat-mm:mexpr-map: ~a~%" mexpr-map)
  (with-accessors ((mm-fvar mm-fvar)
                   (mm-bvar mm-bvar)
                   (mm-pvar mm-pvar)
                   (mm-app mm-app)
                   (mm-lam mm-lam))
      mexpr-map
    (format t "mm-fvar: ~a~%" mm-fvar)
    (format t "mm-bvar: ~a~%" mm-bvar)
    (format t "mm-app: ~a~%" mm-app)
    (format t "mm-lam: ~a~%" mm-lam)

    (match (ma-val alpha-expr)
      ((list :var v)
       (let ((bv (lookup-dbe v (ma-dbe alpha-expr))))
         (if (null bv)
             (gethash v mm-fvar)
             (gethash bv mm-bvar))))

      ((list :app e1 e2)
      ;; App e1 e2 -> mm_app  |>  lookupPatMTM (e1 <$ ae)
      ;;                      >=> lookupPatMTM (e2 <$ ae)
       (let ((ae1 (ma-new (ma-dbe alpha-expr) e1))
             (ae2 (ma-new (ma-dbe alpha-expr) e2)))
         (if (not (null mm-app))
             (let ((m1 (lk-tm ae1 mm-app)))
               (format t "m1: ~a~%" m1)
               (cond
                 ((null m1) nil)
                 (t (lk-tm ae2 m1))))
             nil)))

      ((list :lam v e)
       ;; Lam x e -> mm_lam  |> lookupPatMTM (A (extendDBE x bve) e)
       (if (not (null mm-lam))
           (progn
             (format t "lam:mm-lam:~a~%" mm-lam)
             (let* ((bve2 (extend-dbe v (ma-dbe alpha-expr)))
                    (ae (ma-new bve2 e)))
               (lk-tm ae mm-lam)))
           nil))

      (oops (error "match failed~a ~%" oops)))))
;; -------------------------------------

;; matchPatVarE :: PatKey → AlphaExpr → MatchME ()
;; matchPatVarE pv (A bve e) = refineMatch $ 𝜆ms →
;;   case Map.lookup pv ms of
;;     Nothing -- pv is not bound
;;       | noCaptured bve e → Just (Map.insert pv e ms)
;;       | otherwise → Nothing
;;     Just sol -- pv is already bound
;;       | noCaptured bve e
;;       , eqExpr e sol → Just ms
;;       | otherwise → Nothing
;;
;; eqExpr :: Expr → Expr → Bool
;; noCaptured :: DBEnv → Expr → Bool

;; ---------------------------------------------------------------------
;; P9
;; 5.4 External API

;; Conceptual
;; type PatMap :: Type → Type
;; alterPM :: ([Var], Expr) → TF v → PatMap v → PatMap v
;; lookupPM :: Expr → PatMap v → [(PatSubst, v)]
;; type PatSubst = [(Var, Expr)]

;; Actual

;; type PatMap v = MExprMap (PatKeys, v)

(defclass pat-map (mexpr-map)
  ()
  (:documentation "MExprMap (PatKeys, v)"))

(defun empty-patm ()
  (format t "empty-patm called~%")
  (empty-mm))

;; ---------------------------------------------------------------------
;; p9
;;

;; canonPatKeys :: [Var] → Expr → PatKeys
;; where
;;   data ModAlpha a = A DBEnv a
;;   type AlphaExpr = ModAlpha Expr
;;   data PatExpr = P PatKeys AlphaExpr
;;   type PatKeys = Map PatVar PatKey
;;   type PatVar = Var
;;   type PatKey = DBNum

;; ---------------------------------------------------------------------

;; data ModAlpha a = A DBEnv a
;; data PatExpr    = P PatKeys AlphaExpr
;; type PatKeys = Map PatVar PatKey
;; type PatVar = Var
;; type PatKey = DBNum

(defclass pat-expr ()
  ((%pe-keys :accessor pe-keys :initform (make-instance 'db-env) :initarg :keys)
   (%pe-val :accessor pe-val :initform nil :initarg :val))
  (:documentation "ModAlpha"))

(defmethod my-pretty-print ((pat-expr pat-expr) &optional (depth 0) (stream t))
  (format stream "~v,tPAT-EXPR:~a~%" depth pat-expr)
  (let ((depth1 (+ 2 depth)))
    (format stream "~v,tPAT-EXPR-pe-keys:~a ~%" depth1 (pe-keys pat-expr))
    (my-pretty-print (pe-keys pat-expr) (+ 2 depth1) stream)
    (format stream "~v,tPAT-EXPR-pe-val:~a ~%" depth1 (pe-val pat-expr))
    (my-pretty-print (pe-val pat-expr) (+ 2 depth1) stream)))

(defmethod pe-new (keys val)
  (make-instance 'pat-expr :keys keys :val val))

(defmethod pe-val-new (val)
  (make-instance 'pat-expr :val val))

(defun make-pat-expr (pvars e)
  (let* ((pks (canon-pat-keys pvars e))
         (pa (ma-val-new e))
         (pat (pe-new pks pa)))
    pat))

;; ---------------------------------------------------------------------
;; The auxiliary function canonPatKeys takes the client-side pattern
;; (pvars, e), and returns a PatKeys (Section 5.2.1) that maps each
;; pattern variable to its canonical de Bruijn index. canonPatKeys is
;; entirely straightforward: it simply walks the expression, numbering
;; off the pattern variables in left-to-right order.
;; canonPatKeys :: [Var] → Expr → PatKeys
(defun canon-pat-keys (vars expr)
  (let ((dbenv (empty-dbe)))
    (labels ((do-it (expr1)
               ;; (format t "canon-pat-keys:expr1:~a~%" expr1)
               (match expr1
                 ((list :var v)
                  (extend-dbe-maybe! v dbenv))

                 ((list :app e1 e2)
                  (do-it e1)
                  (do-it e2))

                 ((list :lam v e)
                  (extend-dbe! v dbenv)
                  (do-it e))

                 (oops (error "match failed~a ~%" oops)))))
      (do-it expr))
    (let ((r (make-hash-table :test 'equal)))
      (dolist (var vars r)
        (setf (gethash var r) (lookup-dbe var dbenv))))))

(defun t10 ()
  ;; Original pattern   Canonical PatExpr
  ;; ([a, b], f a b a)  P [a ↦ 1, b ↦ 2] (f a b a)
  ;; ([x, g], f (g x))  P [x ↦ 2, g ↦ 1] (f (g x))
  (format t "1------------------------------------------~%")
  (let ((pat-keys
          (canon-pat-keys
           (list "y")
           '(:lam "y" (:app (:var "fy") (:var "y"))))))
    (my-pretty-print pat-keys))
  (format t "2------------------------------------------~%")
  (let ((pat-keys
          ;; ([a, b], f a b a)  P [a ↦ 1, b ↦ 2] (f a b a)
          (canon-pat-keys
           (list "a" "b")
           '(:app
             (:var "f")
             (:app (:var "a")
              (:app (:var "b") (:var "a")))))))
    (my-pretty-print pat-keys))
  (format t "3------------------------------------------~%")
  (let ((pat-keys
          ;; ([x, g], f (g x))  P [x ↦ 2, g ↦ 1] (f (g x))
          (canon-pat-keys
           (list "x" "g")
           '(:app
             (:var "f")
             (:app (:var "g") (:var "x"))))))
    (my-pretty-print pat-keys)))

;; ---------------------------------------------------------------------

;; data Occ
;;   = Free  !FreeVar
;;   | Bound !BoundKey
;;   | Pat   !PatKey
;;   deriving Eq

;; canonOcc :: PatKeys -> BoundVarEnv -> Var -> Occ
;; canonOcc pks be v
;;   | Just bv <- lookupDBE v be     = Bound bv
;;   | Just pv <- lookupPatKey v pks = Pat pv
;;   | otherwise                     = Free v
;; {-# INLINE canonOcc #-}

(defun canon-occ (pat-keys bound-var-env var)
  (let ((bv (lookup-dbe var bound-var-env)))
    (if bv
        (list :bound bv)
        (let ((pv (lookup-dbe var pat-keys)))
          (if pv
              (list :pat pv)
              (list :free var))))))

;; ---------------------------------------------------------------------

;; matchPatVarE :: PatKey -> AlphaExpr -> MatchM AlphaExpr ()
;; matchPatVarE pv (A bve e) = refineMatch $ \ms ->
;;   case hasMatch pv ms of
;;     Nothing
;;       | noCaptured bve e    -> Just (addMatch pv e ms)
;;       | otherwise           -> Nothing
;;     Just sol
;;       | eqClosedExpr e sol
;;       , noCaptured bve e    -> Just ms
;;       | otherwise           -> Nothing

(defun match-pat-var-e (pat-key alpha-expr)
  (error "match-pat-var-e"))

;; matchE :: PatExpr -> AlphaExpr -> MatchM AlphaExpr ()
;; matchE pat@(P pks (A bve_pat e_pat)) tar@(A bve_tar e_tar) =
;;   -- traceWith (\res -> show ms ++ "  ->  matchE " ++ show pat ++ "   " ++ show tar ++ "  -> " ++ show res) $
;;   case (e_pat, e_tar) of
;;   (Var v, _) -> case canonOcc pks bve_pat v of
;;     Pat pv -> matchPatVarE pv tar
;;     occ | Var v2 <- e_tar
;;         , occ == canonOcc emptyPatKeys bve_tar v2
;;         -> return ()
;;         | otherwise -> mzero
;;   (App f1 a1, App f2 a2) -> match (f1 <$$ pat) (f2 <$ tar) >>
;;                             match (a1 <$$ pat) (a2 <$ tar)
;;   (Lam b1 e1, Lam b2 e2) -> match (P pks (A (extendDBE b1 bve_pat) e1))
;;                                   (A (extendDBE b2 bve_tar) e2)
;;   (_, _) -> mzero

;; (defmethod matchable ((pat pat-expr) (tar mod-alpha))
(defmethod matchable ((pat pat-expr) (tar mod-alpha))
  (format t "matchable:pat:~a~%" pat)
  (my-pretty-print pat)
  (format t "matchable:tar:~a~%" tar)
  (my-pretty-print tar)
  (format t "matchable:match:~a~%" (list (ma-val pat) (ma-val tar)))
  (let ((pks (pe-keys pat))
        (bve_pat (ma-dbe (pe-val pat))))
    (match (list (ma-val pat) (ma-val tar))
      ((list (list :var v) _)
       (format t "matchable:var:~a~%" v)
       (format t "matchable:canon-occ:~a~%" (canon-occ pks bve_pat v))
       (match (canon-occ pks bve_pat v)
         (oops
          (error "matchable:canon-occ gave:~a~%" oops))
         )
       ;; (error "matchable var")
       nil)

         ((list (list :app f1 a1) (list :app f2 a2))
          (format t "matchable:app~%")
          ;; Match f1 with f2
          (let ((mf1 (ma-new (ma-dbe pat) f1))
                (mf2 (ma-new (ma-dbe tar) f2)))
            (matchable mf1 mf2))
          ;; Match a1 with a2
          (let ((ma1 (ma-new (ma-dbe pat) f1))
                (ma2 (ma-new (ma-dbe tar) f2)))
            (matchable ma1 ma2))
          nil)

         ((list (list :lam b1 e1) (list :lam b2 e2))
          (format t "matchable:lam~%")
          (error "matchable lam")
          nil)

         (no
          (format t "matchable:no match:~a~%" no)
          nil)
         )))

;; ---------------------------------------------------------------------


(defmethod at-mm (pat-key tf (mexpr-map mexpr-map))
  "Alter MEXPR-MAP at PAT-KEY using update function TF."
  (with-accessors ((mm-fvar mm-fvar)
                   (mm-bvar mm-bvar)
                   (mm-pvar mm-pvar)
                   (mm-app mm-app)
                   (mm-lam mm-lam))
      mexpr-map
    (format t "at-mm: entry:pat-key:~a~%" pat-key)
    (format t "at-mm: entry:pat-key:val:~a~%" (ma-val (pe-val pat-key)))
    (my-pretty-print mexpr-map 0)
    (format t "at-mm: entry done~%")
    (match (ma-val (pe-val pat-key))
      ((list :var v)
       (format t "at-mm:var:v: ~a~%" v)
       (format t "at-mm:var:mm-fvar: ~a~%" mm-fvar)
       (format t "at-mm:var:mm-bvar: ~a~%" mm-bvar)
       (let ((bv (lookup-dbe v (ma-dbe pat-key))))
         (if (null bv)
             (alter-map tf v mm-fvar)
             (alter-map tf v mm-bvar))))

      ((list :app e1 e2)
       (let ((ae1 (ma-new (ma-dbe (pe-val pat-key)) e1))
             (ae2 (ma-new (ma-dbe (pe-val pat-key)) e2)))

         (let ((mm-app2 (if (null mm-app) (empty-ema) mm-app)))
           (setf mm-app (at-tm ae1 (lift-tf-ema (lambda (em) (at-tm ae2 tf em))) mm-app2))
           (my-pretty-print mm-app 0)
           )))

      ((list :lam v e)
       (format t "at-mm:lam:v: ~a~%" v)
       (format t "at-mm:lam:e: ~a~%" e)
       (let* ((bve2 (extend-dbe v (ma-dbe (pe-val pat-key))))
              (ae (ma-new bve2 e)))
         (format t "at-mm:lam:bve2: ~a~%" bve2)
         (my-pretty-print bve2)
         (let ((mm-lam2 (if (null mm-lam) (empty-ema) mm-lam)))
           (setf mm-lam (at-tm ae tf mm-lam2))
           (format t "at-mm:lam:mm-lam: ~a~%" mm-lam)
           (my-pretty-print mm-lam 0))))

      (oops (format t "at-mm:match failing:~a~%" oops)
            (error "match failed: ~a ~%" oops)))

    (format t "at-mm: exiting~%")
    (my-pretty-print mexpr-map 0)
    (format t "at-mm: exiting done~%")
    mexpr-map))

;; ---------------------------------------------------------------------

;; Then we can simply call the internal atMTM function,
;; passing it a canonical pat :: PatExpr and a transformer ptf ::
;; TF (PatKeys, v) that will pair the PatKeys with the value
;; supplied by the user via tf :: TF v
;; Hence
;;   atMTM :: PatExpr -> TF (PatKeys, v) -> ?
;; (defun at-mtm (pt-expr tf pat-map)
;;   (error "at-mtm called"))

;; ---------------------------------------------------------------------
;; alterPM :: ∀v. ([Var], Expr) → TF v → PatMap v → PatMap v
;; alterPM (pvars, e) tf pm = atMTM pat ptf pm
;;   where
;;     pks :: PatKeys = canonPatKeys pvars e
;;     pat :: PatExpr = P pks (A emptyDBE e)
;;
;;     ptf :: TF (PatKeys, v)
;;     ptf Nothing       = fmap (𝜆v → (pks, v)) (tf Nothing)
;;     ptf (Just (_, v)) = fmap (𝜆v → (pks, v)) (tf (Just v))

(defun alter-pm (pvars-e tf pm)
  (format t "alter-pm:pm:~a~%" pm)
  (let* ((pvars (first pvars-e))
         (e (second pvars-e))
         (pks (canon-pat-keys pvars e))
         (pa (ma-val-new e))
         (pat (pe-new pks pa)))
    (format t "alter-pm:pks:~a~%" pks)
    (format t "alter-pm:pa:~a~%" pa)
    (format t "alter-pm:pat:~a~%" pat)
    (labels ((ptf (m)
               ;; ptf :: TF (PatKeys, v)
               ;; ptf Nothing       = fmap (𝜆v → (pks, v)) (tf Nothing)
               ;; ptf (Just (_, v)) = fmap (𝜆v → (pks, v)) (tf (Just v))
               (format t "alter-pm:ptf:m: ~a~%" m)
               (let ((r (funcall tf m)))
                 (format t "alter-pm:ptf:r: ~a~%" r)
                 (if (null r)
                     r
                     (list pks r)))))
      (at-tm pat #'ptf pm))))
      ;; (at-mtm pat #'ptf pm))))

;; ---------------------------------------------------------------------

;; From accompanying code https://github.com/simonpj/triemap-paper
;; insertPM :: ([PatVar], Expr) -> v -> PatMap v -> PatMap v
;; insertPM (pvars, e) x pm = alterPatMTM pat (\_ -> Just (pks, x)) pm
;;   where
;;     pks = canonPatKeys (Set.fromList pvars) e
;;     pat = P pks (deBruijnize e)

;; deBruijnize :: a -> ModAlpha a
;; deBruijnize = A emptyDBE


(defun insert-pm (pvars e v pm)
  (format t "insert-pm:pm:~a~%" pm)
  (let* ((pks (canon-pat-keys pvars e))
         (pa (ma-val-new e))
         (pat (pe-new pks pa)))
    (format t "insert-pm:pks:~a~%" pks)
    (format t "insert-pm:pa:~a~%" pa)
    (format t "insert-pm:pat:~a~%" pat)
    (labels ((ptf (m)
               (format t "insert-pm:ptf:m: ~a~%" m)
               (list pks v)))
      (at-tm pat #'ptf pm))))
      ;; (at-mtm pat #'ptf pm))))

;; (defun insert-pm (pvars e v pm)
;;   (alter-pm (list pvars e)
;;             (lambda (x)
;;               (declare (ignore x))
;;               v)
;;             pm))

;; ---------------------------------------------------------------------

;; type SubstE = Map PatKey Expr
;; runMatchExpr :: MatchME v → [(SubstE, v)]

;; runMatchExpr runs a MatchME computation, starting with an empty
;; SubstE, and returning a list of all the successful (SubstE, v)
;; matches.
(defun run-match-expr (me)
  ;; MatchME v is a function taking a substitution (of type SubstE) for
  ;; pattern variables, and yielding a possibly-empty list of values (of
  ;; type v), each paired with an extended SubstE
  (let ((subst-e (make-hash-table :test 'equal)))
    ;; (funcall me subst-e)))
    (funcall me)))

;; ---------------------------------------------------------------------

;; lookupPM :: Expr → PatMap v → [(PatSubst, v)]
;; lookupPM e pm
;;   = [ (Map.toList (subst ‘Map.compose‘ pks), x)
;;     | (subst, (pks, x)) ← runMatchExpr $
;;                           lkMTM (A emptyDBE e) pm]
(defun lookup-pm (expr pm)
  (format t "lookup-pm:expr: ~a~%" expr)
  (format t "lookup-pm:pm: ~a~%" pm)
  (run-match-expr (lambda () (lk-mtm (ma-val-new expr) pm))))
  ;; (run-match-expr (lambda () (lk-tm (ma-val-new expr) pm))))

;; ---------------------------------------------------------------------

;; Companion code
;; matchPM :: Expr -> PatMap v -> [(PatSubst, v)]
;; matchPM e pm
;;   = [ (Map.toList (subst `composeMaps` pks), x)
;;     | (subst, (pks, x)) <- runMatchExpr $ lookupPatMTM (deBruijnize e) pm ]
(defun match-pm (e pm)
  (format t "match-pm:e: ~a~%" e)
  (format t "match-pm:pm: ~a~%" pm)
  (run-match-expr (lambda () (lk-tm (ma-val-new e) pm))))

;; ---------------------------------------------------------------------

;; trie-map generic methods for pat-map

;; (defmethod empty-tm ((expra-map expr-map))
;;   (empty-ema))

;; (defmethod lk-tm (key (expra-map expra-map))
;;   (lk-ema key expra-map))

(defmethod at-tm (key f (expra-map expra-map))
  (at-ema key f expra-map))

;; (defmethod foldr-tm (k z (expra-map expra-map))
;;   (foldr-ema k z expra-map))

;; ---------------------------------------------------------------------
;; m-trie-map instances for mexpr-map

(defmethod at-mtm (pat-key tf (mexpr-map mexpr-map))
  (format t "at-mtm:mexpr-map:pat-key:~a~%" pat-key)
  (my-pretty-print pat-key)
  (error "at-mtm mexpr-map")
  )

;; ---------------------------------------------------------------------
;; m-trie-map instances for pat-map


;; (defgeneric at-mtm (pat-key tf m-trie-map)
;;   (:documentation "Alter the value at PAT-KEY in M-TRIE-MAP, by applying TF to it."))
(defmethod at-mtm (pat-key tf (pat-map pat-map))
  (format t "at-mtm:pat-map:pat-key:~a~%" pat-key)
  (error "at-mtm m-trie-map")
  )

;; (defgeneric lk-mtm (match-key m-trie-map)
;;   (:documentation "Looks up MATCH-KEY in M-TRIE-MAP. Returns the value or NIL if not found."))
;; (defmethod lk-mtm (match-key (mexpr-map mexpr-map))
;;   (lookup-pat-mm match-key mexpr-map))

;; ---------------------------------------------------------------------


(defun empty-mtm ()
  (empty-sem #'(lambda () (make-instance 'm-trie-map))))

;; (defmethod empty-mtm ((se-map se-map))
;;   (format t "empty-mtm:se-map~%")
;;   (funcall (se-empty-contents se-map)))

;; ---------------------------------------------------------------------

(defmethod at-tm (pat tf (mexpr-map mexpr-map))
  (format t "at-tm:mexpr-map:map ~a~%" mexpr-map)
  (my-pretty-print mexpr-map)
  (at-mm pat tf mexpr-map))


(defmethod lk-tm (key (mexpr-map mexpr-map))
  (format t "lk-tm:mexpr-map:map ~a~%" mexpr-map)
  (my-pretty-print mexpr-map)
  ;; (lookup-pm key mexpr-map)
  (lookup-pat-mm key mexpr-map)
  )

;; ---------------------------------------------------------------------

;; Orientation.
;;
;; We have one or more patterns, each originating as a list of
;; variables and an expression. We store a value in the trie-map based
;; on this, using the alter methods, specialised as at-mtm. Do we need
;; the specialised version?
;;
;; Our lookup compares an actual expression against the pattern,
;; applying substitutions on the way to make it work.


(defun t11 ()
  (let ((test-pat (empty-patm)))

    (format t "1------------------------------------------~%")
    (format t "test-pat: ~a~%" test-pat)
    (my-pretty-print test-pat 0)

    (format t "2------------------------------------------~%")
    ;; ["fx"], \x.fx x
    (insert-pm  (list "fx") '(:lam "x" (:app (:var "fx") (:var "x"))) 'v1 test-pat)
    (format t "test-pat:--------------------~%")
    (format t "test-pat: ~a~%" test-pat)
    (my-pretty-print test-pat 0)

    (format t "3------------------------------------------~%")
    ;; look up an expression, lets do the original directly
    ;; \x.fx x

    (format t "lookup:~a~%"
            (match-pm '(:lam "x" (:app (:var "fx") (:var "x"))) test-pat))

    ;; let m = mkPatSet [(["a", "b", "c"], read "F (a b) c"), (["ab"], read "F ab C")]
    ;;     matches = matchPM (read "F (A B) C") m

    ))
