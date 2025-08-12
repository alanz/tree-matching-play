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

;; type Var = String
;; data Expr = App Expr Expr | Lam Var Expr | Var Var


;; ---------------------------------------------------------------------
;; Forward declaration from 3.6

(defclass trie-map ()
  ()
  (:documentation "Base class for TrieMap implementations."))

;; ---------------------------------------------------------------------
;; 3.1 interface

(defclass expr-map (trie-map)
  ((%em-var :accessor em-var :initform (make-hash-table :test 'equal))
   ;; For the :app constructor, an expr-map for e1 containing an expr-map for e2
   (%em-app :accessor em-app :initform nil)
   (%em-app-v :accessor em-app-v :initform nil))
  (:documentation "ExprMap v"))

(defun empty-em ()
  (make-instance 'expr-map))


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
        (t (format t "match failed ~%")))))

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
          (setf em-app-v (at-em e1 (lift-tf-lm lm-proto (lambda (em) (at-lm e2 tf em))) em-app-v2))
          (format t "at-em:app-v:em-app-v: ~a~%" em-app-v)
          (my-pretty-print em-app-v 0)
          ))
      ;; ------------------------------
      (t (format t "match failed ~%")))
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
          (let ((z1 (foldr-em #'kcons z lm-cons)))
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
        (labels ((kapp (m1 r)
                   (format t "foldr-em:kapp:m1:~a~%" m1)
                   (format t "foldr-em:kapp:r:~a~%" r)
                   (foldr-tm k r m1))
                 (kappv (m1 r)
                   (format t "foldr-em:kappv:m1:~a~%" m1)
                   (format t "foldr-em:kappv:r:~a~%" r)
                   (foldr-tm k r m1)))
          (let* ((z1 (foldr-em #'kapp z em-app))
                 (z2 (foldr-em #'kappv z1 em-app-v)))
            (format t "foldr-em:z1:~a~%" z1)
            (format t "foldr-em:z2:~a~%" z2)
            (hash-table-foldr k z2 em-var))))))

(defun size-em (expr-map)
  (foldr-em (lambda (v r)
              (declare (ignore v))
              (+ r 1))
            0 expr-map))

(defun elems-em (expr-map)
  (foldr-em (lambda (v r) (cons v r))
            nil expr-map))

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

  (format t "elems:~a~%" (elems-em test-em)))

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

    (format t "elems:~a~%" (elems-em test-tm))))

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
                   ;; (funcall (lm-empty-contents list-map))
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
                           ;; (empty-lm list-map)
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
                        ;; (declare (ignore b))
                        (format t "t7:v:~a~%" v)
                        (format t "t7:r:~a~%" r)
                        (+ r 1))
                      0 test-em))
    (format t "5------------------------------------------~%")
    (format t "elems:~a~%" (elems-em test-em))
    ))

;; ---------------------------------------------------------------------
;; 3.7 Singleton maps, and empty maps revisited
;; P6
;;
;; data SEMap tm v = EmptySEM
;;                 | SingleSEM (Key tm) v
;;                 | MultiSEM (tm v)


(defclass se-map (trie-map)
  ((%se-contents :accessor se-contents :initform nil)
   ;; (%lm-nil :accessor lm-nil :initform nil)
   ;; (%empty-contents :accessor lm-empty-contents :initarg :lm-empty-contents)
   )
  (:documentation "SEMap tm v"))

(defmethod my-pretty-print ((se-map se-map) &optional (depth 0) (stream t))
  (format stream "~v,tSE-MAP:~a~%" depth se-map)
  (let ((depth1 (+ 2 depth)))
    (format stream "~v,tSE-MAP-se-contents:~%" depth1)
    (format stream "~v,t~a ~%" (+ 1 depth1) (se-contents e-map))
    ))

(defun empty-sm ()
  (make-instance 'se-map))
