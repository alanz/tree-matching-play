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
;; 3.1 interface

(defclass expr-map ()
  ((%em-var :accessor em-var :initform (make-hash-table :test 'equal))
   ;; For the :app constructor, an expr-map for e1 containing an expr-map for e2
   (%em-app :accessor em-app :initform nil)
   )
  (:documentation "ExprMap v"))

(defgeneric my-pretty-print (thing &optional (depth) (stream))
  (:documentation "Pretty print."))

(defmethod my-pretty-print ((obj t) &optional (depth 0) (stream t))
  "Default pretty print."
  (format stream "~v,t~a~%" depth obj))

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
        (format stream "~v,t  NIL~%" depth1)))
  )


(defun empty-em ()
  (make-instance 'expr-map))

(defvar test-expr '(:app (:var "a") (:var "b")))
(defvar test-em (empty-em))

(defmethod lk-em (expr (expr-map expr-map))
  "Look up EXPR in EXPR-MAP."
  (format t "expr: ~a~%" expr)
  (format t "expr-map: ~a~%" expr-map)
  (with-accessors ((em-var em-var)
                   (em-app em-app))
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
        (t (format t "match failed ~%")))))

(defun alter-map (f key map)
  "Apply F to the value in the hash-map MAP at KEY (or to nil if not found).
Store the result in the MAP."
  ;; (format t "alter-map:f: ~a~%" f)
  ;; (format t "alter-map:key: ~a~%" key)
  ;; (format t "alter-map:map: ~a~%" map)
  ;; (format t "alter-map:old-val1: ~a~%" (gethash key map))
  (setf (gethash key map) (funcall f (gethash key map))))


(defun lift-tf (f)
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

;; m { em_app = atEM e1 (liftTF (atEM e2 tf )) app)
(defmethod at-em (expr tf (expr-map expr-map))
  "Alter EXPR-MAP at EXPR using update function TF."
  (with-accessors ((em-var em-var)
                   (em-app em-app))
      expr-map
    (format t "at-em:expr: ~a~%" expr)
    (format t "at-em:em-var: ~a~%" em-var)
    (format t "at-em:em-app: ~a~%" em-app)
    (my-pretty-print expr-map 0)
    (match expr
      ((list :var v)

       (format t "at-em:processing :var:1: ~a~%" v)
       (alter-map tf v em-var)
       (format t "at-em:processing :var:2: ~a~%" em-var)
       )
      ((list :app e1 e2)
       ;; App e1 e2 → m { em_app = atEM e1 (liftTF (atEM e2 tf )) app }
       (format t "at-em:processing :app: ~a ~a~%" e1 e2)
       ;; ------------------------------
       ;; We want the current expr-map to have a new or updated one, indexed by e1.
       ;; This one must have an entry for e2, which is updated by TF.
       ;; (let* ((em2 (if (null em-app) (empty-em) em-app))
       ;;        (em2-val (at-em e2 tf em2)))
       ;;   (format t "at-em:em-app: ~a~%" em-app)
       ;;   (format t "at-em:em2: ~a~%" em2)
       ;;   (my-pretty-print em2 0)
       ;;   (format t "at-em:em2-val: ~a~%" em2-val)
       ;;   (format t "at-em:app:recursing-----------------------------~%")
       ;;   (setf em-app (at-em e1 tf em2))
       ;;   (format t "at-em:em-app: ~a~%" em-app)
       ;;   ))

       ;; ------------------------------
       ;; (let* ((f2 (lift-tf (lambda (em) (at-em e2 tf em))))
       ;;        ;; (em2 (at-em e1 f2 em-app)))
       ;;        (em2 nil))
       ;;   (format t "at-em:em2: ~a~%" em2)
       ;;   (my-pretty-print em2)
       ;;   (setf em-app (at-em e1 f2 em-app))
       ;;   (my-pretty-print em-app)))
       ;; ------------------------------
       ;; App e1 e2 → m { em_app = atEM e1 (liftTF (atEM e2 tf )) app }
       (let ((em-app2 (if (null em-app) (empty-em) em-app))
              ;; (em2 (funcall (lift-tf (lambda (em) (at-em e2 tf em))) em-app2))
              ;; (em2 nil)
              )
         (format t "at-em:em-app: ~a~%" em-app)
         (format t "at-em:em-app2: ~a~%" em-app2)
         ;; (format t "at-em:em2: ~a~%" em2)
         ;; (my-pretty-print em2 0)
         (setf em-app (at-em e1 (lift-tf (lambda (em) (at-em e2 tf em))) em-app2))
         (format t "at-em:em-app:2: ~a~%" em-app)
         (my-pretty-print em-app 0)
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
