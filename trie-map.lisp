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
   (%em-app :accessor em-app :initform nil)
   )
  (:documentation "ExprMap v"))

(defun empty-em ()
  (make-instance 'expr-map)
  )

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
  "Apply F to the value in the MAP at KEY (or to nil if not found).
Store the result in the MAP."
  (format t "alter-map:f: ~a~%" f)
  (format t "alter-map:key: ~a~%" key)
  (format t "alter-map:map: ~a~%" map)
  (setf (gethash key map) (apply f (gethash key map))))

(defun lift-tf (f)
  (lambda (v)
    (if (null v)
        (apply f (empty-em))
        (apply f v))))

;; m { em_app = atEM e1 (liftTF (atEM e2 tf )) app)
(defmethod at-em (expr tf (expr-map expr-map))
  "Alter EXPR-MAP at EXPR using update function TF."
  (with-accessors ((em-var em-var)
                   (em-app em-app))
      expr-map
    (format t "at-em:em-var: ~a~%" em-var)
    (format t "at-em:em-app: ~a~%" em-app)
    (match expr
      ((list :var v) (alter-map tf v em-var))
      ((list :app e1 e2)
       (let ((f2 (lift-tf (lambda (m) (at-em e2 tf m)))))
         (setf em-app (at-em e1 f2 em-app))))
      (t (format t "match failed ~%")))))

(defmethod insert-em (expr v (expr-map expr-map))
  "Insert V as the value for key EXPR in EXPR-MAP."
  (at-em expr (lambda (x)
                (declare (ignore x))
                v)
         expr-map))

(defmethod delete-em (expr (expr-map expr-map))
  "Delete the entry for EXPR in EXPR-MAP."
  (at-em expr (lambda (x)
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
  (insert-em '(:var "x") 'v (empty-em)))
