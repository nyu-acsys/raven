(set-logic ALL)

(set-option :produce-models true)
(set-option :smt.mbqi false)
(set-option :produce-unsat-cores true)
;(set-option :timeout 2000)

(declare-sort Loc 0)
(declare-sort Field 1)

; ---------------------------------

(declare-sort IArray)
(declare-fun loc (IArray Int) Loc)
(declare-fun len (IArray) Int)
(declare-fun first (Loc) IArray)
(declare-fun second (Loc) Int)

; lemma all-diff
(assert (
    forall ((a IArray) (i Int)) 
        (and (= (first (loc a i)) a) (= (second (loc a i)) i))
))

(declare-const val (Field Int))

(declare-datatype Predicate (
    (predNull)
    (is_max (is_maxArg1 Int) (is_maxArg2 (Array Int Int)) (is_maxArg3 Int))
    (arr (arrArg1 IArray) (arrArg2 (Array Int Int)))
))

; ---------------------------------

(declare-const a IArray)
(declare-const m (Array Int Int))
(declare-const x Int)

(declare-const PredHeap0 (Array Int Predicate))

; requires arr(a,m)
(assert (= PredHeap0 (store PredHeap0 0 (arr a m))))

; if (len(a) == 0)
(push)
    (assert (= (len a) 0))
    (declare-const x_1 Int)
    (assert (= x_1 -1))

    (push)
        (assert (not
            (exists ((ii Int)) (and (<= 0 ii) (<= ii 0) (= (is_max x m (len a)) (select PredHeap0 0))))
        ))
        (check-sat)
        ; this request times out. Why might that be?
    (pop)
(pop)