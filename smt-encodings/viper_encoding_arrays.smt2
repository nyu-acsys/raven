(set-option :auto_config false) ; Usually a good idea
(set-option :smt.mbqi false)

;; The following definitions are an excerpt of Viper's sequence axiomatisation,
;; which is based on Dafny's sequence axiomatisation.
;; See also:
;;   https://github.com/dafny-lang/dafny
;;   http://viper.ethz.ch

(declare-sort Seq<Int>) ;; Monomorphised sort of integer sequences

(declare-const Seq_empty Seq<Int>)
(declare-fun Seq_length (Seq<Int>) Int)
(declare-fun Seq_singleton (Int) Seq<Int>)
(declare-fun Seq_index (Seq<Int> Int) Int)
(declare-fun Seq_append (Seq<Int> Seq<Int>) Seq<Int>)
(declare-fun Seq_equal (Seq<Int> Seq<Int>) Bool)

(assert (forall ((s Seq<Int>)) (!
  (<= 0 (Seq_length s))
  :pattern ((Seq_length s))
  )))

(assert (= (Seq_length (as Seq_empty  Seq<Int>)) 0))

(assert (forall ((s1 Seq<Int>) (s2 Seq<Int>)) (!
  (implies
    (and
      (not (= s1 (as Seq_empty  Seq<Int>)))
      (not (= s2 (as Seq_empty  Seq<Int>))))
    (= (Seq_length (Seq_append s1 s2)) (+ (Seq_length s1) (Seq_length s2))))
  ; :pattern ((Seq_length (Seq_append s1 s2)))
  )))

(assert (forall ((s Seq<Int>)) (!
  (= (Seq_append (as Seq_empty  Seq<Int>) s) s)
  ; :pattern ((Seq_append (as Seq_empty  Seq<Int>) s))
  )))

(assert (forall ((s Seq<Int>)) (!
  (= (Seq_append s (as Seq_empty  Seq<Int>)) s)
  ; :pattern ((Seq_append s (as Seq_empty  Seq<Int>)))
  )))

(assert (forall ((s1 Seq<Int>) (s2 Seq<Int>) (i Int)) (!
  (implies
    (and
      (not (= s1 (as Seq_empty  Seq<Int>)))
      (not (= s2 (as Seq_empty  Seq<Int>))))
    (ite
      (< i (Seq_length s1))
      (= (Seq_index (Seq_append s1 s2) i) (Seq_index s1 i))
      (= (Seq_index (Seq_append s1 s2) i) (Seq_index s2 (- i (Seq_length s1))))))
  ; :pattern ((Seq_index (Seq_append s1 s2) i))
  ; :pattern ((Seq_index s1 i) (Seq_append s1 s2))
  )))

(assert (forall ((s1 Seq<Int>) (s2 Seq<Int>)) (!
  (=
    (Seq_equal s1 s2)
    (and
      (= (Seq_length s1) (Seq_length s2))
      (forall ((i Int)) (!
        (implies
          (and (<= 0 i) (< i (Seq_length s1)))
          (= (Seq_index s1 i) (Seq_index s2 i)))
        ; :pattern ((Seq_index s1 i))
        ; :pattern ((Seq_index s2 i))
        ))))
  ; :pattern ((Seq_equal s1 s2))
  )))

; (assert (forall ((s1 Seq<Int>) (s2 Seq<Int>)) (!
;   (implies (Seq_equal s1 s2) (= s1 s2))
;   ; :pattern ((Seq_equal s1 s2))
;   )))

; ------------------------------------------------------------

; assert Seq(4) ++ Seq[Int]() == Seq(4)
(push)
(assert (not 
  (Seq_equal
    (Seq_append (Seq_singleton 4) Seq_empty)
    (Seq_singleton 4))))
(check-sat) ; unsat -- good!
(pop)

; assert Seq(4, 1) ++ Seq(1, 4) == Seq(4, 1, 1, 4)
(push)
(assert (not 
  (Seq_equal
    (Seq_append
      (Seq_append (Seq_singleton 4) (Seq_singleton 1))
      (Seq_append (Seq_singleton 1) (Seq_singleton 4)))
    (Seq_append
      (Seq_append
        (Seq_append (Seq_singleton 4) (Seq_singleton 1))
        (Seq_singleton 1))
      (Seq_singleton 4)))))
(check-sat) ; unsat -- good!
(pop)

; assert Seq(4) ++ Seq(1) == Seq(1, 4)
(push)
(assert (not (Seq_equal
  (Seq_append (Seq_singleton 4) (Seq_singleton 1))
  (Seq_append (Seq_singleton 1) (Seq_singleton 4)))))
(check-sat) ; unknown -- OK, since property doesn't hold
(pop)