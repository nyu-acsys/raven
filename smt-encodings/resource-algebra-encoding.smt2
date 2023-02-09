(set-logic ALL)

(set-option :produce-models true)
(set-option :produce-unsat-cores true)

; A manual encoding of Auth resource algebra from resource_algebra.rav

(declare-sort Loc 0)
(declare-sort Field 1)
; Fields to be separated by type

(declare-datatype OwnHeapIndex (par (T) ((OwnIndex (Loc Loc) (Field (Field T))))))

(declare-datatype FracHeapChunk (par (T) ((FracHeapNull) (FracChunk (Val T) (Own Real)))))
; separate heaps for each RA, field

(declare-datatype HeapChunk (par (T) ((HeapNull) (Chunk (Val T)))))

(define-sort FracOwnHeap (T) (Array (OwnHeapIndex T) (FracHeapChunk T)))
(define-sort OwnHeap (T) (Array (OwnHeapIndex T) (HeapChunk T)))

(declare-datatype Predicate ((predNull) (lock (lockArg1 Loc) (lockArg2 Bool))))
(declare-const PredHeap0 (Array Int Predicate))

(declare-fun IntHeapValid ((FracOwnHeap Int)) Bool)
(assert (
	forall (
		(heap (FracOwnHeap Int))
		(lf (OwnHeapIndex Int))
		(chunk (FracHeapChunk Int))
	)

	(=> 
		(and
			(IntHeapValid heap)
			(= (select heap lf) chunk) 
		)

		(match chunk (
            (FracHeapNull true)
            ((FracChunk i r) (and (<= 0 r) (>= 1 r)))            
        ))
	)
))

(declare-fun BoolHeapValid ((FracOwnHeap Bool)) Bool)
(assert (
	forall (
		(heap (FracOwnHeap Bool))
		(lf (OwnHeapIndex Bool))
		(chunk (FracHeapChunk Bool))
	)

	(=> 
		(and
			(BoolHeapValid heap)
			(= (select heap lf) chunk) 
		)

		(match chunk (
            (FracHeapNull true)
            ((FracChunk i r) (and (<= 0 r) (>= 1 r)))            
        ))
	)
))

; ---------------------------------

(declare-sort M 0)
(declare-sort MLoc)
(declare-const M.id M)
(declare-fun M.comp (M M) M)
(declare-fun M.valid (M) Bool)

(declare-fun MHeapValid ((OwnHeap M)) Bool)
(assert (
	forall (
		(heap (OwnHeap M))
		(lf (OwnHeapIndex M))
		(chunk (HeapChunk M))
	)

	(=> 
		(and
			(MHeapValid heap)
			(= (select heap lf) chunk) 
		)

		(match chunk (
            (HeapNull true)
            ((Chunk t) (M.valid t))            
        ))
	)
))


; what needs to be encoded for the fact that M is a ResourceAlgebra?

; M.idValid
(assert (M.valid M.id))

; M.compAssoc
(assert (
    forall ((a M) (b M) (c M))
    (= (M.comp (M.comp a b) c) (M.comp a (M.comp b c)))
))

; M.compCommute
(assert (
    forall ((a M) (b M))
    (= (M.comp a b) (M.comp b a))
))

; fpuUpdate: how to encode 

; M.ownSep
;(assert (
;    forall ((l Loc) (f (Field M)) (heap (OwnHeap M)) (a M) (b M))

;))
; How to encode ownSep exactly?

; rep type T = data {...}
(declare-datatype Auth.T ((frac (frac_frac_chunk M)) (auth_frac (auth_auth_chunk M) (auth_frac_chunk M)) (top)))

; val id = frac(M.id)
(declare-const Auth.id Auth.T)
(assert (= Auth.id (frac M.id)))

(echo "Should be SAT:")
(check-sat)
(echo "")

(declare-fun Auth.comp (Auth.T Auth.T) Auth.T)
; what checks need to be made for functions? Totality?
(assert (
    forall ((a Auth.T) (b Auth.T))
    (
        = (Auth.comp a b)
        (ite 
            (exists ((m M) (n M))
                (and (= a (frac m)) (= b (frac n)))
            )
            (frac (M.comp (frac_frac_chunk a) (frac_frac_chunk b)))
            (ite 
                (exists ((m M) (n1 M) (n2 M))
                    (and (= a (frac m)) (= b (auth_frac n1 n2)))
                )
                (auth_frac (auth_auth_chunk b) (M.comp (frac_frac_chunk a) (auth_frac_chunk b)))
                (ite 
                    (exists ((m M) (n1 M) (n2 M))
                        (and (= b (frac m)) (= a (auth_frac n1 n2)))
                    )
                    (auth_frac (auth_auth_chunk a) (M.comp (auth_frac_chunk a) (frac_frac_chunk b)))
                    top
                )
            )
        )
    )
))


(declare-fun Auth.valid (Auth.T) Bool)
(assert (
    forall ((x Auth.T)) 
    (= (Auth.valid x) (not (= x top)))
))

; lemma idValid()
(push)
(assert (not (Auth.valid Auth.id)))
(check-sat)
(pop)

; lemma compAssoc
(push)
(assert (not
    (forall ((a Auth.T) (b Auth.T) (c Auth.T))
    (= (Auth.comp (Auth.comp a b) c) (Auth.comp a (Auth.comp b c)))
    )
))
(check-sat)
(pop)

; lemma compCommute
(push)
(assert (not
    (forall ((a Auth.T) (b Auth.T))
    (= (Auth.comp a b) (Auth.comp b a))
    )
))
(check-sat)
(pop)