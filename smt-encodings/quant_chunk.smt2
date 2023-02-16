(set-logic ALL)

(set-option :produce-models true)
(set-option :produce-unsat-cores true)
(set-option :timeout 4000)

; A manual encoding of max() from array-max.rav

(declare-sort Loc 0)
(declare-sort Field 1)

; Fields to be separated by type

;(declare-datatype OwnHeapIndex (par (T) ((OwnIndex (Loc Loc) (Field (Field T))))))

(declare-datatype FracHeapChunk (par (T) ((FracHeapNull) (FracChunk (Val T) (Own Real)))))
; separate heaps for each RA, field

(declare-datatype HeapChunk (par (T) ((HeapNull) (Chunk (Val T)))))

(define-sort FracOwnHeap (T) (Array Loc (FracHeapChunk T)))
(define-sort OwnHeap (T) (Array Loc (HeapChunk T)))

(declare-datatype QuantHeapChunk ((QuantChunkConstr (Arg1 (Array Loc Bool)) (Arg2 (Array Loc (FracHeapChunk Int))))))

(declare-const guard1 (Array Loc Bool))
(declare-fun inverseFun (Loc) Int)

; inverse axioms

(assert (forall ((l Loc)) (= (select guard1 l) (and (< 0 (inverseFun l)) (< (inverseFun l) 10))) ))

(declare-const chunkArr1 (Array Loc (FracHeapChunk Int)))

(assert (forall ((l Loc)) (= (select chunkArr1 l) (FracChunk 1 1))))

(declare-const quantChunk1 (QuantHeapChunk))
(assert (= quantChunk1 (QuantChunkConstr guard1 chunkArr1)))


(declare-const quantHeap (Array Int QuantHeapChunk))
(assert (= quantHeap (store quantHeap 1 quantChunk1)))

(declare-const guard2 (Array Loc Bool))

(assert (forall ((l Loc)) (= (select guard2 l) (and (< 0 (inverseFun l)) (< (inverseFun l) 5))) ))

(declare-const chunkArr2 (Array Loc (FracHeapChunk Int)))

(assert (forall ((l Loc)) (= (select chunkArr1 l) (FracChunk 1 1))))

; (declare-const quantHeap2 (Array Int QuantHeapChunk))
(declare-const quantChunk2 (QuantHeapChunk))
(assert (= quantChunk1 (QuantChunkConstr guard2 chunkArr2)))

(push)
    (assert (not 
        (forall ((l Loc)) (=> (select guard2 l) (select guard1 l)))
    ))

    (check-sat)
(pop)

(push)
    (assert (not
        (forall ((l Loc)) (=> (select guard2 l) (<= (Own (select chunkArr2 l)) (Own (select chunkArr1 l)) )))
    ))

    (check-sat)
(pop)

;(assert (= quantHeap2 (store quantHeap2 1 (QuantChunkConstr guard2 chunkArr2))))






