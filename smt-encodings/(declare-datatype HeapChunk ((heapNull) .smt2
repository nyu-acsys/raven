(declare-datatype HeapChunk ((heapNull) (IntChunk (IntVal Int) (IntOwn Real)) (BoolChunk (BoolVal Bool) (BoolOwn Real))))

(assert (= 5 (IntVal (BoolChunk true 0))))
(check-sat)