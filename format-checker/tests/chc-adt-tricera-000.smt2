(set-logic HORN)

(declare-datatypes ((HeapObject 0) (node 0)) (((O_Int  (getInt Int)) (O_UInt  (getUInt Int)) (O_Addr  (getAddr Int)) (O_node  (getnode node)) (defObj ))
                                              ((node  (h Int) (n Int)))))
(declare-datatypes ((Heap 0)) (((HeapCtor  (HeapSize Int) (HeapContents (Array Int HeapObject))))))

(declare-fun |inv_main2| ( Heap ) Bool)
(declare-fun |inv_main33| ( Heap Int Int Int ) Bool)
(declare-fun |inv_main27| ( Heap Int Int Int ) Bool)
(declare-fun |inv_main14| ( Heap Int Int Int ) Bool)
(declare-fun |inv_main19| ( Heap Int Int Int ) Bool)
(declare-fun |inv_main25| ( Heap Int Int Int ) Bool)
(declare-fun |inv_main13| ( Heap Int Int Int ) Bool)
(declare-fun |inv_main32| ( Heap Int Int Int ) Bool)
(declare-fun |inv_main11| ( Heap Int Int Int ) Bool)
(declare-fun |inv_main31| ( Heap Int Int Int ) Bool)

(assert
  (forall ( (v_0 Heap) )
    (=>
      (and
        (and true (= v_0 (HeapCtor 0 ((as const (Array Int HeapObject)) defObj))))
      )
      (inv_main2 v_0)
    )
  )
)
(assert
  (forall ( (A Int) (B node) (C Heap) (D Int) (E Heap) (v_5 Int) ) 
    (=>
      (and
        (inv_main2 E)
        (let ((a!1 (HeapCtor (+ 1 (HeapSize E))
                     (store (HeapContents E) (+ 1 (HeapSize E)) (O_node B)))))
  (and (not (= D 0)) (= D (+ 1 (HeapSize E))) (= C a!1) (= v_5 D)))
      )
      (inv_main11 C D A v_5)
    )
  )
)
(assert
  (forall ( (A Heap) (B Int) (C Int) (D Int) (E Heap) ) 
    (=>
      (and
        (inv_main13 E D C B)
        (let ((a!1 (ite (and (not (<= B 0)) (>= (HeapSize E) B))
                (select (HeapContents E) B)
                defObj)))
(let ((a!2 (O_node (node 2 (n (getnode a!1))))))
(let ((a!3 (ite (and (not (<= B 0)) (>= (HeapSize E) B))
                (HeapCtor (HeapSize E) (store (HeapContents E) B a!2))
                E)))
  (and (is-O_node a!1) (= A a!3)))))
      )
      (inv_main27 A D C B)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G node) (H Heap) (I Heap) (J Int) (K Int) (L Int) (M Int) (N Heap) ) 
    (=>
      (and
        (inv_main14 N M L K)
        (let ((a!1 (ite (and (not (<= K 0)) (>= (HeapSize N) K))
                (select (HeapContents N) K)
                defObj))
      (a!4 (HeapCtor (+ 1 (HeapSize H))
                     (store (HeapContents H) (+ 1 (HeapSize H)) (O_node G)))))
(let ((a!2 (O_node (node 1 (n (getnode a!1))))))
(let ((a!3 (ite (and (not (<= K 0)) (>= (HeapSize N) K))
                (HeapCtor (HeapSize N) (store (HeapContents N) K a!2))
                N)))
  (and (= H a!3)
       (= F E)
       (= E M)
       (= D C)
       (= C L)
       (= B A)
       (= A K)
       (not (= J 0))
       (= J (+ 1 (HeapSize H)))
       (is-O_node a!1)
       (= I a!4)))))
      )
      (inv_main19 I F J B)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Heap) (E Int) (F Int) (G Int) (H Int) (I Heap) ) 
    (=>
      (and
        (inv_main31 I H G F)
        (let ((a!1 (ite (and (not (<= F 0)) (>= (HeapSize I) F))
                (select (HeapContents I) F)
                defObj)))
  (and (= C H)
       (= B G)
       (= A F)
       (not (= E 2))
       (= E (h (getnode a!1)))
       (is-O_node a!1)
       (= D I)))
      )
      (inv_main33 D C B A)
    )
  )
)
(assert
  (forall ( (A Heap) (B Int) (C Int) (D Int) (E Heap) ) 
    (=>
      (and
        (inv_main19 E D C B)
        (let ((a!1 (ite (and (not (<= B 0)) (>= (HeapSize E) B))
                (select (HeapContents E) B)
                defObj)))
(let ((a!2 (O_node (node (h (getnode a!1)) C))))
(let ((a!3 (ite (and (not (<= B 0)) (>= (HeapSize E) B))
                (HeapCtor (HeapSize E) (store (HeapContents E) B a!2))
                E)))
  (and (is-O_node a!1) (= A a!3)))))
      )
      (inv_main25 A D C B)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Heap) (E Int) (F Int) (G Int) (H Int) (I Heap) ) 
    (=>
      (and
        (inv_main11 I H G F)
        (let ((a!1 (ite (and (not (<= H 0)) (>= (HeapSize I) H))
                (select (HeapContents I) H)
                defObj)))
(let ((a!2 (O_node (node 2 (n (getnode a!1))))))
(let ((a!3 (ite (and (not (<= H 0)) (>= (HeapSize I) H))
                (HeapCtor (HeapSize I) (store (HeapContents I) H a!2))
                I)))
  (and (= C H) (= B G) (= A F) (= E 0) (is-O_node a!1) (= D a!3)))))
      )
      (inv_main13 D C B A)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Heap) (F Int) (G Int) (H Int) (I Int) (J Heap) ) 
    (=>
      (and
        (inv_main25 J I H G)
        (let ((a!1 (ite (and (not (<= G 0)) (>= (HeapSize J) G))
                (select (HeapContents J) G)
                defObj)))
  (and (= D I)
       (= C H)
       (= B G)
       (= A (n (getnode a!1)))
       (= F 0)
       (is-O_node a!1)
       (= E J)))
      )
      (inv_main13 E D C A)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Heap) (E Int) (F Int) (G Int) (H Int) (I Heap) ) 
    (=>
      (and
        (inv_main11 I H G F)
        (let ((a!1 (ite (and (not (<= H 0)) (>= (HeapSize I) H))
                (select (HeapContents I) H)
                defObj)))
(let ((a!2 (O_node (node 2 (n (getnode a!1))))))
(let ((a!3 (ite (and (not (<= H 0)) (>= (HeapSize I) H))
                (HeapCtor (HeapSize I) (store (HeapContents I) H a!2))
                I)))
  (and (= C H) (= B G) (= A F) (not (= E 0)) (is-O_node a!1) (= D a!3)))))
      )
      (inv_main14 D C B A)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Heap) (F Int) (G Int) (H Int) (I Int) (J Heap) ) 
    (=>
      (and
        (inv_main25 J I H G)
        (let ((a!1 (ite (and (not (<= G 0)) (>= (HeapSize J) G))
                (select (HeapContents J) G)
                defObj)))
  (and (= D I)
       (= C H)
       (= B G)
       (= A (n (getnode a!1)))
       (not (= F 0))
       (is-O_node a!1)
       (= E J)))
      )
      (inv_main14 E D C A)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Heap) (E Int) (F Int) (G Int) (H Int) (I Heap) ) 
    (=>
      (and
        (inv_main31 I H G F)
        (let ((a!1 (ite (and (not (<= F 0)) (>= (HeapSize I) F))
                (select (HeapContents I) F)
                defObj)))
  (and (= C H)
       (= B G)
       (= A F)
       (= E 2)
       (= E (h (getnode a!1)))
       (is-O_node a!1)
       (= D I)))
      )
      (inv_main32 D C B A)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Heap) (E Int) (F Int) (G Int) (H Int) (I Heap) ) 
    (=>
      (and
        (inv_main32 I H G F)
        (let ((a!1 (ite (and (not (<= F 0)) (>= (HeapSize I) F))
                (select (HeapContents I) F)
                defObj)))
  (and (= C H)
       (= B G)
       (= A F)
       (not (= E 0))
       (= E (n (getnode a!1)))
       (is-O_node a!1)
       (= D I)))
      )
      (inv_main31 D C B E)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Heap) (D Int) (E Int) (F Int) (G Int) (H Heap) (v_8 Int) ) 
    (=>
      (and
        (inv_main27 H G F E)
        (let ((a!1 (ite (and (not (<= E 0)) (>= (HeapSize H) E))
                (select (HeapContents H) E)
                defObj)))
(let ((a!2 (O_node (node (h (getnode a!1)) 0))))
(let ((a!3 (ite (and (not (<= E 0)) (>= (HeapSize H) E))
                (HeapCtor (HeapSize H) (store (HeapContents H) E a!2))
                H)))
  (and (= B F)
       (= A E)
       (not (= D 0))
       (= D G)
       (is-O_node a!1)
       (= C a!3)
       (= v_8 D)))))
      )
      (inv_main31 C D B v_8)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Heap) ) 
    (=>
      (and
        (inv_main11 D C B A)
        (let ((a!1 (ite (and (not (<= C 0)) (>= (HeapSize D) C))
                (select (HeapContents D) C)
                defObj)))
  (not (is-O_node a!1)))
      )
      false
    )
  )
)

(check-sat)
(exit)
