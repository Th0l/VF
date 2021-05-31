(set-logic QF_AUFLIA)

(declare-const m_0 (Array Int (Array Int Int)))
(declare-const m_1 (Array Int (Array Int Int)))


;a[i] é codificada por (select a i)
;a[i] := v  é modelada assim: (= a1 (store a0 i v)))

;matrix[1][1] = 2
(assert (= m_1 (store m_0 1 (store (select m_0 1) 1 2))))

;matrix[1][2] = 3
(assert (= m_1 (store m_0 1 (store (select m_0 1) 2 3))))

;matrix[1][3] = 4
(assert (= m_1 (store m_0 1 (store (select m_0 1) 3 4))))

;matrix[2][1] = 3
(assert (= m_1 (store m_0 2 (store (select m_0 2) 1 3))))

;matrix[2][2] = 4
(assert (= m_1 (store m_0 2 (store (select m_0 2) 2 4))))

;matrix[2][3] = 5
(assert (= m_1 (store m_0 2 (store (select m_0 2) 3 5))))

;matrix[3][1] = 4
(assert (= m_1 (store m_0 3 (store (select m_0 3) 1 4))))

;matrix[3][2] = 5
(assert (= m_1 (store m_0 3 (store (select m_0 3) 2 5))))

;matrix[3][3] = 6
(assert (= m_1 (store m_0 3 (store (select m_0 3) 3 6 ))))

(check-sat)

(echo "------------Begin------------")

;-------------------------------------------------------------------------------
(declare-const i Int)
(declare-const j Int)
(declare-const a Int)
(declare-const b Int)

;-------------------------------------------------------------------------------
;Se i=j entao M[i][j] =/= 3.
;Negativo : Se i=j entao M[i][j] = 3.

(echo "-----------")
(echo "alínea (a)")
(push)

(assert (= (select (select m_1 i) i) 3))
(check-sat)

(pop)
;-------------------------------------------------------------------------------
;para qualquer i,j (>=1 =<3) Mij = Mji
;Negativo: para qualquer i,j (>=1 =<3) Mij =/= Mji

(echo "-----------")
(echo "alínea (b)")
(push)

(assert (and (> i 0) (< i 4)))
(assert (and (> j 0) (< j 4)))
(assert (not (= (select (select m_1 i) j) (select (select m_1 j) i) )))
(check-sat)

(pop)
;-------------------------------------------------------------------------------
;para qualquer i,j (>=1 =<3), se i < j, Mij < 6

(echo "-----------")
(echo "alínea (c)")
(push)

(assert (and (> i 0) (< i 4)))
(assert (and (> j 0) (< j 4)))
(assert (not (=> (< i j) (< (select (select m_1 i) j) 6))))
(check-sat)

(pop)
;-------------------------------------------------------------------------------
;para qualquer i,a,b (>=1 =<3), se a > b, Mia > Mib

(echo "-----------")
(echo "alínea (d)")
(push)

(assert (and (> i 0) (< i 4)))
(assert (and (> a 0) (< a 4)))
(assert (and (> b 0) (< b 4)))
(assert (not (=> (> a b) (> (select (select m_1 i) a) (select (select m_1 i) b)))))
(check-sat)

(pop)
;-------------------------------------------------------------------------------
;para qualquer i,j (>=1 =<3), Mij + M(i+1)(j+1) == M(i+1)j + Mi(j+1)

(echo "-----------")
(echo "alínea (e)")
(push)

(assert (and (> i 0) (< i 4)))
(assert (and (> j 0) (< j 4)))
(assert (= a (+ i 1)))
(assert (= b (+ i 1)))
(assert (not (= (+ (select (select m_1 i) j) (select (select m_1 a) b)) (+ (select (select m_1 a) j) (select (select m_1 i) b)))))
(check-sat)

(pop)
(echo "-----------")
;-------------------------------------------------------------------------------
(echo "-------------End-------------")
