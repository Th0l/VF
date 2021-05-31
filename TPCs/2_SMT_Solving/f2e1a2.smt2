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
