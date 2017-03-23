{-
foo : LTE a b -> LTE b c -> LTE c d -> LTE a d
foo x y z = (x `lteTransitive` y) `lteTransitive` z
-}

{-
plusMonotonic : LTE n m -> LTE (n + k) (m + k)
plusMonotonic {n} {m} {k=Z} lte = rewrite plusZeroRightNeutral n in rewrite plusZeroRightNeutral m in lte
plusMonotonic {n} {m} {k=S x} lte = rewrite sym $ plusSuccRightSucc n x in rewrite sym $ plusSuccRightSucc m x in LTESucc (plusMonotonic lte)
-}

{-
multMonotonicLeft : (k : Nat) -> LTE n m -> LTE (k `mult` n) (k `mult` m)
multMonotonicLeft {n} {m} Z lte = LTEZero
multMonotonicLeft {n} {m} (S x) lte = y1 where
    --rewrite multDistributesOverPlusLeft n x n in rewrite multDistributesOverPlusLeft m x m in
    --rewrite sym $ multDistributesOverSuccLeft n x in rewrite sym $ multDistributesOverSuccLeft m x in 
    {-bar = rewrite multDistributesOverSuccLeft x n in rewrite multDistributesOverSuccLeft x m in
    rewrite multCommutative x n in rewrite multCommutative x m in
    rewrite sym $ multRightSuccPlus n x in rewrite sym $ multRightSuccPlus m x in x1-}
    x1 : LTE (n + mult x n) (n + mult x m)
    x1 = plusMonotonic n (multMonotonicLeft x lte) --rewrite multRightSuccPlus n x in rewrite multRightSuccPlus m x in plusMonotonic lte
    y1 : LTE (n + mult x m) (n + mult x m + (m-n))
    y1 = lteAddRight {m=m-n} (plus n (mult x m))
    y2 : LTE (n + mult x m) (n + (mult x m + (m-n)))
    y2 = rewrite plusAssociative n (mult x m) (m-n) in y1
    y3 : LTE (n + mult x m) (n + ((m-n) + mult x m))
    y3 = rewrite plusCommutative (m-n) (mult x m) in y2
    y4 : LTE (n + mult x m) ((n + (m-n)) + mult x m)
    y4 = rewrite sym $ plusAssociative n (m-n) (mult x m) in y3
    y5 : LTE (n + mult x m) (m + mult x m)
    y5 = rewrite aPlusBMinusAIsB n m in y4

    --x2 = rewrite sym $ multRightSuccPlus n x in rewrite sym $ multRightSuccPlus m x in x1
    x2 : LTE (n + mult n x) (n + mult m x)
    x2 = rewrite multCommutative n x in rewrite multCommutative m x in x1
    {-
    x3 : LTE (mult n (S x)) (mult m (S x))
    x3 = rewrite multDistributesOverSuccLeft n x in rewrite multDistributesOverSuccLeft m x in x2
    -}
-}

