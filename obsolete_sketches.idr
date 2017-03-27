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

{-
foo : S (maximum a b) = maximum (S a) (S b)
--foo = Refl
foo {a=Z} {b} = Refl
foo {a=S b'} {b=Z} = Refl
foo {a=S a'} {b=S b'} = Refl where
    ind : S (maximum a' b) = maximum (S a') (S b)
    ind = foo
-}

{-
--mapAll : (P : a -> Type) -> (Q : b -> Type) -> (x : P a) -> Type -- -> All P vec -> All (Q . P) vec
--mapAll : (P : a -> Type) -> (Q : P a -> Type) -> All P vec -> All (Q . P) vec
mapAll : (P : a -> Type) -> (Q : Type -> Type) -> All P vec -> All (Q . P) vec
--mapAll = ?q
mapAll {vec=Nil} p q Nil = Nil
mapAll {vec=z :: zs} p q (y :: ys) = ?q
--mapAll {vec=z :: zs} p q (y :: ys) = (q (p z)) :: mapAll {vec=zs} p q ys
--mapAll {vec=(z :: zs)} p q (y :: ys) = (q . p) z :: mapAll {vec=zs} p q ys  --(q . p) x :: mapAll p q xs
-}

{-
foo : Either (maximum a b = a) (maximum a b = b)
foo {a} {b} = case checkLTE a b of
    Left LTEZero => Right Refl
    Left (LTESucc lte) => ?a2 -- foo {a=pred a} {b=pred b}
    Right LTEZero => Left (maximumZeroNLeft a)
    Right (LTESucc lte) => ?b2

monotonicImpliesSuccFLTEFSucc : {f : Nat -> Nat} -> ({n, m : Nat} -> LTE n m -> LTE (f n) (f m)) -> {x : Nat} -> LTE (S (f x)) (f (S x))
monotonicImpliesSuccFLTEFSucc {f} mono {x=Z} = ?a where
    p1 : f 0 `LTE` f 1
    p1 = mono (lteSuccRight LTEZero)
    p2 : 0 `LTE` f 0
    p2 = LTEZero
    p3 : 1 `LTE` S (f 0)
    p3 = LTESucc p2
    p4 : 1 `LTE` f 1
    p4 = ?c
monotonicImpliesSuccFLTEFSucc {f} mono {x=S x'} = ?b where
    ind : LTE (S (f x')) (f (S x'))
    ind = monotonicImpliesSuccFLTEFSucc mono
-}

{-
monotonicImpliesMaxHomomorphic : {f : Nat -> Nat} -> ({n, m : Nat} -> LTE n m -> LTE (f n) (f m)) -> maximum (f a) (f b) = f (maximum a b)
monotonicImpliesMaxHomomorphic {a=Z} {b} {f} mono = maximumLTE (mono LTEZero)
monotonicImpliesMaxHomomorphic {a=S a'} {b=Z} {f} mono = rewrite maximumCommutative (f (S a')) (f 0) in maximumLTE (mono LTEZero)
monotonicImpliesMaxHomomorphic {a=S a'} {b=S b'} {f} mono = goal where
    ind : maximum (f a') (f b') = f (maximum a' b')
    ind = monotonicImpliesMaxHomomorphic mono
    --indL : maximum (f a') (f b') `LTE` f (maximum a' b')
    --indR : f (maximum a' b') `LTE` maximum (f a') (f b')
    --indL = reflToLTERefl ind
    --indR = reflToLTERefl (sym ind)
    p1 : (LTE a' (maximum a' b'), LTE b' (maximum a' b'))
    p1 = lteMaximum
    p2 : (LTE (f a') (f (maximum a' b')), LTE (f b') (f (maximum a' b')))
    p2 = (mono (fst p1), mono (snd p1))
    p3a : maximum (f a') (f (maximum a' b')) = (f (maximum a' b'))
    p3a = maximumLTE (fst p2)
    p4 : f x `LTE` f (S x)
    p4 = mono (lteSuccRight lteRefl)
    p4' : maximum (f x) (f (S x)) = f (S x)
    p4' = maximumLTE p4
    p5 : Either (maximum x y = y) (maximum y x = x)
    p5 {x} {y} = case checkLTE x y of
        Left lte => Left (maximumLTE lte)
        Right lte => Right (maximumLTE lte)
    q1 : f (maximum (S a') (S b')) = f (S (maximum a' b'))
    q1 = cong (maximumSuccSucc a' b')
    q2 : (f (maximum (S a') (S b')) `LTE` f (S (maximum a' b')), f (S (maximum a' b')) `LTE` f (maximum (S a') (S b')))
    q2 = eqToLTE q1
    --q2 : Either (f (maximum (S a') (S b')) = f (S (maximum a' a'))) (f (maximum (S a') (S b')) = f (S (maximum b' b')))
    goalL : maximum (f (S a')) (f (S b')) `LTE` f (S (maximum a' b'))
    goalL = ?goalL
    goalR : f (S (maximum a' b')) `LTE` maximum (f (S a')) (f (S b'))
    goalR = ?goalR
    goal : maximum (f (S a')) (f (S b')) = f (S (maximum a' b'))
    goal = lteToEq goalL goalR
-}


lteToEq : LTE a b -> LTE b a -> a = b
lteToEq LTEZero LTEZero = Refl
lteToEq (LTESucc x) (LTESucc y) = cong (lteToEq x y)

eqToLTE : a = b -> (LTE a b, LTE b a)
eqToLTE Refl = (lteRefl, lteRefl)

monoSuccArgLTE : {f : Nat -> Nat} -> ({n, m : Nat} -> LTE n m -> LTE (f n) (f m)) -> f x `LTE` f (S x)
monoSuccArgLTE mono = mono (lteSuccRight lteRefl)
