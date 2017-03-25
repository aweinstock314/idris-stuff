import Data.Vect
import Data.Vect.Quantifiers

%default total

reflToLTERefl : n = m -> LTE n m
reflToLTERefl Refl = lteRefl

oneLTENonzero : {n : Nat} -> LTE 1 (S n)
oneLTENonzero {n=Z} = lteRefl
oneLTENonzero {n=S m} = lteSuccRight oneLTENonzero

{-
nonzeroMultIsNonzero : (n : Nat) -> (m : Nat) -> LTE 1 (S n * S m)
nonzeroMultIsNonzero Z Z = lteRefl
nonzeroMultIsNonzero (S n) m = oneLTENonzero
-}

pow1n_GTE_1 : (n : Nat) -> LTE 1 (power 1 n)
pow1n_GTE_1 n = reflToLTERefl . sym $ powerOneSuccOne n

pow0n_EQ_0 : power 0 (S k) = 0
pow0n_EQ_0 = Refl

succMonotonic : LTE n m -> LTE (S n) (S m)
succMonotonic = LTESucc

plusMonotonic : (k : Nat) -> LTE n m -> LTE (k + n) (k + m)
plusMonotonic Z lte = lte
plusMonotonic (S x) lte = LTESucc (plusMonotonic x lte)

plusMonotonicRight : (k : Nat) -> LTE n m -> LTE (n + k) (m + k)
plusMonotonicRight {n} {m} k lte = rewrite plusCommutative n k in rewrite plusCommutative m k in plusMonotonic k lte

predMonotonic : LTE n m -> LTE (pred n) (pred m)
predMonotonic LTEZero = LTEZero
predMonotonic (LTESucc lte) = lte

minusMonotonic : (k : Nat) -> (l1 : LTE k n) -> (l2 : LTE n m) -> LTE (n - k) ((-) m k {smaller=l1 `lteTransitive` l2})
minusMonotonic {n} {m} Z l1 l2 = rewrite minusZeroRight n in rewrite minusZeroRight m in l2
minusMonotonic {n} {m} (S k') l1 l2 = ind'' where
    tmp : LTE k' (S k')
    tmp = lteSuccRight lteRefl
    tmp2 : LTE k' n
    tmp2 = tmp `lteTransitive` l1
    ind : LTE ((-) n k' {smaller=tmp2}) ((-) m k' {smaller=tmp2 `lteTransitive` l2})
    ind = minusMonotonic k' tmp2 l2
    p1 : ((-) n (S k') {smaller=l1}) = Prelude.Nat.pred ((-) n k' {smaller=tmp2})
    p1 = rewrite minusSuccPred n k' in Refl
    p2 : ((-) m (S k') {smaller=l1 `lteTransitive` l2}) = Prelude.Nat.pred ((-) m k' {smaller=tmp2 `lteTransitive` l2})
    p2 = rewrite minusSuccPred m k' in Refl
    ind' : LTE (Prelude.Nat.pred ((-) n k' {smaller=tmp2})) (Prelude.Nat.pred ((-) m k' {smaller=tmp2 `lteTransitive` l2}))
    ind' = predMonotonic ind
    ind'' : LTE ((-) n (S k') {smaller=l1}) ((-) m (S k') {smaller=l1 `lteTransitive` l2})
    ind'' = rewrite p1 in rewrite p2 in ind'

minusMonotonic' : (k : Nat) -> {n,m : Nat} -> LTE n m -> LTE (n `minus` k) (m `minus` k)
minusMonotonic' {n} {m} Z l2 = rewrite minusZeroRight n in rewrite minusZeroRight m in l2
minusMonotonic' {n} {m} (S k') l2 = ind'' where
    ind : LTE (minus n k') (minus m k')
    ind = minusMonotonic' k' l2
    p1 : (minus n (S k')) = Prelude.Nat.pred (minus n k')
    p1 = rewrite minusSuccPred n k' in Refl
    p2 : (minus m (S k')) = Prelude.Nat.pred (minus m k')
    p2 = rewrite minusSuccPred m k' in Refl
    ind' : LTE (Prelude.Nat.pred (minus n k')) (Prelude.Nat.pred (minus m k'))
    ind' = predMonotonic ind
    ind'' : LTE (minus n (S k')) (minus m (S k'))
    ind'' = rewrite p1 in rewrite p2 in ind'

composeMonotonic : {f : Nat -> Nat} -> {g : Nat -> Nat} -> ({a, b : Nat} -> LTE a b -> LTE (f a) (f b)) -> ({n, m : Nat} -> LTE n m -> LTE (g n) (g m)) -> ({x, y : Nat} -> LTE x y -> LTE (f (g x)) (f (g y)))
composeMonotonic {f} {g} monof monog = monoh where
    monoh : {x, y : Nat} -> LTE x y -> LTE (f (g x)) (f (g y))
    monoh lte = monof (monog lte)

multMonotonicLeft : (k : Nat) -> LTE n m -> LTE (k `mult` n) (k `mult` m)
multMonotonicLeft Z lte = LTEZero
--multMonotonicLeft {n} {m} (S x) lte = lteTransitive (plusMonotonic n (multMonotonicLeft x lte)) (rewrite plusCommutative n (x * m) in rewrite plusCommutative m (x * m) in plusMonotonic (x * m) lte)
multMonotonicLeft {n} {m} (S x) lte = z where
    x1 : LTE (x * n) (x * m)
    x1 = multMonotonicLeft x lte
    x2 : LTE (n + (x * n)) (n + (x * m))
    x2 = plusMonotonic n x1
    x3 : LTE ((S x) * n) (n + (x * m))
    x3 = x2
    y1 : LTE ((x * m) + n) ((x * m) + m)
    y1 = plusMonotonic (x * m) lte
    y2 : LTE (n + (x * m)) (m + (x * m))
    y2 = rewrite plusCommutative n (x * m) in rewrite plusCommutative m (x * m) in y1
    y3 : LTE (n + (x * m)) ((S x) * m)
    y3 = y2
    z : LTE ((S x) * n) ((S x) * m)
    z = lteTransitive x3 y3

multMonotonicRight : (k : Nat) -> LTE n m -> LTE (n * k) (m * k)
multMonotonicRight {n} {m} k lte = rewrite multCommutative n k in rewrite multCommutative m k in multMonotonicLeft k lte

lteMultRight : (k : Nat) -> LTE n m -> LTE n ((S k) * m)
lteMultRight {m} Z lte = rewrite multOneLeftNeutral m in lte
lteMultRight {n} {m} (S k') lte = ind `lteTransitive` p2 where
    ind : LTE n (S k' * m)
    ind = lteMultRight k' lte
    p1 : LTE (S k' * m) ((S k' * m) + m)
    p1 = lteAddRight (S k' * m)
    p2 : LTE (S k' * m) (m + (S k' * m))
    p2 = rewrite plusCommutative m (S k' * m) in p1


{-
ltePredLeft : LTE a b -> LTE (pred a) b
ltePredLeft = ?lte_pred_left

lteToDiff : LTE a b -> (k ** b - a = k)
lteToDiff {b} LTEZero = (b ** minusZeroRight b)
lteToDiff {a} {b} (LTESucc lte) = case lteToDiff lte of
    (k ** eq) => (S k ** rewrite minusSuccSucc a b in eq)
-}

powerMonotonicBase : (k : Nat) -> LTE n m -> LTE (power n (S k)) (power m (S k))
powerMonotonicBase {n} {m} Z lte = rewrite multOneRightNeutral n in rewrite multOneRightNeutral m in lte
powerMonotonicBase {n} {m} (S x) lte = left `lteTransitive` right where
    ind : LTE (power n (S x)) (power m (S x))
    ind = powerMonotonicBase x lte
    left : LTE (power n (S (S x))) (n * power m (S x))
    left = multMonotonicLeft n ind
    right : LTE (n * power m (S x)) (power m (S (S x)))
    right = multMonotonicRight (power m (S x)) lte

nonzeroPowerGTE1 : (n : Nat) -> (m : Nat) -> LTE 1 (power (S n) m)
nonzeroPowerGTE1 Z y = reflToLTERefl . sym $ powerOneSuccOne y
nonzeroPowerGTE1 (S x) Z = lteRefl
--nonzeroPowerGTE1 (S x) (S y) = oneLTENonzero `lteTransitive` nonzeroPowerGTE1 x y
nonzeroPowerGTE1 (S x) (S y) = (ind `lteTransitive` ind') `lteTransitive` ind'' where
    ind : LTE 1 (power (S x) y)
    ind = nonzeroPowerGTE1 x y
    p1 : LTE (S x) (S (S x))
    p1 = lteSuccRight lteRefl
    ind' : LTE (power (S x) y) (power (S x) (S y))
    ind' = lteMultRight x lteRefl
    ind'' : LTE (power (S x) (S y)) (power (S (S x)) (S y))
    ind'' = powerMonotonicBase y p1

powerMonotonicExp : (i : Nat) -> (j : Nat) -> (b : Nat) -> LTE i j -> LTE (power (S b) i) (power (S b) j)
powerMonotonicExp Z Z b lte = lteRefl
powerMonotonicExp (S i') Z b lte = absurd (succNotLTEzero lte)
powerMonotonicExp Z (S j') b lte = nonzeroPowerGTE1 b (S j')
powerMonotonicExp (S i') (S j') b lte = multMonotonicLeft (S b) ind where
    ind : LTE (power (S b) i') (power (S b) j')
    ind = powerMonotonicExp i' j' b (fromLteSucc lte)

powerMonotonicExp' : (b : Nat) -> {i,j : Nat} -> LTE i j -> LTE (power (S b) i) (power (S b) j)
powerMonotonicExp' b {i} {j} = powerMonotonicExp i j b

multDistributesOverSuccLeft : (n : Nat) -> (m : Nat) -> n + (mult m n) = mult n (S m)
multDistributesOverSuccLeft n m = rewrite multCommutative n (S m) in Refl

aPlusBMinusAIsB : (a : Nat) -> (b : Nat) -> {smaller : LTE a b} -> (a + (b - a)) = b
aPlusBMinusAIsB Z Z = Refl
aPlusBMinusAIsB (S x) Z {smaller} = absurd (succNotLTEzero smaller)
aPlusBMinusAIsB Z (S y) = Refl
aPlusBMinusAIsB (S x) (S y) {smaller} = cong (aPlusBMinusAIsB x y {smaller=fromLteSucc smaller})

lteMaximum : (LTE a (maximum a b), LTE b (maximum a b))
lteMaximum {a=Z} {b} = (LTEZero, lteRefl)
lteMaximum {a=S a'} {b=Z} = (lteRefl, LTEZero)
lteMaximum {a=S a'} {b=S b'} = (LTESucc (fst ind), LTESucc (snd ind)) where
    ind : (LTE a' (maximum a' b'), LTE b' (maximum a' b'))
    ind = lteMaximum

maximumLTE : LTE a b -> maximum a b = b
maximumLTE LTEZero = Refl
maximumLTE (LTESucc lte) = rewrite maximumLTE lte in Refl

mapAll : {P, Q : a -> Type} -> (f : (x : a) -> P x -> Q x) -> All P xs -> All Q xs
mapAll _ Nil = Nil
mapAll {xs=i :: is} f (j :: js) = f i j :: mapAll f js

Maximum : Nat -> Nat -> Nat
Maximum = maximum -- hack around implicit capture

{-
maximumVecBound : (vec : Vect (S n) Nat) -> All (\e => LTE e (foldr1 Maximum vec)) vec
maximumVecBound (x :: []) = [lteRefl]
maximumVecBound {n=S m} (x :: xs) = step where
    maxElt : Nat
    maxElt = foldr1 maximum xs
    ind : All (\e => LTE e maxElt) xs
    ind = maximumVecBound xs
    p1 : (LTE x (maximum x maxElt), LTE maxElt (maximum x maxElt))
    p1 = lteMaximum
    --p2 : Maximum x (foldr Maximum Z xs) = foldr Maximum Z (x :: xs)
    --p2 = Refl
    step : All (\e => LTE e (foldr Maximum x xs)) (x :: xs)
    step = ?z
    --step = fst p1 :: mapAll {P=(\e => LTE e maxElt)} {Q=(\e => LTE e (maximum x maxElt))} (\e, lte => lte `lteTransitive` snd p1)
-}

{-
sumBoundedByKMax : (vec : Vect (S n) Nat) -> LTE (foldr (+) Z vec) (S n * foldr Maximum Z vec)
sumBoundedByKMax (x :: []) = rewrite maximumZeroNLeft x in lteRefl
sumBoundedByKMax {n=S m} (x :: xs) = ?sumBound where
    p1 : LTE (foldr (+) Z xs) (S m * foldr Maximum Z xs)
    p1 = sumBoundedByKMax xs
    p2 : LTE (x + foldr (+) Z xs) (x + S m * foldr Maximum Z xs)
    p2 = plusMonotonic x p1
-}

addLTE : LTE a b -> LTE x y -> LTE (a + x) (b + y)
addLTE {a} {b} {x} {y} ab xy = left `lteTransitive` right where
    left : LTE (a + x) (b + x)
    left = rewrite plusCommutative a x in rewrite plusCommutative b x in plusMonotonic x ab
    right : LTE (b + x) (b + y)
    right = plusMonotonic b xy

sumBoundedBy3Max : (a + b + c) `LTE` 3 * ((a `maximum` b) `maximum` c)
sumBoundedBy3Max {a} {b} {c} = s where
    x : Nat
    x = (a `maximum` b) `maximum` c
    p1 : (LTE a (maximum a b), LTE b (maximum a b))
    p1 = lteMaximum
    p2 : (LTE (maximum a b) x, LTE c x)
    p2 = lteMaximum
    la : LTE a x
    la = fst p1 `lteTransitive` fst p2
    lb : LTE b x
    lb = snd p1 `lteTransitive` fst p2
    lc : LTE c x
    lc = snd p2
    q : LTE (a+b+c) (x+x+x)
    q = addLTE (addLTE la lb) lc
    r1 : x + x = 2 * x
    r1 = rewrite plusZeroRightNeutral x in Refl
    r2 : x + (x + x) = 3 * x
    r2 = rewrite plusZeroRightNeutral x in rewrite r1 in Refl
    r3 : x + x + x = 3 * x
    r3 = rewrite sym $ plusAssociative x x x in r2
    s : LTE (a+b+c) (3*x)
    s = rewrite sym r3 in q

checkLTE : (n : Nat) -> (m : Nat) -> Either (LTE n m) (LTE m n)
checkLTE Z m = Left LTEZero
checkLTE n Z = Right LTEZero
checkLTE (S n) (S m) = case checkLTE n m of
    Left x => Left (LTESucc x)
    Right x => Right (LTESucc x)

lteToEq : LTE a b -> LTE b a -> a = b
lteToEq LTEZero LTEZero = Refl
lteToEq (LTESucc x) (LTESucc y) = cong (lteToEq x y)

eqToLTE : a = b -> (LTE a b, LTE b a)
eqToLTE Refl = (lteRefl, lteRefl)

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

data Tern = Root | Branch Tern Tern Tern

data CompleteTree : (n : Nat) -> Type where
    CRoot : CompleteTree (S n)
    CBranch : Vect (S n) (CompleteTree (S n)) -> CompleteTree (S n)

height : Tern -> Nat
height Root = 0
height (Branch t1 t2 t3) = S ((height t1 `maximum` height t2) `maximum` height t3)

{-
height' : CompleteTree n -> Nat
height' CRoot = 0
--height' (CBranch subtrees) = Data.Vect.foldl1 max (map height' subtrees)
height' (CBranch subtrees) = foldr (\subtree, acc => max acc (height' subtree)) Z subtrees
-}

nodes : Tern -> Nat
nodes Root = 1
nodes (Branch t1 t2 t3) = S (nodes t1 + nodes t2 + nodes t3)

minusOnePred : (a `minus` 1) = pred a
minusOnePred {a=Z} = Refl
minusOnePred {a=S a'} = minusZeroRight a'

ltePredRight : (a `minus` S b) `LTE` (a `minus` b)
ltePredRight {a=Z} = LTEZero
ltePredRight {a=S a'} {b=Z} = rewrite minusZeroRight a' in lteSuccRight lteRefl
ltePredRight {a=S a'} {b=S b'} = ltePredRight {a=a'} {b=b'}

lteMinusRight : LTE (a `minus` k) (a `minus` 0)
lteMinusRight {k=Z} = lteRefl
lteMinusRight {a} {k=S k'} = ltePredRight `lteTransitive` lteMinusRight 

height_bound : (t : Tern) -> LTE (nodes t) ((-) (power 3 (S (height t))) 1 {smaller=nonzeroPowerGTE1 2 (S (height t))})
height_bound Root = lteAddRight 1
height_bound (Branch t1 t2 t3) = ?y where
    f : Nat -> Nat
    f h = (-) (power 3 (S h)) 1 {smaller=nonzeroPowerGTE1 2 (S h)}
    --g : Nat -> Nat
    --g = (\x => x `minus` 1) . (\x => power 3 x) . S
    monof : {n, m : Nat} -> LTE n m -> LTE (f n) (f m)
    monof = composeMonotonic (minusMonotonic' 1) (powerMonotonicExp' 2) `composeMonotonic` LTESucc
    r1 : Nat
    r2 : Nat
    r3 : Nat
    r1 = f (height t1)
    r2 = f (height t2)
    r3 = f (height t3)
    s1 : maximum r1 r2 = f (maximum (height t1) (height t2))
    s1 = monotonicImpliesMaxHomomorphic monof
    s2 : f (maximum (height t1) (height t2)) `maximum` r3 = f (maximum (height t1) (height t2) `maximum` (height t3))
    s2 = monotonicImpliesMaxHomomorphic monof
    s3 : maximum r1 r2 `maximum` r3 = f (maximum (height t1) (height t2) `maximum` height t3)
    s3 = rewrite s1 in s2
    ind1 : LTE (nodes t1) r1
    ind1 = height_bound t1
    ind2 : LTE (nodes t2) r2
    ind2 = height_bound t2
    ind3 : LTE (nodes t3) r3
    ind3 = height_bound t3
    maxHeight : Nat
    maxHeight = (maximum (height t1) (height t2) `maximum` height t3)
    p1 : LTE (nodes t1 + nodes t2 + nodes t3) (r1 + r2 + r3)
    p1 = addLTE ind1 ind2 `addLTE` ind3
    p2 : LTE (r1 + r2 + r3) (3 * (maximum r1 r2 `maximum` r3))
    p2 = sumBoundedBy3Max
    p3 : LTE (r1 + r2 + r3) (3 * f maxHeight)
    p3 = rewrite sym s3 in p2
    p4 : LTE (r1 + r2 + r3) (3 * ((power 3 (S maxHeight)) `minus` 1))
    p4 = p3
    p5 : LTE (r1 + r2 + r3) (3 * power 3 (S maxHeight) `minus` 3)
    p5 = rewrite sym $ multDistributesOverMinusRight 3 (power 3 (S (maximum (height t1) (height t2) `maximum` height t3))) 1 in p4
    p6 : LTE (r1 + r2 + r3) (power 3 (S (S maxHeight)) `minus` 3)
    p6 = p5
    p7 : LTE (nodes (Branch t1 t2 t3)) (S (power 3 (S (S maxHeight)) `minus` 3))
    p7 = LTESucc (p1 `lteTransitive` p6)
    --loosenBound : (S (power 3 (S (S maxHeight)) `minus` 3)) = ((power 3 (S (S maxHeight)) `minus` 2))
    --loosenBound = rewrite predSucc (power 3 (S (S maxHeight)) `minus` 2) in
    loosenBound : (power 3 (S (S maxHeight)) `minus` 3) = (pred (power 3 (S (S maxHeight)) `minus` 2))
    loosenBound = minusSuccPred (power 3 (S (S maxHeight))) 2
    loosenBound' : S (power 3 (S (S maxHeight)) `minus` 3) = S (pred (power 3 (S (S maxHeight)) `minus` 2))
    loosenBound' = cong loosenBound
    --loosenBound'' : S (power 3 (S (S maxHeight)) `minus` 3) = power 3 (S (S maxHeight)) `minus` 2
    --loosenBound'' = rewrite foo (nonzeroPowerGTE1 2 (S (S maxHeight))) in loosenBound'
    --loosenBound'' = loosenBound'
