import Data.Vect
import Data.Vect.Quantifiers

%default total

reflToLTERefl : n = m -> LTE n m
reflToLTERefl Refl = lteRefl

monotonicInc : (f : Nat -> Nat) -> Type
monotonicInc f = {n : Nat} -> {m : Nat} -> LTE n m -> LTE (f n) (f m)

composeMonotonic : (monotonicInc f) -> (monotonicInc g) -> (monotonicInc (f . g))
composeMonotonic {f} {g} monof monog = monoh where
    monoh : {x, y : Nat} -> LTE x y -> LTE (f (g x)) (f (g y))
    monoh lte = monof (monog lte)

plusMonotonic : (k : Nat) -> monotonicInc (\x => k + x)
plusMonotonic Z lte = lte
plusMonotonic (S x) lte = LTESucc (plusMonotonic x lte)

plusMonotonicRight : (k : Nat) -> LTE n m -> LTE (n + k) (m + k)
plusMonotonicRight {n} {m} k lte = rewrite plusCommutative n k in rewrite plusCommutative m k in plusMonotonic k lte

predMonotonic : monotonicInc Prelude.Nat.pred
predMonotonic LTEZero = LTEZero
predMonotonic (LTESucc lte) = lte

minusMonotonicLeft : (k : Nat) -> monotonicInc (\x => x `minus` k)
minusMonotonicLeft k = mono k where
    mono : (k : Nat) -> {n, m : Nat} -> LTE n m -> LTE (n `minus` k) (m `minus` k)
    mono {n} {m} Z l2 = rewrite minusZeroRight n in rewrite minusZeroRight m in l2
    mono {n} {m} (S k') l2 = ind'' where
        ind : LTE (minus n k') (minus m k')
        ind = mono k' l2
        p1 : (minus n (S k')) = Prelude.Nat.pred (minus n k')
        p1 = rewrite minusSuccPred n k' in Refl
        p2 : (minus m (S k')) = Prelude.Nat.pred (minus m k')
        p2 = rewrite minusSuccPred m k' in Refl
        ind' : LTE (Prelude.Nat.pred (minus n k')) (Prelude.Nat.pred (minus m k'))
        ind' = predMonotonic ind
        ind'' : LTE (minus n (S k')) (minus m (S k'))
        ind'' = rewrite p1 in rewrite p2 in ind'

ltePredRight : (a `minus` S b) `LTE` (a `minus` b)
ltePredRight {a=Z} = LTEZero
ltePredRight {a=S a'} {b=Z} = rewrite minusZeroRight a' in lteSuccRight lteRefl
ltePredRight {a=S a'} {b=S b'} = ltePredRight {a=a'} {b=b'}

lteMinusZeroRight : LTE (a `minus` k) (a `minus` 0)
lteMinusZeroRight {k=Z} = lteRefl
lteMinusZeroRight {a} {k=S k'} = ltePredRight `lteTransitive` lteMinusZeroRight 

minusMonotonicRight : (k : Nat) -> LTE n m -> LTE (k `minus` m) (k `minus` n)
minusMonotonicRight _ LTEZero = lteMinusZeroRight
minusMonotonicRight {n=S n'} {m=S m'} k (LTESucc lte) = goal where
    ind : LTE (k `minus` m') (k `minus` n')
    ind = minusMonotonicRight k lte
    tmp : LTE (pred (k `minus` m')) (pred (k `minus` n'))
    tmp = predMonotonic ind
    goal : LTE (k `minus` S m') (k `minus` S n')
    goal = rewrite minusSuccPred k n' in rewrite minusSuccPred k m' in tmp

succMinusInnerLeft : {smaller : LTE b a} -> S (a `minus` b) = S a `minus` b
succMinusInnerLeft {a=Z} {b=Z} = Refl
succMinusInnerLeft {a=S a'} {b=Z} = Refl
succMinusInnerLeft {a=Z} {b=S b'} {smaller} = absurd (succNotLTEzero smaller)
succMinusInnerLeft {a=S a'} {b=S b'} {smaller=LTESucc lte} = succMinusInnerLeft {a=a'} {b=b'} {smaller=lte}

multMonotonicLeft : (k : Nat) -> monotonicInc (\x => k * x)
multMonotonicLeft k = mono k where
    mono : (k : Nat) -> LTE n m -> LTE (k `mult` n) (k `mult` m)
    mono Z lte = LTEZero
    mono {n} {m} (S x) lte = z where
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

powerMonotonicBase : (k : Nat) -> monotonicInc (\x => power x (S k))
powerMonotonicBase k = mono k where
    mono : (k : Nat) -> LTE n m -> LTE (power n (S k)) (power m (S k))
    mono {n} {m} Z lte = rewrite multOneRightNeutral n in rewrite multOneRightNeutral m in lte
    mono {n} {m} (S x) lte = left `lteTransitive` right where
        ind : LTE (power n (S x)) (power m (S x))
        ind = mono x lte
        left : LTE (power n (S (S x))) (n * power m (S x))
        left = multMonotonicLeft n ind
        right : LTE (n * power m (S x)) (power m (S (S x)))
        right = multMonotonicRight (power m (S x)) lte

nonzeroPowerGTE1 : (n : Nat) -> (m : Nat) -> LTE 1 (power (S n) m)
nonzeroPowerGTE1 Z y = reflToLTERefl . sym $ powerOneSuccOne y
nonzeroPowerGTE1 (S x) Z = lteRefl
nonzeroPowerGTE1 (S x) (S y) = (ind `lteTransitive` ind') `lteTransitive` ind'' where
    ind : LTE 1 (power (S x) y)
    ind = nonzeroPowerGTE1 x y
    p1 : LTE (S x) (S (S x))
    p1 = lteSuccRight lteRefl
    ind' : LTE (power (S x) y) (power (S x) (S y))
    ind' = lteMultRight x lteRefl
    ind'' : LTE (power (S x) (S y)) (power (S (S x)) (S y))
    ind'' = powerMonotonicBase y p1

nonzeroPowerGTEBase : LTE b (power b (S n))
nonzeroPowerGTEBase {b} {n=Z} = rewrite multOneRightNeutral b in lteRefl
nonzeroPowerGTEBase {b=Z} {n} = lteRefl
nonzeroPowerGTEBase {b=S b'} {n=S n'} = ind `lteTransitive` step where
    b : Nat
    b = S b'
    ind : LTE b (b `mult` power b n')
    ind = nonzeroPowerGTEBase {n=n'}
    step : LTE (b `mult` power b n') (b `mult` (b `mult` power b n'))
    step = lteMultRight b' (lteRefl {n=b `mult` power b n'})

powerMonotonicExp : (b : Nat) -> monotonicInc (\x => power (S b) x)
powerMonotonicExp b = mono where
    mono : {i, j : Nat} -> LTE i j -> LTE (power (S b) i) (power (S b) j)
    mono {i=Z} {j=Z} lte = lteRefl
    mono {i=S i'} {j=Z} lte = absurd (succNotLTEzero lte)
    mono {i=Z} {j=S j'} lte = nonzeroPowerGTE1 b (S j')
    mono {i=S i'} {j=S j'} lte = multMonotonicLeft (S b) ind where
        ind : LTE (power (S b) i') (power (S b) j')
        ind = mono (fromLteSucc lte)

lteMaximum : (LTE a (maximum a b), LTE b (maximum a b))
lteMaximum {a=Z} {b} = (LTEZero, lteRefl)
lteMaximum {a=S a'} {b=Z} = (lteRefl, LTEZero)
lteMaximum {a=S a'} {b=S b'} = (LTESucc (fst ind), LTESucc (snd ind)) where
    ind : (LTE a' (maximum a' b'), LTE b' (maximum a' b'))
    ind = lteMaximum

maximumLTE : LTE a b -> maximum a b = b
maximumLTE LTEZero = Refl
maximumLTE (LTESucc lte) = rewrite maximumLTE lte in Refl

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

monotonicIncImpliesMaxHomomorphicLemma : {f : Nat -> Nat} -> ({n, m : Nat} -> LTE n m -> LTE (f n) (f m)) -> LTE a b -> maximum (f a) (f b) = f (maximum a b)
monotonicIncImpliesMaxHomomorphicLemma {f} mono {a} {b} lte_ab = rewrite left in right where
    left : maximum (f a) (f b) = f b
    left = maximumLTE (mono lte_ab)
    right : f b = f (maximum a b)
    right = rewrite maximumLTE lte_ab in Refl

monotonicIncImpliesMaxHomomorphic : {f : Nat -> Nat} -> ({n, m : Nat} -> LTE n m -> LTE (f n) (f m)) -> maximum (f a) (f b) = f (maximum a b)
monotonicIncImpliesMaxHomomorphic {f} {a} {b} mono = case checkLTE a b of
    Left lte_ab => monotonicIncImpliesMaxHomomorphicLemma mono lte_ab
    Right lte_ba => rewrite maximumCommutative (f a) (f b) in rewrite maximumCommutative a b in monotonicIncImpliesMaxHomomorphicLemma mono lte_ba

data Tern = Root | Branch Tern Tern Tern

height : Tern -> Nat
height Root = 0
height (Branch t1 t2 t3) = S ((height t1 `maximum` height t2) `maximum` height t3)

nodes : Tern -> Nat
nodes Root = 1
nodes (Branch t1 t2 t3) = S (nodes t1 + nodes t2 + nodes t3)

hb_f : Nat -> Nat
hb_f h = (-) (power 3 (S h)) 1 {smaller=nonzeroPowerGTE1 2 (S h)}
--hb_f = (\x => x `minus` 1) . (\x => power 3 x) . S

mono_hb_f : LTE n m -> LTE (hb_f n) (hb_f m)
mono_hb_f = composeMonotonic (minusMonotonicLeft 1) (powerMonotonicExp 2) `composeMonotonic` LTESucc

height_bound : (t : Tern) -> LTE (nodes t) (hb_f (height t))
height_bound Root = lteAddRight 1
height_bound (Branch t1 t2 t3) = goal where
    r1 : Nat
    r2 : Nat
    r3 : Nat
    r1 = hb_f (height t1)
    r2 = hb_f (height t2)
    r3 = hb_f (height t3)
    maxHeight : Nat
    maxHeight = (maximum (height t1) (height t2) `maximum` height t3)
    s1 : maximum r1 r2 = hb_f (maximum (height t1) (height t2))
    s1 = monotonicIncImpliesMaxHomomorphic mono_hb_f
    s2 : hb_f (maximum (height t1) (height t2)) `maximum` r3 = hb_f maxHeight
    s2 = monotonicIncImpliesMaxHomomorphic mono_hb_f
    s3 : maximum r1 r2 `maximum` r3 = hb_f maxHeight
    s3 = rewrite s1 in s2
    ind1 : LTE (nodes t1) r1
    ind1 = height_bound t1
    ind2 : LTE (nodes t2) r2
    ind2 = height_bound t2
    ind3 : LTE (nodes t3) r3
    ind3 = height_bound t3
    p1 : LTE (nodes t1 + nodes t2 + nodes t3) (r1 + r2 + r3)
    p1 = addLTE ind1 ind2 `addLTE` ind3
    p2 : LTE (r1 + r2 + r3) (3 * (maximum r1 r2 `maximum` r3))
    p2 = sumBoundedBy3Max
    p3 : LTE (r1 + r2 + r3) (3 * hb_f maxHeight)
    p3 = rewrite sym s3 in p2
    p4 : LTE (r1 + r2 + r3) (3 * ((power 3 (S maxHeight)) `minus` 1))
    p4 = p3
    p5 : LTE (r1 + r2 + r3) (3 * power 3 (S maxHeight) `minus` 3)
    p5 = rewrite sym $ multDistributesOverMinusRight 3 (power 3 (S (maximum (height t1) (height t2) `maximum` height t3))) 1 in p4
    p6 : LTE (r1 + r2 + r3) (power 3 (S (height (Branch t1 t2 t3))) `minus` 3)
    p6 = p5
    p7 : LTE (nodes (Branch t1 t2 t3)) (S (power 3 (S (height (Branch t1 t2 t3))) `minus` 3))
    p7 = LTESucc (p1 `lteTransitive` p6)
    q1 : (S (power 3 (S (height (Branch t1 t2 t3))) `minus` 3)) = S (power 3 (S (height (Branch t1 t2 t3)))) `minus` 3
    q1 = succMinusInnerLeft {smaller=nonzeroPowerGTEBase}
    q2 : (S (power 3 (S (height (Branch t1 t2 t3))) `minus` 3)) = power 3 (S (height (Branch t1 t2 t3))) `minus` 2
    q2 = q1
    looser : LTE (power 3 (S (height (Branch t1 t2 t3))) `minus` 2) (power 3 (S (height (Branch t1 t2 t3))) `minus` 1)
    looser = minusMonotonicRight (power 3 (S (height (Branch t1 t2 t3)))) (the (LTE 1 2) (LTESucc LTEZero))
    tightGoal : LTE (nodes (Branch t1 t2 t3)) (power 3 (S (height (Branch t1 t2 t3))) `minus` 2)
    tightGoal = rewrite sym q2 in p7
    goal : LTE (nodes (Branch t1 t2 t3)) (hb_f (height (Branch t1 t2 t3)))
    goal = tightGoal `lteTransitive` looser
