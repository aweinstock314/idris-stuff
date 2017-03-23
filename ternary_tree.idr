reflToLTERefl : n = m -> LTE n m
reflToLTERefl Refl = lteRefl

oneLTENonzero : {n : Nat} -> LTE 1 (S n)
oneLTENonzero {n=Z} = lteRefl
oneLTENonzero {n=S m} = lteSuccRight oneLTENonzero

nonzeroMultIsNonzero : (n : Nat) -> (m : Nat) -> LTE 1 (S n * S m)
nonzeroMultIsNonzero Z Z = lteRefl
nonzeroMultIsNonzero (S n) m = oneLTENonzero

pow1n_GTE_1 : (n : Nat) -> LTE 1 (power 1 n)
pow1n_GTE_1 n = reflToLTERefl . sym $ powerOneSuccOne n

pow0n_EQ_0 : power 0 (S k) = 0
pow0n_EQ_0 = Refl

plusMonotonic : (k : Nat) -> LTE n m -> LTE (k + n) (k + m)
plusMonotonic {n} {m} Z lte = lte
plusMonotonic {n} {m} (S x) lte = LTESucc (plusMonotonic x lte)

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


multDistributesOverSuccLeft : (n : Nat) -> (m : Nat) -> n + (mult m n) = mult n (S m)
multDistributesOverSuccLeft n m = rewrite multCommutative n (S m) in Refl

aPlusBMinusAIsB : (a : Nat) -> (b : Nat) -> {smaller : LTE a b} -> (a + (b - a)) = b
aPlusBMinusAIsB Z Z = Refl
aPlusBMinusAIsB (S x) Z {smaller} = absurd (succNotLTEzero smaller)
aPlusBMinusAIsB Z (S y) = Refl
aPlusBMinusAIsB (S x) (S y) {smaller} = cong (aPlusBMinusAIsB x y {smaller=fromLteSucc smaller})

data Tern = Root | Branch Tern Tern Tern

height : Tern -> Nat
height Root = 0
height (Branch t1 t2 t3) = foldl1 max (map height [t1, t2, t3]) + 1

nodes : Tern -> Nat
nodes Root = 1
nodes (Branch t1 t2 t3) = sum (map nodes [t1, t2, t3]) + 1

height_bound : (t : Tern) -> LTE (nodes t) ((-) (power 3 (S (height t))) 1 {smaller=nonzeroPowerGTE1})
height_bound Root = ?x
height_bound (Branch t1 t2 t3) = ?y
