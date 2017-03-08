module DeMorgan

DNE : Type -> Type
DNE a = (Not (Not a)) -> a

infixl 8 &
(&) : Type -> Type -> Type
a & b = (a, b)

contrapositive_eq : (a -> b) -> (Not b -> Not a)
contrapositive_eq f notb a = notb (f a)

or_as_implication : Either (Not a) b -> (a -> b)
or_as_implication (Left nota) a = absurd (nota a)
or_as_implication (Right b) a = b


lem_context : (Either a (Not a) -> b) -> Not (Not b)
lem_context {a} f notb = absurd (notb (f (Right g))) where
    g : Not a
    g x = notb (f (Left x))

{-
lem_context' : (({a : _} -> Either a (Not a)) -> b) -> Not (Not b)
--lem_context' f notb = absurd (notb (f (Right (\x => (notb (f (Left x)))))))
lem_context' f notb = absurd (notb (f (Right g))) where
    g : Not a
    g x = notb (f (Left x))
-}

{-
| !(a | !a)
| ---------
| | a
| | -
| | (a | !a)
| | _|_
| !a
| !a | a
| _|_
!!(a | !a)
-}
notnotLEM : Not (Not (Either a (Not a)))
notnotLEM = lem_context id
--notnotLEM notor = notor (Right (\x => notor (Left x)))
{-
notnotLEM {a} notor = notor (Right f) where
    f : Not a
    f x = notor (Left x)
-}

dni : a -> Not (Not a)
dni a nota = nota a

dne' : Not (Not (Not a)) -> Not a
dne' not3a a = not3a (dni a)

DeMorganOr : Type -> Type -> Type
DeMorganOr a b = Either (Not a) (Not b) -> Not (a, b)
DeMorganAnd : Type -> Type -> Type
DeMorganAnd a b = (Not a, Not b) -> Not (Either a b)

DeMorganOrLHS : Type -> Type -> Type
DeMorganOrLHS a b = Either (Not a) (Not b)
DeMorganOrRHS : Type -> Type -> Type
DeMorganOrRHS a b = Not (a, b)

--demorgan_or : DeMorganOr a b
demorgan_or : DeMorganOrLHS a b -> DeMorganOrRHS a b
demorgan_or (Left nota) = (\(a, _) => nota a)
demorgan_or (Right notb) = (\(_, b) => notb b)

-- HoTT book asserts that (Not (a, b) -> Either (Not a) (Not b)) isn't constructively provable, but its double-negation should still be provable
--demorgan_or' : Not (Not (Not (a, b) -> Either (Not a) (Not b))) -- !!(!(a&b) -> (!a | !b))
--demorgan_or' f = f g where
--    --g : Not (Not (a, b) -> Either (Not a) (Not b))
--    g h = ?x where
--        j : Not (a,b)
--        j = contrapositive_eq h id
--    --i (Left j) = ?y
--    --i (Right j) = ?z
--    --h : Not (a, b) -> Either (Not a) (Not b)

demorgan_or' : DeMorganOrRHS a b -> Not (Not (DeMorganOrLHS a b))
demorgan_or' {a} {b} not_aandb = dne' g where
    f : Either a (Not a) -> Either b (Not b) -> DeMorganOrLHS a b
    f (Left x) (Left y) = absurd (not_aandb (x, y))
    f (Left x) (Right noty) = Right noty
    f (Right notx) _ = Left notx
    g : Not (Not (Not (Not (DeMorganOrLHS a b))))
    g = lem_context (\lem_a => lem_context (\lem_b => f lem_a lem_b))

DeMorganAndLHS : Type -> Type -> Type
DeMorganAndLHS a b = (Not a, Not b)
DeMorganAndRHS : Type -> Type -> Type
DeMorganAndRHS a b = Not (Either a b)

--demorgan_and : DeMorganAnd a b
demorgan_and : DeMorganAndLHS a b -> DeMorganAndRHS a b
demorgan_and (nota, notb) = notor where
    notor (Left a) = nota a
    notor (Right b) = notb b

--demorgan_and' : Not (Either a b) -> (Not a, Not b)
demorgan_and' : { a: Type } -> { b : Type } -> DeMorganAndRHS a b -> DeMorganAndLHS a b
-- it'd be nice to be able to say (demorgan_and' : Converse DeMorganAnd a b) instead of having to explicitly declare the LHS/RHS types
-- is there a way to define Converse s.t. (Converse (a -> b) = (b -> a)) in Idris?
demorgan_and' notor = (\a => notor (Left a), \b => notor (Right b))
