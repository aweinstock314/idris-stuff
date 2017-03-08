import Data.Vect

filter' : (a -> Bool) -> Vect n a -> (m ** (Vect m a, LTE m n))
filter' p [] = (0 ** ([], LTEZero))
filter' p (x :: xs) = case filter' p xs of
    (i ** (xs', wit)) => if p x
        then (S i ** (x :: xs', LTESucc wit))
        else (i ** (xs', lteSuccRight wit))
