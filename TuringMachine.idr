module TuringMachine

%default total

data Direction = L | R
data StateType = Accept | Reject | Continue

data TuringMachine : (state : Type) -> (alphabet : Type) -> Type where
    TM : {state : Type} -> {alphabet : Type} -> (state -> Maybe alphabet -> (state, Maybe alphabet, Direction)) -> (state -> StateType) -> state -> TuringMachine state alphabet

data Fuel = Empty | More (Lazy Fuel)

runTMForSteps : Fuel -> TuringMachine s a -> List a -> Maybe Bool
runTMForSteps steps (TM {state=s} {alphabet=a} transition stateTy init) input = feedTM steps init [] (map Just input) where
    mutual
        feedTM : Fuel -> s -> List (Maybe a) -> List (Maybe a) -> Maybe Bool
        feedTM Empty _ _ _ = Nothing
        feedTM (More fuel) state left [] = stepTM fuel left [] (transition state Nothing)
        feedTM (More fuel) state left (x::right) = stepTM fuel left right (transition state x)
        stepTM : Fuel -> List (Maybe a) -> List (Maybe a) -> (s, Maybe a, Direction) -> Maybe Bool
        stepTM n left right (state, x, dir) = case stateTy state of
            Accept => Just True
            Reject => Just False
            Continue => stepTM' n left right (state, x, dir)
        stepTM' : Fuel -> List (Maybe a) -> List (Maybe a) -> (s, Maybe a, Direction) -> Maybe Bool
        stepTM' n [] right (state, x, L) = feedTM n state [] (Nothing :: x :: right)
        stepTM' n (l::left) right (state, x, L) = feedTM n state left (l :: x :: right)
        stepTM' n left right (state, x, R) = feedTM n state (x :: left) right

natToFuel : Nat -> Fuel
natToFuel Z = Empty
natToFuel (S n) = More (natToFuel n)

partial
forever : Fuel
forever = More forever

partial
runTM : TuringMachine s a -> List a -> Bool
runTM tm input = case runTMForSteps forever tm input of
    Just result => result
    Nothing => const assert_unreachable "TM both halted and did not halt"

data Bit = O | I

-- for the regex (01)*
decideAlternatingBits : TuringMachine Int Bit
decideAlternatingBits = TM delta stateTy 2 where
    stateTy 0 = Reject
    stateTy 1 = Accept
    stateTy _ = Continue
    delta 2 Nothing = (1, Nothing, R) -- accept on empty/complete input
    delta 2 (Just O) = (3, Just O, R) 
    delta 2 (Just I) = (0, Just I, R)
    delta 3 Nothing = (0, Nothing, R) -- reject if the string ended after we saw a 0
    delta 3 (Just O) = (0, Just O, R)
    delta 3 (Just I) = (2, Just I, R)
    delta _ _ = (0, Nothing, R)

namespace Main
    partial
    main : IO ()
    main = do
        printLn $ runTM decideAlternatingBits []
        printLn $ runTM decideAlternatingBits [O, I, O, I, O, I]
        printLn $ runTM decideAlternatingBits [O, O, I]
