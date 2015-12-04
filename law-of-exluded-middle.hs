{-# LANGUAGE DeriveFunctor #-}
module Main where

import Prelude hiding (recip, minimum)
import Control.Monad (when)

newtype Cont r a = MkCont { runCont :: (a -> r) -> r }
    deriving (Functor)

instance Monad (Cont r) where
    return x = MkCont ($ x)
    m >>= f  = MkCont $ \k -> runCont m $ \x -> runCont (f x) k

callCC :: ((a -> Cont r b) -> Cont r a) -> Cont r a
callCC f = MkCont $ \k -> runCont (f (\x -> MkCont $ \k' -> k x)) k

lem :: Cont r (Either a (a -> r))
lem = MkCont $ \k -> k $ Right $ \x -> k (Left x)

lem' :: Cont r (Either a (a -> Cont r b))
lem' = MkCont $ \k -> k $ Right $ \x -> MkCont $ \k' -> k (Left x)

lem'' :: Cont r (Either a (a -> Cont r b))
lem'' = callCC $ \k -> return $ Right $ \x -> k $ Left x

callCC' :: ((a -> Cont r b) -> Cont r a) -> Cont r a
callCC' f = do
    check <- lem'
    case check of
        Left  x -> return x
        Right g -> f g

type Nat = Int
-- thought of as nonnegative integers

type Ix = Nat
minimum :: [Nat] -> Cont r (Ix, Ix -> Cont r ())
minimum as = callCC (go 0)
    where
    -- go i k = k (i, \j -> do if as !! j < as !! i then go j k >> return () else return ())
    go i k = k (i, \j -> when (as !! j < as !! i) (go j k >> return ()))

minimum' :: [Nat] -> Cont r (Ix, Ix -> Cont r ())
minimum' as = go 0 where
    go :: Ix -> Cont r (Ix, Ix -> Cont r ())
    go i = do
        oracle <- lem'
        case oracle of
            Left  j -> go j
            Right f -> return (i, \j ->
                if as!!j >= as!!i then return () else f j)

-- Given a natural number n, fakePrimalityTest n decides whether n is
-- prime or not. In the first case, it returns the Right option:
-- a function which takes a factor of n and produces any value whatsoever.
-- In the second case, it returns the Left option: some factor of n.
--
-- Of course, primality of natural numbers is actually decidable.
-- But it is not, or very expensive, for elements of more complicated rings,
-- for instance the ring of polynomials with rational coefficients.
fakePrimalityTest :: Nat -> Cont r (Either Nat (Nat -> Cont r b))
fakePrimalityTest n = lem'

-- Let m be a prime. Then it's well-known that Z/(m) is a field.
-- If m is not a prime, Z/(m) is still an "ideal field": a placeholder for
-- a real field. More specifically, for any number a there are the following
-- cases:
-- 1. a is zero in Z/(m).
-- 2. a is invertible in Z/(m).
-- 3. Z/(m) can be refined to a different ring, in which m is still zero.
--
-- recip m a calculates the inverse of a in the ideal field Z/(m).
-- It returns a possibly refined modulus m' and either Nothing,
-- if a is zero in the ideal field Z/(m'), or Just b, where b is the
-- inverse to a in Z/(m').
recip :: Nat -> Nat -> Cont r (Nat, Maybe Nat)
recip m a = do
    -- Is m prime?
    check <- fakePrimalityTest m

    case check of
        -- No, it isn't. It has m' as a nontrivial factor.
        -- Then calculate the inverse of a modulo m'.
        Left  m' -> recip m' a

        -- Yes, it is. Then calculate the inverse modulo m.
        Right f  -> do
            -- f is the witness of primality: If we execute f with a factor of m,
            -- we obtain a witness of contradiction, i.e. a value of any type
            -- we want.

            let (b, _, d) = bezout (a `mod` m) m
            -- We have the equation d = b a + _ m, thus d = b a modulo m.

            -- If the gcd is 1, b is the sought inverse.
            if d == 1 then return (m, Just b) else do

            -- If the gcd is m, a was a multiple of m, so is zero modulo m
            -- and therefore doesn't have an inverse.
            if d == m then return (m, Nothing) else do

            -- If the gcd is neither 1 nor m, then a is not zero modulo m,
            -- but still does not have an inverse modulo m.
            -- Since m is prime in this branch, we can use the given witness
            -- of primality, f, to formally deduce a contradiction.
            f d

-- Given numbers a and b, return a Bézout representation of the greatest common
-- divisor of a and b, that is (x,y,d) such that ax + by = d, where d = gcd(a,b).
-- Note that x and y might be negative.
bezout :: Nat -> Nat -> (Int, Int, Nat)
bezout a 0 = (1, 0, a)
bezout a b = (t, s - q * t, g) 
    where
    (q, r)    = a `quotRem` b
    (s, t, g) = bezout b r
