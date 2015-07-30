> module NonNegRational

> import Data.Sign

> import Rational
> import SignProperties

> %default total


* Specification

> ||| Non negative rationals
> data NonNegQ : Type where
>   MkNonNegQ : (q : Q) -> NonNeg q -> NonNegQ

Patrik: TODO: I have a feeling that using |Not| is overkill for finite
types like |Sign|. Note that the definition (|Not a = a -> Void|) uses
a function space so each element of |NonNegQ| will (at least
conceptually) contain a function.

> fromQ : (q : Q) -> Not (sign q = Minus) -> NonNegQ
> fromQ = MkNonNegQ

> toQ : NonNegQ -> Q

> toQSpec : (q : NonNegQ) -> NonNeg (toQ q)


* Constants

> zeroNonNegQ : NonNegQ
> zeroNonNegQ = fromQ zeroQ nonNegZeroQ


* Operations

> |||
> fromIntegerNonNegQ : Integer -> NonNegQ
> fromIntegerNonNegQ i with (fromIntegerQ i)
>   | q with (decEq (sign q) Minus)
>       | Yes _ = zeroNonNegQ
>       | No contra = fromQ q contra

> plus : NonNegQ -> NonNegQ -> NonNegQ
> plus q1 q2 = fromQ q nnq where
>   q   : Q
>   q   = Rational.plus (toQ q1) (toQ q2)
>   nnq : NonNeg q
>   nnq = plusSign1 (toQ q1) (toQ q2) (toQSpec q1) (toQSpec q2)

> minus : NonNegQ -> NonNegQ -> NonNegQ
> minus q1 q2 with (Rational.minus (toQ q1) (toQ q2))
>   | q with (decEq (sign q) Minus)
>       | Yes _ = zeroNonNegQ
>       | No contra = fromQ q contra

> mult : NonNegQ -> NonNegQ -> NonNegQ
> mult q1 q2 = fromQ q nnq where
>   q   : Q
>   q   = Rational.mult (toQ q1) (toQ q2)
>   nnq : NonNeg q
>   nnq = multSign1 (toQ q1) (toQ q2) (toQSpec q1) (toQSpec q2)


* Properties

> instance Num NonNegQ where
>   (+) = plus
>   (-) = minus
>   (*) = mult
>   
>   abs q = q
>   
>   fromInteger = fromIntegerNonNegQ
