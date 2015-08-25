> module GCD

> import NatPredicates
> import NatOperations
> import NatProperties
> import Unique
> import Basics

> %default total


Euclid's greatest common divisor algorithm

> euclidGCD1 : GCD m m Z
> euclidGCD1 {m} = mkGCD (anyDivisorAny m) (anyDivisorZ m) (\ d' => \ d'Dm => \ d'DZ => d'Dm)

> euclidGCD2 : GCD m Z m
> euclidGCD2 {m} = mkGCD (anyDivisorZ m) (anyDivisorAny m) (\ d' => \ d'DZ => \ d'Dm => d'Dm)

> euclidGCD3 : m `LTE` n -> GCD d m (n - m) -> GCD d m n
> euclidGCD3 {m} {n} {d} p (mkGCD dDm dDnmm q) = mkGCD dDm dDn q' where
>   dDnmmpm : d `Divisor` ((n - m) + m)
>   dDnmmpm = divisorPlusLemma1 m (n - m) d dDm dDnmm
>   dDn : d `Divisor` n
>   dDn = replace {x = (n - m) + m}
>                 {y = n}
>                 {P = \ ZUZU => d `Divisor` ZUZU}
>                 (plusRightInverseMinus m n p)
>                 dDnmmpm 
>   q' : (d' : Nat) -> d' `Divisor` m -> d' `Divisor` n -> d' `Divisor` d
>   q' d' d'Dm d'Dn = q d' d'Dm d'Dnmm where
>     d'Dnmm : d' `Divisor` (n - m)
>     d'Dnmm = divisorMinusLemma m n d' d'Dm d'Dn 

> euclidGCD4 : Not (m `LTE` n) -> GCD d (m - n) n -> GCD d m n
> euclidGCD4 {m} {n} {d} p (mkGCD dDmmn dDn q) = mkGCD dDm dDn q' where
>   dDmmnpn : d `Divisor` ((m - n) + n)
>   dDmmnpn = divisorPlusLemma2 (m - n) n d dDmmn dDn
>   dDm : d `Divisor` m
>   dDm = replace {x = (m - n) + n}
>                 {y = m}
>                 {P = \ ZUZU => d `Divisor` ZUZU}
>                 (plusRightInverseMinus n m (notLTELemma1 m n p))
>                 dDmmnpn 
>   q' : (d' : Nat) -> d' `Divisor` m -> d' `Divisor` n -> d' `Divisor` d
>   q' d' d'Dm d'Dn = q d' d'Dmmn d'Dn where
>     d'Dmmn : d' `Divisor` (m - n)
>     d'Dmmn = divisorMinusLemma n m d' d'Dn d'Dm 

> %assert_total
> euclidGCD : (m : Nat) -> (n : Nat) -> (d : Nat ** GCD d m n)
> euclidGCD    m   Z    = (m ** euclidGCD1)
> euclidGCD  Z       n  = (n ** euclidGCD2)
> euclidGCD (S m) (S n) with (decLTE (S m) (S n))
>   | (Yes p) = (gcd ** euclidGCD3 p P) where
>     gcdP : (d : Nat ** GCD d (S m) (S n - S m))
>     gcdP = assert_total (euclidGCD (S m) (S n - S m))
>     gcd  : Nat
>     gcd  = getWitness gcdP
>     P    : GCD gcd (S m) (S n - S m)
>     P    = getProof gcdP
>   | (No  p) = (gcd ** euclidGCD4 p P) where
>     gcdP : (d : Nat ** GCD d (S m - S n) (S n))
>     gcdP = assert_total (euclidGCD (S m - S n) (S n))
>     gcd  : Nat
>     gcd  = getWitness gcdP
>     P    : GCD gcd (S m - S n) (S n)
>     P    = getProof gcdP
 

> ||| Coprime is decidable
> decCoprime : (m : Nat) -> (n : Nat) -> Dec (Coprime m n)
> decCoprime m n with (euclidGCD m n) 
>   | (d ** v) with (decEq d (S Z))
>     | (Yes p) = Yes (mkCoprime {d = d} v p)
>     | (No contra) = No contra' where
>         contra' : Coprime m n -> Void
>         contra' (mkCoprime {d = d'} v' p') = contra p where
>           p : d = S Z
>           p = replace {x = d'} 
>                       {y = d} 
>                       {P = \ ZUZU => ZUZU = S Z} 
>                       (gcdUnique d' d v' v) p'


> ||| Coprime is unique
> uniqueCoprime : (m : Nat) -> (n : Nat) -> Unique (Coprime m n)
> {-
> uniqueCoprime m n (mkCoprime v1 p1) (mkCoprime v2 p2) = cong2 mkCoprime eqv eqp where
>   eqv : v1 = v2
>   eqv = ?kikz
>   eqp : p1 = p2
>   eqp = ?loji
> -}