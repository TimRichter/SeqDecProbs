> module NonNegRational2

> import NatPredicates
> import NatOperations
> import NatProperties
> import Syntax.PreorderReasoning
> import GCD


> PosNat : Type

Cannot use this, since it involves the function type
|Not (n = Z)| and (without function extensionality) it 
usually will be impossible to prove equalities:

< PosNat = (n : Nat ** Not (n = Z)) 

this should work (a lot?) easier than what follows below:

< PosNat2 : Type
< PosNat2 = (n : Nat ** (p : Nat ** n = S p))

But for now

> PosNat = Nat

we represent the nonnegative fraction (n,S d) by
the pair (n,d)

> Fraction : Type
> Fraction = (Nat,PosNat)

Helper operation for the denominators

> infixl 5 *^
> (*^) : Nat -> Nat -> Nat
> d *^ e = pred ((S d) * (S e))

Operations and Num instance

> plusFraction : Fraction -> Fraction -> Fraction
> plusFraction (n, d) (m, e) =
>   (n * (S e) + m * (S d), d *^ e )

> minusFraction : Fraction -> Fraction -> Fraction
> minusFraction (n, d) (m, e) =
>   (n * (S e) - m * (S d), d *^ e)

> multFraction : Fraction -> Fraction -> Fraction
> multFraction (n, d) (m, e) = (n * m, d *^ e)

> fromIntegerFraction : Integer -> Fraction
> fromIntegerFraction i = (fromInteger i, Z)

> instance Num Fraction where
>   (+) = plusFraction
>   (-) = minusFraction
>   (*) = multFraction
>   abs = id
>   fromInteger = fromIntegerFraction

Properties of *^

> multUpLemma : (d, e : Nat) -> S (d *^ e) = (S d) * (S e)
> multUpLemma d e = Refl

> multUpCommutative: (d, e : Nat) -> d *^ e = e *^ d
> multUpCommutative d e = succInjective _ _ pf where
>   pf : S (d *^ e) = S (e *^ d)
>   pf =
>     (S (d *^ e))
>     ={ multUpLemma d e }=
>     ((S d) * (S e))
>     ={ multCommutative (S d) (S e) }=
>     ((S e) * (S d))
>     ={ sym (multUpLemma e d) }=
>     (S (e *^ d))
>     QED

> multUpAssoc : (d, e, f : Nat) -> d *^ (e *^ f) = (d *^ e) *^ f
> multUpAssoc d e f = succInjective _ _ pf where
>   pf : S (d *^ (e *^ f)) = S ((d *^ e) *^ f)
>   pf =
>     (S (d *^ (e *^ f)))
>     ={ multUpLemma d (e *^ f) }=
>     ((S d) * (S (e *^ f)))
>     ={ cong {f = \k => (S d) * k} (multUpLemma e f) }=
>     ((S d) * ((S e) * (S f)))
>     ={ multAssociative (S d) (S e) (S f) }=
>     (((S d) * (S e)) * (S f))
>     ={ cong {f = \k => k * (S f)} (sym (multUpLemma d e)) }=
>     ((S (d *^ e)) * (S f))
>     ={ sym (multUpLemma (d *^ e) f) }=
>     (S ((d *^ e) *^ f))
>     QED

> multUpZeroRightNeutral : (d : Nat) -> d *^ Z = d
> multUpZeroRightNeutral d = succInjective _ _ pf where
>   pf : S (d *^ Z) = (S d)
>   pf = 
>     (S (d *^ Z))
>     ={ multUpLemma d Z }=
>     ((S d) * (S Z))
>     ={ multOneRightNeutral (S d) }=
>     (S d)
>     QED

Properties of Fraction operations

> plusFCommutative : (x : Fraction) -> (y : Fraction) -> (x + y) = (y + x)
> plusFCommutative (n,d) (m,e) = 
>     ((n, d) + (m, e))
>     ={ Refl }=
>     (n * (S e) + m * (S d), d *^ e)
>     ={ cong {f = \k => (k, d *^ e) } (plusCommutative (n * (S e)) (m * (S d))) }=
>     (m * (S d) + n * (S e), d *^ e)
>     ={ cong {f = \k => (m * (S d) + n * (S e), k)} (multUpCommutative d e)}=
>     (m * (S d) + n * (S e), e *^ d)
>     ={ Refl }=
>     ((m, e) + (n, d))
>     QED

> multFCommutative : (x : Fraction) -> (y : Fraction) -> (x * y) = (y * x)
> multFCommutative (n,d) (m,e) =
>     ((n,d) * (m,e))
>     ={ Refl }=
>     (n * m, d *^ e)
>     ={ cong {f = \k => (k, d *^ e)} (multCommutative n m) }=
>     (m * n, d *^ e)
>     ={ cong {f = \k => (m * n, k)} (multUpCommutative d e) }=
>     (m * n, e *^ d)
>     ={ Refl }=
>     ((m, e) * (n, d))
>     QED

> plusFZeroRightNeutral : (x : Fraction) -> x + (fromInteger 0) = x
> plusFZeroRightNeutral (n, d) = pf where
>   numEq : n * (S Z) + Z * (S d) = n
>   numEq =
>     (n * (S Z) + Z * (S d))  
>     ={ cong {f = \m => n * (S Z) + m} (multZeroLeftZero (S d)) }=
>     (n * (S Z) + Z)
>     ={ plusZeroRightNeutral (n * (S Z)) }=
>     (n * (S Z))
>     ={ multOneRightNeutral n }=
>     n   QED
>
>   pf =
>     ((n, d) + (Z, Z))               
>     ={ Refl }=
>     (n * (S Z) + Z * (S d), d *^ Z) 
>     ={ cong {f = \m => (m, d *^ Z)} numEq }=
>     (n, d *^ Z)                     
>     ={ cong {f = \m => (n, m)} (multUpZeroRightNeutral d) }=
>     (n, d)  QED

> plusFZeroLeftNeutral : (x : Fraction) -> (fromInteger 0) + x = x
> plusFZeroLeftNeutral x = trans  (plusFCommutative (fromInteger 0) x) 
>                             (plusFZeroRightNeutral x)

> plusFAssociative : (x, y, z : Fraction) -> x + (y + z) = (x + y) + z
> plusFAssociative (n,d) (m,e) (l,f) = pf where
>   multComm' : (a, b, c : Nat) -> a * b * c = a * (c * b)
>   multComm' a b c =
>     (a * b * c)    ={ sym (multAssociative a b c) }=
>     (a * (b * c))  ={ cong {f = \k => a * k} (multCommutative b c) }=
>     (a * (c * b))  QED
>   multComm'' : (a, b, c : Nat) -> a * b * c = a * c * b
>   multComm'' a b c = trans (multComm' a b c) (multAssociative a c b)
>   numEq :  n * S (e *^ f) + (m * S f + l * S e) * S d = 
>           (n * S e + m * S d) * S f + l * S (d *^ e)
>   numEq =
>     (n * S (e *^ f) + (m * S f + l * S e) * S d)
>     ={ cong {f = \k => n * k + (m * S f + l * S e) * S d } 
>       (multUpLemma e f)}=
>     (n * (S e * S f) + (m * S f + l * S e) * S d)
>     ={ cong {f = \k => k + (m * S f + l * S e) * S d}
>       (multAssociative n (S e) (S f)) }=
>     (n * S e * S f + (m * S f + l * S e) * S d)
>     ={ cong {f = \k => n * S e * S f + k} 
>       (multDistributesOverPlusLeft (m * S f) (l * S e) (S d)) }=
>     (n * S e * S f + (m * S f * S d + l * S e * S d))
>     ={ plusAssociative (n * S e * S f) (m * S f * S d) (l * S e * S d) }=
>     (n * S e * S f + m * S f * S d + l * S e * S d)
>     ={ cong {f = \k => n * S e * S f + k + l * S e * S d}
>       (multComm'' m (S f) (S d)) }=
>     (n * S e * S f + m * S d * S f + l * S e * S d)
>     ={ cong {f = \k => k + l * S e * S d} 
>       (sym (multDistributesOverPlusLeft (n * S e) (m * S d) (S f))) }=
>     ((n * S e + m * S d) * S f + l * S e * S d)
>     ={ cong {f = \k => (n * S e + m * S d) * S f + k} 
>       (multComm' l (S e) (S d)) }=
>     ((n * S e + m * S d) * S f + l * (S d * S e))
>     ={ cong {f = \k => (n * S e + m * S d) * S f + l * k}
>       (sym (multUpLemma d e)) }=
>     ((n * S e + m * S d) * S f + l * S (d *^ e))
>     QED
>
>   pf =          
>     ((n,d) + ((m,e) + (l,f)))
>     ={ Refl }=
>     ((n,d) + (m * S f + l * S e, e *^ f))
>     ={ Refl }=
>     (n * S (e *^ f) + (m * S f + l * S e) * S d, d *^ (e *^ f))
>     ={ cong {f = \k => (k, d *^ (e *^ f))} numEq }= 
>     ((n * S e + m * S d) * S f + l * S (d *^ e), d *^ (e *^ f))
>     ={ cong {f = \k => ((n * S e + m * S d) * S f + l * S (d *^ e), k)}
>         (multUpAssoc d e f) }=
>     ((n * S e + m * S d) * S f + l * S (d *^ e), (d *^ e) *^ f)
>     ={ Refl }=
>     (((n,d) + (m,e)) + (l,f))
>     QED

> multFOneRightNeutral : (x : Fraction) -> x * 1 = x
> multFOneRightNeutral (n,d) =
>   ((n,d) * (1,0))
>   ={ Refl }=
>   (n * (S Z), d *^ 0)
>   ={ cong {f = \k => (n * (S 0), k)} (multUpZeroRightNeutral d) }= 
>   (n * (S Z), d)
>   ={ cong {f = \k => (k, d)} (multOneRightNeutral n) }=
>   (n, d)
>   QED

> multFOneLeftNeutral : (x : Fraction) -> 1 * x = x
> multFOneLeftNeutral x = trans (multFCommutative 1 x) (multFOneRightNeutral x)

Rational numbers will be a quotient of Fractions by the equivalence relation

> infixl 5 =/=
> (=/=) : Fraction -> Fraction -> Type
> (n,d) =/= (m,e) = n * (S e) = m * (S d)

to append to properties, we call this Relation FR

> FR : Fraction -> Fraction -> Type
> FR x y = x =/= y

> reflexiveFR : (x : Fraction) -> x =/= x
> reflexiveFR (n,d) = Refl

> reflexiveFR' : (x, y : Fraction) -> x = y -> x =/= y
> reflexiveFR' x x Refl = reflexiveFR x

> symmetricFR : (x, y : Fraction) -> (x =/= y) -> (y =/= x)
> symmetricFR (n,d) (m,e) ndFRme = sym ndFRme


for transitivity we need that multiplication by a positive number is
injective. This should be provable as (cong { f = divBy... } SdnIsSdm) or 
something like that

> multNonZeroLeftInjective : (n, m, d : Nat) -> (S d) * n = (S d) * m -> n = m

> transitiveFR : (x, y, z : Fraction) -> x =/= y -> y =/= z -> x =/= z
> transitiveFR (n,d) (m,e) (l,f) nSeIsmSd mSfIslSe = 
>   multNonZeroLeftInjective (n * (S f)) (l * (S d)) e pf where
>   pf : S e * (n * S f) = S e * (l * (S d))
>   pf =
>     (S e * (n * S f))
>     ={ multAssociative (S e) n (S f) }=
>     (S e * n * S f)
>     ={ cong {f = \k => k * S f} (multCommutative (S e) n) }=
>     (n * S e * S f)
>     ={ cong {f = \k => k * S f} nSeIsmSd }=
>     (m * S d * S f)
>     ={ sym (multAssociative m (S d) (S f)) }=
>     (m * (S d * S f))
>     ={ cong {f =\k => m * k} (multCommutative (S d) (S f)) }=
>     (m * (S f * S d))
>     ={ multAssociative m (S f) (S d) }=
>     (m * S f * S d)
>     ={ cong {f =\k => k * S d} mSfIslSe }=
>     (l * S e * S d)
>     ={ cong {f = \k => k * S d} (multCommutative l (S e))}=
>     (S e * l * S d)
>     ={ sym (multAssociative (S e) l (S d)) }=
>     (S e * (l * (S d)))
>     QED

> multFZeroRightZero : (x : Fraction) -> x * 0 =/= 0
> multFZeroRightZero (n,d) =
>     (n * 0 * (S 0))
>     ={ cong {f = \k => k * S 0} (multZeroRightZero n) }=
>     (0 * (S 0))
>     ={ multZeroLeftZero (S 0) }=
>     0
>     ={ sym (multZeroLeftZero (S (0 *^ 0))) }=
>     (0 * S (d *^ 0))
>     QED

> multFZeroLeftZero : (x : Fraction) -> 0 * x =/= 0
> multFZeroLeftZero x = 
>   transitiveFR (0 * x) (x * 0) 0 rel (multFZeroRightZero x) where
>   rel : 0 * x =/= x * 0
>   rel = reflexiveFR' (0 * x) (x * 0) (multFCommutative 0 x)

> multFDistributesOverPlusRight : (x,y,z : Fraction) -> 
>                                 x * (y + z) =/= (x * y) + (x * z)
> multFDistributesOverPlusRight (n,d) (m,e) (l,f) = pf where
>   pf1 : S (d *^ e) * S (d *^ f) = S d * S (d *^ (e *^ f))
>   pf1 =
>     (S (d *^ e) * S (d *^ f))
>     ={ Refl }=
>     ((S d * S e) * (S d * S f))
>     ={ sym (multAssociative (S d) (S e) (S d * S f)) }=
>     (S d * (S e * (S d * S f)))
>     ={ cong {f = \k => S d * k} (multAssociative (S e) (S d) (S f)) }=
>     (S d * (S e * S d * S f))
>     ={ cong {f = \k => S d * ( k * S f)} (multCommutative (S e) (S d)) }=
>     (S d * (S d * S e * S f))
>     ={ cong {f = \k => S d * k} (sym (multAssociative (S d) (S e) (S f))) }=
>     (S d * (S d * (S e * S f)))
>     ={ Refl }=
>     (S d * S (d *^ (e *^ f)))
>     QED
>   pf2' : (w,x,y,z : Nat) -> w * (x * S y) * S z = w * x * S (z *^ y)
>   pf2' w x y z =
>     (w * (x * S y) * S z)
>     ={ cong {f = \k => k * S z} (multAssociative w x (S y)) }=
>     (w * x * S y * S z)
>     ={ sym (multAssociative (w * x) (S y) (S z)) }=
>     (w * x * (S y * S z))
>     ={ Refl }=
>     (w * x * S (y *^ z))
>     ={ cong {f =  \k => w * x * S k} (multUpCommutative y z) }=
>     (w * x * S (z *^ y))
>     QED
>   pf2 : (n * (m * S f) + n * (l * S e)) * S d =
>         n * m * S (d *^ f) + n * l * S (d *^ e)
>   pf2 =
>     ((n * (m * S f) + n * (l * S e)) * S d)
>     ={ multDistributesOverPlusLeft _ _ _ }=
>     (n * (m * S f) * S d + n * (l * S e) * S d)
>     ={ cong {f = \k => n * (m * S f) * S d + k} (pf2' n l e d)}=
>     (n * (m * S f) * S d + n * l * S (d *^ e))
>     ={ cong {f = \k => k + n * l * S (d *^ e)} (pf2' n m f d) }=
>     (n * m * S (d *^ f) + n * l * S (d *^ e))
>     QED
>   pf =
>     (n * (m * S f + l * S e) * S ((d *^ e) *^ (d *^ f)))
>     ={ cong {f = \k => n * (m * S f + l * S e) * k} 
>       (multUpLemma (d *^ e) (d *^ f)) }=
>     (n * (m * S f + l * S e) * (S (d *^ e) * S (d *^ f)))
>     ={ cong {f = \k => k * (S (d *^ e) * S (d *^ f)) } 
>       (multDistributesOverPlusRight n (m * S f) (l * S e)) }=
>     ((n * (m * S f) + n * (l * S e)) * (S (d *^ e) * S (d *^ f))) 
>     ={ cong {f = \k => (n * (m * S f) + n * (l * S e)) * k} pf1 }=
>     ((n * (m * S f) + n * (l * S e)) * (S d * S (d *^ (e *^ f))))
>     ={ (multAssociative (n * (m * S f) + n * (l * S e)) (S d) _ ) }=
>     ((n * (m * S f) + n * (l * S e)) * S d * S (d *^ (e *^ f)))
>     ={ cong {f = \k => k * S (d *^ (e *^ f))} pf2 }=
>     ((n * m * S (d *^ f) + n * l * S (d *^ e)) * S (d *^ (e *^ f)))
>     QED


> multFDistributesOverPlusLeft : (x,y,z : Fraction) -> 
>                                 (x + y) * z =/= (x * z) + (y * z)
> multFDistributesOverPlusLeft x y z = 
>   transitiveFR ((x + y) * z) (z * x + z * y) (x * z + y * z) 
>     (transitiveFR ((x + y) * z) (z * (x + y)) (z * x + z * y)     
>       (reflexiveFR' ((x + y) * z) (z * (x + y)) (multFCommutative (x + y) z)) 
>       (multFDistributesOverPlusRight z x y))
>     (reflexiveFR' (z * x + z * y) (x * z + y * z) pf) where
>   pf : z * x + z * y = x * z + y * z
>   pf =
>     (z * x + z * y)
>     ={ cong {f = \k => z * x + k} (multFCommutative z y) }=
>     (z * x + y * z)
>     ={ cong {f = \k => k + y * z} (multFCommutative z x) }=
>     (x * z + y * z)
>     QED
>   

------------------------------------------------------

and now for the quotient

lemmata 

> notZIsS : (n : Nat) -> Not (n = 0) -> (p : Nat ** n = S p)
> notZIsS Z     pf = absurd (pf Refl)
> notZIsS (S p) _  = ( p ** Refl)


a divisor of (S n) is an S _ 

> divPosPos : (n, m : Nat) -> n `Divisor` (S m) -> 
>                 ( p : Nat ** n = S p )
> divPosPos Z m nDivSm = 
>   absurd (ZnotS zIsS) where
>   zIsS : 0 = S m
>   zIsS = getProof nDivSm
> divPosPos (S p) _ _ = (p ** Refl)

> divByPosPos : (n, m : Nat) -> (nDivSm : n `Divisor` (S m)) ->
>               (p : Nat ** (divBy n (S m) nDivSm) = S p)
> divByPosPos n m (Evidence q nqIsSm) =
>   divPosPos q m (Evidence n qnIsSm) where
>     qnIsSm : q * n = S m
>     qnIsSm = trans (multCommutative q n) nqIsSm

> gcdPosPos : (g, m, n : Nat) -> GCD g m (S n) -> (p : Nat ** g = S p)
> gcdPosPos g m n (mkGCD _ gDivSn _) = divPosPos g n gDivSn


> toLowest : Fraction -> Fraction
> toLowest (n,d) = (n',d') where
>   gcd : (g : Nat ** GCD g n (S d))
>   gcd = euclidGCD n (S d)
>   g   : Nat
>   g   = getWitness gcd
>   gIsGCD : GCD g n (S d)
>   gIsGCD = getProof gcd
>   n'  : Nat
>   n'  = divBy g n (gcdDivisorFst gIsGCD)
>   d'  : Nat
>   d'  = getWitness (divByPosPos g d (gcdDivisorSnd gIsGCD))
>   


and we need

> tLowestIdem : (x : Fraction) -> toLowest (toLowest x) = toLowest x














