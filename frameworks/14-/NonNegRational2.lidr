> module NonNegRational2

> import NatPredicates
> import NatProperties
> import Syntax.PreorderReasoning


> NonNegNat : Type
> NonNegNat = Nat

nicht gut, weil man keine Gleichheiten zeigen kann ...
< NonNegNat = (n : Nat ** Not (n = Z)) 

aber das sollte gehen und vermutlich deutlich einfacher als das hier 
mit Nat und Verschiebung

< NonNegNat2 : Type
< NonNegNat2 = (n : Nat ** (p : Nat ** n = S p))



> Fraction : Type
> Fraction = (Nat,NonNegNat)

> infixl 5 *^
> (*^) : Nat -> Nat -> Nat
> d *^ e = pred ((S d) * (S e))

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

> plusFractionCommutative : (x : Fraction) -> (y : Fraction) -> (x + y) = (y + x)
> plusFractionCommutative (n,d) (m,e) = 
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

> multFractionCommutative : (x : Fraction) -> (y : Fraction) -> (x * y) = (y * x)
> multFractionCommutative (n,d) (m,e) =
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

> plusZeroPlusRight : (x : Fraction) -> x + (fromInteger 0) = x
> plusZeroPlusRight (n, d) = pf where
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

> plusZeroPlusLeft : (x : Fraction) -> (fromInteger 0) + x = x
> plusZeroPlusLeft x = trans  (plusFractionCommutative (fromInteger 0) x) 
>                             (plusZeroPlusRight x)

> plusAssoc : (x, y, z : Fraction) -> x + (y + z) = (x + y) + z
> plusAssoc (n,d) (m,e) (l,f) = pf where
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


