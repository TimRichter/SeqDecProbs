> module NonNegRational2

 import NatPredicates

> import NatDivisor
> import NatGCD
> import NatOperations
> import NatProperties
> import Syntax.PreorderReasoning
> import SplitQuotient
> import KernelQuotient

> %default total

> PosNat : Type

Cannot use this, since it involves the function type
|Not (n = Z)| and (without function extensionality) it 
usually will be impossible to prove equalities:

< PosNat = (n : Nat ** Not (n = Z)) 

try here the alternative

define Positivity

> data Positive : Nat -> Type where
>   SuccPos : {n : Nat} -> Positive (S n)

positivity is closed under multiplication

> multPosPosIsPos : (m, n : Nat) -> 
>                   Positive m -> 
>                   Positive n ->
>                   Positive (m * n)
> multPosPosIsPos Z n SuccPos _       impossible
> multPosPosIsPos m Z _       SuccPos impossible
> multPosPosIsPos (S n) (S m) _ _ = SuccPos


> PosNat = Subset Nat Positive

> Fraction : Type
> Fraction = (Nat,PosNat)

> nat : PosNat -> Nat
> nat = getWitness

Helper operation for the denominators

PosNat is closed under multiplication

> infixl 5 *^
> (*^) : PosNat -> PosNat -> PosNat
> (Element d dPos) *^ (Element e ePos) = Element (d * e) (multPosPosIsPos d e dPos ePos)
   
Operations and Num instance

> plusFraction : Fraction -> Fraction -> Fraction
> plusFraction (n, d) (m, e) =
>   (n * (nat e) + m * (nat d), d *^ e )

> minusFraction : Fraction -> Fraction -> Fraction
> minusFraction (n, d) (m, e) =
>   (n * (nat e) - m * (nat d), d *^ e)

> multFraction : Fraction -> Fraction -> Fraction
> multFraction (n, d) (m, e) = (n * m, d *^ e)

> fromIntegerFraction : Integer -> Fraction
> fromIntegerFraction i = (fromInteger i, Element (S Z) SuccPos)

> instance Num Fraction where
>   (+) = plusFraction
>   --(-) = minusFraction
>   (*) = multFraction
>   --abs = id
>   fromInteger = fromIntegerFraction

Properties of *^

> multUpCommutative: (d, e : PosNat) -> d *^ e = e *^ d
> multUpCommutative (Element d dPos) (Element e ePos) = 
>   (Element (d * e) SuccPos)
>     ={ cong {f = \x => (Element x SuccPos)} (multCommutative d e) }=
>   (Element (e * d) SuccPos)
>     QED

> multUpAssoc : (d, e, f : Nat) -> d *^ (e *^ f) = (d *^ e) *^ f
> multUpAssoc d e f = succInjective _ _ pf where
>   pf : S (d *^ (e *^ f)) = S ((d *^ e) *^ f)
>   pf = multAssociative (S d) (S e) (S f)

> multUpZeroRightNeutral : (d : Nat) -> d *^ Z = d
> multUpZeroRightNeutral d = succInjective _ _ pf where
>   pf : S (d *^ Z) = (S d)
>   pf = multOneRightNeutral (S d)

Properties of Fraction operations

first those that prove equalities:

> plusFCommutative : (x : Fraction) -> (y : Fraction) -> (x + y) = (y + x)
> plusFCommutative (n,d) (m,e) = 
>     ((n, d) + (m, e))
>     ={ cong {f = \k => (k, d *^ e) } (plusCommutative (n * (S e)) (m * (S d))) }=
>     (m * (S d) + n * (S e), d *^ e)
>     ={ cong {f = \k => (m * (S d) + n * (S e), k)} (multUpCommutative d e)}=
>     ((m, e) + (n, d))
>     QED

> multFCommutative : (x : Fraction) -> (y : Fraction) -> (x * y) = (y * x)
> multFCommutative (n,d) (m,e) =
>     ((n,d) * (m,e))
>     ={ cong {f = \k => (k, d *^ e)} (multCommutative n m) }=
>     (m * n, d *^ e)
>     ={ cong {f = \k => (m * n, k)} (multUpCommutative d e) }=
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
>     ((n * S e + m * S d) * S f + l * S (d *^ e))
>     QED
>
>   pf =          
>     ((n,d) + ((m,e) + (l,f)))
>     ={ cong {f = \k => (k, d *^ (e *^ f))} numEq }= 
>     ((n * S e + m * S d) * S f + l * S (d *^ e), d *^ (e *^ f))
>     ={ cong {f = \k => ((n * S e + m * S d) * S f + l * S (d *^ e), k)}
>         (multUpAssoc d e f) }=
>     (((n,d) + (m,e)) + (l,f))
>     QED

> multFOneRightNeutral : (x : Fraction) -> x * 1 = x
> multFOneRightNeutral (n,d) =
>   ((n,d) * (1,0))
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
> FR (n,d) (m,e) = n * (S e) = m * (S d)

> syntax  [x] "~" [y] = FR x y

> reflexiveFR : (x : Fraction) -> x ~ x
> reflexiveFR (n,d) = Refl

> reflexiveFR' : (x, y : Fraction) -> x = y -> x ~ y
> reflexiveFR' x x Refl = reflexiveFR x

> symmetricFR : (x, y : Fraction) -> (x ~ y) -> (y ~ x)
> symmetricFR (n,d) (m,e) ndFRme = sym ndFRme


for transitivity we need that multiplication by a positive number is
injective. This should be provable as (cong { f = quotient... } SdnIsSdm) or 
something like that

> multNonZeroLeftInjective : (n, m, d : Nat) -> (S d) * n = (S d) * m -> n = m

> transitiveFR : (x, y, z : Fraction) -> (x ~ y) -> (y ~ z) -> (x ~ z)
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

> multFZeroRightZero : (x : Fraction) -> (x * 0) ~ 0
> multFZeroRightZero (n,d) =
>     (n * 0 * (S 0))
>     ={ cong {f = \k => k * S 0} (multZeroRightZero n) }=
>     (0 * (S 0))
>     ={ multZeroLeftZero (S 0) }=
>     0
>     ={ sym (multZeroLeftZero (S (0 *^ 0))) }=
>     (0 * S (d *^ 0))
>     QED

> multFZeroLeftZero : (x : Fraction) -> (0 * x) ~ 0
> multFZeroLeftZero x = 
>   transitiveFR (0 * x) (x * 0) 0 rel (multFZeroRightZero x) where
>   rel : 0 * x =/= x * 0
>   rel = reflexiveFR' (0 * x) (x * 0) (multFCommutative 0 x)

> multFDistributesOverPlusRight : (x,y,z : Fraction) -> 
>                                 (x * (y + z)) ~ ((x * y) + (x * z))
>
> multFDistributesOverPlusRight (n,d) (m,e) (l,f) = pf where
>   pf1 : S (d *^ e) * S (d *^ f) = S d * S (d *^ (e *^ f))
>   pf1 =
>     (S (d *^ e) * S (d *^ f))
>     ={ sym (multAssociative (S d) (S e) (S d * S f)) }=
>     (S d * (S e * (S d * S f)))
>     ={ cong {f = \k => S d * k} (multAssociative (S e) (S d) (S f)) }=
>     (S d * (S e * S d * S f))
>     ={ cong {f = \k => S d * ( k * S f)} (multCommutative (S e) (S d)) }=
>     (S d * (S d * S e * S f))
>     ={ cong {f = \k => S d * k} (sym (multAssociative (S d) (S e) (S f))) }=
>     (S d * S (d *^ (e *^ f)))
>     QED
>   pf2' : (w,x,y,z : Nat) -> w * (x * S y) * S z = w * x * S (z *^ y)
>   pf2' w x y z =
>     (w * (x * S y) * S z)
>     ={ cong {f = \k => k * S z} (multAssociative w x (S y)) }=
>     (w * x * S y * S z)
>     ={ sym (multAssociative (w * x) (S y) (S z)) }=
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


> multFDistributesOverPlusLeft :  (x,y,z : Fraction) -> 
>                                 ((x + y) * z) ~ ((x * z) + (y * z))
>
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

> syntax [d] "|" [m] = NatDivisor.Divisor d m

> syntax [m] "/" [dDm] "/" [d] = quotient m d dDm


a divisor of (S n) is an S _ 

> divPosPos : (n, m : Nat) -> (n | (S m)) -> 
>                 ( p : Nat ** n = S p )
> divPosPos Z m nDivSm = 
>   absurd (ZnotS zIsS) where
>   zIsS : 0 = S m
>   zIsS = getProof nDivSm
> divPosPos (S p) _ _ = (p ** Refl)

> divByPosPos : (n, m : Nat) -> (nDSm : (n | (S m))) ->
>               (p : Nat ** ((S m) /nDSm/ n) = S p)
> divByPosPos n m (Evidence q nqIsSm) =
>   divPosPos q m (Evidence n qnIsSm) where
>     qnIsSm : q * n = S m
>     qnIsSm = trans (multCommutative q n) nqIsSm


> gcdPosPos : (g, m, n : Nat) -> GCD g m (S n) -> (p : Nat ** g = S p)
> gcdPosPos g m n (MkGCD _ gDivSn _) = divPosPos g n gDivSn


> toLowest : Fraction -> Fraction
> toLowest (n,d) = (n',d') where
>   gcd : (g : Nat ** GCD g n (S d))
>   gcd = euclidGCD n (S d)
>   g   : Nat
>   g   = getWitness gcd
>   gIsGCD : GCD g n (S d)
>   gIsGCD = getProof gcd
>   n'  : Nat
>   n'  = n /(gcdDivisorFst gIsGCD)/ g
>   d'  : Nat
>   d'  = getWitness (divByPosPos g d (gcdDivisorSnd gIsGCD))
>   

we need

> toLowestIdem : (x : Fraction) -> toLowest (toLowest x) = toLowest x

> tlEndo : IdempotentEndo Fraction
> tlEndo = ( toLowest ** toLowestIdem )

> data NonNegQ2 : Type where
>   MkNonNegQ2 : SQuot tlEndo -> NonNegQ2

> unwrap : NonNegQ2 -> SQuot tlEndo
> unwrap (MkNonNegQ2 x) = x


and an Iso:

> fRToKerTL : {x, y : Fraction} -> FR x y -> toLowest x = toLowest y

> fRFromKerTL : {x, y : Fraction} -> toLowest x = toLowest y -> x ~ y 


> plus : NonNegQ2 -> NonNegQ2 -> NonNegQ2
> plus x y = 
>   MkNonNegQ2 ((liftQBinop tlEndo plusFraction) (unwrap x) (unwrap y))


> mult : NonNegQ2 -> NonNegQ2 -> NonNegQ2
> mult x y = 
>   MkNonNegQ2 ((liftQBinop tlEndo multFraction) (unwrap x) (unwrap y))


> minus : NonNegQ2 -> NonNegQ2 -> NonNegQ2
> minus x y = 
>   MkNonNegQ2 ((liftQBinop tlEndo minusFraction) (unwrap x) (unwrap y))


> fromIntegerQ : Integer -> NonNegQ2
> fromIntegerQ = MkNonNegQ2 . (can tlEndo) . fromIntegerFraction


> instance Num NonNegQ2 where
>   (+) = plus
>   (-) = minus
>   (*) = mult
>   fromInteger = fromIntegerQ
>   abs = id

--- how to circumvent the type class "injectivity" issue...?

> NonNegQ3 : Type
> NonNegQ3 = SQuot tlEndo

> instance [nonnegq3] Num NonNegQ3  where
>   (+) = liftQBinop tlEndo (+)
>   (*) = liftQBinop tlEndo (*)
>   (-) = liftQBinop tlEndo (-)
>   fromInteger = (can tlEndo) . fromInteger
>   abs = id



> plusInvariant : (left1, left2, right1, right2 : Fraction) -> 
>                 (left1  ~ left2 ) -> 
>                 (right1 ~ right2) -> 
>                 (left1 + right1) ~ (left2 + right2)

 plusInvariant (n,d) (m,e) (l,f) (k,g) nSfIslSd mSgIskSe = 
   ((n * S f + l * S d) * (S e * S g))
   ={ multDistributesOverPlusLeft }=


 gugu : (x : NonNegQ2) -> x + 0 = x
 gugu x =
  (x + 0) 
   ={ Refl }=
  (MkNonNegQ2 ((liftQBinop tlEndo plusFraction) (unwrap x) (unwrap 0)))
   ={ 



 gugu (MkNonNegQ2 x) = cong {f = MkNonNegQ2} pf where
   pf : x  0


-------- more lemmata 


> multCancelLeft : (d, m, n : Nat) ->
>                  (S d) * m = (S d) * n ->
>                   m = n

> divByDivisorLemma : (d, m, n : Nat) -> (m | n) -> 
>                     (dDm : ((S d) | m)) -> (dDn : ((S d) | n)) ->
>                     (m /dDm/ (S d)) | (n /dDn/ (S d))
> divByDivisorLemma d m n (Evidence k mkIsn) 
>                         (Evidence r sdrIsm) 
>                         (Evidence t sdtIsn) =
>       Evidence k rkIst where
>   sdrkIsSdk : S d * (r * k) = S d * t
>   sdrkIsSdk =
>     (S d * (r * k)) ={ multAssociative (S d) r k }=
>     (S d * r * k)   ={ cong {f = \x => x * k} sdrIsm }=
>     (m * k)         ={ mkIsn }=
>     n               ={ sym sdtIsn }=
>     (S d * t)       QED
>                    
>   rkIst : r * k = t
>   rkIst = multCancelLeft d (r * k) t sdrkIsSdk
>   

> gcdProdLemma :  (alg : (a : Nat) -> (b : Nat) -> (d : Nat ** GCD d a b)) ->
>                 (m, n, l : Nat) ->
>                 gcd (alg (m * n) (m * l)) = m * gcd (alg n l)
>
> gcdProdLemma alg Z n l = gcdUnique (gcd (alg Z Z)) 0 (getProof (alg Z Z)) gcdZZZ where
>   gcdZZZ : GCD 0 0 0
>   gcdZZZ = mkGCD (anyDivisorZ 0) (anyDivisorZ 0) (\d => \x => \y => anyDivisorZ d) 
> gcdProdLemma alg (S m) n l = pf where
>   mDmn : (m | (m * n))
>   mDmn = Evidence n Refl
>   mDml : (m | (m * l))
>   mDml = Evidence l Refl
>   pf = ?lilo

Informal:
   - Seien gmnml = gcd m*n m*l und gnl = gcd n l
   - m | m*n und m | m*l => m | gmnml
   - Sei  g = (gcd m*n m*l) / m, z.z. ist g = gnl
   - gmnml | m*n, m | gmnml und m | m*n
      =>  (gmnml / m) | ((m * n) / m)  (divByDivisorLemma)
      i.e. g | n
   - analog g | l
   - Sei d gemeinsamer Teiler von n und l
     d | n , d | l =>
     m*d | m*n, m*d | m * l =>
     m*d | gmnml  => (m | m*d und m | gmnml, Lemma nochmal)
     d | g















