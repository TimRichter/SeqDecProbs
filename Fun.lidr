> module Fun


> import Data.Fin

> import NatProperties
> import FinOperations
> import FinProperties


> %default total


> ||| Injectivity
> Injective : {A, B : Type} -> (f : A -> B) -> Type
> Injective {A} f = (a1 : A) -> (a2 : A) -> f a1 = f a2 -> a1 = a2


> ||| Non injectivity, constructive
> NonInjective : {A, B : Type} -> (f : A -> B) -> Type
> NonInjective f = Exists (\ a1 => Exists (\ a2 => (Not (a1 = a2) , f a1 = f a2))) 


> ||| Surjectivity
> Surjective : {A, B : Type} -> (f : A -> B) -> Type
> Surjective {B} f = (b : B) -> Exists (\ a => f a = b) 


> ||| Non surjectivity, constructive
> NonSurjective : {A, B : Type} -> (f : A -> B) -> Type
> NonSurjective {A} f = Exists (\ b => (a : A) -> Not (f a = b)) 


Properties of constructive proofs

> ||| NonInjective => Not Injective
> nonInjectiveNotInjective : {A, B : Type} -> (f : A -> B) -> NonInjective f -> Not (Injective f)
> nonInjectiveNotInjective f (Evidence a1 (Evidence a2 (na1eqa2 , fa1eqfa2))) =
>   \ injectivef => na1eqa2 (injectivef a1 a2 fa1eqfa2)


> ||| NonSurjective => Not Surjective
> nonSurjectiveNotSurjective : {A, B : Type} -> (f : A -> B) -> NonSurjective f -> Not (Surjective f)
> nonSurjectiveNotSurjective f (Evidence b faanfab) =
>   \ surjectivef => let a = (getWitness (surjectivef b)) in (faanfab a) (getProof (surjectivef b))  



Pigeonhole principle

We want to prove that, for all |f : Fin n -> Fin m| with |n >= 2| and |m
< n| there exist |k, j : Fin n| with |Not (k = j)| and |f k = f j|:

> pigeonholeLemma : (n : Nat) -> (m : Nat) -> 
>                   (f : Fin (S (S n)) -> Fin m) ->  LT m (S (S n)) -> 
>                   NonInjective f

We can immediately prove the case |n = Z|

> pigeonholeLemma0 : (m : Nat) -> 
>                    (f : Fin (S (S Z)) -> Fin m) -> LT m (S (S Z)) -> 
>                    NonInjective f
> pigeonholeLemma0 Z f zLTssz = 
>   Evidence FZ (Evidence (FS FZ) (FZNotFS , (fin0Lemma (f FZ) (f (FS FZ)))))
> pigeonholeLemma0 (S Z) f szLTssz = 
>   Evidence FZ (Evidence (FS FZ) (FZNotFS , (fin1Lemma (f FZ) (f (FS FZ)))))
> pigeonholeLemma0 (S (S m)) f ssmLTssz = 
>   void (notLTzero (fromLteSucc (fromLteSucc (ssmLTssz))))

and we can prove an induction step

> pigeonholeStep : (n : Nat) -> (m : Nat) ->
>                  (f : Fin (S (S (S n))) -> Fin m) -> 
>                  NonInjective (tail f) -> NonInjective f
> pigeonholeStep n m f evi = 
>   Evidence (FS i) (Evidence (FS j) (sinesj , fsiefsj)) where
>     i       : Fin (S (S n))
>     i       = getWitness evi
>     j       : Fin (S (S n))
>     j       = getWitness (getProof evi)
>     sinesj  : Not (FS i = FS j)
>     sinesj  = fsInjective' i j (fst (getProof (getProof evi)))
>     fsiefsj : f (FS i) = f (FS j)
>     fsiefsj = tailSuccEqLemma i j f (snd (getProof (getProof evi)))

but in order to implement |pigeonholeLemma| we have to generalize the
case |n = Z| to

> pigeonholeBase : (n : Nat) -> (f : Fin (S (S n)) -> Fin (S n)) ->
>                  NonInjective f

With |pigeonholeBase| in place, implementing |pigeonholeLemma| is almost
straightforward:

< pigeonholeLemma : (n : Nat) -> (m : Nat) -> 
<                   (f : Fin (S (S n)) -> Fin m) ->  LT m (S (S n)) -> 
<                   NonInjective f

> pigeonholeLemma  Z      Z     f zLTssz = 
>   pigeonholeLemma0  Z     f zLTssz

> pigeonholeLemma  Z     (S m') f sm'LTssz = 
>   pigeonholeLemma0 (S m') f sm'LTssz

> pigeonholeLemma (S n')  Z f      _ = 
>   let ih = pigeonholeLemma n' Z (tail f) (ltZS (S n')) in
>   pigeonholeStep n' Z f ih

> pigeonholeLemma (S n') (S m') f sm'LTsssn' with (decEq (S m') (S (S n')))
>   pigeonholeLemma (S n') (S (S n')) f sm'LTsssn' | (Yes Refl) = 
>     pigeonholeBase (S n') f
>   pigeonholeLemma (S n') (S m')     f sm'LTsssn' | (No sm'NEQssn') =
>     let sm'LTssn' = strengthenLT (S m') (S (S n')) sm'LTsssn' sm'NEQssn' in
>     let ih = pigeonholeLemma n' (S m') (tail f) sm'LTssn' in
>     pigeonholeStep n' (S m') f ih

Thus the question is whether we can implement |pigeonholeBase|. If we have

> finEndoLemma : (n : Nat) -> (f : Fin n -> Fin n) -> Either (Surjective f) (NonInjective f)

then implementing |pigeonholeBase| is easy:

< pigeonholeBase : (n : Nat) -> (f : Fin (S (S n)) -> Fin (S n)) ->
<                  NonInjective f

> pigeonholeBase  Z    f = pigeonholeLemma0 (S Z) f (LTESucc (LTESucc LTEZero))

> pigeonholeBase (S n) f with (finEndoLemma (S (S n)) (tail f))
>   | (Left surjectivef) = Evidence FZ (Evidence (FS j) (lnesj , flefsj)) where
>     j      : Fin (S (S n))
>     j      = getWitness (surjectivef (f FZ))
>     p      : (tail f) j = f FZ
>     p      = getProof (surjectivef (f FZ))
>     lnesj  : Not (FZ = FS j)
>     lnesj  = FZNotFS 
>     flefsj : f FZ = f (FS j)
>     flefsj = sym p
>   | (Right evi) = pigeonholeStep n (S (S n)) f evi     

Thus the question is whether we can implement |finEndoLemma|. This is
going to be "Knochenarbeit", but it is a more fundamental result than
the pigeonhole lemma, I think.
