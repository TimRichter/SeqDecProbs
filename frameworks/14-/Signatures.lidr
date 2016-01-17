> module Signatures
> import NFun


> Sig : Type
> Sig = Nat -> Type

> SigMor : (s, t : Sig) -> Type
> SigMor s t = {n : Nat} -> s n -> t n 

> SigAlg : Sig -> Type
> SigAlg s = Sigma Type (\ a => ({n : Nat} -> s n -> NOp n a))



