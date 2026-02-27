module AdjProfunctor where

import Data.Profunctor
import Data.Profunctor.Monad
import Data.Prpfunctor.Adjunction

leftAdjunct ::
	( ProfunctorAdjunction f u
	, Profunctor p
	, Profunctor q) =>
	(f p :-> q) -> (p :-> u q) 
leftAdjunct f = promap f . unit

rightAdjunct :: 
	( ProfunctorAdjunction f u
	, Profunctor p
	, Profunctor q) =>
	(p :-> u q) -> (f p :-> q)
rightAdjunct f = counit . promap f

adjuncted :: 
	( ProfunctotAdjunction f u
	, Profunctor p, Profunctor d
	, Profunctor b, Functor g
	, Profunctor c, Profunctor s) =>
	p (d :-> u b) (g (c :-> u s)) ->
	p (f d :-> b) (g (f c :-> s))
adjuncted = bimap leftAdjunct (promap rightAdjunct)

tabulateAdjunction :: 
	( ProfunctorAdjunction f u
	, Profunctor p) =>
	(f (Forget ()) :-> p) -> u p
tabulateAdjunction f = 
	leftAdjunct f (Forget $ const ()) 

indexAdjunction :: 	
	( ProfunctorAdjunction f u
	, Profunctor p
	, Profunctor q ) =>
	u p -> f q -> p
indexAdjunction = rightAdjunct . const

zapWithAdjunction :: 
	( ProfunctorAdjunction f u
	, Profunctor a
	, Profunctor b
	, Profunctor c ) =>
	(a :-> (b :-> c)) -> u a -> f b -> c
zapWithAdjunction f ua = rightAdjunct 
	(\b-> promap (\a-> f a b) ua)

data ProMAdjointT f g m a = ProMAdjointT 
	{runProMAdjointT ::  
		( ProfunctorFunctor f
		, ProfunctorFunctor g
		, ProfunctorFunctor m
		, Profunctor a) =>
		g (m ( f a))
		}

instance ( ProfunctorFunctor f
	 , ProfunctorFunctor g
	 , ProfunctorFunctor m
	 ) => ProfunctorFunctor
	 	(ProMAdjointT f g m) where
	promap q (ProMAdjointT gmfa) =
		ProMAdjointT $ 
		promap (promap (promap q)) gmfa

instance () => ProfunctorMonad (ProMAdjointT f g m)
   

