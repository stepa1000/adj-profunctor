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

--ProMAdjointT m >>>= f = ProMAdjointT $ profmap (>>= rightAdjunct (runAdjointT . f)) m

instance ( ProfunctorFunctor f
	 , ProfunctorFunctor g
	 , ProfunctorFunctor m
	 , ProfunctorMonad m 
	 , ProfunctorAdjunction f u
	 ) => ProfunctorMonad (ProMAdjointT f g m) where
  proreturn = ProMAdjointT $ leftAdjunct proreturn 
  projoint (ProMAdjointT gmfgmfa) = promap (projoint . promap (counit . promap (runProMAdjointT) )) gmfgmfa 

(>>>=) :: ( ProfunctorFunctor f
	 , ProfunctorFunctor g
	 , ProfunctorFunctor m
	 , ProfunctorMonad m
	 ) => ProMAdjointT f g m a -> (a :-> ProMAdjointT f g m b) -> ProMAdjointT f g m b 
m >>>= f = projoint $ promap f m

data ProWAdjointT f g w a = ProWAdjointT 
	{runProWAdjointT ::
		( ProfunctorFunctor f
		, ProfunctorFunctor g
		, ProfunctorFunctor w
		, Profunctor a) => 
		f (w (g a))
	}

instance ( ProfunctorFunctor f
	 , ProfunctorFunctor g
	 , ProfunctorFunctor w
	 ) => ProfunctorFunctor
	 	(ProWAdjointT f g w) where
	promap q (ProWAdjointT gwfa) =
		ProMAdjointT $ 
		promap (promap (promap q)) gwfa

instance ( ProfunctorFunctor f
	 , ProfunctorFunctor g
	 , ProfunctorFunctor w
	 , ProfunctorComonad w
	 , ProfunctorAdjunction f u
	 ) => ProfunctorComonad (ProWAdjointT f g w) where
	proextend f (ProWAdjointT m) = ProWAdjointT $ profmap (proextend $ leftAdjunct (f . ProWAdjointT)) m


