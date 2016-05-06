{-# LANGUAGE GeneralizedNewtypeDeriving, ParallelListComp #-}
module LS_Operators
	where

import LS_Frobenius

data VertexOperator k = P Int k | L Int k | Del | Ch Int k | GV Int k | ChT Int deriving (Show,Eq,Ord)

newtype State a k = Vak { unVak:: [([VertexOperator k],a)] }

weight (P n _) = -n
weight (L n _) = -n
weight Del = 0
weight (Ch _ _) = 0
weight (GV _ _) = 0
weight (ChT _) = 0

degree (P n k) = gfa_deg k
degree (L n k) = gfa_deg k + gfa_d
degree Del = 2
degree (Ch n k) = gfa_deg k + 2*n
degree (GV n k) = gfa_deg k + 2*n
degree (ChT n) = 2*n


data ActsOn = DelState | Both | NakaState deriving (Show,Eq)


actsOn (P _ _) = Both
actsOn Del = Both
actsOn (L _ _) = NakaState
actsOn (Ch _ _) = DelState
actsOn (GV _ _) = DelState
actsOn (ChT _) = DelState


actOnNakaVac p@(P n _) = Vak $ if n<0 then [([p],1)] else []
actOnNakaVac (L n k) = Vak $ sparseNub [(o,y*x/2) | 
	nu <- [n+1 .. -1], ((a,b),x) <- gfa_comult k, (o,y) <-unVak$nakaState $op nu a b ] where
	op nu a b = if n-nu > 0 then [P nu a, P (n-nu) b] else [P (n-nu) a, P nu b]
actOnNakaVac Del = Vak []

actOnDelVac p@(P n k) = Vak $ if n >= 0 then [] else scal ( 1/ fac) $ rec n where
	fac = fromIntegral $ product [n+1 .. -1] 
	rec (-1) = [([P(-1) k],1)]
	rec n = sparseNub [ t | (o,x) <- rec (n+1), (oo,y) <- p', t<-[(oo++o,x*y),(o++oo,-x*y)]]   
	p' = [ ([Del,P(-1) a], x) | (a,x) <-gfa_1 ] ++ [ ([P(-1) a,Del], -x) | (a,x) <-gfa_1 ] 
actOnDelVac Del = Vak  []
actOnDelVac (Ch _ _) = Vak  []
actOnDelVac (GV _ _) = Vak  []
actOnDelVac (ChT _) = Vak []

-- ad(Del)^n(op)/n!
facDiff n op = let 
	bins 0 = [1]
	bins n = zipWith (-) (b++[0]) (0:b) where b = bins (n-1)
	ders = scanr (:) [] $ replicate (fromIntegral n) Del
	dels = scanl (flip (:)) [] $ replicate (fromIntegral n) Del
	fac = product [1..fromIntegral n] 
	in [ (d1++[op]++d2,fromIntegral b/fac) | d1<-ders | d2 <- dels | b <- bins n]

ad n u v = let
	rec = ad (n-1) u v
	--com = [ ([Del,P(-1) 0],1) , ([P(-1) 0,Del], -1)]
	new = [ z | (x,a) <- rec, (y,b) <- u, z <- [(x++y,-a*b),(y++x,a*b)]]
	in if n==0 then v else sparseNub new

commutator (P n a) (P m b) = if n+m==0 then [ ([], gfa_bilinear a b*fromIntegral n) ] else []
commutator Del (P n a) = ([L n a], fromIntegral n) : 
	[ ([P n c],x*y*sc) | (b,x) <- gfa_K, (c,y) <- gfa_mult b a] where
	sc = fromIntegral $ (-n*(abs n - 1) ) `div` 2
commutator p@(P _ _) Del = scal (-1) $ commutator Del p
commutator (L n a) (P m b) = [ ([P (n+m) c], x*fromIntegral(-m)) | (c,x) <- gfa_mult a b ]
commutator (Ch _ _) Del = []
commutator (Ch n a) (P (-1) y) = [ (c,x*fromRational z) | (b,x) <- gfa_mult a y, (c,z) <- facDiff n (P (-1) b) ]
commutator (GV _ _) Del = []
commutator (GV n a) (P (-1) y) = if odd n then [(s,negate x) | (s,x) <-csn] else csn where
	csn = commutator (Ch n a) (P (-1) y) 
commutator (ChT _) Del = []
commutator (ChT n) p@(P (-1) y) =  sparseNub $ first ++ second ++ third ++ fourth ++ fifth where
	k2= [(c,2*x*xx*z) | (a,x) <-gfa_K, (b,xx) <-gfa_K, (c,z) <- gfa_mult a b]
	todd_Inv_y = [[(y,1)], [(b,x*xx/2) | (a,x)<-gfa_K, (b,xx) <- gfa_mult a y],  
		sparseNub [(b,x*xx) | (a,x)<-scal (1/6) k2 ++ scal (1/12) gfa_euler, (b,xx) <- gfa_mult a y]]
	exp_K_y = [[(y,1)], [ (b,-x*xx) | (a,x) <- gfa_K, (b,xx) <- gfa_mult a y] ,
		[ (b,x*xx/2)| (a,x) <-k2, (b,xx) <- gfa_mult a y ] ]
	expTodd_y = zipWith scal [1,-1,1] todd_Inv_y
	first = [ (c,x) | (c,x) <-facDiff n p ]
	second = [ ( o++[GV gn b2], x*xx*z) | k <- [0..2] , (a,x) <- todd_Inv_y!!k, ((b1,b2),xx) <- gfa_comult a, 
		nu <- [0..n-k-2], let gn = n-nu-k-2, (o,z) <- facDiff nu (P (-1) b1) ]
	third = [ (c,x*xx*(-1)^nu) | nu<-[max (n-2) 0..n], 
		(a,x) <- exp_K_y !! (n-nu), (c,xx) <-facDiff nu (P (-1) a) ]
	fourth = [ ( o++[Ch gn b2], x*xx*z*(-1)^nu) | k <- [0..2] , (a,x) <- expTodd_y!!k, ((b1,b2),xx) <- gfa_comult a, 
		nu <- [0..n-k-2], let gn = n-nu-k-2, (o,z) <- facDiff nu (P (-1) b1) ]
	fifth = if n==2 then [ ([P(-1) b], x*xx) | (a,x) <- gfa_euler, (b,xx) <- gfa_mult a y] else []


showOperatorList [] = "|0>"
showOperatorList (Del:r) = "D " ++ showOperatorList r
showOperatorList (P n k:r) = sh ++ showOperatorList r where
	sh = (if n<0 then "p_"++show(-n)else "p"++show n)++"("++show k++") "
showOperatorList (L n k:r) = sh ++ showOperatorList r where
	sh = (if n<0 then "L_"++show(-n)else "L"++show n)++"("++show k++") "
showOperatorList (Ch n k:r) = "ch"++show n++"["++show k++ "] " ++ showOperatorList r 

instance (Show a, Show k) => Show (State a k) where
	show (Vak []) = "0"
	show (Vak [(l,x)]) = show x ++ " * \t"++showOperatorList l
	show (Vak ((l,x):r)) = show x ++ " * \t"++showOperatorList l ++ " +\n"++show(Vak r) 



-- Operator product acting on Vacuum. Result is given in terms of deltas and P(-1) operators.
delState :: (GradedFrobeniusAlgebra k, Ord k) => [VertexOperator k] -> State Rational k

delState [] = Vak [([],1)] 
delState (o:r) = if actsOn o == NakaState then toDel $ nakaState (o:r) else result where
	result = Vak $ sparseNub[ (q,x*y) | (s,x) <-unVak$ delState r, (q,y) <- unVak $ commuteIn s]
	commuteIn [] = actOnDelVac o
	commuteIn (pd:r) = case (o,pd) of 
		(Del,_) -> Vak [ (Del:pd:r,1) ]
		(P (-1) _, Del) -> Vak [ (o:pd:r,1) ]
		(P (-1) a, P (-1) b) -> if a <= b then Vak [(o:pd:r,1)] else Vak cI
		_ -> Vak cI
		where
		cI = case comm of [] -> ted; _ -> sparseNub $ ted ++ comm
		ted = [(pd:q,x*sign) | (q,x) <- unVak $ commuteIn r]
		comm =  [ (ds,x*y) | (q,x) <- commutator o pd, (ds,y) <- unVak $ delState (q++r) ]
		sign= if odd (degree pd) && odd (degree o) then -1 else 1


-- Operator product acting on Vacuum. Result is given in terms of creation operators.
nakaState :: (GradedFrobeniusAlgebra k, Ord k) => [VertexOperator k] -> State Rational k

nakaState [] = Vak [([],1)]
nakaState (o:r) = if actsOn o == DelState then toNaka $ delState (o:r) else result where
	result = Vak $ sparseNub[ (q,x*y) | (s,x) <- unVak $ nakaState r, (q,y) <- unVak $ commuteIn s]
	nakaSort p [] = ([p],1)
	nakaSort p (q:r) = case (odd (degree p)&& odd (degree q), compare p q) of
		(True,EQ) -> (p:q:r,0)
		(v, GT) -> (q:n, if v then -s else s) where (n,s) = nakaSort p r
		_ -> (p:q:r,1) 		
	commuteIn [] = actOnNakaVac o
	commuteIn (p:r) = case (o,p) of
		(P _ _, P _ _) -> if o<p then Vak [(o:p:r,1)] else Vak cI 
		_ -> Vak cI
		where
		cI = case comm of [] -> ted; _ -> sparseNub $ ted ++ comm
		ted = [(n,x*sign*sign2) | (q,x) <- unVak $ commuteIn r, let (n,sign2)=nakaSort p q]
		comm =  [ (ds,x*y) | (q,x) <- commutator o p, (ds,y) <- unVak $ nakaState (q++r) ]
		sign= if odd (degree p) && odd (degree o) then -1 else 1

-- Transforms state representations
toDel (Vak l)  = Vak $ sparseNub[ (p,x*y)|(o,x) <- l, (p,y) <- unVak$delState o] 
toNaka (Vak l) = Vak $ sparseNub[ (p,x*y)|(o,x) <- l, (p,y) <- unVak$nakaState o] 

scale a (Vak sta) = Vak $ scal a sta
add (Vak s) (Vak t) = Vak $ sparseNub $ s ++ t

multLists l stat = toNaka $ ml l stat where
	ml [] stat = stat
	ml (l:r) stat = let 
		Vak s = ml r stat
		ns = sparseNub[ (t,x*y*z) | (a,x) <- s, (o,y) <- l, (t,z)<- unVak $ delState (o++a) ]
		in Vak ns

-- Chern classes related to ChT
cT = (!!) c where
	c = [([],1::Rational)] : [if odd k then [] else cc k | k<-[1..] ]
	cc k = [ (ChT (2*i):o, x*fact(2*i)/fromIntegral(-k) ) | i<-[1..div k 2], (o,x) <- cT (k-2*i) ]
	fact n = fromIntegral $ product [1..n]


