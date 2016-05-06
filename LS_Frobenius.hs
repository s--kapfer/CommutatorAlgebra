{-# LANGUAGE GeneralizedNewtypeDeriving, TypeOperators, TypeFamilies #-}
module LS_Frobenius 
	where

import Data.Array
import Data.List
import Data.MemoTrie

-- the d. We are dealing with surfaces, so d=2.
gfa_d = 2 :: Int

class (Ix k,Ord k)=> GradedFrobeniusAlgebra k where
	gfa_deg :: k -> Int
	gfa_base :: [k]
	gfa_baseOfDeg :: Int -> [k]
	gfa_1 :: Num a => [(k,a)]
	gfa_K :: Num a => [(k,a)]
	gfa_T :: Num a => k -> a
	gfa_mult :: Num a => k -> k -> [(k,a)]
	gfa_bilinear :: Num a => k -> k -> a
	gfa_bilinear i j = sum [ gfa_T k * x | (k,x) <- gfa_mult i j ]
	gfa_bilinearInverse :: Num a => k -> [(k, a)]

-- Tensor product
instance (GradedFrobeniusAlgebra k, GradedFrobeniusAlgebra k') => GradedFrobeniusAlgebra (k,k') where
	gfa_deg (i,j) = gfa_deg i + gfa_deg j
	gfa_base = [(i,j) | i<-gfa_base, j<-gfa_base]
	gfa_baseOfDeg n = [(i,j) | i<-gfa_base, j<-gfa_baseOfDeg (n-gfa_deg i) ]
	gfa_1 = [((i,j),x*y) | (i,x) <- gfa_1, (j,y) <- gfa_1]
	gfa_K = [ ((i,j),x*y) | (i,x) <- gfa_K, (j,y) <- gfa_1] ++ [ ((i,j),x*y) | (i,x) <- gfa_1, (j,y) <- gfa_K] 
	gfa_T (i,j) = gfa_T i * gfa_T j
	gfa_mult (i,j) (k,l) = [((m,n),ep*x*y) | (m,x)<-gfa_mult i k, (n,y)<-gfa_mult j l] where
		ep = if odd (gfa_deg j * gfa_deg k) then (-1) else 1
	gfa_bilinearInverse (i,j) = [ ((k,l),ep k *x*y) | 
		(k,x) <- gfa_bilinearInverse i, (l,y) <-gfa_bilinearInverse j] where
			ep k = if odd (gfa_deg k * gfa_deg j) then (-1) else 1

-- base for Symmetric tensors
gfa_symBase n = cs n gfa_base where
	f [] = []
	f l@(a:b) = (a, if odd (gfa_deg a) then b else l ) : f b
	cs 0 _ = [[]]
	cs k b@(a:r) = [ x:t | (x,r) <- f b, t <- cs (k-1) r] 
-- power is n, degree is k
gfa_symBaseOfDeg n k = csd n k gfa_base where
	f [] = []
	f l@(a:b) = (a, d, if odd d then b else l) : f b where d = gfa_deg a
	csd 0 0 _ = [[]]
	csd n k b@(a:r) = if n<= 0 then [] else
		[ x:t | (x,d,r) <- f b, t <- csd (n-1) (k-d) r] 
	
	
gfa_multList [] = gfa_1
gfa_multList [i] = [(i,1)]
gfa_multList [i,j] = gfa_mult i j
gfa_multList (i:r) = sparseNub [ (k,y*x) | (j,x)<-gfa_multList r, (k,y)<-gfa_mult i j ]

gfa_adjoint f = adj where
	b i = [(j,x) | j<-gfa_base, let x = gfa_bilinear j i, x/=0]
	ftrans = accumArray (flip (:)) [] (head gfa_base, last gfa_base)  [ (j,(i,x)) | i <-gfa_base, (j,x) <- f i] 
	ftb i = sparseNub [ (k,y*x) | (j,x) <- b i, (k,y) <- ftrans!j]
	adj i = sparseNub [ (k,y*x) | (j,x) <- ftb i, (k,y) <- gfa_bilinearInverse j]

gfa_comult :: (GradedFrobeniusAlgebra k, Ix k,Num a,Eq a) => k -> [((k,k),a)]
gfa_comult = gfa_adjoint (uncurry gfa_mult)

gfa_comultN 0 a = [([a],1)]
gfa_comultN n a = let
	rec = gfa_comultN (n-1) a
	in sparseNub [ (c:d:r, x*y) | (b:r,x) <- rec, ((c,d),y) <- gfa_comult b]

gfa_euler :: (GradedFrobeniusAlgebra k, Ix k, Num a) => [(k,a)]
gfa_euler = [(k,fromIntegral x) | (k,x)<-e] where 
	e = sparseNub [ (k,y*x*v) | (u,v) <- gfa_1, (ij,x) <- gfa_comult u, (k,y) <- uncurry gfa_mult ij] 

sparseNub [] = []
sparseNub l = sn (head sl) (tail sl) where
	sl = sortBy ((.fst).compare.fst) l
	sn (i,x) ((j,y):r) = if i==j then sn (i,x+y) r else app (i,x) $ sn (j,y) r
	sn ix [] = app ix []
	app (i,x) r = if x==0 then r else (i,x) : r

scal 0 _ = []
scal a l = [ (p,a*x) | (p,x) <- l]

-- Cohomology of K3 surfaces
newtype K3Domain = K3 Int deriving (Enum,Eq,Num,Ord,Ix)
instance Show K3Domain where show (K3 i) = show i
instance GradedFrobeniusAlgebra K3Domain where
	gfa_deg (K3 0) = -2
	gfa_deg (K3 23) = 2
	gfa_deg i = if 1<=i && i<=22 then 0 else undefined
	
	gfa_1 = [(0,1)]
	gfa_K = []
	
	gfa_T (K3 23) = -1
	gfa_T _ = 0
	
	gfa_base = [0..23]
	gfa_baseOfDeg 0 = [1..22]
	gfa_baseOfDeg (-2) = [0]
	gfa_baseOfDeg 2 = [23]
	gfa_baseOfDeg _ = []
	
	gfa_mult (K3 0) i = [(i,1)]
	gfa_mult i (K3 0) = [(i,1)]
	gfa_mult (K3 23) _ = []
	gfa_mult _ (K3 23) = []
	gfa_mult (K3 i) (K3 j) =  [(23, fromIntegral $ bilK3_func i j)]
	
	gfa_bilinearInverse (K3 i) = [(K3 j,fromIntegral x) | j<-[0..23], let x =bilK3inv_func i j, x/=0]

delta i j = if i==j then 1 else 0

e8 = array ((1,1),(8,8)) $
	zip [(i,j) | i <- [1..8],j <-[1..8]] [
	-2, 1, 0, 0, 0, 0, 0, 0,
	1, -2, 1, 0, 0, 0, 0, 0,
	0, 1, -2, 1, 0, 0, 0, 0,
	0, 0, 1, -2, 1, 0, 0, 0,
	0, 0, 0, 1, -2, 1, 1, 0,
	0, 0, 0, 0, 1, -2, 0, 1,
	0, 0, 0, 0, 1, 0, -2, 0,
	0, 0, 0, 0, 0, 1, 0, -2 :: Int]

inve8= array ((1,1),(8,8)) $
	zip [(i,j) | i <- [1..8],j <-[1..8]] [-2, -3, -4, -5, -6, -4, -3, -2, -3, -6, -8, -10, -12, -8, -6, -4,
		-4, -8, -12, -15, -18, -12, -9, -6, -5, -10, -15, -20, -24, -16, -12,
		-8, -6, -12, -18, -24, -30, -20, -15, -10, -4, -8, -12, -16, -20,
		-14, -10, -7, -3, -6, -9, -12, -15, -10, -8, -5, -2, -4, -6, -8,
		-10, -7, -5, -4 :: Int]

-- Bilinear form on K3 surfaces
bilK3_func ii jj = let 
	(i,j) = (min ii jj, max ii jj) 
	u 1 2 = 1
	u 2 1 = 1
	u 1 1 = 0
	u 2 2 = 0
	u i j = undefined	
	in 
	if (i < 0) || (j > 23) then undefined else
	if (i == 0) then delta j 23 else
	if (i >= 1) && (j <= 2) then u i j else
	if (i >= 3) && (j <= 4) then u (i-2) (j-2) else
	if (i >= 5) && (j <= 6) then u (i-4) (j-4) else
	if (i >= 7) && (j <= 14) then e8 ! ((i-6), (j-6)) else
	if (i >= 15) && (j<= 22) then e8 ! ((i-14), (j-14))  else
	0 :: Int

-- Inverse bilinear form
bilK3inv_func ii jj = let 
	(i,j) = (min ii jj, max ii jj) 
	u 1 2 = 1
	u 2 1 = 1
	u 1 1 = 0
	u 2 2 = 0
	u i j = undefined	
	in 
	if (i < 0) || (j > 23) then undefined else
	if (i == 0) then delta j 23 else
	if (i >= 1) && (j <= 2) then u i j else
	if (i >= 3) && (j <= 4) then u (i-2) (j-2) else
	if (i >= 5) && (j <= 6) then u (i-4) (j-4) else
	if (i >= 7) && (j <= 14) then inve8 ! ((i-6), (j-6)) else
	if (i >= 15) && (j<= 22) then inve8 ! ((i-14), (j-14))  else
	0 :: Int

-- Cohomology of projective space
newtype P2Domain = P2 Int deriving (Show,Eq,Ord,Ix,Num)
instance GradedFrobeniusAlgebra P2Domain where
	gfa_deg (P2 0) = -2
	gfa_deg (P2 1) = 0
	gfa_deg (P2 2) = 2
	
	gfa_1 = [(P2 0,1)]
	gfa_K = [(P2 1,-3)]
	
	gfa_T (P2 2) = -1
	gfa_T _ = 0
	
	gfa_base = [0,1,2]
	gfa_baseOfDeg 0 = [1]
	gfa_baseOfDeg (-2) = [0]
	gfa_baseOfDeg 2 = [2]
	gfa_baseOfDeg _ = []
	
	gfa_mult (P2 0) i = [(i,1)]
	gfa_mult i (P2 0) = [(i,1)]
	gfa_mult (P2 2) _ = []
	gfa_mult _ (P2 2) = []
	gfa_mult (P2 1) (P2 1) =  [(2, 1)]

	gfa_bilinearInverse i =  [(2-i, 1)]


-- Cohomology of complex torus
newtype TorusDomain = Tor Int deriving (Enum,Eq,Num,Ord,Ix)
instance Show TorusDomain where show (Tor i) = show i
instance GradedFrobeniusAlgebra TorusDomain where
	gfa_deg (Tor i) = 
		if i<0 then undefined else
		if i<=0 then -2 else
		if i<=4 then -1 else
		if i<=10 then 0 else
		if i<=14 then 1 else
		if i==15 then 2 else undefined
		
	gfa_1 = [(0,1)]
	gfa_K = []
	
	gfa_T (Tor 15) = -1
	gfa_T _ = 0
	
	gfa_base = [0..15]
	gfa_baseOfDeg (-2) = [0]
	gfa_baseOfDeg (-1) = [1..4]
	gfa_baseOfDeg 0 = [5..10]
	gfa_baseOfDeg 1 = [11..14]
	gfa_baseOfDeg 2 = [15]
	gfa_baseOfDeg _ = []
	
	gfa_mult i j = if k<0 then [] else [(k,fromIntegral x)] where (k,x)= torusMultArray!(i,j)
	
	gfa_bilinearInverse i = [(15-i,gfa_bilinear i (15-i))]

torusMultArray = listArray ((0,0),(15,15)) mults where  
	toLists = listArray (0,15) list
	list = [[],[1],[2],[3],[4],[1,2],[1,3],[1,4],[2,3],[2,4],
			[3,4],[1,2,3],[1,2,4],[1,3,4],[2,3,4],[1,2,3,4::Int]]
	fromLists x = findIndex (x==) list
	mults = [ check (toLists!i ++ toLists!j)  | i<-[0..15],j<-[0..15]]
	check ab = case fromLists $ sort ab of
		Nothing -> (-1,0)
		Just i -> (Tor i, sign ab)
	sign [] = 1; sign (i:r) = sign r * signum (product [j-i | j<-r])
