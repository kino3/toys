module Workshop201509 where
{-
 Kinoshita-lab Gasshuku 2015.08.31-2015.09.02
  @ KU Fujimi Seminar House
-}

{-
sum :: Num a => [ a ] -> a
sum []       = 0
sum (x : xs) = x + sum xs
-}

product' :: Num a => [ a ] -> a
product' [] = 1
product' (x : xs) = x * (product xs)

qsort :: Ord a => [ a ] -> [ a ]
qsort [] = []
qsort (x : xs) = qsort smaller ++ [ x ] ++ qsort larger
  where
    smaller = [ a | a <- xs , a <= x ]
    larger  = [ b | b <- xs , b >  x ]

-- 1.7.4
qsort2 :: Ord a => [ a ] -> [ a ]
qsort2 [] = []
qsort2 (x : xs) = qsort2 larger ++ [ x ] ++ qsort2 smaller
  where
    smaller = [ a | a <- xs , a <= x ]
    larger  = [ b | b <- xs , b >  x ]

-- 1.7.5
qsort3 :: Ord a => [ a ] -> [ a ]
qsort3 [] = []
qsort3 (x : xs) = qsort3 smaller ++ [ x ] ++ qsort3 larger
  where
    smaller = [ a | a <- xs , a < x ]
    larger  = [ b | b <- xs , b >  x ]

-- 2.6.3 N, ''to``, indent xs
n = a `div` length xs
    where
      a = 10
      xs = [1,2,3,4,5]

-- 2.6.4
last2 xs = xs !! (length xs - 1)
last3 xs = head (reverse xs)

-- 2.6.5
init1 xs = reverse $ tail $ reverse xs
init2 xs = take (length xs - 1) xs

-- 3.11.1
{-
*Workshop201509> :t ['a','b','c']
['a','b','c'] :: [Char]
*Workshop201509> :t ('a','b','c')
('a','b','c') :: (Char, Char, Char)
*Workshop201509> :t [(False, '0'),(True,'1')]
[(False, '0'),(True,'1')] :: [(Bool, Char)]
*Workshop201509> :t ([False,True],['0','1'])
([False,True],['0','1']) :: ([Bool], [Char])
*Workshop201509> :t [tail,init,reverse]
[tail,init,reverse] :: [[a] -> [a]]
-}
-- 3.11.2
second xs = head (tail xs)
swap (x,y) = (y,x)
pair x y = (x,y)
double x = x * 2
palindrome xs = reverse xs == xs
twice f x = f (f x)
{-
*Workshop201509> :t second
second :: [a] -> a
*Workshop201509> :t swap
swap :: (t1, t) -> (t, t1)
*Workshop201509> :t pair
pair :: t -> t1 -> (t, t1)
*Workshop201509> :t double
double :: Num a => a -> a
*Workshop201509> :t palindrome
palindrome :: Eq a => [a] -> Bool
*Workshop201509> :t twice
twice :: (t -> t) -> t -> t
-}

-- 4.8.1
halve :: [a] -> ([a],[a])
halve xs = splitAt (length xs `div` 2) xs

-- 4.8.2
safetail1 :: [a] -> [a]
safetail1 xs = if null xs then [] else tail xs

safetail2 :: [a] -> [a]
safetail2 xs | null xs = []
             | otherwise = tail xs

safetail3 :: [a] -> [a]
safetail3 [] = []
safetail3 (x : xs) = tail (x : xs)

-- 4.8.3
{-
(\/) :: Bool -> Bool -> Bool
False \/ False = False
_     \/ _     = True
-}
{-
(\/) :: Bool -> Bool -> Bool
True  \/ True  = True
True  \/ False = True
False \/ True  = True
False \/ False = False
-}
{-
(\/) :: Bool -> Bool -> Bool
True  \/ _  = True
False \/ b  = b
-}
(\/) :: Bool -> Bool -> Bool
b \/ c | b == c    = b
       | otherwise = True

-- 4.8.4
{-
(/\) :: Bool -> Bool -> Bool
b /\ c = if b == True 
           then if c == True
                  then True
                  else False
           else False
-}
-- 4.8.5
(/\) :: Bool -> Bool -> Bool
b /\ c = if b == True 
           then c
           else False

-- 4.8.6
mult :: Num a => a -> a -> a -> a
mult = \ x y z -> x * y * z

-- 5.7.5
ex575before = [(x,y) | x <- [1,2,3], y <- [4,5,6]]
ex575after  = concat [ [ (x,y) | y <- [4,5,6]] | x <- [1,2,3] ]








