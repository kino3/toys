module Seminar where
import Data.Char
-- 5. リスト内包表記

factors :: Int -> [Int]
factors n = [ x | x <- [1..n], n `mod` x == 0]

prime :: Int -> Bool
prime n = factors n == [1,n]

primes :: Int -> [Int]
primes n = [ x | x <- [2..n], prime x]

find :: Eq a => a -> [(a,b)] -> [b]
find k t = [v | (k',v) <- t , k == k']

find2 :: Eq a => a -> [(a,b)] -> [b]
find2 _ [] = []
find2 k ((k',v) : xs) = if k == k' then v : find2 k xs else find2 k xs

pairs :: [a] -> [(a,a)]
pairs xs = zip xs (tail xs)

sorted :: Ord a => [a] -> Bool
sorted xs = and [ x <= y | (x,y) <- pairs xs ]

positions :: Eq a => a -> [a] -> [Int]
positions x xs = [i | (x',i) <- zip xs [0..n], x == x']
                 where n = length xs - 1


lowers :: String -> Int
lowers xs = length [x | x <- xs, isLower x]

count :: Char -> String -> Int
count x xs = length [x' | x' <- xs, x == x']

-- countの別定義が宿題
count' :: Char -> String -> Int
count' _ [] = 0
count' x (c : cs) = if x == c then 1 + count' x cs else count' x cs


-- 浮動小数点数の説明

-- 5.5 Caesar Crypt

let2int :: Char -> Int
let2int c = ord c - ord 'a'

int2let :: Int -> Char
int2let n = chr (ord 'a' + n)

shift :: Int -> Char -> Char
shift n c | isLower c = int2let ((let2int c + n) `mod` 26)
          | otherwise = c

encode :: Int -> String -> String
encode n xs = [ shift n x | x <- xs ]

table :: [Float]
table = [8.2, 1.5, 2.8, 4.3, 12.7,
         2.2, 2.0, 6.1, 7.0, 0.2,
         0.8, 4.0, 2.4, 6.7, 7.5,
         1.9, 0.1, 6.0, 6.3, 9.1,
         2.8, 1.0, 2.4, 0.2, 2.0, 0.1]

percent :: Int -> Int -> Float
percent n m = (fromIntegral n / fromIntegral m) * 100

freqs :: String -> [Float]
freqs xs = [percent (count x xs) n | x <- ['a'..'z']]
           where n = lowers xs

chisqr :: [Float] -> [Float] -> Float
chisqr os es = sum [((o - e) ^ 2) / e | (o,e) <- zip os es]

rotate :: Int -> [a] -> [a]
rotate n xs = drop n xs ++ take n xs

crack :: String -> String
crack xs = encode (-factor) xs
  where
    factor = head (positions (minimum chitab) chitab)
    chitab = [chisqr (rotate n table') table | n <- [0..25]]
    table' = freqs xs

-- 5.7 Exercises

-- 5.7.1
sumpower2 :: Int
sumpower2 = sum [ x ^ 2 | x <- [1..100]]

-- 5.7.2
replicate' :: Int -> a -> [a]
replicate' n x = [x | x' <- [1..n]]

-- 5.7.3
pyths :: Int -> [(Int, Int, Int)]
pyths n = [(x,y,z) | x <- [1..n], y <- [1..n], z <- [1..n], x ^ 2 + y ^ 2 == z ^ 2 ]

-- 5.7.4
perfects :: Int -> [Int]
perfects n = [ x | x <- [1..n] , sum(factors(x)) - x == x]

-- 5.7.5
ex575before :: [(Integer, Integer)]
ex575before = [(x,y) | x <- [1,2,3], y <- [4,5,6]]
ex575after :: [(Integer, Integer)]
ex575after  = concat [ [ (x,y) | y <- [4,5,6]] | x <- [1,2,3] ]

-- 5.7.6
positions' :: Eq a => a -> [a] -> [Int]
positions' x xs = find x (zip xs [0..n]) where n = length xs - 1

-----------------------------------
-- 6 再帰関数
-----------------------------------

-- 6.1

factorial :: Int -> Int
factorial n = product [1..n]

-- http://www.mew.org/~kazu/doc/book/haskell.html
-- n+k pattern はもうつかえない。
factorial' :: Int -> Int
factorial' 0 = 1
factorial' n = n * factorial' (n - 1)
-- これはマイナスのときはとまらない。。。

-- 6.2

product2 :: Num a => [a] -> a
product2 [] = 1
product2 (n:ns) = n * product2 ns

length2 :: [a] -> Int
length2 [] = 0
length2 (_:xs) = 1 + length2 xs

reverse2 :: [a] -> [a]
reverse2 [] = []
reverse2 (x:xs) = reverse2 xs ++ [x]

{-
reverse3 :: [a] -> [a]
reverse3 [] = []
reverse3 (x:xs) = reverse3 xs ++ [x]
-}

(+++) :: [a] -> [a] -> [a]
[]       +++ ys = ys
(x : xs) +++ ys = x : (xs +++ ys)
