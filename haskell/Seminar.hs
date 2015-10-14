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

-- 浮動小数点数の説明
