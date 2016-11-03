module PiH08 where
import Prelude hiding (return,(>>=))
import Data.Char
-- Programming in Haskell Section. 8 Parser

type Parser a = String -> [(a, String)]

return :: a -> Parser a
return v = \inp -> [(v, inp)]

failure :: Parser a
failure = \inp -> []

item :: Parser Char
item = \inp -> case inp of
                 [] -> [] 
                 (x : xs) -> [(x, xs)]

parse :: Parser a -> String -> [(a, String)]
parse p inp = p inp

-- 8.4

(>>=) :: Parser a -> (a -> Parser b) -> Parser b
p >>= f = \inp -> case parse p inp of
                     [] -> []
                     [(v,out)] -> parse (f v) out

p :: Parser (Char,Char)
p = item >>= \x -> item >>= \_ -> item >>= \y -> return (x,y)
{-
do x <- item
       item
       y <- item
       return (x,y)
-}

-- 8.5

(+++) :: Parser a -> Parser a -> Parser a
p +++ q = \inp -> case parse p inp of
                        [] -> parse q inp
                        [(v,out)] -> [(v,out)]
-- 8.6

sat :: (Char -> Bool) -> Parser Char
sat p = item >>= \x -> if p x then return x else failure


digit :: Parser Char
digit = sat isDigit

lower :: Parser Char
lower = sat isLower

upper :: Parser Char
upper = sat isUpper

letter :: Parser Char
letter = sat isAlpha

alphanum :: Parser Char
alphanum = sat isAlphaNum

char :: Char -> Parser Char
char x = sat (== x)

string :: String -> Parser String
string [] = return []
string (x:xs) = char x >>= \_ -> string xs >>= \_ -> return (x : xs)

{-
  parse (string "bc") "abc"
= (string "bc") "abc"
= (char 'b' >>= \_ -> string "c" >>= \_ -> return ('b' : "c")) "abc"
= (char 'b' >>= \_ -> (char 'c' >>= \_ -> string [] >>= \_ -> return ('c' : [])) >>= \_ -> return ('b' : "c")) "abc"
= (char 'b' >>= \_ -> (char 'c' >>= \_ -> return [] >>= \_ -> return ('c' : [])) >>= \_ -> return ('b' : "c")) "abc"
= (sat (=='b') >>= \_ -> (sat (=='c') >>= \_ -> return [] >>= \_ -> return ('c' : [])) >>= \_ -> return ('b' : "c")) "abc"
sat p = item >>= \x -> if p x then return x else failure

= ((item >>= \x -> if (x == 'b') then return x else failure) 
    >>= \_ -> ((item >>= \x -> if (x == 'c') then return x else failure) 
    >>= \_ -> return [] >>= \_ -> return ('c' : [])) 
    >>= \_ -> return ('b' : "c")) "abc"
-}

many :: Parser a -> Parser [a]
many p = many1 p +++ return []

many1 :: Parser a -> Parser [a]
many1 p = p >>= \v -> many p >>= \vs -> return (v : vs)

ident :: Parser String
ident = lower >>= \x -> many alphanum >>= \xs -> return (x : xs)

nat :: Parser Int -- read P.30
nat = many1 digit >>= \xs -> return (read xs) 

space :: Parser ()
space = many (sat isSpace) >>= \_ -> return ()

-- 8.7

token :: Parser a -> Parser a
token p = space >>= \_ -> p >>= \v -> space >>= \_ -> return v

identifier :: Parser String
identifier = token ident

natural :: Parser Int
natural = token nat

symbol :: String -> Parser String
symbol xs = token (string xs)

p87 :: Parser [Int]
p87 = symbol "[" >>= \_ ->
      natural >>= \n ->
      many (symbol "," >>= \_ -> natural) >>= \ns ->
      symbol "]" >>= \_ ->
      return (n : ns)

-- 8.8

expr :: Parser Int
expr = term >>= \t ->
        ((symbol "+" >>= \_ ->
          expr       >>= \e ->
          return (t + e)) 
         +++ return t)

term :: Parser Int
term = factor >>= \f ->
       ((symbol "*" >>= \_ ->
         term       >>= \t ->
         return (f * t))
        +++ return f)

factor :: Parser Int
factor = (symbol "(" >>= \_ ->
          expr       >>= \e ->
          symbol ")" >>= \_ ->
          return e)
         +++ natural

eval :: String -> Int
eval xs = case parse expr xs of
             [(n, [])]  -> n
             [(_, out)] -> error ("unused input: " ++ out)
             []         -> error "invalid input"


-- 8.10
-- 1
int :: Parser Int
int = ((char '-') >>= \_ -> nat >>= \n -> return (-n)) +++ nat

-- 2
comment :: Parser String
comment = (string "--" ) >>= \x -> (many1 (char '\n' +++ item)) >>= \y -> return (x ++ y)

comment' :: Parser ()
comment' = (string "--") >>= \_ -> (many (alphanum +++ (char ' ') +++ (char '\t'))) >>= \_ -> char '\n' >>= \_ -> return ()


-- 3,4 omit

-- 5 brief. term * 2 -> term * 1

-- 6
expr6 :: Parser Int
expr6 = term6 >>= \t ->
          ((symbol "+" >>= \_ ->
            expr6      >>= \e ->
            return (t + e))
           +++
           (symbol "-" >>= \_ ->
            expr6      >>= \e ->
            return (t - e)) 
           +++
           return t
          )

term6 :: Parser Int
term6 = factor6 >>= \f ->
          ((symbol "*" >>= \_ ->
            term6      >>= \t ->
            return (f * t))
           +++
           (symbol "/" >>= \_ ->
            term6      >>= \t ->
            return (f `div` t))
           +++
           return f
          )

factor6 :: Parser Int
factor6 = (symbol "(" >>= \_ ->
           expr6       >>= \e ->
           symbol ")" >>= \_ ->
           return e)
          +++
          natural

eval6 :: String -> Int
eval6 xs = case parse expr6 xs of
             [(n, [])]  -> n
             [(_, out)] -> error ("unused input: " ++ out)
             []         -> error "invalid input"

-- 7
expr7 :: Parser Int
expr7 = term7 >>= \t ->
          ((symbol "+" >>= \_ ->
            expr7      >>= \e ->
            return (t + e))
           +++
           (symbol "-" >>= \_ ->
            expr7      >>= \e ->
            return (t - e)) 
           +++
           return t
          )

term7 :: Parser Int
term7 = term'7 >>= \f ->
          ((symbol "*" >>= \_ ->
            term7      >>= \t ->
            return (f * t))
           +++
           (symbol "/" >>= \_ ->
            term7      >>= \t ->
            return (f `div` t))
           +++
           return f
          )

term'7 :: Parser Int
term'7 = factor7 >>= \f ->
          ((symbol "^" >>= \_ ->
            term'7     >>= \t ->
            return (f ^ t))
           +++
           return f
          )

factor7 :: Parser Int
factor7 = (symbol "(" >>= \_ ->
           expr7       >>= \e ->
           symbol ")" >>= \_ ->
           return e)
          +++
          natural

eval7 :: String -> Int
eval7 xs = case parse expr7 xs of
             [(n, [])]  -> n
             [(_, out)] -> error ("unused input: " ++ out)
             []         -> error "invalid input"


-- 8
{-
8.a

expr   ::= expr '-' factor | factor
factor ::= '(' expr ')' | nat
nat    ::= '0' | '1' | '2' | ...

-}

-- can't stop ...             
expr8 :: Parser Int
expr8 = (expr8      >>= \e ->
         symbol "-" >>= \_ ->
         factor8    >>= \f -> return (e - f))
        +++
        factor8     >>= \f -> return f 
        
factor8 :: Parser Int
factor8 = (symbol "(" >>= \_ ->
           expr8      >>= \e ->
           symbol ")" >>= \_ ->
           return e)
          +++
          natural

eval8 :: String -> Int
eval8 xs = case parse expr8 xs of
             [(n, [])]  -> n
             [(_, out)] -> error ("unused input: " ++ out)
             []         -> error "invalid input"

-- 8.d.
factor8' :: Parser Int
factor8' = (symbol "(" >>= \_ ->
            expr8'     >>= \e ->
            symbol ")" >>= \_ ->
           return e)
          +++
          natural

expr8' :: Parser Int
expr8' =  factor8' >>= \f ->
          many (symbol "-" >>= \_ ->
                factor8'   >>= \f -> return f)
                   >>= \fs ->
          return (f + ((foldl (-) 0) fs))
  
eval8' :: String -> Int
eval8' xs = case parse expr8' xs of
             [(n, [])]  -> n
             [(_, out)] -> error ("unused input: " ++ out)
             []         -> error "invalid input"
