module Kei_parser where 
import Text.Parsec
import Data.Map as Map
import Data.Char

data Symbol = Initial | Next Symbol deriving (Eq, Ord)

data ParsePos = ParsePos (Int, Int) deriving (Show, Eq, Ord)

data VarUnit = VarSimbol Symbol VarUnit | VarName String

instance Show Symbol where
    show x = show (num x)
      where
         num x = case x of
            Initial -> 0
            Next s -> (num s) + 1

instance Show VarUnit where
    show (VarSimbol x y) = (show y) ++ "{" ++ (show x) ++ "}" 
    show (VarName x) = x

instance Eq VarUnit where
    (==) (VarSimbol x _) (VarSimbol x' _) = x == x'
    (==) (VarName x) (VarName x') = x == x'
    (==) _ _ = False

instance Ord VarUnit where
    compare (VarSimbol x _) (VarSimbol x' _) = compare x x'
    compare (VarSimbol x _) (VarName _) = LT
    compare (VarName _) (VarSimbol x _) = LT
    compare (VarName x) (VarName x') = compare x x'

data PTerm = 
        PAbs VarUnit PTerm
      | PApp PTerm PTerm
      | PType VarUnit PTerm PTerm
      | PLambda PTerm PTerm
      | PValue VarUnit
      | PMatch PTerm PTerm [(([VarUnit], PTerm), PTerm)] deriving (Show, Eq, Ord) -- Just a syntactly representation of a Pi Modulo Lambda Term

data Function = Function PTerm PTerm deriving (Show, Eq, Ord) -- a function is just a lambda function that hold ur type
data Def = Def String Function deriving Show
data RewriteRule = RewriteRule String PTerm deriving Show

data Definition = FuncDef Def | RewriteDef RewriteRule | Eval PTerm deriving (Show)

data AST = AST [Definition] deriving Show
var_characters = ['_', '\'']

getPosParser :: Monad m => ParsecT s u m (Int, Int)
getPosParser = do 
    x <- getPosition
    return (sourceLine x, sourceColumn x) 

with_spaces :: Parsec String st a -> Parsec String st a
with_spaces k = (char_ignorable) >> k >>= (\a -> (char_ignorable) >> return a)
 where 
    char_ignorable = do
        let tryC a b = (a <|> b) <|> (b <|> a)
        tryC spaces ((try $ many $ (char '\n')) >>= (\_ -> return ()))

--(try $ many $ (char '\n')) >>= (\_ -> return ())
justParent :: Parsec String st a -> Parsec String st a
justParent k = (between (char '(') (char ')') (with_spaces k))

consume_var_name :: Parsec String st String
consume_var_name = do
    x <- alphaNum
    return x

parseType :: Parsec String st (String, PTerm)
parseType = justParent $ do
              str <- with_spaces consume_var_name
              (with_spaces (string ":"))
              d <- parseTerm
              return (str, d)

parsePi :: Parsec String st PTerm
parsePi = justParent $ do
    (with_spaces (string "forall")) >> do
        let parsePTypes =  do 
            (t, x) <- with_spaces $ parseType
            l <- parsePTypes <|> ((with_spaces (string "->")) >> parseTerm)
            return (PType (VarName t) x l)
        parsePTypes

parseSimplyTerm :: Parsec String st PTerm
parseSimplyTerm = consume_var_name >>= (\a -> return (PValue (VarName a)))

parseLambda :: Parsec String st PTerm
parseLambda = do
    x <- consume_var_name 
    l <- try (space >> parseLambda) <|> ((with_spaces (string "=>") >> (with_spaces parseTerm)))
    return (PAbs (VarName x) l)

parseLambdaAbs :: Parsec String st Function
parseLambdaAbs = justParent $ do
    (with_spaces (string "\\"))
    x <- parsePi
    (with_spaces (string "|"))
    parseLambda >>= (\c -> return (Function x c))

parseApp :: Parsec String st PTerm
parseApp = (between (char '(') (char ')') app)
  where 
    app = do
        x <- parseTerm
        y <- many1 (space >> parseTerm)
        return (Prelude.foldl (\x -> \y -> PApp x y) x y)

parseMatching :: Parsec String st PTerm
parseMatching = matching
 where 
    matching = do
        (with_spaces (char '['))
        k <- parseTerm
        (many1 space)
        (string "of")
        (many1 space)
        type' <- with_spaces parseTerm
        (with_spaces $ return $ ())
        x <- (many matchs)
        (with_spaces (char ']'))
        return (PMatch k type' x)
    matchs = do
        (with_spaces (string "|"))
        y <- between (with_spaces (char '{')) (with_spaces (char '}')) (with_spaces parseFreeVars)
        k <- parseTerm
        with_spaces (string "=>")
        y' <- with_spaces parseTerm
        return ((y, k), y')
    parseFreeVars = do
        many (try (consume_var_name >>= (\a -> (space) >> return (VarName a))) <|> (consume_var_name >>= (\a -> return (VarName a))))
   
parseTerm :: Parsec String st PTerm
parseTerm = choice [try parsePi, try parseMatching, try parseApp, parseSimplyTerm]

parseFuncDefinition ::  Parsec String st Def
parseFuncDefinition =  do
    x <- with_spaces $ consume_var_name
    with_spaces (string "=")
    parseLambdaAbs >>= (\a -> (with_spaces (string ".")) >> return (Def x a))

parseRuleDefinition ::  Parsec String st RewriteRule
parseRuleDefinition = do
    with_spaces (string "Rule")
    x <- with_spaces $ many $ letter
    with_spaces (string ":")
    (try parsePi <|> parseSimplyTerm) >>= (\a -> (with_spaces (string ".")) >> return (RewriteRule x a))

parseEval :: Parsec String st Definition
parseEval = do
    x <- with_spaces (string "#EVAL")
    with_spaces (string ":")
    y <- with_spaces parseTerm
    with_spaces (string ".")
    return (Eval y)

parseS :: [Definition] -> Parsec String st [Definition]
parseS k = do
    (kei_definiton >>= (\a -> (parseS k) >>= (\c -> return (a : c)))) <|> (eof >>= (\a -> return k))
 where
     kei_definiton = choice [try (parseFuncDefinition >>= (\a -> return $ FuncDef $ a)), try (parseRuleDefinition >>= (\a -> return $ RewriteDef $ a)), parseEval]

getAST :: IO (Either (IO ()) AST)
getAST = do
    n <- readFile ("sebastian.sbst")
    case (parse (parseS ([])) "" n) of
      Right x_ -> return (Right (AST x_))
      Left y_ ->  return (Left (print y_))