import Control.Applicative((<*))
import Text.Parsec
import Text.Parsec.String
import Text.Parsec.Expr
import Text.Parsec.Token
import Text.Parsec.Language

data Expr = Var String | Con Int | Duo ExprDuop Expr Expr |Uno ExprUnop Expr deriving Show
data ExprUnop = Minus deriving Show
data ExprDuop = Multiply | Addition deriving Show
data Boolean = Duo Duop Expr Expr | Uno Unop Boolean deriving Show
data Unop = Not deriving Show
data Duop = And | Or | Equals | LessThan | GreaterThan deriving Show
data Stmt = Nop | String := Expr | If Boolean Stmt Stmt | Seq [Stmt]
  deriving Show

def = emptyDef {commentStart = "{-"
               , commentEnd = "-}"
               , identStart = letter
               , identLetter = alphaNum
               , opStart = oneOf "+*-<>=~&|:"
               , opLetter = oneOf "+*-<>=~&|:"
               , reservedOpNames = ["~", "&", "=", ":=", "+", "*", "-", "<", ">", "|" ]
               , reservedNames = ["true", "false", "nop",
                                 "if", "then", "else", "fi",
                                  "od"]
              }

TokenParser{ parens = m_parens
           , identifier = m_identifier
           , reservedOp = m_reservedOp
           , reserved = m_reserved
           , semiSep1 = m_semiSep1
           , whiteSpace = m_whiteSpace } = makeTokenParser def



exprparser :: Parser Expr
exprparser = buildExpressionParser table term <?> "expression"
table = [ [Infix (m_reservedOp "+" >> return (Duo Addition)) AssocLeft]
        , [Infix (m_reservedOp "*" >> return (Duo Multiply)) AssocLeft]
        , [Infix (m_reservedOp "-" >> return (Duo Minus)) AssocLeft]
        ]

boolparser :: Parser Boolean
boolparser = buildExpressionParser table term <?> "boolean"
table = [ [Prefix (m_reservedOp "~" >> return (Uno Not))]
        , [Infix (m_reservedOp "&" >> return (Duo And)) AssocLeft]
        , [Infix (m_reservedOp "=" >> return (Duo Equals)) AssocLeft]
        , [Infix (m_reservedOp "|" >> return (Duo Or)) AssocLeft]
        , [Infix (m_reservedOp "<" >> return (Duo LessThan)) AssocLeft]
        , [Infix (m_reservedOp ">" >> return (Duo GreaterThan)) AssocLeft]

term = m_parens exprparser
       <|> fmap Var m_identifier
       <|> fmap Con m_natural

mainparser :: Parser Stmt
mainparser = m_whiteSpace >> stmtparser <* eof
    where
      stmtparser :: Parser Stmt
      stmtparser = fmap Seq (m_semiSep1 stmt1)
      stmt1 = (m_reserved "nop" >> return Nop)
              <|> do { v <- m_identifier
                     ; m_reservedOp ":="
                     ; e <- exprparser
                     ; return (v := e)
                     }
              <|> do { m_reserved "if"
                     ; b <- boolparser
                     ; m_reserved "then"
                     ; p <- stmtparser
                     ; m_reserved "else"
                     ; q <- stmtparser
                     ; m_reserved "fi"
                     ; return (If b p q)
                     }
run :: Show a => Parser a -> String -> IO ()
run p input
        = case (parse p "" input) of
            Left err -> do{ putStr "parse error at "
                          ; print err
                          }
            Right x  -> print x


play :: String -> IO ()
play inp = case parse mainparser "" inp of
             { Left err -> print err
             ; Right ans -> print ans
             }
