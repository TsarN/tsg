module SM where

import Lang hiding (State)

import Data.List
import Control.Monad.State

type Block = [Instr]

data Instr = Push Atom
           | Cons
           | Split
           | Test -- is cons?
           | Eqa
           | Dup
           | Dup2
           | Drop
           | Swap
           | If Block
           | Call FName
           | Return
           | Exit
           | Func FName
           deriving (Eq, Show)

data CState = CState { funcs :: [Int]
                     , defs :: [FDef]
                     , dispatch :: [FName]
                     }
type SMCompiler = State CState

newCState :: CState
newCState = CState { funcs = []
                   , defs = [(DEFINE "$panic" [PVE "x"] (RETURN (CONS (ATOM "panic called") (PVE "x"))))]
                   , dispatch = []
                   }

getFuncName :: [Int] -> FName
getFuncName f = "$" <> (intercalate "." (map show f))

startFunc :: SMCompiler FName
startFunc = do
    fs <- gets funcs
    modify (\x -> x { funcs = ((head fs)+1):(tail fs) })
    return $ getFuncName fs

thisFunc :: SMCompiler FName
thisFunc = do
    f <- gets funcs
    return $ getFuncName f

nest :: SMCompiler ()
nest = modify (\x -> x { funcs = 0:(funcs x) })

unnest :: SMCompiler ()
unnest = modify (\x -> x { funcs = tail (funcs x) })

registerFunc :: FDef -> SMCompiler ()
registerFunc f = modify (\x -> x { defs = f:(defs x) })

registerDispatch :: FName -> SMCompiler ()
registerDispatch f = modify (\x -> x { dispatch = nub $ f:(dispatch x) })

compileMain :: Block -> SMCompiler Prog
compileMain block = do
    fname <- compileBlock (block ++ [Func "$exit", Exit])
    registerDispatch "$exit"
    generateDispatch
    fs <- gets defs
    return $ (DEFINE "$start" [PVE "arg"]
               (CALL fname [PVE "arg", CONS (ATOM "$exit") (ATOM "Nil")])
             ):fs

generateDispatch :: SMCompiler ()
generateDispatch = do
    names <- gets dispatch
    registerFunc $ DEFINE "$dispatch" [PVE "es", PVE "cs", PVA "f"] $ d names
  where
    d [] = (CALL "$panic" [ATOM "dispatch failed"])
    d (x:xs) = (ALT (EQA' (ATOM x) (PVA "f")) (CALL x [PVE "es", PVE "cs"]) (d xs))

compileBlock :: Block -> SMCompiler FName
compileBlock block = do
    nest
    fname <- thisFunc
    forM_ block compileInstr
    unnest
    return fname

compileInstr :: Instr -> SMCompiler FName
compileInstr instr = do
    fname <- startFunc
    cont <- thisFunc
    compileInstrHelper instr fname cont
    return fname

compileInstrHelper :: Instr -> FName -> FName -> SMCompiler ()
compileInstrHelper instr fname cont = cc
  where
    estack = PVE "es"
    cstack = PVE "cs"
    panic msg = CALL "$panic" [CONS (ATOM (msg <> " in " <> fname)) (CONS estack cstack)]
    pop z top rest body = (ALT (CONS' z top rest (PVA "!a")) body (panic "pop from empty list"))
    toAtom e a body = (ALT (CONS' e (PVE "!l") (PVE "!r") a) (panic "bad toAtom") body)
    reg code = registerFunc $ DEFINE fname [estack, cstack] code
    cc = do
      case instr of
        Push atom -> reg $
            (CALL cont [CONS (ATOM atom) estack, cstack])
        Cons -> reg $
            pop estack (PVE "l") (PVE "R") $
                pop (PVE "R") (PVE "r") (PVE "S") $
                    (CALL cont [CONS (CONS (PVE "l") (PVE "r")) (PVE "S"), cstack])
        Split -> reg $
            pop estack (PVE "x") (PVE "R") $
                pop (PVE "x") (PVE "h") (PVE "t") $
                    (CALL cont [CONS (PVE "h") (CONS (PVE "t") (PVE "R")), cstack])
        Test -> reg $
            pop estack (PVE "x") (PVE "R") $
                (ALT (CONS' (PVE "x") (PVE "!l") (PVE "!r") (PVE "!a"))
                    (CALL cont [CONS (ATOM "True") (PVE "R"), cstack])
                    (CALL cont [CONS (ATOM "False") (PVE "R"), cstack])
                )
        Eqa -> reg $
            pop estack (PVE "x") (PVE "R") $
                toAtom (PVE "x") (PVA "a") $
                    pop (PVE "R") (PVE "y") (PVE "S") $
                        toAtom (PVE "y") (PVA "b") $
                            (ALT (EQA' (PVA "a") (PVA "b"))
                                (CALL cont [CONS (ATOM "True") (PVE "S"), cstack])
                                (CALL cont [CONS (ATOM "False") (PVE "S"), cstack])
                            )
        Dup -> reg $
            pop estack (PVE "x") (PVE "R") $
                (CALL cont [CONS (PVE "x") estack, cstack])
        Dup2 -> reg $
            pop estack (PVE "x") (PVE "R") $
                pop (PVE "R") (PVE "y") (PVE "S") $
                    (CALL cont [CONS (PVE "y") estack, cstack])
        Drop -> reg $
            pop estack (PVE "x") (PVE "R") $
                (CALL cont [PVE "R", cstack])
        Swap -> reg $
            pop estack (PVE "l") (PVE "R") $
                pop (PVE "R") (PVE "r") (PVE "S") $
                    (CALL cont [CONS (PVE "r") (CONS (PVE "l") (PVE "S")), cstack])
        If block -> do
            tcont <- compileBlock block
            reg $
                pop estack (PVE "x") (PVE "R") $
                    toAtom (PVE "x") (PVA "a") $
                        (ALT (EQA' (ATOM "True") (PVA "a"))
                            (CALL tcont [PVE "R", cstack])
                            (CALL cont [PVE "R", cstack]))
        Call fn -> do
            registerDispatch cont
            reg $ (CALL fn [estack, CONS (ATOM cont) cstack])
        Return -> reg $
            pop cstack (PVE "x") (PVE "R") $
                toAtom (PVE "x") (PVA "a") $
                    (CALL "$dispatch" [estack, PVE "R", PVA "a"])
        Exit -> reg $
            pop estack (PVE "x") (PVE "R") $
                (RETURN (PVE "x"))
        Func fn -> do
            registerFunc (DEFINE fn [estack, cstack] $ CALL fname [estack, cstack])
            reg $ (CALL cont [estack, cstack])

compile :: Block  -> Prog
compile block = evalState (compileMain block) newCState
