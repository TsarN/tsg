module SM (Block, Instr(..), compileSM) where

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
           | Call FName
           | Return
           | Exit
           | Label FName
           | Jmp FName
           | CJmp FName
           | Locals Int
           | SetLocal Int
           | GetLocal Int
           deriving (Eq, Show)

data CState = CState { funcs :: Int
                     , defs :: [FDef]
                     , dispatch :: [FName]
                     }
type SMCompiler = State CState

newCState :: CState
newCState = CState { funcs = 0
                   , defs = [(DEFINE "$panic" [PVE "x"] (RETURN (CONS (ATOM "panic called") (PVE "x"))))]
                   , dispatch = []
                   }

getFuncName :: Int -> FName
getFuncName f = "$" <> (show f)

startFunc :: SMCompiler FName
startFunc = do
    fs <- gets funcs
    modify (\x -> x { funcs = fs + 1 })
    return $ getFuncName fs

thisFunc :: SMCompiler FName
thisFunc = do
    f <- gets funcs
    return $ getFuncName f

registerFunc :: FDef -> SMCompiler ()
registerFunc f = modify (\x -> x { defs = f:(defs x) })

registerDispatch :: FName -> SMCompiler ()
registerDispatch f = modify (\x -> x { dispatch = nub $ f:(dispatch x) })

compileMain :: Block -> SMCompiler Prog
compileMain block = do
    fname <- compileBlock (block ++ [Label "$exit", Exit])
    registerDispatch "$exit"
    generateDispatch
    fs <- gets defs
    return $ (DEFINE "$start" [PVE "arg"]
               (CALL fname [PVE "arg", CONS (CONS (ATOM "$exit") (ATOM "Nil")) (ATOM "Nil"), ATOM "Nil"])
             ):fs

generateDispatch :: SMCompiler ()
generateDispatch = do
    names <- gets dispatch
    registerFunc $ DEFINE "$dispatch" [PVE "es", PVE "cs", PVE "lv", PVA "f"] $ d names
  where
    d [] = (CALL "$panic" [ATOM "dispatch failed"])
    d (x:xs) = (ALT (EQA' (ATOM x) (PVA "f")) (CALL x [PVE "es", PVE "cs", PVE "lv"]) (d xs))

compileBlock :: Block -> SMCompiler FName
compileBlock block = do
    fname <- thisFunc
    forM_ block compileInstr
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
    estack = PVE "es" -- expression stack
    cstack = PVE "cs" -- call stack
    locals = PVE "lv" -- function locals

    panic msg = CALL "$panic" [ATOM (msg <> " in " <> fname)]
    pop z top rest body = (ALT (CONS' z top rest (PVA "_")) body (panic "pop from empty list"))
    toAtom e a body = (ALT (CONS' e (PVE "_") (PVE "_") a) (panic "bad toAtom") body)

    index z 0 var body =
        pop z var (PVE "_") body

    index z n var body =
        pop z (PVE "_") (PVE "!r") $
            index (PVE "!r") (n-1) var body

    setIndex z 0 val callback =
        pop z (PVE "_") (PVE "!r") $
            callback $ CONS val (PVE "!r")

    setIndex z n val callback =
        pop z (PVE ("!" <> show n)) (PVE "!r") $
            setIndex (PVE "!r") (n-1) val $ \v ->
                callback $ CONS (PVE ("!" <> show n)) v

    listOfNils 0 = ATOM "Nil"
    listOfNils n = CONS (ATOM "Nil") (listOfNils (n-1))

    reg code = registerFunc $ DEFINE fname [estack, cstack, locals] code

    cc = do
      case instr of
        Push atom -> reg $
            (CALL cont [CONS (ATOM atom) estack, cstack, locals])
        Cons -> reg $
            pop estack (PVE "l") (PVE "R") $
                pop (PVE "R") (PVE "r") (PVE "S") $
                    (CALL cont [CONS (CONS (PVE "l") (PVE "r")) (PVE "S"), cstack, locals])
        Split -> reg $
            pop estack (PVE "x") (PVE "R") $
                pop (PVE "x") (PVE "h") (PVE "t") $
                    (CALL cont [CONS (PVE "h") (CONS (PVE "t") (PVE "R")), cstack, locals])
        Test -> reg $
            pop estack (PVE "x") (PVE "R") $
                (ALT (CONS' (PVE "x") (PVE "!l") (PVE "!r") (PVE "!a"))
                    (CALL cont [CONS (ATOM "True") (PVE "R"), cstack, locals])
                    (CALL cont [CONS (ATOM "False") (PVE "R"), cstack, locals])
                )
        Eqa -> reg $
            pop estack (PVE "x") (PVE "R") $
                toAtom (PVE "x") (PVA "a") $
                    pop (PVE "R") (PVE "y") (PVE "S") $
                        toAtom (PVE "y") (PVA "b") $
                            (ALT (EQA' (PVA "a") (PVA "b"))
                                (CALL cont [CONS (ATOM "True") (PVE "S"), cstack, locals])
                                (CALL cont [CONS (ATOM "False") (PVE "S"), cstack, locals])
                            )
        Dup -> reg $
            pop estack (PVE "x") (PVE "R") $
                (CALL cont [CONS (PVE "x") estack, cstack, locals])
        Dup2 -> reg $
            pop estack (PVE "x") (PVE "R") $
                pop (PVE "R") (PVE "y") (PVE "S") $
                    (CALL cont [CONS (PVE "y") estack, cstack, locals])
        Drop -> reg $
            pop estack (PVE "x") (PVE "R") $
                (CALL cont [PVE "R", cstack, locals])
        Swap -> reg $
            pop estack (PVE "l") (PVE "R") $
                pop (PVE "R") (PVE "r") (PVE "S") $
                    (CALL cont [CONS (PVE "r") (CONS (PVE "l") (PVE "S")), cstack, locals])
        Call fn -> do
            registerDispatch cont
            reg $ (CALL fn [estack, CONS (CONS (ATOM cont) locals) cstack, ATOM "Nil"])
        Return -> reg $
            pop cstack (PVE "x") (PVE "R") $
                pop (PVE "x") (PVE "f") (PVE "l") $
                    toAtom (PVE "f") (PVA "a") $
                        (CALL "$dispatch" [estack, PVE "R", PVE "l", PVA "a"])
        Exit -> reg $
            pop estack (PVE "x") (PVE "R") $
                (RETURN (PVE "x"))
        Label fn -> do
            registerFunc (DEFINE fn [estack, cstack, locals] $ CALL fname [estack, cstack, locals])
            reg $ (CALL cont [estack, cstack, locals])
        Jmp fn -> reg $
            (CALL fn [estack, cstack, locals])
        CJmp fn -> reg $
            pop estack (PVE "x") (PVE "R") $
                toAtom (PVE "x") (PVA "a") $
                    (ALT (EQA' (ATOM "True") (PVA "a"))
                        (CALL fn [PVE "R", cstack, locals])
                        (CALL cont [PVE "R", cstack, locals]))
        Locals n -> reg $
            (CALL cont [estack, cstack, listOfNils n])
        SetLocal n -> reg $
            pop estack (PVE "x") (PVE "R") $
                setIndex locals n (PVE "x") $ \v ->
                    (CALL cont [PVE "R", cstack, v])
        GetLocal n -> reg $
            index locals n (PVE "x") $
                (CALL cont [CONS (PVE "x") estack, cstack, locals])

compileSM :: Block  -> Prog
compileSM block = evalState (compileMain block) newCState
