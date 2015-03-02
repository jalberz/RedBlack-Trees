module DrawRBTree where

import List ((::))
import List
import Signal (Signal, (<~), (~))
import Signal
import Color
import Window
import Text as T
import Graphics.Input (button, customButton)
import Graphics.Element as E
import Graphics.Collage as C
import Time (Time, every, second, millisecond)
import Graphics.Input.Field as F
import Diagrams as D
import String as S
import Result as R

--Data types and aliases--------------


type alias State = { tree : RBTree, diagram : D.Diagram Tag, runState : RunState}

initState = {tree = E, diagram = D.empty, runState = Steady}




type RunState    = Steady | Inserting Int Time Time Time | Resetting Time Time Time | Balancing Int Time Time Time
                  

type Msg         = Insert Int | Reset | Noop 
type TickOr msg  = Tick | M msg
type alias Event = (Time, TickOr Msg)

--Red-Black Tree declarations----------

type Quarternary = Lesser | Greater | Same | Available
type Colour = R | B
type Glow = Glowing | Dark | Flash
type RBTree = E | T Colour Glow RBTree Int RBTree


--Channel function declarations-----------------------



ch : Signal.Channel Msg
ch = Signal.channel Noop

insertActivate i = Signal.send ch (Insert i) 
resetActivate = Signal.send ch Reset
noop   = Signal.send ch Noop

delay = 1.0 * second

inputValue : Signal.Channel F.Content
inputValue =
  Signal.channel F.noContent






--Red-Black basics------------------------------------------



member : Int -> RBTree -> Bool
member x t = case t of
  E -> False
  T _ _ l y r -> if
    | x == y    -> True
    | x <  y    -> member x l
    | otherwise -> member x r


--Inserting Functions-------------------------------------------

insertCheck : Int -> RBTree -> Quarternary
insertCheck x rb = case rb of
    E -> Available
    (T c g a y b) -> if | (x < y) -> Lesser
                        | (x > y) -> Greater
                        | (x == y) -> Same
                        | otherwise -> Available

--'glow' is used to help determine where in the tree we are located during insertion

glowCheck : RBTree -> Bool
glowCheck tree = case tree of
  E -> False
  T c g a y b -> case g of
                  Glowing -> True
                  Flash -> False
                  Dark -> (glowCheck a) || (glowCheck b) || False

bumpGlowNode : Int -> RBTree -> RBTree
bumpGlowNode i tree = 
  case tree of
    E -> T R Flash E i E
    T c g a y b -> case g of
                    Glowing -> case (insertCheck i tree) of
                                  Lesser -> T c Dark (insertGlow i a) y b
                                  Greater -> T c Dark a y (insertGlow i b)
                                  Available -> T R Flash E i E
                                  Same -> T c Flash a y b
                    Dark -> case ((glowCheck tree), (insertCheck i tree)) of
                                  (False,_) -> T c Glowing a y b
                                  (True, Lesser) -> T c g (bumpGlowNode i a) y b
                                  (True, Greater) -> T c g a y (bumpGlowNode i b)
                                  --can't be same since insertion would've stopped
                                  --can't be available since already tested for empty
                    Flash -> tree

--light up tree function

insertGlow : Int -> RBTree -> RBTree
insertGlow i tree = case tree of
  E -> T R Dark E i E
  T c g a y b -> T c Glowing a y b
  



insertStep : Int -> State -> Time -> State
insertStep i state now =
  let
    newtree = bumpGlowNode i state.tree
  in 
  let
    comparison = ((member i state.tree), (glowCheck newtree))
  in
    case comparison of
      (False, True) -> { state | tree <- newtree, runState <- Inserting i now now (now + delay)}
      (False, False) -> { state | tree <- newtree, runState <- Balancing i now now (now + delay) }
      (True, _) -> { state | runState <- Steady }





--Balancing Functions----------------------------------------------

balance : Colour -> RBTree -> Int -> RBTree -> RBTree
balance c l val r =
  case (c, l, val, r) of
    (B, T R _ (T R _ a x b) y c, z, d) -> T R Flash (T B Dark a x b) y (T B Dark c z d)
    (B, T R _ a x (T R _ b y c), z, d) -> T R Flash (T B Dark a x b) y (T B Dark c z d)
    (B, a, x, T R _ (T R _ b y c) z d) -> T R Flash (T B Dark a x b) y (T B Dark c z d)
    (B, a, x, T R _ b y (T R _ c z d)) -> T R Flash (T B Dark a x b) y (T B Dark c z d)
    _                              -> T c Flash l val r


balanceStep : Int -> State -> Time -> State
balanceStep i state now =
  let
    newtree = bumpFlashNode i state.tree
  in 
  let
    comparison = ((flashRoot newtree), (flashCheck newtree))
  in
    case comparison of
      (False, True) -> { state | tree <- newtree, runState <- Balancing i now now (now + delay)}
      (True, True) -> { state | tree <- (tidyRoot newtree), runState <- Steady }
      (False, False) -> { state | tree <- (tidyRoot newtree), runState <- Steady }


flashRoot : RBTree -> Bool
flashRoot tree = case tree of
  E -> False
  T c g a y b -> case g of
                  Flash -> True
                  _ -> False


tidyRoot : RBTree -> RBTree
tidyRoot tree = case tree of
  E -> E
  T c g a y b -> T B Dark a y b


flashCheck : RBTree -> Bool
flashCheck tree = case tree of
  E -> False
  T c g a y b -> case g of
                  Flash -> True
                  Dark -> (flashCheck a) || (flashCheck b) || False
                  Glowing -> False


grandchildCheck : RBTree -> Bool
grandchildCheck tree = case tree of
  E -> False
  T c g a y b -> case (a,b) of
                  (T R _ (T R _ _ _ _) _ _, _) -> True
                  (T R _ _ _ (T R _ _ _ _), _) -> True
                  (_, T R _ _ _ (T R _ _ _ _)) -> True
                  (_, T R _ (T R _ _ _ _) _ _) -> True
                  _                            -> False

bumpFlashNode : Int -> RBTree -> RBTree
bumpFlashNode i tree = case tree of 
  E -> E
  T c g a y b -> case g of
                  Flash -> T c Dark a y b
                  Dark -> case ((grandchildCheck tree), (insertCheck i tree)) of
                                  (True,_) -> balance c a y b
                                  (False, Lesser) -> T c g (bumpFlashNode i a) y b
                                  (False, Greater) -> T c g a y (bumpFlashNode i b)
                                  (False, Available) -> T c g a y b
                                  (False, Same) -> T c g a y b
                                  --can't be same since insertion would've stopped
                                  --can't be available since already tested for empty 


--The Upstate Function---------------------------------------------------

upstate : Event -> State -> State
upstate (now,tm) state = case (tm, state.runState) of
  (M Noop, _)          -> state
  (Tick, Steady)       -> state
  (M (Insert i), Steady)      -> { state | runState <- Inserting i now now (now + delay) }
  (Tick, Inserting v _ start end) -> if
    | now > end -> insertStep v state now
    | otherwise -> { state | runState <- Inserting v now start end }
  (Tick, Balancing v _ start end) -> if
    | now > end -> balanceStep v state now
    | otherwise -> { state | runState <- Balancing v now start end }
  (M Reset, Steady) -> {state | tree <- E}


--Visualization Functions--------------------------------------------------

type Dir = Left | Right

type Tag = NodeT | EdgeT | EmptyT

formNode : (Float,Float) -> RBTree -> D.Diagram Tag
formNode (x,y) (T c g a v b) = 
  let
    style = T.defaultStyle
  in
  let
    nodedia = case c of
                B -> D.circle 40 (C.Solid Color.black)
                R -> D.circle 40 (C.Solid Color.darkRed)
    outline = case g of
                Dark -> D.circle 50 (C.Solid Color.darkCharcoal)
                Glowing -> D.circle 50 (C.Solid Color.lightBlue)
                Flash -> D.circle 50 (C.Solid Color.lightYellow)
    figure = D.text (toString v) ({ style | color <- Color.white})
  in
    D.move (x,y) (D.group [figure, nodedia, outline])




formEdge : RBTree -> (Float, Float) -> Dir -> Float -> (Float, Float) -> D.Diagram Tag
formEdge t (x, y) d level (w,h) =
  case t of
    E -> D.empty --D.circle 1  (C.Solid Color.white) --small non-noticeable value
    T c g a v b -> case d of
                          Left -> D.path [(x,y), (x - 125/(2^(level)) - (0.01*w), y - 125 - (0.01*h))] lineStyle
                          Right -> D.path [(x,y), (x + 125/(2^(level)) + (0.01*w), y - 125 - (0.01*h))] lineStyle



recurseEdgesNodes : RBTree -> (Float,Float) -> (Int,Int) -> Int -> List (List C.Form)
recurseEdgesNodes t (x,y) (w,h) level=
  let
    l' = toFloat level
    w' = toFloat w
    h' = toFloat h
  in
    case t of
        E -> []
        T c g a v b -> let
                          newNode = D.render <| formNode (x, y) t
                          leftEdge = D.render <| formEdge a (x, y) Left l' (w',h')
                          rightEdge = D.render <| formEdge b (x, y) Right l' (w',h')
                       in
                          ([leftEdge, rightEdge, newNode]
                          ::
                          List.append (recurseEdgesNodes a (x-125/(2^l')-(0.01*w'), y - 125 - (0.01*h')) (w,h) (level + 1))
                                      (recurseEdgesNodes b (x+125/(2^l')+(0.01*w'), y - 125- (0.01*h')) (w,h) (level + 1)))


--other attempts at the visualization function... didnt work out unfortunately

{-}
recurseEdgesNodes : RBTree -> (Float,Float) -> Int -> D.Diagram Tag
recurseEdgesNodes t (x,y) level=
  let
    --x' = toFloat x
    --y' = toFloat y
    l' = toFloat level
  in
    case t of
        E -> D.circle 50  (C.Solid Color.white)
        T c g a v b -> let
                          newNode = formNode (x, y) t
                          leftEdge = formEdge a (x, y) Left l'
                          rightEdge = formEdge b (x, y) Right l'
                       in
                          (D.group [newNode, leftEdge, rightEdge]) `D.above`
                          (D.alignCenter <| (recurseEdgesNodes a (x-100/(2^l'), y - 100) (level + 1))
                          `D.beside` 
                          (recurseEdgesNodes b (x+100/(2^l'), y - 100) (level + 1)))-}

{-}
recurseEdgesNodes : RBTree -> (Int,Int) -> Int -> List (D.Diagram Tag)
recurseEdgesNodes t (x,y) level=
  let
    x' = toFloat x
    y' = toFloat y
    l' = toFloat level
  in
    case t of
        E -> []
        T c g a y b -> ((formNode (x', y') t) `D.above` 
                        (D.alignCenter <| (formEdge a (x', y') Left l') `D.beside` (formEdge b (x', y') Right l')))
                        ::
                        (List.append (recurseEdgesNodes a (x-100//(2^level), y - 100) (level + 1))
                                    (recurseEdgesNodes b (x+100//(2^level), y - 100) (level + 1)))-}


--Button mechanics---------------------------------------------------


strStyle : String -> E.Element
strStyle = T.fromString >> T.height 20 >> T.centered

strStyle2 : String -> E.Element
strStyle2 = T.fromString
             >> T.height 12 
             >> T.italic
             >> T.typeface [ "sans-serif", "sans serif", "gothic", "san serif", "helvetica"]
             >>T.leftAligned

lineStyle =
  let ls = C.defaultLine in
    { ls | color <- Color.darkCharcoal,
           width <- 10 }

fieldStyle : F.Style
fieldStyle =
  let fs = F.defaultStyle in
  let ts = T.defaultStyle in
    { fs | style <- { ts | height <- Just 20 }}

wBtn = 150
hBtn = 50

vSep = E.spacer 1 10

--basics for button tweaked from 1/28 Lecture

myButton enabled evt s =
  let mkBtn c =
    C.collage wBtn hBtn [
        C.filled c (C.rect wBtn hBtn)
      , C.outlined lineStyle (C.rect wBtn hBtn)
      , strStyle s |> C.toForm
    ]
  in
  let (x,y,z) =
    if | enabled   -> (Color.lightBlue, Color.blue, Color.orange)
       | otherwise -> (Color.lightRed, Color.lightRed, Color.lightRed)
  in
  customButton evt (mkBtn x) (mkBtn y) (mkBtn z)


--control button characteristics based on state
maybeButton b evt s = if
  | b         -> myButton True evt s
  | otherwise -> myButton False noop s

--helpers-----------------------------------------------------

sizeTree : RBTree -> Int
sizeTree tree = case tree of
  E -> 0
  T c g a y b -> 1 + (sizeTree a) + (sizeTree b)


parseStr : String -> Int
parseStr s = case ( R.toMaybe <| S.toInt s) of
  Just x -> x
  Nothing -> 0



--the View Function---------------------------------------------------


view : (Int, Int) -> F.Content -> State -> E.Element
view (w,h) cont state =
  let console =
       E.flow E.down
    <| List.intersperse vSep
         [ F.field fieldStyle (Signal.send inputValue) "" cont
         , maybeButton (state.runState == Steady && (sizeTree state.tree) /= 10) (insertActivate (parseStr cont.string)) "Insert"
         , maybeButton (state.runState == Steady) (resetActivate) "Reset"
         , strStyle2 "Red-Black Trees: \nInvariants:\n\t1) The tree obeys binary search order properties\n\t2) The root node must be black\n\t3) No red node may have a red child\n\t4) All paths from the root to an empty have an equal number of black trees\nNotes:\n\t-A blue halo represents a node
         that is being tested for equality.\n\t-A yellow halo represents a node that is undergoing rebalancing\n\t-Maximum of 10 nodes"
         ]
  in
  let 
    testTree = T.asText state
    diagramList = recurseEdgesNodes state.tree (0.0,150.0) (w,h) 0
    --formList = C.collage (w - 200) (h - 200) [(D.render <| D.showBBox <| diagramList)]
    --formList = C.collage (w//2) (h//2) [ D.render <| D.zcat (List.append (List.concatMap (List.take 2) diagramList) (List.concatMap (List.drop 2) diagramList))]
    renderedTree = C.collage (w - 350) (h - 350) (List.append (List.concatMap (List.take 2) diagramList) (List.concatMap (List.drop 2) diagramList))
    sizedElements = E.size (w - 300) (h - 300) renderedTree
  in
    E.color Color.grey <| E.container (w-5) (h-5) E.middle (E.flow E.right <| [sizedElements, console])


--Time & Signals, based on 1/28 Lecture--------------------------------------

mergeWithTicker : Time -> Signal msg -> Signal (Time, TickOr msg)
mergeWithTicker t sig =
  let time = every t in
  Signal.merge
    ((\t   -> (t, Tick)) <~ time)
    ((\t m -> (t, M m))  <~ Signal.sampleOn sig time ~ sig)

main : Signal E.Element
main =
  view <~ Window.dimensions
        ~ (Signal.subscribe inputValue)
        ~ Signal.foldp upstate initState
          (mergeWithTicker (100 * millisecond) (Signal.subscribe ch))
        
