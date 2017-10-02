{-@ LIQUID "--exactdc"                                  @-}
{-@ LIQUID "--higherorder"                              @-}

module Label where

-- type Label = Integer -- JP: Do we need a different type for a partial order?

data Label = 
    LabelAMeetB 
  | LabelA 
  | LabelB 
  | LabelAJoinB
  deriving (Eq, Show)

{-@ reflect canFlowTo @-}
canFlowTo :: Label -> Label -> Bool
canFlowTo _ LabelAJoinB = True
canFlowTo LabelAJoinB _ = False
canFlowTo LabelA LabelA = True
canFlowTo LabelAMeetB LabelA = True
canFlowTo LabelB LabelA = False
canFlowTo LabelB LabelB = True
canFlowTo LabelAMeetB LabelB = True
canFlowTo LabelA LabelB = False
canFlowTo LabelAMeetB LabelAMeetB = True
canFlowTo LabelA LabelAMeetB = False
canFlowTo LabelB LabelAMeetB = False
-- canFlowTo x y | x == y = True

{-@ reflect join @-}
join :: Label -> Label -> Label
join LabelAJoinB _ = LabelAJoinB
join _ LabelAJoinB = LabelAJoinB
join LabelA LabelB = LabelAJoinB
join LabelA LabelA = LabelA
join LabelA LabelAMeetB = LabelA
join LabelB LabelA = LabelAJoinB
join LabelB LabelB = LabelB
join LabelB LabelAMeetB = LabelB
join LabelAMeetB LabelA = LabelA
join LabelAMeetB LabelB = LabelB
join LabelAMeetB LabelAMeetB = LabelAMeetB

{-@ reflect meet @-}
meet :: Label -> Label -> Label
meet LabelAMeetB _ = LabelAMeetB
meet _ LabelAMeetB = LabelAMeetB
meet LabelA LabelB = LabelAMeetB
meet LabelA LabelA = LabelA
meet LabelA LabelAJoinB = LabelA
meet LabelB LabelA = LabelAMeetB
meet LabelB LabelB = LabelB
meet LabelB LabelAJoinB = LabelB
meet LabelAJoinB v = v

{-@ reflect bottom @-}
bottom :: Label
bottom = LabelAMeetB
