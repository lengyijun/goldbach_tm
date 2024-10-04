def join : List String → String
  | []      => ""
  | a :: [] => a
  | a :: b :: bs => a ++ " " ++ join (b :: bs)
