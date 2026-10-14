let max_set = new_definition
  `max_set s = @m:num.
      m IN s /\ (!n. n IN s ==> n <= m)`;;



let set_to_list = new_definition
  `(set_to_list : (A -> bool) -> A list) (s:A->bool) =
       @l:A list.
         {x:A | MEM x l} = s /\
         (!p q:num.
            p < LENGTH l /\ q < LENGTH l /\
            EL p l = EL q l
            ==> p = q)`;;