
needs "HOL Light/original/segments.ml";;
needs "HOL Light/utils.ml";;


let ms_eq = new_definition
  `(ms_eq : segment list -> segment list -> bool) ms1 ms2 <=>
     !s:segment.
       LENGTH (FILTER (\t. t = s) ms1) =
       LENGTH (FILTER (\t. t = s) ms2)`;;



(* Will have to introduce a lemma proving that the set is nonempty. *)
let depth = new_definition
  `(depth : segment list -> num -> num option) ms i =
    if ~(ms = []) /\ i < LENGTH ms
    then SOME
      (max_set
        ({dep:num |
            dep < LENGTH ms /\
            ?c:num list.
              LENGTH c = dep + 1 /\
              HD c = i /\
              ALL (\k. k < LENGTH ms) c /\
              ALL2
                (\r s. precedes (EL r ms) (EL s ms))
                (BUTLAST c)
                (TL c)}))
    else NONE`;;



let d = new_definition
  `(d : segment list -> num option) ms =
    if ~(ms = [])
    then SOME
      (max_set
        ({x:num |
            ?i:num.
              i < LENGTH ms /\
              depth ms i = SOME x}))
    else NONE`;;


let bucket = new_definition
  `(bucket : segment list -> num -> num -> bool) ms dep =
     {i:num |
        i < LENGTH ms /\
        depth ms i = SOME dep}`;;


(* Will have to introduce a lemma proving existence. *)
let admissible_enumeration = new_definition
  `(admissible_enumeration :
      segment list -> num -> (num list) option) ms k =
    if ~(ms = []) /\
       (?dm:num. d ms = SOME dm /\ k <= dm)
    then SOME
      (@e:num list.
          {i:num | MEM i e} = bucket ms k /\
          (!p q.
             p < LENGTH e /\
             q < LENGTH e /\
             EL p e = EL q e
             ==> p = q) /\
          ALL (\i. i < LENGTH ms) e /\
          ALL2
            (\r s.
               seg_subset_eq
                 (EL r ms)
                 (EL s ms))
            (BUTLAST e)
            (TL e))
    else NONE`;;


(* Returns an admissible enumeration of i's depth bucket
   together with i's position in it. *)
let p_and_enumeration = new_definition
  `(p_and_enumeration :
      segment list -> num -> ((num list)#num) option) ms i =
    if ~(ms = []) /\ i < LENGTH ms
    then
      let k = @k:num. depth ms i = SOME k in
      let e =
        @e:num list.
          admissible_enumeration ms k = SOME e
      in
      SOME
        (e,
         @p:num.
           p < LENGTH e /\
           EL p e = i)
    else NONE`;;


let ivee = new_definition
  `(ivee : segment list -> num -> num option) ms i =
    if ~(ms = []) /\ i < LENGTH ms
    then
      let ep =
        @ep:(num list)#num.
          p_and_enumeration ms i = SOME ep
      in
      let e = FST ep in
      let p = SND ep in
      SOME
        (if p + 1 < LENGTH e
         then EL (p + 1) e
         else HD e)
    else NONE`;;


(* Delta'_i = [b(Delta_i), e(Delta_(i^vee))]. *)
let delta_prime = new_definition
  `(delta_prime :
      segment list -> num -> segment option) ms i =
    if ~(ms = []) /\ i < LENGTH ms
    then
      let j = @j:num. ivee ms i = SOME j in
      SOME
        (mk_segment
          (segment_begin (EL i ms),
           segment_end (EL j ms)))
    else NONE`;;


(* ================================================ *)
(* 1. FIRST LEADING INDEX                           *)
(* ================================================ *)

(* An admissible first index has the smallest       *)
(* segment beginning, and among those, the          *)
(* smallest segment end.                            *)

let MW_FIRST_CANDIDATE = new_definition
  `(MW_FIRST_CANDIDATE : segment list -> num -> bool)
     (ms:segment list) (i:num) <=>
     i < LENGTH ms /\
     (!j:num. j < LENGTH ms
          ==> segment_begin (EL i ms) <=
              segment_begin (EL j ms)) /\
     (!j:num. j < LENGTH ms /\
          segment_begin (EL j ms) =
          segment_begin (EL i ms)
          ==> segment_end (EL i ms) <=
              segment_end (EL j ms))`;;


let MW_FIRST = new_definition
  `(MW_FIRST : segment list -> num)
     (ms:segment list) =
     @i:num. MW_FIRST_CANDIDATE ms i`;;


(* ================================================ *)
(* 2. ELIGIBLE NEXT INDEX                           *)
(* ================================================ *)

(* j is eligible to follow i if:                    *)
(* - both indices are valid;                        *)
(* - the beginning increases by exactly one;        *)
(* - the ending increases strictly.                 *)

let MW_NEXT_ELIGIBLE = new_definition
  `(MW_NEXT_ELIGIBLE : segment list -> num -> num -> bool)
     (ms:segment list) (i:num) (j:num) <=>
     i < LENGTH ms /\
     j < LENGTH ms /\
     segment_begin (EL j ms) =
       segment_begin (EL i ms) + &1 /\
     segment_end (EL i ms) <
       segment_end (EL j ms)`;;


(* Of all eligible next indices, choose one whose   *)
(* segment ending is minimal.                       *)

let MW_NEXT_CANDIDATE = new_definition
  `(MW_NEXT_CANDIDATE : segment list -> num -> num -> bool)
     (ms:segment list) (i:num) (j:num) <=>
     MW_NEXT_ELIGIBLE ms i j /\
     (!r:num. MW_NEXT_ELIGIBLE ms i r
          ==> segment_end (EL j ms) <=
              segment_end (EL r ms))`;;


let MW_HAS_NEXT = new_definition
  `(MW_HAS_NEXT : segment list -> num -> bool)
     (ms:segment list) (i:num) <=>
     ?j:num. MW_NEXT_CANDIDATE ms i j`;;


let MW_NEXT = new_definition
  `(MW_NEXT : segment list -> num -> num)
     (ms:segment list) (i:num) =
     @j:num. MW_NEXT_CANDIDATE ms i j`;;


(* ================================================ *)
(* 3. RECURSIVE MW WALK                             *)
(* ================================================ *)

(* Construct the sequence of leading indices.       *)
(* The parameter max_steps bounds recursive transitions. *)

let MW_WALK = define
  `((MW_WALK : segment list -> num -> num -> num list)
       (ms:segment list) (i:num) 0 = [i]) /\
   ((MW_WALK : segment list -> num -> num -> num list)
       ms i (SUC (max_steps:num)) =
      if MW_HAS_NEXT ms i
      then CONS i
        (MW_WALK ms (MW_NEXT ms i) max_steps)
      else [i])`;;


(* ================================================ *)
(* 4. COMPLETE LEADING-INDEX SEQUENCE               *)
(* ================================================ *)

(* Starting at MW_FIRST, at most LENGTH ms - 1      *)
(* transitions are needed for a nonempty ms.        *)

let MW_LEADING_INDICES = new_definition
  `(MW_LEADING_INDICES : segment list -> num list)
     (ms:segment list) =
     if ~(ms = [])
     then MW_WALK ms (MW_FIRST ms)
             (LENGTH ms - 1)
     else []`;;


(* ================================================ *)
(* 5. LEADING-INDEX SET I*                          *)
(* ================================================ *)

let MW_LEADING_SET = new_definition
  `(MW_LEADING_SET : segment list -> num -> bool)
     (ms:segment list) =
     {i:num | MEM i (MW_LEADING_INDICES ms)}`;;


(* ================================================ *)
(* 6. THE SEGMENT DELTA-CIRCLE                      *)
(* ================================================ *)

(* Delta-circle(ms) =                            *)
(* [min(ms), min(ms) + k - 1],                    *)
(* where k is the number of leading indices.     *)

let DELTA_circle = new_definition
  `DELTA_circle (ms:segment list) =
     if ~(ms = [])
     then SOME
       (mk_segment
         (segment_begin (EL (MW_FIRST ms) ms),
          segment_begin (EL (MW_FIRST ms) ms) +
            &(LENGTH (MW_LEADING_INDICES ms) - 1)))
     else NONE`;;



let DELTA_STAR = new_definition
  `DELTA_STAR (ms:segment list) (i:num) =
     if i IN MW_LEADING_SET ms
     then truncate_left (EL i ms)
     else SOME (EL i ms)`;;



let MW_DAGGER = new_definition
  `MW_DAGGER (ms:segment list) =
     MAP
       (\x:segment option. @s:segment. x = SOME s)
       (FILTER
         (\x:segment option. ~(x = NONE))
         (list_of_seq
           (\i. DELTA_STAR ms i)
           (LENGTH ms)))`;;



let l = new_definition
  `(l : segment list -> segment list) ms =
     if ms = [] then []
     else
       let dm = @k:num. d ms = SOME k in
       list_of_seq
         (\k:num.
            let e = @e:num list.
              admissible_enumeration ms k = SOME e
            in
            let i = LAST e in
            @s:segment. delta_prime ms i = SOME s)
         (dm + 1)`;;


let m_prime = new_definition
  `(m_prime : segment list -> segment list) ms =
     MAP
       (\i:num.
          @s:segment. delta_prime ms i = SOME s)
       (FILTER
         (\i:num.
            ?e:num list. ?p:num.
              p_and_enumeration ms i = SOME (e,p) /\
              p + 1 < LENGTH e)
         (list_of_seq (\i:num. i) (LENGTH ms)))`;;


let ms_min = new_definition
  `(ms_min : segment list -> int) ms =
     if ms = [] then &0
     else
       @a:int.
         (?i:num.
            i < LENGTH ms /\
            a = segment_begin (EL i ms)) /\
         (!j:num.
            j < LENGTH ms
            ==> a <= segment_begin (EL j ms))`;;



let COROLLARY =
  `!ms:segment list.
     ~(ms = []) /\
     ms_min ms < ms_min (l ms)
     ==>
       ms_eq (l ms) (l (MW_DAGGER ms)) /\
       DELTA_circle ms = DELTA_circle (m_prime ms) /\
       ms_eq (m_prime (MW_DAGGER ms))
             (MW_DAGGER (m_prime ms))`;;



