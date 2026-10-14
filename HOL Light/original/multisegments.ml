needs "HOL Light/original/segments.ml";;
needs "HOL Light/utils.ml";;


(* Every list of segments is a valid representation of a multisegment. *)
let is_multisegment_rep = new_definition
  `(is_multisegment_rep : segment list -> bool) xs <=> T`;;


let MULTISEGMENT_EXISTS = prove
  (`?xs:segment list. is_multisegment_rep xs`,
   EXISTS_TAC `[]:segment list` THEN
   REWRITE_TAC[is_multisegment_rep]);;


(* Abstract type of multisegments. *)
let multisegment_tybij =
  new_type_definition
    "multisegment"
    ("mk_multisegment","segments_of")
    MULTISEGMENT_EXISTS;;


(* Number of segments in a multisegment. *)
let ms_length = new_definition
  `(ms_length : multisegment -> num) ms =
     LENGTH (segments_of ms)`;;


(* The segment at index i. *)
let segment_at = new_definition
  `(segment_at : multisegment -> num -> segment) ms i =
     EL i (segments_of ms)`;;


let is_nonempty_multisegment = new_definition
  `(is_nonempty_multisegment : multisegment -> bool) ms <=>
     ~(segments_of ms = [])`;;


(* Will have to introduce a lemma proving that the set is nonempty. *)
let depth = new_definition
  `(depth : multisegment -> num -> num option) ms i =
    if is_nonempty_multisegment ms /\ i < ms_length ms
    then SOME
      (max_set
        ({dep:num |
            dep < ms_length ms /\
            ?c:num list.
              LENGTH c = dep + 1 /\
              HD c = i /\                                                   //**
              ALL (\k. k < ms_length ms) c /\                               //**
              ALL2                                                          //**
                (\r s. precedes (EL ms r) (EL ms s))                        //**
                (BUTLAST c)                                                 //**
                (TL c)}))                                                   //**
    else NONE`;;



let d = new_definition
  `(d : multisegment -> num option) ms =
    if is_nonempty_multisegment ms
    then SOME
      (max_set
        ({x:num |
            ?i:num.
              i < ms_length ms /\
              depth ms i = SOME x}))
    else NONE`;;


let bucket = new_definition
  `(bucket : multisegment -> num -> num -> bool) ms dep =
     {i:num |
        i < ms_length ms /\
        depth ms i = SOME dep}`;;


(* Will have to introduce a lemma proving existence. *)
let admissible_enumeration = new_definition
  `(admissible_enumeration :
      multisegment -> num -> (num list) option) ms k =
    if is_nonempty_multisegment ms /\
       (?dm:num. d ms = SOME dm /\ k <= dm)
    then SOME
      (@e:num list.
          {i:num | MEM i e} = bucket ms k /\
          (!p q.
             p < LENGTH e /\
             q < LENGTH e /\
             EL p e = EL q e
             ==> p = q) /\
          ALL (\i. i < ms_length ms) e /\
          ALL2
            (\r s.
               seg_subset_eq
                 (segment_at ms r)
                 (segment_at ms s))
            (BUTLAST e)
            (TL e))
    else NONE`;;


(* Returns an admissible enumeration of i's depth bucket
   together with i's position in it. *)
let p_and_enumeration = new_definition
  `(p_and_enumeration :
      multisegment -> num -> ((num list)#num) option) ms i =
    if is_nonempty_multisegment ms /\ i < ms_length ms
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
  `(ivee : multisegment -> num -> num option) ms i =
    if is_nonempty_multisegment ms /\ i < ms_length ms
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
      multisegment -> num -> segment option) ms i =
    if is_nonempty_multisegment ms /\ i < ms_length ms
    then
      let j = @j:num. ivee ms i = SOME j in
      SOME
        (mk_segment
          (segment_begin (segment_at ms i),
           segment_end (segment_at ms j)))
    else NONE`;;


(* ================================================ *)
(* 1. FIRST LEADING INDEX                           *)
(* ================================================ *)

(* An admissible first index has the smallest       *)
(* segment beginning, and among those, the          *)
(* smallest segment end.                            *)

let MW_FIRST_CANDIDATE = new_definition
  `MW_FIRST_CANDIDATE (ms:multisegment) (i:num) <=>
     i < ms_length ms /\
     (!j. j < ms_length ms
          ==> segment_begin (segment_at ms i) <=
              segment_begin (segment_at ms j)) /\
     (!j. j < ms_length ms /\
          segment_begin (segment_at ms j) =
          segment_begin (segment_at ms i)
          ==> segment_end (segment_at ms i) <=
              segment_end (segment_at ms j))`;;


let MW_FIRST = new_definition
  `MW_FIRST (ms:multisegment) =
     @i:num. MW_FIRST_CANDIDATE ms i`;;


(* ================================================ *)
(* 2. ELIGIBLE NEXT INDEX                           *)
(* ================================================ *)

(* j is eligible to follow i if:                    *)
(* - both indices are valid;                        *)
(* - the beginning increases by exactly one;        *)
(* - the ending increases strictly.                 *)

let MW_NEXT_ELIGIBLE = new_definition
  `MW_NEXT_ELIGIBLE
     (ms:multisegment) (i:num) (j:num) <=>
     i < ms_length ms /\
     j < ms_length ms /\
     segment_begin (segment_at ms j) =
       segment_begin (segment_at ms i) + &1 /\
     segment_end (segment_at ms i) <
       segment_end (segment_at ms j)`;;


(* Of all eligible next indices, choose one whose   *)
(* segment ending is minimal.                       *)

let MW_NEXT_CANDIDATE = new_definition
  `MW_NEXT_CANDIDATE
     (ms:multisegment) (i:num) (j:num) <=>
     MW_NEXT_ELIGIBLE ms i j /\
     (!r. MW_NEXT_ELIGIBLE ms i r
          ==> segment_end (segment_at ms j) <=
              segment_end (segment_at ms r))`;;


let MW_HAS_NEXT = new_definition
  `MW_HAS_NEXT (ms:multisegment) (i:num) <=>
     ?j. MW_NEXT_CANDIDATE ms i j`;;


let MW_NEXT = new_definition
  `MW_NEXT (ms:multisegment) (i:num) =
     @j:num. MW_NEXT_CANDIDATE ms i j`;;


(* ================================================ *)
(* 3. RECURSIVE MW WALK                              *)
(* ================================================ *)

(* Construct the sequence of leading indices.      *)
(* The parameter fuel bounds recursive transitions. *)

let MW_WALK = define
  `(MW_WALK (ms:multisegment) (i:num) 0 = [i]) /\
   (MW_WALK ms i (SUC fuel) =
      if MW_HAS_NEXT ms i
      then CONS i
        (MW_WALK ms (MW_NEXT ms i) fuel)
      else [i])`;;


(* ================================================ *)
(* 4. COMPLETE LEADING-INDEX SEQUENCE               *)
(* ================================================ *)

(* Starting at MW_FIRST, at most ms_length ms - 1   *)
(* transitions are needed for a nonempty ms.        *)

let MW_LEADING_INDICES = new_definition
  `MW_LEADING_INDICES (ms:multisegment) =
     if is_nonempty_multisegment ms
     then MW_WALK ms (MW_FIRST ms)
             (ms_length ms - 1)
     else []`;;


(* ================================================ *)
(* 5. LEADING-INDEX SET I*                          *)
(* ================================================ *)

let MW_LEADING_SET = new_definition
  `MW_LEADING_SET (ms:multisegment) =
     {i:num | MEM i (MW_LEADING_INDICES ms)}`;;


(* ================================================ *)
(* 6. THE SEGMENT DELTA-CIRCLE                      *)
(* ================================================ *)

(* Delta-circle(ms) =                            *)
(* [min(ms), min(ms) + k - 1],                    *)
(* where k is the number of leading indices.     *)

let MW_DELTA = new_definition
  `MW_DELTA (ms:multisegment) =
     if is_nonempty_multisegment ms
     then SOME
       (mk_segment
         (segment_begin
            (segment_at ms (MW_FIRST ms)),
          segment_begin
            (segment_at ms (MW_FIRST ms)) +
              &(LENGTH (MW_LEADING_INDICES ms) - 1)))
     else NONE`;;
