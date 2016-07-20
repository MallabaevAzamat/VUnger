module Test

open FStar.List.Tot

(*
let p = (1, 0)

val is_good_list: x:list (int * int) -> Tot (Bt:bool { Bt <==> contains (1, 0) x })
let rec is_good_list x =
    match x with
    | [] -> false
    | h::t -> if h = (1, 0) then true else is_good_list t

    (*| (1, 0) :: _ -> true
    | _ :: h ->*)

val is_very_good_list: list (int * int) -> Tot bool
let is_very_good_list g = is_good_list g

;;

assert(forall g . is_very_good_list g ==> contains (1, 0) g)
*)

open FStar.List.Tot

type term =
    | At: term
    | Bt: term
    | Ct: term
type unterm =
    | A: unterm
    | B: unterm
    | C: unterm
    | D: unterm
    | E: unterm

//val i2t: int -> Tot term
//val i2u: int -> Tot unterm

type rule =
    | Term of term
    | And of unterm * unterm
type def = unterm * rule
type grm = list def
type src = list term

type grm_def (u:unterm) (r:rule) (g:grm) = exists (d:def) . fst d = u /\ snd d = r /\ contains d g

assume AppendIts: forall (a:Type) (l:a) (r:a) .
    append [l] [r] = [l;r]

assume AppendH: forall (a:Type) (l:a) (r:list a) .
    append [l] r = l::r
    
assume AppendR: forall (a:Type) (l:list a) (r:a) .
    rev (append l [r]) = r::(rev l)

//assume AppendE: forall (a:Type) (l:list a)
//    length l > 1 <==> (exists (l1:list a) (l2:list a) . l = append l1 l2 /\ length l1 > 0 /\ length l2 > 0 /\ length l1 < length l /\ length l2 < length l /\ length l1 + length l2 = length l)


assume val unger_rule: grm -> rule -> src -> Tot bool

assume UngerTerm: forall (g:grm) (t:term) .
    {:pattern unger_rule g (Term t) [t]}
    unger_rule g (Term t) [t]

//assume UngerTermAnd: forall (g:grm) (u1:unterm) (u2:unterm) (t:term) (s:src) .
//    {:pattern unger_rule g () t /\ unger_rule g (And(u1, u2)) 
    
//assume UngerTermE: forall (g:grm) (t:term) .
//    {:pattern unger_rule g (Term t) [t]}
//    (exists s . s = [t] /\ unger_rule g (Term t) s)

assume UngerRule: forall (g:grm) (u1:unterm) (u2:unterm) (s1:src) (s2:src) .
    {:pattern unger_rule g (And(u1,u2)) (append s1 s2)}
    (exists (r1:rule) (r2:rule) .
        (grm_def u1 r1 g /\ grm_def u2 r2 g /\ unger_rule g r1 s1 /\ unger_rule g r2 s2)
    ) ==> unger_rule g (And(u1, u2)) (append s1 s2)

val get_rules_by_unterm: g:grm -> u:unterm -> Tot (list rule)
let rec get_rules_by_unterm g u =
    match g with
    | [] -> []
    | (v, r) :: o -> if u = v then r :: get_rules_by_unterm o u else get_rules_by_unterm o u

val unger: grm -> src -> Tot bool
let unger g s =
    match g with
    | [] -> false
    | (u, _)::_ -> existsb (fun r -> unger_rule g r s) (get_rules_by_unterm g u)

let a = assert(unger_rule [A, Term (At)] (Term (At)) [At])

let m'1 = assert(append [1] [1] = [1;1])
let m'2 = assert(append [1;1] [1] = [1;1;1])
let t'1 = assert(unger_rule [A, Term (At); A, And (A, A)] (Term (At)) [At])
let t'2 = assert(unger_rule [A, Term (At); A, And (A, A)] (And (A, A)) [At; At])

let t'3 = assert(unger [B, And (A, A); A, Term (At); A, And (B, A); B, Term (At)] [At; At; At; At; At])
let t'4 = assert(unger [A, Term (At); A, And (B, B); B, And (B, B); B, Term (At)] [At; At; At; At; At])
let x'4 = assert(unger [A, And(D, E); C, Term (Ct); D, Term (At); E, And(C, D)] [At; Ct; At])

let u_test4 = assert(unger [A, And(A, A); A, Term (At)] [At; At])
let u_test5 = assert(unger [A, And(A, B); A, Term (At); B, Term (At)] [At; At; At; At])

let unger_g_1111 = let g:grm = [A, And(A, A); A, Term (At)] in assert(unger g [At; At; At; At])

val ones: src -> Tot bool
let rec ones xs =
    match xs with
    | [] -> true
    | At::s -> ones s
    | _ -> false
    
//assume Ones: forall (s:src) .
//    ones s ==> ones (1::s)

//type ones (s:src) = forall k . contains k s <==> k = 1
let u_test4' = assert(forall s . ones s /\ length s = 1 ==> unger [A, And(A, A); A, Term (At)] s)
let u_test5' = assert(forall s . ones s /\ length s = 1 ==> unger [A, And(A, B); A, Term (At); B, Term (At)] s)

//let unger_e = let g1:grm = [1, Term 1; 1, And(1, 1)] in let g2:grm = [1, Term 1; 1, And(1, 2); 2, Term 1] in assert(forall s . unger g1 s <==> unger g2 s)


//let Bt'' = assert(forall t . (unger [1, Term 1; 2, And (1, 1); 2, Term 1] [t] = unger [1, Term 1; 2, And (2, 2); 2, Term 1] [t]))
//let eq' = assert(forall s . unger_rule [1, Term 1; 1, And (1, 1); 2, Term 1] (And (1, 1)) s <==> unger_rule [1, Term 1; 2, And (2, 2); 2, Term 1] (And (2, 2)) s)

//let e'' = assert(forall s . unger [1, Term 1; 2, Term 2; 3, And(1, 2)] s <==> 
  