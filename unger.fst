module Unger

//#set-options "--print_fuels --initial_fuel 1 --initial_ifuel 1 --max_fuel 32 --max_ifuel 8"
type array (a:Type) (#len:nat) = x:nat {x < len} -> Tot a

let splice'array
    (#a:Type)
    (#len:nat)
    (arr:array a #len)
    (f:nat)
    (t:nat {f <= t /\ t <= len})
    : Tot (array a #(t - f)) =
        (fun x -> arr (x + f))

let split'array
    (#a:Type)
    (#len:nat)
    (arr:array a #len)
    (n:nat {n <= len})
    : Tot (array a #n * array a #(len - n)) =
        splice'array arr 0 n, splice'array arr n len

let merge'array
    (#a:Type)
    (#len1:nat)
    (#len2:nat)
    (arr1:array a #len1)
    (arr2:array a #len2)
    : Tot (array a #(len1 + len2)) =
        fun x ->
            if x < len1 then arr1 x else arr2 (x - len1)

let split_merge_lemma
    (#a:Type {hasEq a})
    (#len:nat)
    (arr:array a #len)
    (n:nat {n <= len})
    : Lemma
        (requires True)
        (ensures (forall x . let (l, r) = split'array arr n in (merge'array l r) x = arr x)) = ()

let merge_split_lemma
    (#a:Type {hasEq a})
    (#len1:nat)
    (#len2:nat)
    (arr1:array a #len1)
    (arr2:array a #len2)
    : Lemma
        (requires True)
        (ensures (forall x y . let (l, r) = split'array (merge'array arr1 arr2) len1 in l x = arr1 x /\ r y = arr2 y)) = ()

let map'array (#a:Type) (#b:Type) (#len:nat) (xs:array a #len) (f:a -> Tot b): Tot (array b #len) = fun x -> f (xs x)

type container (a:Type) = a -> Tot bool

let empty'container (#a:Type): Tot (container a) = fun _ -> false
let add'container'item (#a:Type {hasEq a}) (xs:container a) (it:a): Tot (container a) = fun x -> (if x = it then true else xs x)
let union'containers (#a:Type) (xs:container a) (ys:container a): Tot (container a) = fun x -> xs x || ys x
let intersect'containers (#a:Type) (xs:container a) (ys:container a): Tot (container a) = fun x -> xs x && ys x
let xor'containers (#a:Type) (xs:container a) (ys:container a): Tot (container a) = fun x -> (not (xs x && ys x)) && (xs x || ys x)

let rec container_of_array (#a:Type {hasEq a}) (#len:nat) (arr:array a #len): Tot (container a) =
    if len = 0 then empty'container else add'container'item (container_of_array #a #(len - 1) (splice'array arr 1 len)) (arr 0)

let contains'array (#a:Type {hasEq a}) (#len:nat) (arr:array a #len) (it:a): Tot bool =
    (container_of_array arr) it

type full'array (a:Type {hasEq a}) (#len:nat) =
    arr:array a #len {forall (it:a) . contains'array arr it <==> (it:a)}

type counter (a:Type) = a -> Tot nat
let empty'counter (#a:Type): Tot (counter a) = fun _ -> 0
let add'counter'item (#a:Type {hasEq a}) (xs:counter a) (it:a): Tot (counter a) = fun x -> (if x = it then 1 else 0) + xs x

let rec counter_of_array (#a:Type {hasEq a}) (#len:nat) (arr:array a #len): Tot (counter a) =
    if len = 0 then empty'counter else add'counter'item (counter_of_array #a #(len - 1) (splice'array arr 1 len)) (arr 0)

let count'array (#a:Type {hasEq a}) (#len:nat) (arr:array a #len) (it:a): Tot nat =
    (counter_of_array arr) it

type set (a:Type {hasEq a}) (#len:nat) = xs:array a #len { forall x . count'array xs x < 2 }

type full'set (a:Type {hasEq a}) (#len:nat) =
    arr:set a #len {forall (it:a) . contains'array arr it <==> (it:a)}

let rec for_all'nat
    (to':nat)
    (a:x:nat {x < to'} -> Tot bool):
    Tot bool =
    if to' = 0 then true else for_all'nat (to' - 1) a && a (to' - 1)

let rec exists'nat
    (to':nat)
    (a:x:nat {x < to'} -> Tot bool):
    Tot bool =
    if to' = 0 then false else exists'nat (to' - 1) a || a (to' - 1)

let for_all'array (#a:Type {hasEq a}) (#n:nat) (arr:array a #n) (p:a -> Tot bool): Tot bool =
    for_all'nat n (fun i -> p (arr i))

let rec for_all'arrays (#a:Type {hasEq a}) (#n:nat) (arr:full'array a #n) (#g:nat) (p:array a #g -> Tot bool): Tot bool =
    if g = 0 then true else for_all'arrays #a #n arr #(g - 1) (fun x -> for_all'array #a #n arr (fun t -> p (fun i -> if i = g - 1 then t else x i)))

type term =
    | A | B

let terms'set: full'set term #2 =
    let terms'array: full'array term #2 =
        fun (x:nat{x < 2}) ->
            match x with
            | 0 -> A
            | 1 -> B in
    terms'array

type unterm =
    | N | K

let unterms'set: full'set unterm #2 =
    let unterms'array: full'array unterm #2 =
        fun (x:nat{x < 2}) ->
            match x with
            | 0 -> N
            | 1 -> K in
    unterms'array

type source (#len:nat { len > 0 }) = array term #len

type rule (#len:nat) (#unterms:set unterm #len) =
    | Term of term
    | Unterm of u:unterm {contains'array unterms u}
    | And of rule #len #unterms * rule #len #unterms
    | Or of rule #len #unterms * rule #len #unterms

type dictionary (key_type:Type {hasEq key_type}) (value_type: Type) (#keys_len:nat) (#keys:set key_type #keys_len) = (x:key_type {contains'array keys x} -> Tot value_type)

type grammar (#unterms_count:nat) (#unterms:set unterm #unterms_count) = dictionary unterm (rule #unterms_count #unterms) #unterms_count #unterms

assume val unger_rule: #unterms_count:nat
                    -> #unterms:set unterm #unterms_count
                    -> grm:grammar #unterms_count #unterms
                    -> r:rule #unterms_count #unterms
                    -> #source_length:nat {source_length > 0}
                    -> s:source #source_length
                    -> Tot bool

assume UngerRuleTerm:
    forall (unterms_count:nat) (unterms:set unterm #unterms_count) (g:grammar #unterms_count #unterms) (t:term) (l:nat {l > 0}) (s:source #l) .
    {:pattern unger_rule g (Term t) s}
    unger_rule g (Term t) s <==> (l = 1 /\ t = s 0)

assume UngerRuleUnterm:
    forall (unterms_count:nat) (unterms:set unterm #unterms_count) (g:grammar #unterms_count #unterms) (u:unterm {contains'array unterms u}) (l:nat {l > 0}) (s:source #l) .
    {:pattern unger_rule g (Unterm u) s}
    (unger_rule g (Unterm u) s <==> unger_rule g (g u) s)

assume UngerRuleOr:
    forall (unterms_count:nat) (unterms:set unterm #unterms_count) (g:grammar #unterms_count #unterms) (r1:rule #unterms_count #unterms) (r2:rule #unterms_count #unterms) (l:nat {l > 0}) (s:source #l) .
    {:pattern unger_rule g (Or (r1, r2)) s}
    unger_rule g (Or (r1, r2)) s <==> unger_rule g r1 s \/ unger_rule g r2 s

assume UngerRuleAnd:
    forall (unterms_count:nat) (unterms:set unterm #unterms_count) (g:grammar #unterms_count #unterms) (r1:rule #unterms_count #unterms) (r2:rule #unterms_count #unterms) (l:nat {l > 0}) (s:source #l) .
    {:pattern unger_rule g (And (r1, r2)) s}
    (forall  (n:nat {n > 0 /\ n < l}) . unger_rule g r1 (splice'array s 0 n) /\ unger_rule g r2 (splice'array s n l) ==> unger_rule g (And (r1, r2)) s)
    /\ (exists (n:nat {n > 0 /\ n < l}) . unger_rule g (And (r1, r2)) s ==> unger_rule g r1 (splice'array s 0 n) /\ unger_rule g r2 (splice'array s n l))

(*
assume UngerRuleAnd:
    forall (unterms_count:nat) (unterms:set unterm #unterms_count) (g:grammar #unterms_count #unterms) (r1:rule #unterms_count #unterms) (r2:rule #unterms_count #unterms) (l:nat {l > 1}) (s:source #l) .
    {:pattern unger_rule g (And (r1, r2)) s}  //-----------------------------------------------------------------------------------------------------------
    forall (n:nat) . n < l /\ n > 0 ==> (
        let ll = fst (split'array #term #l s n) in
        let rr = snd (split'array #term #l s n) in
        unger_rule #unterms_count #unterms g r1 #n ll /\ unger_rule #unterms_count #unterms g r2 #(l - n) rr ==> unger_rule #unterms_count #unterms g (And (r1, r2)) #l s)
*)

(*
let unterms: set unterm #2 = (fun x -> if x = 1 then K else N)
let rA: rule #2 #unterms = Term A
let rB: rule #2 #unterms = Term B
let rN: rule #2 #unterms = Unterm N
let rK: rule #2 #unterms = Unterm K
let rZ: rule #2 #unterms = And (rA, rK)
let rY: rule #2 #unterms = And (rA, rN)
let rX: rule #2 #unterms = Or (rA, rY)
let rW: rule #2 #unterms = Or (rA, rZ)
let grm1: grammar #2 #unterms = (fun x -> if x = N then rX else rN)
let grm2: grammar #2 #unterms = (fun x -> if x = N then rK else rW)
//let unger (#unterms_count:nat) (#unterms:set unterm #unterms_count) (g:grammar #unterms_count #unterms) (#roots_count: nat) (#roots: array (u:unterm {contains'array unterms u})) (#l:nat) (s:source #l) =
    //existsb (fun u -> unger_rule unterms sg (sg u) s) roots
*)
let grammarEqualsBySrcf
    (#uc1:nat)
    (#us1:set unterm #uc1)
    (g1:grammar #uc1 #us1)
    (r1:rule #uc1 #us1)
    (#uc2:nat)
    (#us2:set unterm #uc2)
    (g2:grammar #uc2 #us2)
    (r2:rule #uc2 #us2)
    (#n:nat{n>0})
    (s:source #n): Tot bool =
    unger_rule #uc1 #us1 g1 r1 #n s = unger_rule #uc2 #us2 g2 r2 #n s

let grammarEqualsByNSrcf
    (#uc1:nat)
    (#us1:set unterm #uc1)
    (g1:grammar #uc1 #us1)
    (r1:rule #uc1 #us1)
    (#uc2:nat)
    (#us2:set unterm #uc2)
    (g2:grammar #uc2 #us2)
    (r2:rule #uc2 #us2)
    (n:nat{n>0}): Tot bool =
    for_all'arrays #term #2 terms'set #n (fun s -> grammarEqualsBySrcf g1 r1 g2 r2 s)

let grammarEqualsByGNSrcf
    (#uc1:nat)
    (#us1:set unterm #uc1)
    (g1:grammar #uc1 #us1)
    (r1:rule #uc1 #us1)
    (#uc2:nat)
    (#us2:set unterm #uc2)
    (g2:grammar #uc2 #us2)
    (r2:rule #uc2 #us2)
    (g:nat{g>0}): Tot bool =
    for_all'nat g (fun t -> grammarEqualsByNSrcf g1 r1 g2 r2 (t + 1))
    
type grammarEqualsBySrct
    (#uc1:nat)
    (#us1:set unterm #uc1)
    (g1:grammar #uc1 #us1)
    (r1:rule #uc1 #us1)
    (#uc2:nat)
    (#us2:set unterm #uc2)
    (g2:grammar #uc2 #us2)
    (r2:rule #uc2 #us2)
    (#n:nat{n>0})
    (s:source #n) =
    unger_rule #uc1 #us1 g1 r1 #n s <==> unger_rule #uc2 #us2 g2 r2 #n s

type grammarEqualsByNSrct
    (#uc1:nat)
    (#us1:set unterm #uc1)
    (g1:grammar #uc1 #us1)
    (r1:rule #uc1 #us1)
    (#uc2:nat)
    (#us2:set unterm #uc2)
    (g2:grammar #uc2 #us2)
    (r2:rule #uc2 #us2)
    (n:nat{n>0}) =
    forall (s:source #n) . grammarEqualsBySrct g1 r1 g2 r2 s

type grammarEqualsByGNSrct
    (#uc1:nat)
    (#us1:set unterm #uc1)
    (g1:grammar #uc1 #us1)
    (r1:rule #uc1 #us1)
    (#uc2:nat)
    (#us2:set unterm #uc2)
    (g2:grammar #uc2 #us2)
    (r2:rule #uc2 #us2)
    (g:nat{g>0}) =
    forall (n:nat{n > 0 /\ n <= g}) . grammarEqualsByNSrct g1 r1 g2 r2 n
    
assume GrammarEqualsImpGNt: forall
    (uc1:nat)
    (us1:set unterm #uc1)
    (g1:grammar #uc1 #us1)
    (r1:rule #uc1 #us1)
    (uc2:nat)
    (us2:set unterm #uc2)
    (g2:grammar #uc2 #us2)
    (r2:rule #uc2 #us2)
    (g:nat{g>0}) .
    {:pattern grammarEqualsByGNSrct g1 r1 g2 r2 (g + 1)}
    grammarEqualsByGNSrct g1 r1 g2 r2 g /\ grammarEqualsByNSrct g1 r1 g2 r2 (g + 1) <==> grammarEqualsByGNSrct g1 r1 g2 r2 (g + 1)

assume GImp:
    forall (a:Type {hasEq a}) (n:nat) (g:nat) (t:full'array a #g) (p:array a #n -> Tot bool) .
    (forall (x:array a #n) . p x)
    <==> (for_all'arrays t p)

let grammar1: grammar #2 #unterms'set =
    let rK: rule #2 #unterms'set = Unterm N in
    let tA: rule #2 #unterms'set = Term A in
    let tK: rule #2 #unterms'set = And(tA, rK) in
    let rN: rule #2 #unterms'set = Or(tA, tK) in
    fun u ->
        match u with
        | N -> rN
        | K -> rN

let grammar2: grammar #2 #unterms'set =
    let rK: rule #2 #unterms'set = Unterm N in
    let tA: rule #2 #unterms'set = Term A in
    let tK: rule #2 #unterms'set = And(rK, tA) in
    let rN: rule #2 #unterms'set = Or(tA, tK) in
    fun u ->
        match u with
        | N -> rN
        | K -> rN

let rS: rule #2 #unterms'set = Unterm K

let xt'1 =
    assert(grammarEqualsByGNSrct grammar1 rS grammar2 rS 1)

let xt'2 =
    assert(grammarEqualsByGNSrct grammar1 rS grammar2 rS 2)

let xt'3 =
    assert(grammarEqualsByGNSrct grammar1 rS grammar2 rS 3)

//let xt'4 =
//    assert(grammarEqualsByGNSrct grammar1 rS grammar2 rS 4)

let xf'1 =
    assert(grammarEqualsByGNSrcf grammar1 rS grammar2 rS 1)

let xf'2 =
    assert(grammarEqualsByGNSrcf grammar1 rS grammar2 rS 2)

let xf'3 =
    assert(grammarEqualsByGNSrcf grammar1 rS grammar2 rS 3)

let xf'4 =
    assert(grammarEqualsByGNSrcf grammar1 rS grammar2 rS 4)
    
//let y =
//    assert(grammarEqualsByGNSrc grm1 rX grm2 rW 10)


//assert(forall x . x = 1 <==> (add'container'item (empty'container) 1) x);
//assert(forall x . x > 0 /\ x < 3 <==> (add'container'item (add'container'item (empty'container) 1) 2) x);
//assert(forall x . x = 1 <==> (intersect'containers (add'container'item (empty'container) 1) (add'container'item (add'container'item (empty'container) 1) 2)) x);
//assert(forall x . x = 1 \/ x = 2 <==> (union'containers (add'container'item (empty'container) 1) (add'container'item (add'container'item (empty'container) 1) 2)) x);
//assert(forall x . x = 2 <==> (xor'containers (add'container'item (empty'container) 1) (add'container'item (add'container'item (empty'container) 1) 2)) x);
//assert(forall x . x = 1 \/ x = 2 <==> (contains'array #int #2 (fun n -> if n = 1 then 1 else 2) x));


//assert(forall n s . unger #2 #unterms grm1 rZ #n s <==> unger_rule #2 #unterms grm2 rY #n s)

//let contains (#a:Type {hasEq a}) (#len:nat) (xs:array a #len) =