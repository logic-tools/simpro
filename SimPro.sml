structure SimPro : sig
  type nat
  type nibble
  type char
  type nnf
  val test : nnf
  val make_sequents : nnf -> ((nat * nnf) list) list
  val next_sequents : ((nat * nnf) list) list -> ((nat * nnf) list) list
end = struct

datatype nat = Zero_nat | Suc of nat;

fun equal_nata Zero_nat (Suc x2) = false
  | equal_nata (Suc x2) Zero_nat = false
  | equal_nata (Suc x2) (Suc y2) = equal_nata x2 y2
  | equal_nata Zero_nat Zero_nat = true;

type 'a equal = {equal : 'a -> 'a -> bool};
val equal = #equal : 'a equal -> 'a -> 'a -> bool;

val equal_nat = {equal = equal_nata} : nat equal;

fun equal_bool p true = p
  | equal_bool p false = not p
  | equal_bool true p = p
  | equal_bool false p = not p;

fun eq A_ a b = equal A_ a b;

fun equal_list A_ [] (x21 :: x22) = false
  | equal_list A_ (x21 :: x22) [] = false
  | equal_list A_ (x21 :: x22) (y21 :: y22) =
    eq A_ x21 y21 andalso equal_list A_ x22 y22
  | equal_list A_ [] [] = true;

datatype nibble = Nibble0 | Nibble1 | Nibble2 | Nibble3 | Nibble4 | Nibble5 |
  Nibble6 | Nibble7 | Nibble8 | Nibble9 | NibbleA | NibbleB | NibbleC | NibbleD
  | NibbleE | NibbleF;

datatype char = Char of nibble * nibble;

datatype nnf = Pre of bool * char list * nat list | Con of nnf * nnf |
  Dis of nnf * nnf | Uni of nnf | Exi of nnf;

fun equal_nibble NibbleE NibbleF = false
  | equal_nibble NibbleF NibbleE = false
  | equal_nibble NibbleD NibbleF = false
  | equal_nibble NibbleF NibbleD = false
  | equal_nibble NibbleD NibbleE = false
  | equal_nibble NibbleE NibbleD = false
  | equal_nibble NibbleC NibbleF = false
  | equal_nibble NibbleF NibbleC = false
  | equal_nibble NibbleC NibbleE = false
  | equal_nibble NibbleE NibbleC = false
  | equal_nibble NibbleC NibbleD = false
  | equal_nibble NibbleD NibbleC = false
  | equal_nibble NibbleB NibbleF = false
  | equal_nibble NibbleF NibbleB = false
  | equal_nibble NibbleB NibbleE = false
  | equal_nibble NibbleE NibbleB = false
  | equal_nibble NibbleB NibbleD = false
  | equal_nibble NibbleD NibbleB = false
  | equal_nibble NibbleB NibbleC = false
  | equal_nibble NibbleC NibbleB = false
  | equal_nibble NibbleA NibbleF = false
  | equal_nibble NibbleF NibbleA = false
  | equal_nibble NibbleA NibbleE = false
  | equal_nibble NibbleE NibbleA = false
  | equal_nibble NibbleA NibbleD = false
  | equal_nibble NibbleD NibbleA = false
  | equal_nibble NibbleA NibbleC = false
  | equal_nibble NibbleC NibbleA = false
  | equal_nibble NibbleA NibbleB = false
  | equal_nibble NibbleB NibbleA = false
  | equal_nibble Nibble9 NibbleF = false
  | equal_nibble NibbleF Nibble9 = false
  | equal_nibble Nibble9 NibbleE = false
  | equal_nibble NibbleE Nibble9 = false
  | equal_nibble Nibble9 NibbleD = false
  | equal_nibble NibbleD Nibble9 = false
  | equal_nibble Nibble9 NibbleC = false
  | equal_nibble NibbleC Nibble9 = false
  | equal_nibble Nibble9 NibbleB = false
  | equal_nibble NibbleB Nibble9 = false
  | equal_nibble Nibble9 NibbleA = false
  | equal_nibble NibbleA Nibble9 = false
  | equal_nibble Nibble8 NibbleF = false
  | equal_nibble NibbleF Nibble8 = false
  | equal_nibble Nibble8 NibbleE = false
  | equal_nibble NibbleE Nibble8 = false
  | equal_nibble Nibble8 NibbleD = false
  | equal_nibble NibbleD Nibble8 = false
  | equal_nibble Nibble8 NibbleC = false
  | equal_nibble NibbleC Nibble8 = false
  | equal_nibble Nibble8 NibbleB = false
  | equal_nibble NibbleB Nibble8 = false
  | equal_nibble Nibble8 NibbleA = false
  | equal_nibble NibbleA Nibble8 = false
  | equal_nibble Nibble8 Nibble9 = false
  | equal_nibble Nibble9 Nibble8 = false
  | equal_nibble Nibble7 NibbleF = false
  | equal_nibble NibbleF Nibble7 = false
  | equal_nibble Nibble7 NibbleE = false
  | equal_nibble NibbleE Nibble7 = false
  | equal_nibble Nibble7 NibbleD = false
  | equal_nibble NibbleD Nibble7 = false
  | equal_nibble Nibble7 NibbleC = false
  | equal_nibble NibbleC Nibble7 = false
  | equal_nibble Nibble7 NibbleB = false
  | equal_nibble NibbleB Nibble7 = false
  | equal_nibble Nibble7 NibbleA = false
  | equal_nibble NibbleA Nibble7 = false
  | equal_nibble Nibble7 Nibble9 = false
  | equal_nibble Nibble9 Nibble7 = false
  | equal_nibble Nibble7 Nibble8 = false
  | equal_nibble Nibble8 Nibble7 = false
  | equal_nibble Nibble6 NibbleF = false
  | equal_nibble NibbleF Nibble6 = false
  | equal_nibble Nibble6 NibbleE = false
  | equal_nibble NibbleE Nibble6 = false
  | equal_nibble Nibble6 NibbleD = false
  | equal_nibble NibbleD Nibble6 = false
  | equal_nibble Nibble6 NibbleC = false
  | equal_nibble NibbleC Nibble6 = false
  | equal_nibble Nibble6 NibbleB = false
  | equal_nibble NibbleB Nibble6 = false
  | equal_nibble Nibble6 NibbleA = false
  | equal_nibble NibbleA Nibble6 = false
  | equal_nibble Nibble6 Nibble9 = false
  | equal_nibble Nibble9 Nibble6 = false
  | equal_nibble Nibble6 Nibble8 = false
  | equal_nibble Nibble8 Nibble6 = false
  | equal_nibble Nibble6 Nibble7 = false
  | equal_nibble Nibble7 Nibble6 = false
  | equal_nibble Nibble5 NibbleF = false
  | equal_nibble NibbleF Nibble5 = false
  | equal_nibble Nibble5 NibbleE = false
  | equal_nibble NibbleE Nibble5 = false
  | equal_nibble Nibble5 NibbleD = false
  | equal_nibble NibbleD Nibble5 = false
  | equal_nibble Nibble5 NibbleC = false
  | equal_nibble NibbleC Nibble5 = false
  | equal_nibble Nibble5 NibbleB = false
  | equal_nibble NibbleB Nibble5 = false
  | equal_nibble Nibble5 NibbleA = false
  | equal_nibble NibbleA Nibble5 = false
  | equal_nibble Nibble5 Nibble9 = false
  | equal_nibble Nibble9 Nibble5 = false
  | equal_nibble Nibble5 Nibble8 = false
  | equal_nibble Nibble8 Nibble5 = false
  | equal_nibble Nibble5 Nibble7 = false
  | equal_nibble Nibble7 Nibble5 = false
  | equal_nibble Nibble5 Nibble6 = false
  | equal_nibble Nibble6 Nibble5 = false
  | equal_nibble Nibble4 NibbleF = false
  | equal_nibble NibbleF Nibble4 = false
  | equal_nibble Nibble4 NibbleE = false
  | equal_nibble NibbleE Nibble4 = false
  | equal_nibble Nibble4 NibbleD = false
  | equal_nibble NibbleD Nibble4 = false
  | equal_nibble Nibble4 NibbleC = false
  | equal_nibble NibbleC Nibble4 = false
  | equal_nibble Nibble4 NibbleB = false
  | equal_nibble NibbleB Nibble4 = false
  | equal_nibble Nibble4 NibbleA = false
  | equal_nibble NibbleA Nibble4 = false
  | equal_nibble Nibble4 Nibble9 = false
  | equal_nibble Nibble9 Nibble4 = false
  | equal_nibble Nibble4 Nibble8 = false
  | equal_nibble Nibble8 Nibble4 = false
  | equal_nibble Nibble4 Nibble7 = false
  | equal_nibble Nibble7 Nibble4 = false
  | equal_nibble Nibble4 Nibble6 = false
  | equal_nibble Nibble6 Nibble4 = false
  | equal_nibble Nibble4 Nibble5 = false
  | equal_nibble Nibble5 Nibble4 = false
  | equal_nibble Nibble3 NibbleF = false
  | equal_nibble NibbleF Nibble3 = false
  | equal_nibble Nibble3 NibbleE = false
  | equal_nibble NibbleE Nibble3 = false
  | equal_nibble Nibble3 NibbleD = false
  | equal_nibble NibbleD Nibble3 = false
  | equal_nibble Nibble3 NibbleC = false
  | equal_nibble NibbleC Nibble3 = false
  | equal_nibble Nibble3 NibbleB = false
  | equal_nibble NibbleB Nibble3 = false
  | equal_nibble Nibble3 NibbleA = false
  | equal_nibble NibbleA Nibble3 = false
  | equal_nibble Nibble3 Nibble9 = false
  | equal_nibble Nibble9 Nibble3 = false
  | equal_nibble Nibble3 Nibble8 = false
  | equal_nibble Nibble8 Nibble3 = false
  | equal_nibble Nibble3 Nibble7 = false
  | equal_nibble Nibble7 Nibble3 = false
  | equal_nibble Nibble3 Nibble6 = false
  | equal_nibble Nibble6 Nibble3 = false
  | equal_nibble Nibble3 Nibble5 = false
  | equal_nibble Nibble5 Nibble3 = false
  | equal_nibble Nibble3 Nibble4 = false
  | equal_nibble Nibble4 Nibble3 = false
  | equal_nibble Nibble2 NibbleF = false
  | equal_nibble NibbleF Nibble2 = false
  | equal_nibble Nibble2 NibbleE = false
  | equal_nibble NibbleE Nibble2 = false
  | equal_nibble Nibble2 NibbleD = false
  | equal_nibble NibbleD Nibble2 = false
  | equal_nibble Nibble2 NibbleC = false
  | equal_nibble NibbleC Nibble2 = false
  | equal_nibble Nibble2 NibbleB = false
  | equal_nibble NibbleB Nibble2 = false
  | equal_nibble Nibble2 NibbleA = false
  | equal_nibble NibbleA Nibble2 = false
  | equal_nibble Nibble2 Nibble9 = false
  | equal_nibble Nibble9 Nibble2 = false
  | equal_nibble Nibble2 Nibble8 = false
  | equal_nibble Nibble8 Nibble2 = false
  | equal_nibble Nibble2 Nibble7 = false
  | equal_nibble Nibble7 Nibble2 = false
  | equal_nibble Nibble2 Nibble6 = false
  | equal_nibble Nibble6 Nibble2 = false
  | equal_nibble Nibble2 Nibble5 = false
  | equal_nibble Nibble5 Nibble2 = false
  | equal_nibble Nibble2 Nibble4 = false
  | equal_nibble Nibble4 Nibble2 = false
  | equal_nibble Nibble2 Nibble3 = false
  | equal_nibble Nibble3 Nibble2 = false
  | equal_nibble Nibble1 NibbleF = false
  | equal_nibble NibbleF Nibble1 = false
  | equal_nibble Nibble1 NibbleE = false
  | equal_nibble NibbleE Nibble1 = false
  | equal_nibble Nibble1 NibbleD = false
  | equal_nibble NibbleD Nibble1 = false
  | equal_nibble Nibble1 NibbleC = false
  | equal_nibble NibbleC Nibble1 = false
  | equal_nibble Nibble1 NibbleB = false
  | equal_nibble NibbleB Nibble1 = false
  | equal_nibble Nibble1 NibbleA = false
  | equal_nibble NibbleA Nibble1 = false
  | equal_nibble Nibble1 Nibble9 = false
  | equal_nibble Nibble9 Nibble1 = false
  | equal_nibble Nibble1 Nibble8 = false
  | equal_nibble Nibble8 Nibble1 = false
  | equal_nibble Nibble1 Nibble7 = false
  | equal_nibble Nibble7 Nibble1 = false
  | equal_nibble Nibble1 Nibble6 = false
  | equal_nibble Nibble6 Nibble1 = false
  | equal_nibble Nibble1 Nibble5 = false
  | equal_nibble Nibble5 Nibble1 = false
  | equal_nibble Nibble1 Nibble4 = false
  | equal_nibble Nibble4 Nibble1 = false
  | equal_nibble Nibble1 Nibble3 = false
  | equal_nibble Nibble3 Nibble1 = false
  | equal_nibble Nibble1 Nibble2 = false
  | equal_nibble Nibble2 Nibble1 = false
  | equal_nibble Nibble0 NibbleF = false
  | equal_nibble NibbleF Nibble0 = false
  | equal_nibble Nibble0 NibbleE = false
  | equal_nibble NibbleE Nibble0 = false
  | equal_nibble Nibble0 NibbleD = false
  | equal_nibble NibbleD Nibble0 = false
  | equal_nibble Nibble0 NibbleC = false
  | equal_nibble NibbleC Nibble0 = false
  | equal_nibble Nibble0 NibbleB = false
  | equal_nibble NibbleB Nibble0 = false
  | equal_nibble Nibble0 NibbleA = false
  | equal_nibble NibbleA Nibble0 = false
  | equal_nibble Nibble0 Nibble9 = false
  | equal_nibble Nibble9 Nibble0 = false
  | equal_nibble Nibble0 Nibble8 = false
  | equal_nibble Nibble8 Nibble0 = false
  | equal_nibble Nibble0 Nibble7 = false
  | equal_nibble Nibble7 Nibble0 = false
  | equal_nibble Nibble0 Nibble6 = false
  | equal_nibble Nibble6 Nibble0 = false
  | equal_nibble Nibble0 Nibble5 = false
  | equal_nibble Nibble5 Nibble0 = false
  | equal_nibble Nibble0 Nibble4 = false
  | equal_nibble Nibble4 Nibble0 = false
  | equal_nibble Nibble0 Nibble3 = false
  | equal_nibble Nibble3 Nibble0 = false
  | equal_nibble Nibble0 Nibble2 = false
  | equal_nibble Nibble2 Nibble0 = false
  | equal_nibble Nibble0 Nibble1 = false
  | equal_nibble Nibble1 Nibble0 = false
  | equal_nibble NibbleF NibbleF = true
  | equal_nibble NibbleE NibbleE = true
  | equal_nibble NibbleD NibbleD = true
  | equal_nibble NibbleC NibbleC = true
  | equal_nibble NibbleB NibbleB = true
  | equal_nibble NibbleA NibbleA = true
  | equal_nibble Nibble9 Nibble9 = true
  | equal_nibble Nibble8 Nibble8 = true
  | equal_nibble Nibble7 Nibble7 = true
  | equal_nibble Nibble6 Nibble6 = true
  | equal_nibble Nibble5 Nibble5 = true
  | equal_nibble Nibble4 Nibble4 = true
  | equal_nibble Nibble3 Nibble3 = true
  | equal_nibble Nibble2 Nibble2 = true
  | equal_nibble Nibble1 Nibble1 = true
  | equal_nibble Nibble0 Nibble0 = true;

fun equal_chara (Char (x1, x2)) (Char (y1, y2)) =
  equal_nibble x1 y1 andalso equal_nibble x2 y2;

val equal_char = {equal = equal_chara} : char equal;

fun equal_nnfa (Uni x4) (Exi x5) = false
  | equal_nnfa (Exi x5) (Uni x4) = false
  | equal_nnfa (Dis (x31, x32)) (Exi x5) = false
  | equal_nnfa (Exi x5) (Dis (x31, x32)) = false
  | equal_nnfa (Dis (x31, x32)) (Uni x4) = false
  | equal_nnfa (Uni x4) (Dis (x31, x32)) = false
  | equal_nnfa (Con (x21, x22)) (Exi x5) = false
  | equal_nnfa (Exi x5) (Con (x21, x22)) = false
  | equal_nnfa (Con (x21, x22)) (Uni x4) = false
  | equal_nnfa (Uni x4) (Con (x21, x22)) = false
  | equal_nnfa (Con (x21, x22)) (Dis (x31, x32)) = false
  | equal_nnfa (Dis (x31, x32)) (Con (x21, x22)) = false
  | equal_nnfa (Pre (x11, x12, x13)) (Exi x5) = false
  | equal_nnfa (Exi x5) (Pre (x11, x12, x13)) = false
  | equal_nnfa (Pre (x11, x12, x13)) (Uni x4) = false
  | equal_nnfa (Uni x4) (Pre (x11, x12, x13)) = false
  | equal_nnfa (Pre (x11, x12, x13)) (Dis (x31, x32)) = false
  | equal_nnfa (Dis (x31, x32)) (Pre (x11, x12, x13)) = false
  | equal_nnfa (Pre (x11, x12, x13)) (Con (x21, x22)) = false
  | equal_nnfa (Con (x21, x22)) (Pre (x11, x12, x13)) = false
  | equal_nnfa (Exi x5) (Exi y5) = equal_nnfa x5 y5
  | equal_nnfa (Uni x4) (Uni y4) = equal_nnfa x4 y4
  | equal_nnfa (Dis (x31, x32)) (Dis (y31, y32)) =
    equal_nnfa x31 y31 andalso equal_nnfa x32 y32
  | equal_nnfa (Con (x21, x22)) (Con (y21, y22)) =
    equal_nnfa x21 y21 andalso equal_nnfa x22 y22
  | equal_nnfa (Pre (x11, x12, x13)) (Pre (y11, y12, y13)) =
    equal_bool x11 y11 andalso
      (equal_list equal_char x12 y12 andalso equal_list equal_nat x13 y13);

val equal_nnf = {equal = equal_nnfa} : nnf equal;

fun maps f [] = []
  | maps f (x :: xs) = f x @ maps f xs;

fun null [] = true
  | null (x :: xs) = false;

fun extend l Zero_nat = l
  | extend l (Suc n) = n :: l;

fun adjust [] = []
  | adjust (h :: t) = extend (adjust t) h;

fun fv (Pre (uu, uv, v)) = v
  | fv (Con (p, q)) = fv p @ fv q
  | fv (Dis (p, q)) = fv p @ fv q
  | fv (Uni p) = adjust (fv p)
  | fv (Exi p) = adjust (fv p);

fun bind x Zero_nat = x
  | bind uu (Suc n) = n;

fun bump uu Zero_nat = Zero_nat
  | bump f (Suc n) = Suc (f n);

fun map f [] = []
  | map f (x21 :: x22) = f x21 :: map f x22;

fun subst f (Pre (b, i, v)) = Pre (b, i, map f v)
  | subst f (Con (p, q)) = Con (subst f p, subst f q)
  | subst f (Dis (p, q)) = Dis (subst f p, subst f q)
  | subst f (Uni p) = Uni (subst (bump f) p)
  | subst f (Exi p) = Exi (subst (bump f) p);

fun inst p n = subst (bind n) p;

fun mapsa f l = maps f l;

fun maxd Zero_nat = Zero_nat
  | maxd (Suc n) = n;

fun maxp x Zero_nat = x
  | maxp x (Suc n) = Suc (maxp x n);

fun maxm x Zero_nat = x
  | maxm x (Suc n) = maxm (maxd x) n;

fun maxl [] = Zero_nat
  | maxl (h :: t) = maxp (maxm (maxl t) h) h;

fun stop B_ a uu [] = a
  | stop B_ a p (h :: t) = (if eq B_ p h then [] else stop B_ a p t);

val test : nnf =
  Dis (Uni (Con (Pre (false, [Char (Nibble5, Nibble0)], [Zero_nat]),
                  Pre (false, [Char (Nibble5, Nibble1)], [Zero_nat]))),
        Dis (Exi (Pre (true, [Char (Nibble5, Nibble1)], [Zero_nat])),
              Exi (Pre (true, [Char (Nibble5, Nibble0)], [Zero_nat]))));

fun fresh l = (if null l then Zero_nat else Suc (maxl l));

fun snd (x1, x2) = x2;

fun fst (x1, x2) = x1;

fun track s uu (Pre (b, i, v)) =
  stop equal_nnf [s @ [(Zero_nat, Pre (b, i, v))]] (Pre (not b, i, v))
    (map snd s)
  | track s uv (Con (p, q)) = [s @ [(Zero_nat, p)], s @ [(Zero_nat, q)]]
  | track s uw (Dis (p, q)) = [s @ [(Zero_nat, p), (Zero_nat, q)]]
  | track s ux (Uni p) =
    [s @ [(Zero_nat, inst p (fresh (mapsa fv (Uni p :: map snd s))))]]
  | track s n (Exi p) = [s @ [(Zero_nat, inst p n), (Suc n, Exi p)]];

fun solve [] = [[]]
  | solve (h :: t) = track t (fst h) (snd h);

fun make_sequents p = [[(Zero_nat, p)]];

fun next_sequents a = mapsa solve a;

end; (*struct SimPro*)
