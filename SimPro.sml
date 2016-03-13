structure SimPro : sig
  type nat
  type nnf
  val main :
    ((((nat * nnf) list) list -> ((nat * nnf) list) list) ->
      ((nat * nnf) list) list -> bool) ->
      nnf -> bool
  val test : nnf
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

datatype nnf = Pre of bool * nat * nat list | Con of nnf * nnf |
  Dis of nnf * nnf | Uni of nnf | Exi of nnf;

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
      (equal_nata x12 y12 andalso equal_list equal_nat x13 y13);

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

fun snd (x1, x2) = x2;

fun fst (x1, x2) = x1;

fun maxp x Zero_nat = x
  | maxp x (Suc n) = Suc (maxp x n);

fun maxd Zero_nat = Zero_nat
  | maxd (Suc n) = n;

fun maxm x Zero_nat = x
  | maxm x (Suc n) = maxm (maxd x) n;

fun maxl [] = Zero_nat
  | maxl (h :: t) = maxp (maxm (maxl t) h) h;

fun fresh l = (if null l then Zero_nat else Suc (maxl l));

fun stop B_ a uu [] = a
  | stop B_ a p (h :: t) = (if eq B_ p h then [] else stop B_ a p t);

fun mapsa f l = maps f l;

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

fun main prover p = prover (mapsa solve) [[(Zero_nat, p)]];

val test : nnf =
  Dis (Uni (Con (Pre (false, Zero_nat, [Zero_nat]),
                  Pre (false, Suc Zero_nat, [Zero_nat]))),
        Dis (Exi (Pre (true, Suc Zero_nat, [Zero_nat])),
              Exi (Pre (true, Zero_nat, [Zero_nat]))));

end; (*struct SimPro*)
