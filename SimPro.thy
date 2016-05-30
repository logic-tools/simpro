section \<open>A Simple Prover in Isabelle\<close>

theory SimPro imports Main begin

type_synonym id = nat

datatype nnf = Pre bool id "nat list" | Con nnf nnf | Dis nnf nnf | Uni nnf | Exi nnf

abbreviation (input) "TEST P Q \<equiv> (\<exists>x. P x \<or> Q x) \<longrightarrow> (\<exists>x. Q x) \<or> (\<exists>x. P x)"

proposition "TEST P Q"
by iprover

proposition "TEST P Q = (\<forall>x. \<not> P x \<and> \<not> Q x) \<or> (\<exists>x. Q x) \<or> (\<exists>x. P x)"
by fast

abbreviation (input) "P_id \<equiv> 0"

abbreviation (input) "Q_id \<equiv> Suc 0"

definition \<comment> \<open>TEST P Q\<close>
  "test \<equiv> Dis
    (Uni (Con (Pre False P_id [0]) (Pre False Q_id [0])))
    (Dis (Exi (Pre True Q_id [0])) (Exi (Pre True P_id [0])))"

type_synonym proxy = "unit list"

type_synonym model = "proxy set \<times> (id \<Rightarrow> proxy list \<Rightarrow> bool)"

type_synonym environment = "nat \<Rightarrow> proxy"

definition is_model_environment :: "model \<Rightarrow> environment \<Rightarrow> bool" where
  "is_model_environment m e \<equiv> \<forall>n. e n \<in> fst m"

primrec semantics :: "model \<Rightarrow> environment \<Rightarrow> nnf \<Rightarrow> bool" where
  "semantics m e (Pre b i v) = (b = snd m i (map e v))" |
  "semantics m e (Con p q) = (semantics m e p \<and> semantics m e q)" |
  "semantics m e (Dis p q) = (semantics m e p \<or> semantics m e q)" |
  "semantics m e (Uni p) = (\<forall>z \<in> fst m. semantics m (\<lambda>x. case x of 0 \<Rightarrow> z | Suc n \<Rightarrow> e n) p)" |
  "semantics m e (Exi p) = (\<exists>z \<in> fst m. semantics m (\<lambda>x. case x of 0 \<Rightarrow> z | Suc n \<Rightarrow> e n) p)"

primrec extend :: "nat list \<Rightarrow> nat \<Rightarrow> nat list" where
  "extend l 0 = l" |
  "extend l (Suc n) = n # l"

primrec adjust :: "nat list \<Rightarrow> nat list" where
  "adjust [] = []" |
  "adjust (h # t) = extend (adjust t) h"

primrec fv :: "nnf \<Rightarrow> nat list" where
  "fv (Pre _ _ v) = v" |
  "fv (Con p q) = fv p @ fv q" |
  "fv (Dis p q) = fv p @ fv q" |
  "fv (Uni p) = adjust (fv p)" |
  "fv (Exi p) = adjust (fv p)"

primrec increase :: "(nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> nat" where
  "increase _ 0 = 0" |
  "increase f (Suc n) = Suc (f n)"

primrec sv :: "(nat \<Rightarrow> nat) \<Rightarrow> nnf \<Rightarrow> nnf" where
  "sv f (Pre b i v) = Pre b i (map f v)" |
  "sv f (Con p q) = Con (sv f p) (sv f q)" |
  "sv f (Dis p q) = Dis (sv f p) (sv f q)" |
  "sv f (Uni p) = Uni (sv (increase f) p)" |
  "sv f (Exi p) = Exi (sv (increase f) p)"

primrec bind :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "bind x 0 = x" |
  "bind _ (Suc n) = n"

definition inst :: "nnf \<Rightarrow> nat \<Rightarrow> nnf" where
  "inst p x \<equiv> sv (bind x) p"

primrec dec :: "nat \<Rightarrow> nat" where
  "dec 0 = 0" |
  "dec (Suc n) = n"

primrec sub :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "sub x 0 = x" |
  "sub x (Suc n) = dec (sub x n)"

primrec add :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "add x 0 = x" |
  "add x (Suc n) = Suc (add x n)"

primrec fresh :: "nat list \<Rightarrow> nat" where
  "fresh [] = 0" |
  "fresh (h # t) = Suc (add (sub (dec (fresh t)) h) h)"

primrec stop :: "'a list \<Rightarrow> 'b \<Rightarrow> 'b list \<Rightarrow> 'a list" where
  "stop c _ [] = c" |
  "stop c p (h # t) = (if p = h then [] else stop c p t)"

definition maps :: "('a \<Rightarrow> 'b list) \<Rightarrow> 'a list \<Rightarrow> 'b list" where
  "maps f l \<equiv> concat (map f l)"

type_synonym sequent = "(nat \<times> nnf) list"

primrec track :: "sequent \<Rightarrow> nat \<Rightarrow> nnf \<Rightarrow> sequent list" where
  "track s _ (Pre b i v) = stop [s @ [(0,Pre b i v)]] (Pre (\<not> b) i v) (map snd s)" |
  "track s _ (Con p q) = [s @ [(0,p)],s @ [(0,q)]]" |
  "track s _ (Dis p q) = [s @ [(0,p),(0,q)]]" |
  "track s _ (Uni p) = [s @ [(0,inst p (fresh (maps fv (Uni p # map snd s))))]]" |
  "track s n (Exi p) = [s @ [(0,inst p n),(Suc n,Exi p)]]"

primrec solve :: "sequent \<Rightarrow> sequent list" where
  "solve [] = [[]]" |
  "solve (h # t) = track t (fst h) (snd h)"

type_synonym 'a algorithm = "('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> bool"

primrec null :: "'a list \<Rightarrow> bool" where
  "null [] = True" |
  "null (_ # _) = False"

definition main :: "sequent list algorithm \<Rightarrow> nnf \<Rightarrow> bool" where
  "main a p \<equiv> a null (maps solve) [[(0,p)]]" 

primrec repeat :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> 'a" where
  "repeat _ c 0 = c" |
  "repeat f c (Suc n) = repeat f (f c) n"

definition iterator :: "'a algorithm" where
  "iterator g f c \<equiv> \<exists>n. g (repeat f c n)"

definition check :: "nnf \<Rightarrow> bool" where
  "check \<equiv> main iterator"

abbreviation (input) "CHECK \<equiv> check = (\<lambda>p. \<forall>m e. is_model_environment m e \<longrightarrow> semantics m e p)"

inductive_set calculation :: "sequent \<Rightarrow> (nat \<times> sequent) set" for s where
  "(0,s) \<in> calculation s" |
  "(n,k) \<in> calculation s \<Longrightarrow> l \<in> set (solve k) \<Longrightarrow> (Suc n,l) \<in> calculation s"

primrec semantics_alternative :: "model \<Rightarrow> environment \<Rightarrow> nnf list \<Rightarrow> bool" where
  "semantics_alternative _ _ [] = False" |
  "semantics_alternative m e (h # t) = (semantics m e h \<or> semantics_alternative m e t)"

definition valid :: "nnf list \<Rightarrow> bool" where
  "valid l \<equiv> \<forall>m e. is_model_environment m e \<longrightarrow> semantics_alternative m e l"

abbreviation (input) "VALID \<equiv> valid = finite \<circ> calculation \<circ> map (Pair 0)"

proposition "\<forall>m e. is_model_environment m e \<longrightarrow> fst m \<noteq> {}"
unfolding is_model_environment_def
by fast

proposition iterator[code]: "iterator g f c = (if g c then True else iterator g f (f c))"
unfolding iterator_def
by (metis repeat.simps not0_implies_Suc)

abbreviation (input) "PROVER \<equiv> iterator null (maps solve)"

lemma check_prover: "check p \<equiv> PROVER [[(0,p)]]"
unfolding check_def main_def
by -

proposition "PROVER c = (if null c then True else PROVER (maps solve c))"
using iterator
by - 

lemma prover: "PROVER c = PROVER (maps solve c)"
using iterator maps_def concat.simps(1) list.map(1) null.simps(2) list.exhaust
by metis

lemma prover_next: "PROVER (h # t) = PROVER (maps solve (h # t))"
using prover
by -

lemma prover_done: "PROVER [] = True"
by (simp add: iterator)

lemma map_simps: "map f [] = []" "map f (h # t) = f h # map f t"
by (rule list.map(1),rule list.map(2))

lemma concat_simps: "concat [] = []" "concat (h # t) = h @ concat t"
by (rule concat.simps(1),rule concat.simps(2))

lemma append_simps: "[] @ l = l" "(h # t) @ l = h # t @ l"
by (rule append.simps(1),rule append.simps(2))

lemma if_simps: "(if True then x else y) = x" "(if False then x else y) = y"
by (rule if_True,rule if_False)

lemma not_simps: "(\<not> True) = False" "(\<not> False) = True" "(\<not> \<not> b) = b"
by (rule not_True_eq_False,rule not_False_eq_True,rule not_not)

lemma prod_simps: "fst (x,y) = x" "snd (x,y) = y"
unfolding fst_def snd_def
by (rule prod.case,rule prod.case)

lemma nat_simps: "(0 = 0) = True"
by (rule simp_thms)

lemma list_simps: "([] = []) = True"
by (rule simp_thms)

lemma bool_simps: "(True = True) = True" "(False = False) = True"
by (rule simp_thms,rule simp_thms)

lemma inject_simps: "(True \<and> b) = b" "(False \<and> b) = False"
by (rule simp_thms,rule simp_thms)

lemmas simps = check_prover prover_next prover_done solve.simps track.simps maps_def stop.simps
  fresh.simps add.simps sub.simps dec.simps inst_def bind.simps sv.simps increase.simps fv.simps
  adjust.simps extend.simps nnf.distinct nnf.inject map_simps concat_simps append_simps if_simps
  not_simps prod_simps nat.distinct list.distinct bool.distinct nat_simps list_simps bool_simps
  prod.inject nat.inject list.inject inject_simps

theorem program:
  "\<And>p. check p \<equiv> PROVER [[(0,p)]]"
  "\<And>h t. PROVER (h # t) \<equiv> PROVER (maps solve (h # t))"
  "PROVER [] \<equiv> True"
  "solve [] \<equiv> [[]]"
  "\<And>h t. solve (h # t) \<equiv> track t (fst h) (snd h)"
  "\<And>s n b i v. track s n (Pre b i v) \<equiv> stop [s @ [(0,Pre b i v)]] (Pre (\<not> b) i v) (map snd s)"
  "\<And>s n p q. track s n (Con p q) \<equiv> [s @ [(0,p)],s @ [(0,q)]]"
  "\<And>s n p q. track s n (Dis p q) \<equiv> [s @ [(0,p),(0,q)]]"
  "\<And>s n p. track s n (Uni p) \<equiv> [s @ [(0,inst p (fresh (maps fv (Uni p # map snd s))))]]"
  "\<And>s n p. track s n (Exi p) \<equiv> [s @ [(0,inst p n),(Suc n,Exi p)]]"
  "\<And>f l. maps f l \<equiv> concat (map f l)"
  "\<And>c p. stop c p [] \<equiv> c"
  "\<And>c p h t. stop c p (h # t) \<equiv> (if p = h then [] else stop c p t)"
  "fresh [] \<equiv> 0"
  "\<And>h t. fresh (h # t) \<equiv> Suc (add (sub (dec (fresh t)) h) h)"
  "\<And>x. add x 0 \<equiv> x"
  "\<And>x n. add x (Suc n) \<equiv> Suc (add x n)"
  "\<And>x. sub x 0 \<equiv> x"
  "\<And>x n. sub x (Suc n) \<equiv> dec (sub x n)"
  "dec 0 \<equiv> 0"
  "\<And>n. dec (Suc n) \<equiv> n"
  "\<And>p x. inst p x \<equiv> sv (bind x) p"
  "\<And>x. bind x 0 \<equiv> x"
  "\<And>x n. bind x (Suc n) \<equiv> n"
  "\<And>f b i v. sv f (Pre b i v) \<equiv> Pre b i (map f v)"
  "\<And>f p q. sv f (Con p q) \<equiv> Con (sv f p) (sv f q)"
  "\<And>f p q. sv f (Dis p q) \<equiv> Dis (sv f p) (sv f q)"
  "\<And>f p. sv f (Uni p) \<equiv> Uni (sv (increase f) p)"
  "\<And>f p. sv f (Exi p) \<equiv> Exi (sv (increase f) p)"
  "\<And>f. increase f 0 \<equiv> 0"
  "\<And>f n. increase f (Suc n) \<equiv> Suc (f n)"
  "\<And>b i v. fv (Pre b i v) \<equiv> v"
  "\<And>p q. fv (Con p q) \<equiv> fv p @ fv q"
  "\<And>p q. fv (Dis p q) \<equiv> fv p @ fv q"
  "\<And>p. fv (Uni p) \<equiv> adjust (fv p)"
  "\<And>p. fv (Exi p) \<equiv> adjust (fv p)"
  "adjust [] \<equiv> []"
  "\<And>h t. adjust (h # t) \<equiv> extend (adjust t) h"
  "\<And>l. extend l 0 \<equiv> l"
  "\<And>l n. extend l (Suc n) \<equiv> n # l"
by ((simp only: simps(1)),
    (simp only: simps(2)),
    (simp only: simps(3)),
    (simp only: simps(4)),
    (simp only: simps(5)),
    (simp only: simps(6)),
    (simp only: simps(7)),
    (simp only: simps(8)),
    (simp only: simps(9)),
    (simp only: simps(10)),
    (simp only: simps(11)),
    (simp only: simps(12)),
    (simp only: simps(13)),
    (simp only: simps(14)),
    (simp only: simps(15)),
    (simp only: simps(16)),
    (simp only: simps(17)),
    (simp only: simps(18)),
    (simp only: simps(19)),
    (simp only: simps(20)),
    (simp only: simps(21)),
    (simp only: simps(22)),
    (simp only: simps(23)),
    (simp only: simps(24)),
    (simp only: simps(25)),
    (simp only: simps(26)),
    (simp only: simps(27)),
    (simp only: simps(28)),
    (simp only: simps(29)),
    (simp only: simps(30)),
    (simp only: simps(31)),
    (simp only: simps(32)),
    (simp only: simps(33)),
    (simp only: simps(34)),
    (simp only: simps(35)),
    (simp only: simps(36)),
    (simp only: simps(37)),
    (simp only: simps(38)),
    (simp only: simps(39)),
    (simp only: simps(40)))

theorem data:
  "\<And>b i v p q. Pre b i v = Con p q \<equiv> False"
  "\<And>b i v p q. Con p q = Pre b i v \<equiv> False"
  "\<And>b i v p q. Pre b i v = Dis p q \<equiv> False"
  "\<And>b i v p q. Dis p q = Pre b i v \<equiv> False"
  "\<And>b i v p. Pre b i v = Uni p \<equiv> False"
  "\<And>b i v p. Uni p = Pre b i v \<equiv> False"
  "\<And>b i v p. Pre b i v = Exi p \<equiv> False"
  "\<And>b i v p. Exi p = Pre b i v \<equiv> False"
  "\<And>p q p' q'. Con p q = Dis p' q' \<equiv> False"
  "\<And>p q p' q'. Dis p' q' = Con p q \<equiv> False"
  "\<And>p q p'. Con p q = Uni p' \<equiv> False"
  "\<And>p q p'. Uni p' = Con p q \<equiv> False"
  "\<And>p q p'. Con p q = Exi p' \<equiv> False"
  "\<And>p q p'. Exi p' = Con p q \<equiv> False"
  "\<And>p q p'. Dis p q = Uni p' \<equiv> False"
  "\<And>p q p'. Uni p' = Dis p q \<equiv> False"
  "\<And>p q p'. Dis p q = Exi p' \<equiv> False"
  "\<And>p q p'. Exi p' = Dis p q \<equiv> False"
  "\<And>p p'. Uni p = Exi p' \<equiv> False"
  "\<And>p p'. Exi p' = Uni p \<equiv> False"
  "\<And>b i v b' i' v'. Pre b i v = Pre b' i' v' \<equiv> b = b' \<and> i = i' \<and> v = v'"
  "\<And>p q p' q'. Con p q = Con p' q' \<equiv> p = p' \<and> q = q'"
  "\<And>p q p' q'. Dis p q = Dis p' q' \<equiv> p = p' \<and> q = q'"
  "\<And>p p'. Uni p = Uni p' \<equiv> p = p'"
  "\<And>p p'. Exi p = Exi p' \<equiv> p = p'"
by ((simp only: simps(41)),
    (simp only: simps(42)),
    (simp only: simps(43)),
    (simp only: simps(44)),
    (simp only: simps(45)),
    (simp only: simps(46)),
    (simp only: simps(47)),
    (simp only: simps(48)),
    (simp only: simps(49)),
    (simp only: simps(50)),
    (simp only: simps(51)),
    (simp only: simps(52)),
    (simp only: simps(53)),
    (simp only: simps(54)),
    (simp only: simps(55)),
    (simp only: simps(56)),
    (simp only: simps(57)),
    (simp only: simps(58)),
    (simp only: simps(59)),
    (simp only: simps(60)),
    (simp only: simps(61)),
    (simp only: simps(62)),
    (simp only: simps(63)),
    (simp only: simps(64)),
    (simp only: simps(65)))

theorem library:
  "\<And>f. map f [] \<equiv> []"
  "\<And>f h t. map f (h # t) \<equiv> f h # map f t"
  "concat [] \<equiv> []"
  "\<And>h t . concat (h # t) \<equiv> h @ concat t"
  "\<And>l. [] @ l \<equiv> l"
  "\<And>h t l. (h # t) @ l \<equiv> h # t @ l"
  "\<And>x y. if True then x else y \<equiv> x"
  "\<And>x y. if False then x else y \<equiv> y"
  "\<not> True \<equiv> False"
  "\<not> False \<equiv> True"
  "\<And>b. \<not> \<not> b \<equiv> b"
  "\<And>x y. fst (x,y) \<equiv> x"
  "\<And>x y. snd (x,y) \<equiv> y"
  "\<And>n. 0 = Suc n \<equiv> False"
  "\<And>n. Suc n = 0 \<equiv> False"
  "\<And>h t. [] = h # t \<equiv> False"
  "\<And>h t. h # t = [] \<equiv> False"
  "True = False \<equiv> False"
  "False = True \<equiv> False"
  "0 = 0 \<equiv> True"
  "[] = [] \<equiv> True"
  "True = True \<equiv> True"
  "False = False \<equiv> True"
  "\<And>x y x' y'. (x,y) = (x',y') \<equiv> x = x' \<and> y = y'"
  "\<And>n n'. Suc n = Suc n' \<equiv> n = n'"
  "\<And>h t h' t'. h # t = h' # t' \<equiv> h = h' \<and> t = t'"
  "\<And>b. True \<and> b \<equiv> b"
  "\<And>b. False \<and> b \<equiv> False"
by ((simp only: simps(66)),
    (simp only: simps(67)),
    (simp only: simps(68)),
    (simp only: simps(69)),
    (simp only: simps(70)),
    (simp only: simps(71)),
    (simp only: simps(72)),
    (simp only: simps(73)),
    (simp only: simps(74)),
    (simp only: simps(75)),
    (simp only: simps(76)),
    (simp only: simps(77)),
    (simp only: simps(78)),
    (simp only: simps(79)),
    (simp only: simps(80)),
    (simp only: simps(81)),
    (simp only: simps(82)),
    (simp only: simps(83)),
    (simp only: simps(84)),
    (simp only: simps(85)),
    (simp only: simps(86)),
    (simp only: simps(87)),
    (simp only: simps(88)),
    (simp only: simps(89)),
    (simp only: simps(90)),
    (simp only: simps(91)),
    (simp only: simps(92)),
    (simp only: simps(93)))

proposition "check test"
unfolding test_def
unfolding program(1)
unfolding program(2)
unfolding program(3-) data library
unfolding program(2)
unfolding program(3-) data library
unfolding program(2)
unfolding program(3-) data library
unfolding program(2)
unfolding program(3-) data library
unfolding program(2)
unfolding program(3-) data library
unfolding program(2)
unfolding program(3-) data library
unfolding program(2)
unfolding program(3-) data library
by (rule TrueI)

proposition "check test"
unfolding check_def
unfolding main_def
unfolding test_def
by (simp add: maps_def inst_def iterator)

proposition "check test"
by code_simp

proposition "map length (map (repeat (maps solve) [[(0,test)]]) [1,2,3,4,5,6,7]) = [1,1,1,2,2,2,0]"
by code_simp

proposition "repeat (maps solve) [[(0,test)]] (Suc (Suc (Suc (Suc (Suc (Suc (Suc 0))))))) = []"
unfolding repeat.simps
unfolding test_def
unfolding program data library
by (rule TrueI)

section "Basics"

primrec maxl :: "nat list \<Rightarrow> nat" where
  "maxl [] = 0" |
  "maxl (h # t) = add (sub (maxl t) h) h"

definition fresh' :: "nat list \<Rightarrow> nat" where
  "fresh' l \<equiv> if null l then 0 else Suc (maxl l)"

lemma fresh': "fresh l = fresh' l"
unfolding fresh'_def by (induct l) (auto, metis null.simps(2) list.exhaust maxl.simps) 

primrec repeat' :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> 'a" where
  "repeat' _ c 0 = c" |
  "repeat' f c (Suc n) = f (repeat' f c n)"

lemma r: "f (repeat f c n) = repeat f (f c) n"
by (induct n arbitrary: c) simp_all

lemma rr: "repeat' f c n = repeat f c n"
by (induct n) (simp_all add: r)

primrec sub' :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "sub' x 0 = x" |
  "sub' x (Suc n) = sub' (dec x) n"

lemma ddd: "dec x = x-(1::nat)"
by (simp add: nat_diff_split)

lemma dddd: "sub' x y = x-(y::nat)"
using ddd diff_Suc_eq_diff_pred sub'.simps by (induct y arbitrary: x) presburger+

lemma ddddd: "sub x y = x-(y::nat)"
by (induct y arbitrary: x) (simp_all add: ddd)

lemma dx: "sub x y = sub' x y"
by (simp add: dddd ddddd)

lemma mmm: "(add (sub n n') n') = (max n n')"
proof (induct n' arbitrary: n)
  case 0 then show ?case by simp
next
  case Suc then show ?case 
  proof -
    fix n'a :: nat and na :: nat
    assume a1: "\<And>n. add (sub n n'a) n'a = max n n'a"
    have f2: "\<And>n na. n = 0 \<or> Suc (max na (n - 1)) = max (Suc na) n"
      by (metis (lifting) Nitpick.case_nat_unfold max_Suc1)
    { assume "na \<noteq> 0"
      then have "Suc (max n'a (dec na)) = max na (Suc n'a)"
        using f2 by (metis (lifting) dec.simps(2) Suc_pred' max.commute not_gr0) }
    then have "Suc (max n'a (dec na)) = max na (Suc n'a)"
      by (metis max.commute max_0L dec.simps(1))
    then show "add (sub na (Suc n'a)) (Suc n'a) = max na (Suc n'a)"
      using a1 dx by simp
  qed
qed

lemma maps: "maps f = (concat \<circ> map f)"
using maps_def comp_apply
by fastforce

definition make_sequent :: "nnf list \<Rightarrow> sequent" where
  "make_sequent l = map (\<lambda>p. (0,p)) l"

definition list_sequent :: "sequent \<Rightarrow> nnf list" where
  "list_sequent s = map snd s"

definition fv_list :: "nnf list \<Rightarrow> nat list" where
  "fv_list \<equiv> maps fv"

primrec is_axiom :: "nnf list \<Rightarrow> bool" where
  "is_axiom [] = False" |
  "is_axiom (p # t) = ((\<exists>b i v. p = Pre b i v \<and> Pre (\<not> b) i v \<in> set t))"

primrec member :: "'a \<Rightarrow> 'a list \<Rightarrow> bool" where
  "member _ [] = False" |
  "member a (h # t) = (if a = h then True else member a t)"

lemma member_set: "member a l = (a \<in> set l)"
by (induct l) auto

lemma stop: "stop [t @ [(0,r)]] (Pre (\<not> b) i v) l =
  (if member (Pre (\<not> b) i v) l then [] else [t @ [(0,r)]])"
by (induct l) simp_all

lemma pre: "(n,(m,Pre b i v) # xs) \<in> calculation(nfs) \<Longrightarrow>
    \<not> is_axiom (list_sequent ((m,Pre b i v) # xs)) \<Longrightarrow>
    (Suc n,xs@[(0,Pre b i v)]) \<in> calculation(nfs)"
  and con1: "(n,(m,Con p q) # xs) \<in> calculation(nfs) \<Longrightarrow>
    \<not> is_axiom (list_sequent ((m,Con p q) # xs)) \<Longrightarrow>
    (Suc n,xs@[(0,p)]) \<in> calculation(nfs)"
  and con2: "(n,(m,Con p q) # xs) \<in> calculation(nfs) \<Longrightarrow>
    \<not> is_axiom (list_sequent ((m,Con p q) # xs)) \<Longrightarrow>
    (Suc n,xs@[(0,q)]) \<in> calculation(nfs)"
  and dis: "(n,(m,Dis p q) # xs) \<in> calculation(nfs) \<Longrightarrow>
    \<not> is_axiom (list_sequent ((m,Dis p q) # xs)) \<Longrightarrow>
    (Suc n,xs@[(0,p),(0,q)]) \<in> calculation(nfs)"
  and uni: "(n,(m,Uni p) # xs) \<in> calculation(nfs) \<Longrightarrow>
    \<not> is_axiom (list_sequent ((m,Uni p) # xs)) \<Longrightarrow>
    (Suc n,xs@[(0,sv (bind (fresh ((concat \<circ> map fv) (list_sequent ((m,Uni p) # xs))))) p)])
      \<in> calculation(nfs)"
  and exi: "(n,(m,Exi p) # xs) \<in> calculation(nfs) \<Longrightarrow>
    \<not> is_axiom (list_sequent ((m,Exi p) # xs)) \<Longrightarrow>
    (Suc n,xs@[(0,sv (bind m) p),(Suc m,Exi p)]) \<in> calculation(nfs)"
by (auto simp: list_sequent_def maps inst_def stop member_set calculation.intros(2))

lemmas not_is_axiom_subs = pre con1 con2 dis uni exi

lemma calculation_init: "(0,k) \<in> calculation s = (k = s)"
using calculation.simps
by blast

lemma calculation_upwards:
  assumes "(n,k) \<in> calculation s" and "\<not> is_axiom (list_sequent (k))"
  shows "(\<exists>l. (Suc n,l) \<in> calculation s \<and> l \<in> set (solve k))"
proof (cases k)
  case Nil then show ?thesis using assms(1) calculation.intros(2) by auto
next
  case (Cons a _) then show ?thesis
  proof (cases a)
    case (Pair _ p) then show ?thesis
      using Cons assms calculation.intros(2)
        by (cases p) (fastforce simp: list_sequent_def stop member_set)+
  qed
qed

lemma calculation_downwards: "(Suc n,k) \<in> calculation s \<Longrightarrow>
  \<exists>t. (n,t) \<in> calculation s \<and> k \<in> set (solve t) \<and> \<not> is_axiom (list_sequent t)"
proof (erule calculation.cases)
  assume "Suc n = 0"
  then show ?thesis using list_sequent_def by simp
next
  fix m l k'
  assume 1: "Suc n = Suc m"
  and 2: "k = k'"
  and 3: "(m,l) \<in> calculation s"
  and 4: "k' \<in> set (solve l)"
  then show ?thesis
  proof (cases l)
    case Nil then show ?thesis using 1 2 3 4 list_sequent_def by fastforce
  next
    case (Cons a _) then show ?thesis
    proof (cases a)
      case (Pair _ p) then show ?thesis
        using 1 2 3 4 Cons list_sequent_def by (cases p) (auto simp: stop member_set)
    qed
  qed
qed
 
lemma calculation_calculation_child:
  "\<forall>s t. (Suc n,s) \<in> calculation t =
    (\<exists>k. k \<in> set (solve t) \<and> \<not> is_axiom (list_sequent t) \<and> (n,s) \<in> calculation k)"
by (induct n) (metis calculation.intros(2) calculation_downwards calculation_init,
    meson calculation.intros(2) calculation_downwards)

lemma calculation_progress:
  assumes "(n,a # l) \<in> calculation s" and "\<not> is_axiom (list_sequent (a # l))"
  shows "(\<exists>k. (Suc n,l@k) \<in> calculation s)"
proof (cases a)
  case (Pair _ p) then show ?thesis using assms by (cases p) (auto dest: not_is_axiom_subs)
qed

definition inc :: "nat \<times> sequent \<Rightarrow> nat \<times> sequent" where
  "inc \<equiv> \<lambda>(n,fs). (Suc n,fs)"

lemma inj_inc: "inj inc"
by (simp add: inc_def inj_on_def)

lemma calculation: "calculation s =
  insert (0,s) (inc ` (\<Union> (calculation ` {k. \<not> is_axiom (list_sequent s) \<and> k \<in> set (solve s)})))"
proof (rule set_eqI,simp add: split_paired_all)
  fix n k
  show "((n,k) \<in> calculation s) =
    (n = 0 \<and> k = s \<or> (n,k) \<in> inc ` (\<Union>x\<in>{k. \<not> is_axiom (list_sequent s) \<and> k \<in> set (solve s)}.
      calculation x))"
  by (cases n) (auto simp: calculation_init calculation_calculation_child inc_def)
qed

lemma calculation_is_axiom:
  assumes "is_axiom (list_sequent s)"
  shows "calculation s = {(0,s)}"
proof (rule set_eqI,simp add: split_paired_all)
  fix n k
  show "((n,k) \<in> calculation s) = (n = 0 \<and> k = s)"
  proof (rule iffI)
    assume "(n,k) \<in> calculation s" then show "(n = 0 \<and> k = s)"
      using assms calculation.simps calculation_calculation_child by metis
  next
    assume "(n = 0 \<and> k = s)" then show "(n,k) \<in> calculation s"
      using assms calculation.simps by blast
  qed
qed
 
lemma is_axiom_finite_calculation: "is_axiom (list_sequent s) \<Longrightarrow> finite (calculation s)"
by (simp add: calculation_is_axiom)

primrec failing_path :: "(nat \<times> sequent) set \<Rightarrow> nat \<Rightarrow> (nat \<times> sequent)" where
  "failing_path ns 0 = (SOME x. x \<in> ns \<and> fst x = 0 \<and> infinite (calculation (snd x)) \<and>
    \<not> is_axiom (list_sequent (snd x)))" |
  "failing_path ns (Suc n) = (let fn = failing_path ns n in 
    (SOME fsucn. fsucn \<in> ns \<and> fst fsucn = Suc n \<and> (snd fsucn) \<in> set (solve (snd fn)) \<and>
      infinite (calculation (snd fsucn)) \<and> \<not> is_axiom (list_sequent (snd fsucn))))"

lemma f0:
  assumes "f = failing_path (calculation s)"
  and "infinite (calculation s)"
  shows "f 0 \<in> (calculation s) \<and> fst (f 0) = 0 \<and> infinite (calculation (snd (f 0))) \<and>
    \<not> is_axiom (list_sequent (snd (f 0)))"
proof -
  have "\<And>p P. p \<notin> P \<or> fst p \<noteq> (0::nat) \<or> finite (calculation (snd p)) \<or>
    (SOME p. p \<in> P \<and> fst p = 0 \<and> infinite (calculation (snd p)) \<and>
      \<not> is_axiom (list_sequent (snd p))) \<in> P \<and> fst (SOME p. p \<in> P \<and> fst p = 0 \<and>
      infinite (calculation (snd p)) \<and> \<not> is_axiom (list_sequent (snd p))) = 0 \<and>
      infinite (calculation (snd (SOME p. p \<in> P \<and> fst p = 0 \<and>
      infinite (calculation (snd p)) \<and> \<not> is_axiom (list_sequent (snd p))))) \<and>
      \<not> is_axiom (list_sequent (snd (SOME p. p \<in> P \<and> fst p = 0 \<and>
      infinite (calculation (snd p)) \<and> \<not> is_axiom (list_sequent (snd p)))))"
  proof -
    fix p :: "nat \<times> (nat \<times> nnf) list" and P :: "(nat \<times> (nat \<times> nnf) list) set"
    have f1: "\<forall>p pa. \<not> p (pa::nat \<times> (nat \<times> nnf) list) \<or> p (Eps p)" by (metis someI)
    { assume "(SOME p. p \<in> P \<and> fst p = 0 \<and> infinite (calculation (snd p)) \<and>
      \<not> is_axiom (list_sequent (snd p))) \<notin> P \<or> fst (SOME p. p \<in> P \<and> fst p = 0 \<and>
      infinite (calculation (snd p)) \<and> \<not> is_axiom (list_sequent (snd p))) \<noteq> 0 \<or>
      finite (calculation (snd (SOME p. p \<in> P \<and> fst p = 0 \<and> infinite (calculation (snd p)) \<and>
      \<not> is_axiom (list_sequent (snd p))))) \<or> is_axiom (list_sequent (snd (SOME p. p \<in> P \<and>
      fst p = 0 \<and> infinite (calculation (snd p)) \<and> \<not> is_axiom (list_sequent (snd p)))))"
      then have "\<not> ((SOME p. p \<in> P \<and> fst p = 0 \<and> infinite (calculation (snd p)) \<and>
        \<not> is_axiom (list_sequent (snd p))) \<in> P \<and> fst (SOME p. p \<in> P \<and> fst p = 0 \<and>
        infinite (calculation (snd p)) \<and> \<not> is_axiom (list_sequent (snd p))) = 0 \<and>
        infinite (calculation (snd (SOME p. p \<in> P \<and> fst p = 0 \<and>
        infinite (calculation (snd p)) \<and> \<not> is_axiom (list_sequent (snd p))))) \<and>
        \<not> is_axiom (list_sequent (snd (SOME p. p \<in> P \<and> fst p = 0 \<and>
        infinite (calculation (snd p)) \<and> \<not> is_axiom (list_sequent (snd p))))))"
        by metis
      then have "\<not> (p \<in> P \<and> fst p = 0 \<and> infinite (calculation (snd p)) \<and>
        \<not> is_axiom (list_sequent (snd p)))"
        using f1 by (metis (mono_tags, lifting) someI) 
      then have "p \<notin> P \<or> fst p \<noteq> 0 \<or> finite (calculation (snd p)) \<or>
        (SOME p. p \<in> P \<and> fst p = 0 \<and> infinite (calculation (snd p)) \<and>
        \<not> is_axiom (list_sequent (snd p))) \<in> P \<and> fst (SOME p. p \<in> P \<and> fst p = 0 \<and>
        infinite (calculation (snd p)) \<and> \<not> is_axiom (list_sequent (snd p))) = 0 \<and>
        infinite (calculation (snd (SOME p. p \<in> P \<and> fst p = 0 \<and>
        infinite (calculation (snd p)) \<and> \<not> is_axiom (list_sequent (snd p))))) \<and>
        \<not> is_axiom (list_sequent (snd (SOME p. p \<in> P \<and> fst p = 0 \<and>
        infinite (calculation (snd p)) \<and> \<not> is_axiom (list_sequent (snd p)))))"
        by (metis (no_types) is_axiom_finite_calculation) }
     then show "p \<notin> P \<or> fst p \<noteq> 0 \<or> finite (calculation (snd p)) \<or>
       (SOME p. p \<in> P \<and> fst p = 0 \<and> infinite (calculation (snd p)) \<and>
       \<not> is_axiom (list_sequent (snd p))) \<in> P \<and> fst (SOME p. p \<in> P \<and> fst p = 0 \<and>
       infinite (calculation (snd p)) \<and> \<not> is_axiom (list_sequent (snd p))) = 0 \<and>
       infinite (calculation (snd (SOME p. p \<in> P \<and> fst p = 0 \<and>
       infinite (calculation (snd p)) \<and> \<not> is_axiom (list_sequent (snd p))))) \<and>
       \<not> is_axiom (list_sequent (snd (SOME p. p \<in> P \<and> fst p = 0 \<and>
       infinite (calculation (snd p)) \<and> \<not> is_axiom (list_sequent (snd p)))))"
       by blast
  qed 
  then have "\<And>ps. fst (0::nat, ps) \<noteq> 0 \<or> finite (calculation (snd (0::nat, ps))) \<or>
    (SOME p. p \<in> calculation ps \<and> fst p = 0 \<and> infinite (calculation (snd p)) \<and>
    \<not> is_axiom (list_sequent (snd p))) \<in> calculation ps \<and>
    fst (SOME p. p \<in> calculation ps \<and> fst p = 0 \<and>
    infinite (calculation (snd p)) \<and> \<not> is_axiom (list_sequent (snd p))) = 0 \<and>
    infinite (calculation (snd (SOME p. p \<in> calculation ps \<and> fst p = 0 \<and>
    infinite (calculation (snd p)) \<and> \<not> is_axiom (list_sequent (snd p))))) \<and>
    \<not> is_axiom (list_sequent (snd (SOME p. p \<in> calculation ps \<and> fst p = 0 \<and>
    infinite (calculation (snd p)) \<and> \<not> is_axiom (list_sequent (snd p)))))"
    by (meson calculation.simps)
  then show ?thesis
    using assms(1) assms(2) by auto
qed

lemma infinite_union: "finite Y \<Longrightarrow> infinite (Union (f ` Y)) \<Longrightarrow> \<exists>y. y \<in> Y \<and> infinite (f y)"
by auto

lemma finite_subs: "finite {w. \<not> is_axiom (list_sequent y) \<and> w \<in> set (solve y)}"
by simp

lemma fSuc:
  assumes "f = failing_path (calculation s)"
  and "f n \<in> calculation s \<and> fst (f n) = n \<and> infinite (calculation (snd (f n))) \<and>
    \<not> is_axiom (list_sequent (snd (f n)))"
  shows "f (Suc n) \<in> calculation s \<and> fst (f (Suc n)) = Suc n \<and> (snd (f (Suc n)))
    \<in> set (solve (snd (f n))) \<and> infinite (calculation (snd (f (Suc n)))) \<and>
    \<not> is_axiom (list_sequent (snd (f (Suc n))))"
proof -
  have "infinite (\<Union> (calculation ` {w. \<not> is_axiom (list_sequent (snd (f n))) \<and>
    w \<in> set (solve (snd (f n)))}))"
    using assms
    by (metis (mono_tags,lifting) Collect_cong calculation finite.insertI finite_imageI)
  then show ?thesis using assms calculation.intros(2) is_axiom_finite_calculation
    by simp (rule someI_ex,simp,metis prod.collapse)
qed

lemma is_path_f_0: "infinite (calculation s) \<Longrightarrow> failing_path (calculation s) 0 = (0,s)"
using calculation_init f0 prod.collapse
by metis

lemma is_path_f':
  assumes "f = failing_path (calculation s)"
  and "infinite (calculation s)"
  shows "f n \<in> calculation s \<and> fst (f n) = n \<and> infinite (calculation (snd (f n))) \<and>
    \<not> is_axiom (list_sequent (snd (f n)))"
using assms f0 fSuc
by (induct n) simp_all

lemma is_path_f:
  assumes "f = failing_path (calculation s)"
  and "infinite (calculation s)"
  shows "\<forall>n. f n \<in> calculation s \<and> fst (f n) = n \<and> (snd (f (Suc n))) \<in> set (solve (snd (f n))) \<and>
    infinite (calculation (snd (f n)))"
using assms is_path_f' fSuc
by simp

lemma adjust: "Suc n \<in> set l = (n \<in> set (adjust l))"
proof (induct l)
  case Nil then show ?case by simp
next
  case (Cons m _) then show ?case by (cases m) simp_all
qed

lemma ttt: "(\<And>e e'. \<forall>x. x \<in> set (fv p) \<longrightarrow> e x = e' x \<Longrightarrow> semantics m e p = semantics m e' p) \<Longrightarrow>
  \<forall>x. x \<in> set (adjust (fv p)) \<longrightarrow> e x = e' x \<Longrightarrow>
  (\<forall>z\<in>fst m. semantics m (\<lambda>x. case x of 0 \<Rightarrow> z | Suc n \<Rightarrow> e n) p) =
    (\<forall>z\<in>fst m. semantics m (\<lambda>x. case x of 0 \<Rightarrow> z | Suc n \<Rightarrow> e' n) p)"
proof -
  assume a1: "\<And>e e'. \<forall>x. x \<in> set (fv p) \<longrightarrow> e x = e' x \<Longrightarrow> semantics m e p = semantics m e' p"
  assume a2: "\<forall>x. x \<in> set (adjust (fv p)) \<longrightarrow> e x = e' x"
  have f3: "((\<forall>us. us \<in> fst m \<longrightarrow> semantics m (case_nat us e) p) \<noteq> (\<forall>us. us \<in> fst m \<longrightarrow>
    semantics m (case_nat us e') p)) = ((\<exists>us. us \<in> fst m \<and>
    \<not> semantics m (case_nat us e) p) = (\<forall>us. us \<notin> fst m \<or> semantics m (case_nat us e') p))"
    by blast
  obtain uus and uusa where
    f4: "((\<exists>us. us \<in> fst m \<and> \<not> semantics m (case_nat us e) p) =
      (\<forall>us. us \<notin> fst m \<or> semantics m (case_nat us e') p)) =
      (((\<forall>us. us \<notin> fst m \<or> semantics m (case_nat us e) p) \<or>
        (\<forall>us. us \<notin> fst m \<or> semantics m (case_nat us e') p)) \<and>
        (uusa \<in> fst m \<and> \<not> semantics m (case_nat uusa e) p \<or> uus \<in> fst m \<and>
        \<not> semantics m (case_nat uus e') p))"
    by (metis (no_types))
  then have "(\<exists>us. us \<in> fst m \<and> \<not> semantics m (case_nat us e) p) \<and>
    (\<exists>us. us \<in> fst m \<and> \<not> semantics m (case_nat us e') p) \<or>
    (uusa \<notin> fst m \<or> semantics m (case_nat uusa e) p) \<and> (uus \<notin> fst m \<or>
    semantics m (case_nat uus e') p)"
    using a2 a1 by (metis (no_types,lifting) Nitpick.case_nat_unfold Suc_pred' adjust neq0_conv)
  then have "(\<forall>us. us \<in> fst m \<longrightarrow> semantics m (case_nat us e) p) =
    (\<forall>us. us \<in> fst m \<longrightarrow> semantics m (case_nat us e') p)"
    using f4 f3 by blast
  then show ?thesis
    by blast
qed

lemma ttt': "(\<And>e e'. \<forall>x. x \<in> set (fv p) \<longrightarrow> e x = e' x \<Longrightarrow> semantics m e p = semantics m e' p) \<Longrightarrow>
  \<forall>x. x \<in> set (adjust (fv p)) \<longrightarrow> e x = e' x \<Longrightarrow>
  (\<exists>z\<in>fst m. semantics m (\<lambda>x. case x of 0 \<Rightarrow> z | Suc n \<Rightarrow> e n) p) =
    (\<exists>z\<in>fst m. semantics m (\<lambda>x. case x of 0 \<Rightarrow> z | Suc n \<Rightarrow> e' n) p)"
proof -
  assume a1: "\<And>e e'. \<forall>x. x \<in> set (fv p) \<longrightarrow> e x = e' x \<Longrightarrow> semantics m e p = semantics m e' p"
  assume a2: "\<forall>x. x \<in> set (adjust (fv p)) \<longrightarrow> e x = e' x"
  have f3: "\<forall>us f n. if n = 0 then (case n of 0 \<Rightarrow> us::unit list | Suc x \<Rightarrow> f x) =
    us else (case n of 0 \<Rightarrow> us | Suc x \<Rightarrow> f x) = f (n - 1)"
    by (simp add: Nitpick.case_nat_unfold)
  obtain uus and uusa where
    f4: "((\<forall>us. us \<notin> fst m \<or> \<not> semantics m (case_nat us e) p) =
      (\<exists>us. us \<in> fst m \<and> semantics m (case_nat us e') p)) =
      ((uusa \<in> fst m \<and> semantics m (case_nat uusa e) p \<or> uus \<in> fst m \<and>
      semantics m (case_nat uus e') p) \<and> ((\<forall>us. us \<notin> fst m \<or> \<not> semantics m (case_nat us e) p) \<or>
      (\<forall>us. us \<notin> fst m \<or> \<not> semantics m (case_nat us e') p)))"
    by blast
  have "(uusa \<notin> fst m \<or> \<not> semantics m (case_nat uusa e) p) \<and> (uus \<notin> fst m \<or>
    \<not> semantics m (case_nat uus e') p) \<or> (\<exists>us. us \<in> fst m \<and> semantics m (case_nat us e) p) \<and>
      (\<exists>us. us \<in> fst m \<and> semantics m (case_nat us e') p)"
    using f3 a2 a1
    proof -
      obtain nn :: "(nat \<Rightarrow> proxy) \<Rightarrow> (nat \<Rightarrow> proxy) \<Rightarrow> nat" where
        f1: "\<forall>f fa. nn fa f \<in> set (fv p) \<and> f (nn fa f) \<noteq> fa (nn fa f) \<or>
          semantics m f p = semantics m fa p"
        using a1 by moura
      have "\<forall>p f n. if n = 0 then (case n of 0 \<Rightarrow> p::proxy | Suc x \<Rightarrow> f x) = p else
        (case n of 0 \<Rightarrow> p | Suc x \<Rightarrow> f x) = f (n - 1)"
        by (simp add: Nitpick.case_nat_unfold)
      then show ?thesis
        using f1 by (metis (no_types) Suc_pred' a2 adjust not_gr0)
    qed
  then show ?thesis
    using f4 by blast
qed

lemma eval_cong: "\<forall>x. x \<in> set (fv p) \<longrightarrow> e x = e' x \<Longrightarrow> semantics m e p = semantics m e' p"
proof (induct p arbitrary: e e')
  case Pre then show ?case using map_cong fv.simps(1) semantics.simps(1) by metis
next
  case Con then show ?case using Un_iff fv.simps(2) semantics.simps(2) set_append by metis
next
  case Dis then show ?case using Un_iff fv.simps(3) semantics.simps(3) set_append by metis
next
  case Uni then show ?case using ttt by simp
next
  case Exi then show ?case using ttt' by simp
qed

lemma semantics_alternative_def2: "semantics_alternative m e s = (\<exists>p. p \<in> set s \<and> semantics m e p)"
by (induct s) auto

lemma semantics_alternative_append: "semantics_alternative m e (s @ s') =
  ((semantics_alternative m e s) \<or> (semantics_alternative m e s'))"
by (induct s) auto

lemma fv_list_cons: "fv_list (a # list) = (fv a) @ (fv_list list)"
by (simp add: fv_list_def maps)

lemma semantics_alternative_cong: "(\<forall>x. x \<in> set (fv_list s) \<longrightarrow> e x = e' x) \<longrightarrow> 
  semantics_alternative m e s = semantics_alternative m e' s" 
by (induct s) (simp_all,metis eval_cong Un_iff set_append fv_list_cons)

section "Soundness"

lemma ball: "\<forall>x \<in> m. P x = Q x \<Longrightarrow> (\<exists>x \<in> m. P x) = (\<exists>x \<in> m. Q x)"
by simp_all

definition bump' :: "(nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> nat" where
  "bump' f x \<equiv> (case x of 0 \<Rightarrow> 0 | Suc n \<Rightarrow> Suc (f n))"

lemma bump': "increase f x = bump' f x"
by (metis Nitpick.case_nat_unfold increase.simps Suc_pred' bump'_def not_gr0)

lemma sss: "semantics m e (sv f p) = semantics m (e \<circ> f) p \<Longrightarrow>
  (\<And>p e e' m. \<forall>x. x \<in> set (fv p) \<longrightarrow> e x = e' x \<Longrightarrow> semantics m e p = semantics m e' p) \<Longrightarrow>
  (\<forall>z\<in>fst m. semantics m (case_nat z e \<circ> increase f) p) =
    (\<forall>z\<in>fst m. semantics m (\<lambda>x. case x of 0 \<Rightarrow> z | Suc n \<Rightarrow> (e \<circ> f) n) p)"
proof -
  assume a1: "\<And>p e e' m. \<forall>x. x \<in> set (fv p) \<longrightarrow> e x = e' x \<Longrightarrow> semantics m e p = semantics m e' p"
  obtain pp :: proxy and ppa :: proxy where
    f2: "((\<exists>pa. pa \<in> fst m \<and> \<not> semantics m (case_nat pa e \<circ> increase f) p) = (\<forall>pa. pa \<notin> fst m \<or>
      semantics m (case_nat pa (e \<circ> f)) p)) = (((\<forall>pa. pa \<notin> fst m \<or> semantics m (case_nat pa e \<circ>
      increase f) p) \<or> (\<forall>pa. pa \<notin> fst m \<or> semantics m (case_nat pa (e \<circ> f)) p)) \<and> (ppa \<in> fst m \<and>
      \<not> semantics m (case_nat ppa e \<circ> increase f) p \<or> pp \<in> fst m \<and>
      \<not> semantics m (case_nat pp (e \<circ> f)) p))"
    by moura
  have f3: "\<forall>n f fa p. (\<exists>na. na \<in> set (fv n) \<and> f na \<noteq> fa na) \<or> semantics p f n = semantics p fa n"
    using a1 by (metis (no_types))
  obtain nn :: "(nat \<Rightarrow> proxy) \<Rightarrow> (nat \<Rightarrow> proxy) \<Rightarrow> nnf \<Rightarrow> nat" where
    "\<forall>x1 x2 x3. (\<exists>v4. v4 \<in> set (fv x3) \<and> x2 v4 \<noteq> x1 v4) = (nn x1 x2 x3 \<in> set (fv x3) \<and> x2
      (nn x1 x2 x3) \<noteq> x1 (nn x1 x2 x3))"
    by moura
  then have f4: "\<forall>n f fa p. nn fa f n \<in> set (fv n) \<and> f (nn fa f n) \<noteq> fa (nn fa f n) \<or>
      semantics p f n = semantics p fa n"
    using f3 by presburger
  have f5: "\<forall>p f n. if n = 0 then (case n of 0 \<Rightarrow> p::proxy | Suc x \<Rightarrow> f x) = p else
    (case n of 0 \<Rightarrow> p | Suc x \<Rightarrow> f x) = f (n - 1)"
    by (metis (no_types) Nitpick.case_nat_unfold)
  then have f6: "(case increase f (nn (case_nat ppa (e \<circ> f)) (case_nat ppa e \<circ> increase f) p) of 0 \<Rightarrow> ppa |
      Suc x \<Rightarrow> e x) = ppa \<and> (case_nat ppa e \<circ> increase f) (nn (case_nat ppa (e \<circ> f)) (case_nat ppa e \<circ>
      increase f) p) \<noteq> (case nn (case_nat ppa (e \<circ> f)) (case_nat ppa e \<circ> increase f) p of 0 \<Rightarrow> ppa |
      Suc x \<Rightarrow> (e \<circ> f) x) \<longrightarrow> nn (case_nat ppa (e \<circ> f)) (case_nat ppa e \<circ> increase f) p \<noteq> 0"
    by (metis o_apply)
  have f7: "\<forall>n f na. if na = 0 then (case na of 0 \<Rightarrow> n::nat | Suc x \<Rightarrow> f x) = n else
    (case na of 0 \<Rightarrow> n | Suc x \<Rightarrow> f x) = f (na - 1)"
    by (simp add: Nitpick.case_nat_unfold)
  have "(case_nat ppa e \<circ> increase f) (nn (case_nat ppa (e \<circ> f)) (case_nat ppa e \<circ> increase f) p) \<noteq>
    (case nn (case_nat ppa (e \<circ> f)) (case_nat ppa e \<circ> increase f) p of 0 \<Rightarrow> ppa | Suc x \<Rightarrow> (e \<circ> f) x)
    \<longrightarrow> nn (case_nat ppa (e \<circ> f)) (case_nat ppa e \<circ> increase f) p \<noteq> 0"
    using f6 bump'_def by fastforce
  then have f8: "(case_nat ppa e \<circ> increase f) (nn (case_nat ppa (e \<circ> f)) (case_nat ppa e \<circ> increase f) p)
    \<noteq> (case nn (case_nat ppa (e \<circ> f)) (case_nat ppa e \<circ> increase f) p of 0 \<Rightarrow> ppa | Suc x \<Rightarrow> (e \<circ> f) x)
    \<longrightarrow> (case_nat ppa e \<circ> increase f) (nn (case_nat ppa (e \<circ> f)) (case_nat ppa e \<circ> increase f) p) =
    (case nn (case_nat ppa (e \<circ> f)) (case_nat ppa e \<circ> increase f) p of 0 \<Rightarrow> ppa | Suc x \<Rightarrow> (e \<circ> f) x)"
    using f7 f5 bump'_def bump' by force
  have f9: "nn (case_nat pp (e \<circ> f)) (case_nat pp e \<circ> increase f) p \<noteq> 0 \<longrightarrow> (case_nat pp e \<circ> increase f)
    (nn (case_nat pp (e \<circ> f)) (case_nat pp e \<circ> increase f) p) = (case nn (case_nat pp (e \<circ> f))
    (case_nat pp e \<circ> increase f) p of 0 \<Rightarrow> pp | Suc x \<Rightarrow> (e \<circ> f) x)"
    using f7 f5 by (simp add: bump'_def bump')
  then have "(case_nat pp e \<circ> increase f) (nn (case_nat pp (e \<circ> f)) (case_nat pp e \<circ> increase f) p) \<noteq>
    (case nn (case_nat pp (e \<circ> f)) (case_nat pp e \<circ> increase f) p of 0 \<Rightarrow> pp | Suc x \<Rightarrow> (e \<circ> f) x) \<longrightarrow>
    increase f (nn (case_nat pp (e \<circ> f)) (case_nat pp e \<circ> increase f) p) = 0"
    using f7 by (metis bump' bump'_def)
  then have "(case_nat pp e \<circ> increase f) (nn (case_nat pp (e \<circ> f)) (case_nat pp e \<circ> increase f) p) =
    (case nn (case_nat pp (e \<circ> f)) (case_nat pp e \<circ> increase f) p of 0 \<Rightarrow> pp | Suc x \<Rightarrow> (e \<circ> f) x)"
    using f9 f5 by (metis (no_types) o_apply)
  then have "(\<exists>pa. pa \<in> fst m \<and> \<not> semantics m (case_nat pa e \<circ> increase f) p) \<and> (\<exists>pa. pa \<in> fst m \<and>
    \<not> semantics m (case_nat pa (e \<circ> f)) p) \<or> (ppa \<notin> fst m \<or>
    semantics m (case_nat ppa e \<circ> increase f) p) \<and> (pp \<notin> fst m \<or> semantics m (case_nat pp (e \<circ> f)) p)"
    using f8 f4 by blast
  then show ?thesis
    using f2 by blast
qed

lemma eval_subst: "semantics m e (sv f p) = semantics m (e \<circ> f) p"
by (induct p arbitrary: e f) (simp,simp,simp,
  simp add: sss eval_cong,simp add: Nitpick.case_nat_unfold ball bump'_def eval_cong bump')

definition bind' :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "bind' y x \<equiv> (case x of 0 \<Rightarrow> y | Suc n \<Rightarrow> n)"

lemma bind': "bind y x = bind' y x"
by (metis Nitpick.case_nat_unfold bind.simps Suc_pred' bind'_def not_gr0)

lemma eval_bind: "semantics m e (sv (bind n) p) = semantics m (case_nat (e n) e) p"
using eval_cong eval_subst
by (simp add: Nitpick.case_nat_unfold bind'_def bind')

lemma sound_Uni:
  assumes "u \<notin> set (fv_list (Uni p # s))"
  and "valid (s@[sv (bind u) p])"
  shows "valid (Uni p # s)"
proof (clarsimp simp: valid_def)
  fix M I e z
  show "is_model_environment (M,I) e \<Longrightarrow> \<not> semantics_alternative (M,I) e s \<Longrightarrow> z \<in> M \<Longrightarrow>
    semantics (M,I) (case_nat z e) p"
  proof -
    assume "z \<in> M" and "\<not> semantics_alternative (M,I) e s" and  "is_model_environment (M,I) e"
    have 1: "semantics (M,I) (case_nat z (e(u:=z))) p = semantics (M,I) (case_nat z e) p"
      using assms
      by (clarsimp simp: Nitpick.case_nat_unfold fv_list_cons intro!: eval_cong[rule_format])
        (metis One_nat_def Suc_pred' adjust)
    have "is_model_environment (M,I) (e(u := z)) \<longrightarrow> semantics_alternative (M,I) (e(u := z))
      (s @ [sv (bind u) p])"
      using assms valid_def by blast
    then have 2: "(\<forall>n. (if n = u then z else e n) \<in> M) \<longrightarrow>
      semantics_alternative (M,I) (e(u := z)) s \<or> semantics (M,I) (case_nat z e) p"
      using 1 eval_bind is_model_environment_def semantics_alternative_append by simp
    have 3: "u \<notin> set (adjust (fv p)) \<and> u \<notin> set (fv_list s)"
      using assms fv_list_cons by simp
    have "\<forall>n. e n \<in> M"
      using \<open>is_model_environment (M,I) e\<close> is_model_environment_def by simp
    then show ?thesis
      using 2 3 \<open>z \<in> M\<close> \<open>\<not> semantics_alternative (M,I) e s\<close>
      by (metis (no_types,lifting) fun_upd_apply semantics_alternative_cong)
  qed
qed
  
lemma sound_Exi: "valid (s@[sv (bind u) p,Exi p]) \<Longrightarrow> valid (Exi p # s)"
using valid_def eval_bind
by (simp add: semantics_alternative_append,metis is_model_environment_def prod.sel(1))

lemma max_exists: "finite (X::nat set) \<Longrightarrow> X \<noteq> {} \<longrightarrow> (\<exists>x. x \<in> X \<and> (\<forall>y. y \<in> X \<longrightarrow> y \<le> x))"
using Max.coboundedI Max_in
by blast

definition init :: "sequent \<Rightarrow> bool" where
  "init s == \<forall>x \<in> (set s). fst x = 0"

definition is_Exi :: "nnf \<Rightarrow> bool" where
  "is_Exi f \<equiv> case f of Exi _ \<Rightarrow> True | _ \<Rightarrow> False"

lemma is_Exi: "\<not> is_Exi (Pre b i v) \<and> \<not> is_Exi (Con p q) \<and> \<not> is_Exi (Dis p q) \<and> \<not> is_Exi (Uni p)"
using is_Exi_def
by simp

lemma index0:
  assumes "init s"
  shows "\<forall>k m p. (n,k) \<in> calculation s \<longrightarrow> (m,p) \<in> (set k) \<longrightarrow> \<not> is_Exi p \<longrightarrow> m = 0"
proof (induct n)
  case 0 then show ?case using assms init_def calculation_init by fastforce
next
  case IH: (Suc x)
    then show ?case
    proof (intro allI impI)
      fix k m p
      show "(Suc x,k) \<in> calculation s \<Longrightarrow> (m,p) \<in> (set k) \<Longrightarrow> \<not> is_Exi p \<Longrightarrow> m = 0"
      proof -
        assume "(Suc x,k) \<in> calculation s" and 1: "(m,p) \<in> (set k)" and 2: "\<not> is_Exi p"
        then obtain t
          where 3: "(x,t) \<in> calculation s \<and> k \<in> set (solve t) \<and> \<not> is_axiom (list_sequent t)"
          using calculation_downwards by blast
        then show ?thesis
        proof (cases t)
          case Nil then show ?thesis using assms IH 1 3 by simp
        next
         case (Cons a _) then show ?thesis
         proof (cases a)
          case (Pair _ q)
            then show ?thesis using 1 2 3 IH Cons
            by (cases q) (fastforce simp: list_sequent_def stop is_Exi_def member_set)+
        qed
      qed
    qed
  qed
qed

lemma maxl: "\<forall>v \<in> set l. v \<le> maxl l"
by (induct l) (auto simp: max_def mmm)

lemma fresh: "fresh l \<notin> (set l)"
unfolding fresh'_def fresh'
using maxl maxl.simps not_less_eq_eq order_refl empty_iff list.set(1) null.simps(2) list.exhaust
by metis

lemma soundness':
  assumes "init s"
  and "m \<in> (fst ` (calculation s))"
  and "\<forall>y u. (y,u) \<in> (calculation s) \<longrightarrow> y \<le> m"
  shows "\<forall>n t. h = m - n \<and> (n,t) \<in> calculation s \<longrightarrow> valid (list_sequent t)"
proof (induct h)
  case 0 then show ?case
    proof (intro allI impI)
      fix n t
      show "0 = m - n \<and> (n,t) \<in> calculation s \<Longrightarrow> valid (list_sequent t)"
      proof -
        assume *: "0 = m - n \<and> (n,t) \<in> calculation s"
        then show ?thesis
        proof (cases "is_axiom (list_sequent t)")
          case True then show ?thesis
            proof (cases t)
              case Nil then show ?thesis using True list_sequent_def by simp
            next
              case Cons then show ?thesis
              using True list_sequent_def valid_def semantics_alternative_def2
              by simp (metis (no_types,lifting) semantics.simps(1))
            qed
        next
          case False
            then have "n = m" using assms * by fastforce
            then show ?thesis using assms * False
            by (meson calculation_upwards le_SucI le_antisym n_not_Suc_n)
        qed
      qed
    qed
next
  case IH: (Suc x) then show ?case
    proof (intro allI impI)
      fix n t
      show "Suc x = m - n \<and> (n,t) \<in> calculation s \<Longrightarrow> valid (list_sequent t)"
      proof -
        assume "Suc x = m - n \<and> (n,t) \<in> calculation s"
        then have *: "Suc x = m - n" and **: "(n,t) \<in> calculation s"
          by (simp,simp)
        then show ?thesis
        proof (cases "is_axiom (list_sequent t)")
          case True then show ?thesis
            proof (cases t)
              case Nil then show ?thesis using True list_sequent_def by simp
            next
              case Cons then show ?thesis
              using True list_sequent_def valid_def semantics_alternative_def2
              by simp (metis (no_types,lifting) semantics.simps(1))
            qed
        next
          case notAxiom: False then show ?thesis
            proof (cases "\<exists>a f list. t = (a,Uni f) # list")
              case True
              then obtain a and f and list where 1: "t = (a,Uni f) # list" by blast
              then show ?thesis using IH assms * ** fv_list_def fresh list_sequent_def inst_def
              by simp (frule calculation.intros(2),simp add: maps,
                  metis (no_types,lifting) Suc_leD diff_Suc_Suc diff_diff_cancel diff_le_self
                  le_SucI list.map map_append snd_conv sound_Uni)
        next
          case notUni: False then show ?thesis
            proof (cases "\<exists>a f list. t = (a,Exi f) # list")
             case True
              then obtain a and f and list where 1: "t = (a,Exi f) # list" by blast
              then show ?thesis using IH assms * ** fresh list_sequent_def inst_def
                by simp (frule calculation.intros(2),simp,
                   metis (no_types,lifting) Suc_leD diff_Suc_Suc diff_diff_cancel diff_le_self
                    le_SucI list.map map_append snd_conv sound_Exi)
            next
              case notExi: False
              then show ?thesis
              proof (cases t)
                case Nil
                then show ?thesis using assms notAxiom IH * ** calculation_upwards
                   by (metis (no_types,lifting) calculation.intros(2) diff_Suc_Suc diff_diff_cancel
                     diff_le_self list.set_intros(1) not_less_eq_eq solve.simps(1))
              next
                case (Cons a list)
                then show ?thesis
                using IH
                proof (simp add: valid_def semantics_alternative_def2,intro allI impI)
                  fix as gs g
                  show "\<forall>n t. x = m - n \<and> (n,t) \<in> calculation s \<longrightarrow>
                       (\<forall>a b e. is_model_environment (a,b) e \<longrightarrow> (\<exists>p. p \<in> set (list_sequent t) \<and>
                         semantics (a,b) e p))
                       \<Longrightarrow> is_model_environment (as,gs) g \<Longrightarrow> \<exists>p. p \<in> set (list_sequent (a # list))
                         \<and> semantics (as,gs) g p"
                  proof -
                    assume ***: "is_model_environment (as,gs) g"
                    and IH': "\<forall>n t. x = m - n \<and> (n,t) \<in> calculation s \<longrightarrow>
                               (\<forall>a b e. is_model_environment (a,b) e \<longrightarrow>
                               (\<exists>p. p \<in> set (list_sequent t) \<and> semantics (a,b) e p))"
                    then show ?thesis
                    proof (cases a)
                      case (Pair _ p) then show ?thesis
                        proof (cases p)
                          case (Pre b i v) then show ?thesis
                            using IH' assms * ** Cons notAxiom *** Pair
                            by (fastforce simp: list_sequent_def dest!: pre)
                        next
                          case (Con q r)
                            then have 1: "(Suc n,list @ [(0,q)]) \<in> calculation s"
                            using ** Pair con1 local.Cons notAxiom by blast
                            then have 2: "x = m - Suc n \<and> (Suc n,list @ [(0,q)]) \<in> calculation s"
                            using * by linarith
                            have 3: "(Suc n,list @ [(0,r)]) \<in> calculation s"
                            using ** Pair Con con2 local.Cons notAxiom by blast
                            then have 4: "x = m - Suc n \<and> (Suc n,list @ [(0,r)]) \<in> calculation s"
                            using * by linarith
                            then have 5: "(Suc n,list @ [(0,q)]) \<in> calculation s \<longrightarrow>
                              (\<forall>a b e. is_model_environment (a,b) e \<longrightarrow>
                              (\<exists>p. p \<in> set (list_sequent (list @ [(0,q)])) \<and> semantics (a,b) e p))"
                            using IH' by blast
                            then have "x = m - Suc n \<and> (Suc n,list @ [(0,r)]) \<in> calculation s \<longrightarrow>
                            (\<forall>a b e. is_model_environment (a,b) e \<longrightarrow>
                            (\<exists>p. p \<in> set (list_sequent (list @ [(0,r)])) \<and> semantics (a,b) e p))"
                            using 2 IH' by blast
                            then show ?thesis
                            using 5
                            proof (elim impE)
                              show "(Suc n,list @ [(0,q)]) \<in> calculation s" using 1 by simp
                            next
                              show "\<forall>a b e. is_model_environment (a,b) e \<longrightarrow>
                                (\<exists>p. p \<in> set (list_sequent (list @ [(0,q)])) \<and>
                                  semantics (a,b) e p) \<Longrightarrow>
                                x = m - Suc n \<and> (Suc n,list @ [(0,r)]) \<in> calculation s"
                              using 2 3 by blast
                            next
                              show "\<forall>a b e. is_model_environment (a,b) e \<longrightarrow>
                                (\<exists>p. p \<in> set (list_sequent (list @ [(0,r)])) \<and>
                                  semantics (a,b) e p) \<Longrightarrow>
                                 (Suc n,list @ [(0,q)]) \<in> calculation s"
                              using 1 by blast
                            next show "\<forall>a b e. is_model_environment (a,b) e \<longrightarrow>
                              (\<exists>p. p \<in> set (list_sequent (list @ [(0,r)])) \<and> semantics (a,b) e p) \<Longrightarrow>
                              \<forall>a b e. is_model_environment (a,b) e \<longrightarrow>
                              (\<exists>p. p \<in> set (list_sequent (list @ [(0,q)])) \<and> semantics (a,b) e p) \<Longrightarrow>
                              \<exists>p. p \<in> set (list_sequent (a # list)) \<and> semantics (as,gs) g p"
                              using Con *** Pair list_sequent_def
                              by simp (metis (no_types,lifting) semantics.simps(2))
                            qed
                      next
                        case (Dis q r)
                        then have "x = m - Suc n \<and> (Suc n,list @ [(0,q),(0,r)]) \<in> calculation s \<longrightarrow>
                                  (\<forall>a b e. is_model_environment (a,b) e \<longrightarrow>
                                  (\<exists>p. p \<in> set (list_sequent (list @ [(0,q),(0,r)])) \<and>
                                  semantics (a,b) e p))"
                                  using * IH' by blast
                        then show ?thesis
                        proof (elim impE)
                          have 1: "(Suc n,list @ [(0,q),(0,r)]) \<in> calculation s"
                            using ** Dis Pair dis local.Cons notAxiom by blast
                          have "x = m - Suc n" using "*" by linarith
                          then show "x = m - Suc n \<and> (Suc n,list @ [(0,q),(0,r)]) \<in> calculation s"
                            using 1 by simp
                        next
                          show "\<forall>a b e. is_model_environment (a,b) e \<longrightarrow>
                               (\<exists>p. p \<in> set (list_sequent (list @ [(0,q),(0,r)])) \<and>
                                 semantics (a,b) e p) \<Longrightarrow>
                                 \<exists>p. p \<in> set (list_sequent (a # list)) \<and> semantics (as,gs) g p"
                            using Dis *** Pair list_sequent_def
                            by simp (metis (no_types,lifting) semantics.simps(3))
                        qed
                    next
                      case Uni then show ?thesis
                        using notUni Pair Cons by blast
                    next
                      case Exi then show ?thesis
                        using notExi Pair Cons by blast
                    qed
                  qed
                qed
              qed
            qed
          qed
        qed
      qed
    qed
  qed
qed

lemma list_make_sequent_inverse: "list_sequent (make_sequent s) = s"
using list_sequent_def make_sequent_def
by (induct s) simp_all

lemma soundness:
  assumes "finite (calculation (make_sequent s))"
  shows "valid s"
proof -
  have "init (make_sequent s)" and "finite (fst ` (calculation (make_sequent s)))"
    using assms by (simp add: init_def make_sequent_def,simp)
  then show ?thesis using assms soundness' list_make_sequent_inverse max_exists
    by (metis (mono_tags,lifting) empty_iff fst_conv image_eqI calculation.intros(1))
qed

section "Contains / Considers"

definition contains :: "(nat \<Rightarrow> (nat \<times> sequent)) \<Rightarrow> nat \<Rightarrow> nat \<times> nnf \<Rightarrow> bool" where
  "contains f n nf \<equiv> nf \<in> set (snd (f n))"

definition considers :: "(nat \<Rightarrow> (nat \<times> sequent)) \<Rightarrow> nat \<Rightarrow> nat \<times> nnf \<Rightarrow> bool" where
  "considers f n nf \<equiv> case snd (f n) of [] \<Rightarrow> False | (x # xs) \<Rightarrow> x = nf"

lemma progress:
  assumes "f = failing_path (calculation s)"
  and "infinite (calculation s)"
  shows "snd (f n) = a # l \<longrightarrow> (\<exists>zs'. snd (f (Suc n)) = l@zs')"
proof -
  obtain suc: "(snd (f (Suc n))) \<in> set (solve (snd (f n)))" using assms is_path_f by blast
  then show ?thesis
  proof (cases a)
    case (Pair _ p)
    then show ?thesis using suc
    by (induct p,safe,simp_all add: stop split: if_splits) blast
  qed
qed

lemma contains_considers':
  assumes "f = failing_path (calculation s)"
  and "infinite (calculation s)"
  shows "\<forall>n ys. snd (f n) = xs@y # ys \<longrightarrow> (\<exists>m zs'. snd (f (n+m)) = y # zs')"
proof (induct xs)
  case Nil then show ?case using append.simps(1) by (metis Nat.add_0_right)
next
  case Cons then show ?case using append.simps(2)
    by (metis (no_types,lifting) add_Suc_shift append_assoc assms progress)
qed

lemma contains_considers:
  assumes "f = failing_path (calculation s)"
  and "infinite (calculation s)"
  and "contains f n y"
  shows "(\<exists>m. considers f (n+m) y)"
using assms 
by (clarsimp simp: contains_def considers_def dest!: split_list_first)
  (frule contains_considers'[rule_format],simp,simp,metis (mono_tags,lifting) list.simps(5))

lemma contains_propagates_Pre:
  assumes "f = failing_path (calculation s)"
  and "infinite (calculation s)"
  and "contains f n (0,Pre b i v)"
  shows "contains f (n+q) (0,Pre b i v)"
proof (induct q)
  case 0 then show ?case using assms by simp
next
  case IH: (Suc q')
  then have "\<exists>ys zs. snd (f (n + q')) = ys @ (0,Pre b i v) # zs \<and> (0,Pre b i v) \<notin> set ys"
    by (meson contains_def split_list_first)
  then obtain ys and zs where 1:
    "snd (f (n + q')) = ys @ (0,Pre b i v) # zs \<and> (0,Pre b i v) \<notin> set ys"
    by blast
  then have 2: "(snd (f (Suc (n + q')))) \<in> set (solve (snd (f (n + q'))))"
    using assms is_path_f by blast
  then show ?case
  proof (cases ys)
    case Nil
    then show ?thesis using 1 2 contains_def
      by (simp add: stop split: if_splits)
  next
    case (Cons a _) then show ?thesis
      proof (cases a)
        case (Pair _ p) then show ?thesis
          using 1 contains_def assms Cons progress by fastforce
      qed
  qed
qed

lemma contains_propagates_Con:
  assumes "f = failing_path (calculation s)"
  and "infinite (calculation s)"
  and "contains f n (0,Con p q)"
  shows "(\<exists>y. contains f (n+y) (0,p) \<or> contains f (n+y) (0,q))"
proof -
  have "(\<exists>l. considers f (n+l) (0,Con p q))" using assms contains_considers by blast
  then obtain l where 1: "considers f (n+l) (0,Con p q)" by blast
  then have 2: "(snd (f (Suc (n + l)))) \<in> set (solve (snd (f (n + l))))"
    using assms is_path_f by blast
  then show ?thesis
  proof (cases "snd (f (n + l))")
    case Nil then show ?thesis using 1 considers_def by simp
  next
    case Cons then show ?thesis using 1 2 considers_def contains_def
      by (rule_tac x="Suc l" in exI) auto
  qed
qed

lemma contains_propagates_Dis:
  assumes "f = failing_path (calculation s)"
  and "infinite (calculation s)"
  and "contains f n (0,Dis p q)"
  shows "(\<exists>y. contains f (n+y) (0,p) \<and> contains f (n+y) (0,q))"
proof -
  have "(\<exists>l. considers f (n+l) (0,Dis p q))" using assms contains_considers by blast
  then obtain l where 1: "considers f (n+l) (0,Dis p q)" by blast
  then have 2: "(snd (f (Suc (n + l)))) \<in> set (solve (snd (f (n + l))))"
    using assms is_path_f by blast
  then show ?thesis
  proof (cases "snd (f (n + l))")
    case Nil then show ?thesis using 1 considers_def by simp
  next
    case Cons then show ?thesis using 1 2 considers_def contains_def
      by (rule_tac x="Suc l" in exI) simp_all
  qed
qed

lemma contains_propagates_Uni:
  assumes "f = failing_path (calculation s)"
  and "infinite (calculation s)"
  and "contains f n (0,Uni p)"
  shows "(\<exists>y. contains f (Suc(n+y)) (0,(sv (bind (fresh (fv_list (map snd (snd (f (n+y))))))) p)))"
proof -
  have "(\<exists>l. considers f (n+l) (0,Uni p))" using assms contains_considers by blast
  then obtain l where 1: "considers f (n+l) (0,Uni p)" by blast
  then have 2: "(snd (f (Suc (n + l)))) \<in> set (solve (snd (f (n + l))))"
    using assms is_path_f by blast
  then show ?thesis
  proof (cases "snd (f (n + l))")
    case Nil then show ?thesis using 1 considers_def by simp
  next
    case Cons then show ?thesis using 1 2 considers_def contains_def inst_def
      by (rule_tac x="l" in exI) (simp add: fv_list_def maps_def)
  qed
qed

lemma contains_propagates_Exi:
  assumes "f = failing_path (calculation s)"
  and "infinite (calculation s)"
  and "contains f n (m,Exi p)"
  shows "(\<exists>y. (contains f (n+y) (0,(sv (bind m) p)) \<and> (contains f (n+y) (Suc m,Exi p))))"
proof -
  have "(\<exists>l. considers f (n+l) (m,Exi p))" using assms contains_considers by blast
  then obtain l where 1: "considers f (n+l) (m,Exi p)" by blast
  then have 2: "(snd (f (Suc (n + l)))) \<in> set (solve (snd (f (n + l))))"
    using assms is_path_f by blast
  then show ?thesis
  proof (cases "snd (f (n + l))")
    case Nil then show ?thesis using 1 considers_def by simp
  next
    case Cons then show ?thesis using 1 2 considers_def contains_def inst_def
      by (rule_tac x="Suc l" in exI) simp
  qed
qed

lemma Exi_downward:
  assumes "f = failing_path (calculation s)"
  and "infinite (calculation s)"
  and "init s"
  shows "\<forall>m. (Suc m,Exi g) \<in> set (snd (f n)) \<longrightarrow> (\<exists>n'. (m,Exi g) \<in> set (snd (f n')))"
proof (induct n)
  case 0 then show ?case using assms init_def is_path_f_0 by fastforce
next
  case IH: (Suc x)
  then have fxSuc: "f x \<in> calculation s \<and> fst (f x) = x \<and>
    snd (f (Suc x)) \<in> set (solve (snd (f x))) \<and> infinite (calculation (snd (f x)))"
    using assms is_path_f by blast
  then show ?case
  proof (cases "f x")
    case fxPair: (Pair _ l)
    then show ?thesis
    proof (cases l)
      case Nil then show ?thesis using fxSuc fxPair by simp
    next
      case (Cons a _) then show ?thesis
      proof (cases a)
        case (Pair _ p) then show ?thesis
        proof (cases p)
          case Pre then show ?thesis using IH fxSuc fxPair Cons Pair
            by (simp add: stop split: if_splits)
        next
          case Con then show ?thesis using IH fxSuc fxPair Cons Pair
            by (simp split: if_splits) fastforce
        next
          case Dis then show ?thesis using IH fxSuc fxPair Cons Pair
            by (simp split: if_splits)
        next
          case Uni then show ?thesis using IH fxSuc fxPair Cons Pair
            by (simp split: if_splits)
        next
          case Exi then show ?thesis using IH fxSuc fxPair Cons Pair
            by (simp split: if_splits) (metis list.set_intros(1) snd_eqD)
        qed
      qed
    qed
  qed
qed
   
lemma Exi0:
  assumes "f = failing_path (calculation s)"
  and "infinite (calculation s)"
  and "init s"
  shows "\<forall>n. contains f n (m,Exi g) \<longrightarrow> (\<exists>n'. contains f n' (0,Exi g))"
using assms Exi_downward contains_def
by (induct m) auto
     
lemma Exi_upward':
  assumes "f = failing_path (calculation s)"
  and "infinite (calculation s)"
  and "init s"
  shows "\<forall>n. contains f n (0,Exi g) \<longrightarrow> (\<exists>n'. contains f n' (m,Exi g))"
using assms contains_propagates_Exi
by (induct m) (simp,blast)

lemma Exi_upward:
  assumes "f = failing_path (calculation s)"
  and "infinite (calculation s)"
  and "init s"
  and "contains f n (m,Exi g)"
  shows "(\<forall>m'. \<exists>n'. contains f n' (0,sv (bind m') g))"
proof -
  fix m'
  have "\<exists>n'. contains f n' (m',Exi g)" using assms Exi0 Exi_upward' by metis
  then show ?thesis using assms contains_propagates_Exi Exi0 Exi_upward' by metis
qed

definition ntou :: "nat \<Rightarrow> proxy" where
  "ntou n \<equiv> replicate n ()"

definition uton :: "proxy \<Rightarrow> nat" where
  "uton u \<equiv> length u"

lemma aaa: "ntou (uton u) = u"
using ntou_def uton_def
by (induct u) auto

lemma bbb: "uton (ntou n) = n"
using ntou_def uton_def
by (induct n) auto

lemma ccc: "uton \<circ> ntou = id"
using bbb by auto

section "Falsifying Model From Failing Path"

definition model :: "sequent \<Rightarrow> model" where
  "model s \<equiv> (range ntou,\<lambda> p ms. (let f = failing_path (calculation s) in
    (\<forall>n m. \<not> contains f n (m,Pre True p (map uton ms)))))"

lemma is_env_model_ntou: "is_model_environment (model s) ntou"
using is_model_environment_def model_def
by simp

lemma not_is_Exi:
  assumes "f = failing_path (calculation s)"
  and "infinite (calculation s)"
  and "init s"
  and "(contains f n (m,p))"
  shows "\<not> is_Exi p \<Longrightarrow> m = 0"
using assms contains_def index0 is_path_f' prod.collapse
by metis

lemma size_subst: "size (sv f p) = size p"
by (induct p arbitrary: f) simp_all

lemma size_bind: "size (sv (bind m) p) = size p"
using bind_def size_subst
by simp

lemma model':
  assumes "f = failing_path (calculation s)"
  and "infinite (calculation s)"
  and "init s"
  shows "\<forall>p. size p = h \<longrightarrow> (\<forall>m n. contains f n (m,p) \<longrightarrow> \<not> (semantics (model s) ntou p))"
proof (rule nat_less_induct,rule allI)
  fix p n
  show "\<forall>m<n. \<forall>p. size p = m \<longrightarrow> (\<forall>m n. contains f n (m,p) \<longrightarrow> \<not> semantics (model s) ntou p) \<Longrightarrow>
    size p = n \<longrightarrow> (\<forall>m n. contains f n (m,p) \<longrightarrow> \<not> semantics (model s) ntou p)"
  proof -
    assume *: "\<forall>m<n. \<forall>p. size p = m \<longrightarrow> (\<forall>m n. contains f n (m,p) \<longrightarrow>
      \<not> semantics (model s) ntou p)"
    show ?thesis
    proof (cases p)
      case (Pre b i v) then show ?thesis
      proof (cases b)
        case True then show ?thesis using Pre assms model_def ccc by auto
      next
        case False then show ?thesis using Pre
        proof (clarsimp simp: model_def ccc)
          fix na m nb ma
          show "n = 0 \<Longrightarrow> contains f na (m,Pre False i v) \<Longrightarrow>
            contains (failing_path (calculation s)) nb (ma,Pre True i v) \<Longrightarrow> False"
          proof -
            assume 1: "contains f na (m,Pre False i v)" and
                   2: "contains (failing_path (calculation s)) nb (ma,Pre True i v)"
            then have 3: "m = 0 \<and> ma = 0" using assms is_Exi not_is_Exi by simp
            then have "\<exists>y. considers (failing_path (calculation s)) (nb+na+y) (0,Pre True i v)"
            using assms 2 contains_considers contains_propagates_Pre by simp
            then obtain y
            where 4: "considers (failing_path (calculation s)) (nb+na+y) (0,Pre True i v)"
            by blast
            then have 5: "contains (failing_path (calculation s)) (na+nb+y) (0,Pre False i v)"
            using assms 1 3 contains_propagates_Pre by simp
            then have 6: "nb+na=na+nb"
            by simp
            then have "is_axiom (list_sequent (snd ((failing_path (calculation s)) (na+nb+y))))"
            proof (cases "snd ((failing_path (calculation s)) (na + nb + y))")
              case Nil then show ?thesis using 5 contains_def by simp
            next
              case Cons then show ?thesis
                using 4 5 6 by (force simp: contains_def list_sequent_def considers_def)
            qed
            then show ?thesis using assms is_path_f' by blast
          qed
        qed
      qed
    next
      case Con then show ?thesis using assms * is_Exi not_is_Exi contains_propagates_Con
        by (metis Nat.add_0_right add_Suc_right nnf.size(7)
          less_add_Suc1 less_add_Suc2 semantics.simps(2))
      next
        case Dis then show ?thesis using assms * contains_propagates_Dis is_Exi not_is_Exi
          by (metis Nat.add_0_right add_Suc_right nnf.size(8)
                less_add_Suc1 less_add_Suc2 semantics.simps(3))
      next
        case (Uni q) then show ?thesis
        proof (intro impI allI)
          fix na m
          show "size p = n \<Longrightarrow> contains f na (m,p) \<Longrightarrow> \<not> semantics (model s) ntou p"
          proof -
            assume 1: "size p = n" and 2: "contains f na (m,p)"
            then have "m = 0" using assms Uni is_Exi not_is_Exi by simp
            then have "\<exists>y. contains f (Suc (na + y)) (0,(sv (bind (fresh (fv_list
              (map snd (snd (f (na + y))))))) q))"
              using assms Uni 2 contains_propagates_Uni by simp
            then obtain y where 3: "contains f (Suc (na + y)) (0,sv (bind (fresh (fv_list
              (map snd (snd (f (na + y))))))) q)"
              by blast
            have 4: "Suc (size q) = n" using Uni 1 by simp
            then show ?thesis using Uni
            proof (simp)
              show "\<exists>z\<in>fst (model s). \<not> semantics (model s) (case_nat z ntou) q"
              proof (rule_tac x="ntou (fresh (fv_list (map snd (snd (f (na + y))))))" in bexI)
                show "\<not> semantics (model s) (case_nat (ntou (fresh (fv_list
                  (map snd (snd (f (na + y))))))) ntou) q"
                using * 3 4 eval_bind size_bind lessI by metis
              next
                show "ntou (fresh (fv_list (map snd (snd (f (na + y)))))) \<in> fst (model s)"
                  using is_env_model_ntou is_model_environment_def by blast
              qed
            qed
          qed
        qed
      next
        case (Exi q) then show ?thesis
        proof (clarsimp)
          fix m na ma z
          show "p = Exi q \<Longrightarrow> n = Suc (size q) \<Longrightarrow> z \<in> fst (model s) \<Longrightarrow> contains f na (m,Exi q)
            \<Longrightarrow> semantics (model s) (case_nat z ntou) q \<Longrightarrow> False"
          proof -
            assume "n = Suc (size q)" and "contains f na (m,Exi q)"
            and 1: "semantics (model s) (case_nat z ntou) q"
            then have "\<forall>m'. \<not> semantics (model s) ntou (sv (bind m') q)"
              using assms * by (meson Exi_upward eval_cong id_apply lessI size_bind)
            also have "\<forall>u. ntou (uton u) = u" using aaa by simp
            ultimately show ?thesis using 1 eval_bind by metis
          qed
      qed
    qed
  qed
qed
   
lemma model:
  assumes "f = failing_path (calculation s)"
  and "infinite (calculation s)"
  and "init s"
  shows "(\<forall>p m n. contains f n (m,p) \<longrightarrow> \<not> (semantics (model s) ntou p))"
using assms model'
by simp

section "Completeness"

lemma completeness': "infinite (calculation s) \<Longrightarrow> init s \<Longrightarrow>
    \<forall>mA \<in> set s. \<not> semantics (model s) ntou (snd mA)"
by (metis contains_def eq_snd_iff is_path_f_0 model)

lemma completeness'': "infinite (calculation (make_sequent s)) \<Longrightarrow>
    init (make_sequent s) \<Longrightarrow> \<forall>p. p \<in> set s \<longrightarrow> \<not> semantics (model (make_sequent s)) ntou p"
using completeness' make_sequent_def
by fastforce

lemma completeness: "infinite (calculation (make_sequent s)) \<Longrightarrow> \<not> valid s"
using valid_def init_def make_sequent_def is_env_model_ntou semantics_alternative_def2
  completeness''
by (subgoal_tac "init (make_sequent s)") (metis,simp)

section "Algorithm"

definition loop :: "sequent list \<Rightarrow> nat \<Rightarrow> sequent list" where
  "loop s n \<equiv> repeat' (concat \<circ> map solve) s n"

lemma loop_upwards: "loop s n = [] \<Longrightarrow> loop s (n+m) = []"
using loop_def
by (induct m) auto

lemma concat_append: "concat (xs@ys) = ((concat xs) @ (concat ys))"
by (induct xs) auto

lemma set_concat: "set (concat xs) = \<Union> (set ` set xs)"
by (induct xs) auto

lemma loop: "\<forall>x. ((n,x) \<in> calculation s) = (x \<in> set (loop [s] n))"
proof (induct n)
  case 0 then show ?case using loop_def calculation_init by simp
next
  case (Suc m) then show ?case
  proof (intro allI iffI)
    fix x ys z
    assume "(Suc m,x) \<in> calculation s"
    then have "\<exists>t. (m,t) \<in> calculation s \<and> x \<in> set (solve t) \<and> \<not> is_axiom (list_sequent t)"
      using calculation_downwards by blast
    then obtain t
      where 1: "(m,t) \<in> calculation s \<and> x \<in> set (solve t) \<and> \<not> is_axiom (list_sequent t)"
      by blast
      then show "(x \<in> set (loop [s] (Suc m)))"
        using Suc loop_def by (clarsimp dest!: split_list_first)
  next
    fix x
    assume "(x \<in> set (loop [s] (Suc m)))"
    then show "(Suc m,x) \<in> calculation s"
      using Suc by (fastforce simp: set_concat loop_def calculation.intros(2))
  qed
qed

lemma calculation_f: "calculation s = UNION UNIV (\<lambda>x. set (map (\<lambda>y. (x,y)) (loop [s] x)))"
using loop
by fastforce

lemma finite_calculation':
  assumes "finite (calculation s)"
  shows "(\<exists>m. loop [s] m = [])"
proof -
  have "finite (fst ` (calculation s))" using assms by simp
  then obtain x where xMax: "x \<in> fst ` calculation s \<and> (\<forall>y. y \<in> fst ` calculation s \<longrightarrow> y \<le> x)"
    using max_exists calculation.simps by (metis empty_iff image_is_empty) 
  then show ?thesis
  proof (cases "loop [s] (Suc x)")
    assume "loop [s] (Suc x) = []" then show ?thesis by blast
  next
    fix a l
    assume "loop [s] (Suc x) = a # l"
    then have "(Suc x,a) \<in> calculation s" using loop by simp
    then show ?thesis using xMax by fastforce
  qed
qed

lemma finite_calculation'':
  assumes "(\<exists>m. loop [s] m = [])"
  shows "finite (calculation s)"
proof -
  obtain m where "loop [s] m = []" using assms by blast
  then have "\<forall>y. loop [s] (m+y) = []" using loop_upwards by simp
  then have 1: "(UN x:Collect (op \<le> m). Pair x ` set (loop [s] x)) = (UN x:Collect (op \<le> m). {})"
    using SUP_cong image_is_empty le_Suc_ex mem_Collect_eq set_empty
      by (metis (no_types,lifting))
    then have "(UNIV::nat set) = {y. y < m} Un {y. m \<le> y}" by fastforce
    then show ?thesis using 1 calculation_f by (clarsimp elim!: ssubst)
 qed

lemma finite_calculation: "finite (calculation s) = (\<exists>m. loop [s] m = [])"
using finite_calculation' finite_calculation''
by blast

corollary finite_calculation_prover: "finite (calculation s) = iterator null (maps solve) [s]"
using finite_calculation loop_def iterator_def maps null.simps list.exhaust rr
by metis

section \<open>Correctness\<close>

lemmas magic = soundness completeness finite_calculation_prover

theorem correctness: CHECK VALID
proof -
  have "\<forall>p. [[(0,p)]] = [map (Pair 0) [p]]" by simp
  then have CHECK
    unfolding check_def
    using magic valid_def make_sequent_def semantics_alternative.simps main_def
    by (metis (no_types,hide_lams))
  moreover have VALID
    using magic make_sequent_def by fastforce
  ultimately show CHECK VALID by -
qed

corollary "\<exists>p. check p" "\<exists>p. \<not> check p"
proof -
  have "\<not> valid [Pre True 0 []]" "valid [Dis (Pre True 0 []) (Pre False 0 [])]"
    using valid_def is_model_environment_def by auto
  then show "\<exists>p. check p" "\<exists>p. \<not> check p"
    using magic correctness semantics_alternative.simps valid_def by (metis,metis)
qed

section \<open>Appendix\<close>

text \<open>Code by hand\<close>

ML

{*

datatype nnf = Pre of bool * string * int list | Con of nnf * nnf | Uni of nnf
                                               | Dis of nnf * nnf | Exi of nnf

fun extend l 0 = l | extend l n = n-1 :: l

fun adjust [] = [] | adjust (h :: t) = extend (adjust t) h

fun fv (Pre (_,_,v)) = v
  | fv (Con (p,q)) = fv p @ fv q
  | fv (Dis (p,q)) = fv p @ fv q
  | fv (Uni p) = adjust (fv p)
  | fv (Exi p) = adjust (fv p)

fun increase _ 0 = 0 | increase f n = (f n-1)+1

fun sv f (Pre (b,i,v)) = Pre (b,i,map f v)
  | sv f (Con (p,q)) = Con (sv f p,sv f q)
  | sv f (Dis (p,q)) = Dis (sv f p,sv f q)
  | sv f (Uni p) = Uni (sv (increase f) p)
  | sv f (Exi p) = Exi (sv (increase f) p)

fun bind x 0 = x | bind _ n = n-1

fun inst p x = sv (bind x) p

fun helper x [] = x | helper x (h :: t) = helper (if x > h then x else h) t

fun fresh [] = 0 | fresh (h :: t) = (helper h t)+1

fun stop c _ [] = c | stop c p (h :: t) = if p = h then [] else stop c p t

fun track s _ (Pre (b,i,v)) = stop [s @ [(0,Pre (b,i,v))]] (Pre (not b,i,v)) (map snd s)
  | track s _ (Con (p,q)) = [s @ [(0,p)],s @ [(0,q)]]
  | track s _ (Dis (p,q)) = [s @ [(0,p),(0,q)]]
  | track s _ (Uni p) = [s @ [(0,inst p (fresh (maps fv (Uni p :: map snd s))))]]
  | track s n (Exi p) = [s @ [(0,inst p n),(n+1,Exi p)]]

fun solve [] = [[]] | solve (h :: t) = track t (fst h) (snd h)

fun prover c = if null c then () else prover (maps solve c)

fun check p = prover [[(0,p)]]

val () = check (Dis (Uni (Con (Pre (false,"P",[0]),Pre (false,"Q",[0]))),
                     Dis (Exi (Pre (true,"Q",[0])),Exi (Pre (true,"P",[0])))))

*}

text \<open>Code generation\<close>

value "check test"

value "check (Dis (Pre True 0 []) (Pre False 0 []))"

(* value "check (Pre True 0 [])" *)

proposition "check test"
by eval

proposition "check (Dis (Pre True 0 []) (Pre False 0 []))"
by eval

proposition "check test"
by normalization

proposition "check (Dis (Pre b i v) (Pre (\<not> b) i v))"
by normalization

(*

code_reflect SimPro functions check test

ML {* val true = SimPro.check SimPro.test *}

*)

code_reflect X datatypes nnf = Pre | Con | Dis | Uni | Exi and nat = "0::nat" | Suc functions check

ML

{*

val true = X.check (X.Dis (X.Uni (X.Con (X.Pre (false,X.Zero_nat,[X.Zero_nat]),
                                         X.Pre (false,X.Suc X.Zero_nat,[X.Zero_nat]))),
                           X.Dis (X.Exi (X.Pre (true,X.Suc X.Zero_nat,[X.Zero_nat])),
                                  X.Exi (X.Pre (true,X.Zero_nat,[X.Zero_nat])))))

*}

(* export_code check test in SML module_name SimPro file "SimPro.sml" *)

(*

SML_file "SimPro.sml"

SML_export "val SimPro_check = SimPro.check val SimPro_test = SimPro.test"

ML {* val true = SimPro_check SimPro_test *}

*)

end
