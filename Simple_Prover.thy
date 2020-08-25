(* Authors: Jørgen Villadsen, Anders Schlichtkrull, Asta Halkjær From *)

(* Latest version here: https://github.com/logic-tools/simpro/blob/master/Simple_Prover.thy *)

(* Thanks to Jens Carl Moesgård Eschen for updates to the soundness and completeness proofs *)

section \<open>Simple Prover for First-Order Logic\<close>

theory Simple_Prover imports Main begin

section \<open>Preliminaries\<close>

primrec dec :: \<open>nat \<Rightarrow> nat\<close> where
  \<open>dec 0 = 0\<close> |
  \<open>dec (Suc n) = n\<close>

primrec sub :: \<open>nat \<Rightarrow> nat \<Rightarrow> nat\<close> where
  \<open>sub x 0 = x\<close> |
  \<open>sub x (Suc n) = dec (sub x n)\<close>

primrec add :: \<open>nat \<Rightarrow> nat \<Rightarrow> nat\<close> where
  \<open>add x 0 = x\<close> |
  \<open>add x (Suc n) = Suc (add x n)\<close>

lemma append_simps: \<open>[] @ l = l\<close> \<open>(h # t) @ l = h # t @ l\<close>
  by (rule append.simps(1),rule append.simps(2))

lemma if_simps: \<open>(if True then x else y) = x\<close> \<open>(if False then x else y) = y\<close>
  by (rule if_True,rule if_False)

lemma not_simps: \<open>(\<not> True) = False\<close> \<open>(\<not> False) = True\<close>
  by (rule not_True_eq_False,rule not_False_eq_True)

lemma prod_simps: \<open>fst (x,y) = x\<close> \<open>snd (x,y) = y\<close>
  unfolding fst_def snd_def
  by (rule prod.case,rule prod.case)

lemma nat_simps: \<open>(0 = 0) = True\<close>
  by (rule simp_thms)

lemma list_simps: \<open>([] = []) = True\<close>
  by (rule simp_thms)

lemma bool_simps: \<open>(True = True) = True\<close> \<open>(False = False) = True\<close>
  by (rule simp_thms,rule simp_thms)

lemma inject_simps: \<open>(True \<and> b) = b\<close> \<open>(False \<and> b) = False\<close>
  by (rule simp_thms,rule simp_thms)

section \<open>Syntax and Semantics\<close>

type_synonym id = \<open>nat\<close>

datatype nnf = Pre \<open>bool\<close> \<open>id\<close> \<open>nat list\<close> | Con \<open>nnf\<close> \<open>nnf\<close> | Dis \<open>nnf\<close> \<open>nnf\<close> | Uni \<open>nnf\<close> | Exi \<open>nnf\<close>

abbreviation (input) \<open>TEST P Q \<equiv> (\<exists>x. P x \<or> Q x) \<longrightarrow> (\<exists>x. Q x) \<or> (\<exists>x. P x)\<close>

proposition \<open>TEST P Q\<close>
  by iprover

proposition \<open>TEST P Q = ((\<forall>x. \<not> P x \<and> \<not> Q x) \<or> (\<exists>x. Q x) \<or> (\<exists>x. P x))\<close>
  by fast

abbreviation (input) \<open>P_id \<equiv> 0\<close>

abbreviation (input) \<open>Q_id \<equiv> Suc 0\<close>

definition \<comment> \<open>TEST P Q\<close>
  \<open>test \<equiv> Dis
    (Uni (Con (Pre False P_id [0]) (Pre False Q_id [0])))
    (Dis (Exi (Pre True Q_id [0])) (Exi (Pre True P_id [0])))\<close>

type_synonym proxy = \<open>unit list\<close>

type_synonym model = \<open>proxy set \<times> (id \<Rightarrow> proxy list \<Rightarrow> bool)\<close>

type_synonym environment = \<open>nat \<Rightarrow> proxy\<close>

definition is_model_environment :: \<open>model \<Rightarrow> environment \<Rightarrow> bool\<close> where
  \<open>is_model_environment m e \<equiv> \<forall>n. e n \<in> fst m\<close>

primrec semantics :: \<open>model \<Rightarrow> environment \<Rightarrow> nnf \<Rightarrow> bool\<close> where
  \<open>semantics m e (Pre b i v) = (b = snd m i (map e v))\<close> |
  \<open>semantics m e (Con p q) = (semantics m e p \<and> semantics m e q)\<close> |
  \<open>semantics m e (Dis p q) = (semantics m e p \<or> semantics m e q)\<close> |
  \<open>semantics m e (Uni p) = (\<forall>z \<in> fst m. semantics m (\<lambda>x. case x of 0 \<Rightarrow> z | Suc n \<Rightarrow> e n) p)\<close> |
  \<open>semantics m e (Exi p) = (\<exists>z \<in> fst m. semantics m (\<lambda>x. case x of 0 \<Rightarrow> z | Suc n \<Rightarrow> e n) p)\<close>

section \<open>Sequent Calculus\<close>

primrec dash :: \<open>nat list \<Rightarrow> nat \<Rightarrow> nat list\<close> where
  \<open>dash l 0 = l\<close> |
  \<open>dash l (Suc n) = n # l\<close>

primrec dump :: \<open>nat list \<Rightarrow> nat list\<close> where
  \<open>dump [] = []\<close> |
  \<open>dump (h # t) = dash (dump t) h\<close>

primrec free :: \<open>nnf \<Rightarrow> nat list\<close> where
  \<open>free (Pre _ _ v) = v\<close> |
  \<open>free (Con p q) = free p @ free q\<close> |
  \<open>free (Dis p q) = free p @ free q\<close> |
  \<open>free (Uni p) = dump (free p)\<close> |
  \<open>free (Exi p) = dump (free p)\<close>

primrec frees :: \<open>nnf list \<Rightarrow> nat list\<close> where
  \<open>frees [] = []\<close> |
  \<open>frees (h # t) = free h @ frees t\<close>

primrec fresh :: \<open>nat list \<Rightarrow> nat\<close> where
  \<open>fresh [] = 0\<close> |
  \<open>fresh (h # t) = Suc (add (sub (dec (fresh t)) h) h)\<close>

primrec over :: \<open>nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat\<close> where
  \<open>over s _ 0 = s\<close> |
  \<open>over _ h (Suc _) = h\<close>

primrec more :: \<open>nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat\<close> where
  \<open>more x s h 0 = over s h (sub x h)\<close> |
  \<open>more _ _ h (Suc _) = dec h\<close>

primrec mend :: \<open>nat \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> nat list\<close> where
  \<open>mend _ _ [] = []\<close> |
  \<open>mend x s (h # t) = more x s h (sub h x) # mend x s t\<close>

primrec subst :: \<open>nat \<Rightarrow> nat \<Rightarrow> nnf \<Rightarrow> nnf\<close> where
  \<open>subst x s (Pre b i v) = Pre b i (mend x s v)\<close> |
  \<open>subst x s (Con p q) = Con (subst x s p) (subst x s q)\<close> |
  \<open>subst x s (Dis p q) = Dis (subst x s p) (subst x s q)\<close> |
  \<open>subst x s (Uni p) = Uni (subst (Suc x) (Suc s) p)\<close> |
  \<open>subst x s (Exi p) = Exi (subst (Suc x) (Suc s) p)\<close>

type_synonym sequent = \<open>(nat \<times> nnf) list\<close>

primrec base :: \<open>sequent \<Rightarrow> nnf list\<close> where
  \<open>base [] = []\<close> |
  \<open>base (h # t) = snd h # base t\<close>

primrec stop :: \<open>sequent list \<Rightarrow> nnf \<Rightarrow> nnf list \<Rightarrow> sequent list\<close> where
  \<open>stop c _ [] = c\<close> |
  \<open>stop c p (h # t) = (if p = h then [] else stop c p t)\<close>

primrec track :: \<open>sequent \<Rightarrow> nat \<Rightarrow> nnf \<Rightarrow> sequent list\<close> where
  \<open>track s _ (Pre b i v) = stop [s @ [(0,Pre b i v)]] (Pre (\<not> b) i v) (base s)\<close> |
  \<open>track s _ (Con p q) = [s @ [(0,p)],s @ [(0,q)]]\<close> |
  \<open>track s _ (Dis p q) = [s @ [(0,p),(0,q)]]\<close> |
  \<open>track s _ (Uni p) = [s @ [(0,subst 0 (fresh (frees (Uni p # base s))) p)]]\<close> |
  \<open>track s n (Exi p) = [s @ [(0,subst 0 n p),(Suc n,Exi p)]]\<close>

primrec solve :: \<open>sequent \<Rightarrow> sequent list\<close> where
  \<open>solve [] = [[]]\<close> |
  \<open>solve (h # t) = track t (fst h) (snd h)\<close>

primrec solves :: \<open>sequent list \<Rightarrow> sequent list\<close> where
  \<open>solves [] = []\<close> |
  \<open>solves (h # t) = solve h @ solves t\<close>

type_synonym 'a algorithm = \<open>('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> bool\<close>

primrec null :: \<open>'a list \<Rightarrow> bool\<close> where
  \<open>null [] = True\<close> |
  \<open>null (_ # _) = False\<close>

definition main :: \<open>sequent list algorithm \<Rightarrow> nnf \<Rightarrow> bool\<close> where
  \<open>main a p \<equiv> a null solves [[(0,p)]]\<close>

primrec repeat :: \<open>('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> 'a\<close> where
  \<open>repeat _ c 0 = c\<close> |
  \<open>repeat f c (Suc n) = repeat f (f c) n\<close>

definition iterator :: \<open>'a algorithm\<close> where
  \<open>iterator g f c \<equiv> \<exists>n. g (repeat f c n)\<close>

definition check :: \<open>nnf \<Rightarrow> bool\<close> where
  \<open>check \<equiv> main iterator\<close>

section \<open>Prover\<close>

abbreviation (input) \<open>CHECK \<equiv> check = (\<lambda>p. \<forall>m e. is_model_environment m e \<longrightarrow> semantics m e p)\<close>

abbreviation \<open>prover \<equiv> iterator null solves\<close>

lemma check_prover: \<open>check p \<equiv> prover [[(0,p)]]\<close>
  unfolding check_def main_def .

lemma iterator[code]: \<open>iterator g f c = (if g c then True else iterator g f (f c))\<close>
  unfolding iterator_def
  using repeat.simps not0_implies_Suc
  by metis

lemma prover: \<open>prover c = (if null c then True else prover (solves c))\<close>
  using iterator .

lemma prover_next: \<open>prover (h # t) = prover (solves (h # t))\<close>
  using prover
  by simp

lemma prover_done: \<open>prover [] = True\<close>
  using prover
  by simp

lemmas simps = check_prover prover_next prover_done solves.simps solve.simps track.simps stop.simps
  base.simps subst.simps mend.simps more.simps over.simps fresh.simps frees.simps free.simps
  dump.simps dash.simps nnf.distinct nnf.inject add.simps sub.simps dec.simps append_simps if_simps
  not_simps prod_simps nat_simps list_simps bool_simps inject_simps nat.distinct list.distinct
  bool.distinct prod.inject nat.inject list.inject

theorem program:
  \<open>\<And>p. check p \<equiv> prover [[(0,p)]]\<close>
  \<open>\<And>h t. prover (h # t) \<equiv> prover (solves (h # t))\<close>
  \<open>prover [] \<equiv> True\<close>
  \<open>solves [] \<equiv> []\<close>
  \<open>\<And>h t. solves (h # t) \<equiv> solve h @ solves t\<close>
  \<open>solve [] \<equiv> [[]]\<close>
  \<open>\<And>h t. solve (h # t) \<equiv> track t (fst h) (snd h)\<close>
  \<open>\<And>s n b i v. track s n (Pre b i v) \<equiv> stop [s @ [(0,Pre b i v)]] (Pre (\<not> b) i v) (base s)\<close>
  \<open>\<And>s n p q. track s n (Con p q) \<equiv> [s @ [(0,p)],s @ [(0,q)]]\<close>
  \<open>\<And>s n p q. track s n (Dis p q) \<equiv> [s @ [(0,p),(0,q)]]\<close>
  \<open>\<And>s n p. track s n (Uni p) \<equiv> [s @ [(0,subst 0 (fresh (frees (Uni p # base s))) p)]]\<close>
  \<open>\<And>s n p. track s n (Exi p) \<equiv> [s @ [(0,subst 0 n p),(Suc n,Exi p)]]\<close>
  \<open>\<And>c p. stop c p [] \<equiv> c\<close>
  \<open>\<And>c p h t. stop c p (h # t) \<equiv> (if p = h then [] else stop c p t)\<close>
  \<open>base [] \<equiv> []\<close>
  \<open>\<And>h t. base (h # t) \<equiv> snd h # base t\<close>
  \<open>\<And>x s b i v. subst x s (Pre b i v) \<equiv> Pre b i (mend x s v)\<close>
  \<open>\<And>x s p q. subst x s (Con p q) \<equiv> Con (subst x s p) (subst x s q)\<close>
  \<open>\<And>x s p q. subst x s (Dis p q) \<equiv> Dis (subst x s p) (subst x s q)\<close>
  \<open>\<And>x s p. subst x s (Uni p) \<equiv> Uni (subst (Suc x) (Suc s) p)\<close>
  \<open>\<And>x s p. subst x s (Exi p) \<equiv> Exi (subst (Suc x) (Suc s) p)\<close>
  \<open>\<And>x s. mend x s [] \<equiv> []\<close>
  \<open>\<And>x s h t. mend x s (h # t) \<equiv> more x s h (sub h x) # mend x s t\<close>
  \<open>\<And>x s h. more x s h 0 \<equiv> over s h (sub x h)\<close>
  \<open>\<And>x s h n. more x s h (Suc n) \<equiv> dec h\<close>
  \<open>\<And>s h. over s h 0 \<equiv> s\<close>
  \<open>\<And>s h n. over s h (Suc n) \<equiv> h\<close>
  \<open>fresh [] \<equiv> 0\<close>
  \<open>\<And>h t. fresh (h # t) \<equiv> Suc (add (sub (dec (fresh t)) h) h)\<close>
  \<open>frees [] \<equiv> []\<close>
  \<open>\<And>h t. frees (h # t) \<equiv> free h @ frees t\<close>
  \<open>\<And>b i v. free (Pre b i v) \<equiv> v\<close>
  \<open>\<And>p q. free (Con p q) \<equiv> free p @ free q\<close>
  \<open>\<And>p q. free (Dis p q) \<equiv> free p @ free q\<close>
  \<open>\<And>p. free (Uni p) \<equiv> dump (free p)\<close>
  \<open>\<And>p. free (Exi p) \<equiv> dump (free p)\<close>
  \<open>dump [] \<equiv> []\<close>
  \<open>\<And>h t. dump (h # t) \<equiv> dash (dump t) h\<close>
  \<open>\<And>l. dash l 0 \<equiv> l\<close>
  \<open>\<And>l n. dash l (Suc n) \<equiv> n # l\<close>
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
  \<open>\<And>b i v p q. Pre b i v = Con p q \<equiv> False\<close>
  \<open>\<And>b i v p q. Con p q = Pre b i v \<equiv> False\<close>
  \<open>\<And>b i v p q. Pre b i v = Dis p q \<equiv> False\<close>
  \<open>\<And>b i v p q. Dis p q = Pre b i v \<equiv> False\<close>
  \<open>\<And>b i v p. Pre b i v = Uni p \<equiv> False\<close>
  \<open>\<And>b i v p. Uni p = Pre b i v \<equiv> False\<close>
  \<open>\<And>b i v p. Pre b i v = Exi p \<equiv> False\<close>
  \<open>\<And>b i v p. Exi p = Pre b i v \<equiv> False\<close>
  \<open>\<And>p q p' q'. Con p q = Dis p' q' \<equiv> False\<close>
  \<open>\<And>p q p' q'. Dis p' q' = Con p q \<equiv> False\<close>
  \<open>\<And>p q p'. Con p q = Uni p' \<equiv> False\<close>
  \<open>\<And>p q p'. Uni p' = Con p q \<equiv> False\<close>
  \<open>\<And>p q p'. Con p q = Exi p' \<equiv> False\<close>
  \<open>\<And>p q p'. Exi p' = Con p q \<equiv> False\<close>
  \<open>\<And>p q p'. Dis p q = Uni p' \<equiv> False\<close>
  \<open>\<And>p q p'. Uni p' = Dis p q \<equiv> False\<close>
  \<open>\<And>p q p'. Dis p q = Exi p' \<equiv> False\<close>
  \<open>\<And>p q p'. Exi p' = Dis p q \<equiv> False\<close>
  \<open>\<And>p p'. Uni p = Exi p' \<equiv> False\<close>
  \<open>\<And>p p'. Exi p' = Uni p \<equiv> False\<close>
  \<open>\<And>b i v b' i' v'. Pre b i v = Pre b' i' v' \<equiv> b = b' \<and> i = i' \<and> v = v'\<close>
  \<open>\<And>p q p' q'. Con p q = Con p' q' \<equiv> p = p' \<and> q = q'\<close>
  \<open>\<And>p q p' q'. Dis p q = Dis p' q' \<equiv> p = p' \<and> q = q'\<close>
  \<open>\<And>p p'. Uni p = Uni p' \<equiv> p = p'\<close>
  \<open>\<And>p p'. Exi p = Exi p' \<equiv> p = p'\<close>
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
  \<open>\<And>x. add x 0 \<equiv> x\<close>
  \<open>\<And>x n. add x (Suc n) \<equiv> Suc (add x n)\<close>
  \<open>\<And>x. sub x 0 \<equiv> x\<close>
  \<open>\<And>x n. sub x (Suc n) \<equiv> dec (sub x n)\<close>
  \<open>dec 0 \<equiv> 0\<close>
  \<open>\<And>n. dec (Suc n) \<equiv> n\<close>
  \<open>\<And>l. [] @ l \<equiv> l\<close>
  \<open>\<And>h t l. (h # t) @ l \<equiv> h # t @ l\<close>
  \<open>\<And>x y. if True then x else y \<equiv> x\<close>
  \<open>\<And>x y. if False then x else y \<equiv> y\<close>
  \<open>\<not> True \<equiv> False\<close>
  \<open>\<not> False \<equiv> True\<close>
  \<open>\<And>x y. fst (x,y) \<equiv> x\<close>
  \<open>\<And>x y. snd (x,y) \<equiv> y\<close>
  \<open>0 = 0 \<equiv> True\<close>
  \<open>[] = [] \<equiv> True\<close>
  \<open>True = True \<equiv> True\<close>
  \<open>False = False \<equiv> True\<close>
  \<open>\<And>b. True \<and> b \<equiv> b\<close>
  \<open>\<And>b. False \<and> b \<equiv> False\<close>
  \<open>\<And>n. 0 = Suc n \<equiv> False\<close>
  \<open>\<And>n. Suc n = 0 \<equiv> False\<close>
  \<open>\<And>h t. [] = h # t \<equiv> False\<close>
  \<open>\<And>h t. h # t = [] \<equiv> False\<close>
  \<open>True = False \<equiv> False\<close>
  \<open>False = True \<equiv> False\<close>
  \<open>\<And>x y x' y'. (x,y) = (x',y') \<equiv> x = x' \<and> y = y'\<close>
  \<open>\<And>n n'. Suc n = Suc n' \<equiv> n = n'\<close>
  \<open>\<And>h t h' t'. h # t = h' # t' \<equiv> h = h' \<and> t = t'\<close>
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
      (simp only: simps(93)),
      (simp only: simps(94)))

proposition \<open>check test\<close>
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

proposition \<open>check test\<close>
  unfolding check_def
  unfolding main_def
  unfolding test_def
  by (simp add: iterator)

proposition \<open>check test\<close>
  by code_simp

proposition \<open>map length (map (repeat (solves) [[(0,test)]]) [1,2,3,4,5,6,7]) = [1,1,1,2,2,2,0]\<close>
  by code_simp

proposition \<open>repeat (solves) [[(0,test)]] (Suc (Suc (Suc (Suc (Suc (Suc (Suc 0))))))) = []\<close>
  unfolding repeat.simps
  unfolding test_def
  unfolding program data library
  by (rule TrueI)

proposition \<open>\<forall>m e. is_model_environment m e \<longrightarrow> fst m \<noteq> {}\<close>
  unfolding is_model_environment_def
  by fast

inductive_set calculation :: \<open>sequent \<Rightarrow> (nat \<times> sequent) set\<close> for s where
  \<open>(0,s) \<in> calculation s\<close> |
  \<open>(n,k) \<in> calculation s \<Longrightarrow> l \<in> set (solve k) \<Longrightarrow> (Suc n,l) \<in> calculation s\<close>

primrec semantics_alternative :: \<open>model \<Rightarrow> environment \<Rightarrow> nnf list \<Rightarrow> bool\<close> where
  \<open>semantics_alternative _ _ [] = False\<close> |
  \<open>semantics_alternative m e (h # t) = (semantics m e h \<or> semantics_alternative m e t)\<close>

definition valid :: \<open>nnf list \<Rightarrow> bool\<close> where
  \<open>valid l \<equiv> \<forall>m e. is_model_environment m e \<longrightarrow> semantics_alternative m e l\<close>

abbreviation (input) \<open>VALID \<equiv> valid = finite \<circ> calculation \<circ> map (Pair 0)\<close>

section \<open>Soundness and Completeness\<close>

subsection \<open>Basics\<close>

lemma sub_alt: \<open>sub h x = h - x\<close>
  by (induct \<open>x\<close>) (simp_all split: nat_diff_split)

lemma base_alt: \<open>base s = map snd s\<close>
  by (induct \<open>s\<close>) simp_all

lemma frees_alt: \<open>frees l = (concat \<circ> map free) l\<close>
  by (induct \<open>l\<close>) simp_all

lemma solves_alt: \<open>solves l = (concat \<circ> map solve) l\<close>
  by (induct \<open>l\<close>) simp_all

lemma stop_alt: \<open>stop s (Pre (\<not> b) i v) l = (if (Pre (\<not> b) i v) \<in> (set l) then [] else s)\<close>
  by (induct \<open>l\<close>) simp_all

lemma dump_suc: \<open>Suc n \<in> set l = (n \<in> set (dump l))\<close>
proof (induct \<open>l\<close>)
  case (Cons m _)
  then show \<open>?case\<close>
    by (cases \<open>m\<close>) simp_all
qed simp

primrec maxl :: \<open>nat list \<Rightarrow> nat\<close> where
  \<open>maxl [] = 0\<close> |
  \<open>maxl (h # t) = add (sub (maxl t) h) h\<close>

lemma add_sub_eq_max: \<open>(add (sub n n') n') = (max n n')\<close>
proof (induct \<open>n'\<close> arbitrary: \<open>n\<close>)
  case Suc
  then show \<open>?case\<close>
    by (metis add.simps(2) add_Suc add_Suc_shift diff_add_inverse2 sub_alt nat_minus_add_max)
qed simp

lemma maxl_is_max: \<open>\<forall>v \<in> set l. v \<le> maxl l\<close>
  by (induct \<open>l\<close>) (auto simp: max_def add_sub_eq_max)

lemma fresh_alt: \<open>fresh l = (if null l then 0 else Suc (maxl l))\<close>
proof (induct \<open>l\<close>)
  case Cons
  then show \<open>?case\<close>
    using list.exhaust dec.simps fresh.simps(2) maxl.simps null.simps(2) by metis
qed simp

lemma fresh_is_fresh: \<open>fresh l \<notin> (set l)\<close>
  using fresh_alt maxl_is_max by (metis Simple_Prover.null.simps(2) Suc_n_not_le_n list.set_cases)

definition subst_var :: \<open>nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat\<close> where
  \<open>subst_var x s n \<equiv> (if n < x then n else if n = x then s else n - 1)\<close>

lemma subst_var_eq_mend: \<open>map (subst_var x s) v = mend x s v\<close>
proof -
  have \<open>\<forall>h. more x s h (sub h x) = (if sub h x = 0 then (if sub x h = 0 then s else h) else dec h)\<close>
    by (metis more.simps(1) more.simps(2) not0_implies_Suc over.simps(1) over.simps(2))
  then have \<open>mend x s v = map (\<lambda>n. (if n < x then n else if n = x then s else n - 1)) v\<close>
    by (induct \<open>v\<close>) (simp_all add: sub_alt nat_diff_split)
  with subst_var_def show \<open>?thesis\<close>
    by simp
qed

lemma repeat_compower: \<open>repeat f c n = (f ^^ n) c\<close>
  by (induct \<open>n\<close> arbitrary: \<open>c\<close>) (simp_all add: funpow_swap1)

primrec is_axiom :: \<open>nnf list \<Rightarrow> bool\<close> where
  \<open>is_axiom [] = False\<close> |
  \<open>is_axiom (p # t) = (\<exists>b i v. p = Pre b i v \<and> Pre (\<not> b) i v \<in> set t)\<close>

lemma calculation_init: \<open>(0,k) \<in> calculation s = (k = s)\<close>
  using calculation.simps by blast

lemma calculation_upwards:
  assumes \<open>(n,k) \<in> calculation s\<close> and \<open>\<not> is_axiom (base (k))\<close>
  shows \<open>\<exists>l. (Suc n,l) \<in> calculation s \<and> l \<in> set (solve k)\<close>
proof (cases \<open>k\<close>)
  case Nil
  then show \<open>?thesis\<close>
    using assms(1) calculation.intros(2) by simp_all
next
  case (Cons a _)
  then show \<open>?thesis\<close>
  proof (cases \<open>a\<close>)
    case (Pair _ p)
    then show \<open>?thesis\<close>
      using Cons assms calculation.intros(2) by (cases \<open>p\<close>) (fastforce simp: base_alt stop_alt)+
  qed
qed

lemma calculation_downwards:
  assumes \<open>(Suc n,k) \<in> calculation s\<close>
  shows \<open>\<exists>t. (n,t) \<in> calculation s \<and> k \<in> set (solve t) \<and> \<not> is_axiom (base t)\<close>
  using assms
proof (induct \<open>Suc n\<close> \<open>k\<close> arbitrary: \<open>n\<close> rule: calculation.induct)
  case (2 k l)
  then show \<open>?case\<close>
  proof (cases \<open>l\<close>)
    case Nil
    then show \<open>?thesis\<close>
      using 2 by auto
  next
    case (Cons a _)
    then show \<open>?thesis\<close>
    proof (cases \<open>a\<close>)
      case (Pair _ p)
      then show \<open>?thesis\<close>
        using 2 Cons stop_alt by (cases \<open>p\<close>) auto
    qed
  qed
qed

lemma calculation_calculation_child:
  \<open>(Suc n,s) \<in> calculation t =
   (\<exists>k. k \<in> set (solve t) \<and> \<not> is_axiom (base t) \<and> (n,s) \<in> calculation k)\<close>
  by (induct \<open>n\<close> arbitrary: \<open>s\<close> \<open>t\<close>)
    (metis calculation.intros(2) calculation_downwards calculation_init,
      meson calculation.intros(2) calculation_downwards)

definition inc :: \<open>nat \<times> sequent \<Rightarrow> nat \<times> sequent\<close> where \<open>inc \<equiv> \<lambda>(n,fs). (Suc n,fs)\<close>

lemma calculation_alt: \<open>calculation s =
  insert (0,s) (inc ` (\<Union> (calculation ` {k. \<not> is_axiom (base s) \<and> k \<in> set (solve s)})))\<close>
proof -
  have \<open>(n,k) \<in> calculation s =
      (n = 0 \<and> k = s \<or>
      (n,k) \<in> inc ` (\<Union>x\<in>{k. \<not> is_axiom (base s) \<and> k \<in> set (solve s)}. calculation x))\<close> for n k
    unfolding inc_def by (cases \<open>n\<close>) (auto simp: calculation_init calculation_calculation_child)
  then show \<open>?thesis\<close>
    by auto
qed

lemma is_axiom_finite_calculation: assumes \<open>is_axiom (base s)\<close> shows \<open>finite (calculation s)\<close>
proof -
  from calculation_alt assms have \<open>calculation s = {(0,s)}\<close>
    by blast
  then show \<open>?thesis\<close>
    by simp
qed

primrec failing_path :: \<open>(nat \<times> sequent) set \<Rightarrow> nat \<Rightarrow> (nat \<times> sequent)\<close> where
  \<open>failing_path ns 0 = (SOME x. x \<in> ns \<and> fst x = 0 \<and> infinite (calculation (snd x)) \<and>
    \<not> is_axiom (base (snd x)))\<close> |
  \<open>failing_path ns (Suc n) = (let fn = failing_path ns n in
    (SOME fsucn. fsucn \<in> ns \<and> fst fsucn = Suc n \<and> (snd fsucn) \<in> set (solve (snd fn)) \<and>
      infinite (calculation (snd fsucn)) \<and> \<not> is_axiom (base (snd fsucn))))\<close>

abbreviation \<open>fp s \<equiv> failing_path (calculation s)\<close>
abbreviation \<open>ic s \<equiv> infinite (calculation s)\<close>

lemma fSuc:
  assumes \<open>ic (snd (fp s n))\<close> and \<open>fp s n \<in> calculation s\<close>
    and \<open>fst (fp s n) = n\<close> and \<open>\<not> is_axiom (base (snd (fp s n)))\<close>
  shows \<open>fp s (Suc n) \<in> calculation s \<and> fst (fp s (Suc n)) = Suc n \<and>
    (snd (fp s (Suc n))) \<in> set (solve (snd (fp s n))) \<and> ic (snd (fp s (Suc n))) \<and>
    \<not> is_axiom (base (snd (fp s (Suc n))))\<close>
proof -
  have \<open>infinite (\<Union> (calculation ` {w. \<not> is_axiom (base (snd (fp s n))) \<and>
      w \<in> set (solve (snd (fp s n)))}))\<close>
    using assms calculation_alt
    by (metis (mono_tags,lifting) Collect_cong finite.insertI finite_imageI)
  then have \<open>\<not> is_axiom (base (snd (fp s n))) \<and> (\<exists>x. x \<in> set (solve (snd (fp s n))) \<and> ic x)\<close>
    by simp
  then have \<open>\<exists>b. (Suc n, b) \<in> calculation s \<and>
      b \<in> set (solve (snd (fp s n))) \<and> ic b \<and> \<not> is_axiom (base b)\<close>
    using assms(2-3) is_axiom_finite_calculation calculation.intros(2)
    by (metis prod.collapse)
  moreover have \<open>\<exists>b. (Suc n, b) \<in> calculation s \<and>
      b \<in> set (solve (snd (fp s n))) \<and> ic b \<and> \<not> is_axiom (base b) \<Longrightarrow>
        \<exists>x. x \<in> calculation s \<and> fst x = Suc n \<and> snd x \<in> set (solve (snd (fp s n))) \<and>
          ic (snd x) \<and> \<not> is_axiom (base (snd x))\<close>
    by simp
  ultimately show \<open>?thesis\<close>
    by (metis (mono_tags, lifting) failing_path.simps(2) is_axiom_finite_calculation someI)
qed

lemma is_path_f_0: assumes \<open>ic s\<close> shows \<open>fp s 0 = (0,s)\<close>
  using assms calculation_init is_axiom_finite_calculation by auto

lemma is_path_f:
  assumes \<open>ic s\<close> shows \<open>fp s n \<in> calculation s \<and> fst (fp s n) = n
  \<and> (snd (fp s (Suc n))) \<in> set (solve (snd (fp s n))) \<and> ic (snd (fp s n))\<close>
proof (induct \<open>n\<close>)
  case 0
  then show \<open>?case\<close>
    using assms fSuc is_path_f_0 calculation.intros(1) is_axiom_finite_calculation
    by (metis prod_simps(1) prod_simps(2))
next
  case (Suc n)
  then show \<open>?case\<close>
    using assms fSuc is_axiom_finite_calculation by blast
qed

lemma eval_cong: \<open>\<forall>x \<in> set (free p). e x = e' x \<Longrightarrow> semantics m e p = semantics m e' p\<close>
proof (induct \<open>p\<close> arbitrary: \<open>e\<close> \<open>e'\<close>)
  case (Pre b i v)
  then show \<open>?case\<close>
    by (metis (no_types, lifting) map_eq_conv program(32) semantics.simps(1))
next
  case (Con p1 p2)
  then show \<open>?case\<close>
    by (metis (mono_tags, lifting) Un_iff free.simps(2) semantics.simps(2) set_append)
next
  case (Dis p1 p2)
  then show \<open>?case\<close>
    by (metis (mono_tags, lifting) Un_iff free.simps(3) semantics.simps(3) set_append)
next
  case (Uni p)
  then have \<open>\<forall>x\<in>set (free p). (case_nat z e) x = (case_nat z e') x\<close> for z
    using dump_suc unfolding Nitpick.case_nat_unfold by (metis diff_Suc_1 nat.exhaust program(35))
  then show \<open>?case\<close>
    using Uni(1) by (metis semantics.simps(4))
next
  case (Exi p)
  then have \<open>\<forall>x\<in>set (free p). (case_nat z e) x = (case_nat z e') x\<close> for z
    using dump_suc unfolding Nitpick.case_nat_unfold by (metis diff_Suc_1 nat.exhaust program(36))
  then show \<open>?case\<close>
    using Exi(1) by (metis semantics.simps(5))
qed

lemma semantics_alternative2: \<open>semantics_alternative m e s = (\<exists>p \<in> set s. semantics m e p)\<close>
  by (induct \<open>s\<close>) auto

lemma semantics_alternative_cong: \<open>(\<forall>x. x \<in> set (frees s) \<longrightarrow> e x = e' x) \<longrightarrow>
  semantics_alternative m e s = semantics_alternative m e' s\<close>
  by (induct \<open>s\<close>) (simp,
      metis eval_cong Un_iff set_append frees.simps(2) semantics_alternative.simps(2))

subsection \<open>Soundness\<close>

lemma subst_var: \<open>map e (mend x s v) = map (e \<circ> subst_var x s) v\<close>
  by (metis map_map subst_var_eq_mend)

lemma subst_var_Uni_Exi_env:
  \<open>(case_nat z e) \<circ> (subst_var (Suc x) (Suc s)) = case_nat z (e \<circ> (subst_var x s))\<close>
  unfolding subst_var_def Nitpick.case_nat_unfold by fastforce

lemma subst_eq_subst_var_env: \<open>semantics m e (subst x s p) = semantics m (e \<circ> (subst_var x s)) p\<close>
  by (induct \<open>p\<close> arbitrary: \<open>e\<close> \<open>x\<close> \<open>s\<close>) (simp_all add: subst_var subst_var_Uni_Exi_env)

lemma subst_var_eq_case_nat_0: \<open>subst_var 0 s = case_nat s id\<close>
  unfolding subst_var_def Nitpick.case_nat_unfold by auto

lemma env_case_nat: \<open>e \<circ> case_nat s id = case_nat (e s) e\<close>
  unfolding Nitpick.case_nat_unfold by auto

lemma eval_subst: \<open>semantics m e (subst 0 s p) = semantics m (case_nat (e s) e) p\<close>
  using subst_eq_subst_var_env subst_var_eq_case_nat_0 by (simp add: env_case_nat)

lemma sound_Uni':
  assumes \<open>u \<notin> set (frees (Uni p # s))\<close> \<open>valid (s@[subst 0 u p])\<close> and
    ime: \<open>is_model_environment (M,I) e\<close> and sa: \<open>\<not> semantics_alternative (M,I) e s\<close> and zM: \<open>z \<in> M\<close>
  shows \<open>semantics (M,I) (case_nat z e) p\<close>
proof -
  have \<open>semantics (M,I) (case_nat z (e(u:=z))) p = semantics (M,I) (case_nat z e) p\<close>
    unfolding Nitpick.case_nat_unfold using assms(1) dump_suc
    by (fastforce intro!: eval_cong)
  moreover have \<open>is_model_environment (M,I) (e(u := z)) \<longrightarrow> semantics_alternative (M,I) (e(u := z))
      (s @ [subst 0 u p])\<close>
    using assms(2) unfolding valid_def by blast
  ultimately have \<open>(\<forall>n. (if n = u then z else e n) \<in> M) \<longrightarrow>
      semantics_alternative (M,I) (e(u := z)) s \<or> semantics (M,I) (case_nat z e) p\<close>
    using eval_subst is_model_environment_def semantics_alternative2 by auto
  moreover have \<open>u \<notin> set (dump (free p)) \<and> u \<notin> set (frees s)\<close>
    using assms by simp
  moreover have \<open>\<forall>n. e n \<in> M\<close>
    using ime is_model_environment_def by simp
  ultimately show \<open>?thesis\<close>
    using zM sa semantics_alternative_cong by (metis fun_upd_other)
qed

lemma sound_Uni:
  assumes \<open>u \<notin> set (frees (Uni p # s))\<close> and \<open>valid (s@[subst 0 u p])\<close>
  shows \<open>valid (Uni p # s)\<close>
  unfolding valid_def using assms sound_Uni' by auto

lemma axiom_is_valid: \<open>is_axiom (base t) \<Longrightarrow> valid (base t)\<close>
  unfolding valid_def using semantics_alternative2 by (cases t) fastforce+

lemma solve_maintains_validity_backwards_dir:
  assumes \<open>\<forall>seq \<in> set (solve s). valid (base seq)\<close>
  shows \<open>valid (base s)\<close>
proof (cases \<open>s\<close>)
  case Nil
  then show \<open>?thesis\<close>
    using assms by auto
next
  case (Cons np list)
  then show \<open>?thesis\<close>
  proof (cases \<open>np\<close>)
    case (Pair n p')
    then show \<open>?thesis\<close>
    proof (cases \<open>p'\<close>)
      case (Pre b i v)
      then have Cases: \<open>solve s = [] \<or> solve s = [list @ [(0,Pre b i v)]]\<close>
        using assms Cons Pair stop_alt Pre by simp
      from stop_alt have \<open>solve s = [] \<Longrightarrow> is_axiom (base s)\<close>
        by (metis calculation_init calculation_upwards list.discI list.set_cases)
      with axiom_is_valid have C1: \<open>solve s = [] \<Longrightarrow> valid (base s)\<close>
        by simp
      from valid_def have \<open>\<forall>l m q. valid (base (l @ [(m,q)])) = valid (base ([(m,q)] @ l))\<close>
        using base_alt semantics_alternative2 by simp
      with assms have C2: \<open>solve s = [list @ [(0,Pre b i v)]] \<Longrightarrow> valid (base s)\<close>
        by (simp add: Pair Pre local.Cons)
      from Cases C1 C2 show \<open>?thesis\<close>
        by auto
    next
      case (Con p q)
      then show \<open>?thesis\<close>
        using assms base_alt semantics_alternative2 Pair local.Cons
        unfolding valid_def by fastforce
    next
      case (Dis p q)
      then show \<open>?thesis\<close>
        using assms base_alt semantics_alternative2 Pair local.Cons
        unfolding valid_def by fastforce
    next
      case (Uni p)
      have \<open>Uni p # map snd list = Uni p # base list\<close>
        using base_alt by fastforce
      then have \<open>fresh (frees (Uni p # base list)) \<notin> set (frees (Uni p # map snd list))\<close>
        by (metis fresh_is_fresh)
      then show \<open>?thesis\<close>
        using Uni assms base_alt sound_Uni Pair Uni base_alt Cons by fastforce
    next
      case (Exi p)
      then have \<open>\<forall>seq\<in>set [list @ [(0, subst 0 n p), (Suc n, p')]]. valid (base seq)\<close>
        using assms Pair Cons by simp
      then have \<open>valid (base list @ [subst 0 n p, p'])\<close>
        using base_alt by simp
      then have \<open>\<exists>p \<in> set (base list @ [subst 0 n p, p']). semantics m e p\<close>
        if \<open>is_model_environment m e\<close> for m e
        unfolding valid_def using that semantics_alternative2 by blast
      then have \<open>semantics m (case_nat (e n) e) p \<or> (\<exists>p \<in> set (p' # base list). semantics m e p)\<close>
        if \<open>is_model_environment m e\<close> for m e
        using that eval_subst by simp
      then have \<open>valid (p' # base list)\<close>
        using Exi semantics_alternative2 unfolding is_model_environment_def valid_def
        using semantics.simps(5) semantics_alternative.simps(2) by blast
      then show \<open>?thesis\<close>
        using Pair Cons by simp
    qed
  qed
qed

lemma soundness':
  assumes \<open>deepest_leaf \<in> fst ` calculation s\<close>
    and \<open>\<forall>y u. (y,u) \<in> calculation s \<longrightarrow> y \<le> deepest_leaf\<close>
    and \<open>height = deepest_leaf - n \<and> (n,t) \<in> calculation s\<close>
  shows \<open>valid (base t)\<close>
  using assms(3)
proof (induct \<open>height\<close> arbitrary: \<open>n\<close> \<open>t\<close>)
  case 0
  with assms have \<open>n = deepest_leaf\<close> \<open>(n,t) \<in> calculation s\<close>
    by auto
  then show \<open>?case\<close>
    using assms(2) axiom_is_valid calculation_upwards
    by (meson Suc_le_eq less_irrefl_nat)
next
  case (Suc height)
  then show \<open>?case\<close>
    using calculation_upwards solve_maintains_validity_backwards_dir
    by (metis Suc_diff_diff calculation.intros(2) minus_nat.diff_0)
qed

lemma list_make_sequent_inverse: \<open>base (map (\<lambda>p. (0,p)) s) = s\<close>
  using base_alt by (induct \<open>s\<close>) simp_all

lemma max_exists: \<open>finite (X::nat set) \<Longrightarrow> X \<noteq> {} \<longrightarrow> (\<exists>x. x \<in> X \<and> (\<forall>y. y \<in> X \<longrightarrow> y \<le> x))\<close>
  using Max.coboundedI Max_in by blast

definition init :: \<open>sequent \<Rightarrow> bool\<close> where \<open>init s \<equiv> \<forall>x \<in> (set s). fst x = 0\<close>

lemma soundness:
  assumes \<open>finite (calculation (map (\<lambda>p. (0,p)) s))\<close>
  shows \<open>valid s\<close>
proof -
  have \<open>init (map (\<lambda>p. (0,p)) s)\<close> and \<open>finite (fst ` (calculation (map (\<lambda>p. (0,p)) s)))\<close>
    unfolding init_def using assms by simp_all
  then show \<open>?thesis\<close>
    using assms soundness' list_make_sequent_inverse max_exists
    by (metis (mono_tags,lifting) empty_iff fst_conv image_eqI calculation.intros(1))
qed

subsection \<open>Contains / Considers\<close>

definition contains :: \<open>(nat \<Rightarrow> (nat \<times> sequent)) \<Rightarrow> nat \<Rightarrow> nat \<times> nnf \<Rightarrow> bool\<close> where
  \<open>contains f n nf \<equiv> nf \<in> set (snd (f n))\<close>

definition considers :: \<open>(nat \<Rightarrow> (nat \<times> sequent)) \<Rightarrow> nat \<Rightarrow> nat \<times> nnf \<Rightarrow> bool\<close> where
  \<open>considers f n nf \<equiv> case snd (f n) of [] \<Rightarrow> False | (x # xs) \<Rightarrow> x = nf\<close>

lemma progress:
  assumes \<open>ic s\<close> \<open>snd (fp s n) = a # l\<close>
  shows \<open>\<exists>zs. snd (fp s (Suc n)) = l@zs\<close>
proof (cases a)
  case (Pair _ p)
  have \<open>(snd (fp s (Suc n))) \<in> set (solve (snd (fp s n)))\<close>
    using assms(1) is_path_f by blast
  then show \<open>?thesis\<close>
    using Pair assms(2) by (induct \<open>p\<close>) (auto simp: stop_alt)
qed

lemma contains_considers':
  assumes \<open>ic s\<close> \<open>snd (fp s n) = xs @ y # ys\<close>
  shows \<open>\<exists>m zs. snd (fp s (n+m)) = y # zs\<close>
  using assms(2)
proof (induct \<open>xs\<close> arbitrary: \<open>n\<close> \<open>ys\<close>)
  case Nil
  then show \<open>?case\<close>
    using append_Nil by (metis Nat.add_0_right)
next
  case Cons
  then show \<open>?case\<close>
    using append_Cons by (metis (no_types,lifting) add_Suc_shift append_assoc assms(1) progress)
qed

lemma contains_considers:
  assumes \<open>ic s\<close> and \<open>contains (fp s) n y\<close>
  shows \<open>\<exists>m. considers (fp s) (n+m) y\<close>
proof -
  have \<open>\<exists>xs ys. snd (fp s n) = xs @ y # ys\<close>
    using assms(2) unfolding contains_def by (simp add: split_list)
  then have \<open>\<exists>m zs. snd (fp s (n+m)) = y # zs\<close>
    using assms(1) contains_considers' by blast
  then show \<open>?thesis\<close>
    unfolding considers_def by (metis (mono_tags, lifting) list.simps(5))
qed

lemma contains_propagates_Pre:
  assumes \<open>ic s\<close> and \<open>contains (fp s) n (0,Pre b i v)\<close>
  shows \<open>contains (fp s) (n+q) (0,Pre b i v)\<close>
proof (induct \<open>q\<close>)
  case 0
  then show \<open>?case\<close>
    using assms by simp
next
  case IH: (Suc q)
  then obtain ys and zs where
    1: \<open>snd (fp s (n + q)) = ys @ (0,Pre b i v) # zs \<and> (0,Pre b i v) \<notin> set ys\<close>
    unfolding contains_def by (meson split_list_first)
  then have 2: \<open>(snd (fp s (Suc (n + q)))) \<in> set (solve (snd (fp s (n + q))))\<close>
    using assms is_path_f by blast
  then show \<open>?case\<close>
  proof (cases \<open>ys\<close>)
    case Nil
    then show \<open>?thesis\<close>
      using 1 2 contains_def by (simp add: stop_alt split: if_splits)
  next
    case (Cons a _)
    then show \<open>?thesis\<close>
    proof (cases \<open>a\<close>)
      case (Pair _ p)
      then show \<open>?thesis\<close>
        using 1 contains_def assms Cons progress by fastforce
    qed
  qed
qed

lemma contains_propagates_Con:
  assumes \<open>ic s\<close> and \<open>contains (fp s) n (0,Con p q)\<close>
  shows \<open>\<exists>y. contains (fp s) (n+y) (0,p) \<or> contains (fp s) (n+y) (0,q)\<close>
proof -
  obtain l where 1: \<open>considers (fp s) (n+l) (0,Con p q)\<close>
    using assms contains_considers by blast
  then have 2: \<open>(snd (fp s (Suc (n + l)))) \<in> set (solve (snd (fp s (n + l))))\<close>
    using assms is_path_f by blast
  then show \<open>?thesis\<close>
  proof (cases \<open>snd (fp s (n + l))\<close>)
    case Nil
    then show \<open>?thesis\<close>
      using 1 considers_def by simp
  next
    case Cons
    then show \<open>?thesis\<close>
      using 1 2 considers_def contains_def exI[where x=\<open>Suc l\<close>] by fastforce
  qed
qed

lemma contains_propagates_Dis:
  assumes \<open>ic s\<close> and \<open>contains (fp s) n (0,Dis p q)\<close>
  shows \<open>\<exists>y. contains (fp s) (n+y) (0,p) \<and> contains (fp s) (n+y) (0,q)\<close>
proof -
  obtain l where 1: \<open>considers (fp s) (n+l) (0,Dis p q)\<close>
    using assms contains_considers by blast
  then have 2: \<open>(snd (fp s (Suc (n + l)))) \<in> set (solve (snd (fp s (n + l))))\<close>
    using assms is_path_f by blast
  then show \<open>?thesis\<close>
  proof (cases \<open>snd (fp s (n + l))\<close>)
    case Nil
    then show \<open>?thesis\<close>
      using 1 considers_def by simp
  next
    case Cons
    then show \<open>?thesis\<close>
      using 1 2 considers_def contains_def using exI[where x=\<open>Suc l\<close>] by simp
  qed
qed

lemma contains_propagates_Uni:
  assumes \<open>ic s\<close> and \<open>contains (fp s) n (0,Uni p)\<close>
  shows
    \<open>\<exists>y. contains (fp s) (Suc(n+y)) (0,(subst 0 (fresh (frees (map snd (snd (fp s (n+y)))))) p))\<close>
proof -
  obtain l where 1: \<open>considers (fp s) (n+l) (0,Uni p)\<close>
    using assms contains_considers by blast
  then have 2: \<open>(snd (fp s (Suc (n + l)))) \<in> set (solve (snd (fp s (n + l))))\<close>
    using assms is_path_f by blast
  then show \<open>?thesis\<close>
  proof (cases \<open>snd (fp s (n + l))\<close>)
    case Nil
    then show \<open>?thesis\<close>
      using 1 considers_def by simp
  next
    case Cons
    then show \<open>?thesis\<close>
      using 1 2 considers_def contains_def base_alt frees_alt subst_def exI[where x=\<open>l\<close>]
      by (simp add: maps_def)
  qed
qed

lemma contains_propagates_Exi:
  assumes \<open>ic s\<close> and \<open>contains (fp s) n (m,Exi p)\<close>
  shows \<open>(\<exists>y. (contains (fp s) (n+y) (0,(subst 0 m p)) \<and> (contains (fp s) (n+y) (Suc m,Exi p))))\<close>
proof -
  obtain l where 1: \<open>considers (fp s) (n+l) (m,Exi p)\<close>
    using assms contains_considers by blast
  then have 2: \<open>(snd (fp s (Suc (n + l)))) \<in> set (solve (snd (fp s (n + l))))\<close>
    using assms is_path_f by blast
  then show \<open>?thesis\<close>
  proof (cases \<open>snd (fp s (n + l))\<close>)
    case Nil
    then show \<open>?thesis\<close>
      using 1 considers_def by simp
  next
    case Cons
    then show \<open>?thesis\<close>
      using 1 2 considers_def contains_def exI[where x=\<open>Suc l\<close>] by simp
  qed
qed

lemma Exi_downward:
  assumes \<open>ic s\<close> \<open>init s\<close> \<open>(Suc m, Exi g) \<in> set (snd (fp s n))\<close>
  shows \<open>\<exists>n'. (m,Exi g) \<in> set (snd (fp s n'))\<close>
  using assms(3)
proof (induct \<open>n\<close>)
  case 0
  then show \<open>?case\<close>
    using assms init_def is_path_f_0 by fastforce
next
  case (Suc x)
  then have fxSuc: \<open>fp s x \<in> calculation s\<close> \<open>fst (fp s x) = x\<close>
    \<open>snd (fp s (Suc x)) \<in> set (solve (snd (fp s x)))\<close> \<open>infinite (calculation (snd (fp s x)))\<close>
    using assms is_path_f by blast+
  then show \<open>?case\<close>
  proof (cases \<open>fp s x\<close>)
    case fxPair: (Pair _ l)
    then show \<open>?thesis\<close>
    proof (cases \<open>l\<close>)
      case Nil
      then show \<open>?thesis\<close>
        using Suc fxSuc fxPair by simp
    next
      case (Cons h t)
      then show \<open>?thesis\<close>
      proof (cases \<open>h\<close>)
        case (Pair m' p)
        then show \<open>?thesis\<close>
        proof (cases \<open>p\<close>)
          case Pre
          then show \<open>?thesis\<close>
            using Suc fxSuc fxPair Cons Pair by (simp add: stop_alt split: if_splits)
        next
          case Con
          then show \<open>?thesis\<close>
            using Suc fxSuc fxPair Cons Pair by (fastforce split: if_splits)
        next
          case Dis
          then show \<open>?thesis\<close>
            using Suc fxSuc fxPair Cons Pair by simp
        next
          case Uni
          then show \<open>?thesis\<close>
            using Suc fxSuc fxPair Cons Pair by (simp split: if_splits)
        next
          case (Exi p)
          then have \<open>snd (fp s (Suc x)) = t @ [(0,subst 0 m' p), (Suc m', Exi p)]\<close>
            using fxSuc(3) fxPair Cons Pair by simp
          then consider \<open>(Suc m, Exi g) \<in> set t\<close> | \<open>m = m'\<close> \<open>g = p\<close>
            using Suc(2) by auto
          then show \<open>?thesis\<close>
            using Suc(1) Exi Pair fxPair Cons by (metis snd_conv insert_iff list.set(2))
        qed
      qed
    qed
  qed
qed

lemma Exi0:
  assumes \<open>ic s\<close> and \<open>init s\<close>
  shows \<open>\<forall>n. contains (fp s) n (m,Exi p) \<longrightarrow> (\<exists>n'. contains (fp s) n' (0,Exi p))\<close>
  using assms Exi_downward contains_def by (induct \<open>m\<close>) auto

lemma Exi_upward':
  assumes \<open>ic s\<close> and \<open>init s\<close>
  shows \<open>\<forall>n. contains (fp s) n (0,Exi p) \<longrightarrow> (\<exists>n'. contains (fp s) n' (m,Exi p))\<close>
  using assms contains_propagates_Exi by (induct \<open>m\<close>) (simp, blast)

lemma Exi_upward:
  assumes \<open>ic s\<close> and \<open>init s\<close> and \<open>contains (fp s) n (m,Exi p)\<close>
  shows \<open>\<exists>n'. contains (fp s) n' (0,subst 0 m' p)\<close>
  using assms Exi0 Exi_upward' contains_propagates_Exi by blast

definition ntou :: \<open>nat \<Rightarrow> proxy\<close> where \<open>ntou n \<equiv> replicate n ()\<close>

lemma inj_ntou: \<open>inj ntou\<close>
  unfolding inj_def ntou_def using length_replicate by simp

definition uton :: \<open>proxy \<Rightarrow> nat\<close> where \<open>uton \<equiv> inv ntou\<close>

lemma uton_ntou_id[simp]: \<open>uton \<circ> ntou = id\<close>
  unfolding uton_def using inj_ntou by simp

subsection \<open>Falsifying Model From Failing Path\<close>

definition model :: \<open>sequent \<Rightarrow> model\<close> where
  \<open>model s \<equiv> (range ntou,\<lambda> i us. (\<forall>n m. \<not> contains (fp s) n (m,Pre True i (map uton us))))\<close>

lemma is_env_model_ntou: \<open>is_model_environment (model s) ntou\<close>
  using is_model_environment_def model_def by simp

definition is_Exi :: \<open>nnf \<Rightarrow> bool\<close> where \<open>is_Exi f \<equiv> case f of Exi _ \<Rightarrow> True | _ \<Rightarrow> False\<close>

lemma is_Exi: \<open>\<not> is_Exi (Pre b i v) \<and> \<not> is_Exi (Con p q) \<and> \<not> is_Exi (Dis p q) \<and> \<not> is_Exi (Uni p)\<close>
  using is_Exi_def by simp

lemma index0:
  assumes \<open>init s\<close> \<open>(n,k) \<in> calculation s\<close> \<open>(m,p) \<in> (set k)\<close> \<open>\<not> is_Exi p\<close>
  shows \<open>m = 0\<close>
  using assms(2-)
proof (induct \<open>n\<close> arbitrary: \<open>k\<close> \<open>m\<close> \<open>p\<close>)
  case 0
  then show \<open>?case\<close>
    using assms init_def calculation_init by fastforce
next
  case (Suc n)
  then obtain t where N: \<open>(n,t) \<in> calculation s\<close> \<open>k \<in> set (solve t)\<close> \<open>\<not> is_axiom (base t)\<close>
    using calculation_downwards by blast
  then show \<open>?case\<close>
  proof (cases \<open>t\<close>)
    case Nil
    then show \<open>?thesis\<close>
      using assms Suc N by simp
  next
    case (Cons a _)
    then show \<open>?thesis\<close>
    proof (cases \<open>a\<close>)
      case (Pair _ q)
      then show \<open>?thesis\<close>
        using N Suc Cons stop_alt unfolding is_Exi_def by (cases \<open>q\<close>) fastforce+
    qed
  qed
qed

lemma not_is_Exi:
  assumes \<open>ic s\<close> and \<open>init s\<close> and \<open>(contains (fp s) n (m,p))\<close> \<open>\<not> is_Exi p\<close>
  shows \<open>m = 0\<close>
  using assms contains_def index0 is_path_f prod.collapse by metis

lemma size_subst: \<open>size (subst x s p) = size p\<close>
  by (induct \<open>p\<close> arbitrary: \<open>x\<close> \<open>s\<close>) simp_all

lemma model':
  assumes \<open>ic s\<close> \<open>init s\<close> \<open>contains (fp s) n (m,p)\<close>
  shows \<open>\<not> (semantics (model s) ntou p)\<close>
  using assms(3)
proof (induct \<open>size p\<close> arbitrary: \<open>p\<close> \<open>m\<close> \<open>n\<close> rule: nat_less_induct)
  case 1
  then show \<open>?case\<close>
  proof (cases \<open>p\<close>)
    case (Pre b i v)
    then show \<open>?thesis\<close>
    proof (cases \<open>b\<close>)
      case True
      then show \<open>?thesis\<close>
        using 1(2) Pre unfolding model_def by auto
    next
      case False
      with Pre show \<open>?thesis\<close>
      proof (clarsimp simp: model_def)
        fix na ma
        assume *: \<open>\<not> b\<close> \<open>p = Pre False i v\<close> \<open>contains (fp s) na (ma, Pre True i v)\<close>
        then have 3: \<open>m = 0 \<and> ma = 0\<close>
          using 1(2) assms(1,2) is_Exi not_is_Exi by auto
        then obtain y where y: \<open>considers (failing_path (calculation s)) (na+n+y) (0,Pre True i v)\<close>
          using *(3) assms(1) contains_considers contains_propagates_Pre by blast
        moreover have \<open>n + na + y = na + n + y\<close>
          by simp
        ultimately have 5: \<open>contains (failing_path (calculation s)) (na+n+y) (0,Pre False i v)\<close>
          using 1(2) 3 False Pre assms(1) contains_propagates_Pre by (metis (full_types))
        then have \<open>is_axiom (base (snd ((failing_path (calculation s)) (na+n+y))))\<close>
        proof (cases \<open>snd ((failing_path (calculation s)) (na+n+y))\<close>)
          case Nil
          then show \<open>?thesis\<close>
            using 5 unfolding contains_def by simp
        next
          case Cons
          then show \<open>?thesis\<close>
            using y 5 base_alt unfolding contains_def considers_def by force
        qed
        then show False
          using assms(1) is_axiom_finite_calculation is_path_f by blast
      qed
    qed
  next
    case Con
    then show \<open>?thesis\<close>
      using assms 1 is_Exi not_is_Exi contains_propagates_Con
      by (metis Nat.add_0_right add_Suc_right nnf.size(7)
          less_add_Suc1 less_add_Suc2 semantics.simps(2))
  next
    case Dis
    then show \<open>?thesis\<close>
      using assms 1 contains_propagates_Dis is_Exi not_is_Exi
      by (metis Nat.add_0_right add_Suc_right nnf.size(8)
          less_add_Suc1 less_add_Suc2 semantics.simps(3))
  next
    case (Uni q)
    then have \<open>m = 0\<close>
      using 1 assms Uni is_Exi not_is_Exi by simp
    then obtain y where
      \<open>contains (fp s) (Suc (n + y)) (0,subst 0 (fresh (frees (map snd (snd ((fp s) (n + y)))))) q)\<close>
      using 1 assms Uni contains_propagates_Uni by meson
    moreover have \<open>Suc (size q) = size p\<close>
      using Uni 1 by simp
    ultimately show \<open>?thesis\<close>
      using Uni 1(1) eval_subst is_env_model_ntou size_subst unfolding is_model_environment_def
      by (metis lessI semantics.simps(4))
  next
    case (Exi q)
    then have \<open>contains (fp s) n (m, Exi q)\<close>
      using 1 by blast
    then have \<open>\<exists>n'. contains (fp s) n' (0,subst 0 m q)\<close> for m
      using assms Exi_upward by blast
    moreover have \<open>Suc (size q) = size p\<close>
      using Exi 1 by simp
    ultimately have \<open>\<not> semantics (model s) ntou (subst 0 m q)\<close> for m
      using 1 size_subst by (metis less_Suc_eq)
    then have \<open>\<not> semantics (model s) (case_nat (ntou m) ntou) q\<close> for m
      using eval_subst by blast
    then show \<open>?thesis\<close>
      using Exi unfolding model_def by simp
  qed
qed

lemma model:
  assumes \<open>ic s\<close> and \<open>init s\<close> \<open>contains (fp s) n (m,p)\<close>
  shows \<open>\<not> (semantics (model s) ntou p)\<close>
  using assms model' by fast

subsection \<open>Completeness\<close>

lemma completeness':
  assumes \<open>ic s\<close> and \<open>init s\<close> \<open>m \<in> set s\<close>
  shows \<open>\<not> semantics (model s) ntou (snd m)\<close>
  using assms model unfolding contains_def by (metis eq_snd_iff is_path_f_0)

lemma completeness'':
  assumes \<open>ic (map (\<lambda>p. (0,p)) s)\<close> and \<open>init (map (\<lambda>p. (0,p)) s)\<close> \<open>p \<in> set s\<close>
  shows \<open>\<not> semantics (model (map (\<lambda>p. (0,p)) s)) ntou p\<close>
  using assms completeness' by fastforce

lemma completeness:
  assumes \<open>ic (map (\<lambda>p. (0,p)) s)\<close> shows \<open>\<not> valid s\<close>
proof -
  have \<open>init (map (\<lambda>p. (0,p)) s)\<close>
    unfolding init_def by simp
  then show \<open>?thesis\<close>
    unfolding valid_def using assms is_env_model_ntou semantics_alternative2 completeness'' by fast
qed

subsection \<open>Algorithm\<close>

definition loop :: \<open>sequent list \<Rightarrow> nat \<Rightarrow> sequent list\<close> where
  \<open>loop s n \<equiv> ((concat \<circ> map solve) ^^ n) s\<close>

lemma loop_upwards: \<open>loop s n = [] \<Longrightarrow> loop s (n+m) = []\<close>
  using loop_def by (induct \<open>m\<close>) auto

lemma loop: \<open>((n,x) \<in> calculation s) = (x \<in> set (loop [s] n))\<close>
proof (induct \<open>n\<close> arbitrary: \<open>x\<close>)
  case 0
  then show \<open>?case\<close>
    using loop_def calculation_init by simp
next
  case (Suc m)
  show \<open>?case\<close>
  proof
    assume \<open>(Suc m,x) \<in> calculation s\<close>
    then have \<open>\<exists>t. (m,t) \<in> calculation s \<and> x \<in> set (solve t) \<and> \<not> is_axiom (base t)\<close>
      using calculation_downwards by blast
    then obtain t where 1: \<open>(m,t) \<in> calculation s\<close> \<open>x \<in> set (solve t)\<close> \<open>\<not> is_axiom (base t)\<close>
      by blast
    then show \<open>(x \<in> set (loop [s] (Suc m)))\<close>
      using Suc unfolding loop_def by auto
  next
    assume \<open>(x \<in> set (loop [s] (Suc m)))\<close>
    then show \<open>(Suc m,x) \<in> calculation s\<close>
      using Suc unfolding loop_def by (auto intro: calculation.intros(2))
  qed
qed

lemma calculation_f: \<open>calculation s = (\<Union>x. set (map (\<lambda>y. (x,y)) (loop [s] x)))\<close>
  using loop by fastforce

lemma finite_calculation_right_dir:
  assumes \<open>finite (calculation s)\<close>
  shows \<open>\<exists>m. loop [s] m = []\<close>
proof -
  have \<open>finite (fst ` (calculation s))\<close>
    using assms by simp
  then obtain x where xMax: \<open>x \<in> fst ` calculation s \<and> (\<forall>y. y \<in> fst ` calculation s \<longrightarrow> y \<le> x)\<close>
    using max_exists calculation.simps by (metis empty_iff image_is_empty)
  then show \<open>?thesis\<close>
  proof (cases \<open>loop [s] (Suc x)\<close>)
    assume \<open>loop [s] (Suc x) = []\<close>
    then show \<open>?thesis\<close>
      by blast
  next
    fix a l
    assume \<open>loop [s] (Suc x) = a # l\<close>
    then have \<open>(Suc x,a) \<in> calculation s\<close>
      using loop by simp
    then show \<open>?thesis\<close>
      using xMax by fastforce
  qed
qed

lemma finite_calculation_left_dir:
  assumes \<open>\<exists>m. loop [s] m = []\<close>
  shows \<open>finite (calculation s)\<close>
proof -
  obtain m where \<open>loop [s] m = []\<close>
    using assms by blast
  then have \<open>\<forall>y. loop [s] (m+y) = []\<close>
    using loop_upwards by simp
  then have 1: \<open>(\<Union>x\<in>Collect ((\<le>) m). Pair x ` set (loop [s] x)) = (\<Union>x\<in>Collect ((\<le>) m). {})\<close>
    using SUP_cong image_is_empty le_Suc_ex mem_Collect_eq set_empty by (metis (no_types,lifting))
  then have \<open>(UNIV::nat set) = {y. y < m} \<union> {y. m \<le> y}\<close>
    by fastforce
  then show \<open>?thesis\<close>
    using 1 calculation_f by (auto elim: ssubst)
qed

lemma finite_calculation: \<open>finite (calculation s) = (\<exists>m. loop [s] m = [])\<close>
  using finite_calculation_left_dir finite_calculation_right_dir by blast

corollary finite_calculation_prover':
  \<open>finite (calculation s) = iterator null ((concat \<circ> map solve)) [s]\<close>
  using finite_calculation repeat_compower unfolding loop_def iterator_def
  by (metis (no_types, hide_lams) null.simps list.exhaust)

corollary finite_calculation_prover: \<open>finite (calculation s) = iterator null solves [s]\<close>
  using finite_calculation_prover' solves_alt by presburger

section \<open>Correctness\<close>

lemmas magic = soundness completeness finite_calculation_prover

theorem correctness: \<open>CHECK\<close> \<open>VALID\<close>
proof -
  have \<open>\<forall>p. [[(0,p)]] = [map (Pair 0) [p]]\<close>
    by simp
  then have \<open>CHECK\<close>
    unfolding check_def
    using magic valid_def semantics_alternative.simps main_def
    by (metis (no_types,hide_lams))
  moreover have \<open>VALID\<close>
    using magic by fastforce
  ultimately show \<open>CHECK\<close> \<open>VALID\<close> .
qed

corollary \<open>\<exists>p. check p\<close> \<open>\<exists>p. \<not> check p\<close>
proof -
  have \<open>\<not> valid [Pre True 0 []]\<close> \<open>valid [Dis (Pre True 0 []) (Pre False 0 [])]\<close>
    using valid_def is_model_environment_def by auto
  then show \<open>\<exists>p. check p\<close> \<open>\<exists>p. \<not> check p\<close>
    using correctness semantics_alternative.simps valid_def by (metis, metis)
qed

section \<open>Code Generation\<close>

value \<open>check test\<close>

value \<open>check (Dis (Pre True 0 []) (Pre False 0 []))\<close>

(* value \<open>check (Pre True 0 [])\<close> *)

proposition \<open>check test\<close>
  by eval

proposition \<open>check (Dis (Pre True 0 []) (Pre False 0 []))\<close>
  by eval

proposition \<open>check test\<close>
  by normalization

proposition \<open>check (Dis (Pre b i v) (Pre (\<not> b) i v))\<close>
  by normalization

code_reflect X datatypes nnf = _ and nat = _ functions check

ML_val

\<open>

val true = X.check (X.Dis (X.Uni (X.Con (X.Pre (false,X.Zero_nat,[X.Zero_nat]),
                                         X.Pre (false,X.Suc X.Zero_nat,[X.Zero_nat]))),
                           X.Dis (X.Exi (X.Pre (true,X.Suc X.Zero_nat,[X.Zero_nat])),
                                  X.Exi (X.Pre (true,X.Zero_nat,[X.Zero_nat])))))

\<close>

export_code \<open>check\<close> \<open>test\<close> in SML module_name X

section \<open>Appendix\<close>

abbreviation (input) \<open>EXAMPLE P \<equiv> (\<forall>x. P x) \<longrightarrow> (\<exists>x. P x)\<close>

proposition \<open>EXAMPLE P\<close>
  by iprover

proposition \<open>EXAMPLE P = ((\<exists>x. \<not> P x) \<or> (\<exists>x. P x))\<close>
  by fast

definition \<open>simple_prover c \<equiv> \<exists>n. null (repeat solves c n)\<close>

lemma \<open>simple_prover [[(0,p)]] = (\<forall>m e. is_model_environment m e \<longrightarrow> semantics m e p)\<close>
  using check_prover correctness unfolding simple_prover_def iterator_def by meson

lemma [code]: \<open>simple_prover c = (if null c then True else simple_prover (solves c))\<close>
  using iterator unfolding simple_prover_def iterator_def by metis

definition \<open>example \<equiv> Dis (Exi (Pre False 0 [0])) (Exi (Pre True 0 [0]))\<close>

value \<open>simple_prover [[(0,example)]]\<close>

section \<open>Acknowledgements\<close>

text \<open>Based on the Archive of Formal Proofs entry Verified-Prover by Tom Ridge (TPHOLs 2005)\<close>

end
