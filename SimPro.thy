section \<open>A Simple Prover\<close>

theory SimPro imports Main begin

datatype nnf = Pre bool "char list" "nat list" | Con nnf nnf | Dis nnf nnf | Uni nnf | Exi nnf

abbreviation (input) "TEST P Q \<equiv> (\<exists>x. P x \<or> Q x) \<longrightarrow> (\<exists>x. Q x) \<or> (\<exists>x. P x)"

proposition "TEST P Q"
by iprover

proposition "TEST P Q = (\<forall>x. \<not> P x \<and> \<not> Q x) \<or> (\<exists>x. Q x) \<or> (\<exists>x. P x)"
by fast

definition \<comment> \<open>TEST P Q\<close>
  "test \<equiv> Dis
    (Uni (Con (Pre False ''P'' [0]) (Pre False ''Q'' [0]))) 
    (Dis (Exi (Pre True ''Q'' [0])) (Exi (Pre True ''P'' [0])))"

type_synonym proxy = "unit list"

type_synonym model = "proxy set \<times> (char list \<Rightarrow> proxy list \<Rightarrow> bool)"

type_synonym environment = "nat \<Rightarrow> proxy"

definition is_model_environment :: "model \<Rightarrow> environment \<Rightarrow> bool" where
  "is_model_environment m e \<equiv> \<forall>n. e n \<in> fst m"

primrec semantics :: "model \<Rightarrow> environment \<Rightarrow> nnf \<Rightarrow> bool" where
  "semantics m e (Pre b i v) = (b = snd m i (map e v))" |
  "semantics m e (Con p q) = (semantics m e p \<and> semantics m e q)" |
  "semantics m e (Dis p q) = (semantics m e p \<or> semantics m e q)" |
  "semantics m e (Uni p) = (\<forall>z \<in> fst m. semantics m (\<lambda>x. case x of 0 \<Rightarrow> z | Suc n \<Rightarrow> e n) p)" |
  "semantics m e (Exi p) = (\<exists>z \<in> fst m. semantics m (\<lambda>x. case x of 0 \<Rightarrow> z | Suc n \<Rightarrow> e n) p)"

primrec adjust :: "nat list \<Rightarrow> nat list" where
  "adjust [] = []" |
  "adjust (h # t) = (case h of 0 \<Rightarrow> adjust t | Suc n \<Rightarrow> n # adjust t)"

primrec fv :: "nnf \<Rightarrow> nat list" where
  "fv (Pre _ _ v) = v" |
  "fv (Con p q) = fv p @ fv q" |
  "fv (Dis p q) = fv p @ fv q" |
  "fv (Uni p) = adjust (fv p)" |
  "fv (Exi p) = adjust (fv p)"

primrec subst :: "(nat \<Rightarrow> nat) \<Rightarrow> nnf \<Rightarrow> nnf" where
  "subst f (Pre b i v) = Pre b i (map f v)" |
  "subst f (Con p q) = Con (subst f p) (subst f q)" |
  "subst f (Dis p q) = Dis (subst f p) (subst f q)" |
  "subst f (Uni p) = Uni (subst (\<lambda>x. case x of 0 \<Rightarrow> 0 | Suc n \<Rightarrow> Suc (f n)) p)" |
  "subst f (Exi p) = Exi (subst (\<lambda>x. case x of 0 \<Rightarrow> 0 | Suc n \<Rightarrow> Suc (f n)) p)"

definition bind :: "nnf \<Rightarrow> nat \<Rightarrow> nnf" where
  "bind p y \<equiv> subst (\<lambda>x. case x of 0 \<Rightarrow> y | Suc n \<Rightarrow> n) p"

primrec maxn :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "maxn 0 n = n" |
  "maxn (Suc n) n' = Suc (case n' of 0 \<Rightarrow> n | Suc n'' \<Rightarrow> maxn n n'')"

primrec maxl :: "nat list \<Rightarrow> nat" where
  "maxl [] = 0" |
  "maxl (h # t) = maxn h (maxl t)"

primrec null :: "'a list \<Rightarrow> bool" where
  "null [] = True" |
  "null (_ # _) = False"

definition fresh :: "nat list \<Rightarrow> nat" where
  "fresh l \<equiv> if null l then 0 else Suc (maxl l)"

primrec flatten :: "'a list list \<Rightarrow> 'a list" where
  "flatten [] = []" |
  "flatten (h # t) = h @ flatten t"

definition all :: "('a \<Rightarrow> 'b list) \<Rightarrow> 'a list \<Rightarrow> 'b list" where
  "all f l \<equiv> flatten (map f l)"

primrec member :: "'a \<Rightarrow> 'a list \<Rightarrow> bool" where
  "member _ [] = False" |
  "member a (h # t) = (if a = h then True else member a t)"

type_synonym sequent = "(nat \<times> nnf) list"

definition solve :: "sequent \<Rightarrow> sequent list" where
  "solve s \<equiv> case s of [] \<Rightarrow> [[]] | h # t \<Rightarrow> (case h of (n,r) \<Rightarrow> (case r of
    Pre b i v \<Rightarrow> if member (Pre (\<not> b) i v) (map snd t) then [] else [t @ [(0,Pre b i v)]] |
    Con p q \<Rightarrow> [t @ [(0,p)],t @ [(0,q)]] |
    Dis p q \<Rightarrow> [t @ [(0,p),(0,q)]] |
    Uni p \<Rightarrow> [t @ [(0,bind p (fresh (all fv (map snd s))))]] |
    Exi p \<Rightarrow> [t @ [(0,bind p n),(Suc n,r)]]))"

primrec repeat :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> 'a" where
  "repeat _ a 0 = a" |
  "repeat f a (Suc n) = f (repeat f a n)"

definition prover :: "sequent list \<Rightarrow> bool" where
  "prover a \<equiv> \<exists>n. repeat (all solve) a n = []"

definition check :: "nnf \<Rightarrow> bool" where
  "check p \<equiv> prover [[(0,p)]]"

abbreviation (input) "CHECK \<equiv> check = (\<lambda>p. \<forall>m e. is_model_environment m e \<longrightarrow> semantics m e p)"

inductive_set calculation :: "sequent \<Rightarrow> (nat \<times> sequent) set" for s where
  init[intro]: "(0,s) \<in> calculation s" |
  step[intro]: "(n,k) \<in> calculation s \<Longrightarrow> l \<in> set (solve k) \<Longrightarrow> (Suc n,l) \<in> calculation s"

primrec semantics_alternative :: "model \<Rightarrow> environment \<Rightarrow> nnf list \<Rightarrow> bool" where
  "semantics_alternative _ _ [] = False" |
  "semantics_alternative m e (h # t) = (semantics m e h \<or> semantics_alternative m e t)"

definition valid :: "nnf list \<Rightarrow> bool" where
  "valid l \<equiv> \<forall>m e. is_model_environment m e \<longrightarrow> semantics_alternative m e l"

abbreviation (input) "VALID \<equiv> valid = finite \<circ> calculation \<circ> map (Pair 0)"

proposition "\<forall>m e. is_model_environment m e \<longrightarrow> fst m \<noteq> {}"
using is_model_environment_def
by fast

proposition "\<exists>m. \<forall>e. is_model_environment m e \<and> infinite (fst m)"
using is_model_environment_def infinite_UNIV_listI
by auto

lemma repeat_once: "repeat f (f a) n = f (repeat f a n)"
by (induct n) simp_all

proposition "(\<exists>n. r (repeat f a n)) = (if r a then True else \<exists>n. r (repeat f (f a) n))"
by (metis repeat.simps repeat_once not0_implies_Suc)

lemma prover_simps: "prover [] = True" "prover (h # t) = prover (solve h @ all solve t)"
unfolding prover_def
by (metis repeat.simps(1),metis repeat.simps(2) repeat_once list.map flatten.simps all_def)

lemma append_simps: "[] @ l = l" "(h # t) @ l = h # t @ l"
by (rule append.simps(1),rule append.simps(2))

lemma map_simps: "map f [] = []" "map f (h # t) = f h # map f t"
by (rule list.map(1),rule list.map(2))

lemma if_simps: "(if True then x else y) = x" "(if False then x else y) = y"
by (rule if_True,rule if_False)

lemma not_simps: "(\<not> True) = False" "(\<not> False) = True" "(\<not> \<not> b) = b"
by (rule simp_thms,rule simp_thms,rule nnf_simps)

lemma prod_simps: "fst z = (case z of (x,_) \<Rightarrow> x)" "snd z = (case z of (_,y) \<Rightarrow> y)"
by (rule fst_def,rule snd_def)

lemma case_nnf:
"(case Pre b i v of Pre b' i' v' \<Rightarrow> f b' i' v' |
  Con p' q' \<Rightarrow> f' p' q' | Dis p'' q'' \<Rightarrow> f'' p'' q'' |
  Uni p''' \<Rightarrow> f''' p''' | Exi p'''' \<Rightarrow> f'''' p'''') = (f b i v)"
"(case Con p q of Pre b' i' v' \<Rightarrow> f b' i' v' |
  Con p' q' \<Rightarrow> f' p' q' | Dis p'' q'' \<Rightarrow> f'' p'' q'' |
  Uni p''' \<Rightarrow> f''' p''' | Exi p'''' \<Rightarrow> f'''' p'''') = (f' p q)"
"(case Dis p q of Pre b' i' v' \<Rightarrow> f b' i' v' |
  Con p' q' \<Rightarrow> f' p' q' | Dis p'' q'' \<Rightarrow> f'' p'' q'' |
  Uni p''' \<Rightarrow> f''' p''' | Exi p'''' \<Rightarrow> f'''' p'''') = (f'' p q)"
"(case Uni p of Pre b' i' v' \<Rightarrow> f b' i' v' |
  Con p' q' \<Rightarrow> f' p' q' | Dis p'' q'' \<Rightarrow> f'' p'' q'' |
  Uni p''' \<Rightarrow> f''' p''' | Exi p'''' \<Rightarrow> f'''' p'''') = (f''' p)"
"(case Exi p of Pre b' i' v' \<Rightarrow> f b' i' v' |
  Con p' q' \<Rightarrow> f' p' q' | Dis p'' q'' \<Rightarrow> f'' p'' q'' |
  Uni p''' \<Rightarrow> f''' p''' | Exi p'''' \<Rightarrow> f'''' p'''') = (f'''' p)"
by (rule nnf.case(1),rule nnf.case(2),rule nnf.case(3),rule nnf.case(4),rule nnf.case(5))

lemma case_nat:
"(case 0 of 0 \<Rightarrow> x | Suc n' \<Rightarrow> f n') = x"
"(case Suc n of 0 \<Rightarrow> x | Suc n' \<Rightarrow> f n') = (f n)"
by (rule nat.case(1),rule nat.case(2))

lemma case_prod:
"(case (x,y) of (x',y') \<Rightarrow> f x' y') = (f x y)"
by (rule prod.case(1))

lemma case_list:
"(case [] of [] \<Rightarrow> x | h' # t' \<Rightarrow> f h' t') = x"
"(case h # t of [] \<Rightarrow> x | h' # t' \<Rightarrow> f h' t') = (f h t)"
by (rule list.case(1),rule list.case(2))

lemma reflexivity: "(x = x) = True"
by (rule simp_thms)

lemma inject_simps: "(True \<and> P) = P" "(False \<and> P) = False"
by (rule simp_thms,rule simp_thms)

lemmas simps = prover_simps solve_def all_def fresh_def bind_def
  append_simps map_simps if_simps not_simps prod_simps
  member.simps flatten.simps null.simps maxl.simps maxn.simps subst.simps fv.simps adjust.simps
  case_nnf case_nat case_prod case_list reflexivity
  nnf.inject list.inject char.inject inject_simps
  nnf.distinct list.distinct nibble.distinct

proposition "check test"
unfolding check_def test_def
by (simp only: simps(1-321))

section "Basics"

lemma mmm[simp]: "(maxn n n') = (max n n')"
by (induct n arbitrary: n') (simp_all add: Nitpick.case_nat_unfold max_Suc1)

lemma all: "all f = (flatten \<circ> map f)" using all_def comp_apply by fastforce

definition make_sequent :: "nnf list \<Rightarrow> sequent" where
  "make_sequent l = map (\<lambda>p. (0,p)) l"

definition list_sequent :: "sequent \<Rightarrow> nnf list" where
  "list_sequent s = map snd s"

definition fv_list :: "nnf list \<Rightarrow> nat list" where
  "fv_list \<equiv> all fv"

primrec is_axiom :: "nnf list \<Rightarrow> bool" where
  "is_axiom [] = False"
| "is_axiom (p # t) = ((\<exists>b i v. p = Pre b i v \<and> Pre (\<not> b) i v \<in> set t))"

lemma member_set[simp]: "member a l = (a \<in> set l)" by (induct l) auto

lemma pre:  "(n,(m,Pre b i v) # xs) \<in> calculation(nfs) \<Longrightarrow> \<not> is_axiom (list_sequent ((m,Pre b i v) # xs)) \<Longrightarrow> (Suc n,xs@[(0,Pre b i v)]) \<in> calculation(nfs)"
  and con1: "(n,(m,Con p q) # xs) \<in> calculation(nfs) \<Longrightarrow> \<not> is_axiom (list_sequent ((m,Con p q) # xs)) \<Longrightarrow> (Suc n,xs@[(0,p)]) \<in> calculation(nfs)"
  and con2: "(n,(m,Con p q) # xs) \<in> calculation(nfs) \<Longrightarrow> \<not> is_axiom (list_sequent ((m,Con p q) # xs)) \<Longrightarrow> (Suc n,xs@[(0,q)]) \<in> calculation(nfs)"
  and dis:  "(n,(m,Dis p q) # xs) \<in> calculation(nfs) \<Longrightarrow> \<not> is_axiom (list_sequent ((m,Dis p q) # xs)) \<Longrightarrow> (Suc n,xs@[(0,p),(0,q)]) \<in> calculation(nfs)"
  and uni:  "(n,(m,Uni p) # xs) \<in> calculation(nfs) \<Longrightarrow> \<not> is_axiom (list_sequent ((m,Uni p) # xs)) \<Longrightarrow> (Suc n,xs@[(0,bind p (fresh ((flatten \<circ> map fv) (list_sequent ((m,Uni p) # xs)))))]) \<in> calculation(nfs)"
  and exi:  "(n,(m,Exi p) # xs) \<in> calculation(nfs) \<Longrightarrow> \<not> is_axiom (list_sequent ((m,Exi p) # xs)) \<Longrightarrow> (Suc n,xs@[(0,bind p m),(Suc m,Exi p)]) \<in> calculation(nfs)"
  by (auto simp: solve_def list_sequent_def all)

lemmas not_is_axiom_subs = pre con1 con2 dis uni exi

lemma calculation_init[simp]: "(0,k) \<in> calculation s = (k = s)"
  using calculation.cases by blast

lemma calculation_upwards:
  assumes "(n,k) \<in> calculation s" and "\<not> is_axiom (list_sequent (k))"
  shows "(\<exists>l. (Suc n,l) \<in> calculation s \<and> l \<in> set (solve k))"
  proof (cases k)
    case Nil then show ?thesis using assms(1) solve_def by auto
  next
    case (Cons a _) then show ?thesis
    proof (cases a)
      case (Pair _ p) then show ?thesis
        using Cons assms by (cases p) (fastforce simp: list_sequent_def solve_def)+
    qed
  qed

lemma calculation_downwards: "(Suc n,k) \<in> calculation s \<Longrightarrow> \<exists>t. (n,t) \<in> calculation s \<and> k \<in> set (solve t) \<and> \<not> is_axiom (list_sequent t)"
  proof (erule calculation.cases)
    assume "Suc n = 0"
    then show ?thesis using list_sequent_def by simp
  next
    fix m l k'
    assume 1: "Suc n = Suc m"
    and 2: "k = k'"
    and 3: "(m,l) \<in> calculation s"
    and 4: "k' \<in> set (solve l)"
    then show ?thesis proof (cases l)
      case Nil then show ?thesis using 1 2 3 4 list_sequent_def by fastforce
    next
      case (Cons a _) then show ?thesis proof (cases a)
        case (Pair _ p) then show ?thesis
          using 1 2 3 4 Cons solve_def list_sequent_def by (cases p) auto
      qed
    qed
  qed
 
lemma calculation_calculation_child[rule_format]:
  shows "\<forall>s t. (Suc n,s) \<in> calculation t = (\<exists>k. k \<in> set (solve t) \<and> \<not> is_axiom (list_sequent t) \<and> (n,s) \<in> calculation k)"
  using calculation_downwards by (induct n) (fastforce,blast)

lemma calculation_progress:
  assumes "(n,a # l) \<in> calculation s" and "\<not> is_axiom (list_sequent (a # l))"
  shows "(\<exists>k. (Suc n,l@k) \<in> calculation s)"
  proof (cases a)
    case (Pair _ p) then show ?thesis
      using assms by (cases p) (auto dest: not_is_axiom_subs)
  qed

definition inc :: "nat \<times> sequent \<Rightarrow> nat \<times> sequent" where
  "inc \<equiv> \<lambda>(n,fs). (Suc n,fs)"

lemma inj_inc: "inj inc"
  by (simp add: inc_def inj_on_def)

lemma calculation: "calculation s = insert (0,s) (inc ` (\<Union> (calculation ` {k. \<not> is_axiom (list_sequent s) \<and> k \<in> set (solve s)})))"
  proof (rule set_eqI,simp add: split_paired_all)
    fix n k
    show "((n,k) \<in> calculation s) =
           (n = 0 \<and> k = s \<or> (n,k) \<in> inc ` (\<Union>x\<in>{k. \<not> is_axiom (list_sequent s) \<and> k \<in> set (solve s)}. calculation x))"
    by (cases n) (auto simp: calculation_calculation_child inc_def)
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
        using assms by blast
    qed
  qed
 
lemma is_axiom_finite_calculation: "is_axiom (list_sequent s) \<Longrightarrow> finite (calculation s)"
  by (simp add: calculation_is_axiom)

primrec failing_path :: "(nat \<times> sequent) set \<Rightarrow> nat \<Rightarrow> (nat \<times> sequent)" where
  "failing_path ns 0 = (SOME x. x \<in> ns \<and> fst x = 0 \<and> infinite (calculation (snd x)) \<and> \<not> is_axiom (list_sequent (snd x)))"
| "failing_path ns (Suc n) = (let fn = failing_path ns n in 
  (SOME fsucn. fsucn \<in> ns \<and> fst fsucn = Suc n \<and> (snd fsucn) \<in> set (solve (snd fn)) \<and> infinite (calculation (snd fsucn)) \<and> \<not> is_axiom (list_sequent (snd fsucn))))"

lemma f0:
  assumes "f = failing_path (calculation s)"
  and "infinite (calculation s)"
  shows "f 0 \<in> (calculation s) \<and> fst (f 0) = 0 \<and> infinite (calculation (snd (f 0))) \<and> \<not> is_axiom (list_sequent (snd (f 0)))"
  using assms by simp (metis (mono_tags,lifting) calculation.init is_axiom_finite_calculation fst_conv snd_conv someI_ex)

lemma infinite_union: "finite Y \<Longrightarrow> infinite (Union (f ` Y)) \<Longrightarrow> \<exists>y. y \<in> Y \<and> infinite (f y)"
  by auto

lemma finite_subs: "finite {w. \<not> is_axiom (list_sequent y) \<and> w \<in> set (solve y)}"
  by simp

lemma fSuc:
  assumes "f = failing_path (calculation s)"
  and "f n \<in> calculation s \<and> fst (f n) = n \<and> infinite (calculation (snd (f n))) \<and> \<not> is_axiom (list_sequent (snd (f n)))"
  shows "f (Suc n) \<in> calculation s \<and> fst (f (Suc n)) = Suc n \<and> (snd (f (Suc n))) \<in> set (solve (snd (f n))) \<and> infinite (calculation (snd (f (Suc n)))) \<and> \<not> is_axiom (list_sequent (snd (f (Suc n))))"
  proof -
    fix g Y
    have "infinite (\<Union> (calculation ` {w. \<not> is_axiom (list_sequent (snd (f n))) \<and> w \<in> set (solve (snd (f n)))}))"
      using assms by (metis (mono_tags,lifting) Collect_cong calculation finite.insertI finite_imageI)
    then show ?thesis using assms calculation.step is_axiom_finite_calculation
      by simp (rule someI_ex,simp,metis prod.collapse)
 qed

lemma is_path_f_0: "infinite (calculation s) \<Longrightarrow> failing_path (calculation s) 0 = (0,s)"
  using calculation_init f0 prod.collapse by metis

lemma is_path_f':
  assumes "f = failing_path (calculation s)"
  and "infinite (calculation s)"
  shows "f n \<in> calculation s \<and> fst (f n) = n \<and> infinite (calculation (snd (f n))) \<and> \<not> is_axiom (list_sequent (snd (f n)))"
  using assms f0 fSuc by (induct n) simp_all

lemma is_path_f:
  assumes "f = failing_path (calculation s)"
  and "infinite (calculation s)"
  shows "\<forall>n. f n \<in> calculation s \<and> fst (f n) = n \<and> (snd (f (Suc n))) \<in> set (solve (snd (f n))) \<and> infinite (calculation (snd (f n)))"
  using assms is_path_f' fSuc by simp

lemma adjust: "Suc n \<in> set l = (n \<in> set (adjust l))"
  proof (induct l)
    case Nil then show ?case by simp
  next
    case (Cons m _) then show ?case by (cases m) simp_all
  qed

lemma eval_cong: "\<forall>x. x \<in> set (fv p) \<longrightarrow> e x = e' x \<Longrightarrow> semantics m e p = semantics m e' p"
  proof (induct p arbitrary: e e')
    case Pre then show ?case using map_cong fv.simps(1) semantics.simps(1) by metis
  next
    case Con then show ?case using Un_iff fv.simps(2) semantics.simps(2) set_append by metis
  next
    case Dis then show ?case using Un_iff fv.simps(3) semantics.simps(3) set_append by metis
  next
    case Uni then show ?case
      using Nitpick.case_nat_unfold adjust not_gr0 Suc_pred' fv.simps(4) semantics.simps(4)
      by (metis (no_types,lifting))
  next
    case Exi then show ?case
      using Nitpick.case_nat_unfold adjust not_gr0 Suc_pred' fv.simps(5) semantics.simps(5)
      by (metis (no_types,lifting))
  qed

lemma semantics_alternative_def2: "semantics_alternative m e s = (\<exists>p. p \<in> set s \<and> semantics m e p)"
  by (induct s) auto

lemma semantics_alternative_append: "semantics_alternative m e (s @ s') = ((semantics_alternative m e s) \<or> (semantics_alternative m e s'))"
  by (induct s) auto

lemma fv_list_cons: "fv_list (a # list) = (fv a) @ (fv_list list)"
  by (simp add: fv_list_def all)

lemma semantics_alternative_cong: "(\<forall>x. x \<in> set (fv_list s) \<longrightarrow> e x = e' x) \<longrightarrow> semantics_alternative m e s = semantics_alternative m e' s" 
  by (induct s) (simp_all,metis eval_cong Un_iff set_append fv_list_cons)

section "Soundness"

lemma ball: "\<forall>x \<in> m. P x = Q x \<Longrightarrow> (\<forall>x \<in> m. P x) = (\<forall>x \<in> m. Q x) \<and> (\<exists>x \<in> m. P x) = (\<exists>x \<in> m. Q x)"
  by simp

lemma eval_subst: "semantics m e (subst f p) = semantics m (e \<circ> f) p"
  using eval_cong by (induct p arbitrary: e f) (simp_all add: Nitpick.case_nat_unfold ball)

lemma eval_bind: "semantics m e (bind p n) = semantics m (case_nat (e n) e) p"
  using eval_cong eval_subst unfolding bind_def by (simp add: Nitpick.case_nat_unfold)

lemma sound_Uni:
  assumes "u \<notin> set (fv_list (Uni p # s))"
  and "valid (s@[bind p u])"
  shows "valid (Uni p # s)"
  proof (clarsimp simp: valid_def)
    fix M I e z
    show "is_model_environment (M,I) e \<Longrightarrow> \<not> semantics_alternative (M,I) e s \<Longrightarrow> z \<in> M \<Longrightarrow> semantics (M,I) (case_nat z e) p"
    proof -
      assume "z \<in> M" and "\<not> semantics_alternative (M,I) e s" and  "is_model_environment (M,I) e"
      have 1: "semantics (M,I) (case_nat z (e(u:=z))) p = semantics (M,I) (case_nat z e) p"
        using assms
        by (clarsimp simp: Nitpick.case_nat_unfold fv_list_cons intro!: eval_cong[rule_format])
           (metis One_nat_def Suc_pred' adjust)
      have "is_model_environment (M,I) (e(u := z)) \<longrightarrow> semantics_alternative (M,I) (e(u := z)) (s @ [bind p u])"
        using assms valid_def by blast
      then have 2: "(\<forall>n. (if n = u then z else e n) \<in> M) \<longrightarrow> semantics_alternative (M,I) (e(u := z)) s \<or> semantics (M,I) (case_nat z e) p"
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
  
lemma sound_Exi: "valid (s@[bind p u,Exi p]) \<Longrightarrow> valid (Exi p # s)"
  by (simp add: valid_def semantics_alternative_append eval_bind)
     (metis is_model_environment_def prod.sel(1))

lemma max_exists: "finite (X::nat set) \<Longrightarrow> X \<noteq> {} \<longrightarrow> (\<exists>x. x \<in> X \<and> (\<forall>y. y \<in> X \<longrightarrow> y \<le> x))"
  using Max.coboundedI Max_in by blast

definition init :: "sequent \<Rightarrow> bool" where
  "init s == \<forall>x \<in> (set s). fst x = 0"

definition is_Exi :: "nnf \<Rightarrow> bool" where
  "is_Exi f \<equiv> case f of Exi _ \<Rightarrow> True | _ \<Rightarrow> False"

lemma is_Exi: "\<not> is_Exi (Pre b i v) \<and> \<not> is_Exi (Con p q) \<and> \<not> is_Exi (Dis p q) \<and> \<not> is_Exi (Uni p)"
  using is_Exi_def by simp

lemma index0:
  assumes "init s"
  shows "\<forall>k m p. (n,k) \<in> calculation s \<longrightarrow> (m,p) \<in> (set k) \<longrightarrow> \<not> is_Exi p \<longrightarrow> m = 0"
  proof (induct n)
    case 0 then show ?case using assms init_def by fastforce
  next
    case IH: (Suc x) then show ?case proof (intro allI impI)
      fix k m p
      show "(Suc x,k) \<in> calculation s \<Longrightarrow> (m,p) \<in> (set k) \<Longrightarrow> \<not> is_Exi p \<Longrightarrow> m = 0"
      proof -
        assume "(Suc x,k) \<in> calculation s" and 1: "(m,p) \<in> (set k)" and 2: "\<not> is_Exi p"
        then obtain t where 3: "(x,t) \<in> calculation s \<and> k \<in> set (solve t) \<and> \<not> is_axiom (list_sequent t)"
          using calculation_downwards by blast
        then show ?thesis proof (cases t)
          case Nil then show ?thesis using assms IH 1 3 solve_def by simp
        next
          case (Cons a _) then show ?thesis proof (cases a)
            case (Pair _ q) then show ?thesis using 1 2 3 IH Cons
              by (cases q) (fastforce simp: solve_def list_sequent_def is_Exi_def)+
          qed
        qed
      qed
    qed
  qed

lemma maxl: "\<forall>v \<in> set l. v \<le> maxl l"
  by (induct l) (auto simp: max_def)

lemma fresh: "fresh l \<notin> (set l)"
  using maxl fresh_def by (auto,metis null.simps(2) empty_iff list.exhaust list.set(1),force)

lemma soundness':
  assumes "init s"
  and "m \<in> (fst ` (calculation s))"
  and "\<forall>y u. (y,u) \<in> (calculation s) \<longrightarrow> y \<le> m"
  shows "\<forall>n t. h = m - n \<and> (n,t) \<in> calculation s \<longrightarrow> valid (list_sequent t)"
  proof (induct h)
    case 0 then show ?case proof (intro allI impI)
      fix n t
      show "0 = m - n \<and> (n,t) \<in> calculation s \<Longrightarrow> valid (list_sequent t)"
      proof -
        assume *: "0 = m - n \<and> (n,t) \<in> calculation s"
        then show ?thesis proof (cases "is_axiom (list_sequent t)")
          case True then show ?thesis proof (cases t)
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
    case IH: (Suc x) then show ?case proof (intro allI impI)
      fix n t
      show "Suc x = m - n \<and> (n,t) \<in> calculation s \<Longrightarrow> valid (list_sequent t)"
      proof -
        assume "Suc x = m - n \<and> (n,t) \<in> calculation s"
        then have *: "Suc x = m - n" and **: "(n,t) \<in> calculation s"
          by (simp,simp)
        then show ?thesis proof (cases "is_axiom (list_sequent t)")
          case True then show ?thesis proof (cases t)
            case Nil then show ?thesis using True list_sequent_def by simp
          next
            case Cons then show ?thesis using True list_sequent_def valid_def semantics_alternative_def2
              by simp (metis (no_types,lifting) semantics.simps(1))
          qed
        next
          case notAxiom: False then show ?thesis proof (cases "\<exists>a f list. t = (a,Uni f) # list")
            case True
            then obtain a and f and list where 1: "t = (a,Uni f) # list" by blast
            then show ?thesis using IH assms * ** solve_def fv_list_def fresh list_sequent_def
              by simp (frule calculation.step,simp add: all,
                 metis (no_types,lifting) Suc_leD diff_Suc_Suc diff_diff_cancel diff_le_self
                  le_SucI list.map map_append snd_conv sound_Uni)
          next
            case notUni: False then show ?thesis proof (cases "\<exists>a f list. t = (a,Exi f) # list")
              case True
              then obtain a and f and list where 1: "t = (a,Exi f) # list" by blast
              then show ?thesis using IH assms * ** solve_def fresh list_sequent_def
                by simp (frule calculation.step,simp,
                   metis (no_types,lifting) Suc_leD diff_Suc_Suc diff_diff_cancel diff_le_self
                    le_SucI list.map map_append snd_conv sound_Exi)
            next
              case notExi: False
              then show ?thesis proof (cases t)
                case Nil
                then show ?thesis using assms notAxiom IH * ** calculation_upwards split_list_first solve_def
                  using list.simps(4) by (metis (no_types,lifting) Suc_diff_Suc Suc_leD Un_iff append_Nil2 diff_diff_cancel
                       diff_le_self insert_iff le_simps(3) list.set set_append)
              next
                case (Cons a list)
                then show ?thesis using IH proof (simp add: valid_def semantics_alternative_def2,intro allI impI)
                  fix as gs g
                  show "\<forall>n t. x = m - n \<and> (n,t) \<in> calculation s \<longrightarrow>
                       (\<forall>a b e. is_model_environment (a,b) e \<longrightarrow> (\<exists>p. p \<in> set (list_sequent t) \<and> semantics (a,b) e p))
                       \<Longrightarrow> is_model_environment (as,gs) g \<Longrightarrow> \<exists>p. p \<in> set (list_sequent (a # list)) \<and> semantics (as,gs) g p"
                   proof -
                    assume ***: "is_model_environment (as,gs) g"
                    and IH': "\<forall>n t. x = m - n \<and> (n,t) \<in> calculation s \<longrightarrow> (\<forall>a b e. is_model_environment (a,b) e \<longrightarrow>
                             (\<exists>p. p \<in> set (list_sequent t) \<and> semantics (a,b) e p))"
                    then show ?thesis proof (cases a)
                      case (Pair _ p) then show ?thesis proof (cases p)
                        case (Pre b i v) then  show ?thesis
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
                          then show ?thesis using 5 proof (elim impE)
                            show "(Suc n,list @ [(0,q)]) \<in> calculation s"
                              using 1 by simp
                         next
                            show "\<forall>a b e. is_model_environment (a,b) e \<longrightarrow>
                                  (\<exists>p. p \<in> set (list_sequent (list @ [(0,q)])) \<and> semantics (a,b) e p) \<Longrightarrow>
                                  x = m - Suc n \<and> (Suc n,list @ [(0,r)]) \<in> calculation s"
                              using 2 3 by blast
                         next
                            show "\<forall>a b e. is_model_environment (a,b) e \<longrightarrow>
                                  (\<exists>p. p \<in> set (list_sequent (list @ [(0,r)])) \<and> semantics (a,b) e p) \<Longrightarrow>
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
                                  (\<exists>p. p \<in> set (list_sequent (list @ [(0,q),(0,r)])) \<and> semantics (a,b) e p))"
                                  using * IH' by blast
                        then show ?thesis proof (elim impE)
                          have 1: "(Suc n,list @ [(0,q),(0,r)]) \<in> calculation s"
                            using ** Dis Pair dis local.Cons notAxiom by blast
                          have "x = m - Suc n" using "*" by linarith
                          then show "x = m - Suc n \<and> (Suc n,list @ [(0,q),(0,r)]) \<in> calculation s"
                            using 1 by simp
                        next
                          show "\<forall>a b e. is_model_environment (a,b) e \<longrightarrow>
                               (\<exists>p. p \<in> set (list_sequent (list @ [(0,q),(0,r)])) \<and> semantics (a,b) e p) \<Longrightarrow>
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

lemma list_make_sequent_inverse[simp]: "list_sequent (make_sequent s) = s"
  using list_sequent_def make_sequent_def by (induct s) simp_all

lemma soundness:
  assumes "finite (calculation (make_sequent s))"
  shows "valid s"
  proof -
    have "init (make_sequent s)" and "finite (fst ` (calculation (make_sequent s)))"
      using assms by (simp add: init_def make_sequent_def,simp)
    then show ?thesis using assms calculation.init soundness' list_make_sequent_inverse max_exists
      by (metis (mono_tags,lifting) empty_iff fst_conv image_eqI)
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
    obtain suc: "(snd (f (Suc n))) \<in> set (solve (snd (f n)))"
      using assms is_path_f by blast
    then show ?thesis proof (cases a)
      case (Pair _ p)
      then show ?thesis using suc solve_def
        by (induct p,safe,simp_all split: if_splits) blast
  qed
qed

lemma contains_considers':
  assumes "f = failing_path (calculation s)"
  and "infinite (calculation s)"
  shows "\<forall>n y ys. snd (f n) = xs@y # ys \<longrightarrow> (\<exists>m zs'. snd (f (n+m)) = y # zs')"
  proof (induct xs)
    case Nil then show ?case by simp (metis Nat.add_0_right)
  next
    case Cons then show ?case
      by (metis (no_types,lifting) add_Suc_shift append.simps(2) append_assoc assms progress)
  qed

lemma contains_considers:
  assumes "f = failing_path (calculation s)"
  and "infinite (calculation s)"
  and "contains f n y"
  shows "(\<exists>m. considers f (n+m) y)"
  using assms 
  by (clarsimp simp: contains_def considers_def dest!: split_list_first)
     (frule contains_considers'[rule_format],simp,simp,metis (mono_tags,lifting) list.simps(5))

lemma contains_propagates_Pre[rule_format]:
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
    then obtain ys and zs where 1: "snd (f (n + q')) = ys @ (0,Pre b i v) # zs \<and> (0,Pre b i v) \<notin> set ys"
      by blast
    then have 2: "(snd (f (Suc (n + q')))) \<in> set (solve (snd (f (n + q'))))"
      using assms is_path_f by blast
    then show ?case proof (cases ys)
      case Nil
      then show ?thesis using 1 2 contains_def solve_def
        by (simp split: if_splits)
    next
      case (Cons a _) then show ?thesis proof (cases a)
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
    then show ?thesis proof (cases "snd (f (n + l))")
      case Nil then show ?thesis using 1 considers_def by simp
    next
      case Cons then show ?thesis using 1 2 considers_def contains_def solve_def
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
    then show ?thesis proof (cases "snd (f (n + l))")
      case Nil then show ?thesis using 1 considers_def by simp
    next
      case Cons then show ?thesis using 1 2 considers_def contains_def solve_def
        by (rule_tac x="Suc l" in exI) simp_all
    qed
  qed

lemma contains_propagates_Uni:
  assumes "f = failing_path (calculation s)"
  and "infinite (calculation s)"
  and "contains f n (0,Uni p)"
  shows "(\<exists>y. contains f (Suc(n+y)) (0,bind p (fresh (fv_list (map snd (snd (f (n+y))))))))"
  proof -
    have "(\<exists>l. considers f (n+l) (0,Uni p))" using assms contains_considers by blast
    then obtain l where 1: "considers f (n+l) (0,Uni p)" by blast
    then have 2: "(snd (f (Suc (n + l)))) \<in> set (solve (snd (f (n + l))))"
      using assms is_path_f by blast
    then show ?thesis proof (cases "snd (f (n + l))")
      case Nil then show ?thesis using 1 considers_def by simp
    next
      case Cons then show ?thesis using 1 2 considers_def contains_def solve_def
        by (rule_tac x="l" in exI) (simp add: fv_list_def all_def)
    qed
  qed

lemma contains_propagates_Exi:
  assumes "f = failing_path (calculation s)"
  and "infinite (calculation s)"
  and "contains f n (m,Exi p)"
  shows "(\<exists>y. (contains f (n+y) (0,bind p m)) \<and> (contains f (n+y) (Suc m,Exi p)))"
  proof -
    have "(\<exists>l. considers f (n+l) (m,Exi p))" using assms contains_considers by blast
    then obtain l where 1: "considers f (n+l) (m,Exi p)" by blast
    then have 2: "(snd (f (Suc (n + l)))) \<in> set (solve (snd (f (n + l))))"
      using assms is_path_f by blast
    then show ?thesis proof (cases "snd (f (n + l))")
      case Nil then show ?thesis using 1 considers_def by simp
    next
      case Cons then show ?thesis using 1 2 considers_def contains_def solve_def
        by (rule_tac x="Suc l" in exI) simp
    qed
  qed

lemma Exi_downward:
  assumes "f = failing_path (calculation s)"
  and "infinite (calculation s)"
  and "init s"
  shows "\<forall>m. (Suc m,Exi g) \<in> set (snd (f n)) \<longrightarrow> (\<exists>n'. (m,Exi g) \<in> set (snd (f n')))"
  proof -
    show ?thesis proof (induct n)
      case 0 then show ?case using assms init_def is_path_f_0 by fastforce
    next
      case IH: (Suc x)
      then have fxSuc: "f x \<in> calculation s \<and> fst (f x) = x \<and> snd (f (Suc x)) \<in> set (solve (snd (f x))) \<and> infinite (calculation (snd (f x)))"
        using assms is_path_f by blast
      then show ?case proof (cases "f x")
        case fxPair: (Pair _ l)
        then show ?thesis proof (cases l)
          case Nil then show ?thesis using fxSuc fxPair solve_def by simp
        next
          case (Cons a _) then show ?thesis proof (cases a)
            case (Pair _ p) then show ?thesis proof (cases p)
              case Pre then show ?thesis using IH fxSuc fxPair Cons Pair solve_def
                by (simp split: if_splits)
            next
              case Con then show ?thesis using IH fxSuc fxPair Cons Pair solve_def
                by (simp split: if_splits) fastforce
            next
              case Dis then show ?thesis using IH fxSuc fxPair Cons Pair solve_def
                by (simp split: if_splits)
            next
              case Uni then show ?thesis using IH fxSuc fxPair Cons Pair solve_def
                by (simp split: if_splits)
            next
              case Exi then show ?thesis using IH fxSuc fxPair Cons Pair solve_def
                by (simp split: if_splits) (metis list.set_intros(1) snd_eqD)
            qed
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
  using assms Exi_downward contains_def by (induct m) (simp,blast)
     
lemma Exi_upward':
  assumes "f = failing_path (calculation s)"
  and "infinite (calculation s)"
  and "init s"
  shows "\<forall>n. contains f n (0,Exi g) \<longrightarrow> (\<exists>n'. contains f n' (m,Exi g))"
  using assms contains_propagates_Exi by (induct m) (simp,blast)

lemma Exi_upward:
  assumes "f = failing_path (calculation s)"
  and "infinite (calculation s)"
  and "init s"
  and "contains f n (m,Exi g)"
  shows "(\<forall>m'. \<exists>n'. contains f n' (0,bind g m'))"
  proof -
    fix m'
    have "\<exists>n'. contains f n' (m',Exi g)" using assms Exi0 Exi_upward' by metis
    then show ?thesis using assms contains_propagates_Exi Exi0 Exi_upward' by metis
  qed

definition ntou :: "nat \<Rightarrow> proxy" where "ntou n \<equiv> replicate n ()"

definition uton :: "proxy \<Rightarrow> nat" where "uton u \<equiv> length u"

lemma aaa[simp]: "ntou (uton u) = u" using ntou_def uton_def by (induct u) auto

lemma bbb[simp]: "uton (ntou n) = n" using ntou_def uton_def by (induct n) auto

lemma ccc[simp]: "uton \<circ> ntou = id" by auto

section "Falsifying Model From Failing Path"

definition model :: "sequent \<Rightarrow> model" where
  "model s \<equiv> (range ntou,\<lambda> p ms. (let f = failing_path (calculation s) in (\<forall>n m. \<not> contains f n (m,Pre True p (map uton ms)))))"

lemma is_env_model_ntou: "is_model_environment (model s) ntou"
  using is_model_environment_def model_def by simp

lemma not_is_Exi:
  assumes "f = failing_path (calculation s)"
  and "infinite (calculation s)"
  and "init s"
  and "(contains f n (m,p))"
  shows "\<not> is_Exi p \<Longrightarrow> m = 0"
  using assms contains_def index0 is_path_f' prod.collapse by metis

lemma size_subst[simp]: "size (subst f p) = size p"
  by (induct p arbitrary: f) simp_all

lemma size_bind[simp]: "size (bind p n) = size p"
  using bind_def by simp

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
      assume *: "\<forall>m<n. \<forall>p. size p = m \<longrightarrow> (\<forall>m n. contains f n (m,p) \<longrightarrow> \<not> semantics (model s) ntou p)"
      show ?thesis proof (cases p)
        case (Pre b i v) then show ?thesis proof (cases b)
          case True then show ?thesis using Pre assms model_def by auto
        next
          case False then show ?thesis using Pre proof (clarsimp simp: model_def)
          fix na m nb ma
          show "n = 0 \<Longrightarrow> contains f na (m,Pre False i v) \<Longrightarrow> contains (failing_path (calculation s)) nb (ma,Pre True i v) \<Longrightarrow> False"
          proof -
            assume 1: "contains f na (m,Pre False i v)" and 2: "contains (failing_path (calculation s)) nb (ma,Pre True i v)"
            then have 3: "m = 0 \<and> ma = 0"
              using assms is_Exi not_is_Exi by simp
            then have "\<exists>y. considers (failing_path (calculation s)) (nb+na+y) (0,Pre True i v)"
              using assms 2 contains_considers contains_propagates_Pre by simp
            then obtain y where 4: "considers (failing_path (calculation s)) (nb+na+y) (0,Pre True i v)"
              by blast
            then have 5: "contains (failing_path (calculation s)) (na+nb+y) (0,Pre False i v)"
              using assms 1 3 contains_propagates_Pre by simp
            then have 6: "nb+na=na+nb"
              by simp
            then have "is_axiom (list_sequent (snd ((failing_path (calculation s)) (na+nb+y))))"
              proof (cases "snd ((failing_path (calculation s)) (na + nb + y))")
                case Nil then show ?thesis
                  using 5 contains_def by simp
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
          by (metis Nat.add_0_right add_Suc_right nnf.size(7) less_add_Suc1 less_add_Suc2 semantics.simps(2))
      next
        case Dis then show ?thesis using assms * contains_propagates_Dis is_Exi not_is_Exi
          by (metis Nat.add_0_right add_Suc_right nnf.size(8) less_add_Suc1 less_add_Suc2 semantics.simps(3))
      next
        case (Uni q) then show ?thesis proof (intro impI allI)
          fix na m
          show "size p = n \<Longrightarrow> contains f na (m,p) \<Longrightarrow> \<not> semantics (model s) ntou p"
          proof -
            assume 1: "size p = n" and 2: "contains f na (m,p)"
            then have "m = 0" using assms Uni is_Exi not_is_Exi by simp
            then have "\<exists>y. contains f (Suc (na + y)) (0,bind q (fresh (fv_list (map snd (snd (f (na + y)))))))"
              using assms Uni 2 contains_propagates_Uni by simp
            then obtain y where 3: "contains f (Suc (na + y)) (0,bind q (fresh (fv_list (map snd (snd (f (na + y)))))))"
              by blast
            have 4: "Suc (size q) = n" using Uni 1 by simp
            then show ?thesis using Uni proof (simp)
              show "\<exists>z\<in>fst (model s). \<not> semantics (model s) (case_nat z ntou) q"
              proof (rule_tac x="ntou (fresh (fv_list (map snd (snd (f (na + y))))))" in bexI)
                show "\<not> semantics (model s) (case_nat (ntou (fresh (fv_list (map snd (snd (f (na + y))))))) ntou) q"
                  using * 3 4 eval_bind size_bind lessI by metis
              next
                show "ntou (fresh (fv_list (map snd (snd (f (na + y)))))) \<in> fst (model s)"
                  using is_env_model_ntou is_model_environment_def by blast
              qed
            qed
          qed
        qed
      next
        case (Exi q) then show ?thesis proof (clarsimp)
          fix m na ma z
          show "p = Exi q \<Longrightarrow> n = Suc (size q) \<Longrightarrow> z \<in> fst (model s) \<Longrightarrow> contains f na (m,Exi q)
                \<Longrightarrow> semantics (model s) (case_nat z ntou) q \<Longrightarrow> False"
          proof -
            assume "n = Suc (size q)" and "contains f na (m,Exi q)"
            and 1: "semantics (model s) (case_nat z ntou) q"
            then have "\<forall>m'. \<not> semantics (model s) ntou (bind q m')"
              using assms * by (meson Exi_upward eval_cong id_apply lessI size_bind)
            also have "\<forall>u. ntou (uton u) = u" by simp
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
  using assms model' by simp

section "Completeness"

lemma completeness': "infinite (calculation s) \<Longrightarrow> init s \<Longrightarrow> \<forall>mA \<in> set s. \<not> semantics (model s) ntou (snd mA)"
  by (metis contains_def eq_snd_iff is_path_f_0 model)

lemma completeness'': "infinite (calculation (make_sequent s)) \<Longrightarrow> init (make_sequent s) \<Longrightarrow> \<forall>p. p \<in> set s \<longrightarrow> \<not> semantics (model (make_sequent s)) ntou p"
  using completeness' make_sequent_def by fastforce

lemma completeness: "infinite (calculation (make_sequent s)) \<Longrightarrow> \<not> valid s"
  using valid_def init_def make_sequent_def is_env_model_ntou semantics_alternative_def2 completeness''
  by (subgoal_tac "init (make_sequent s)") (metis,simp)

section "Algorithm"

definition loop :: "sequent list \<Rightarrow> nat \<Rightarrow> sequent list" where
  "loop s n \<equiv> repeat (flatten \<circ> map solve) s n"

lemma loop_upwards: "loop s n = [] \<Longrightarrow> loop s (n+m) = []"
  using loop_def by (induct m) auto

lemma flatten_append: "flatten (xs@ys) = ((flatten xs) @ (flatten ys))"
  by (induct xs) auto

lemma set_flatten: "set (flatten xs) = \<Union> (set ` set xs)"
  by (induct xs) auto

lemma loop: "\<forall>x. ((n,x) \<in> calculation s) = (x \<in> set (loop [s] n))"
  proof (induct n)
    case 0 then show ?case using loop_def by simp
  next
    case (Suc m) then show ?case proof (intro allI iffI)
      fix x ys zs
      assume "(Suc m,x) \<in> calculation s"
      then have "\<exists>t. (m,t) \<in> calculation s \<and> x \<in> set (solve t) \<and> \<not> is_axiom (list_sequent t)"
        using calculation_downwards by blast
      then obtain t where 1: "(m,t) \<in> calculation s \<and> x \<in> set (solve t) \<and> \<not> is_axiom (list_sequent t)"
        by blast
      then show "(x \<in> set (loop [s] (Suc m)))"
        using Suc loop_def by (clarsimp dest!: split_list_first simp: flatten_append)
    next
      fix x
      assume "(x \<in> set (loop [s] (Suc m)))"
      then show "(Suc m,x) \<in> calculation s"
        using Suc by (fastforce simp: set_flatten loop_def)
    qed
  qed

lemma calculation_f: "calculation s = UNION UNIV (\<lambda>x. set (map (\<lambda>y. (x,y)) (loop [s] x)))"
  using loop by fastforce

lemma finite_calculation':
  assumes "finite (calculation s)"
  shows "(\<exists>m. loop [s] m = [])"
  proof -
    show ?thesis proof -
      have "finite (fst ` (calculation s))" using assms by simp
      then obtain x where xMax: "x \<in> fst ` calculation s \<and> (\<forall>y. y \<in> fst ` calculation s \<longrightarrow> y \<le> x)"
        using max_exists by fastforce
      then show ?thesis proof (cases "loop [s] (Suc x)")
        assume "loop [s] (Suc x) = []" then show ?thesis by blast
      next
        fix a l
        assume "loop [s] (Suc x) = a # l"
        then have "(Suc x,a) \<in> calculation s" using loop by simp
        then show ?thesis using xMax by fastforce
      qed
    qed
  qed

lemma finite_calculation'':
  assumes "(\<exists>m. loop [s] m = [])"
  shows "finite (calculation s)"
  proof -
    obtain m where "loop [s] m = []" using assms by blast
    then have "\<forall>y. loop [s] (m+y) = []" using loop_upwards by simp
    then have 1: "(UN x:Collect (op \<le> m). Pair x ` set (loop [s] x)) =  (UN x:Collect (op \<le> m). {})"
      using SUP_cong image_is_empty le_Suc_ex mem_Collect_eq set_empty
      by (metis (no_types,lifting))
    then have "(UNIV::nat set) = {y. y < m} Un {y. m \<le> y}" by fastforce
    then show ?thesis using 1 calculation_f by (clarsimp elim!: ssubst)
 qed

lemma finite_calculation: "finite (calculation s) = (\<exists>m. loop [s] m = [])"
  using finite_calculation' finite_calculation'' by blast

corollary finite_calculation_prover: "finite (calculation s) = prover [s]"
  using finite_calculation loop_def prover_def by (simp add: all)

section "Correctness"

lemmas magic = soundness completeness finite_calculation_prover

theorem correctness: CHECK VALID
proof -
  have xxx: "\<forall>p. [[(0,p)]] = [map (Pair 0) [p]]" by simp  
  have CHECK using magic check_def valid_def semantics_alternative.simps by (metis xxx make_sequent_def)
  also have VALID using magic make_sequent_def by force
  then show CHECK VALID using calculation by simp_all
qed

corollary "\<exists>p. check p" "\<exists>p. \<not> check p"
proof -
  have "\<not> valid [Pre True '''' []]" "valid [Dis (Pre True '''' []) (Pre False '''' [])]"
    using valid_def is_model_environment_def by auto
  then show "\<exists>p. check p" "\<exists>p. \<not> check p"
    unfolding correctness using magic check_def correctness(1) by (auto,metis) 
qed

section "Appendix"

ML

{*

datatype nnf = Pre of bool * string * int list | Con of nnf * nnf | Uni of nnf
                                               | Dis of nnf * nnf | Exi of nnf

val test = Dis (Uni (Con (Pre (false,"P",[0]),Pre (false,"Q",[0]))),
                Dis (Exi (Pre (true,"Q",[0])),Exi (Pre (true,"P",[0]))))

fun adjust [] = []
  | adjust (h :: t) = case h of 0 => adjust t | n => n - 1 :: adjust t

fun fv (Pre (_,_,v)) = v
  | fv (Con (p,q)) = fv p @ fv q
  | fv (Dis (p,q)) = fv p @ fv q
  | fv (Uni p) = adjust (fv p)
  | fv (Exi p) = adjust (fv p)

fun maxn x y = if x > y then x else y

fun maxl [] = 0
  | maxl (h :: t) = maxn h (maxl t)

fun fresh l = if l = [] then 0 else (maxl l) + 1

fun subst f (Pre (b,i,v)) = Pre (b,i,map f v)
  | subst f (Con (p,q)) = Con (subst f p,subst f q)
  | subst f (Dis (p,q)) = Dis (subst f p,subst f q)
  | subst f (Uni p) = Uni (subst (fn 0 => 0 | n => f (n - 1) + 1) p)
  | subst f (Exi p) = Exi (subst (fn 0 => 0 | n => f (n - 1) + 1) p)

fun bind p y = subst (fn 0 => y | n => n - 1) p

fun member _ [] = false
  | member a (h :: t) = if a = h then true else member a t

fun flatten [] = []
  | flatten (h :: t) = h @ flatten t

fun all f l = flatten (map f l)

fun solve s = case s of [] => [[]] | h :: t => case h of (n,r) => case r of
  Pre (b,i,v) => if member (Pre (not b,i,v)) (map snd t) then [] else [t @ [(0,Pre (b,i,v))]]
| Con (p,q) => [t @ [(0,p)],t @ [(0,q)]]
| Dis (p,q) => [t @ [(0,p),(0,q)]]
| Uni p => [t @ [(0,bind p (fresh (all fv (map snd s))))]]
| Exi p => [t @ [(0,bind p n),(n + 1,r)]]

fun prover a = if a = [] then () else prover (all solve a)

fun check p = prover [[(0,p)]]

val () = check test

*}

(*

export_code make_sequent flatten solve test in SML module_name SimPro file "SimPro.sml"

SML_file "SimPro.sml"

SML_export "val SimPro_make_sequent = SimPro.make_sequent"

SML_export "val SimPro_flatten = SimPro.flatten"

SML_export "val SimPro_inference = SimPro.inference"

SML_export "val SimPro_test = SimPro.test"

ML {*

fun SimPro_prover a = if a = () then true else SimPro_prover ((SimPro_flatten o map SimPro_inference) a);

fun SimPro_check p = SimPro_prover [SimPro_make_sequent [p]]

val () = SimPro_check SimPro_test

*}

*)
