theory SimPro imports Main begin

type_synonym proxy = nat

datatype form = Pos string "nat list" | Con form form | Uni form
              | Neg string "nat list" | Dis form form | Exi form

type_synonym model = "proxy set \<times> (string \<Rightarrow> proxy list \<Rightarrow> bool)"

type_synonym environment = "nat \<Rightarrow> proxy"

definition is_model_environment :: "model \<Rightarrow> environment \<Rightarrow> bool" where
  "is_model_environment m e = (\<forall>n. e n \<in> fst m)"

primrec semantics :: "model \<Rightarrow> environment \<Rightarrow> form \<Rightarrow> bool" where
  "semantics m e (Pos i v) = snd m i (map e v)"
| "semantics m e (Neg i v) = (\<not> snd m i (map e v))"
| "semantics m e (Con p q) = (semantics m e p \<and> semantics m e q)"
| "semantics m e (Dis p q) = (semantics m e p \<or> semantics m e q)"
| "semantics m e (Uni p) = (\<forall>z \<in> fst m. semantics m (\<lambda>x. case x of 0 \<Rightarrow> z | Suc n \<Rightarrow> e n) p)"
| "semantics m e (Exi p) = (\<exists>z \<in> fst m. semantics m (\<lambda>x. case x of 0 \<Rightarrow> z | Suc n \<Rightarrow> e n) p)"

primrec semantics_alternative :: "model \<Rightarrow> environment \<Rightarrow> form list \<Rightarrow> bool" where
  "semantics_alternative _ _ [] = False"
| "semantics_alternative m e (h # t) = (semantics m e h \<or> semantics_alternative m e t)"

definition valid :: "form list \<Rightarrow> bool" where
  "valid l = (\<forall>m e. is_model_environment m e \<longrightarrow> semantics_alternative m e l)"

type_synonym sequent = "(nat \<times> form) list"

definition make_sequent :: "form list \<Rightarrow> sequent" where
  "make_sequent l = map (\<lambda>p. (0,p)) l"

definition list_sequent :: "sequent \<Rightarrow> form list" where
  "list_sequent s = map snd s"

primrec member :: "'a => 'a list => bool" where
  "member _ [] = False"
| "member a (h # t) = (if a = h then True else member a t)"

primrec flatten :: "'a list list \<Rightarrow> 'a list" where
  "flatten [] = []"
| "flatten (h # t) = h @ flatten t"

primrec cut :: "nat list \<Rightarrow> nat list" where
  "cut [] = []"
| "cut (h # t) = (case h of 0 \<Rightarrow> cut t | Suc n \<Rightarrow> n # cut t)"

primrec fv :: "form \<Rightarrow> nat list" where
  "fv (Pos _ v) = v"
| "fv (Neg _ v) = v"
| "fv (Con p q) = fv p @ fv q"
| "fv (Dis p q) = fv p @ fv q"
| "fv (Uni p) = cut (fv p)"
| "fv (Exi p) = cut (fv p)"

primrec max_list :: "nat list \<Rightarrow> nat" where
  "max_list [] = 0"
| "max_list (h # t) = max h (max_list t)"

definition fresh :: "nat list \<Rightarrow> nat" where
  "fresh l = (if l = [] then 0 else Suc (max_list l))"

primrec substitution :: "(nat \<Rightarrow> nat) \<Rightarrow> form \<Rightarrow> form" where
  "substitution f (Pos i v) = Pos i (map f v)"
| "substitution f (Neg i v) = Neg i (map f v)"
| "substitution f (Con p q) = Con (substitution f p) (substitution f q)"
| "substitution f (Dis p q) = Dis (substitution f p) (substitution f q)"
| "substitution f (Uni p) = Uni (substitution (\<lambda>x. case x of 0 \<Rightarrow> 0 | Suc n \<Rightarrow> Suc (f n)) p)"
| "substitution f (Exi p) = Exi (substitution (\<lambda>x. case x of 0 \<Rightarrow> 0 | Suc n \<Rightarrow> Suc (f n)) p)"

definition substitution_bind :: "form \<Rightarrow> nat \<Rightarrow> form" where
  "substitution_bind p y = substitution (\<lambda>x. case x of 0 \<Rightarrow> y | Suc n \<Rightarrow> n) p"

definition inference :: "sequent \<Rightarrow> sequent list" where
  "inference s = (case s of [] \<Rightarrow> [[]] | (n,h) # t \<Rightarrow> (case h of
      Pos i v \<Rightarrow> if member (Neg i v) (list_sequent t) then [] else [t @ [(0,Pos i v)]]
    | Neg i v \<Rightarrow> if member (Pos i v) (list_sequent t) then [] else [t @ [(0,Neg i v)]]
    | Con p q \<Rightarrow> [t @ [(0,p)],t @ [(0,q)]]
    | Dis p q \<Rightarrow> [t @ [(0,p),(0,q)]]
    | Uni p \<Rightarrow> [t @ [(0,substitution_bind p (fresh ((flatten \<circ> map fv) (list_sequent s))))]]
    | Exi p \<Rightarrow> [t @ [(0,substitution_bind p n),(Suc n,h)]] ))"

primrec repeat :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> 'a" where
  "repeat _ a 0 = a"
| "repeat f a (Suc n) = f (repeat f a n)"

definition prover :: "sequent list \<Rightarrow> bool" where
  "prover a = (\<exists>n. repeat (flatten \<circ> map inference) a n = [])"

definition check :: "form \<Rightarrow> bool" where
  "check p = prover [make_sequent [p]]"

abbreviation(input) check_thesis :: bool where
  "check_thesis \<equiv> check = (\<lambda>p. \<forall>m e. is_model_environment m e \<longrightarrow> semantics m e p)"

lemma repeat_repeat: "repeat f (f a) n = f (repeat f a n)"
  by (induct n) auto

proposition "(\<exists>n. r (repeat f a n)) = (if r a then True else (\<exists>n. r (repeat f (f a) n)))"
  by (metis repeat.simps repeat_repeat not0_implies_Suc)

inductive_set calculation :: "sequent \<Rightarrow> (nat \<times> sequent) set" for s :: sequent where
  init[intro]: "(0,s) \<in> calculation s"
| step[intro]: "(n,k) \<in> calculation s \<Longrightarrow> l \<in> set (inference k) \<Longrightarrow> (Suc n,l) \<in> calculation s"

abbreviation(input) valid_thesis :: bool where
  "valid_thesis \<equiv> valid = finite \<circ> calculation \<circ> make_sequent"

lemma "\<forall>m. \<forall>e. is_model_environment m e \<longrightarrow> fst m \<noteq> {}"
  using is_model_environment_def by auto

lemma "\<exists>m. \<forall>e. is_model_environment m e \<and> infinite (fst m)"
  using is_model_environment_def by auto

(**************************************************************************************************)

definition fv_list :: "form list \<Rightarrow> nat list" where
  "fv_list = flatten \<circ> map fv"

primrec is_axiom :: "form list \<Rightarrow> bool" where
  "is_axiom [] = False"
| "is_axiom (p # t) = ((\<exists>i v. p = Pos i v \<and> Neg i v \<in> set t) \<or> (\<exists>i v. p = Neg i v \<and> Pos i v \<in> set t))"

lemma member_set[simp]: "member a l = (a \<in> (set l))" by (induct l) auto

lemma pos:  "(n,(m,Pos i v) # xs) \<in> calculation(nfs) \<Longrightarrow> \<not> is_axiom (list_sequent ((m,Pos i v) # xs)) \<Longrightarrow> (Suc n,xs@[(0,Pos i v)]) \<in> calculation(nfs)"
  and neg:  "(n,(m,Neg i v) # xs) \<in> calculation(nfs) \<Longrightarrow> \<not> is_axiom (list_sequent ((m,Neg i v) # xs)) \<Longrightarrow> (Suc n,xs@[(0,Neg i v)]) \<in> calculation(nfs)"
  and con1: "(n,(m,Con f g) # xs) \<in> calculation(nfs) \<Longrightarrow> \<not> is_axiom (list_sequent ((m,Con f g) # xs)) \<Longrightarrow> (Suc n,xs@[(0,f)]) \<in> calculation(nfs)"
  and con2: "(n,(m,Con f g) # xs) \<in> calculation(nfs) \<Longrightarrow> \<not> is_axiom (list_sequent ((m,Con f g) # xs)) \<Longrightarrow> (Suc n,xs@[(0,g)]) \<in> calculation(nfs)"
  and dis:  "(n,(m,Dis f g) # xs) \<in> calculation(nfs) \<Longrightarrow> \<not> is_axiom (list_sequent ((m,Dis f g) # xs)) \<Longrightarrow> (Suc n,xs@[(0,f),(0,g)]) \<in> calculation(nfs)"
  and uni:  "(n,(m,Uni f) # xs) \<in> calculation(nfs) \<Longrightarrow> \<not> is_axiom (list_sequent ((m,Uni f) # xs)) \<Longrightarrow> (Suc n,xs@[(0,substitution_bind f (fresh ((flatten \<circ> map fv) (list_sequent ((m,Uni f) # xs)))))]) \<in> calculation(nfs)"
  and exi:  "(n,(m,Exi f) # xs) \<in> calculation(nfs) \<Longrightarrow> \<not> is_axiom (list_sequent ((m,Exi f) # xs)) \<Longrightarrow> (Suc n,xs@[(0,substitution_bind f m),(Suc m,Exi f)]) \<in> calculation(nfs)"
  by (auto simp: inference_def list_sequent_def)

lemmas not_is_axiom_subs = pos neg con1 con2 dis uni exi

lemma calculation_init[simp]: "(0,k) \<in> calculation s = (k = s)"
  using calculation.cases by blast

lemma calculation_upwards:
  assumes 1: "(n,k) \<in> calculation s" and 2: "\<not> is_axiom (list_sequent (k))"
  shows "(\<exists>l. (Suc n, l) \<in> calculation s \<and> l \<in> set (inference k))"
  proof (cases k)
    case Nil then show ?thesis using 1 inference_def by auto
  next
    case c: (Cons a _) then show ?thesis
    proof (cases a)
      case (Pair _ p)
      then show ?thesis using c 1 2 list_sequent_def inference_def by (cases p) fastforce+
    qed
  qed

lemma calculation_downwards: "(Suc n, k) \<in> calculation s \<Longrightarrow> \<exists>t. (n,t) \<in> calculation s \<and> k \<in> set (inference t) \<and> \<not> is_axiom (list_sequent t)"
  proof (erule calculation.cases)
    assume "Suc n = 0"
    then show ?thesis using list_sequent_def by simp
  next
    fix m l k'
    assume 1: "Suc n = Suc m"
    assume 2: "k = k'"
    assume 3: "(m, l) \<in> calculation s"
    assume 4: "k' \<in> set (inference l)"
    then show ?thesis proof (cases l)
      case Nil then show ?thesis using 1 2 3 4 list_sequent_def by fastforce
    next
      case c: (Cons a _) then show ?thesis proof (cases a)
        case (Pair _ p) then show ?thesis
          using 1 2 3 4 c inference_def list_sequent_def by (cases p) auto
      qed
    qed
  qed
 
lemma calculation_calculation_child[rule_format]: "\<forall>s t. (Suc n,s) \<in> calculation t = (\<exists>k. k \<in> set (inference t) \<and> \<not> is_axiom (list_sequent t) \<and> (n,s) \<in> calculation k)"
  using calculation_downwards by (induct n) (fastforce, blast)

lemma calculation_progress:
  assumes 1:  "(n,a # l) \<in> calculation s" and 2: "\<not> is_axiom (list_sequent (a # l))"
  shows "(\<exists>k. (Suc n, l@k) \<in> calculation s)"
  proof (cases a)
    case p: (Pair _ p)
    show ?thesis using p 1 2 by (cases p) (auto dest: not_is_axiom_subs)
  qed

definition
  inc :: "nat \<times> sequent \<Rightarrow> nat \<times> sequent" where
  "inc = (\<lambda>(n,fs). (Suc n, fs))"

lemma inj_inc[simp]: "inj inc"
  by (simp add: inc_def inj_on_def)

lemma calculation: "calculation s = insert (0,s) (inc ` (\<Union> (calculation ` {k. \<not> is_axiom (list_sequent s) \<and> k \<in> set (inference s)})))"
   by (clarsimp intro!: set_eqI, rename_tac n k, case_tac n)
      (auto simp: calculation_calculation_child inc_def)

lemma calculation_is_axiom: "is_axiom (list_sequent s) \<Longrightarrow> calculation s = {(0,s)}"
  by (clarsimp intro!: set_eqI, rule iffI)
     (metis calculation.simps calculation_calculation_child, blast)
   
lemma is_axiom_finite_calculation: "is_axiom (list_sequent s) \<Longrightarrow> finite (calculation s)"
  by (simp add: calculation_is_axiom)

primrec failing_path :: "(nat \<times> sequent) set \<Rightarrow> nat \<Rightarrow> (nat \<times> sequent)" where
  "failing_path ns 0 = (SOME x. x \<in> ns \<and> fst x = 0 \<and> infinite (calculation (snd x)) \<and> \<not> is_axiom (list_sequent (snd x)))"
| "failing_path ns (Suc n) = (let fn = failing_path ns n in 
  (SOME fsucn. fsucn \<in> ns \<and> fst fsucn = Suc n \<and> (snd fsucn) \<in> set (inference (snd fn)) \<and> infinite (calculation (snd fsucn)) \<and> \<not> is_axiom (list_sequent (snd fsucn))))"

locale loc1 = fixes s and f assumes f: "f = failing_path (calculation s)"

lemma (in loc1) f0: "infinite (calculation s) \<Longrightarrow> f 0 \<in> (calculation s) \<and> fst (f 0) = 0 \<and> infinite (calculation (snd (f 0))) \<and> \<not> is_axiom (list_sequent (snd (f 0)))"
  by (simp add: f) (metis (mono_tags, lifting) calculation.init is_axiom_finite_calculation fst_conv snd_conv someI_ex)

lemma infinite_union: "finite Y \<Longrightarrow> infinite (Union (f ` Y)) \<Longrightarrow> \<exists>y. y \<in> Y \<and> infinite (f y)"
  by auto

lemma infinite_inj_infinite_image: "inj_on f Z \<Longrightarrow> infinite (f ` Z) = infinite Z"
  using finite_imageD by auto

lemma inj_inj_on: "inj f \<Longrightarrow> inj_on f A"
  using subset_inj_on by blast

lemma t: "finite {w. P w} \<Longrightarrow> finite {w. Q w \<and> P w}"
  using finite_subset by simp

lemma finite_subs: "finite {w. \<not> is_axiom (list_sequent y) \<and> w : set (inference y)}"
  by simp

lemma (in loc1) fSuc:
  assumes "f n \<in> calculation s \<and> fst (f n) = n \<and> infinite (calculation (snd (f n))) \<and> \<not> is_axiom (list_sequent (snd (f n)))"
  shows "f (Suc n) \<in> calculation s \<and> fst (f (Suc n)) = Suc n \<and> (snd (f (Suc n))) \<in> set (inference (snd (f n))) \<and> infinite (calculation (snd (f (Suc n)))) \<and> \<not> is_axiom (list_sequent (snd (f (Suc n))))"
  proof -
    have "infinite (\<Union> (calculation ` {w. \<not> is_axiom (list_sequent (snd (f n))) \<and> w \<in> set (inference (snd (f n)))}))"
      using assms by (clarsimp simp: f) (metis (no_types, lifting) calculation finite.insertI finite_imageI finite_subs infinite_union mem_Collect_eq)
    then show ?thesis using assms f calculation.step is_axiom_finite_calculation
      by simp (rule someI_ex, simp, metis prod.collapse)
 qed

lemma (in loc1) is_path_f_0: "infinite (calculation s) \<Longrightarrow> f 0 = (0,s)"
  using calculation_init f0 prod.collapse by metis

lemma (in loc1) is_path_f': "infinite (calculation s) \<Longrightarrow> f n \<in> calculation s \<and> fst (f n) = n \<and> infinite (calculation (snd (f n))) \<and> \<not> is_axiom (list_sequent (snd (f n)))"
  using f0 fSuc by (induct n) simp_all

lemma (in loc1) is_path_f: "infinite (calculation s) \<Longrightarrow> \<forall>n. f n \<in> calculation s \<and> fst (f n) = n \<and> (snd (f (Suc n))) \<in> set (inference (snd (f n))) \<and> infinite (calculation (snd (f n)))"
  using is_path_f' fSuc by simp

lemma cut[simp]: "Suc n \<in> set A = (n \<in> set (cut A))"
  proof (induct A)
    case Nil then show ?case by simp
  next
    case (Cons m _) then show ?case by (cases m) simp_all
  qed

lemma eval_cong: "\<forall>e1 e2. (\<forall>x. x \<in> set (fv A) \<longrightarrow> e1 x = e2 x) \<longrightarrow> semantics mi e1 A = semantics mi e2 A"
  proof (induct A)
    case Pos then show ?case using map_cong fv.simps(1) semantics.simps(1) by metis
  next
    case Neg then show ?case using map_cong fv.simps(2) semantics.simps(2) by metis
  next
    case Con then show ?case using Un_iff fv.simps(3) semantics.simps(3) set_append by metis
  next
    case Dis then show ?case using Un_iff fv.simps(4) semantics.simps(4) set_append by metis
  next
    case Uni then show ?case 
     using Nitpick.case_nat_unfold cut not_gr0 Suc_pred' fv.simps(5) semantics.simps(5)
     by (metis (no_types, lifting))
  next
    case Exi then show ?case
      using Nitpick.case_nat_unfold cut not_gr0 Suc_pred' fv.simps(6) semantics.simps(6)
      by (metis (no_types, lifting))
   qed

lemma semantics_alternative_def2: "semantics_alternative m e s = (\<exists>p. p \<in> set s \<and> semantics m e p)"
  by (induct s) auto

lemma semantics_alternative_append: "semantics_alternative m e (s @ s') = ((semantics_alternative m e s) \<or> (semantics_alternative m e s'))"
  by (induct s) auto

lemma fv_list_nil: "fv_list [] = []"
  by (simp add: fv_list_def)

lemma fv_list_cons: "fv_list (a # list) = (fv a) @ (fv_list list)"
  by (simp add: fv_list_def)

lemma semantics_alternative_cong: "(\<forall>x. x \<in> set (fv_list s) \<longrightarrow> e1 x = e2 x) \<longrightarrow> semantics_alternative m e1 s = semantics_alternative m e2 s" 
 by (induct s) (simp, metis eval_cong semantics_alternative.simps(2) Un_iff set_append fv_list_cons)

section "Soundness"

lemma ball_eq_ball: "\<forall>x \<in> m. P x = Q x \<Longrightarrow> (\<forall>x \<in> m. P x) = (\<forall>x \<in> m. Q x)"
  by simp

lemma bex_eq_bex: "\<forall>x \<in> m. P x = Q x \<Longrightarrow> (\<exists>x \<in> m. P x) = (\<exists>x \<in> m. Q x)"
  by simp

lemma eval_substitution: "\<forall>e f. (semantics mi e (substitution f A)) = (semantics mi (e \<circ> f) A)"
  proof (induct A)
    case Pos then show ?case by (simp add: comp_def)
  next
    case Neg then show ?case by (simp add: comp_def)
  next
    case Con then show ?case by (simp add: comp_def)
  next
    case Dis then show ?case by (simp add: comp_def)
  next
    case Uni
    then show ?case
      by (clarsimp intro!: ball_eq_ball simp: eval_cong Nitpick.case_nat_unfold)
  next
    case Exi then show ?case
      by (clarsimp intro!: bex_eq_bex simp: eval_cong Nitpick.case_nat_unfold)
  qed

lemma eval_substitution_bind: "semantics mo e (substitution_bind A u) = semantics mo (case_nat (e u) e) A"
  using substitution_bind_def eval_substitution eval_cong
  by (simp add: Nitpick.case_nat_unfold)

lemma sound_Uni: "u \<notin> set (fv_list (Uni f # s)) \<Longrightarrow> valid (s@[substitution_bind f u]) \<Longrightarrow> valid (Uni f # s)"
  apply(clarsimp simp: valid_def)
  apply(rename_tac M I e z)
  apply(subgoal_tac "semantics (M,I) (case_nat z (e(u:=z))) f = semantics (M,I) (case_nat z e) f")
   prefer 2
   apply(clarsimp simp: Nitpick.case_nat_unfold fv_list_cons intro!: eval_cong[rule_format])
   apply(metis One_nat_def Suc_pred' cut)
  apply(clarsimp simp: fv_list_cons semantics_alternative_cong semantics_alternative_append eval_substitution_bind is_model_environment_def)
  apply(drule_tac x=M in spec)
  apply(drule_tac x=I in spec)
  apply(metis (no_types, lifting) fun_upd_apply semantics_alternative_cong)
  done
 
lemma sound_Exi: "valid (s@[substitution_bind f u,Exi f]) \<Longrightarrow> valid (Exi f # s)"
  by (simp add: valid_def semantics_alternative_append eval_substitution_bind)
     (metis is_model_environment_def prod.sel(1))

lemma max_exists: "finite (X::nat set) \<Longrightarrow> X \<noteq> {} \<longrightarrow> (\<exists>x. x \<in> X \<and> (\<forall>y. y \<in> X \<longrightarrow> y \<le> x))"
  using Max.coboundedI Max_in by blast

lemma inj_finite_image_eq_finite: "inj_on f Z \<Longrightarrow> finite (f ` Z) = finite Z"
  using finite_imageD by blast

lemma finite_inc: "finite (inc ` X) = finite X"
  using finite_imageI inj_inc inv_image_comp by metis

lemma finite_calculation_calculation: "finite (calculation s) \<Longrightarrow> finite  (calculation ` {w. \<not> is_axiom (list_sequent s) \<and> w : set (inference s)})"
  by simp

definition init :: "sequent \<Rightarrow> bool" where
  "init s = (\<forall>x \<in> (set s). fst x = 0)"

definition is_Exi :: "form \<Rightarrow> bool" where
  "is_Exi f = (case f of
    Exi _ \<Rightarrow> True |
    _     \<Rightarrow> False)"

lemma is_Exi[simp]: "\<not> is_Exi (Pos i v) \<and> \<not> is_Exi (Neg i v) \<and> \<not> is_Exi (Con f g) \<and> \<not> is_Exi (Dis f g) \<and> \<not> is_Exi (Uni f)"
  using is_Exi_def by simp

lemma index0: "init s \<Longrightarrow> \<forall>u m A. (n, u) \<in> calculation s \<longrightarrow> (m,A) \<in> (set u) \<longrightarrow> (\<not> is_Exi A) \<longrightarrow> m = 0"
  proof (induct n)
    case 0 then show ?case using init_def by fastforce
  next
    case Suc then show ?case
      by (clarsimp dest!: calculation_downwards, case_tac t, simp add: inference_def, case_tac a, case_tac b)
         (fastforce simp: inference_def list_sequent_def is_Exi_def)+
  qed

lemma max_list: "\<forall>v \<in> set l. v \<le> max_list l"
  by (induct l) (auto simp: max_def)

lemma fresh: "fresh l \<notin> (set l)"
  using length_pos_if_in_set max_list fresh_def by fastforce

lemma soundness': "init s \<Longrightarrow> finite (calculation s) \<Longrightarrow> m \<in> (fst ` (calculation s)) \<Longrightarrow> \<forall>y u. (y,u) \<in> (calculation s) \<longrightarrow> y \<le> m \<Longrightarrow> \<forall>n t. h = m - n \<and> (n,t) \<in> calculation s \<longrightarrow> valid (list_sequent t)"
  using inference_def fv_list_def
  apply(induct h)
    -- "base case"
   apply(intro allI impI)
   apply(subgoal_tac "n=m")
    prefer 2 apply(fastforce)
   apply(clarsimp simp: valid_def semantics_alternative_def2)
   apply(case_tac "is_axiom (list_sequent t)")
     -- "base case, is axiom"
    apply(simp add: list_sequent_def)
    apply(case_tac t)
     apply(simp)
    apply(simp)
    apply (metis (no_types, lifting) semantics.simps(1) semantics.simps(2))
   
    -- "base case, not is axiom: if not a satax, then inference holds... but this can't be"
   apply (meson calculation_upwards le_SucI le_antisym n_not_Suc_n)
   
     -- "step case, by case analysis"
  apply(intro allI impI)
  apply(elim exE conjE)

  apply(case_tac "is_axiom (list_sequent t)")
    -- "step case, is axiom"
   apply(clarsimp simp: valid_def semantics_alternative_def2 list_sequent_def)
   apply(case_tac t)
    apply(simp)
   apply(simp)
   apply(metis (no_types, lifting) semantics.simps(1) semantics.simps(2))
   -- "we hit Uni/ Exi cases first"
  apply(case_tac "\<exists>(a::nat) f list. t = (a,Uni f) # list")
   apply(elim exE)
   apply(simp)
   apply(subgoal_tac "a = 0")
    prefer 2 apply (meson index0 is_Exi list.set_intros(1))
   apply(frule calculation.step)
    apply(simp)
    apply(metis (no_types, lifting) Suc_diff_Suc Suc_leD diff_diff_cancel diff_le_self fresh le_simps(3) list.simps(8) list.simps(9) list_sequent_def map_append snd_eqD sound_Uni)
  apply(case_tac "\<exists>a f list. t = (a,Exi f) # list")
   apply(elim exE)
   apply(frule calculation.step)
    apply(simp)
   apply(metis (no_types, lifting) Suc_diff_Suc Suc_leD diff_diff_cancel diff_le_self le_simps(3) list.simps(8) list.simps(9) list_sequent_def map_append snd_eqD sound_Exi)
   -- "now for other cases"
      -- "case empty list"
  apply(case_tac t)
   apply (metis (no_types, lifting) Suc_diff_Suc Suc_leD Un_iff append_Nil2 calculation_upwards diff_diff_cancel diff_le_self insert_iff le_simps(3) list.set(2) list.simps(4) set_append split_list_first)
   
  apply(simp add: valid_def semantics_alternative_def2)
  apply(rule allI)
  apply(rule allI)
  apply(rename_tac gs g)
  apply(rule allI)
  apply(rule impI)
  -- "na t in calculation, so too is inference"
   -- "if not a satax, then inference holds... "
  apply(case_tac a)
  apply(case_tac b)
       apply(fastforce simp: list_sequent_def dest!: pos)
      apply(simp del: semantics.simps)
      apply(frule con1)
       apply(assumption)
      apply(frule con2)
       apply(assumption)
      apply(rename_tac form1 form2)
      apply(frule_tac x="Suc n" in spec, drule_tac x="list @ [(0, form1)]" in spec)
      apply(erule impE)
       apply(simp)
      apply(drule_tac x=gs in spec, drule_tac x=g in spec, drule_tac x=e in spec)
      apply(erule impE)
       apply(simp)
      apply(elim exE conjE)
      apply(drule_tac x="Suc n" in spec, drule_tac x="list @ [(0, form2)]" in spec)
      apply(erule impE)
       apply(simp)
      apply(metis (no_types, lifting) Un_iff append_Nil2 insert_iff list.set(2) list.set_intros(1) list.simps(9) list_sequent_def map_append semantics.simps(3) set_append snd_conv)
     apply(blast)
    apply(fastforce simp: list_sequent_def dest!: neg)
   apply(simp)
   apply(frule dis)
    apply(assumption)
   apply(rename_tac form1 form2)
   apply(frule_tac x="Suc n" in spec, drule_tac x="list @ [(0, form1),(0,form2)]" in spec)
   apply(erule impE)
    apply(simp)
   apply(metis (no_types, lifting) Un_iff append_Nil2 insert_iff list.set(2) list.set_intros(1) list.simps(9) list_sequent_def map_append semantics.simps(4) set_append snd_conv)
    -- "all case"
  apply(blast)
  done

lemma xxx[simp]: "list_sequent (make_sequent s) = s"
  using list_sequent_def make_sequent_def by (induct s) simp_all

lemma soundness:
  assumes 1: "finite (calculation (make_sequent s))"
  shows "valid s"
  proof -
    have "init (make_sequent s)" and "finite (fst ` (calculation (make_sequent s)))"
      using 1 by (simp add: init_def make_sequent_def, simp)
    then show ?thesis using 1 calculation.init soundness' xxx max_exists
      by (metis (mono_tags, lifting) empty_iff fst_conv image_eqI)
qed

section "Contains / Considers"

definition contains :: "(nat \<Rightarrow> (nat \<times> sequent)) \<Rightarrow> nat \<Rightarrow> nat \<times> form \<Rightarrow> bool" where
  "contains f n nf = (nf \<in> set (snd (f n)))"

definition considers :: "(nat \<Rightarrow> (nat \<times> sequent)) \<Rightarrow> nat \<Rightarrow> nat \<times> form \<Rightarrow> bool" where
  "considers f n nf = (case snd (f n) of [] \<Rightarrow> False | (x # xs) \<Rightarrow> x = nf)"

lemma (in loc1) progress:
  assumes 1: "infinite (calculation s)"
  shows "snd (f n) = a # list \<longrightarrow> (\<exists>zs'. snd (f (Suc n)) = list@zs')"
  proof -
    obtain 2: "(snd (f (Suc n))) : set (inference (snd (f n)))" using 1 is_path_f by blast
    then show ?thesis proof (cases a)
      case (Pair _ b)
      then show ?thesis using 2 inference_def
        by (induct b, safe, simp_all split: if_splits) blast
  qed
qed

lemma (in loc1) contains_considers'[rule_format]: "infinite (calculation s) \<Longrightarrow> \<forall>n y ys. snd (f n) = xs@y # ys \<longrightarrow> (\<exists>m zs'. snd (f (n+m)) = y # zs')"
  proof (induct xs)
    case Nil then show ?case by simp (metis Nat.add_0_right)
  next
    case Cons then show ?case
      by (clarsimp, clarsimp dest!: progress, elim impE)
         (simp, metis add_Suc_shift append_Cons append_assoc)
  qed

lemma (in loc1) contains_considers: "infinite (calculation s) \<Longrightarrow> contains f n y \<Longrightarrow> (\<exists>m. considers f (n+m) y)"
  by (clarsimp simp: contains_def considers_def dest!: split_list_first, frule contains_considers')
     (assumption, metis (mono_tags, lifting) list.simps(5))

lemma (in loc1) contains_propagates_Pos[rule_format]:
  assumes "infinite (calculation s)" and "contains f n (0, Pos i v)"
  shows "contains f (n+q) (0, Pos i v)"
  proof (induct q)
    case 0 then show ?case using assms by simp
  next
    case (Suc q')
    then have IH: "contains f (n + q') (0, Pos i v)" by simp
    then have "\<exists>ys zs. snd (f (n + q')) = ys @ (0, Pos i v) # zs \<and> (0, Pos i v) \<notin> set ys"
      by (meson contains_def split_list_first)
    then obtain ys and zs where 4: "snd (f (n + q')) = ys @ (0, Pos i v) # zs \<and> (0, Pos i v) \<notin> set ys"
      by blast
    then have 5: "(snd (f (Suc (n + q')))) \<in> set (inference (snd (f (n + q'))))"
      using assms by (blast dest: is_path_f)
    then show ?case proof (cases ys)
      case Nil
      then show ?thesis using 4 5 contains_def inference_def
        by (simp split: if_splits)
    next
      case Cons then show ?thesis using assms 4 contains_def progress
        by simp (metis IH Un_iff set_ConsD set_append)
    qed
  qed

lemma (in loc1) contains_propagates_Neg[rule_format]:
  assumes "infinite (calculation s)" and "contains f n (0, Neg i v)"
  shows "contains f (n+q) (0, Neg i v)"
  proof (induct q)
    case 0 then show ?case using assms by simp
  next
    case (Suc q')
    then have IH: "contains f (n + q') (0, Neg i v)" by simp
    then have "\<exists>ys zs. snd (f (n + q')) = ys @ (0, Neg i v) # zs \<and> (0, Neg i v) \<notin> set ys"
      by (meson contains_def split_list_first)
    then obtain ys and zs where 4: "snd (f (n + q')) = ys @ (0, Neg i v) # zs \<and> (0, Neg i v) \<notin> set ys"
      by blast
    then have 5: "(snd (f (Suc (n + q')))) \<in> set (inference (snd (f (n + q'))))"
      using assms by (blast dest: is_path_f)
    then show ?case proof (cases ys)
      case Nil
      then show ?thesis using 4 5 contains_def inference_def
        by (simp split: if_splits)
    next
      case Cons then show ?thesis using assms 4 contains_def progress
        by simp (metis IH Un_iff set_ConsD set_append)
    qed
  qed

lemma (in loc1) contains_propagates_Con:
  assumes 1: "infinite (calculation s)" and 2: "contains f n (0, Con g h)"
  shows "(\<exists>y. contains f (n+y) (0,g) \<or> contains f (n+y) (0,h))"
  proof -
    have 3: "(\<exists>l. considers f (n+l) (0, Con g h))" using 1 2 by (blast dest: contains_considers)
    then obtain l where 4: "considers f (n+l) (0,Con g h)" by blast
    then have 5: "(snd (f (Suc (n + l)))) \<in> set (inference (snd (f (n + l))))"
      using 1 by (blast dest: is_path_f)
    then show ?thesis proof (case_tac "snd (f (n + l))")
      assume "snd (f (n + l)) = []"
      then show ?thesis using 4 considers_def by simp
    next
      fix a list
      assume "snd (f (n + l)) = a # list"
      then show ?thesis using 4 5 considers_def contains_def inference_def
        by (rule_tac x="Suc l" in exI) auto
    qed
  qed

lemma (in loc1) contains_propagates_Dis:
  assumes 1: "infinite (calculation s)" and 2: "contains f n (0, Dis g h)"
  shows "(\<exists>y. contains f (n+y) (0,g) \<and> contains f (n+y) (0,h))"
  proof -
    have 3: "(\<exists>l. considers f (n+l) (0, Dis g h))" using 1 2 by (blast dest: contains_considers)
    then obtain l where 4: "considers f (n+l) (0, Dis g h)" by blast
    then have 5: "(snd (f (Suc (n + l)))) \<in> set (inference (snd (f (n + l))))"
      using 1 by (blast dest: is_path_f)
    then show ?thesis proof (case_tac "snd (f (n + l))")
      assume "snd (f (n + l)) = []"
      then show ?thesis using 4 considers_def by simp
    next
      fix a list
      assume "snd (f (n + l)) = a # list"
      then show ?thesis using 4 5 considers_def contains_def inference_def
        by (rule_tac x="Suc l" in exI) simp
    qed
  qed

lemma (in loc1) contains_propagates_Uni:
  assumes 1: "infinite (calculation s)" and 2: "contains f n (0, Uni g)"
  shows "(\<exists>y. contains f (Suc(n+y)) (0,substitution_bind g (fresh (fv_list (list_sequent (snd (f (n+y))))))))"
  proof -
    have 3: "(\<exists>l. considers f (n+l) (0, Uni g))" using 1 2 by (blast dest: contains_considers)
    then obtain l where 4: "considers f (n+l) (0, Uni g)" by blast
    then have 5: "(snd (f (Suc (n + l)))) \<in> set (inference (snd (f (n + l))))"
      using 1 by (blast dest: is_path_f)
    then show ?thesis proof (case_tac "snd (f (n + l))")
      assume "snd (f (n + l)) = []"
      then show ?thesis using 4 considers_def by simp
    next
      fix a list
      assume "snd (f (n + l)) = a # list"
      then show ?thesis using 4 5 considers_def contains_def inference_def
        by (rule_tac x="l" in exI) (simp add: fv_list_def)
    qed
  qed

lemma (in loc1) contains_propagates_Exi:
  assumes 1: "infinite (calculation s)" and 2: "contains f n (m, Exi g)"
  shows "(\<exists>y. (contains f (n+y) (0,substitution_bind g m)) \<and> (contains f (n+y) (Suc m, Exi g)))"
  proof -
    have 3: "(\<exists>l. considers f (n+l) (m, Exi g))" using 1 2 by (blast dest: contains_considers)
    then obtain l where 4: "considers f (n+l) (m, Exi g)" by (blast dest: is_path_f)
    then have 5: "(snd (f (Suc (n + l)))) \<in> set (inference (snd (f (n + l))))"
      using 1 by (blast dest: is_path_f)
    then show ?thesis proof (case_tac "snd (f (n + l))")
      assume "snd (f (n + l)) = []"
      then show ?thesis using 4 considers_def by simp
    next
      fix a list
      assume "snd (f (n + l)) = a # list"
      then show ?thesis using 4 5 considers_def contains_def inference_def
        by (rule_tac x="Suc l" in exI) simp
    qed
  qed

lemma (in loc1) Exi_downward: "infinite (calculation s) \<Longrightarrow> init s \<Longrightarrow> \<forall>m. (Suc m, Exi g) \<in> set (snd (f n)) \<longrightarrow> (\<exists>n'. (m, Exi g) \<in> set (snd (f n')))"
  apply(frule is_path_f)
  apply(induct_tac n)
   apply(fastforce simp: init_def is_path_f_0)
  apply(drule_tac x="n" in spec)
  apply(case_tac "f n")
  apply(case_tac b)
   apply(simp add: inference_def)
  apply(case_tac aa)
  apply(case_tac ba)
       apply(auto split: if_splits simp: inference_def)[5]
  apply(simp add: inference_def)
  apply(metis list.set_intros(1) snd_eqD)
  done
   
lemma (in loc1) Exi0: "infinite (calculation s) \<Longrightarrow> init s \<Longrightarrow> \<forall>n. contains f n (m,Exi g) \<longrightarrow> (\<exists>n'. contains f n' (0, Exi g))"
  using Exi_downward contains_def by (induct m) (simp, blast)
     
lemma (in loc1) Exi_upward': "infinite (calculation s) \<Longrightarrow> init s \<Longrightarrow> \<forall>n. contains f n (0, Exi g) \<longrightarrow> (\<exists>n'. contains f n' (m, Exi g))"
  using contains_propagates_Exi by (induct m) (simp, blast)

lemma (in loc1) Exi_upward:
  assumes "infinite (calculation s)" and "init s" and "contains f n (m, Exi g)"
  shows "(\<forall>m'. \<exists>n'. contains f n' (0, substitution_bind g m'))"
  proof -
    fix m'
    have "\<exists>n'. contains f n' (m', Exi g)" using assms Exi0 Exi_upward' by blast
    then show ?thesis using assms contains_propagates_Exi Exi0
      by simp (blast dest: Exi_upward')
  qed

abbreviation ntou :: "nat \<Rightarrow> proxy" where "ntou \<equiv> id"

abbreviation uton :: "proxy \<Rightarrow> nat" where "uton \<equiv> id"

section "Falsifying Model From Failing Path"

definition model :: "sequent \<Rightarrow> model" where
  "model s = (range ntou, \<lambda> p ms. (let f = failing_path (calculation s) in (\<forall>n m. \<not> contains f n (m,Pos p (map uton ms)))))"

locale loc2 = loc1 + fixes mo assumes mo: "mo = model s"

lemma is_env_model_ntou: "is_model_environment (model s) ntou"
  using is_model_environment_def model_def by simp

lemma (in loc1) [simp]: "infinite (calculation s) \<Longrightarrow> init s \<Longrightarrow> (contains f n (m,A)) \<Longrightarrow> \<not> is_Exi A \<Longrightarrow> m = 0"
  using contains_def index0 is_path_f' prod.collapse by metis

lemma size_substitution[simp]: "\<forall>m. size (substitution m f) = size f"
  by (induct f) simp_all

lemma size_substitution_bind[simp]: "size (substitution_bind f m) = size f"
  using substitution_bind_def by simp
 
lemma (in loc2) model': "infinite (calculation s) \<Longrightarrow> init s \<Longrightarrow> \<forall>A. size A = h \<longrightarrow> (\<forall>m n. contains f n (m,A) \<longrightarrow> \<not> (semantics mo ntou A))"
  apply(rule nat_less_induct)
  apply(rule allI)
  apply(case_tac A)
       apply(clarsimp simp: mo model_def f[symmetric])
       apply(blast)
      apply(clarsimp)
      apply(metis (mono_tags, lifting) contains_def index0 is_Exi is_path_f less_add_Suc1 less_add_Suc2 contains_propagates_Con prod.collapse)
     apply(intro impI allI)
     apply(subgoal_tac "m=0")
      prefer 2 apply(simp)
     apply(simp)
     apply(frule contains_propagates_Uni)
      apply(assumption)
     apply(erule exE) -- "all case"
     apply(rename_tac form m na y)
     apply(drule_tac x="size form" in spec)
     apply(erule impE)
      apply(simp)
     apply(drule_tac x="substitution_bind form (fresh (fv_list (list_sequent (snd (f (na + y))))))" in spec)
     apply(simp add: eval_substitution_bind)
     apply(erule impE)
      apply(blast)
     apply(rule_tac x="ntou (fresh (fv_list (list_sequent (snd (f (na + y))))))" in bexI)
      apply(simp)
     using is_env_model_ntou is_model_environment_def mo apply(blast)
    
    apply(clarsimp simp: mo model_def f[symmetric])
    apply(subgoal_tac "m = 0 \<and> ma = 0")
     prefer 2 apply(simp)
    apply(rename_tac nat list m na nb ma)
    apply(subgoal_tac "\<exists>y. considers f (nb+na+y) (0, Pos nat list)")
     prefer 2 apply(simp add: contains_considers contains_propagates_Pos)
    apply(erule exE)
    apply(subgoal_tac "contains f (na+nb+y) (0, Neg nat list)")
     apply(subgoal_tac "nb+na=na+nb")
      apply(subgoal_tac "is_axiom (list_sequent (snd (f (na+nb+y))))")
       apply(blast dest: is_path_f is_axiom_finite_calculation)
      apply(simp add: contains_def considers_def)
      apply(case_tac "snd (f (na + nb + y))")
       apply(simp)
      apply(force simp: list_sequent_def)
     apply(simp)
    apply(simp add: contains_propagates_Neg)
   apply(metis (no_types, lifting) contains_def add.right_neutral add_Suc_right form.size(11) index0 is_Exi is_path_f less_add_Suc1 less_add_Suc2 contains_propagates_Dis prod.collapse semantics.simps(4))
 
  apply(clarsimp)
  apply(rename_tac form m na ma)
  apply(subgoal_tac "\<forall>m'. \<not> semantics mo ntou (substitution_bind form m')")
   apply(simp add: eval_substitution_bind id_def)
  apply(intro allI)
  apply(drule_tac x="size form" in spec)
  apply(erule impE)
   apply(simp)
  apply(drule_tac x="substitution_bind form m'" in spec)
  apply(fastforce simp: id_def dest: Exi_upward)
  done
   
lemma (in loc2) model: "infinite (calculation s) \<Longrightarrow> init s \<Longrightarrow> (\<forall>A m n. contains f n (m,A) \<longrightarrow> \<not> (semantics mo ntou A))"
  using model' by simp

section "Completeness"

lemma (in loc2) completeness': "infinite (calculation s) \<Longrightarrow> init s \<Longrightarrow> \<forall>mA \<in> set s. \<not> semantics mo ntou (snd mA)" -- "FIXME tidy calculation s so that s consists of formulae only?"
  by (metis SimPro.contains_def eq_snd_iff is_path_f_0 model)
 
lemma completeness': "infinite (calculation s) \<Longrightarrow> init s \<Longrightarrow> \<forall>mA \<in> set s. \<not> semantics (model s) ntou (snd mA)"
  by (rule loc2.completeness'[simplified loc2_def loc2_axioms_def loc1_def]) simp

lemma completeness'': "infinite (calculation (make_sequent s)) \<Longrightarrow> init (make_sequent s) \<Longrightarrow> \<forall>A. A \<in> set s \<longrightarrow> \<not> semantics (model (make_sequent s)) ntou A"
  using completeness' make_sequent_def by fastforce

lemma completeness: "infinite (calculation (make_sequent s)) \<Longrightarrow> \<not> valid s"
  using valid_def init_def make_sequent_def is_env_model_ntou semantics_alternative_def2 completeness''
  by(subgoal_tac "init (make_sequent s)") (metis, simp)

section "Algorithm"

definition loop :: "sequent list \<Rightarrow> nat \<Rightarrow> sequent list" where
  "loop s n = repeat (flatten \<circ> map inference) s n"

lemma loop_upwards: "loop s n = [] \<Longrightarrow> loop s (n+m) = []"
  using loop_def by (induct m) auto

lemma flatten_append: "flatten (xs@ys) = ((flatten xs) @ (flatten ys))"
  by (induct xs) auto

lemma set_flatten: "set (flatten xs) = Union (set ` set xs)"
  by (induct xs) auto

lemma loop: "\<forall>x. ((n,x) \<in> calculation s) = (x \<in> set (loop [s] n))"
  proof (induct n)
    case 0 then show ?case using loop_def by simp
  next
    case Suc then show ?case
      using loop_def
      by (intro allI iffI, clarsimp dest!: calculation_downwards)
         (clarsimp dest!: split_list_first spec simp: flatten_append, fastforce simp: set_flatten)
qed

lemma calculation_f: "calculation s = UNION UNIV (\<lambda>x. set (map (\<lambda>y. (x,y)) (loop [s] x)))"
  using loop by fastforce

lemma finite_calculation':
  assumes "finite (calculation s)"
  shows "(\<exists>m. loop [s] m = [])"
  proof -
    have 1: "finite (fst ` (calculation s))" using assms by simp
    then show ?thesis proof -
      obtain x where 2: "x \<in> fst ` calculation s \<and> (\<forall>y. y \<in> fst ` calculation s \<longrightarrow>  y \<le> x)"
        using 1 max_exists by fastforce
      then show ?thesis proof (cases "loop [s] (Suc x)")
        assume "loop [s] (Suc x) = []" then show ?thesis by blast
      next
       fix a l
       assume "loop [s] (Suc x) = a # l"
       then have 3: "(Suc x, a) \<in> calculation s" using loop by simp
       then show ?thesis using 2 3 by fastforce
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
      by (metis (no_types, lifting))
    then have "(UNIV::nat set) = {y. y < m} Un {y. m \<le> y}" by fastforce
    then show ?thesis using 1 calculation_f by (clarsimp elim!: ssubst)
 qed

lemma finite_calculation: "finite (calculation s) = (\<exists>m. loop [s] m = [])"
  using finite_calculation' finite_calculation'' by blast

(**************************************************************************************************)

lemma "(\<exists>x. A x \<or> B x) \<longrightarrow> ((\<exists>x. B x) \<or> (\<exists>x. A x))" by iprover

lemma "((\<exists>x. A x \<or> B x) \<longrightarrow> ((\<exists>x. B x) \<or> (\<exists>x. A x))) = 
  ((\<forall>x. \<not> A x \<and> \<not> B x) \<or> ((\<exists>x. B x) \<or> (\<exists>x. A x)))" by blast

definition test :: "form" where
  "test = Dis (Uni (Con (Neg ''A'' [0]) (Neg ''B'' [0])))
              (Dis (Exi (Pos ''B'' [0])) (Exi (Pos ''A'' [0])))"

lemmas ss =
  append_Cons
  append_Nil
  comp_def
  flatten.simps 
  form.simps
  fresh_def
  fv_list_def
  inference_def
  list.simps
  list_sequent_def
  snd_conv
  split_beta
  substitution.simps
  substitution_bind_def

lemma prover_Nil: "prover []"
  by (metis repeat.simps(1) prover_def)

lemma prover_Cons: "prover (h # t) = prover (inference h @ (flatten \<circ> map inference) t)"
  using repeat_repeat list.simps(8) list.simps(9) flatten.simps
    by (metis (no_types) repeat.simps(2) comp_def prover_def)

corollary finite_calculation_prover: "finite (calculation s) = prover [s]"
  using finite_calculation loop_def prover_def by simp

lemma search: "finite (calculation [(0,test)])"
  unfolding test_def finite_calculation_prover using prover_Nil prover_Cons by (simp only: ss) simp

lemmas magic = soundness completeness finite_calculation_prover

theorem correctness: check_thesis valid_thesis
proof -
  have check_thesis using magic check_def valid_def semantics_alternative.simps by metis
  also have valid_thesis using magic by force
  then show check_thesis valid_thesis using calculation by simp_all
qed

corollary "\<exists>p. check p" "\<exists>p. \<not> check p"
proof -
  have "\<not> valid [Pos '''' []]" "valid [Dis (Pos '''' []) (Neg '''' [])]"
    using valid_def is_model_environment_def by auto
  then show "\<exists>p. check p" "\<exists>p. \<not> check p"
    unfolding correctness using magic check_def correctness(1) by (auto, metis) 
qed

ML \<open>

fun max x y = if x > y then x else y

datatype form = Pos of string * int list | Con of form * form | Uni of form
              | Neg of string * int list | Dis of form * form | Exi of form

fun make_sequent l = map (fn p => (0,p)) l

fun list_sequent s = map snd s

fun member _ [] = false
  | member a (h :: t) = if a = h then true else member a t

fun flatten [] = []
  | flatten (h :: t) = h @ flatten t

fun cut [] = []
  | cut (h :: t) = case h of 0 => cut t | n => n - 1 :: cut t

fun fv (Pos (_,v)) = v
  | fv (Neg (_,v)) = v
  | fv (Con (p,q)) = fv p @ fv q
  | fv (Dis (p,q)) = fv p @ fv q
  | fv (Uni p) = cut (fv p)
  | fv (Exi p) = cut (fv p)

fun max_list [] = 0
  | max_list (h :: t) = max h (max_list t)

fun fresh l = if l = [] then 0 else (max_list l) + 1

fun substitution f (Pos (i,v)) = Pos (i,map f v)
  | substitution f (Neg (i,v)) = Neg (i,map f v)
  | substitution f (Con (p,q)) = Con (substitution f p,substitution f q)
  | substitution f (Dis (p,q)) = Dis (substitution f p,substitution f q)
  | substitution f (Uni p) = Uni (substitution (fn 0 => 0 | n => (f (n - 1)) + 1) p)
  | substitution f (Exi p) = Exi (substitution (fn 0 => 0 | n => (f (n - 1)) + 1) p)

fun substitution_bind p y = substitution (fn 0 => y | n => n - 1) p

fun inference s = case s of [] => [[]] | (n,h) :: t => case h of
      Pos (i,v) => if member (Neg (i,v)) (list_sequent t) then [] else [t @ [(0,Pos (i,v))]]
    | Neg (i,v) => if member (Pos (i,v)) (list_sequent t) then [] else [t @ [(0,Neg (i,v))]]
    | Con (p,q) => [t @ [(0,p)],t @ [(0,q)]]
    | Dis (p,q) => [t @ [(0,p),(0,q)]]
    | Uni p => [t @ [(0,substitution_bind p (fresh ((flatten o map fv) (list_sequent s))))]]
    | Exi p => [t @ [(0,substitution_bind p n),(n + 1,h)]]

fun prover a = if a = [] then true else prover ((flatten o map inference) a)

fun check p = prover [make_sequent [p]]

val test = Dis (Uni (Con (Neg ("A",[0]),Neg ("B",[0]))),
                Dis (Exi (Pos ("B",[0])),Exi (Pos ("A",[0]))))

val _ = check test orelse 0 div 0 = 42

\<close>

(*

export_code make_sequent inference test in SML module_name SimPro file "SimPro.sml"

SML_file "SimPro.sml"

SML_export "val SimPro_inference = SimPro.inference"

SML_export "val SimPro_make_sequent = SimPro.make_sequent"

SML_export "val SimPro_test = SimPro.test"

ML \<open>

fun SimPro_prover a = if a = [] then true else SimPro_prover ((flatten o map SimPro_inference) a);

fun SimPro_check p = SimPro_prover [SimPro_make_sequent [p]]

val _ = SimPro_check SimPro_test orelse 0 div 0 = 42

\<close>

*)

end
