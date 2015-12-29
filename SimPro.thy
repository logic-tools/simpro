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

definition substitution_helper :: "form \<Rightarrow> nat \<Rightarrow> form" where
  "substitution_helper p y = substitution (\<lambda>x. case x of 0 \<Rightarrow> y | Suc n \<Rightarrow> n) p"

definition inference :: "sequent \<Rightarrow> sequent list" where
  "inference s = (case s of [] \<Rightarrow> [[]] | ((n,h) # t) \<Rightarrow> (case h of
      Pos i v \<Rightarrow> if member (Neg i v) (list_sequent t) then [] else [t @ [(0,Pos i v)]]
    | Neg i v \<Rightarrow> if member (Pos i v) (list_sequent t) then [] else [t @ [(0,Neg i v)]]
    | Con p q \<Rightarrow> [t @ [(0,p)],t @ [(0,q)]]
    | Dis p q \<Rightarrow> [t @ [(0,p),(0,q)]]
    | Uni p \<Rightarrow> [t @ [(0,substitution_helper p (fresh ((flatten \<circ> map fv) (list_sequent s))))]]
    | Exi p \<Rightarrow> [t @ [(0,substitution_helper p n),(Suc n,h)]] ))"

primrec repeat :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> 'a" where
  "repeat _ a 0 = a"
| "repeat f a (Suc n) = f (repeat f a n)"

definition prover :: "sequent list \<Rightarrow> bool" where
  "prover a = (\<exists>n. repeat (flatten \<circ> map inference) a n = [])"

definition prover_wrapper :: "form list \<Rightarrow> sequent list" where
  "prover_wrapper l = [make_sequent l]"

abbreviation(input) prover_thesis :: bool where
  "prover_thesis \<equiv> valid = prover \<circ> prover_wrapper"

lemma repeat: "repeat f (f a) n = f (repeat f a n)"
  by (induct n) auto

proposition "(\<exists>n. r (repeat f a n)) = (if r a then True else (\<exists>n. r (repeat f (f a) n)))"
  by (metis repeat.simps repeat not0_implies_Suc)

inductive_set calculation :: "sequent \<Rightarrow> (nat \<times> sequent) set" for s :: sequent where
  init[intro]: "(0,s) \<in> calculation s"
| step[intro]: "(n,k) \<in> calculation s \<Longrightarrow> l \<in> set (inference k) \<Longrightarrow> (Suc n,l) \<in> calculation s"

abbreviation(input) calculation_thesis :: bool where
  "calculation_thesis \<equiv> valid = finite \<circ> calculation \<circ> make_sequent"

lemma "\<forall>e. (is_model_environment m e \<longrightarrow> fst m \<noteq> {})"
  using is_model_environment_def by auto

lemma "\<exists>m. \<forall>e. is_model_environment m e \<and> infinite (fst m)"
  using is_model_environment_def infinite_UNIV_nat by auto

(**************************************************************************************************)

definition fv_list :: "form list \<Rightarrow> nat list" where
  "fv_list = flatten \<circ> map fv"

primrec is_axiom :: "form list \<Rightarrow> bool"
where
  "is_axiom [] = False"
| "is_axiom (a # list) = ((? i v. a = Pos i v \<and> Neg i v : set list) \<or> (? i v. a = Neg i v \<and> Pos i v : set list))"

lemma mm[simp]: "member a l = (a : (set l))" by (induct l) auto

lemma patom:  "(n,(m,Pos i v) # xs) \<in> calculation(nfs) \<Longrightarrow> \<not> is_axiom (list_sequent ((m,Pos i v) # xs)) \<Longrightarrow> (Suc n,xs@[(0,Pos i v)]) \<in> calculation(nfs)"
  and natom:  "(n,(m,Neg i v) # xs) \<in> calculation(nfs) \<Longrightarrow> \<not> is_axiom (list_sequent ((m,Neg i v) # xs)) \<Longrightarrow> (Suc n,xs@[(0,Neg i v)]) \<in> calculation(nfs)"
  and fconj1: "(n,(m,Con f g) # xs) \<in> calculation(nfs) \<Longrightarrow> \<not> is_axiom (list_sequent ((m,Con f g) # xs)) \<Longrightarrow> (Suc n,xs@[(0,f)]) \<in> calculation(nfs)"
  and fconj2: "(n,(m,Con f g) # xs) \<in> calculation(nfs) \<Longrightarrow> \<not> is_axiom (list_sequent ((m,Con f g) # xs)) \<Longrightarrow> (Suc n,xs@[(0,g)]) \<in> calculation(nfs)"
  and fdisj:  "(n,(m,Dis f g) # xs) \<in> calculation(nfs) \<Longrightarrow> \<not> is_axiom (list_sequent ((m,Dis f g) # xs)) \<Longrightarrow> (Suc n,xs@[(0,f),(0,g)]) \<in> calculation(nfs)"
  and fall:   "(n,(m,Uni f) # xs) \<in> calculation(nfs) \<Longrightarrow> \<not> is_axiom (list_sequent ((m,Uni f) # xs)) \<Longrightarrow> (Suc n,xs@[(0,substitution_helper f (fresh ((flatten \<circ> map fv) (list_sequent ((m,Uni f) # xs)))))]) \<in> calculation(nfs)"
  and fex:    "(n,(m,Exi f) # xs) \<in> calculation(nfs) \<Longrightarrow> \<not> is_axiom (list_sequent ((m,Exi f) # xs)) \<Longrightarrow> (Suc n,xs@[(0,substitution_helper f m),(Suc m,Exi f)]) \<in> calculation(nfs)"
  by (auto simp add: inference_def Let_def list_sequent_def comp_def)

lemmas not_is_axiom_subs = patom natom fconj1 fconj2 fdisj fall fex

lemma calculation0[simp]: "(0,x) \<in> calculation y = (x = y)"
  using calculation.cases by blast

lemma calculation_upwards: "(n,list) \<in> calculation s \<Longrightarrow> \<not> is_axiom (list_sequent (list)) \<Longrightarrow> (\<exists>zs. (Suc n, zs) \<in> calculation s \<and> zs : set (inference list))"
  using inference_def apply(case_tac list) apply force
  apply(case_tac a) apply(case_tac b)
       apply(simp add: Let_def) apply(rule) apply(simp add: list_sequent_def) apply(force dest: not_is_axiom_subs)
     apply(simp add: Let_def) apply(force dest: not_is_axiom_subs)
    apply(simp add: Let_def) apply(force dest: not_is_axiom_subs)
      apply(simp add: Let_def) apply(rule) apply(simp add: list_sequent_def) apply(force dest: not_is_axiom_subs)
   apply(simp add: Let_def) apply(force dest: not_is_axiom_subs)
  apply(simp add: Let_def) apply(force dest: not_is_axiom_subs)
  done

lemma calculation_downwards: "(Suc n, x) \<in> calculation s \<Longrightarrow> \<exists>y. (n,y) \<in> calculation s \<and> x : set (inference y) \<and> \<not> is_axiom (list_sequent y)"
  apply(erule calculation.cases)
  apply(simp)
  apply(simp add: list_sequent_def Let_def)
  apply(rule_tac x=k in exI) apply(simp)
  apply(case_tac k) apply(simp)
  apply(case_tac a) apply(case_tac b) 
       apply(auto simp add: Let_def)
   apply (rename_tac[!] nat lista a)
apply(simp only: list_sequent_def inference_def)
   apply(subgoal_tac "Neg nat lista \<in> snd ` set list") apply(simp) apply(force)
  apply(subgoal_tac "Pos nat lista \<in> snd ` set list")
apply(simp only: list_sequent_def inference_def)
apply(simp) apply(force)
  done

lemma calculation_calculation_child[rule_format]: "\<forall>x y. (Suc n,x) \<in> calculation y = (\<exists>z. z : set (inference y) \<and> \<not> is_axiom (list_sequent y) \<and> (n,x) \<in> calculation z)"
  apply(induct n)
   apply(rule, rule) apply(rule) apply(frule_tac calculation_downwards) apply(simp)
   apply(simp) apply(rule step) apply(simp) apply(simp)
  apply(blast dest!: calculation_downwards elim: calculation.cases) -- "blast needs some help with the reasoning, hence calculationSucE"
  done

lemma calculation_progress: "(n,a # list) \<in> calculation s \<Longrightarrow> \<not> is_axiom (list_sequent (a # list)) \<Longrightarrow> (\<exists>zs. (Suc n, list@zs) \<in> calculation s)"
  apply(subgoal_tac "a # list \<noteq> []") prefer 2 apply(simp)
  apply(case_tac a) apply(case_tac b)
       apply(force dest: not_is_axiom_subs)+
  done

definition
  inc :: "nat \<times> sequent \<Rightarrow> nat \<times> sequent" where
  "inc = (\<lambda>(n,fs). (Suc n, fs))"

lemma inj_inc[simp]: "inj inc"
  by (simp add: inc_def inj_on_def)

lemma calculation: "calculation y = insert (0,y) (inc ` (Union (calculation ` {w. \<not> is_axiom (list_sequent y) \<and> w : set (inference y)})))"
  apply(rule set_eqI)
  apply(simp add: split_paired_all)
  apply(case_tac a)
   apply(force simp: inc_def)
  apply(force simp: calculation_calculation_child inc_def)
  done

lemma calculation_is_axiom: "is_axiom (list_sequent s) \<Longrightarrow> calculation s = {(0,s)}"
  apply(rule)
   apply(rule)
   apply(case_tac x) apply(simp)
   apply(erule_tac calculation.induct) apply(force) apply(simp_all add: list_sequent_def) apply(case_tac s) apply(simp) apply(case_tac aa) apply(case_tac ba)
         apply(simp_all add: Let_def list_sequent_def inference_def)
  done
   
lemma is_axiom_finite_calculation: "is_axiom (list_sequent s) \<Longrightarrow> finite (calculation s)"
  by (simp add: calculation_is_axiom)

section "Failing path"

primrec failing_path :: "(nat \<times> sequent) set \<Rightarrow> nat \<Rightarrow> (nat \<times> sequent)"
where
  "failing_path ns 0 = (SOME x. x \<in> ns \<and> fst x = 0 \<and> infinite (calculation (snd x)) \<and> \<not> is_axiom (list_sequent (snd x)))"
| "failing_path ns (Suc n) = (let fn = failing_path ns n in 
  (SOME fsucn. fsucn \<in> ns \<and> fst fsucn = Suc n \<and> (snd fsucn) : set (inference (snd fn)) \<and> infinite (calculation (snd fsucn)) \<and> \<not> is_axiom (list_sequent (snd fsucn))))"

locale loc1 =
  fixes s and f
  assumes f: "f = failing_path (calculation s)"

lemma (in loc1) f0: "infinite (calculation s) \<Longrightarrow> f 0 \<in> (calculation s) \<and> fst (f 0) = 0 \<and> infinite (calculation (snd (f 0))) \<and> \<not> is_axiom (list_sequent (snd (f 0)))"
  by (simp add: f) (metis (mono_tags, lifting) calculation.init is_axiom_finite_calculation fst_conv snd_conv someI_ex)

lemma infinite_union: "finite Y \<Longrightarrow> infinite (Union (f ` Y)) \<Longrightarrow> \<exists>y. y \<in> Y \<and> infinite (f y)"
  by auto

lemma infinite_inj_infinite_image: "inj_on f Z \<Longrightarrow> infinite (f ` Z) = infinite Z"
  by (auto dest: finite_imageD)

lemma inj_inj_on: "inj f \<Longrightarrow> inj_on f A"
  by (blast intro: subset_inj_on)

lemma t: "finite {w. P w} \<Longrightarrow> finite {w. Q w \<and> P w}"
  by (simp add: finite_subset)

lemma finite_subs: "finite {w. \<not> is_axiom (list_sequent y) \<and> w : set (inference y)}"
  by simp

lemma (in loc1) fSuc: "f n \<in> calculation s \<and> fst (f n) = n \<and> infinite (calculation (snd (f n))) \<and> \<not> is_axiom (list_sequent (snd (f n)))
  \<Longrightarrow> f (Suc n) \<in> calculation s \<and> fst (f (Suc n)) = Suc n \<and> (snd (f (Suc n))) : set (inference (snd (f n))) \<and> infinite (calculation (snd (f (Suc n)))) \<and> \<not> is_axiom (list_sequent (snd (f (Suc n))))"
  apply(simp add: Let_def f)
  apply(rule_tac someI_ex)
  apply(simp only: f[symmetric]) 
  apply(drule_tac subst[OF calculation[of "snd (f n)"] ])
  apply(simp only: finite_insert) apply(subgoal_tac "infinite (\<Union>(calculation ` {w. \<not> is_axiom (list_sequent (snd (f n))) \<and> w : set (inference (snd (f n)))}))")
   apply(drule_tac infinite_union[OF finite_subs]) apply(erule exE) apply(rule_tac x="(Suc n, y)" in exI)
   apply(clarify) apply(simp) apply(case_tac "f n") apply(simp add: step) apply(force simp add: is_axiom_finite_calculation)
  apply(force simp add: infinite_inj_infinite_image inj_inj_on) 
  done

lemma (in loc1) is_path_f_0: "infinite (calculation s) \<Longrightarrow> f 0 = (0,s)"
  apply(subgoal_tac "f 0 \<in> calculation s \<and> fst (f 0) = 0")
   prefer 2 apply(frule_tac f0) apply(simp)
  apply(case_tac "f 0") apply(elim conjE, simp)
  done

lemma (in loc1) is_path_f': "infinite (calculation s) \<Longrightarrow> f n \<in> calculation s \<and> fst (f n) = n \<and> infinite (calculation (snd (f n))) \<and> \<not> is_axiom (list_sequent (snd (f n)))"
  by (induct n) (auto simp add: f0 fSuc)

lemma (in loc1) is_path_f: "infinite (calculation s) \<Longrightarrow> \<forall>n. f n \<in> calculation s \<and> fst (f n) = n \<and> (snd (f (Suc n))) : set (inference (snd (f n))) \<and> infinite (calculation (snd (f n)))"
  by (simp add: is_path_f' fSuc)

section "Models"

lemma ball_eq_ball: "\<forall>x \<in> m. P x = Q x \<Longrightarrow> (\<forall>x \<in> m. P x) = (\<forall>x \<in> m. Q x)"
  by blast

lemma bex_eq_bex: "\<forall>x \<in> m. P x = Q x \<Longrightarrow> (\<exists>x \<in> m. P x) = (\<exists>x \<in> m. Q x)"
  by blast

lemma cut[simp]:"Suc n \<in> set A = (n \<in> set (cut A))"
  by (induct A) (simp, case_tac a, simp_all)

lemma FEval_cong: "\<forall>e1 e2. (\<forall>xx. xx \<in> set (fv A) \<longrightarrow> e1 xx = e2 xx) \<longrightarrow> semantics mi e1 A = semantics mi e2 A"
  apply(induct_tac A)
       apply(simp add: Let_def ) apply(intro allI impI) apply(rule arg_cong, rule map_cong) apply(rule) apply(force)
     apply(simp add: Let_def ) apply(intro allI impI) apply(rule conj_cong) apply(force) apply(force)
   apply(simp add: Let_def ) apply(intro allI impI) apply(rule ball_eq_ball) apply(rule) 
   apply(drule_tac x="case_nat z e1" in spec) apply(drule_tac x="case_nat z e2" in spec) apply(erule impE)
    apply(rule) apply(rule) apply(rename_tac x) apply(case_tac x) apply(simp) apply(simp)
   apply(assumption)
      apply(simp add: Let_def ) apply(intro allI impI) apply(rule arg_cong, rule map_cong) apply(rule)  apply(force)
    apply(simp add: Let_def ) apply(intro allI impI) apply(rule disj_cong) apply(force) apply(force)
  apply(simp add: Let_def ) apply(intro allI impI) apply(rule bex_eq_bex) apply(rule)
  apply(drule_tac x="case_nat z e1" in spec) apply(drule_tac x="case_nat z e2" in spec) apply(erule impE)
   apply(rule) apply(rule) apply(rename_tac x) apply(case_tac x) apply(simp) apply(simp)
  apply(assumption)
  done

lemma semantics_alternative_def2: "semantics_alternative m e s = (\<exists>f. f \<in> set s \<and> semantics m e f)"
  by (induct s) auto

lemma semantics_alternative_append: "semantics_alternative m e (xs@ys) = ( (semantics_alternative m e xs) \<or> (semantics_alternative m e ys))"
  by (induct xs) auto

lemma all_eq_all: "\<forall>x. P x = Q x \<Longrightarrow> (\<forall>x. P x) = (\<forall>x. Q x)"
  by blast

lemma fv_list_nil: "fv_list [] = []"
  by (simp add: fv_list_def)

lemma fv_list_cons: "fv_list (a # list) = (fv a) @ (fv_list list)"
  by (simp add: fv_list_def)

lemma semantics_alternative_cong: "(\<forall>x. x \<in> set (fv_list s) \<longrightarrow> e1 x = e2 x) \<longrightarrow> semantics_alternative m e1 s = semantics_alternative m e2 s"
  by (induct s) (simp, metis FEval_cong semantics_alternative.simps(2) Un_iff set_append fv_list_cons)

section "Soundness"

lemma FEval_substitution: "\<forall>e f. (semantics mi e (substitution f A)) = (semantics mi (e \<circ> f) A)"
  apply(induct A)
       apply(simp add: Let_def) apply(simp only: comp_def) apply(blast)
    apply(simp)
   apply(simp) apply(rule,rule) apply(rule ball_eq_ball) apply(rule)
   apply(subgoal_tac "(\<lambda>u. case_nat z e (case u of 0 \<Rightarrow> 0 | Suc n \<Rightarrow> Suc (f n))) = (case_nat z (\<lambda>n. e (f n)))") apply(simp)
   apply(rule ext) apply(case_tac u)
    apply(simp) apply(simp)
      apply(simp add: Let_def) apply(simp only: comp_def) apply(blast)
     apply(simp)
  apply(simp) apply(rule,rule) apply(rule bex_eq_bex) apply(rule)
  apply(subgoal_tac "(\<lambda>u. case_nat z e (case u of 0 \<Rightarrow> 0 | Suc n \<Rightarrow> Suc (f n))) = (case_nat z (\<lambda>n. e (f n)))") apply(simp)
  apply(rule ext) apply(case_tac u)
   apply(simp) apply(simp)
  done

lemma FEval_substitution_helper: "semantics mo e (substitution_helper A u) = semantics mo (case_nat (e u) e) A"
  apply(simp add: substitution_helper_def)
  apply(simp add: FEval_substitution)
  apply(subgoal_tac "(e \<circ> case_nat u (\<lambda>n. n)) = (case_nat (e u) e)") apply(simp)
  apply(rule ext)
  apply(case_tac x, auto)
  done

lemma ball_maxscope: "(\<forall>x \<in> m. P x \<or> Q) \<Longrightarrow> (\<forall>x \<in> m. P x) \<or> Q "
  by simp

lemma sound_FAll: "u \<notin> set (fv_list (Uni f # s)) \<Longrightarrow> valid (s@[substitution_helper f u]) \<Longrightarrow> valid (Uni f # s)"
  apply(simp add: valid_def del: semantics_alternative.simps)
  apply(rule allI) 
  apply(rule allI)
  apply(rename_tac M I)
  apply(rule allI) apply(rule)
  apply(simp)
  apply(simp add: semantics_alternative_append)
  apply(rule ball_maxscope)
  apply(rule)
  apply(simp add: FEval_substitution_helper)

  apply(drule_tac x=M in spec, drule_tac x=I in spec) -- "this is the goal"

  apply(drule_tac x="e(u:=z)" in spec) apply(erule impE) apply(simp add: is_model_environment_def) apply(erule disjE)
   apply(rule disjI2)
   apply(subgoal_tac "semantics_alternative (M,I) (e(u:=z)) s = semantics_alternative (M,I) e s")
    apply(simp)
   apply(rule semantics_alternative_cong[rule_format]) apply(simp add: fv_list_cons) apply(force)

  apply(rule disjI1)
  apply(simp)
  apply(subgoal_tac "semantics (M,I) (case_nat z (e(u:=z))) f = semantics (M,I) (case_nat z e) f")
   apply(simp)
  apply(rule FEval_cong[rule_format])

  apply(case_tac xx, simp)
  apply(simp)
  apply(simp only: cut[rule_format, symmetric])
  apply(subgoal_tac "nat \<in> set (fv (Uni f))") prefer 2 apply(simp)
  
  apply(force simp: fv_list_cons)
  done
    -- "phew, that really was a bit more difficult than expected"
    -- "note that we can avoid maxscoping at the cost of instantiating the hyp twice- an additional time for M"
    -- "different proof, instantiating quantifier twice, avoiding maxscoping --- not much better, probably slightly worse"

lemma sound_FEx: "valid (s@[substitution_helper f u,Exi f]) \<Longrightarrow> valid (Exi f # s)"
  apply(simp add: valid_def del: semantics_alternative.simps)
  apply(rule allI)
  apply(rule allI)
  apply(rename_tac ms m)
  apply(rule) apply(rule)
  apply(simp)
  apply(simp add: semantics_alternative_append)
  apply(simp add: FEval_substitution_helper)

  apply(drule_tac x=ms in spec, drule_tac x=m in spec)
  apply(drule_tac x=e in spec) apply(erule impE) apply(assumption)
  apply(erule disjE)
  apply(simp)
  apply(erule disjE)
   apply(rule disjI1)
   apply(rule_tac x="e u" in bexI) apply(simp) apply(simp add: is_model_environment_def)
  apply(force)
  done

lemma max_exists: "finite (X::nat set) \<Longrightarrow> X \<noteq> {} \<longrightarrow> (\<exists>x. x \<in> X \<and> (\<forall>y. y \<in> X \<longrightarrow> y \<le> x))"
  apply(erule_tac finite_induct) 
  apply(force)
  apply(rule)
  apply(case_tac "F = {}")
  apply(force)
  apply(erule impE) apply(force)
  apply(elim exE conjE)
  apply(rule_tac x="max x xa" in exI)
  apply(rule) apply(simp add: max_def)
  apply(simp add: max_def) apply(force)
  done
  -- "poor max lemmas in lib"

lemma inj_finite_image_eq_finite: "inj_on f Z \<Longrightarrow> finite (f ` Z) = finite Z"
  by (blast intro: finite_imageD)

lemma finite_inc: "finite (inc ` X) = finite X"
  by (metis finite_imageI inj_inc inv_image_comp)

lemma finite_calculation_calculation: "finite (calculation s) \<Longrightarrow> finite  (calculation ` {w. \<not> is_axiom (list_sequent s) \<and> w : set (inference s)})"
  by simp

definition
  init :: "sequent \<Rightarrow> bool" where
  "init s = (\<forall>x \<in> (set s). fst x = 0)"

definition
  is_FEx :: "form \<Rightarrow> bool" where
  "is_FEx f = (case f of
      Pos i v \<Rightarrow> False
    | Neg i v \<Rightarrow> False
    | Con f g \<Rightarrow> False
    | Dis f g \<Rightarrow> False
    | Uni f \<Rightarrow> False
    | Exi f \<Rightarrow> True)"

lemma is_FEx[simp]: "\<not> is_FEx (Pos i v)
  \<and> \<not> is_FEx (Neg i v)
  \<and> \<not> is_FEx (Con f g)
  \<and> \<not> is_FEx (Dis f g)
  \<and> \<not> is_FEx (Uni f)"
  by (simp add: is_FEx_def)

lemma index0: "init s \<Longrightarrow> \<forall>u m A. (n, u) \<in> calculation s \<longrightarrow> (m,A) \<in> (set u) \<longrightarrow> (\<not> is_FEx A) \<longrightarrow> m = 0"
  apply(induct_tac n)
  apply(rule,rule,rule,rule,rule,rule) apply(simp) apply(force simp add: init_def)
  apply(rule,rule,rule,rule,rule,rule)
  -- {*inversion on @{term "(Suc n, u) \<in> calculation s"}*}
  apply(drule_tac calculation_downwards) apply(elim exE conjE)
  apply(case_tac y) apply(simp add: inference_def)
  apply(case_tac a) apply(case_tac b)
       apply(force simp add: Let_def list_sequent_def inference_def)
      apply(force simp add: Let_def list_sequent_def inference_def)
     apply(force simp add: Let_def list_sequent_def inference_def)
    apply(force simp add: Let_def list_sequent_def inference_def)
   apply(force simp add: Let_def list_sequent_def inference_def)
  apply(force simp add: is_FEx_def Let_def list_sequent_def inference_def)
  done

lemma max_list: "\<forall>v \<in> set l. v \<le> max_list l"
  by (induct l) (auto simp add: max_def)

lemma fresh: "fresh l \<notin> (set l)"
  using length_pos_if_in_set max_list fresh_def by force

lemma soundness': "init s \<Longrightarrow> finite (calculation s) \<Longrightarrow> m \<in> (fst ` (calculation s)) \<Longrightarrow> \<forall>y u. (y,u) \<in> (calculation s) \<longrightarrow> y \<le> m \<Longrightarrow> \<forall>n t. h = m - n \<and> (n,t) \<in> calculation s \<longrightarrow> valid (list_sequent t)"
using inference_def fv_list_def
  apply(induct_tac h)
    -- "base case"
   apply(simp) apply(rule,rule,rule) apply(elim conjE)
   apply(subgoal_tac "n=m") prefer 2 apply(force)
   apply(simp)
   apply(simp add: valid_def) apply(rule,rule) apply(rename_tac gs g) apply(rule) apply(rule) apply(simp add: semantics_alternative_def2)
   apply(case_tac "is_axiom (list_sequent t)")
     -- "base case, is axiom"
    apply(simp add: list_sequent_def) apply(case_tac t) apply(simp) apply(simp)
    apply(erule disjE) 
      -- "base case, is axiom, starts with Pos"
     apply(elim conjE exE)
     apply(subgoal_tac "semantics (gs,g) e (Pos i v) \<or> semantics (gs,g) e (Neg i v)")
      apply(erule disjE) apply(force) apply(rule_tac x="Neg i v" in exI) apply(force)
     apply(simp add: Let_def)
      -- "base case, is axiom, starts with Neg"
    apply(elim conjE exE)
    apply(subgoal_tac "semantics (gs,g) e (Pos i v) \<or> semantics (gs,g) e (Neg i v)")
      apply(erule disjE) apply(rule_tac x="Pos i v" in exI) apply(force) apply(force)
    apply(simp add: Let_def) 
    
    -- "base case, not is axiom: if not a satax, then inference holds... but this can't be"
   apply(drule_tac calculation_upwards) apply(assumption) apply(elim conjE exE) apply(force) 
   
     -- "step case, by case analysis"

  apply(intro allI impI) apply(elim exE conjE)

  apply(case_tac "is_axiom (list_sequent t)")
    -- "step case, is axiom"
  apply(simp add: valid_def) apply(rule,rule) apply(rename_tac gs g) apply(rule) apply(rule) apply(simp add: semantics_alternative_def2)
    apply(simp add: list_sequent_def) apply(case_tac t) apply(simp) apply(simp)
    apply(erule disjE)
     apply(elim conjE exE)
     apply(subgoal_tac "semantics (gs,g) e (Pos i v) \<or> semantics (gs,g) e (Neg i v)")
      apply(erule disjE) apply(force) apply(rule_tac x="Neg i v" in exI) apply(blast)
     apply(simp add: Let_def)
    apply(elim conjE exE)
    apply(subgoal_tac "semantics (gs,g) e (Pos i v) \<or> semantics (gs,g) e (Neg i v)")
      apply(erule disjE) apply(rule_tac x="Pos i v" in exI) apply(blast) apply(simp) apply(force)
    apply(simp add: Let_def)

     -- "we hit Uni/ Exi cases first"
  
  apply(case_tac "\<exists>(a::nat) f list. t = (a,Uni f) # list")
   apply(elim exE) apply(simp)
   apply(subgoal_tac "a = 0")
    prefer 2 
    apply(rule_tac n=na and u=t and A="Uni f" in index0[rule_format])
    apply(assumption) apply(simp) apply(simp) apply(simp)
   apply(frule_tac calculation.step) apply(simp add: Let_def)  -- "nice use of simp to instantiate"
   apply(drule_tac x="Suc na" in spec, drule_tac x="list @ [(0, substitution_helper f (fresh ((flatten \<circ> map fv) (list_sequent t))))]" in spec) apply(erule impE, simp)
   apply(subgoal_tac "fresh ((flatten \<circ> map fv)(list_sequent t)) \<notin> set ((flatten \<circ> map fv) (list_sequent t))") 
    prefer 2 apply(rule fresh)
   apply(simp)
   apply(simp add: list_sequent_def inference_def)
   apply(frule_tac sound_FAll) apply(simp) apply(simp)
  
  apply(case_tac "\<exists>a f list. t = (a,Exi f) # list")
   apply(elim exE)
   apply(frule_tac calculation.step) apply(simp add: Let_def) -- "nice use of simp to instantiate"
   apply(drule_tac x="Suc na" in spec, drule_tac x="list @ [(0, substitution_helper f a), (Suc a, Exi f)]" in spec) apply(erule impE, assumption)
   apply(drule_tac x="Suc na" in spec, drule_tac x="list @ [(0, substitution_helper f a), (Suc a, Exi f)]" in spec) apply(erule impE) apply(rule) apply(arith) apply(assumption)
   apply(subgoal_tac "valid (list_sequent (list@[(0,substitution_helper f a), (Suc a, Exi f)]))")
    apply(simp add: list_sequent_def)
    apply(frule_tac sound_FEx) apply(simp) apply(simp)
   
  -- "now for other cases"
      -- "case empty list"
  apply(case_tac t) apply(simp)
   apply(frule_tac step) apply(simp) apply(simp) apply(metis add_Suc_shift add_right_cancel diff_add)
   
  apply(simp add: valid_def) apply(rule,rule) apply(rename_tac gs g) apply(rule) apply(rule) apply(simp add: semantics_alternative_def2)
  -- "na t in calculation, so too is inference"
   -- "if not a satax, then inference holds... "
  apply(case_tac a)
  apply(case_tac b)
       apply(simp del: semantics.simps) apply(frule_tac patom) apply(assumption)
       apply(rename_tac nat lista)
       apply(frule_tac x="Suc na" in spec, drule_tac x="list @ [(0, Pos nat lista)]" in spec)
       apply(erule impE) apply(arith)
       apply(drule_tac x=gs in spec, drule_tac x=g in spec, drule_tac x=e in spec) apply(erule impE) apply(simp add: is_model_environment_def)
       apply(elim exE conjE) apply(rule_tac x=f in exI) apply(simp add: list_sequent_def) -- "weirdly, simp succeeds, force and blast fail"
     apply(simp del: semantics.simps) apply(frule_tac fconj1) apply(assumption) apply(frule_tac fconj2) apply(assumption) 
     apply(rename_tac form1 form2)
     apply(frule_tac x="Suc na" in spec, drule_tac x="list @ [(0, form1)]" in spec)
     apply(erule impE) apply(arith)
     apply(drule_tac x=gs in spec, drule_tac x=g in spec, drule_tac x=e in spec) apply(erule impE, simp) apply(elim exE conjE)
     apply(drule_tac x="Suc na" in spec, drule_tac x="list @ [(0, form2)]" in spec)
     apply(erule impE) apply(arith)
     apply(drule_tac x=gs in spec, drule_tac x=g in spec, drule_tac x=e in spec) apply(erule impE, simp) apply(elim exE conjE)
     apply(simp only: list_sequent_def) 
     apply(simp)
     apply(elim disjE) 
        apply(simp) apply(rule_tac x="Con form1 form2" in exI) apply(simp)
       apply(simp) apply(rule_tac x="fa" in exI) apply(simp)
      apply(simp) apply(rule_tac x="f" in exI) apply(simp)
     apply(rule_tac x="f" in exI, simp)
   apply(force)
      apply(simp del: semantics.simps) apply(frule_tac natom) apply(assumption)
      apply(rename_tac nat lista)
      apply(frule_tac x="Suc na" in spec, drule_tac x="list @ [(0, Neg nat lista)]" in spec)
      apply(erule impE) apply(arith)
      apply(drule_tac x=gs in spec, drule_tac x=g in spec, drule_tac x=e in spec) apply(erule impE, simp)
      apply(elim exE conjE) apply(rule_tac x=f in exI) apply(simp add: list_sequent_def)
    apply(simp del: semantics.simps) apply(frule_tac fdisj) apply(assumption)
    apply(rename_tac form1 form2)
    apply(frule_tac x="Suc na" in spec, drule_tac x="list @ [(0, form1),(0,form2)]" in spec)
    apply(erule impE) apply(simp)
    apply(drule_tac x=gs in spec, drule_tac x=g in spec, drule_tac x=e in spec) apply(erule impE, simp) apply(elim exE conjE)
    apply(simp add: list_sequent_def)
    apply(elim disjE)
      apply(simp) apply(rule_tac x="Dis form1 form2" in exI) apply(simp)
     apply(simp) apply(rule_tac x="Dis form1 form2" in exI) apply(simp)
    apply(rule_tac x="f" in exI) apply(simp)
      -- "all case"
  apply(force)
  done

lemma xxx[simp]: "list_sequent (make_sequent s) = s"
  by (induct s) (simp_all add: list_sequent_def make_sequent_def)

lemma soundness: "finite (calculation (make_sequent s)) \<Longrightarrow> valid s"
  apply(subgoal_tac "init (make_sequent s)") 
   prefer 2 apply(simp add: init_def make_sequent_def)
  apply(subgoal_tac "finite (fst ` (calculation (make_sequent s)))") prefer 2 apply(simp)
  apply(frule_tac max_exists) apply(erule impE) apply(simp) apply(subgoal_tac "(0,make_sequent s) \<in> calculation (make_sequent s)") apply(force) apply(simp)
  apply(elim exE conjE)
  apply(frule_tac soundness') apply(assumption) apply(assumption) apply(force) 
  apply(drule_tac x=0 in spec, drule_tac x="make_sequent s" in spec)
  apply(force )
  done

section "Contains, Considers"

definition contains :: "(nat \<Rightarrow> (nat \<times> sequent)) \<Rightarrow> nat \<Rightarrow> nat \<times> form \<Rightarrow> bool"
where
  "contains f n nf = (nf \<in> set (snd (f n)))"

definition considers :: "(nat \<Rightarrow> (nat \<times> sequent)) \<Rightarrow> nat \<Rightarrow> nat \<times> form \<Rightarrow> bool"
where
  "considers f n nf = (case snd (f n) of [] \<Rightarrow> False | (x # xs) \<Rightarrow> x = nf)"

lemma (in loc1) progress: "infinite (calculation s) \<Longrightarrow> snd (f n) = a # list \<longrightarrow> (\<exists>zs'. snd (f (Suc n)) = list@zs')"
using inference_def apply(subgoal_tac "(snd (f (Suc n))) : set (inference (snd (f n)))") defer apply(frule_tac is_path_f) apply(blast)
  apply(case_tac a)
  apply(case_tac b)
  apply(safe)
  apply(simp_all add: Let_def split: if_splits)
  apply(erule disjE)
  apply(simp_all)
  done

lemma (in loc1) contains_considers': "infinite (calculation s) \<Longrightarrow> \<forall>n y ys. snd (f n) = xs@y # ys \<longrightarrow> (\<exists>m zs'. snd (f (n+m)) = y # zs')"
  apply(induct_tac xs)
  apply(rule,rule,rule,rule) apply(rule_tac x=0 in exI) apply(rule_tac x=ys in exI) apply(force)

  apply(rule,rule,rule,rule) apply(simp) apply(frule_tac progress) apply(erule impE) apply(assumption)
  apply(erule exE) apply(simp) 

  apply(drule_tac x="Suc n" in spec)
  apply(case_tac y) apply(rename_tac u v)
  apply(drule_tac x="u" in spec)
  apply(drule_tac x="v" in spec)
  apply(erule impE) apply(force)
  
  apply(elim exE)
  apply(rule_tac x="Suc m" in exI)
  apply(force)
  done

lemma list_decomp[rule_format]: "v \<in> set p \<longrightarrow> (\<exists>xs ys. p = xs@(v # ys) \<and> v \<notin> set xs)"
  apply(induct p)
  apply(force)
  apply(case_tac "v=a")
   apply(force)
  apply(auto)
  apply(rule_tac x="a # xs" in exI)
  apply(auto)
  done

lemma (in loc1) contains_considers: "infinite (calculation s) \<Longrightarrow> contains f n y \<Longrightarrow> (\<exists>m. considers f (n+m) y)"
  apply(simp add: contains_def considers_def)
  apply(frule_tac list_decomp) apply(elim exE conjE)
  apply(frule_tac contains_considers'[rule_format]) apply(assumption) apply(elim exE)
  apply(rule_tac x=m in exI)
  apply(force)
  done

lemma (in loc1) contains_propagates_patoms[rule_format]: "infinite (calculation s) \<Longrightarrow> contains f n (0, Pos i v) \<longrightarrow> contains f (n+q) (0, Pos i v)"
using inference_def apply(induct_tac q) apply(simp)
  apply(rule)
  apply(erule impE) apply(assumption)
  apply(subgoal_tac "\<not> is_axiom (list_sequent (snd (f (n+na))))") defer
   apply(subgoal_tac "infinite (calculation (snd (f (n+na))))") defer
    apply(force dest: is_path_f)
   defer
   apply(rule) apply(simp add: calculation_is_axiom)
  apply(simp add: contains_def)
  apply(drule_tac p="snd (f (n + na))" in list_decomp) 
  apply(elim exE conjE)
  apply(case_tac xs)
   apply(simp)
   apply(subgoal_tac "(snd (f (Suc (n + na)))) : set (inference (snd (f (n + na))))")
    apply(simp add: Let_def split: if_splits)
   apply(frule_tac is_path_f) apply(drule_tac x="n+na" in spec) apply(force)
  apply(drule_tac progress)
  apply(erule impE) apply(force)
  apply(force)
  done

lemma (in loc1) contains_propagates_natoms[rule_format]: "infinite (calculation s) \<Longrightarrow> contains f n (0, Neg i v) \<longrightarrow> contains f (n+q) (0, Neg i v)"
using inference_def apply(induct_tac q) apply(simp)
  apply(rule)
  apply(erule impE) apply(assumption)
  apply(subgoal_tac "\<not> is_axiom (list_sequent (snd (f (n+na))))") defer
   apply(subgoal_tac "infinite (calculation (snd (f (n+na))))") defer
    apply(force dest: is_path_f)
   defer
   apply(rule) apply(simp add: calculation_is_axiom)
  apply(simp add: contains_def)
  apply(drule_tac p = "snd (f (n + na))" in list_decomp) 
  apply(elim exE conjE)
  apply(case_tac xs)
   apply(simp)
   apply(subgoal_tac "(snd (f (Suc (n + na)))) : set (inference (snd (f (n + na))))")
    apply(simp add: Let_def split: if_splits)
   apply(frule_tac is_path_f) apply(drule_tac x="n+na" in spec) apply(force)
  apply(drule_tac progress)
  apply(erule impE) apply(force)
  apply(force)
  done

lemma (in loc1) contains_propagates_fconj: "infinite (calculation s) \<Longrightarrow> contains f n (0, Con g h) \<Longrightarrow> (\<exists>y. contains f (n+y) (0,g) \<or> contains f (n+y) (0,h))"
  apply(subgoal_tac "(\<exists>l. considers f (n+l) (0,Con g h))") defer apply(rule contains_considers) apply(assumption) apply(assumption)
  apply(erule exE)
  apply(rule_tac x="Suc l" in exI)
  apply(simp add: considers_def) apply(case_tac "snd (f (n + l))", simp)
  apply(simp)
  apply(subgoal_tac "(snd (f (Suc (n + l)))) : set (inference (snd (f (n + l))))")
   apply(simp add: contains_def Let_def inference_def) apply(force)
  apply(frule_tac is_path_f) apply(drule_tac x="n+l" in spec) apply(force)
  done

lemma (in loc1) contains_propagates_fdisj: "infinite (calculation s) \<Longrightarrow> contains f n (0, Dis g h) \<Longrightarrow> (\<exists>y. contains f (n+y) (0,g) \<and> contains f (n+y) (0,h))"
  apply(subgoal_tac "(\<exists>l. considers f (n+l) (0,Dis g h))") defer apply(rule contains_considers) apply(assumption) apply(assumption)
  apply(erule exE)
  apply(rule_tac x="Suc l" in exI)
  apply(simp add: considers_def) apply(case_tac "snd (f (n + l))", simp)
  apply(simp)
  apply(subgoal_tac " (snd (f (Suc (n + l)))) : set (inference (snd (f (n + l))))")
   apply(simp add: contains_def Let_def inference_def) 
  apply(frule_tac is_path_f) apply(drule_tac x="n+l" in spec) apply(force)
  done

lemma (in loc1) contains_propagates_fall: "infinite (calculation s) \<Longrightarrow> contains f n (0, Uni g)
  \<Longrightarrow> (\<exists>y. contains f (Suc(n+y)) (0,substitution_helper g (fresh (fv_list (list_sequent (snd (f (n+y))))))))" -- "may need constraint on fv"
using fv_list_def
  apply(subgoal_tac "(\<exists>l. considers f (n+l) (0,Uni g))") defer apply(rule contains_considers) apply(assumption) apply(assumption)
  apply(erule exE)
  apply(rule_tac x="l" in exI)
  apply(simp add: considers_def) apply(case_tac "snd (f (n + l))", simp)
  apply(simp)
  apply(subgoal_tac "(snd (f (Suc (n + l)))) : set (inference (snd (f (n + l))))")
   apply(simp add: contains_def Let_def inference_def)
  apply(frule_tac is_path_f) apply(drule_tac x="n+l" in spec) apply(force)
  done

lemma (in loc1) contains_propagates_fex: "infinite (calculation s) \<Longrightarrow> contains f n (m, Exi g) 
  \<Longrightarrow> (\<exists>y. (contains f (n+y) (0,substitution_helper g m)) \<and> (contains f (n+y) (Suc m,Exi g)))"
  apply(subgoal_tac "(\<exists>l. considers f (n+l) (m,Exi g))") defer apply(rule contains_considers) apply(assumption) apply(assumption)
  apply(erule exE)
  apply(rule_tac x="Suc l" in exI)
  apply(simp add: considers_def) apply(case_tac "snd (f (n + l))", simp)
  apply(simp)
  apply(subgoal_tac " (snd (f (Suc (n + l)))) : set (inference (snd (f (n + l))))")
   apply(simp add: contains_def Let_def inference_def)
  apply(frule_tac is_path_f) apply(drule_tac x="n+l" in spec) apply(force)
  done

  -- "also need that if contains one, then contained an original at beginning"
  -- "existentials: show that for exists formulae, if Suc m is marker, then there must have been m"
  -- "show this by showing that nodes are upwardly closed, i.e. if never contains (m,x), then never contains (Suc m, x), by induction on n"

lemma (in loc1) FEx_downward: "infinite (calculation s) \<Longrightarrow> init s \<Longrightarrow> \<forall>m. (Suc m,Exi g) \<in> set (snd (f n)) \<longrightarrow> (\<exists>n'. (m, Exi g) \<in> set (snd (f n')))"
using inference_def apply(frule_tac is_path_f)
  apply(induct_tac n)
   apply(drule_tac x="0" in spec) apply(case_tac "f 0") apply(force simp: init_def) 
  apply(intro allI impI)
  apply(frule_tac x="Suc n" in spec, elim conjE) apply(drule_tac x="n" in spec, elim conjE)
  apply(thin_tac "(snd (f (Suc (Suc n)))) : set (inference (snd (f (Suc n))))")
  apply(case_tac "f n") apply(simp)
  apply(case_tac b) apply(simp)
  apply(case_tac aa) apply(case_tac ba)
       apply(simp add: Let_def split: if_splits)
     apply(force simp add: Let_def)
    apply(force simp add: Let_def)
      apply(simp add: Let_def split: if_splits)
   apply(force simp add: Let_def)
  apply(rename_tac form)
  apply(case_tac "(ab, Exi form) = (m, Exi g)")
   apply(rule_tac x=n in exI) apply(force)
  apply(auto simp add: Let_def)
  done
   
lemma (in loc1) FEx0: "infinite (calculation s) \<Longrightarrow> init s \<Longrightarrow> \<forall>n. contains f n (m,Exi g) \<longrightarrow> (\<exists>n'. contains f n' (0, Exi g))"
  apply(simp add: contains_def)
  apply(induct_tac m)
   apply(force)
  apply(intro allI impI) apply(erule exE) 
  apply(drule_tac FEx_downward[rule_format]) apply(assumption) apply(force)
  apply(elim exE conjE)
  apply(force)
  done
     
lemma (in loc1) FEx_upward': "infinite (calculation s) \<Longrightarrow> init s \<Longrightarrow> \<forall>n. contains f n (0, Exi g) \<longrightarrow> (\<exists>n'. contains f n' (m, Exi g))"
  apply(intro allI impI)
  apply(induct_tac m) apply(force)
  apply(erule exE)
  apply(frule_tac n=n' in contains_considers) apply(assumption) 
  apply(erule exE)
  apply(rule_tac x="Suc(n'+m)" in exI)
  apply(frule_tac is_path_f) 
  apply(simp add: considers_def) apply(case_tac "snd (f (n'+m))") apply(force)
  apply(simp)
  apply(drule_tac x="n'+m" in spec)
  apply(force simp add: contains_def considers_def Let_def inference_def)
  done
  -- "FIXME contains and considers aren't buying us much"

lemma (in loc1) FEx_upward: "infinite (calculation s) \<Longrightarrow> init s \<Longrightarrow> contains f n (m, Exi g) \<Longrightarrow> (\<forall>m'. \<exists>n'. contains f n' (0, substitution_helper g m'))"
using inference_def apply(intro allI impI)
  apply(subgoal_tac "\<exists>n'. contains f n' (m', Exi g)") defer
  apply(frule_tac m = m and g = g in FEx0) apply(assumption)
  apply(drule_tac x=n in spec)
  apply(simp)
  apply(elim exE)
  apply(frule_tac g=g and m=m' in FEx_upward') apply(assumption)
  apply (blast dest: contains_propagates_fex intro: elim:)+
  done

section "Models 2"

abbreviation ntou :: "nat \<Rightarrow> proxy" where "ntou \<equiv> id"

abbreviation uton :: "proxy \<Rightarrow> nat" where "uton \<equiv> id"

section "Falsifying Model From Failing Path"

definition model :: "sequent \<Rightarrow> model" where
  "model s = (range ntou, \<lambda> p ms. (let f = failing_path (calculation s) in
    (\<forall>n m. \<not> contains f n (m,Pos p (map uton ms)))))"

locale loc2 = loc1 +
  fixes mo
  assumes mo: "mo = model s"

lemma is_env_model_ntou: "is_model_environment (model s) ntou"
  by (simp add: is_model_environment_def model_def)

lemma (in loc1) [simp]: "infinite (calculation s) \<Longrightarrow> init s \<Longrightarrow> (contains f n (m,A)) \<Longrightarrow> \<not> is_FEx A \<Longrightarrow> m = 0"
  apply(frule_tac n=n in index0) 
  apply(frule_tac is_path_f) apply(drule_tac x=n in spec) apply(case_tac "f n")
  apply(simp)
  apply(simp add: contains_def)
  apply(force)
  done

lemma size_substitution[simp]: "\<forall>m. size (substitution m f) = size f"
  by (induct f) simp_all

lemma size_substitution_helper[simp]: "size (substitution_helper f m) = size f"
  by (simp add: substitution_helper_def)

lemma (in loc2) model': "infinite (calculation s) \<Longrightarrow> init s \<Longrightarrow> \<forall>A. size A = h \<longrightarrow> (\<forall>m n. contains f n (m,A) \<longrightarrow> \<not> (semantics mo ntou A))"

  apply(rule_tac nat_less_induct) apply(rule, rule) apply(case_tac A) 
       apply(rule,rule,rule) apply(simp add: mo Let_def) apply(simp add: model_def Let_def) apply(simp only: f[symmetric]) apply(force)

     apply(intro impI allI)
     apply(subgoal_tac "m=0") prefer 2 apply(simp) apply(simp del: semantics.simps)
     apply(frule_tac contains_propagates_fconj) apply(assumption)
     apply(rename_tac form1 form2 m na)
     apply(frule_tac x="size form1" in spec) apply(erule impE) apply(force) apply(drule_tac x="form1" in spec) apply(drule_tac x="size form2" in spec) apply(erule impE) apply(force) apply(simp)
     apply(force)

   apply(intro impI allI)
   apply(subgoal_tac "m=0") prefer 2 apply(simp) apply(simp del: semantics.simps)
   apply(frule_tac contains_propagates_fall) apply(assumption)
   apply(erule exE) -- "all case"
   apply(rename_tac form m na y)
   apply(drule_tac x="size form" in spec) apply(erule impE, force) apply(drule_tac x="substitution_helper form (fresh (fv_list (list_sequent (snd (f (na + y))))))" in spec) apply(erule impE, force)
   apply(erule impE, force) apply(simp add: FEval_substitution_helper) apply(rule_tac x="ntou (fresh (fv_list (list_sequent (snd (f (na + y))))))" in bexI) apply(simp)
   using is_env_model_ntou[of s] apply(simp add: is_model_environment_def mo)

      apply(rule,rule,rule) apply(simp add: mo Let_def) apply(simp add: model_def Let_def) apply(simp only: f[symmetric]) apply(rule ccontr) apply(simp) apply(elim exE)
      apply(subgoal_tac "m = 0 \<and> ma = 0") prefer 2 apply(simp)
      apply(simp)
      apply(rename_tac nat list m na nb ma)
      apply(subgoal_tac "\<exists>y. considers f (nb+na+y) (0, Pos nat list)") prefer 2 apply(rule contains_considers) apply(assumption) 
       apply(rule contains_propagates_patoms) apply(assumption) apply(assumption)
      apply(erule exE)
      apply(subgoal_tac "contains f (na+nb+y) (0, Neg nat list)")
       apply(subgoal_tac "nb+na=na+nb") 
        apply(simp) apply(subgoal_tac "is_axiom (list_sequent (snd (f (na+nb+y))))")
         apply(drule_tac is_axiom_finite_calculation) apply(force dest: is_path_f)
        apply(simp add: contains_def considers_def) apply(case_tac "snd (f (na + nb + y))") apply(simp) apply(simp add: list_sequent_def) apply(force)
       apply(force)
      apply(force intro: contains_propagates_natoms contains_propagates_patoms)
    apply(intro impI allI)
    apply(subgoal_tac "m=0") prefer 2 apply(simp) apply(simp del: semantics.simps)
    apply(frule_tac contains_propagates_fdisj) apply(assumption)
    apply(rename_tac form1 form2 m na)
    apply(frule_tac x="size form1" in spec) apply(erule impE) apply(force) apply(drule_tac x="form1" in spec) apply(drule_tac x="size form2" in spec) apply(erule impE) apply(force) apply(simp)
    apply(force)

  apply(intro impI allI) apply(simp del: semantics.simps)
  apply(frule_tac FEx_upward) apply(assumption) apply(assumption)
  apply(simp)
  apply(rule)
  apply(rename_tac form m na ma)
  apply(subgoal_tac "\<forall>m'. \<not> semantics mo ntou (substitution_helper form m')") 
   prefer 2 apply(rule)
   apply(drule_tac x="size form" in spec) apply(erule impE, force) 
   apply(drule_tac x="substitution_helper form m'" in spec) apply(erule impE, force) apply(erule impE) apply(force) apply(simp add: id_def)
  apply(simp add: FEval_substitution_helper id_def)
  done
   
lemma (in loc2) model: "infinite (calculation s) \<Longrightarrow> init s \<Longrightarrow> (\<forall>A m n. contains f n (m,A) \<longrightarrow> \<not> (semantics mo ntou A))"
  apply(rule)
  apply(frule_tac model') apply(auto)
  done

section "Completeness"

lemma (in loc2) completeness': "infinite (calculation s) \<Longrightarrow> init s \<Longrightarrow> \<forall>mA \<in> set s. \<not> semantics mo ntou (snd mA)" -- "FIXME tidy calculation s so that s consists of formulae only?"
  apply(frule_tac model) apply(assumption)
  apply(rule)
  apply(case_tac mA)
  apply(drule_tac x="b" in spec) apply(drule_tac x="0" in spec) apply(drule_tac x=0 in spec) apply(erule impE)
   apply(simp add: contains_def) apply(frule_tac is_path_f_0) apply(simp) 
   apply(subgoal_tac "a=0") 
    prefer 2 apply(simp only: init_def, force)
  apply auto
  done -- "FIXME very ugly"

lemma completeness': "infinite (calculation s) \<Longrightarrow> init s \<Longrightarrow> \<forall>mA \<in> set s. \<not> semantics (model s) ntou (snd mA)"
  by (rule loc2.completeness'[simplified loc2_def loc2_axioms_def loc1_def]) simp

lemma completeness'': "infinite (calculation (make_sequent s)) \<Longrightarrow> init (make_sequent s) \<Longrightarrow> \<forall>A. A \<in> set s \<longrightarrow> \<not> semantics (model (make_sequent s)) ntou A"
  using completeness' make_sequent_def by force

lemma completeness: "infinite (calculation (make_sequent s)) \<Longrightarrow> \<not> valid s"
  apply(subgoal_tac "init (make_sequent s)") 
   prefer 2 apply(simp add: init_def make_sequent_def)
  apply(frule_tac completeness'') apply(assumption)
  apply(simp add: valid_def)
  apply(simp add: semantics_alternative_def2)
  apply(rule_tac x="fst (model (make_sequent s))" in exI)
  apply(rule_tac x="snd (model (make_sequent s))" in exI)
  apply(rule_tac x="ntou" in exI)
  apply(simp add: model_def)
  apply(simp add: is_model_environment_def)
  done
-- "FIXME silly splitting of quantified pairs "

section "Algorithm"

definition loop :: "sequent list \<Rightarrow> nat \<Rightarrow> sequent list"
where
  "loop s n = repeat (flatten \<circ> map inference) s n"

lemma loop_upwards: "loop s n = [] \<Longrightarrow> loop s (n+m) = []"
  by (induct m) (auto simp add: loop_def)

lemma flatten_append: "flatten (xs@ys) = ((flatten xs) @ (flatten ys))"
  by (induct xs) auto

lemma set_flatten: "set (flatten xs) = Union (set ` set xs)"
  by (induct xs) auto

lemma loop: "\<forall>x. ((n,x) \<in> calculation s) = (x \<in> set (loop [s] n))"
  apply(induct n)
  apply(simp) apply(simp add: loop_def)
  apply(rule)
  apply(rule)
   apply(drule_tac calculation_downwards)
   apply(elim exE conjE)
   apply(drule_tac x=y in spec)
   apply(simp)
   apply(drule_tac list_decomp) apply(elim exE conjE)
   apply(simp add: flatten_append loop_def Let_def)
  apply(simp add: loop_def)
  apply(simp add: set_flatten)
  apply(erule bexE)
  apply(drule_tac x=a in spec)
  apply(rule step) apply(auto)
  done

lemma calculation_f: "calculation s = UNION UNIV (\<lambda>x. set (map (\<lambda>y. (x,y)) (loop [s] x)))"
  by (force simp add: loop)  

lemma finite_calculation: "finite (calculation s) = (\<exists>m. loop [s] m = [])"
  apply(rule)
   apply(subgoal_tac "finite (fst ` (calculation s))") prefer 2 apply(simp)
   apply(frule_tac max_exists) apply(erule impE) apply(simp) apply(subgoal_tac "(0,s) \<in> calculation s") apply(force) apply(simp)
   apply(elim exE conjE)
   apply(rule_tac x="Suc x" in exI)
   apply(simp)
   apply(rule ccontr) apply(case_tac "loop [s] (Suc x)") apply(simp) 
   apply(subgoal_tac "(Suc x, a) \<in> calculation s") apply(force)
   apply(simp add: loop)
  apply(erule exE)
  apply(subgoal_tac "\<forall>y. loop [s] (m+y) = []") 
   prefer 2 apply(rule) apply(rule loop_upwards) apply(assumption)
  apply(simp add: calculation_f)
  apply(subgoal_tac "(UNIV::nat set) = {y. y < m} Un {y. m \<le> y}")
   prefer 2 apply force
  apply(erule_tac t="UNIV::nat set" in ssubst) 
  apply(simp)
  apply(subgoal_tac "(UN x:Collect (op \<le> m). Pair x ` set (loop [s] x)) =  (UN x:Collect (op \<le> m). {})") apply(simp only:) apply(force)
  apply(rule SUP_cong) apply(force) apply(drule_tac x="x-m" in spec) apply(force)
  done

(**************************************************************************************************)

lemma "(\<exists>x. A x \<or> B x) \<longrightarrow> ((\<exists>x. B x) \<or> (\<exists>x. A x))" by iprover

lemma "((\<exists>x. A x \<or> B x) \<longrightarrow> ((\<exists>x. B x) \<or> (\<exists>x. A x))) =
  ((\<forall>x. \<not> A x \<and> \<not> B x) \<or> ((\<exists>x. B x) \<or> (\<exists>x. A x)))" by blast

definition test :: "form" where
  "test = Dis
    (Uni (Con (Neg ''A'' [0]) (Neg ''B'' [0])))
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
  substitution_helper_def

lemma prover_Nil: "prover []"
  by (metis repeat.simps(1) prover_def)

lemma prover_Cons: "prover (h # t) = prover (inference h @ (flatten \<circ> map inference) t)"
  using repeat list.simps(8) list.simps(9) flatten.simps
  by (metis (no_types) repeat.simps(2) comp_def prover_def)

corollary finite_calculation_prover: "finite (calculation s) = prover [s]"
  using finite_calculation loop_def prover_def by simp

lemma search: "finite (calculation [(0,test)])"
  unfolding test_def finite_calculation_prover using prover_Nil prover_Cons by (simp only: ss) simp

ML \<open>

fun max x y = if x > y then x else y;

datatype form = Pos of string * int list | Con of form * form | Uni of form
              | Neg of string * int list | Dis of form * form | Exi of form;

fun make_sequent l = map (fn p => (0,p)) l;

fun list_sequent s = map snd s;

fun member _ [] = false
  | member a (h :: t) = if a = h then true else member a t;

fun flatten [] = []
  | flatten (h :: t) = h @ flatten t;

fun cut [] = []
  | cut (h :: t) = case h of 0 => cut t | n => n - 1 :: cut t;

fun fv (Pos (_,v)) = v
  | fv (Neg (_,v)) = v
  | fv (Con (p,q)) = fv p @ fv q
  | fv (Dis (p,q)) = fv p @ fv q
  | fv (Uni p) = cut (fv p)
  | fv (Exi p) = cut (fv p);

fun max_list [] = 0
  | max_list (h :: t) = max h (max_list t);

fun fresh l = if l = [] then 0 else (max_list l) + 1;

fun substitution f (Pos (i,v)) = Pos (i,map f v)
  | substitution f (Neg (i,v)) = Neg (i,map f v)
  | substitution f (Con (p,q)) = Con (substitution f p,substitution f q)
  | substitution f (Dis (p,q)) = Dis (substitution f p,substitution f q)
  | substitution f (Uni p) = Uni (substitution (fn 0 => 0 | n => (f (n - 1)) + 1) p)
  | substitution f (Exi p) = Exi (substitution (fn 0 => 0 | n => (f (n - 1)) + 1) p);

fun substitution_helper p y = substitution (fn 0 => y | n => n - 1) p;

fun inference s = case s of [] => [[]] | ((n,h) :: t) => case h of
      Pos (i,v) => if member (Neg (i,v)) (list_sequent t) then [] else [t @ [(0,Pos (i,v))]]
    | Neg (i,v) => if member (Pos (i,v)) (list_sequent t) then [] else [t @ [(0,Neg (i,v))]]
    | Con (p,q) => [t @ [(0,p)],t @ [(0,q)]]
    | Dis (p,q) => [t @ [(0,p),(0,q)]]
    | Uni p => [t @ [(0,substitution_helper p (fresh ((flatten o map fv) (list_sequent s))))]]
    | Exi p => [t @ [(0,substitution_helper p n),(n + 1,h)]];

fun prover a = if a = [] then true else prover ((flatten o map inference) a);

fun prover_wrapper l = [make_sequent l];

fun check p = (prover o prover_wrapper) [p];

val test = Dis (
  (Uni (Con ((Neg ("A",[0])), (Neg ("B",[0])))),
  (Dis ((Exi ((Pos ("B",[0])))), (Exi (Pos ("A",[0])))))));

check test orelse 0 div 0 = 42;

\<close>

theorem correctness: prover_thesis calculation_thesis
  using soundness completeness finite_calculation_prover
  by (auto simp add: prover_wrapper_def comp_def)

abbreviation check :: "form \<Rightarrow> bool" where
  "check p \<equiv> (prover \<circ> prover_wrapper) [p]"

corollary "\<exists>p. check p" "\<exists>p. \<not> check p"
proof -
  have "\<not> valid [Pos '''' []]" "valid [Dis (Pos '''' []) (Neg '''' [])]"
    using valid_def is_model_environment_def by auto
  then show "\<exists>p. check p" "\<exists>p. \<not> check p" unfolding correctness by auto
qed

proposition "check p = (\<forall>m e. is_model_environment m e \<longrightarrow> semantics m e p)"
  using valid_def unfolding correctness by simp

end
