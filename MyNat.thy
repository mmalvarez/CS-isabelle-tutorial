theory MyNat imports Main
begin

(* This is the first part of the workshop, introducing some basic concepts of
   Isabelle through some small examples about natural numbers *)

(*
   Unary natural numbers
*)

datatype mynat =
  M0
  | MS "mynat"

(* This looks simple, right? In fact, Isabelle is doing a lot of work behind the scenes
   to present us with the ability to define datatypes this way. Try querying "name:mynat"
   (without quotes) in the "find theorems" pane if you don't believe me :)
*)

fun mynatD :: "mynat \<Rightarrow> nat" where
"mynatD M0 = 0"
| "mynatD (MS m') = 1 + mynatD m'"

fun mynat_plus :: "mynat \<Rightarrow> mynat \<Rightarrow> mynat" where
"mynat_plus M0 x = x"
| "mynat_plus (MS x1) x2 = mynat_plus x1 (MS x2)"

fun mynat_minus :: "mynat \<Rightarrow> mynat \<Rightarrow> mynat" where
"mynat_minus M0 x2 = M0"
| "mynat_minus x1 (M0) = x1"
| "mynat_minus (MS x1) (MS x2) =
   mynat_minus x1 x2"

function (sequential) mynat_minus' :: "mynat \<Rightarrow> mynat \<Rightarrow> mynat" where
"mynat_minus' M0 x2 = M0"
| "mynat_minus' x1 (M0) = x1"
| "mynat_minus' (MS x1) (MS x2) =
   mynat_minus' x1 x2"
  by pat_completeness auto

(*termination by lexicographic_order*)
(* termination by size_change *)

termination
proof(relation "measure (\<lambda> (n1, n2) . mynatD n1)")
  show "wf (measure (\<lambda>(n1, n2). mynatD n1))"
    by auto
next
  fix x1 x2
  show "((x1, x2), MS x1, MS x2) \<in> measure (\<lambda>(n1, n2). mynatD n1)"
    by auto
qed

lemma mynat_plus_correct :
  "mynatD (mynat_plus x1 x2) =
   mynatD x1 + mynatD x2"
proof(induction x1 arbitrary: x2)
case M0
  then show ?case by(auto)
next
  case (MS x1)
    (*  then show ?case by auto *)

    (* let's be pedantic and look at a more manual argument. *)
  show ?case
    unfolding mynat_plus.simps
    using MS.prems MS.IH[of "MS x2"]
    unfolding mynatD.simps
    by simp (* Isabelle's arithmetic automation handles things from here. *)
qed

fun mynat_times :: "mynat \<Rightarrow> mynat \<Rightarrow> mynat" where
"mynat_times M0 _ = M0"
| "mynat_times (MS x) y = mynat_plus y (mynat_times x y)"

(* checking results of a computation is easy!
   (We can generate Haskell/ML code using a related mechanism) *)
(* 2 * 3 = 6 *)
value "mynatD (mynat_times (MS (MS (MS M0))) (MS (MS M0)))"


(*
 * Inductive predicates: evenness and oddness
 *)

(* other uses of induction in isabelle: inductive predicates! *)
inductive myeven :: "mynat \<Rightarrow> bool" and
          myodd :: "mynat \<Rightarrow> bool" where
"myeven M0"
| "myeven x \<Longrightarrow> myodd (MS x)"
| "myodd x \<Longrightarrow> myeven (MS x)"

(* an example of an apply-style proof - 
   good for experimentation, but less maintainable. *)
lemma three_odd : "myodd (MS (MS (MS (M0))))"
  apply(rule myeven_myodd.intros)
  apply(rule myeven_myodd.intros)
  apply(rule myeven_myodd.intros)
  apply(rule myeven_myodd.intros)
  done

(* or, more automated: *)
lemma three_odd' : "myodd (MS (MS (MS (M0))))"
  by(auto intro: myeven_myodd.intros)

definition mynat_two :: "mynat" where
"mynat_two = MS (MS (M0))"

(* we could have defined even and odd differently: *)

(* definition is used for defining non-recursive things *)
definition myeven' :: "mynat \<Rightarrow> bool" where
"myeven' x =  (\<exists> x' . x = mynat_times mynat_two x')"

definition myodd' :: "mynat \<Rightarrow> bool" where
"myodd' x = (\<exists> x' . x = MS (mynat_times mynat_two x'))"

(* which is better? the non-inductive definitions tend to be easier to
   compute with, but at the cost of potentially obscuring the inductive structure
   of the predicates, which may complicate some proofs *)

(* exercise, possibly annoying: show these definitions are equivalent *)

(*
 * Rational numbers: a taste of Isabelle typedefs
 *)


(* Originally I was going to try to show this proof using the natural numbers developed
   above, but the details of the proof got annoying. *)

(* isabelle's answer to dependent types: subset types!
   all types (even mynat, e.g.), except for some extremely basic ones,
   are defined "under the hood" as
   nonempty subsets of different
   existing types *)


definition coprime :: "nat \<Rightarrow> nat \<Rightarrow> bool" where
"coprime x y =
  (\<forall> n x' y' . n * x' = x \<longrightarrow> n * y' = y \<longrightarrow> n = 1)"

(* convenience lemma for more easily applying coprime in Isabelle proof scripts (see below)
   "E" stands for eliminator (though this might technically be a destructor)
 *)
lemma coprimeE :
  assumes H : "coprime x y"
  assumes Hx : "n * x' = x"
  assumes Hy : "n * y' = y"
  shows "n = 1" using assms
  unfolding coprime_def by auto

lemma mul_bound :
  fixes a b c :: nat
  assumes H1 : "a * b = c"
  assumes H2 : "c \<noteq> 0"
  shows "a \<le> c" using assms
proof-

  have Bnz : "1 \<le> b" using H1 H2
    by(cases b; auto)

  hence "1 * a \<le> b * a" by auto

  thus "a \<le> c" using H1 by  auto
qed

typedef myrat = "{xy :: (nat * nat) .
                  (case xy of (x, y) \<Rightarrow> coprime x y)}"
(* cool, but now we need to show this set isn't empty
   (no, there is no empty/False type in Isabelle's logic - another key
    difference from CiC/dependent types based systems.)
*)
proof-
  have "coprime 2 3" unfolding coprime_def
  proof(step+)
    fix n x' y' :: nat
    assume Hx : "n * x' = 2"
    assume Hy : "n * y' = 3"

    have Xnz : "0 < x'" using Hx by (cases x'; auto)
    have Ynz : "0 < y'" using Hy by (cases y'; auto)
    have Nnz : "0 < n" using Hy by (cases n; auto)

    have Bound : "n \<le> 2" using mul_bound[OF Hx] by auto

    show "n = 1"
    proof(cases n)
      case 0
      then show ?thesis using Nnz by auto
    next
      case Suc1 : (Suc n')
      then show ?thesis
      proof(cases n')
        case 0 (* n = 1 *)
        then show ?thesis using Suc1 by auto
      next
        case Suc2 : (Suc n'') 
        then show ?thesis
        proof(cases n'')
          case 0 (* n = 2 is the only interesting case really *)

          hence N2 : "n = 2" using Suc1 Suc2 by auto

          have Hy' : "y' * n = 3" using Hy by(simp add: mult.commute)

          have Bound' : "y' \<le> 3" using mul_bound[OF Hy'] by auto

          (* out of laziness i am not going to write out the full case analysis on y here *)
          then show ?thesis using N2 Hy'
            by(cases y'; auto)
        next
          case Suc3 : (Suc n''')
          then show ?thesis using Suc1 Suc2 Suc3 Bound by auto
        qed
      qed
    qed
  qed

  then show "\<exists>x. x \<in> {xy. case xy of (x, y) \<Rightarrow> MyNat.coprime x y}"
    by auto
qed

(* luckily Isabelle provides primitives for working with typedef'd types more
   conveniently - handles a lot of annoying bookkeeping that comes with converting
   between (nat * nat) and myrat, which while the same structurally are
   different types from Isabelle's point of view. *)
setup_lifting type_definition_myrat

(* an example of an "admitted" theorem.
   be careful with these, you can "prove" absurdities!
   proving this may be annoying because we may need to show a bunch of basic
   mathematical identities. As we'll see below, Isabelle's standard library
   contains such theorems, which is a good reason to use the standard natural
   numbers (and other datatypes too) instead of rolling your own
*)
lemma coprime_square : "coprime a b \<Longrightarrow> coprime (a * a) (b * b)" sorry

definition rat_square' :: "(nat * nat) \<Rightarrow> (nat * nat)" where
"rat_square' xy =
  (case xy of (x, y) \<Rightarrow> ((x * x), (y * y)))"


(* a lifted definition, giving us a function we can use on the typedef'd type *)
lift_definition rat_square :: "myrat \<Rightarrow> myrat" is rat_square'
  using coprime_square unfolding rat_square'_def  
  by(auto)


(*
 * A (sort of) interesting theorem: square root of 2 is irrational
 *)

(* we could use what we developed above to prove that sqrt(2) is irrational, but let's simplify
   things again and just express this directly on natural numbers. 
   this will let us use some library theorems.

   note the number of library lemmas we end up using here
   (a fun exercise might be seeing if the automation can get through parts of this proof
    with less hand-holding - although arguably the result would be a less clear proof)
*)

lemma sqrt2_irrational :
  fixes x :: nat
  fixes y :: nat
  assumes Coprime : "coprime x y"
  assumes Hxy : "x * x = 2 * y * y"
  shows False
proof-
  have  "(2 * y * y) mod 2 = 0" using Hxy mod_mult_self2_is_0[of "y * y" 2] by auto
  hence "x * x mod 2 = 0" using Hxy by auto

  hence Xeven : "x mod 2 = 0" using sym[OF mod_mult_eq[of x 2 x]] by auto

  obtain x' where X' : "x = 2 * x'"
    using mod_eq_0D[OF Xeven] by auto

  then have "4 * x' * x' = 2 * y * y" using Hxy by auto

  then have Hxy' : "2 * x' * x' = y * y" by auto

(* now we repeat the above argument to show y must be even and derive a contradiction *)
  have  "(2 * x' * x') mod 2 = 0" using Hxy mod_mult_self2_is_0[of "x' * x'" 2] by auto
  hence "y * y mod 2 = 0" using Hxy' by auto

  hence Yeven : "y mod 2 = 0" using sym[OF mod_mult_eq[of x 2 x]] by auto

  obtain y' where Y' : "y = 2 * y'"
    using mod_eq_0D[OF Yeven] by auto

  (* unfolding the definition of Coprime into Isabelle's meta-logic in order to
     make it easier to work with here - this could be done as a separate lemma
     (in fact there's probably automation for it, I just don't know how to use it. *)
  show False using coprimeE[OF Coprime, of 2 x' y'] X' Y' by auto
qed 
    

end