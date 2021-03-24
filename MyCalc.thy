theory MyCalc imports Main
begin

(* For the second part of the workshop, let's have a look at a more typical
   task that might arise in software verification. *)

(* Here's a very simple four-function calculator language
   (something like this might be useful e.g. in modeling expressions in a larger language *)

datatype calc =
  N nat
  | Add calc calc
  | Sub calc calc
  | Mul calc calc
  | Div calc calc (* normal natural-number division; that is, round down *)

(*
  We give a semantics to this language by showing how it maps into computation in
  Isabelle. We call this a _denotational semantics_ because it maps (or _denotes_)
  that mathematical meaning of calc expressions directly into Isabelle's logic.

  Note that we can only get away with this because calc is a language of terminating
  programs. If we wanted to express nonterminating programs, we would need to deal with the
  fact that Isabelle functions (generally) need to terminate in order to be convenient to
  reason about. There are several standard ways to do this, one of the most common being
  to give nonterminating interpreters an extra "fuel" argument (usually a natural number)
  that decreases with each iteration, establishing termination.
*)

fun calcD :: "calc \<Rightarrow> nat" where
"calcD (N n) = n"
| "calcD (Add c1 c2) = calcD c1 + calcD c2"
| "calcD (Sub c1 c2) = calcD c1 - calcD c2"
| "calcD (Mul c1 c2) = calcD c1 * calcD c2"
| "calcD (Div c1 c2) = divide_nat_inst.divide_nat (calcD c1) (calcD c2)"

(* We can run some computations in this language if we like *)
value "calcD (Add (Add (N 1) (N 1)) (Mul (N 4) (N 10)))"


(* Now that we have a semantics of this language in Isabelle - a system amenable to proofs -
   there are some interesting things we can do. For instance, we might notice that some
   programs can be simplified according to arithmetic identities. For instance,
   (Add (N 0) x) = x
   for any calc expression x.
   Let's define a program transformation capturing this "insight."
*)

fun calc_simplify_addzero :: "calc \<Rightarrow> calc" where
"calc_simplify_addzero (N n) = N n"
| "calc_simplify_addzero (Add (N n) c2) = 
    (if n = 0 then calc_simplify_addzero c2
     else Add (N n) (calc_simplify_addzero c2))"
| "calc_simplify_addzero (Add c1 c2) = 
    Add (calc_simplify_addzero c1) (calc_simplify_addzero c2)"
| "calc_simplify_addzero (Sub c1 c2) = 
    Sub (calc_simplify_addzero c1) (calc_simplify_addzero c2)"
| "calc_simplify_addzero (Mul c1 c2) =
    Mul (calc_simplify_addzero c1) (calc_simplify_addzero c2)"
| "calc_simplify_addzero (Div c1 c2) =
    Div (calc_simplify_addzero c1) (calc_simplify_addzero c2)"


value "calc_simplify_addzero (Add (N 1) (Add (N 0) (N 1)))"

(* Exercise: will this transformation ever yield programs that still contain expressions
   of the form (Add (N 0) x)? When does this happen? How can we fix this?
*)

(* Next, we'd like to show this transformation is correct. Fortunately it's quite clear
   what we mean by that in this case - the semantics of the program
   (i.e., the result of running calcD) should be the same before and after the
   transformation. Let's capture this in a lemma and try to prove it. *)

lemma calc_simplify_addzero_correct :
  "calcD c = calcD (calc_simplify_addzero c)"
proof(induction c)
case (N x)
  then show ?case by auto
next
  (* the interesting case, of course. *)
  case (Add c1 c2)
  show ?case
  (* this way of expressing the proof is rather pedantic and longer than it needs to be -
     trying to cut it down might be an interesting exercise (bonus points for not using
     apply-style tactics in doing so. *)
  proof(cases c1)
    case (N x1)
    show ?thesis
    proof(cases "x1 = 0")
      case True
      then show ?thesis using Add N by(auto)
    next
      case False
      then show ?thesis using Add N by(auto)
    qed
  next
    case Add' : (Add x21 x22) (* we can name our cases - useful for avoiding collisions *)
    then show ?thesis using Add by auto
  next
    case (Sub x31 x32)
    then show ?thesis using Add by auto
  next
    case (Mul x41 x42)
    then show ?thesis using Add by auto
  next
    case (Div x51 x52)
    then show ?thesis using Add by auto
  qed
next
  case (Sub c1 c2)
  then show ?case by auto
next
  case (Mul c1 c2)
  then show ?case by auto
next
  case (Div c1 c2)
  then show ?case by auto
qed


(* Exercise : can you prove the transformation corresponding to the identity
   "1 * x = x"?
*)

(* Exercise : what about "a * b + c * b = (a + c) * b?
*)


end