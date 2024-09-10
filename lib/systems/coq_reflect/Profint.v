Require Import List.
Import ListNotations.

Inductive side : Type := Pos | Neg.

Definition flip side :=
  match side with Pos => Neg | _ => Pos end.

Polymorphic Inductive ctx : side -> list Type -> Type :=
| Hole           : ctx Pos nil
| AndL side Ts   : ctx side Ts -> Prop -> ctx side Ts
| AndR side Ts   : Prop -> ctx side Ts -> ctx side Ts
| OrL side Ts    : ctx side Ts -> Prop -> ctx side Ts
| OrR side Ts    : Prop -> ctx side Ts -> ctx side Ts
| ImpL side Ts   : ctx (flip side) Ts -> Prop -> ctx side Ts
| ImpR side Ts   : Prop -> ctx side Ts -> ctx side Ts
| AllD A side Ts : (A -> ctx side Ts) -> ctx side (A :: Ts)
| ExD A side Ts  : (A -> ctx side Ts) -> ctx side (A :: Ts).

Reserved Notation "Cx '{{' P '}}'" (at level 1, format "'[ ' Cx '{{'  P  '}}' ']'").

Fixpoint ho_absract (Ts : list Type) (U : Type) : Type :=
  (* match Ts return Type with *)
  match Ts with
  | nil => U
  | A :: Ts => A -> ho_absract Ts U
  end.
Notation "Ts ▷ U" := (ho_absract Ts U) (at level 100, right associativity).

Fixpoint ctx_place side Ts (ctx : ctx side Ts) : (Ts ▷ Prop) -> Prop :=
  (* match ctx in (ctx _ Us) return (Us ▷ Prop) -> Prop with *)
  match ctx with
  | Hole => fun p => p
  | AndL _ _ ctx q => fun p => ctx{{ p }} /\ q
  | AndR _ _ q ctx => fun p => q /\ ctx{{ p }}
  | OrL _ _ ctx q => fun p => ctx{{ p }} \/ q
  | OrR _ _ q ctx => fun p => q \/ ctx{{ p }}
  | ImpL _ _ ctx q => fun p => ctx{{ p }} -> q
  | ImpR _ _ q ctx => fun p => q -> ctx{{ p }}
  | AllD A _ _ ctx => fun p => forall (x : A), (ctx x){{ p x }}
  | ExD A _ _ ctx => fun p => exists (x : A), (ctx x){{ p x }}
  end
where "Cx {{ P }}" := (@ctx_place _ _ Cx P).

Fixpoint ho_impl (Ts : list Type) : (Ts ▷ Prop) -> (Ts ▷ Prop) -> (Ts ▷ Prop) :=
  match Ts with
  | nil => (fun p q => p -> q)
  | A :: Ts => (fun (p q : A -> (Ts ▷ Prop)) (x : A) => ho_impl Ts (p x) (q x))
  end.

Fixpoint ho_and (Ts : list Type) : (Ts ▷ Prop) -> (Ts ▷ Prop) -> (Ts ▷ Prop) :=
  match Ts with
  | nil => (fun p q => p /\ q)
  | A :: Ts => (fun (p q : A -> (Ts ▷ Prop)) (x : A) => ho_and Ts (p x) (q x))
  end.

Fixpoint ho_true (Ts : list Type) : Ts ▷ Prop :=
  match Ts with
  | nil => True
  | A :: Ts => (fun (_ : A) => ho_true Ts)
  end.

Fixpoint ho_or (Ts : list Type) : (Ts ▷ Prop) -> (Ts ▷ Prop) -> (Ts ▷ Prop) :=
  match Ts with
  | nil => (fun p q => p \/ q)
  | A :: Ts => (fun (p q : A -> (Ts ▷ Prop)) (x : A) => ho_or Ts (p x) (q x))
  end.

Fixpoint ho_false (Ts : list Type) : Ts ▷ Prop :=
  match Ts with
  | nil => False
  | A :: Ts => (fun (_ : A) => ho_false Ts)
  end.

Fixpoint ho_all (A : Type) (Ts : list Type) : (A -> (Ts ▷ Prop)) -> (Ts ▷ Prop) :=
  match Ts with
  | nil => (fun p => forall (x : A), p x)
  | B :: Ts => (fun p (x : B) => ho_all A Ts (fun u => p u x))
  end.

Fixpoint ho_ex (A : Type) (Ts : list Type) : (A -> (Ts ▷ Prop)) -> (Ts ▷ Prop) :=
  match Ts with
  | nil => (fun p => exists (x : A), p x)
  | B :: Ts => (fun p (x : B) => ho_ex A Ts (fun u => p u x))
  end.

Fixpoint ho_eq (A : Type) (Ts : list Type) : (Ts ▷ A) -> (Ts ▷ A) -> (Ts ▷ Prop) :=
  match Ts with
  | nil => (fun s t => @eq A s t)
  | B :: Ts => (fun s t (x : B) => ho_eq A Ts (s x) (t x))
  end.

Fixpoint ho_entails (Ts : list Type) : (Ts ▷ Prop) -> (Ts ▷ Prop) -> Prop :=
  match Ts with
  | nil => (fun p q => p -> q)
  | A :: Ts => (fun p q => forall (x : A), ho_entails Ts (p x) (q x))
  end.

Module HONotations.
  Notation "f → g" :=
    (ho_impl _ f g)
      (at level 99, right associativity, g at level 200).
  Notation "f ∧ g" :=
    (ho_and _ f g)
      (at level 80, right associativity).
  Notation "⊤" := (ho_true _) (at level 0).
  Notation "f ∨ g" :=
    (ho_or _ f g)
      (at level 85, right associativity).
  Notation "⊥" := (ho_false _) (at level 0).
  Notation "∀ x .. y , p" :=
    (ho_all _ _ (fun x => .. (ho_all _ _ (fun y => p)) ..))
      (at level 200, x binder, right associativity).
  Notation "∃ x .. y , p" :=
    (ho_ex _ _ (fun x => .. (ho_ex _ _ (fun y => p)) ..))
      (at level 200, x binder, right associativity).
  Notation "s ≐ t" :=
    (ho_eq _ _ s t) (at level 20, no associativity).
  Notation "f ⊢ g" :=
    (ho_entails _ f g) (at level 100, right associativity).
End HONotations.

Import HONotations.

Theorem
  placement side Ts (R : ctx side Ts) (p q : Ts ▷ Prop) :
    match side with
    | Pos => (p ⊢ q) -> R{{ p }} -> R{{ q }}
    | Neg => (p ⊢ q) -> R{{ q }} -> R{{ p }}
    end.
Proof.
  induction R ; try destruct side0 ; intros Hpq Hin ;
  try (compute in Hpq ; tauto) ;
  cbn in Hin |- * ; try (specialize (IHR _ _ Hpq) ; try tauto).
  * exact (fun x => H x _ _ (Hpq x) (Hin x)).
  * exact (fun x => H x _ _ (Hpq x) (Hin x)).
  * destruct Hin as (x & Hin) ; exists x ; exact (H x _ _ (Hpq x) Hin).
  * destruct Hin as (x & Hin) ; exists x ; exact (H x _ _ (Hpq x) Hin).
Qed.

Fixpoint ho_apply (Ts : list Type) U R : (U -> (Ts ▷ R)) -> (Ts ▷ U) -> (Ts ▷ R) :=
  match Ts with
  | nil => (fun f t => f t)
  | A :: Ts => (fun f t (x : A) => ho_apply Ts U R (fun u => f u x) (t x))
  end.
Notation "f ◆ x" :=
  (ho_apply _ _ _ f x) (at level 3, left associativity).

(******************************************************************************)
(* Paths *)

Require Import List.

Definition path := list nat.

Inductive resolve : Prop -> path -> forall side Ts, ctx side Ts -> (Ts ▷ Prop) -> Prop :=
| AtHere a :
    resolve a nil Pos nil Hole a
| And1 side Ts path ctx a b f :
    resolve a path side Ts ctx f ->
    resolve (a /\ b) (0 :: path) side Ts (@AndL side Ts ctx b) f
| And2 side Ts path ctx a b f :
    resolve b path side Ts ctx f ->
    resolve (a /\ b) (1 :: path) side Ts (@AndR side Ts a ctx) f
| Or1 side Ts path ctx a b f :
    resolve a path side Ts ctx f ->
    resolve (a \/ b) (0 :: path) side Ts (@OrL side Ts ctx b) f
| Or2 side Ts path ctx a b f :
    resolve b path side Ts ctx f ->
    resolve (a \/ b) (1 :: path) side Ts (@OrR side Ts a ctx) f
| Imp1 side Ts path ctx (a b : Prop) f :
    resolve a path (flip side) Ts ctx f ->
    resolve (a -> b) (0 :: path) side Ts (@ImpL side Ts ctx b) f
| Imp2 side Ts path ctx (a b : Prop) f :
    resolve b path side Ts ctx f ->
    resolve (a -> b) (1 :: path) side Ts (@ImpR side Ts a ctx) f
| All0 A side Ts path ctx a f :
    (forall x, resolve (a x) path side Ts (ctx x) (f x)) ->
    resolve (forall x, a x) (0 :: path) side (A :: Ts) (@AllD A side Ts ctx) f
| Ex0 A side Ts path ctx a f :
    (forall x, resolve(a x) path side Ts  (ctx x) (f x)) ->
    resolve (exists x, a x) (0 :: path) side (A :: Ts) (@ExD A side Ts ctx) f
.

Require Import Relation_Definitions Setoid.
Require Import Coq.Program.Equality.

Lemma resolve_place A path side Ts Cx F :
  resolve A path side Ts Cx F -> Cx{{F}} <-> A.
Proof.
  induction 1 ; cbn ;
  try match goal with
    | [ H : (forall _, _ <-> _) |- _ ] => setoid_rewrite H
    | [ H : resolve _ _ _ _ _ _ |- _ ] => rewrite (resolve_place _ _ _ _ _ _ H)
    end ; tauto.
Qed.

(******************************************************************************)
(* Rules names *)

Inductive rule_name : Type :=
| RN_goal_ts_and_l               (* ((a -> b) /\ c) -> (a -> (b /\ c)) *)
| RN_goal_ts_and_r               (* (c /\ (a -> b)) -> (a -> (c /\ b)) *)
| RN_goal_and_ts_l               (* (a -> b) -> (a /\ c -> b) *)
| RN_goal_and_ts_r               (* (a -> b) -> (c /\ a -> b) *)
| RN_goal_ts_or_l                (* (a -> b) -> (a -> b \/ c) *)
| RN_goal_ts_or_r                (* (a -> b) -> (a -> c \/ b) *)
| RN_goal_or_ts                  (* ((a -> c) /\ (b -> c)) -> (a \/ b -> c) *)
| RN_goal_ts_imp_l               (* (a /\ b -> c) -> (a -> b -> c) *)
| RN_goal_ts_imp_r               (* (c -> a -> b) -> (a -> c -> b) *)
| RN_goal_imp_ts                 (* (c /\ (a -> b)) -> ((c -> a) -> b) *)
| RN_goal_ts_all                 (* (forall x, a -> p x) -> (a -> forall x, p x) *)
| RN_goal_all_ts                 (* (exists x, p x -> b) -> (forall x, p x) -> b *)
| RN_goal_ts_ex                  (* (exists x, a -> p x) -> (a -> exists x, p x) *)
| RN_goal_ex_ts                  (* (forall x, p x -> a) -> (exists x, p x) -> a *)
| RN_asms_and_l_l                (* (a /\ (b /\ c)) -> (a /\ b) *)
| RN_asms_and_l_r                (* (a /\ (c /\ b)) -> (a /\ b) *)
| RN_asms_and_r_l                (* ((a /\ c) /\ b) -> (a /\ b) *)
| RN_asms_and_r_r                (* ((c /\ a) /\ b) -> (a /\ b) *)
| RN_asms_or_l_l                 (* (a /\ (b \/ c)) -> ((a /\ b) \/ c) *)
| RN_asms_or_l_r                 (* (a /\ (c \/ b)) -> (c \/ (a /\ b)) *)
| RN_asms_or_r_l                 (* ((a \/ c) /\ b) -> ((a /\ b) \/ c) *)
| RN_asms_or_r_r                 (* ((c \/ a) /\ b) -> (c \/ (a /\ b)) *)
| RN_asms_imp_l_l                (* (a /\ (b -> c)) -> ((a -> b) -> c) *)
| RN_asms_imp_l_r                (* (a /\ (c -> b)) -> (c -> (a /\ b)) *)
| RN_asms_imp_r_l                (* ((a -> c) /\ b) -> ((b -> a) -> c) *)
| RN_asms_imp_r_r                (* ((c -> a) /\ b) -> (c -> (a /\ b)) *)
| RN_asms_all_l                  (* (a /\ forall x, p x) -> forall x, (a /\ p x) *)
| RN_asms_all_r                  (* ((forall x, p x) /\ a) -> forall x, (p x /\ a) *)
| RN_asms_ex_l                   (* (a /\ exists x, p x) -> exists x, (a /\ p x) *)
| RN_asms_ex_r                   (* ((exists x, p x) /\ a) -> exists x, (p x /\ a) *)
| RN_contract                    (* (a -> a -> b) -> (a -> b) *)
| RN_weaken                      (* b -> (a -> b) *)
| RN_inst_r {T : Type} (t : T)   (* p t -> (exists x, p x) *)
| RN_inst_l {T : Type} (t : T)   (* (forall x, p x) -> p t *)
| RN_rewrite_rtl                 (* p s -> s = t -> p t *)
| RN_rewrite_ltr                 (* p t -> s = t -> p s *)
| RN_repeat                      (* a -> a *)
| RN_simp_goal_and_top           (* a -> (a /\ True) *)
| RN_simp_goal_top_and           (* a -> (True /\ a) *)
| RN_simp_asms_and_top           (* (a /\ True) -> a *)
| RN_simp_asms_top_and           (* (True /\ a) -> a *)
| RN_simp_goal_or_top            (* True -> (a \/ True) *)
| RN_simp_goal_top_or            (* True -> (True \/ a) *)
| RN_simp_asms_or_top            (* (a \/ True) -> True *)
| RN_simp_asms_top_or            (* (True \/ a) -> True *)
| RN_simp_goal_imp_top           (* True -> (a -> True) *)
| RN_simp_goal_top_imp           (* a -> (True -> a) *)
| RN_simp_asms_imp_top           (* (a -> True) -> True *)
| RN_simp_asms_top_imp           (* (True -> a) -> a *)
| RN_simp_goal_and_bot           (* False -> (a /\ False) *)
| RN_simp_goal_bot_and           (* False -> (False /\ a) *)
| RN_simp_asms_and_bot           (* (a /\ False) -> False *)
| RN_simp_asms_bot_and           (* (False /\ a) -> False *)
| RN_simp_goal_or_bot            (* a -> (a \/ False) *)
| RN_simp_goal_bot_or            (* a -> (False \/ a) *)
| RN_simp_asms_or_bot            (* (a \/ False) -> a *)
| RN_simp_asms_bot_or            (* (False \/ a) -> a *)
| RN_simp_goal_bot_imp           (* True -> (False -> a) *)
| RN_simp_asms_bot_imp           (* (False -> a) -> True *)
| RN_simp_goal_all_top           (* True -> forall (_ : T), True *)
| RN_simp_asms_all_top           (* (forall (_ : T), True) -> True *)
| RN_simp_goal_ex_bot            (* False -> exists (_ : T), False *)
| RN_simp_asms_ex_bot            (* (exists (_ : T), False) -> False *)
| RN_init                        (* True -> p -> p *)
| RN_congr                       (* True -> t = t *)
.

(******************************************************************************)
(* Checking derivations *)

Definition deriv := list (rule_name * path).

Fixpoint check (deriv : deriv) (goal : Prop) : Prop :=
  match deriv with
  | nil => goal
  | rp :: deriv =>
      let (rule, path) := rp in
      match rule with
      | RN_goal_ts_and_l =>
          exists Ts ctx a b c,
          resolve goal path Pos Ts ctx (a → (b ∧ c))
          /\ check deriv (ctx{{ (a → b) ∧ c }})
      | RN_goal_ts_and_r =>
          (* (c /\ (a -> b)) -> (a -> (c /\ b)) *)
          exists Ts ctx a b c,
          resolve goal path Pos Ts ctx (a → (c ∧ b))
          /\ check deriv (ctx{{ c ∧ (a → b) }})
      | RN_goal_and_ts_l =>
          (* (a -> b) -> (a /\ c -> b) *)
          exists Ts ctx a b c,
          resolve goal path Pos Ts ctx ((a ∧ c) → b)
          /\ check deriv (ctx{{ a → b }})
      | RN_goal_and_ts_r =>
          (* (a -> b) -> (c /\ a -> b) *)
          exists Ts ctx a b c,
          resolve goal path Pos Ts ctx ((c ∧ a) → b)
          /\ check deriv (ctx{{ a → b }})
      | RN_goal_ts_or_l =>
          (* (a -> b) -> (a -> b \/ c) *)
          exists Ts ctx a b c,
          resolve goal path Pos Ts ctx (a → (b ∨ c))
          /\ check deriv (ctx{{ a → b }})
      | RN_goal_ts_or_r =>
          (* (a -> b) -> (a -> c \/ b) *)
          exists Ts ctx a b c,
          resolve goal path Pos Ts ctx (a → (c ∨ b))
          /\ check deriv (ctx{{ a → b }})
      | RN_goal_or_ts =>
          (* ((a -> c) /\ (b -> c)) -> (a \/ b -> c) *)
          exists Ts ctx a b c,
          resolve goal path Pos Ts ctx ((a ∨ b) → c)
          /\ check deriv (ctx{{ (a → c) ∧ (b → c) }})
      | RN_goal_ts_imp_l =>
          (* (a /\ b -> c) -> (a -> b -> c) *)
          exists Ts ctx a b c,
          resolve goal path Pos Ts ctx (a → b → c)
          /\ check deriv (ctx{{ (a ∧ b) → c }})
      | RN_goal_ts_imp_r =>
          (* (c -> a -> b) -> (a -> c -> b) *)
          exists Ts ctx a b c,
          resolve goal path Pos Ts ctx (a → (c → b))
          /\ check deriv (ctx{{ c → (a → b) }})
      | RN_goal_imp_ts =>
          (* (c /\ (a -> b)) -> ((c -> a) -> b) *)
          exists Ts ctx a b c,
          resolve goal path Pos Ts ctx ((c → a) → b)
          /\ check deriv (ctx{{ c ∧ (a → b) }})
      | RN_goal_ts_all =>
          (* (forall x, a -> p x) -> (a -> forall x, p x) *)
          exists Ts U ctx a p,
          resolve goal path Pos Ts ctx (a → (∀ (x : U), p x))
          /\ check deriv (ctx{{ ∀ (x : U), (a → p x) }})
      | RN_goal_all_ts =>
          (* (exists x, p x -> b) -> (forall x, p x) -> b *)
          exists Ts U ctx b p,
          resolve goal path Pos Ts ctx ((∀ (x : U), p x) → b)
          /\ check deriv (ctx{{ ∃ (x : U), (p x → b) }})
      | RN_goal_ts_ex =>
          (* (exists x, a -> p x) -> (a -> exists x, p x) *)
          exists Ts U ctx a p,
          resolve goal path Pos Ts ctx (a → (∃ (x : U), p x))
          /\ check deriv (ctx{{ ∃ (x : U), (a → p x) }})
      | RN_goal_ex_ts =>
          (* (forall x, p x -> a) -> (exists x, p x) -> a *)
          exists Ts U ctx b p,
          resolve goal path Pos Ts ctx ((∃ (x : U), p x) → b)
          /\ check deriv (ctx{{ ∀ (x : U), (p x → b) }})
      | RN_asms_and_l_l =>
          (* (a /\ (b /\ c)) -> (a /\ b) *)
          exists Ts ctx a b c,
          resolve goal path Neg Ts ctx (a ∧ (b ∧ c))
          /\ check deriv (ctx{{ a ∧ b }})
      | RN_asms_and_l_r =>
          (* (a /\ (c /\ b)) -> (a /\ b) *)
          exists Ts ctx a b c,
          resolve goal path Neg Ts ctx (a ∧ (c ∧ b))
          /\ check deriv (ctx{{ a ∧ b }})
      | RN_asms_and_r_l =>
          (* ((a /\ c) /\ b) -> (a /\ b) *)
          exists Ts ctx a b c,
          resolve goal path Neg Ts ctx ((a ∧ c) ∧ b)
          /\ check deriv (ctx{{ a ∧ b }})
      | RN_asms_and_r_r =>
          (* ((c /\ a) /\ b) -> (a /\ b) *)
          exists Ts ctx a b c,
          resolve goal path Neg Ts ctx ((c ∧ a) ∧ b)
          /\ check deriv (ctx{{ a ∧ b }})
      | RN_asms_or_l_l =>
          (* (a /\ (b \/ c)) -> ((a /\ b) \/ c) *)
          exists Ts ctx a b c,
          resolve goal path Neg Ts ctx (a ∧ (b ∨ c))
          /\ check deriv (ctx{{ (a ∧ b) ∨ c }})
      | RN_asms_or_l_r =>
          (* (a /\ (c \/ b)) -> (c \/ (a /\ b)) *)
          exists Ts ctx a b c,
          resolve goal path Neg Ts ctx (a ∧ (c ∨ b))
          /\ check deriv (ctx{{ c ∨ (a ∧ b) }})
      | RN_asms_or_r_l =>
          (* ((a \/ c) /\ b) -> ((a /\ b) \/ c) *)
          exists Ts ctx a b c,
          resolve goal path Neg Ts ctx ((a ∨ c) ∧ b)
          /\ check deriv (ctx{{ (a ∧ b) ∨ c }})
      | RN_asms_or_r_r =>
          (* ((c \/ a) /\ b) -> (c \/ (a /\ b)) *)
          exists Ts ctx a b c,
          resolve goal path Neg Ts ctx ((c ∨ a) ∧ b)
          /\ check deriv (ctx{{ c ∨ (a ∧ b) }})
      | RN_asms_imp_l_l =>
          (* (a /\ (b -> c)) -> ((a -> b) -> c) *)
          exists Ts ctx a b c,
          resolve goal path Neg Ts ctx (a ∧ (b → c))
          /\ check deriv (ctx{{ (a → b) → c }})
      | RN_asms_imp_l_r =>
          (* (a /\ (c -> b)) -> (c -> (a /\ b)) *)
          exists Ts ctx a b c,
          resolve goal path Neg Ts ctx (a ∧ (c → b))
          /\ check deriv (ctx{{ c → (a ∧ b) }})
      | RN_asms_imp_r_l =>
          (* ((a -> c) /\ b) -> ((b -> a) -> c) *)
          exists Ts ctx a b c,
          resolve goal path Neg Ts ctx ((a → c) ∧ b)
          /\ check deriv (ctx{{ (b → a) → c }})
      | RN_asms_imp_r_r =>
          (* ((c -> a) /\ b) -> (c -> (a /\ b)) *)
          exists Ts ctx a b c,
          resolve goal path Neg Ts ctx ((c → a) ∧ b)
          /\ check deriv (ctx{{ c → (a ∧ b) }})
      | RN_asms_all_l =>
          (* (a /\ forall x, p x) -> forall x, (a /\ p x) *)
          exists Ts U ctx a p,
          resolve goal path Neg Ts ctx (a ∧ (∀ (x : U), p x))
          /\ check deriv (ctx{{ ∀ (x : U), (a ∧ p x) }})
      | RN_asms_all_r =>
          (* ((forall x, p x) /\ a) -> forall x, (p x /\ a) *)
          exists Ts U ctx a p,
          resolve goal path Neg Ts ctx ((∀ (x : U), p x) ∧ a)
          /\ check deriv (ctx{{ ∀ (x : U), (p x ∧ a) }})
      | RN_asms_ex_l =>
          (* (a /\ exists x, p x) -> exists x, (a /\ p x) *)
          exists Ts U ctx a p,
          resolve goal path Neg Ts ctx (a ∧ (∃ (x : U), p x))
          /\ check deriv (ctx{{ ∃ (x : U), (a ∧ p x) }})
      | RN_asms_ex_r =>
          (* ((exists x, p x) /\ a) -> exists x, (p x /\ a) *)
          exists Ts U ctx a p,
          resolve goal path Neg Ts ctx ((∃ (x : U), p x) ∧ a)
          /\ check deriv (ctx{{ ∃ (x : U), (p x ∧ a) }})
      | RN_contract =>
          (* (a -> a -> b) -> (a -> b) *)
          exists Ts ctx a b,
          resolve goal path Pos Ts ctx (a → b)
          /\ check deriv (ctx{{ a → (a → b) }})
      | RN_weaken =>
          (* b -> (a -> b) *)
          exists Ts ctx a b,
          resolve goal path Pos Ts ctx (a → b)
          /\ check deriv (ctx{{ b }})
      | @RN_inst_r T tx =>
          (* p t -> (exists x, p x) *)
          exists Ts ctx U a (t : Ts ▷ U),
          resolve goal path Pos Ts ctx (∃ (x : U), a x)
          /\ T = (Ts ▷ U) (* tx ~= t *)
          /\ check deriv (ctx{{ a ◆ t }})
      | RN_inst_l tx =>
          (* (forall x, p x) -> p t *)
          exists Ts ctx U a (t : Ts ▷ U),
          resolve goal path Neg Ts ctx (∀ (x : U), a x)
          /\ tx ~= t
          /\ check deriv (ctx{{ a ◆ t }})
      | RN_rewrite_rtl =>
          (* p s -> s = t -> p t *)
          exists Ts ctx U (s t : Ts ▷ U) p,
          resolve goal path Pos Ts ctx ((s ≐ t) → (p ◆ t))
          /\ check deriv (ctx{{ p ◆ s}})
      | RN_rewrite_ltr =>
          (* p t -> s = t -> p s *)
          exists Ts ctx U (s t : Ts ▷ U) p,
          resolve goal path Pos Ts ctx ((s ≐ t) → (p ◆ s))
          /\ check deriv (ctx{{ p ◆ t}})
      | RN_repeat =>
          (* a -> a *)
          exists Ts ctx a,
          resolve goal path Pos Ts ctx a
          /\ check deriv (ctx{{ a }})
      | RN_simp_goal_and_top =>
          (* a -> (a /\ True) *)
          exists Ts ctx a,
          resolve goal path Pos Ts ctx (a ∧ ⊤)
          /\ check deriv (ctx{{ a }})
      | RN_simp_goal_top_and =>
          (* a -> (True /\ a) *)
          exists Ts ctx a,
          resolve goal path Pos Ts ctx (⊤ ∧ a)
          /\ check deriv (ctx{{ a }})
      | RN_simp_asms_and_top =>
          (* (a /\ True) -> a *)
          exists Ts ctx a,
          resolve goal path Neg Ts ctx (a ∧ ⊤)
          /\ check deriv (ctx{{ a }})
      | RN_simp_asms_top_and =>
          (* (True /\ a) -> a *)
          exists Ts ctx a,
          resolve goal path Neg Ts ctx (⊤ ∧ a)
          /\ check deriv (ctx{{ a }})
      | RN_simp_goal_or_top =>
          (* True -> (a \/ True) *)
          exists Ts ctx a,
          resolve goal path Pos Ts ctx (a ∨ ⊤)
          /\ check deriv (ctx{{ ⊤ }})
      | RN_simp_goal_top_or =>
          (* True -> (True \/ a) *)
          exists Ts ctx a,
          resolve goal path Pos Ts ctx (⊤ ∨ a)
          /\ check deriv (ctx{{ ⊤ }})
      | RN_simp_asms_or_top =>
          (* (a \/ True) -> True *)
          exists Ts ctx a,
          resolve goal path Neg Ts ctx (a ∨ ⊤)
          /\ check deriv (ctx{{ ⊤ }})
      | RN_simp_asms_top_or =>
          (* (True \/ a) -> True *)
          exists Ts ctx a,
          resolve goal path Neg Ts ctx (a ∨ ⊤)
          /\ check deriv (ctx{{ ⊤ }})
      | RN_simp_goal_imp_top =>
          (* True -> (a -> True) *)
          exists Ts ctx a,
          resolve goal path Pos Ts ctx (a → ⊤)
          /\ check deriv (ctx{{ ⊤ }})
      | RN_simp_goal_top_imp =>
          (* a -> (True -> a) *)
          exists Ts ctx a,
          resolve goal path Pos Ts ctx (⊤ → a)
          /\ check deriv (ctx{{ a }})
      | RN_simp_asms_imp_top =>
          (* (a -> True) -> True *)
          exists Ts ctx a,
          resolve goal path Neg Ts ctx (a → ⊤)
          /\ check deriv (ctx{{ ⊤ }})
      | RN_simp_asms_top_imp =>
          (* (True -> a) -> a *)
          exists Ts ctx a,
          resolve goal path Neg Ts ctx (⊤ → a)
          /\ check deriv (ctx{{ a }})
      | RN_simp_goal_and_bot =>
          (* False -> (a /\ False) *)
          exists Ts ctx a,
          resolve goal path Pos Ts ctx (a ∧ ⊥)
          /\ check deriv (ctx{{ ⊥ }})
      | RN_simp_goal_bot_and =>
          (* False -> (False /\ a) *)
          exists Ts ctx a,
          resolve goal path Pos Ts ctx (⊥ ∧ a)
          /\ check deriv (ctx{{ ⊥ }})
      | RN_simp_asms_and_bot =>
          (* (a /\ False) -> False *)
          exists Ts ctx a,
          resolve goal path Neg Ts ctx (a ∧ ⊥)
          /\ check deriv (ctx{{ ⊥ }})
      | RN_simp_asms_bot_and =>
          (* (False /\ a) -> False *)
          exists Ts ctx a,
          resolve goal path Neg Ts ctx (a ∧ ⊥)
          /\ check deriv (ctx{{ ⊥ }})
      | RN_simp_goal_or_bot =>
          (* a -> (a \/ False) *)
          exists Ts ctx a,
          resolve goal path Pos Ts ctx (a ∨ ⊥)
          /\ check deriv (ctx{{ a }})
      | RN_simp_goal_bot_or =>
          (* a -> (False \/ a) *)
          exists Ts ctx a,
          resolve goal path Pos Ts ctx (⊥ ∨ a)
          /\ check deriv (ctx{{ a }})
      | RN_simp_asms_or_bot =>
          (* (a \/ False) -> a *)
          exists Ts ctx a,
          resolve goal path Neg Ts ctx (a ∨ ⊥)
          /\ check deriv (ctx{{ a }})
      | RN_simp_asms_bot_or =>
          (* (False \/ a) -> a *)
          exists Ts ctx a,
          resolve goal path Neg Ts ctx (⊥ ∨ a)
          /\ check deriv (ctx{{ a }})
      | RN_simp_goal_bot_imp =>
          (* True -> (False -> a) *)
          exists Ts ctx a,
          resolve goal path Pos Ts ctx (⊥ → a)
          /\ check deriv (ctx{{ ⊤ }})
      | RN_simp_asms_bot_imp =>
          (* (False -> a) -> True *)
          exists Ts ctx a,
          resolve goal path Neg Ts ctx (⊥ → a)
          /\ check deriv (ctx{{ ⊤ }})
      | RN_simp_goal_all_top =>
          (* True -> forall (_ : T), True *)
          exists Ts ctx U,
          resolve goal path Pos Ts ctx (∀ (_ : U), ⊤)
          /\ check deriv (ctx{{ ⊤ }})
      | RN_simp_asms_all_top =>
          (* (forall (_ : T), True) -> True *)
          exists Ts ctx U,
          resolve goal path Neg Ts ctx (∀ (_ : U), ⊤)
          /\ check deriv (ctx{{ ⊤ }})
      | RN_simp_goal_ex_bot =>
          (* False -> exists (_ : T), False *)
          exists Ts ctx U,
          resolve goal path Pos Ts ctx (∃ (_ : U), ⊥)
          /\ check deriv (ctx{{ ⊥ }})
      | RN_simp_asms_ex_bot
          (* (exists (_ : T), False) -> False *) =>
          exists Ts ctx U,
          resolve goal path Pos Ts ctx (∃ (_ : U), ⊥)
          /\ check deriv (ctx{{ ⊥ }})
      | RN_init =>
          (* True -> p -> p *)
          exists Ts ctx p,
          resolve goal path Pos Ts ctx (p → p)
          /\ check deriv (ctx{{ ⊤ }})
      | RN_congr =>
          (* True -> t = t *)
          exists Ts ctx A (t : Ts ▷ A),
          resolve goal path Pos Ts ctx (t ≐ t)
          /\ check deriv (ctx{{ ⊤ }})
      end
  end.

Theorem correctness deriv : forall (goal : Prop), check deriv goal -> goal.
Proof.
  induction deriv as [ | rp deriv ] ; intros goal Hcheck ;
    [ exact Hcheck | destruct rp as (rule & path) ; destruct rule ].
  all : repeat match goal with
          | [ H : check (_ :: _) _ |- _ ] =>
              cbn in Hcheck ; destruct Hcheck
          | [ H : ex _ |- _ ] => destruct H
          | [ H : _ /\ _ |- _ ] => destruct H
          | [ H : resolve _ _ Pos _ _ _, Hch : check _ _ |- _ ] =>
              specialize (IHderiv _ Hch) ;
              rewrite <- (resolve_place _ _ Pos _ _ _ H) ;
              refine (placement Pos _ _ _ _ _ IHderiv)
          | [ H : resolve _ _ Neg _ _ _, Hch : check _ _ |- _ ] =>
              specialize (IHderiv _ Hch) ;
              rewrite <- (resolve_place _ _ Neg _ _ _ H) ;
              refine (placement Neg _ _ _ _ _ IHderiv)
          | [ |- ho_entails ?x _ _ ] =>
              let Ts := fresh "Ts" in
              rename x into Ts ; clear ; induction Ts as [ | A Ts ] ;
              [ compute ; tauto | intro u ]
          end.
  all : repeat match reverse goal with
          | [ x : (_ :: _ ▷ _), IH : (forall (_ : _ ▷ Prop), _) |- _ ] =>
              specialize (IH (x u)) ; cbn in x ; try tauto
          end.
  all : try match goal with
          | [ x : list Type |- _ ] =>
              clear ;
              let Ts := fresh "Ts" in
              rename x into Ts ; induction Ts ;
              [ compute ; (eauto || intuition) | intro u ; apply IHTs ]
        end.
  all : repeat match goal with
          | [ H : ex _ |- _ ] => destruct H
          | [ H : _ /\ _ |- _ ] => destruct H
          | [ H : _ = _ |- _ ] => try rewrite H in * |- * ; clear H
          end ; try eauto.
Qed.

Ltac check_simplify_one :=
  match goal with
  | [ |- check (@cons _ _ _) _ ] =>
      unfold check ;
      repeat match goal with
        | [ |- @ex _ _ ] =>
            eexists
        | [ |- @and _ _ ] =>
            split ; [ compute ; repeat econstructor | ]
        end
  end.

Ltac check_simplify :=
  match goal with
  | [ |- check (@cons _ _ _) _ ] =>
      check_simplify_one ;
      check_simplify
  | _ => compute
  end.

Ltac check_solve := cbv zeta ; check_simplify ; eauto.
