Require Import List.
Import ListNotations.

Polymorphic Inductive rcx : list Type -> Type :=
| Hole      : rcx nil
| RAndL A   : rcx A -> Prop -> rcx A
| RAndR A   : Prop -> rcx A -> rcx A
| ROrL A    : rcx A -> Prop -> rcx A
| ROrR A    : Prop -> rcx A -> rcx A
| RImpL A   : lcx A -> Prop -> rcx A
| RImpR A   : Prop -> rcx A -> rcx A
| RAll A B  : (A -> rcx B) -> rcx (A :: B)
| REx A B   : (A -> rcx B) -> rcx (A :: B)
with lcx : list Type -> Type :=
| LAndL A   : lcx A -> Prop -> lcx A
| LAndR A   : Prop -> lcx A -> lcx A
| LOrL A    : lcx A -> Prop -> lcx A
| LOrR A    : Prop -> lcx A -> lcx A
| LImpL A   : rcx A -> Prop -> lcx A
| LImpR A   : Prop -> lcx A -> lcx A
| LAll A B  : (A -> lcx B) -> lcx (A :: B)
| LEx A B   : (A -> lcx B) -> lcx (A :: B).

Reserved Notation "R [[ P ]]" (at level 1, format "'[ ' R [[  P  ]] ']'").
Reserved Notation "L {{ P }}" (at level 1, format "'[ ' L '{{'  P  '}}' ']'").

Fixpoint ho_absract (Ts : list Type) (U : Type) :=
  match Ts return Type with
  | nil => U
  | A :: Ts => A -> ho_absract Ts U
  end.
Notation "Ts ▷ U" := (ho_absract Ts U) (at level 100, right associativity).

Fixpoint rcx_place Ts (rcx : rcx Ts) {struct rcx} : (Ts ▷ Prop) -> Prop :=
  match rcx in (rcx Ts1) return ((Ts1 ▷ Prop) -> Prop) with
  | Hole          => fun p => p
  | RAndL _ rcx q => fun p => rcx[[ p ]] /\ q
  | RAndR _ q rcx => fun p => q /\ rcx[[ p ]]
  | ROrL _ rcx q  => fun p => rcx[[ p ]] \/ q
  | ROrR _ q rcx  => fun p => q \/ rcx[[ p ]]
  | RImpL _ lcx q => fun p => lcx{{ p }} -> q
  | RImpR _ q rcx => fun p => q -> rcx[[ p ]]
  | RAll a _ rcx  => fun p => forall (x : a), (rcx x)[[ (p x) ]]
  | REx a _ rcx   => fun p => exists (x : a), (rcx x)[[ (p x) ]]
  end
with lcx_place Ts (lcx : lcx Ts) {struct lcx} : (Ts ▷ Prop) -> Prop :=
  match lcx in (lcx Ts1) return ((Ts1 ▷ Prop) -> Prop) with
  | LAndL _ lcx q => fun p => lcx{{ p }} /\ q
  | LAndR _ q lcx => fun p => q /\ lcx{{ p }}
  | LOrL _ lcx q  => fun p => lcx{{ p }} \/ q
  | LOrR _ q lcx  => fun p => q \/ lcx{{ p }}
  | LImpL _ rcx q => fun p => rcx[[ p ]] -> q
  | LImpR _ q lcx => fun p => q -> lcx{{ p }}
  | LAll a _ lcx  => fun p => forall (x : a), (lcx x){{ (p x) }}
  | LEx a _ lcx   => fun p => exists (x : a), (lcx x){{ (p x) }}
  end
where "R [[ P ]]" := (@rcx_place _ R P) : type_scope
and   "L {{ P }}" := (@lcx_place _ L P) : type_scope.

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
  placement_r Ts (R : rcx Ts) (p q : Ts ▷ Prop) :
    (p ⊢ q) -> R[[ p ]] -> R[[ q ]]
with
  placement_l Ts (L : lcx Ts) (p q : Ts ▷ Prop) :
    (p ⊢ q) -> L{{ q }} -> L{{ p }}.
Proof.
- induction R ; intros Hpq Hin ; try (compute in Hpq ; tauto) ;
    cbn in Hin |- * ; try (specialize (IHR _ _ Hpq) ; try tauto).
  * exact (fun Hq => Hin (placement_l _ _ _ _ Hpq Hq)).
  * exact (fun x => H x _ _ (Hpq x) (Hin x)).
  * destruct Hin as (x & Hin) ; exists x ; exact (H x _ _ (Hpq x) Hin).
- induction L ; intros Hqp Hin ; try (compute in Hqp ; tauto) ;
    cbn in Hin |- * ; try (specialize (IHL _ _ Hqp) ; tauto).
  * exact (fun Hp => Hin (placement_r _ _ _ _ Hqp Hp)).
  * exact (fun x => H x _ _ (Hqp x) (Hin x)).
  * destruct Hin as (x & Hin) ; exists x ; exact (H x _ _ (Hqp x) Hin).
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

Inductive resolve_r : forall Ts, Prop -> path -> rcx Ts -> (Ts ▷ Prop) -> Prop :=
| AtHere a :
    resolve_r _ a nil Hole a
| RAnd1 T path rcx a b f :
    resolve_r _ a path rcx f ->
    resolve_r _ (a /\ b) (0 :: path) (RAndL T rcx b) f
| RAnd2 T path rcx a b f :
    resolve_r _ b path rcx f ->
    resolve_r _ (a /\ b) (1 :: path) (RAndR T a rcx) f
| ROr1 T path rcx a b f :
    resolve_r _ a path rcx f ->
    resolve_r _ (a \/ b) (0 :: path) (ROrL T rcx b) f
| ROr2 T path rcx a b f :
    resolve_r _ b path rcx f ->
    resolve_r _ (a \/ b) (1 :: path) (ROrR T a rcx) f
| RImp1 T path lcx (a b : Prop) f :
    resolve_l _ a path lcx f ->
    resolve_r _ (a -> b) (0 :: path) (RImpL T lcx b) f
| RImp2 T path rcx (a b : Prop) f :
    resolve_r _ b path rcx f ->
    resolve_r _ (a -> b) (1 :: path) (RImpR T a rcx) f
| RAll0 A T path rcx a f :
    (forall x, resolve_r _ (a x) path (rcx x) (f x)) ->
    resolve_r _ (forall x, a x) (0 :: path) (RAll A T rcx) f
| REx0 A T path rcx a f :
    (forall x, resolve_r _ (a x) path (rcx x) (f x)) ->
    resolve_r _ (exists x, a x) (0 :: path) (REx A T rcx) f
with resolve_l : forall Ts, Prop -> path -> lcx Ts -> (Ts ▷ Prop) -> Prop :=
| LAnd1 T path lcx a b f :
    resolve_l _ a path lcx f ->
    resolve_l _ (a /\ b) (0 :: path) (LAndL T lcx b) f
| LAnd2 T path lcx a b f :
    resolve_l _ b path lcx f ->
    resolve_l _ (a /\ b) (1 :: path) (LAndR T a lcx) f
| LOr1 T path lcx a b f :
    resolve_l _ a path lcx f ->
    resolve_l _ (a \/ b) (0 :: path) (LOrL T lcx b) f
| LOr2 T path lcx a b f :
    resolve_l _ b path lcx f ->
    resolve_l _ (a \/ b) (1 :: path) (LOrR T a lcx) f
| LImp1 T path rcx (a b : Prop) f :
    resolve_r _ a path rcx f ->
    resolve_l _ (a -> b) (0 :: path) (LImpL T rcx b) f
| LImp2 T path lcx (a b : Prop) f :
    resolve_l _ b path lcx f ->
    resolve_l _ (a -> b) (1 :: path) (LImpR T a lcx) f
| LAll0 A T path lcx a f :
    (forall x, resolve_l _ (a x) path (lcx x) (f x)) ->
    resolve_l _ (forall x, a x) (0 :: path) (LAll A T lcx) f
| LEx0 A T path lcx a f :
    (forall x, resolve_l _ (a x) path (lcx x) (f x)) ->
    resolve_l _ (exists x, a x) (0 :: path) (LEx A T lcx) f.

Require Import Relation_Definitions Setoid.
Require Import Coq.Program.Equality.

Lemma
  resolve_place_r Ts (rp : path) (rcx : rcx Ts) (a : Prop) (f : Ts ▷ Prop) :
    resolve_r _ a rp rcx f -> rcx[[ f ]] <-> a
with
  resolve_place_l Ts (lp : path) (lcx : lcx Ts) (a : Prop) (f : Ts ▷ Prop) :
    resolve_l _ a lp lcx f -> lcx{{ f }} <-> a.
Proof.
- induction 1 ; cbn ;
  try match goal with
    | [ H : (forall _, _ <-> _) |- _ ] => setoid_rewrite H
    | [ H : resolve_l _ _ _ _ _ |- _ ] => rewrite (resolve_place_l _ _ _ _ _ H)
    end ; tauto.
- induction 1 ; cbn ;
  try match goal with
    | [ H : (forall _, _ <-> _) |- _ ] => setoid_rewrite H
    | [ H : resolve_r _ _ _ _ _ |- _ ] => rewrite (resolve_place_r _ _ _ _ _ H)
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
| RN_inst {T : Type} (t : T)     (* p t -> (exists x, p x) *)
| RN_inst_all {T : Type} (t : T) (* (forall x, p x) -> p t *)
| RN_simp_imp_true               (* True -> a -> True *)
| RN_simp_true_imp_r             (* a -> (True -> a) *)
| RN_simp_true_imp_l             (* (True -> a) -> a *)
| RN_simp_false_imp              (* True -> (False -> a) *)
| RN_simp_and_true_l             (* a -> (a /\ True) *)
| RN_simp_and_true_r             (* a -> (True /\ a) *)
| RN_simp_or_true_l              (* True -> (a \/ True) *)
| RN_simp_or_true_r              (* True -> (True \/ a) *)
| RN_simp_all_true               (* True -> forall (_ : T), True *)
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
          exists T rcx a b c,
          resolve_r T goal path rcx (a → (b ∧ c))
          /\ check deriv (rcx[[ (a → b) ∧ c ]])
      | RN_goal_ts_and_r =>
          (* (c /\ (a -> b)) -> (a -> (c /\ b)) *)
          exists T rcx a b c,
          resolve_r T goal path rcx (a → (c ∧ b))
          /\ check deriv (rcx[[ c ∧ (a → b) ]])
      | RN_goal_and_ts_l =>
          (* (a -> b) -> (a /\ c -> b) *)
          exists T rcx a b c,
          resolve_r T goal path rcx ((a ∧ c) → b)
          /\ check deriv (rcx[[ a → b ]])
      | RN_goal_and_ts_r =>
          (* (a -> b) -> (c /\ a -> b) *)
          exists T rcx a b c,
          resolve_r T goal path rcx ((c ∧ a) → b)
          /\ check deriv (rcx[[ a → b ]])
      | RN_goal_ts_or_l =>
          (* (a -> b) -> (a -> b \/ c) *)
          exists T rcx a b c,
          resolve_r T goal path rcx (a → (b ∨ c))
          /\ check deriv (rcx[[ a → b ]])
      | RN_goal_ts_or_r =>
          (* (a -> b) -> (a -> c \/ b) *)
          exists T rcx a b c,
          resolve_r T goal path rcx (a → (c ∨ b))
          /\ check deriv (rcx[[ a → b ]])
      | RN_goal_or_ts =>
          (* ((a -> c) /\ (b -> c)) -> (a \/ b -> c) *)
          exists T rcx a b c,
          resolve_r T goal path rcx ((a ∨ b) → c)
          /\ check deriv (rcx[[ (a → c) ∧ (b → c) ]])
      | RN_goal_ts_imp_l =>
          (* (a /\ b -> c) -> (a -> b -> c) *)
          exists T rcx a b c,
          resolve_r T goal path rcx (a → b → c)
          /\ check deriv (rcx[[ (a ∧ b) → c ]])
      | RN_goal_ts_imp_r =>
          (* (c -> a -> b) -> (a -> c -> b) *)
          exists T rcx a b c,
          resolve_r T goal path rcx (a → (c → b))
          /\ check deriv (rcx[[ c → (a → b) ]])
      | RN_goal_imp_ts =>
          (* (c /\ (a -> b)) -> ((c -> a) -> b) *)
          exists T rcx a b c,
          resolve_r T goal path rcx ((c → a) → b)
          /\ check deriv (rcx[[ c ∧ (a → b) ]])
      | RN_goal_ts_all =>
          (* (forall x, a -> p x) -> (a -> forall x, p x) *)
          exists T U rcx a p,
          resolve_r T goal path rcx (a → (∀ (x : U), p x))
          /\ check deriv (rcx[[ ∀ (x : U), (a → p x) ]])
      | RN_goal_all_ts =>
          (* (exists x, p x -> b) -> (forall x, p x) -> b *)
          exists T U rcx b p,
          resolve_r T goal path rcx ((∀ (x : U), p x) → b)
          /\ check deriv (rcx[[ ∃ (x : U), (p x → b) ]])
      | RN_goal_ts_ex =>
          (* (exists x, a -> p x) -> (a -> exists x, p x) *)
          exists T U rcx a p,
          resolve_r T goal path rcx (a → (∃ (x : U), p x))
          /\ check deriv (rcx[[ ∃ (x : U), (a → p x) ]])
      | RN_goal_ex_ts =>
          (* (forall x, p x -> a) -> (exists x, p x) -> a *)
          exists T U rcx b p,
          resolve_r T goal path rcx ((∃ (x : U), p x) → b)
          /\ check deriv (rcx[[ ∀ (x : U), (p x → b) ]])
      | RN_asms_and_l_l =>
          (* (a /\ (b /\ c)) -> (a /\ b) *)
          exists T lcx a b c,
          resolve_l T goal path lcx (a ∧ (b ∧ c))
          /\ check deriv (lcx{{ a ∧ b }})
      | RN_asms_and_l_r =>
          (* (a /\ (c /\ b)) -> (a /\ b) *)
          exists T lcx a b c,
          resolve_l T goal path lcx (a ∧ (c ∧ b))
          /\ check deriv (lcx{{ a ∧ b }})
      | RN_asms_and_r_l =>
          (* ((a /\ c) /\ b) -> (a /\ b) *)
          exists T lcx a b c,
          resolve_l T goal path lcx ((a ∧ c) ∧ b)
          /\ check deriv (lcx{{ a ∧ b }})
      | RN_asms_and_r_r =>
          (* ((c /\ a) /\ b) -> (a /\ b) *)
          exists T lcx a b c,
          resolve_l T goal path lcx ((c ∧ a) ∧ b)
          /\ check deriv (lcx{{ a ∧ b }})
      | RN_asms_or_l_l =>
          (* (a /\ (b \/ c)) -> ((a /\ b) \/ c) *)
          exists T lcx a b c,
          resolve_l T goal path lcx (a ∧ (b ∨ c))
          /\ check deriv (lcx{{ (a ∧ b) ∨ c }})
      | RN_asms_or_l_r =>
          (* (a /\ (c \/ b)) -> (c \/ (a /\ b)) *)
          exists T lcx a b c,
          resolve_l T goal path lcx (a ∧ (c ∨ b))
          /\ check deriv (lcx{{ c ∨ (a ∧ b) }})
      | RN_asms_or_r_l =>
          (* ((a \/ c) /\ b) -> ((a /\ b) \/ c) *)
          exists T lcx a b c,
          resolve_l T goal path lcx ((a ∨ c) ∧ b)
          /\ check deriv (lcx{{ (a ∧ b) ∨ c }})
      | RN_asms_or_r_r =>
          (* ((c \/ a) /\ b) -> (c \/ (a /\ b)) *)
          exists T lcx a b c,
          resolve_l T goal path lcx ((c ∨ a) ∧ b)
          /\ check deriv (lcx{{ c ∨ (a ∧ b) }})
      | RN_asms_imp_l_l =>
          (* (a /\ (b -> c)) -> ((a -> b) -> c) *)
          exists T lcx a b c,
          resolve_l T goal path lcx (a ∧ (b → c))
          /\ check deriv (lcx{{ (a → b) → c }})
      | RN_asms_imp_l_r =>
          (* (a /\ (c -> b)) -> (c -> (a /\ b)) *)
          exists T lcx a b c,
          resolve_l T goal path lcx (a ∧ (c → b))
          /\ check deriv (lcx{{ c → (a ∧ b) }})
      | RN_asms_imp_r_l =>
          (* ((a -> c) /\ b) -> ((b -> a) -> c) *)
          exists T lcx a b c,
          resolve_l T goal path lcx ((a → c) ∧ b)
          /\ check deriv (lcx{{ (b → a) → c }})
      | RN_asms_imp_r_r =>
          (* ((c -> a) /\ b) -> (c -> (a /\ b)) *)
          exists T lcx a b c,
          resolve_l T goal path lcx ((c → a) ∧ b)
          /\ check deriv (lcx{{ c → (a ∧ b) }})
      | RN_asms_all_l =>
          (* (a /\ forall x, p x) -> forall x, (a /\ p x) *)
          exists T U lcx a p,
          resolve_l T goal path lcx (a ∧ (∀ (x : U), p x))
          /\ check deriv (lcx{{ ∀ (x : U), (a ∧ p x) }})
      | RN_asms_all_r =>
          (* ((forall x, p x) /\ a) -> forall x, (p x /\ a) *)
          exists T U lcx a p,
          resolve_l T goal path lcx ((∀ (x : U), p x) ∧ a)
          /\ check deriv (lcx{{ ∀ (x : U), (p x ∧ a) }})
      | RN_asms_ex_l =>
          (* (a /\ exists x, p x) -> exists x, (a /\ p x) *)
          exists T U lcx a p,
          resolve_l T goal path lcx (a ∧ (∃ (x : U), p x))
          /\ check deriv (lcx{{ ∃ (x : U), (a ∧ p x) }})
      | RN_asms_ex_r =>
          (* ((exists x, p x) /\ a) -> exists x, (p x /\ a) *)
          exists T U lcx a p,
          resolve_l T goal path lcx ((∃ (x : U), p x) ∧ a)
          /\ check deriv (lcx{{ ∃ (x : U), (p x ∧ a) }})
      | RN_contract =>
          (* (a -> a -> b) -> (a -> b) *)
          exists T rcx a b,
          resolve_r T goal path rcx (a → b)
          /\ check deriv (rcx[[ a → (a → b) ]])
      | RN_weaken =>
          (* b -> (a -> b) *)
          exists T rcx a b,
          resolve_r T goal path rcx (a → b)
          /\ check deriv (rcx[[ b ]])
      | @RN_inst U tx =>
          (* p t -> (exists x, p x) *)
          exists T rcx a (t : T ▷ U),
          resolve_r T goal path rcx (∃ (x : U), a x)
          /\ tx ~= t
          /\ check deriv (rcx[[ a ◆ t ]])
      | @RN_inst_all U tx =>
          (* (forall x, p x) -> p t *)
          exists T lcx a (t : T ▷ U),
          resolve_l T goal path lcx (∀ (x : U), a x)
          /\ tx ~= t
          /\ check deriv (lcx{{ a ◆ t }})
      | RN_simp_imp_true =>
          (* True -> a -> True *)
          exists T rcx a,
          resolve_r T goal path rcx (a → ⊤)
          /\ check deriv (rcx[[ ⊤ ]])
      | RN_simp_true_imp_r =>
          (* a -> (True -> a) *)
          exists T rcx a,
          resolve_r T goal path rcx (⊤ → a)
          /\ check deriv (rcx[[ a ]])
      | RN_simp_true_imp_l =>
          (* (True -> a) -> a *)
          exists T lcx a,
          resolve_l T goal path lcx (⊤ → a)
          /\ check deriv (lcx{{ a }})
      | RN_simp_false_imp =>
          (* True -> (False -> a) *)
          exists T rcx a,
          resolve_r T goal path rcx (⊥ → a)
          /\ check deriv (rcx[[ ⊤ ]])
      | RN_simp_and_true_l =>
          (* a -> (a /\ True) *)
          exists T rcx a,
          resolve_r T goal path rcx (a ∧ ⊤)
          /\ check deriv (rcx[[ a ]])
      | RN_simp_and_true_r =>
          (* a -> (True /\ a) *)
          exists T rcx a,
          resolve_r T goal path rcx (⊤ ∧ a)
          /\ check deriv (rcx[[ a ]])
      | RN_simp_or_true_l =>
          (* True -> (a \/ True) *)
          exists T rcx a,
          resolve_r T goal path rcx (a ∨ ⊤)
          /\ check deriv (rcx[[ ⊤ ]])
      | RN_simp_or_true_r =>
          (* True -> (True \/ a) *)
          exists T rcx a,
          resolve_r T goal path rcx (⊤ ∨ a)
          /\ check deriv (rcx[[ ⊤ ]])
      | RN_simp_all_true =>
          (* True -> forall (_ : T), True *)
          exists T U rcx,
          resolve_r T goal path rcx (∀ (x : U), ⊤)
          /\ check deriv (rcx[[ ⊤ ]])
      | RN_init =>
          (* True -> p -> p *)
          exists T rcx p,
          resolve_r T goal path rcx (p → p)
          /\ check deriv (rcx[[ ⊤ ]])
      | RN_congr =>
          (* True -> t = t *)
          exists T rcx A (t : T ▷ A),
          resolve_r T goal path rcx (t ≐ t)
          /\ check deriv (rcx[[ ⊤ ]])
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
          | [ H : resolve_r _ _ _ _ _, Hch : check _ _ |- _ ] =>
              specialize (IHderiv _ Hch) ;
              rewrite <- (resolve_place_r _ _ _ _ _ H) ;
              refine (placement_r _ _ _ _ _ IHderiv)
          | [ H : resolve_l _ _ _ _ _, Hch : check _ _ |- _ ] =>
              specialize (IHderiv _ Hch) ;
              rewrite <- (resolve_place_l _ _ _ _ _ H) ;
              refine (placement_l _ _ _ _ _ IHderiv)
          | [ |- ho_entails ?x _ _ ] =>
              let Ts := fresh "Ts" in
              rename x into Ts ; clear ; induction Ts as [ | A Ts ] ;
              [ compute ; tauto | intro u ]
          end.
  all : repeat match reverse goal with
          | [ x : (_ :: _ ▷ _), IH : (forall (_ : _ ▷ Prop), _) |- _ ] =>
              specialize (IH (x u)) ; cbn in x ; try tauto
          end.
  11 : tauto.
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
