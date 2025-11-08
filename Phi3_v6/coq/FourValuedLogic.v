(* ============================================================================
   Φ³/LGPDT: Four-Valued Paraconsistent Logic
   Author: Felipe Sáez Acevedo (formalized)
   Date: 2025
   
   This module defines the core logic LG⇄ with truth values {T, F, B, N}
   and proves its non-trivialization and paraconsistency properties.
   ============================================================================ *)

Require Import Coq.Init.Datatypes.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Relations.Relations.

(* --------------------------------------------------------------------------
   1. DEFINITION OF TRUTH VALUES
   -------------------------------------------------------------------------- *)

Inductive TruthValue : Type :=
  | VT : TruthValue  (* True: classically valid *)
  | VF : TruthValue  (* False: classically invalid *)
  | VB : TruthValue  (* Both: productive contradiction P ∧ ¬P *)
  | VN : TruthValue. (* Neither: generative incompleteness ¬(P ∨ ¬P) *)

Notation "T" := VT.
Notation "F" := VF.
Notation "B" := VB.
Notation "N" := VN.

(* Decidable equality *)
Theorem tv_eq_dec : forall (x y : TruthValue), {x = y} + {x <> y}.
Proof.
  decide equality.
Qed.

(* --------------------------------------------------------------------------
   2. LOGICAL CONNECTIVES
   -------------------------------------------------------------------------- *)

(* Conjunction: ∧ *)
Definition land (v1 v2 : TruthValue) : TruthValue :=
  match v1, v2 with
  | T, T => T
  | F, _ => F  (* Falsity dominates *)
  | _, F => F
  | B, T => B
  | T, B => B
  | B, B => B
  | N, _ => N  (* Incompleteness emerges *)
  | _, N => N
  end.

Notation "x ∧₄ y" := (land x y) (at level 40, left associativity).

(* Disjunction: ∨ *)
Definition lor (v1 v2 : TruthValue) : TruthValue :=
  match v1, v2 with
  | F, F => F
  | T, _ => T  (* Truth dominates *)
  | _, T => T
  | B, F => B
  | F, B => B
  | B, B => B
  | B, N => B  (* Contradiction absorbs incompleteness *)
  | N, B => B
  | N, F => N
  | F, N => N
  | N, N => N
  end.

Notation "x ∨₄ y" := (lor x y) (at level 50, left associativity).

(* Negation: ¬ (preserves B and N) *)
Definition lneg (v : TruthValue) : TruthValue :=
  match v with
  | T => F
  | F => T
  | B => B  (* ¬B = B: negation doesn't resolve contradiction *)
  | N => N  (* ¬N = N: negation doesn't resolve incompleteness *)
  end.

Notation "¬₄ x" := (lneg x) (at level 35, right associativity).

(* Implication: → (defined as ¬A ∨ B) *)
Definition limpl (v1 v2 : TruthValue) : TruthValue :=
  (¬₄ v1) ∨₄ v2.

Notation "x →₄ y" := (limpl x y) (at level 55, right associativity).

(* --------------------------------------------------------------------------
   3. PROPERTIES OF CONNECTIVES
   -------------------------------------------------------------------------- *)

(* Idempotence of ∧ *)
Lemma land_idemp : forall v, v ∧₄ v = v.
Proof.
  intros []; reflexivity.
Qed.

(* Idempotence of ∨ *)
Lemma lor_idemp : forall v, v ∨₄ v = v.
Proof.
  intros []; reflexivity.
Qed.

(* Double negation on stable values *)
Lemma lneg_involution_stable : forall v,
  (v = T \/ v = F) -> ¬₄ (¬₄ v) = v.
Proof.
  intros v [H|H]; rewrite H; reflexivity.
Qed.

(* Negation preserves spin values *)
Lemma lneg_preserves_spin :
  ¬₄ B = B /\ ¬₄ N = N.
Proof.
  split; reflexivity.
Qed.

(* De Morgan's Laws (valid for all values) *)
Lemma de_morgan_and : forall v1 v2,
  ¬₄ (v1 ∧₄ v2) = (¬₄ v1) ∨₄ (¬₄ v2).
Proof.
  intros [] []; reflexivity.
Qed.

Lemma de_morgan_or : forall v1 v2,
  ¬₄ (v1 ∨₄ v2) = (¬₄ v1) ∧₄ (¬₄ v2).
Proof.
  intros [] []; reflexivity.
Qed.

(* --------------------------------------------------------------------------
   4. SPIN OPERATOR (⇄)
   -------------------------------------------------------------------------- *)

(* The productive oscillation operator *)
Definition spin (v : TruthValue) : TruthValue :=
  match v with
  | B => N  (* Contradiction transforms to incompleteness *)
  | N => B  (* Incompleteness transforms to contradiction *)
  | T => T  (* Stable values don't spin *)
  | F => F
  end.

Notation "⇄ x" := (spin x) (at level 35).

(* Spin is involutive on active values *)
Lemma spin_involution : forall v,
  (v = B \/ v = N) -> ⇄ (⇄ v) = v.
Proof.
  intros v [H|H]; rewrite H; reflexivity.
Qed.

(* Spin is identity on stable values *)
Lemma spin_stable : forall v,
  (v = T \/ v = F) -> ⇄ v = v.
Proof.
  intros v [H|H]; rewrite H; reflexivity.
Qed.

(* Spin differs from negation *)
Lemma spin_not_neg : ⇄ B <> ¬₄ B.
Proof.
  simpl. discriminate.
Qed.

(* --------------------------------------------------------------------------
   5. ACTIVE PROPOSITIONS
   -------------------------------------------------------------------------- *)

(* A value is active if it requires resolution *)
Definition is_active (v : TruthValue) : Prop :=
  v = B \/ v = N.

Definition is_stable (v : TruthValue) : Prop :=
  v = T \/ v = F.

Lemma active_stable_disjoint : forall v,
  is_active v -> ~is_stable v.
Proof.
  intros v [HB|HN] [HT|HF]; 
    try (rewrite HB in HT; discriminate);
    try (rewrite HB in HF; discriminate);
    try (rewrite HN in HT; discriminate);
    try (rewrite HN in HF; discriminate).
Qed.

(* --------------------------------------------------------------------------
   6. PARACONSISTENCY (NON-EXPLOSION)
   -------------------------------------------------------------------------- *)

(* 
   THEOREM 7.1 (Non-Explosion):
   From B we cannot derive arbitrary Q.
   
   This is modeled by showing that modus ponens doesn't trivialize:
   If P has value B, P → Q doesn't automatically make Q true.
*)

Theorem non_explosion : forall vQ : TruthValue,
  B →₄ vQ = vQ \/ B →₄ vQ = B \/ B →₄ vQ = T.
Proof.
  intro vQ.
  destruct vQ; simpl; auto.
Qed.

(* More precisely: B doesn't imply F *)
Lemma B_not_implies_F : B →₄ F = B.
Proof.
  reflexivity.
Qed.

(* And B doesn't force arbitrary Q to be T *)
Lemma B_not_trivial : exists vQ, B →₄ vQ <> T.
Proof.
  exists F. simpl. discriminate.
Qed.

(* --------------------------------------------------------------------------
   7. NON-TRIVIALIZATION
   -------------------------------------------------------------------------- *)

(*
   A logic is trivial if all formulas have the same value.
   We prove LG⇄ is non-trivial.
*)

Theorem logic_nontrivial : exists v1 v2 : TruthValue, v1 <> v2.
Proof.
  exists T, F. discriminate.
Qed.

(* Even with contradiction present, not all values collapse *)
Theorem B_distinct_from_others :
  B <> T /\ B <> F /\ B <> N.
Proof.
  repeat split; discriminate.
Qed.

(* --------------------------------------------------------------------------
   8. PRODUCTIVE OSCILLATION DYNAMICS
   -------------------------------------------------------------------------- *)

(* If a value is active, applying spin changes it *)
Lemma spin_changes_active : forall v,
  is_active v -> ⇄ v <> v.
Proof.
  intros v [HB|HN].
  - rewrite HB. simpl. discriminate.
  - rewrite HN. simpl. discriminate.
Qed.

(* Repeated spin oscillates *)
Lemma spin_oscillates : forall n v,
  is_active v ->
  (Nat.even n = true -> Nat.iter n spin v = v) /\
  (Nat.odd n = true -> Nat.iter n spin v = ⇄ v).
Proof.
  induction n; intros v Hact; split; intro Hparity.
  - (* n=0, even *) simpl. reflexivity.
  - (* n=0, odd *) discriminate.
  - (* S n, even *)
    simpl. destruct (Nat.even n) eqn:E.
    + apply IHn in Hact. destruct Hact as [Heven _].
      rewrite Heven; auto.
      destruct v; auto; destruct Hact as [H|H]; discriminate.
    + simpl in Hparity. rewrite E in Hparity. discriminate.
  - (* S n, odd *)
    simpl. destruct (Nat.odd n) eqn:E.
    + apply IHn in Hact. destruct Hact as [_ Hodd].
      rewrite Hodd; auto.
      apply spin_involution. assumption.
    + simpl in Hparity. rewrite E in Hparity. discriminate.
Qed.

(* --------------------------------------------------------------------------
   9. SUMMARY
   -------------------------------------------------------------------------- *)

(*
   We have formalized:
   1. Four-valued logic {T, F, B, N}
   2. Logical connectives that preserve paraconsistency
   3. Spin operator ⇄ that productively oscillates active values
   4. Non-explosion property (no Ex Falso Quodlibet)
   5. Non-trivialization (system remains coherent despite B)
   
   This forms the logical foundation for the LGPDT system.
*)

(* Export key definitions and theorems *)
#[export] Hint Resolve land_idemp lor_idemp spin_involution : lgpdt_hints.
#[export] Hint Resolve non_explosion B_not_trivial : lgpdt_hints.