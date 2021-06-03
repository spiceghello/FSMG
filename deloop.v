Require Export hott_lemmas.

(** Delooping of symmetric groups **)

Section deloop.
Open Scope nat.

Private Inductive deloop : nat -> Type :=
  | dlpt0 : deloop 0
  | dli : forall n : nat, deloop n -> deloop n.+1.
Global Arguments dli {n} _.

Fixpoint dlpt (n : nat) : deloop n
  := match n with
  | 0 => dlpt0
  | n'.+1 => dli (dlpt n') end.

Axiom dltw : forall (n : nat) (a : deloop n),
  dli (dli a) = dli (dli a)
  :> deloop n.+2.
Global Arguments dltw {n} _.

Axiom dldo : forall (n : nat) (a : deloop n),
  dltw a @ dltw a = idpath
  :> (dli (dli a) = dli (dli a)).
Global Arguments dldo {n} _.

  Definition dldo_ : forall (n : nat) (a : deloop n),
    (dltw a)^ = dltw a.
  Proof.
    intros n a.
    refine (cancelR (dltw a)^ (dltw a) (dltw a) _).
    exact (concat_Vp _ @ (dldo a)^).
  Defined.
  Global Arguments dldo_ {n} _.

Axiom dlbr : forall (n : nat) (a : deloop n),
  dltw (dli a) @ ap dli (dltw a) @ dltw (dli a) = ap dli (dltw a) @ dltw (dli a) @ ap dli (dltw a)
  :> (dli (dli (dli a)) = dli (dli (dli a))).
Global Arguments dlbr {n} _.

Axiom dlT : forall (n : nat), IsTrunc 1 (deloop n).

Definition deloop_dot
  := sig deloop.

Definition dlT_dot
  : IsTrunc 1 deloop_dot.
Proof.
  srapply @trunc_sigma; intro; apply dlT.
Defined.

Definition Sdli
  : deloop_dot -> deloop_dot
  := sigma_function S (@dli).

Section deloop_ind.

Definition dltw'_type 
  (P : forall n : nat, deloop n -> Type)
  (dli' : forall (n : nat) (a : deloop n) (a' : P n a), P n.+1 (dli a))
  : Type
  := forall (n : nat) (a : deloop n) (a' : P n a),
  transport (P n.+2) (dltw a) (dli' _ _ (dli' _ _ a')) = dli' _ _ (dli' _ _ a').

Definition dldo'_type
  (P : forall n : nat, deloop n -> Type)
  (dli' : forall (n : nat) (a : deloop n) (a' : P n a), P n.+1 (dli a))
  (dltw' : dltw'_type P dli')
  : Type
  := forall (n : nat) (a : deloop n) (a' : P n a),
  (ap (fun z => transport (P n.+2) z (dli' _ _ (dli' _ _ a'))) (dldo a))^
  @ concat_D (dltw' _ _ a') (dltw' _ _ a')
  = idpath.

Definition dlbr'_type
  (P : forall n : nat, deloop n -> Type)
  (dli' : forall (n : nat) (a : deloop n) (a' : P n a), P n.+1 (dli a))
  (dltw' : dltw'_type P dli')
  : Type
  := forall (n : nat) (a : deloop n) (a' : P n a),
  (ap (fun z => transport (P n.+3) z (dli' _ _ (dli' _ _ (dli' _ _ a')))) (dlbr a))^ @
  concat_D
    (concat_D
      (dltw' _ _ (dli' _ _ a'))
      (transport_ap_nat (@dli) (@dli') (dltw a) (dltw' _ _ a')))
    (dltw' _ _ (dli' _ _ a'))
  = concat_D
    (concat_D
      (transport_ap_nat (@dli) (@dli') (dltw a) (dltw' _ _ a'))
      (dltw' _ _ (dli' _ _ a')))
    (transport_ap_nat (@dli) (@dli') (dltw a) (dltw' _ _ a')).

Context (P : forall n : nat, deloop n -> Type)
  (dlpt0' : P 0 dlpt0)
  (dli' : forall (n : nat) (a : deloop n) (a' : P n a), P n.+1 (dli a)).
Arguments dli' {n} {a} _.

Fixpoint deloop_ind
  (dltw' : dltw'_type P (@dli'))
  (dldo' : dldo'_type P (@dli') dltw')
  (dlbr' : dlbr'_type P (@dli') dltw')
  (dlT' : forall (n : nat) (x : deloop n), IsTrunc 1 (P n x))
  (n : nat) (s : deloop n)
  : P n s
  := match s with
  | dlpt0 => fun _ => fun _ => fun _ => fun _ => dlpt0'
  | dli n s0 => fun _ => fun _ => fun _ => fun _ =>
    dli' (deloop_ind dltw' dldo' dlbr' dlT' n s0)
  end dltw' dldo' dlbr' dlT'.

Axiom deloop_ind_beta_dltw
  : forall 
  (dltw' : dltw'_type P (@dli'))
  (dldo' : dldo'_type P (@dli') dltw')
  (dlbr' : dlbr'_type P (@dli') dltw')
  (dlT' : forall (n : nat) (x : deloop n), IsTrunc 1 (P n x))
  (n : nat) (a : deloop n),
  apD (deloop_ind dltw' dldo' dlbr' dlT' n.+2) (dltw a) =
  dltw' _ _ (deloop_ind dltw' dldo' dlbr' dlT' n a).

Lemma deloop_ind_to_set
  (dltw' : dltw'_type P (@dli'))
  (dlT' : forall (n : nat) (x : deloop n), IsTrunc 0 (P n x))
  (n : nat) (s : deloop n)
  : P n s.
Proof.
  srapply @deloop_ind.
  { exact dltw'. }
  all: repeat intro; srapply @path_ishprop.
Defined.

Lemma deloop_ind_to_prop
  (dlT' : forall (n : nat) (x : deloop n), IsHProp (P n x))
  (n : nat) (s : deloop n)
  : P n s.
Proof.
  srapply @deloop_ind_to_set.
  repeat intro; srapply @path_ishprop.
Defined.

End deloop_ind.

Section deloop_rec.

Definition dltw'_rec_type
  (P : nat -> Type)
  (dli' : forall n : nat, P n -> P n.+1)
  : Type
  := forall (n : nat) (a' : P n),
  dli' _ (dli' _ a') = dli' _ (dli' _ a').

Definition dldo'_rec_type
  (P : nat -> Type)
  (dli' : forall n : nat, P n -> P n.+1)
  (dltw' : dltw'_rec_type P dli')
  : Type
  := forall (n : nat) (a' : P n),
  dltw' n a' @ dltw' n a' = idpath.

Definition dlbr'_rec_type
  (P : nat -> Type)
  (dli' : forall n : nat, P n -> P n.+1)
  (dltw' : dltw'_rec_type P dli')
  : Type
  := forall (n : nat) (a' : P n),
    dltw' _ (dli' _ a') @ ap (dli' _) (dltw' _ a') @ dltw' _ (dli' _ a') = ap (dli' _) (dltw' _ a') @ dltw' _ (dli' _ a') @ ap (dli' _) (dltw' _ a').

Context (P : nat -> Type)
  (dlpt0' : P 0)
  (dli' : forall n : nat, P n -> P n.+1).
Arguments dli' {_} _.

Definition deloop_rec_do_ind_of_rec
  (dltw' : dltw'_rec_type P (@dli'))
  (dldo' : dldo'_rec_type P (@dli') dltw')
  : forall (n : nat) (a : deloop n) (a' : P n),
  (ap (fun z : dli (dli a) = dli (dli a) => transport (fun _ : deloop n.+2 => P n.+2) z (dli' (dli' a')))
(dldo a))^ @
  concat_D
    (transport_const (dltw a) (dli' (dli' a')) @ dltw' n a')
    (transport_const (dltw a) (dli' (dli' a')) @ dltw' n a') =
  transport_const 1 (dli' (dli' a')).
Proof.
  intros.
  refine (whiskerL _ (concat_D_const_p (dltw' n a') (dltw' n a')) @ _).
  refine (concat_p_pp _ _ _ @ _).
  refine (whiskerL _ (dldo' _ a') @ _).
  refine (concat_p1 _ @ _).
  apply moveR_Vp.
  refine (transport_const_pq (dldo a) (dli' (dli' a')))^.
Defined.

Definition deloop_rec_br_ind_of_rec
  (dltw' : dltw'_rec_type P (@dli'))
  (dlbr' : dlbr'_rec_type P (@dli') dltw')
  : forall (n : nat) (a : deloop n) (a' : P n), (ap
   (fun z : dli (dli (dli a)) = dli (dli (dli a)) => transport (fun _ : deloop n.+3 => P n.+3) z (dli' (dli' (dli' a')))) (dlbr a))^ @
  concat_D
    (concat_D (transport_const (dltw (dli a)) (dli' (dli' (dli' a'))) @ dltw' n.+1 (dli' a'))
      (transport_ap_nat (@dli) (fun (n0 : nat) (_ : deloop n0) => @dli' n0) (dltw a)
        (transport_const (dltw a) (dli' (dli' a')) @ dltw' n a')))
    (transport_const (dltw (dli a)) (dli' (dli' (dli' a'))) @ dltw' n.+1 (dli' a'))
  = concat_D
    (concat_D
      (transport_ap_nat (@dli) (fun (n0 : nat) (_ : deloop n0) => @dli' n0) (dltw a)
        (transport_const (dltw a) (dli' (dli' a')) @ dltw' n a'))
      (transport_const (dltw (dli a)) (dli' (dli' (dli' a'))) @ dltw' n.+1 (dli' a')))
    (transport_ap_nat (@dli) (fun (n0 : nat) (_ : deloop n0) => @dli' n0) (dltw a)
      (transport_const (dltw a) (dli' (dli' a')) @ dltw' n a')).
Proof.
  intros.
  rewrite transport_ap_nat_transport_const_p.
  rewrite concat_D_const_p, concat_D_const_p, concat_D_const_p, concat_D_const_p.
  refine (concat_p_pp _ _ _ @ _).
  refine (whiskerL _ (dlbr' _ a') @ _); apply whiskerR.
  apply moveR_Vp.
  exact (transport_const_pq _ _)^.
Defined.

Definition deloop_rec
  (dltw' : dltw'_rec_type P (@dli'))
  (dldo' : dldo'_rec_type P (@dli') dltw')
  (dlbr' : dlbr'_rec_type P (@dli') dltw')
  (dlT' : forall n : nat, IsTrunc 1 (P n))
  (m : nat)
  : deloop m -> P m.
Proof.
  srefine (deloop_ind (fun n _ => P n) dlpt0' (fun n _ => dli') _ _ _ (fun n _ => dlT' n) m).
  + unfold dltw'_type. simpl; intros. refine (transport_const _ _ @ _). exact (dltw' _ a').
  + unfold dldo'_type. apply deloop_rec_do_ind_of_rec. exact dldo'.
  + unfold dlbr'_type. apply deloop_rec_br_ind_of_rec. exact dlbr'.
Defined.

Lemma deloop_rec_beta_dltw
  (dltw' : dltw'_rec_type P (@dli'))
  (dldo' : dldo'_rec_type P (@dli') dltw')
  (dlbr' : dlbr'_rec_type P (@dli') dltw')
  (dlT' : forall n : nat, IsTrunc 1 (P n))
  (n : nat) (a : deloop n)
  : ap (deloop_rec dltw' dldo' dlbr' dlT' n.+2) (dltw a)
    = dltw' _ (deloop_rec dltw' dldo' dlbr' dlT' _ a).
Proof.
  eapply (cancelL (transport_const (dltw a) _)).
  refine ((apD_const _ (dltw a))^ @ _).
  refine (deloop_ind_beta_dltw _ _ _ _ _ _ _ _ _).
Defined.

Lemma deloop_rec_to_set
  (dlT' : forall n : nat, IsTrunc 0 (P n))
  (dltw' : dltw'_rec_type P (@dli'))
  (m : nat)
  : deloop m -> P m.
Proof.
  srapply @deloop_rec.
  { exact dltw'. }
  all: repeat intro; srapply @path_ishprop.
Defined.

Lemma deloop_rec_to_prop
  (dlT' : forall n : nat, IsHProp (P n))
  (m : nat)
  : deloop m -> P m.
Proof.
  srapply @deloop_rec_to_set.
  repeat intro; srapply @path_ishprop.
Defined.

End deloop_rec.

Section deloop_rec_const.

Context (P : Type)
  (dlpt0' : P )
  (dli' : P -> P)
  (dltw' : forall a' : P, dli' (dli' a') = dli' (dli' a'))
  (dldo' : forall a' : P, dltw' a' @ dltw' a' = idpath)
  (dlbr' : forall a' : P, (dltw' (dli' a') @ ap dli' (dltw' a')) @ dltw' (dli' a') = (ap dli' (dltw' a') @ dltw' (dli' a')) @ ap dli' (dltw' a'))
  (dlT' : IsTrunc 1 P).

Definition deloop_rec_const
  (m : nat)
  : deloop m -> P.
Proof.
  srapply @deloop_rec; simpl.
  + exact dlpt0'.
  + intro; exact dli'.
  + unfold dltw'_rec_type; simpl. intro; exact dltw'.
  + unfold dldo'_rec_type; simpl. intro; exact dldo'.
  + unfold dlbr'_rec_type; simpl. intro; exact dlbr'.
Defined.

Lemma deloop_rec_const_beta_dltw
  (m : nat) (a : deloop m)
  : ap (deloop_rec_const m.+2) (dltw a) = dltw' (deloop_rec_const m a).
Proof.
  srapply @deloop_rec_beta_dltw.
Defined.

End deloop_rec_const.

Section deloop_rec_subuniverse.

Lemma deloop_rec_truncfib
  (A : Type)
  (Q : nat -> A -> Type)
  (T : forall n : nat, IsTrunc 1 {a : A & Q n a})
  (Tf : forall (n : nat) (a : A), IsHProp (Q n a))
  (dlpt0' : A)
  (dlpt0'q : Q 0 dlpt0')
  (dli' : nat -> A -> A)
  (dli'q : forall (n : nat) (a : A), Q n a -> Q n.+1 (dli' n a))
  (dltw' : forall (n : nat) (a : A), dli' n.+1 (dli' n a) = dli' n.+1 (dli' n a))
  (dldo' : forall (n : nat) (a : A), dltw' n a @ dltw' n a = idpath)
  (dlbr' : forall (n : nat) (a : A), (dltw' n.+1 (dli' n a) @ ap (dli' n.+2) (dltw' n a)) @ dltw' n.+1 (dli' n a) = (ap (dli' n.+2) (dltw' n a) @ dltw' n.+1 (dli' n a)) @ ap (dli' n.+2) (dltw' n a))
  : forall (n : nat), deloop n -> {a : A & Q n a}.
Proof.
  srapply @deloop_rec; hnf.
  + exists dlpt0'. exact dlpt0'q.
  + intro n. exact (sigma_function (dli' n) (dli'q n)).
  + simpl. intros n [a q]; unfold sigma_function.
    srapply @sigma_truncfib. apply dltw'.
  + abstract (intros n [a q];
    refine (sigma_truncfib_concat _ _ (dltw' n a) (dltw' n a) @ _ @ @sigma_truncfib_1 _ (fun a : A => Q n.+2 a) _ _ (Tf n.+2) _ idpath);
    apply ap; apply dldo').
  + abstract (intros n [a q]; simpl;
    rewrite ap_sigma_function_p;
    unfold path_sigma_function;
    rewrite path_path_sigma'_concat, path_path_sigma'_concat, path_path_sigma'_concat, path_path_sigma'_concat;
    srapply @path_path_sigma'_truncfib;
    rewrite sigma_truncfib_pr1;
    apply dlbr').
Defined.

Lemma deloop_rec_truncfib_beta_dltw
  (A : Type)
  (Q : nat -> A -> Type)
  (T : forall n : nat, IsTrunc 1 {a : A & Q n a})
  (Tf : forall (n : nat) (a : A), IsHProp (Q n a))
  (dlpt0' : A)
  (dlpt0'q : Q 0 dlpt0')
  (dli' : nat -> A -> A)
  (dli'q : forall (n : nat) (a : A), Q n a -> Q n.+1 (dli' n a))
  (dltw' : forall (n : nat) (a : A), dli' n.+1 (dli' n a) = dli' n.+1 (dli' n a))
  (dldo' : forall (n : nat) (a : A), dltw' n a @ dltw' n a = idpath)
  (dlbr' : forall (n : nat) (a : A), (dltw' n.+1 (dli' n a) @ ap (dli' n.+2) (dltw' n a)) @ dltw' n.+1 (dli' n a) = (ap (dli' n.+2) (dltw' n a) @ dltw' n.+1 (dli' n a)) @ ap (dli' n.+2) (dltw' n a))
  (n : nat) (a : deloop n)
  : ap pr1 (ap (deloop_rec_truncfib A Q T Tf dlpt0' dlpt0'q dli' dli'q dltw' dldo' dlbr' n.+2) (dltw a))
    = dltw' n (deloop_rec_truncfib A Q T Tf dlpt0' dlpt0'q dli' dli'q dltw' dldo' dlbr' n a).1.
Proof.
  unfold deloop_rec_truncfib.
  refine (ap (ap pr1) (deloop_rec_beta_dltw _ _ _ _ _ _ _ _ a) @ _).
  apply sigma_truncfib_pr1.
Defined.

Definition deloop_rec_subuniverse
  := deloop_rec_truncfib Type.

Definition deloop_rec_subuniverse_beta_dltw
  := deloop_rec_truncfib_beta_dltw Type.

End deloop_rec_subuniverse.

End deloop.

Ltac unfold_deloop_types
  := try unfold dltw'_type in *;
      try unfold dldo'_type in *;
      try unfold dlbr'_type in *;
      try unfold dltw'_rec_type in *;
      try unfold dldo'_rec_type in *;
      try unfold dlbr'_rec_type in *.

Open Scope nat.

(** deloop 0 and deloop 1 are contractible **)

Lemma deloop_contr_0 `{Funext}
  : forall (n : nat) (a : deloop n), n = 0 -> dlpt n = a.
Proof.
  srapply @deloop_ind_to_set; simpl.
  + intros; exact idpath.
  + intros n b IH p. apply Empty_rec. exact (not_sn_0 p).
  + unfold dltw'_type. intros. srapply @path_forall. intro p.
    apply Empty_rec. exact (not_sn_0 p).
  + intros; srapply @trunc_forall; intros; srapply @dlT.
Defined.

Lemma Contr_deloop0 `{Funext}
  : Contr (deloop 0).
Proof.
  srapply @Build_Contr.
  + apply dlpt.
  + intro a. exact (deloop_contr_0 0 a idpath).
Defined.

Lemma deloop_contr_1 `{Funext}
  : forall (n : nat) (a : deloop n), n = 1 -> dlpt n = a.
Proof.
  srapply @deloop_ind_to_set; simpl.
  + intros; exact idpath. (* Or ex falso; we don't care. *)
  + intros n b _ p. induction n.
    - apply ap. apply Contr_deloop0.
    - apply Empty_rec. exact (not_ssn_1 p).
  + unfold dltw'_type; intros; simpl. srapply @path_forall. intro p.
    apply Empty_rec. exact (not_ssn_1 p).
  + intros; srapply @trunc_forall; intros; srapply @dlT.
Defined.

Lemma Contr_deloop1 `{Funext}
  : Contr (deloop 1).
Proof.
  srapply @Build_Contr.
  + apply dlpt.
  + intro a. exact (deloop_contr_1 1 a idpath).
Defined.

(** The argument, of course, fails starting at 2! **)
Lemma deloop_contr_2 `{Funext}
  : forall (n : nat) (a : deloop n), n = 2 -> dlpt n = a.
Proof.
  assert (T : forall (n : nat) (x : deloop n), IsHSet (n = 2 -> dlpt n = x)).
  { intros; srapply @trunc_forall; intros; srapply @dlT. }
  srefine (deloop_ind_to_set _ _ _ _ T); simpl.
  + intros; exact idpath.
  + intros n b _ p. induction n.
    - apply Empty_rec. exact (not_ssn_1 p^).
    - clear IHn. induction n.
      * apply ap. apply Contr_deloop1.
      * apply Empty_rec. exact (not_ssn_1 (sn_sm p)).
  + unfold dltw'_type; intros; simpl. srapply @path_forall. intro p.
    induction n.
    - simpl. refine (@transport_forall_fun_path_const_l_idmap_r (deloop 2) (fun _ => 2 = 2) (dlpt 2) _ _ (dltw a) _ p @ _).
      refine (_ @ concat_p1 _); apply whiskerL. (* contradiction! *)
Abort.

(** deloop n is connected for every n **)
Lemma Connected_deloopn
  : forall n : nat, Contr (Trunc 0 (deloop n)).
Proof.
  intro n. srapply @Build_Contr.
  + apply tr. exact (dlpt n).
  + srapply @Trunc_ind.
    revert n. srapply @deloop_ind_to_prop; simpl.
    - constructor.
    - intros m b p.
      exact (ap (truncmap 0 dli) p).
Defined.

(** if we had a path tw = refl, then deloop n would be contractible **)
Lemma almost_contr_deloop_n
  : (forall (n : nat) (a : deloop n), dltw a = idpath)
    -> forall n : nat, Contr (deloop n).
Proof.
  intros twrefl n. srapply @Build_Contr.
  + apply dlpt.
  + revert n. srapply @deloop_ind_to_set; simpl.
    - constructor.
    - intros n a a'. exact (ap dli a').
    - intros n a a'; simpl.
      exact (ap (fun z => transport (fun s => dlpt n.+2 = s) z (ap dli (ap dli a'))) (twrefl n a)).
    - intros; srapply @dlT.
Defined.


(** tw commutes with ap i (ap i) **)
Lemma dltw_natural
  : forall (n : nat) (a b : deloop n) (p : a = b),
  ap dli (ap dli p) @ dltw b = dltw a @ ap dli (ap dli p).
Proof.
  intros; induction p; simpl.
  exact (concat_1p _ @ (concat_p1 _)^).
Defined.
Global Arguments dltw_natural {n} {a} {b} p.

Lemma dltw_natural_n
  : forall (n : nat) (a b : deloop n) (p : a = b),
  ap Sdli (ap Sdli (path_sigma' deloop idpath p)) @ path_sigma' deloop idpath (dltw b) = path_sigma' deloop idpath (dltw a) @ ap Sdli (ap Sdli (path_sigma' deloop idpath p)).
Proof.
  intros; induction p; simpl.
  exact (concat_1p _ @ (concat_p1 _)^).
Defined.
Global Arguments dltw_natural_n {n} {a} {b} p.

Lemma dltw_natural_n_sigma
  {x x' : {n : nat & deloop n}} (p : x = x')
  : ap Sdli (ap Sdli p) @ path_sigma' deloop idpath (dltw _) = path_sigma' deloop idpath (dltw _) @ ap Sdli (ap Sdli p).
Proof.
  intros; induction p; simpl.
  exact (concat_1p _ @ (concat_p1 _)^).
Defined.

Lemma dltw_natural_n_sigma_f
  (f : {n : nat & deloop n} -> {n : nat & deloop n})
  {n : nat} {a : deloop n} (p : f (n; a) = (n; a))
  : ap Sdli (ap Sdli p) @ path_sigma' deloop idpath (dltw _) = path_sigma' deloop idpath (dltw (f (n; a)).2) @ ap Sdli (ap Sdli p).
Proof.
  exact (@dltw_natural_n_sigma (f (n; a)) (n; a) p).
Defined.

(** Small results using connectedness of deloop **)
Section mere_statements.
Context `{Univalence}.

Lemma mere_dlptn
  : forall (n : nat) (a : deloop n), merely (dlpt n = a).
Proof.
  intro n.
  exact (@conn_to_prop _ (deloop n) (Connected_deloopn n) (fun a => merely (dlpt n = a)) _ (dlpt n) (tr idpath)).
Defined.

Lemma merely_dli_inj
  : forall (n : nat) (a : deloop n.+1), merely {a' : deloop n & a = dli a'}.
Proof.
  intro n.
  srefine (@conn_to_prop _ (deloop n.+1) (Connected_deloopn n.+1) (fun a => merely {a' : deloop n & a = dli a'}) _ (dlpt n.+1) _); hnf.
  apply tr. exists (dlpt n). exact idpath.
Defined.
End mere_statements.


(** Symmetric monoidal structure on deloop_dot **)

Require Import smonoidalgroupoid.

Section deloop_smgpd.
Context `{Univalence}.

  Definition dltw_dot
    : forall a : deloop_dot, Sdli (Sdli a) = Sdli (Sdli a).
  Proof.
    intro. exact (path_sigma' deloop idpath (dltw a.2)).
  Defined.

  Lemma dldo_dot
    : forall a : deloop_dot, dltw_dot a @ dltw_dot a = idpath.
  Proof.
    intro.
    refine (path_sigma'_concat _ _ _ _ _ @ _). simpl.
    srefine (path_sigma'_1 _ _ idpath _); simpl.
    exact (dldo _)^.
  Defined.

  Lemma dlbr_dot
    : forall a : deloop_dot,
    dltw_dot (Sdli a) @ ap Sdli (dltw_dot a) @ dltw_dot (Sdli a) = ap Sdli (dltw_dot a) @ dltw_dot (Sdli a) @ ap Sdli (dltw_dot a).
  Proof.
    intro.
    unfold Sdli.
    repeat rewrite ap_sigma_function_p.
    unfold dltw_dot. unfold path_sigma_function.
    rewrite <- path_sigma'_ap'_p.
    change ((path_sigma' deloop 1 (dltw (Sdli a).2) @ ap Sdli (path_sigma' deloop 1 (dltw a.2))) @ path_sigma' deloop 1 (dltw (Sdli a).2) = (ap Sdli (path_sigma' deloop 1 (dltw a.2)) @ path_sigma' deloop 1 (dltw (Sdli a).2)) @ ap Sdli (path_sigma' deloop 1 (dltw a.2))).
    rewrite ap_sigma_function_path_sigma'_1.
    repeat rewrite path_sigma'_concat. simpl. apply ap.
    apply dlbr.
  Defined.

  Lemma dltw_dot_natural
    {x y : deloop_dot} (p : x = y)
    : ap Sdli (ap Sdli p) @ dltw_dot y = dltw_dot x @ ap Sdli (ap Sdli p).
  Proof.
    induction p; simpl.
    exact (concat_1p _ @ (concat_p1 _)^).
  Defined.

Definition deloop_e
  : deloop_dot
  := (0; dlpt0).

  Definition deloop_m_dli
    : (deloop_dot -> deloop_dot) -> deloop_dot -> deloop_dot.
  Proof.
    intro a'. exact (Sdli o a').
  Defined.

  Definition deloop_m_dltw
    : forall a' : deloop_dot -> deloop_dot, deloop_m_dli (deloop_m_dli a') = deloop_m_dli (deloop_m_dli a').
  Proof.
    unfold deloop_m_dli.
    intros. srapply @path_forall; intro x.
    apply dltw_dot.
  Defined.

  Definition deloop_m_dldo
    : forall a' : deloop_dot -> deloop_dot, deloop_m_dltw a' @ deloop_m_dltw a' = 1%path.
  Proof.
    unfold deloop_m_dltw.
    intros.
    refine ((path_forall_pp _ _ _ _ _)^ @ _).
    refine (_ @ path_forall_1 _).
    apply ap. srapply @path_forall; intro x.
    apply dldo_dot.
  Defined.

  Definition deloop_m_dlbr
    : forall a' : deloop_dot -> deloop_dot,
      (deloop_m_dltw (deloop_m_dli a') @ ap deloop_m_dli (deloop_m_dltw a')) @ deloop_m_dltw (deloop_m_dli a')
      = (ap deloop_m_dli (deloop_m_dltw a') @ deloop_m_dltw (deloop_m_dli a')) @ ap deloop_m_dli (deloop_m_dltw a').
  Proof.
    unfold deloop_m_dltw, deloop_m_dli.
    intros.
    rewrite ap_compose_pf.
    repeat rewrite <- path_forall_pp.
    apply ap. srapply @path_forall; intro x.
    apply dlbr_dot.
  Defined.

Definition deloop_m
  : deloop_dot -> deloop_dot -> deloop_dot.
Proof.
  srapply @sig_rect; intro n; revert n; hnf.
  assert (T : (IsTrunc 1 (deloop_dot -> deloop_dot))).
  { exact (@trunc_forall _ _ _ _ (fun _ => dlT_dot)). }
  srefine (deloop_rec_const (deloop_dot -> deloop_dot) _ _ _ _ _ _); clear T.
  + exact idmap.
  + exact deloop_m_dli.
  + exact deloop_m_dltw.
  + exact deloop_m_dldo.
  + exact deloop_m_dlbr.
Defined.

Lemma ap_sig_rect_ap_base
  {A : Type} (B : A -> Type) (C : Type)
  (f : forall a : A, B a -> C)
  (a0 : A)
  {b b' : B a0} (p : b = b')
  : ap (sig_rect (fun _ : sig B => C) f) (ap (fun b : B a0 => (a0; b)) p) = ap (f a0) p.
Proof.
  induction p; constructor.
Defined.

Lemma ap_deloop_m_path_sigma_dltw {n : nat} (a : deloop n) (b : deloop_dot)
  : ap (fun x => deloop_m x b) (path_sigma' deloop idpath (dltw a)) = dltw_dot (deloop_m (n; a) b).
Proof.
  refine (@ap_compose deloop_dot (deloop_dot -> deloop_dot) deloop_dot deloop_m (fun q => q b) _ _ _ @ _).
  unfold deloop_m.
  refine (ap (ap (fun q : deloop_dot -> deloop_dot => q b)) (ap_sig_rect_ap_base deloop (deloop_dot -> deloop_dot) _ n.+2 (dltw a)) @ _).
  unfold deloop_rec_const.
  refine (ap (ap (fun q : deloop_dot -> deloop_dot => q b)) (@deloop_rec_beta_dltw (fun _ : nat => deloop_dot -> deloop_dot) idmap (fun _ : nat => deloop_m_dli) (fun _ : nat => deloop_m_dltw) (fun _ : nat => deloop_m_dldo) (fun _ : nat => deloop_m_dlbr) (fun _ : nat => (@trunc_forall _ _ _ _ (fun _ => dlT_dot))) n a) @ _).
  unfold deloop_m_dltw.
  refine (ap_pf_D _ b).
Defined.

Lemma ap_deloop_m_dltw {n : nat} (a : deloop n) (b : deloop_dot)
  : ap (fun x : deloop n.+2 => deloop_m (n.+2; x) b) (dltw a) = dltw_dot (deloop_m (n; a) b).
Proof.
  refine (@ap_compose (deloop n.+2) deloop_dot deloop_dot (fun x => (n.+2; x)) (fun x => deloop_m x b) _ _ (dltw a) @ _).
  srapply @ap_deloop_m_path_sigma_dltw.
Defined.

Lemma ap_deloop_m_dltw_dot (a : deloop_dot) (b : deloop_dot)
  : ap (fun z : deloop_dot => deloop_m z b) (dltw_dot a) = dltw_dot (deloop_m a b).
Proof.
  refine (ap_deloop_m_path_sigma_dltw a.2 b).
Defined.

Lemma ap011_deloop_m_ap_Sdli (* compare: ap011_sapp_ap_cons *)
  {a a' b b' : deloop_dot} (p : a = a') (q : b = b')
  : ap011 deloop_m (ap Sdli p) q = ap Sdli (ap011 deloop_m p q).
Proof.
  induction p, q; constructor.
Defined.

Definition alpha_deloop
  : forall a b c : deloop_dot, deloop_m (deloop_m a b) c = deloop_m a (deloop_m b c).
Proof.
  intros [n a] b c; revert a; revert n.
  assert (T : (forall (n : nat) (a : deloop n), IsHSet (deloop_m (deloop_m (n; a) b) c = deloop_m (n; a) (deloop_m b c)))).
  { intros. srapply (@istrunc_paths _ _ dlT_dot). }
  srefine (deloop_ind_to_set _ _ _ _ T); clear T; hnf.
  + constructor.
  + intros n a h.
    change (Sdli (deloop_m (deloop_m (n; a) b) c) = Sdli (deloop_m (n; a) (deloop_m b c))).
    apply ap. exact h.
  + abstract (intros n a a'; simpl;
    srefine (@transport_paths_FlFr (deloop n.+2) _ (fun a0 => deloop_m (deloop_m (n.+2; a0) b) c) (fun a0 => deloop_m (n.+2; a0) (deloop_m b c)) _ _ (dltw a) _ @ concat_pp_p _ _ _ @ _); apply moveR_Vp;
    srefine (whiskerL _ (ap_deloop_m_dltw _ _) @ _);
    srefine (_ @ whiskerR (@ap_compose (deloop n.+2) deloop_dot deloop_dot (fun a0 => deloop_m (n.+2; a0) b) (fun x => deloop_m x c) _ _ (dltw a))^ _);
    rewrite ap_deloop_m_dltw;
    rewrite ap_deloop_m_path_sigma_dltw;
    change (ap Sdli (ap Sdli a') @ path_sigma' (fun n0 : nat => deloop n0) 1 (dltw (deloop_m (n; a) (deloop_m b c)).2) = path_sigma' deloop idpath (dltw (deloop_m (deloop_m (n; a) b) c).2) @ ap Sdli (ap Sdli a'));
    apply dltw_dot_natural ) using alpha_deloop_dltw.
Defined.

Definition lambda_deloop
  : forall b : deloop_dot, deloop_m deloop_e b = b.
Proof.
  constructor.
Defined.

Definition rho_deloop
  : forall a : deloop_dot, deloop_m a deloop_e = a.
Proof.
  intros [n a]; revert a; revert n.
  assert (T : (forall (n : nat) (a : deloop n), IsHSet (deloop_m (n; a) deloop_e = (n; a)))).
  { intros. srapply (@istrunc_paths _ _ dlT_dot). }
  srefine (deloop_ind_to_set _ _ _ _ T); clear T; hnf.
  + constructor.
  + intros n a h.
    exact (ap Sdli h).
  + abstract (intros n a a'; simpl;
    srefine (@transport_paths_FlFr (deloop n.+2) _ (fun a0 => deloop_m (n.+2; a0) deloop_e) (fun a0 => (n.+2; a0)) _ _ (dltw a) _ @ concat_pp_p _ _ _ @ _); apply moveR_Vp;
    rewrite ap_deloop_m_dltw;
    change (ap Sdli (ap Sdli a') @ path_sigma' (fun n0 : nat => deloop n0) 1 (dltw a) = path_sigma' (fun n0 : nat => deloop n0) 1 (dltw (deloop_m (n; a) deloop_e).2) @ ap Sdli (ap Sdli a'));
    exact (dltw_dot_natural a') ) using rho_deloop_dltw.
Defined.

    Lemma tau_deloop_Q_dltw (y : deloop_dot)
      : forall (n : nat) (a : deloop n) (a' : Sdli (deloop_m (n; a) y) = deloop_m (n; a) (Sdli y)),
        transport
          (fun a0 : deloop n.+2 => Sdli (deloop_m (n.+2; a0) y) = deloop_m (n.+2; a0) (Sdli y))
          (dltw a)
          (dltw_dot (deloop_m (n.+1; dli a) y)
        @  ap Sdli (dltw_dot (deloop_m (n; a) y) @ ap Sdli a'))
        = dltw_dot (deloop_m (n.+1; dli a) y) @ ap Sdli (dltw_dot (deloop_m (n; a) y) @ ap Sdli a').
    Proof.
      intros n a h.
      refine (@transport_paths_FlFr (deloop n.+2) _ (fun a0 => Sdli (deloop_m (n.+2; a0) y)) (fun a0 => deloop_m (n.+2; a0) (Sdli y)) _ _ (dltw a) _ @ concat_pp_p _ _ _ @ _); apply moveR_Vp.
      rewrite (@ap_compose (deloop n.+2) deloop_dot deloop_dot (fun a0 => deloop_m (n.+2; a0) y) Sdli _ _ (dltw a)).
      repeat rewrite ap_deloop_m_dltw.
      repeat rewrite ap_pp.
      repeat rewrite concat_p_pp; refine (concat_pp_p _ _ _ @ _).
      refine (whiskerL _ (dltw_dot_natural _) @ concat_p_pp _ _ _ @ _); apply whiskerR.
      apply dlbr_dot.
    Defined.

  Definition tau_deloop_Q
    : forall (y x : deloop_dot), Sdli (deloop_m x y) = deloop_m x (Sdli y).
  Proof.
    intros y [n a]; revert a; revert n.
    assert (T : (forall (n : nat) (a : deloop n), IsHSet (Sdli (deloop_m (n; a) y) = deloop_m (n; a) (Sdli y)))).
    { intros. srapply (@istrunc_paths _ _ dlT_dot). }
    srefine (deloop_ind_to_set _ _ _ _ T); clear T; hnf.
    + constructor.
    + intros n a h. change (Sdli (Sdli (deloop_m (n; a) y)) = Sdli (deloop_m (n; a) (Sdli y))).
      exact (dltw_dot (deloop_m (n; a) y) @ (ap Sdli h)).
    + apply tau_deloop_Q_dltw.
  Defined.

  Definition tau_deloop_R
    : forall (n : nat) (a : deloop n) (b : deloop_dot),
      ap Sdli (tau_deloop_Q (n; a) b) @ (tau_deloop_Q (n.+1; dli a) b @ ap (fun a0 : deloop n.+2 => deloop_m b (n.+2; a0)) (dltw a))
      = dltw_dot (deloop_m b (n; a)) @ (ap Sdli (tau_deloop_Q (n; a) b) @ tau_deloop_Q (n.+1; dli a) b).
  Proof.
    intros n a [m b]; revert b; revert m.
    assert (T : (forall m b, IsHProp (ap Sdli (tau_deloop_Q (n; a) (m; b)) @ (tau_deloop_Q (n.+1; dli a) (m; b) @ ap (fun a0 : deloop n.+2 => deloop_m (m; b) (n.+2; a0)) (dltw a)) = dltw_dot (deloop_m (m; b) (n; a)) @ (ap Sdli (tau_deloop_Q (n; a) (m; b)) @ tau_deloop_Q (n.+1; dli a) (m; b))))).
    { intros. srapply (@istrunc_paths _ _ dlT_dot). }
    srapply @deloop_ind_to_prop; hnf.
    + refine (concat_1p _ @ concat_1p _ @ (concat_p1 _)^).
    + intros m b IHb.
      change (
(ap Sdli (dltw_dot (deloop_m (m; b) (n; a)) @ ap Sdli (tau_deloop_Q (n; a) (m; b)))) @
((dltw_dot (deloop_m (m; b) (n.+1; dli a)) @ ap Sdli (tau_deloop_Q (n.+1; dli a) (m; b))) @
 ap (fun a0 : deloop n.+2 => Sdli (deloop_m (m; b) (n.+2; a0))) (dltw a)) =
dltw_dot (Sdli (deloop_m (m; b) (n; a))) @
((ap Sdli (dltw_dot (deloop_m (m; b) (n; a)) @ ap Sdli (tau_deloop_Q (n; a) (m; b)))) @ (dltw_dot (deloop_m (m; b) (n.+1; dli a)) @ ap Sdli (tau_deloop_Q (n.+1; dli a) (m; b))))
).
      repeat rewrite (ap_pp Sdli).
      refine (concat_p_pp _ _ _ @ whiskerR (concat_p_pp _ _ _ @ whiskerR (concat_pp_p _ _ _ @ whiskerL _ (dltw_dot_natural (tau_deloop_Q (n; a) (m; b)))) _) _ @ _).
      refine (_ @ whiskerL _ (whiskerR (whiskerL _ (dltw_dot_natural (tau_deloop_Q (n; a) (m; b)))^ @ concat_p_pp _ _ _) _ @ concat_pp_p _ _ _)).
      refine (_ @ whiskerR (whiskerR (dlbr_dot (deloop_m (m; b) (n; a)))^ _ @ concat_pp_p _ _ _ @ concat_pp_p _ _ _) _ @ concat_pp_p _ _ _);
      repeat rewrite concat_pp_p; apply whiskerL; apply whiskerL.
      refine (whiskerL _ (whiskerL _ (ap_compose (fun a0 : deloop n.+2 => deloop_m (m; b) (n.+2; a0)) Sdli _)) @ _).
      repeat rewrite <- (ap_pp Sdli); apply ap; exact IHb.
  Qed.

  Lemma tau_deloop_dltw
    : forall (n : nat) (a : deloop n) (a' : forall b : {n0 : nat & deloop n0}, deloop_m (n; a) b = deloop_m b (n; a)),
      transport
        (fun a0 : deloop n.+2 => forall b : {n0 : nat & deloop n0}, deloop_m (n.+2; a0) b = deloop_m b (n.+2; a0))
        (dltw a)
        (fun b : {n0 : nat & deloop n0} => ap Sdli (ap Sdli (a' b) @ tau_deloop_Q (n; a) b) @ tau_deloop_Q (n.+1; dli a) b)
      = (fun b : {n0 : nat & deloop n0} => ap Sdli (ap Sdli (a' b) @ tau_deloop_Q (n; a) b) @ tau_deloop_Q (n.+1; dli a) b).
  Proof.
    intros.
    srapply @path_forall; intro b.
    refine (@transport_forall' (deloop n.+2) deloop_dot deloop_dot (fun a0 b0 => deloop_m (n.+2; a0) b0) (fun a0 b0 => deloop_m b0 (n.+2; a0)) _ _ (dltw a) _ _ @ _); apply moveR_Vp.
    rewrite ap_deloop_m_dltw.
    rewrite ap_pp; repeat rewrite concat_p_pp.
    rewrite <- dltw_dot_natural; repeat rewrite concat_pp_p; apply whiskerL.
    srapply tau_deloop_R.
  Defined.

  Lemma tau_deloop_nil_dltw
    : forall (n : nat) (a : deloop n) (a' : (n; a) = deloop_m (n; a) (0; dlpt0)),
transport (fun b : deloop n.+2 => (n.+2; b) = deloop_m (n.+2; b) (0; dlpt0)) (dltw a) (ap Sdli (ap Sdli a')) =
ap Sdli (ap Sdli a').
  Proof.
    intros; simpl.
    refine (@transport_paths_FlFr (deloop n.+2) deloop_dot (fun z => (n.+2; z)) (fun z => deloop_m (n.+2; z) (0; dlpt0)) _ _ (dltw a) _ @ concat_pp_p _ _ _ @ _); apply moveR_Vp.
    change (ap Sdli (ap Sdli a') @ ap (fun z : deloop n.+2 => deloop_m (n.+2; z) (0; dlpt0)) (dltw a) =
dltw_dot (n; a) @ ap Sdli (ap Sdli a')).
    refine (_ @ dltw_dot_natural a'); apply whiskerL.
    refine (_ @ ap_deloop_m_dltw_dot (n; a) (0; dlpt0)).
    exact (ap_sigma_ap_fiber deloop (fun z => deloop_m z (0; dlpt0)) (dltw a))^.
  Defined.

Definition tau_deloop
  : forall a b : deloop_dot, deloop_m a b = deloop_m b a.
Proof.
  intros [n a]; revert a; revert n.
  assert (T : (forall (n : nat) (a : deloop n), IsHSet (forall b, deloop_m (n; a) b = deloop_m b (n; a)))).
  { intros. enough (t : forall b, IsHSet (deloop_m (n; a) b = deloop_m b (n; a))). { srapply @trunc_forall. }
    intros. exact (@istrunc_paths _ _ (dlT_dot) _ _). }
  srefine (deloop_ind_to_set _ _ _ _ T); clear T; hnf.
  + intro. change (b = deloop_m b (0; dlpt0)). (*  exact (rho_deloop b)^. *)
    induction b as [m b]; revert b; revert m.
    assert (T : (forall (m : nat) (b : deloop m), IsHSet ((m; b) = deloop_m (m; b) (0; dlpt0)))).
    { intros. srapply @istrunc_paths. exact dlT_dot. }
    srefine (deloop_ind_to_set _ _ _ _ T); clear T; hnf.
    - constructor.
    - intros n a h.
      change (Sdli (n; a) = Sdli (deloop_m (n; a) (0; dlpt0))).
      exact (ap Sdli h).
    - hnf. exact tau_deloop_nil_dltw.
  + intros n a ih b.
    change (Sdli (deloop_m (n; a) b) = deloop_m b (Sdli (n; a))).
    refine (ap Sdli (ih b) @ _).
    exact (tau_deloop_Q (n; a) b).
  + exact tau_deloop_dltw.
Defined.

(* This goes exactly the same way as for slists.
We show the pentagon and the triangle as an example. *)
Definition pentagon_deloop
  : IsPentagonCoherent deloop_m alpha_deloop.
Proof.
  unfold IsPentagonCoherent.
  intros [n a] b c d; revert a; revert n.
  assert (T : forall (n : nat) (a : deloop n), IsHProp (alpha_deloop (deloop_m (n; a) b) c d @ alpha_deloop (n; a) b (deloop_m c d) =
(ap011 deloop_m (alpha_deloop (n; a) b c) 1 @ alpha_deloop (n; a) (deloop_m b c) d) @
ap011 deloop_m 1 (alpha_deloop b c d))).
  { intros. apply @istrunc_paths. apply @istrunc_paths. exact dlT_dot. }
  refine (deloop_ind_to_prop _ _ _ T); clear T; hnf.
  + simpl. refine (concat_p1 _ @ _ @ (concat_1p _)^).
    change (alpha_deloop b c d = ap idmap (alpha_deloop b c d)).
    exact (ap_idmap _)^.
  + intros n a h.
    change (ap Sdli (alpha_deloop (deloop_m (n; a) b) c d) @ ap Sdli (alpha_deloop (n; a) b (deloop_m c d)) = (ap011 deloop_m (ap Sdli (alpha_deloop (n; a) b c)) 1 @ ap Sdli (alpha_deloop (n; a) (deloop_m b c) d)) @ ap011 deloop_m (ap Sdli (idpath (n; a))) (alpha_deloop b c d)).
    rewrite (ap011_deloop_m_ap_Sdli (alpha_deloop (n; a) b c) (idpath d)).
    rewrite (ap011_deloop_m_ap_Sdli (idpath (n; a)) (alpha_deloop b c d)).
    repeat rewrite <- (ap_pp Sdli); apply ap; exact h.
Qed.

Definition triangle_deloop
  : IsTriangleCoherent deloop_e deloop_m alpha_deloop lambda_deloop rho_deloop.
Proof.
  unfold IsTriangleCoherent.
  intros [n a] b; revert a; revert n.
  assert (T : forall (n : nat) (a : deloop n), IsHProp (alpha_deloop (n; a) deloop_e b @ ap011 deloop_m 1 (lambda_deloop b) = ap011 deloop_m (rho_deloop (n; a)) 1)).
  { intros. apply @istrunc_paths. apply @istrunc_paths. exact dlT_dot. }
  refine (deloop_ind_to_prop _ _ _ T); clear T; hnf.
  + constructor.
  + intros n a h.
    change (ap Sdli (alpha_deloop (n; a) deloop_e b) @ ap Sdli 1 = ap011 deloop_m (ap Sdli (rho_deloop (n; a))) 1).
    rewrite (ap011_deloop_m_ap_Sdli (rho_deloop (n; a)) 1).
    rewrite <- (ap_pp Sdli); apply ap; exact h.
Qed.

Definition hexagon_deloop
  : IsHexagonCoherent deloop_m alpha_deloop tau_deloop.
Proof.
Admitted.

Definition bigon_deloop
  : IsBigonCoherent deloop_m tau_deloop.
Proof.
Admitted.

Definition deloopSMG
  : SymMonoidalGroupoid
  := Build_SymMonoidalGroupoid deloop_dot dlT_dot deloop_e deloop_m alpha_deloop lambda_deloop rho_deloop tau_deloop pentagon_deloop triangle_deloop hexagon_deloop bigon_deloop.

End deloop_smgpd.
