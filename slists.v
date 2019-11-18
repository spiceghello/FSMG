Require Export path_algebra_lemmas.

(* Part I : definition of the type slist. *)

Section slist_private.

Private Inductive slist (X : Type) : Type :=
  | nil : slist X
  | cons : X -> slist X -> slist X.
Global Arguments nil {X}.
Global Arguments cons {X} _ _.

End slist_private.

Infix "::" := cons (at level 60, right associativity) : slist_scope.
Open Scope slist_scope.

Section slist.

Context {X : Type}.

Axiom swap
  : forall (x y : X) (l : slist X),
    x :: y :: l = y :: x :: l.

Axiom double
  : forall (x y : X) (l : slist X),
    swap x y l @ swap y x l = idpath.

Axiom triple
  : forall (x y z : X) (l : slist X),
  swap x y (cons z l) @ ap (cons y) (swap x z l) @ swap y z (cons x l)
  = ap (cons x) (swap y z l) @ swap x z (cons y l) @ ap (cons z) (swap x y l).

Axiom T_slist
  : IsTrunc 1 (slist X).

Lemma swap_natural {x y : X} {l l' : slist X} (p : l = l')
  : swap x y l @ ap (cons y) (ap (cons x) p) = ap (cons x) (ap (cons y) p) @ swap x y l'.
Proof.
  induction p; simpl. exact (concat_p1 _ @ (concat_1p _)^).
Defined.

Lemma swap_inv {x y : X} {l : slist X}
  : swap x y l = (swap y x l)^.
Proof.
  apply moveL_1V. apply double.
Defined.

Section slist_ind.

Definition swap'_ind_type
  (P : slist X -> Type)
  (cons' : forall (x : X) (l : slist X) (IHl : P l), P (x :: l))
  : Type
  := forall (x y : X) (l : slist X) (IHl : P l),
    transport P (swap x y l) (cons' x _ (cons' y _ IHl)) = cons' y _ (cons' x _ IHl).

Definition double'_ind_type
  (P : slist X -> Type)
  (cons' : forall (x : X) (l : slist X) (IHl : P l), P (x :: l))
  (swap' : swap'_ind_type P cons')
  : Type
  := forall (x y : X) (l : slist X) (IHl : P l),
    concat_D (swap' x y l IHl) (swap' y x l IHl)
    = ap (fun z => transport P z (cons' x _ (cons' y _ IHl))) (double x y l).

Definition triple'_ind_type
  (P : slist X -> Type)
  (cons' : forall (x : X) (l : slist X) (IHl : P l), P (x :: l))
  (swap' : swap'_ind_type P cons')
  : Type
  := forall (x y z : X) (l : slist X) (IHl : P l),
    concat_D
      (concat_D
        (swap' x y _ (cons' z _ IHl))
        (transport_ap P (cons y) (cons' y) _ (swap' x z _ IHl)))
      (swap' y z _ (cons' x _ IHl))
    = ap (fun w => transport P w (cons' x _ (cons' y _ (cons' z _ IHl)))) (triple x y z l)
    @ concat_D
        (concat_D
          (transport_ap P (cons x) (cons' x) _ (swap' y z _ IHl))
          (swap' x z _ (cons' y _ IHl)))
        (transport_ap P (cons z) (cons' z) _ (swap' x y _ IHl)).

Fixpoint slist_ind
  (P : slist X -> Type)
  (nil' : P nil)
  (cons' : forall (x : X) (l : slist X) (IHl : P l), P (x :: l))
  (swap' : swap'_ind_type P cons')
  (double' : double'_ind_type P cons' swap')
  (triple' : triple'_ind_type P cons' swap')
  (T_slist' : forall (l : slist X), IsTrunc 1 (P l))
  (l : slist X)
  : P l
  := match l with
    | nil => nil'
    | x :: k => cons' x k (slist_ind P nil' cons' swap' double' triple' T_slist' k)
    end.

Axiom slist_ind_beta_swap
  : forall (P : slist X -> Type)
  (nil' : P nil)
  (cons' : forall (x : X) (l : slist X) (IHl : P l), P (x :: l))
  (swap' : swap'_ind_type P cons')
  (double' : double'_ind_type P cons' swap')
  (triple' : triple'_ind_type P cons' swap')
  (T_slist' : forall (l : slist X), IsTrunc 1 (P l))
  (x y : X) (l : slist X),
  apD (slist_ind P nil' cons' swap' double' triple' T_slist') (swap x y l) = swap' x y _ (slist_ind P nil' cons' swap' double' triple' T_slist' l).

End slist_ind.

Section slist_ind_trunc.

Context (P : slist X-> Type)
  (nil' : P nil)
  (cons' : forall (x : X) (l : slist X) (IHl : P l), P (x :: l)).

Definition slist_ind_to_set
  (swap' : swap'_ind_type P cons')
  (T_slist' : forall (l : slist X), IsTrunc 0 (P l))
  : forall l : slist X, P l.
Proof.
  srefine (@slist_ind P nil' cons' swap' _ _ _);
  [ unfold double'_ind_type | unfold triple'_ind_type];
  intros; apply T_slist'.
Defined.

Definition slist_ind_to_prop
  (T_slist' : forall (l : slist X), IsTrunc -1 (P l))
  : forall l : slist X, P l.
Proof.
  srapply @slist_ind_to_set;
  unfold swap'_ind_type;
  intros; apply T_slist'.
Defined.

End slist_ind_trunc.

Section slist_ind_paths.

Definition slist_ind_to_paths_in_gpd
  (P : Type)
  (f f' : slist X -> P)
  (nil' : f nil = f' nil)
  (cons' : forall (x : X) (l : slist X) (IHl : f l = f' l), f (x :: l) = f' (x :: l))
  (swap' : forall (x y : X) (l : slist X) (IHl : f l = f' l),
    cons' x (y :: l) (cons' y l IHl) @ ap f' (swap x y l)
    = ap f (swap x y l) @ cons' y (x :: l) (cons' x l IHl))
  (T' : IsTrunc 1 P)
  : forall w : slist X, f w = f' w.
Proof.
  srefine (@slist_ind_to_set (fun w => f w = f' w) nil' cons' _ _); simpl.
  unfold swap'_ind_type; intros.
  refine (transport_paths_FlFr _ _ @ concat_pp_p _ _ _ @ _); apply moveR_Vp.
  apply swap'.
Defined.

Definition slist_ind_to_paths_in_set
  (P : Type)
  (T' : IsTrunc 0 P)
  (f f' : slist X -> P)
  (nil' : f nil = f' nil)
  (cons' : forall (x : X) (l : slist X) (IHl : f l = f' l), f (x :: l) = f' (x :: l))
  : forall w : slist X, f w = f' w.
Proof.
  exact (@slist_ind_to_prop (fun w => f w = f' w) nil' cons' _).
Defined.

Definition slist_ind_to_2paths_in_gpd
  (P : Type)
  (T' : IsTrunc 1 P)
  (f f' : slist X -> P)
  (p p' : forall l : slist X, f l = f' l)
  (nil' : p nil = p' nil)
  (cons' : forall (x : X) (l : slist X) (IHl : p l = p' l), p (x :: l) = p' (x :: l))
  : forall w : slist X, p w = p' w.
Proof.
  exact (@slist_ind_to_prop (fun w => p w = p' w) nil' cons' _).
Defined.

Definition slist_ind_to_fam_paths_in_gpd
  `{Funext}
  (P : Type)
  (T' : IsTrunc 1 P)
  (f f' : slist X -> slist X -> P)
  (nil' : forall l' : slist X, f nil l' = f' nil l')
  (cons' : forall (x : X) (l : slist X) (IHl : forall l' : slist X, f l l' = f' l l') (l' : slist X),
    f (x :: l) l' = f' (x :: l) l')
  (swap' : forall (x y : X) (l : slist X) (IHl : forall w' : slist X, f l w' = f' l w') (l' : slist X),
    cons' x (y :: l) (cons' y l IHl) l' @ ap (fun a : slist X => f' a l') (swap x y l)
    = ap (fun a : slist X => f a l') (swap x y l) @ cons' y (x :: l) (cons' x l IHl) l')
  : forall w w' : slist X, f w w' = f' w w'.
Proof.
  srefine (@slist_ind_to_set (fun w => forall w' : slist X, f w w' = f' w w') nil' cons' _ _).
  unfold swap'_ind_type; intros.
  by_extensionality l'.
  refine (transport_forall' f f' (swap x y l) _ l' @ _); apply moveR_Vp.
  apply swap'.
Defined.

Definition slist_ind_to_fam_2paths_in_gpd
  `{Funext}
  (P : Type)
  (T' : IsTrunc 1 P)
  (f f' : slist X -> slist X -> P)
  (p p' : forall (l l' : slist X), f l l' = f' l l')
  (nil' : forall w' : slist X, p nil w' = p' nil w')
  (cons' : forall (x : X) (l : slist X) (IHl : forall w' : slist X, p l w' = p' l w') (w' : slist X),
    p (x :: l) w' = p' (x :: l) w')
  : forall w w' : slist X, p w w' = p' w w'.
Proof.
  exact (slist_ind_to_prop (fun l : slist X => forall w' : slist X, p l w' = p' l w') nil' cons' _).
Defined.

End slist_ind_paths.

Section slist_rec.

Definition swap'_rec_type
  (P : Type)
  (cons' : X -> P -> P)
  : Type
  := forall (x y : X) (l' : P),
      cons' x (cons' y l') = cons' y (cons' x l').

Definition double'_rec_type
  (P : Type)
  (cons' : X -> P -> P)
  (swap' : swap'_rec_type P cons')
  : Type
  := forall (x y : X) (l' : P),
      swap' x y l' @ swap' y x l' = idpath.

Definition triple'_rec_type
  (P : Type)
  (cons' : X -> P -> P)
  (swap' : swap'_rec_type P cons')
  : Type
  := forall (x y z : X) (l' : P),
      swap' x y (cons' z l') @ ap (cons' y) (swap' x z l') @ swap' y z (cons' x l')
      = ap (cons' x) (swap' y z l') @ swap' x z (cons' y l') @ ap (cons' z) (swap' x y l').

  Definition slist_rec_swap
    {P : Type}
    {cons' : X -> P -> P}
    (swap' : swap'_rec_type P cons')
    : swap'_ind_type (fun _ : slist X => P) (fun (x : X) (_ : slist X) => cons' x).
  Proof.
    unfold swap'_ind_type; unfold swap'_rec_type in swap'.
    exact (fun x y _ l' => transport_const _ _ @ swap' x y l').
  Defined.

  Definition slist_rec_double
    {P : Type}
    {cons' : X -> P -> P}
    (swap' : swap'_rec_type P cons')
    (double' : double'_rec_type P cons' swap')
    : double'_ind_type (fun _ : slist X => P) (fun (x : X) (_ : slist X) => cons' x) (slist_rec_swap swap').
  Proof.
    unfold double'_ind_type; unfold double'_rec_type in double'.
    intros. refine (concat_D_const_p (swap' x y IHl) (swap' y x IHl) @ _).
    refine (whiskerL _ (double' x y IHl) @ concat_p1 _ @ _).
    exact ((transport_const_pq (double x y l) _)^ @ concat_p1 _).
  Qed.

  Definition slist_rec_triple
    {P : Type}
    {cons' : X -> P -> P}
    (swap' : swap'_rec_type P cons')
    (triple' : triple'_rec_type P cons' swap')
    : triple'_ind_type (fun _ : slist X => P) (fun (x : X) (_ : slist X) => cons' x) (slist_rec_swap swap').
  Proof.
    unfold triple'_ind_type; unfold triple'_rec_type in triple'.
    intros. simpl.
    rewrite transport_ap_transport_const_p, transport_ap_transport_const_p, transport_ap_transport_const_p.
    rewrite concat_D_const_p, concat_D_const_p, concat_D_const_p, concat_D_const_p.
    apply moveR_pM.
    refine ((transport_const_pq (triple x y z l) (cons' x (cons' y (cons' z IHl))))^ @ _).
    refine (_ @ concat_p_pp _ _ _). apply whiskerL.
    refine ((concat_p1 _)^ @ _ @ concat_p_pp _ _ _). apply whiskerL.
    apply moveL_pV. refine (concat_1p _ @ _). apply triple'.
  Qed.

Definition slist_rec
  (P : Type)
  (nil' : P)
  (cons' : X -> P -> P)
  (swap' : swap'_rec_type P cons')
  (double' : double'_rec_type P cons' swap')
  (triple' : triple'_rec_type P cons' swap')
  (T_slist' : IsTrunc 1 P)
  : slist X -> P.
Proof.
  exact (slist_ind (fun _ => P) nil' (fun x _ => cons' x) (slist_rec_swap swap') (slist_rec_double swap' double') (slist_rec_triple swap' triple') _).
Defined.

Definition slist_rec_beta_swap
  (P : Type)
  (T_slist' : IsTrunc 1 P)
  (nil' : P)
  (cons' : X -> P -> P)
  (swap' : swap'_rec_type P cons')
  (double' : double'_rec_type P cons' swap')
  (triple' : triple'_rec_type P cons' swap')
  (x y : X) (l : slist X)
  : ap (slist_rec P nil' cons' swap' double' triple' T_slist') (swap x y l) = swap' x y (slist_rec P nil' cons' swap' double' triple' T_slist' l).
Proof.
  eapply (cancelL (transport_const (swap x y l) _)).
  refine ((apD_const _ (swap x y l))^ @ _).
  exact (slist_ind_beta_swap (fun _ => P) nil' (fun x _ => cons' x) (slist_rec_swap swap') (slist_rec_double swap' double') (slist_rec_triple swap' triple') _ x y l).
Defined.

End slist_rec.

Section slist_rec_trunc.

Definition slist_rec_to_set
  (P : Type)
  (nil' : P)
  (cons' : X -> P -> P)
  (swap' : swap'_rec_type P cons')
  (T_slist' : IsTrunc 0 P)
  : slist X -> P.
Proof.
  srefine (@slist_rec P nil' cons' swap' _ _ _);
  [ unfold double'_rec_type | unfold triple'_rec_type ];
  intros; apply T_slist'.
Defined.

Definition slist_rec_to_prop
  (P : Type)
  (nil' : P)
  (cons' : X -> P -> P)
  (T_slist' : IsTrunc -1 P)
  : slist X -> P.
Proof.
  srefine (@slist_rec_to_set P nil' cons' _ _);
  unfold swap'_rec_type; intros; apply T_slist'.
Defined.

End slist_rec_trunc.

End slist.

Arguments nil {X}.
Arguments cons {X} _ _.
Arguments swap {X} _ _ _.
Arguments double {X} _ _ _.
Arguments triple {X} _ _ _ _.
Arguments swap_natural {X} _ _ {l} {l'} _.
Arguments swap_inv {X} _ _ _.

Ltac unfold_slist_types
  := try unfold triple'_ind_type in *;
      try unfold triple'_rec_type in *;
      try unfold double'_ind_type in *;
      try unfold double'_rec_type in *;
      try unfold swap'_ind_type in *;
      try unfold swap'_rec_type in *.


(* Part II : definition of the symmetric monoidal product (slist append). *)

Section sapp.

Open Scope path_scope.
Open Scope slist_scope.

Context `{Funext}.
Context {X : Type}.

  Lemma sapp_cons
    : X -> (slist X -> slist X) -> slist X -> slist X.
  Proof.
    intros x f. exact (cons x o f).
  Defined.

  Lemma sapp_swap
    : swap'_rec_type (slist X -> slist X) sapp_cons.
  Proof.
    unfold_slist_types.
    intros x y f. unfold sapp_cons.
    exact (path_forall (fun l : slist X => x :: y :: f l) (fun l : slist X => y :: x :: f l) (fun l => swap x y (f l))).
  Defined.

  Lemma sapp_double
    : double'_rec_type (slist X -> slist X) sapp_cons sapp_swap.
  Proof.
    unfold_slist_types.
    intros x y f.
    unfold sapp_swap.
    refine ((path_forall_pp _ _ _ (fun l => swap x y (f l)) (fun l => swap y x (f l)))^ @ _).
    refine (_ @ path_forall_1 (fun l : slist X => x :: y :: f l)).
    apply ap. srapply @path_forall; intro l.
    apply double.
  Qed.

  Lemma sapp_triple
    : triple'_rec_type (slist X -> slist X) sapp_cons sapp_swap.
  Proof.
    unfold_slist_types.
    intros x y z f.
    rewrite (ap_pf_2 (swap x z)), (ap_pf_2 (swap y z)), (ap_pf_2 (swap x y)).
    unfold sapp_swap, sapp_cons.
    rewrite <- path_forall_pp, <- path_forall_pp, <- path_forall_pp, <- path_forall_pp.
    apply ap. apply path_forall; intro l.
    apply triple.
  Qed.

(*   Definition sapp_trunc
    : IsTrunc 1 (slist X -> slist X).
  Proof.
    exact (@trunc_forall H (slist X) (fun _ => slist X) 1 (fun _ => T_slist)).
  Defined. *)

Definition sapp
  : slist X -> slist X -> slist X
  := slist_rec _ idmap sapp_cons sapp_swap sapp_double sapp_triple _.

End sapp.

Infix "++" := sapp (right associativity, at level 60) : slist_scope.

Section sapp_monoidal_product.

Open Scope path_scope.
Open Scope slist_scope.

Context `{Funext}.
Context {X : Type}.

Lemma sapp_beta_swap (x y : X) (l' : slist X)
  : ap sapp (swap x y l') = path_forall _ _ (fun z => swap x y (l' ++ z)).
Proof.
  srapply @slist_rec_beta_swap.
Defined.

Lemma sapp_blank_beta_swap (x y : X) (l l' : slist X)
  : ap (fun w : slist X => w ++ l') (swap x y l) = swap x y (l ++ l').
Proof.
  refine (ap_compose sapp (fun q => q l') (swap x y l) @ _).
  refine (ap (ap (fun q => q l')) (sapp_beta_swap x y l) @ _).
  exact (ap_pf (fun z : slist X => swap x y (l ++ z)) l').
Defined.

Lemma ap011_sapp_ap_cons (x : X) {l l' k k' : slist X} (p : l = l') (q : k = k')
  : ap011 sapp (ap (cons x) p) q = ap (cons x) (ap011 sapp p q).
Proof.
  induction p, q; constructor.
Defined.

(* alpha *)
  Lemma alpha_slist_swap (l2 l3 : slist X)
    : forall (x y : X) (l1 : slist X) (h : (l1 ++ l2) ++ l3 = l1 ++ l2 ++ l3),
      ap (cons x) (ap (cons y) h) @ ap (fun w : slist X => w ++ l2 ++ l3) (swap x y l1)
      = ap (fun w : slist X => (w ++ l2) ++ l3) (swap x y l1) @ ap (cons y) (ap (cons x) h).
  Proof.
    intros x y l1 h; simpl.
    refine (whiskerL _ (sapp_blank_beta_swap x y l1 (l2 ++ l3)) @ _).
    refine (_ @ whiskerR (ap_compose ((fun h => h l2) o sapp) ((fun h => h l3) o sapp) (swap x y l1))^ _).
    refine (_ @ whiskerR (ap (ap (fun h => sapp h l3)) (sapp_blank_beta_swap x y l1 l2))^ _).
    refine (_ @ whiskerR (sapp_blank_beta_swap x y (l1 ++ l2) l3)^ _).
    exact (swap_natural x y h)^.
  Qed.

Lemma alpha_slist
  : forall l1 l2 l3 : slist X, (l1 ++ l2) ++ l3 = l1 ++ l2 ++ l3.
Proof.
  intros; revert l1; srapply @slist_ind_to_paths_in_gpd; simpl.
  + constructor.
  + intros x l1 h.
    change (x :: (l1 ++ l2) ++ l3 = x :: l1 ++ l2 ++ l3).
    apply ap; exact h.
  + hnf. apply alpha_slist_swap.
Defined.

(* lambda *)
Lemma lambda_slist
  : forall l : slist X, nil ++ l = l.
Proof.
  intros. constructor.
Defined.

(* rho *)
  Lemma rho_slist_swap
    : forall (x y : X) (l : slist X) (h : l ++ nil = l),
      ap (cons x) (ap (cons y) h) @ ap idmap (swap x y l)
      = ap (fun w : slist X => w ++ nil) (swap x y l) @ ap (cons y) (ap (cons x) h).
  Proof.
    intros; simpl.
    refine (whiskerL _ (ap_idmap _) @ _).
    refine ((swap_natural x y h)^ @ _); apply whiskerR.
    exact (sapp_blank_beta_swap x y l nil)^.
  Qed.

Lemma rho_slist
  : forall l : slist X, l ++ nil = l.
Proof.
  srapply @slist_ind_to_paths_in_gpd; simpl.
  + constructor.
  + intros x l h.
    change (x :: l ++ nil = x :: l).
    apply ap; exact h.
  + hnf. apply rho_slist_swap.
Defined.

(* tau *)
  Lemma sapp_Q_swap (x : X) (l2 : slist X)
    : forall (y z : X) (l1 : slist X) (h : x :: l1 ++ l2 = l1 ++ x :: l2),
      (swap x y ((z :: l1) ++ l2) @ ap (cons y) (swap x z (l1 ++ l2) @ ap (cons z) h))
      @ ap (fun w : slist X => w ++ x :: l2) (swap y z l1)
      = ap (fun w : slist X => x :: w ++ l2) (swap y z l1)
      @ (swap x z ((y :: l1) ++ l2) @ ap (cons z) (swap x y (l1 ++ l2) @ ap (cons y) h)).
  Proof.
    intros.
    refine (whiskerL _ (sapp_blank_beta_swap y z l1 (x :: l2)) @ _).
    refine (whiskerR (whiskerL _ (ap_pp _ _ _) @ concat_p_pp _ _ _) _ @ _);
    refine (concat_pp_p _ _ _ @ whiskerL _ (swap_natural y z h)^ @ concat_p_pp _ _ _ @ _);
    refine (_ @ concat_pp_p _ _ _ @ whiskerL _ (concat_pp_p _ _ _ @ whiskerL _ (ap_pp _ _ _)^));
    apply whiskerR.
    refine (triple x y z (l1 ++ l2) @ concat_pp_p _ _ _ @ _); apply whiskerR.
    refine (_ @ (ap_compose (fun w => w ++ l2) (cons x) (swap y z l1))^); apply ap.
    exact (sapp_blank_beta_swap y z l1 l2)^.
  Qed.

Lemma sapp_Q (x : X) (l2 : slist X)
  : forall l1 : slist X,
    x :: l1 ++ l2 = l1 ++ x :: l2.
Proof.
  srapply @slist_ind_to_paths_in_gpd; simpl.
  + constructor.
  + intros y l1 h.
    change (x :: y :: l1 ++ l2 = y :: l1 ++ x :: l2).
    refine (swap x y (l1 ++ l2) @ _).
    apply ap. exact h.
  + hnf. apply sapp_Q_swap.
Defined.

Lemma sapp_R (x y : X) (l1 : slist X)
  : forall l2 : slist X,
    swap x y (l2 ++ l1) @ (ap (cons y) (sapp_Q x l1 l2) @ sapp_Q y (x :: l1) l2) =
    (ap (cons x) (sapp_Q y l1 l2) @ sapp_Q x (y :: l1) l2) @ ap (fun z => l2 ++ z) (swap x y l1).
Proof.
  srapply @slist_ind_to_2paths_in_gpd; hnf.
  + simpl. refine (concat_p1 _ @ _ @ (concat_1p _)^).
    change (swap x y l1 = ap idmap (swap x y l1)).
    exact (ap_idmap _)^.
  + intros z l2 h.
    change (swap x y ((z :: l2) ++ l1) @ (ap (cons y) (swap x z (l2 ++ l1) @ ap (cons z) (sapp_Q x l1 l2)) @ (swap y z (l2 ++ x :: l1) @ ap (cons z) (sapp_Q y (x :: l1) l2))) = (ap (cons x) (swap y z (l2 ++ l1) @ ap (cons z) (sapp_Q y l1 l2)) @  (swap x z (l2 ++ y :: l1) @ ap (cons z) (sapp_Q x (y :: l1) l2))) @ ap (fun z0 : slist X => (z :: l2) ++ z0) (swap x y l1));
    repeat rewrite ap_pp.
    refine (whiskerL _ (concat_pp_p _ _ _ @ whiskerL _ (concat_p_pp _ _ _ @ whiskerR (swap_natural y z (sapp_Q x l1 l2))^ _)) @ _).
    refine (concat_p_pp _ _ _ @ whiskerL _ (concat_pp_p _ _ _) @ concat_p_pp _ _ _ @ whiskerR (triple x y z (sapp l2 l1)) _ @ _);
    refine (concat_pp_p _ _ _ @ concat_pp_p _ _ _ @ _ @ concat_p_pp _ _ _ @ concat_p_pp _ _ _); apply whiskerL.
    refine (whiskerL _ (whiskerL _ (ap_pp (cons z) _ _)^ @ (ap_pp (cons z) _ _)^ @ ap (ap (cons z)) h) @ _); repeat rewrite ap_pp.
    refine (whiskerL _ (concat_pp_p _ _ _) @ concat_p_pp _ _ _ @ whiskerR (swap_natural x z (sapp_Q y l1 l2)) _ @ concat_pp_p _ _ _ @ _);
    apply whiskerL;
    refine (_ @ concat_p_pp _ _ _);
    apply whiskerL; apply whiskerL.
    exact (ap_compose (fun w => l2 ++ w) (cons z) (swap x y l1))^.
Qed.

  Lemma tau_slist_swap
    : forall (x y : X) (l1 : slist X) (h : forall w' : slist X, l1 ++ w' = w' ++ l1) (l2 : slist X),
    (ap (cons x) (ap (cons y) (h l2) @ sapp_Q y l1 l2) @ sapp_Q x (y :: l1) l2)
    @ ap (fun a : slist X => l2 ++ a) (swap x y l1)
    = ap (fun a : slist X => a ++ l2) (swap x y l1)
    @ (ap (cons y) (ap (cons x) (h l2) @ sapp_Q x l1 l2) @ sapp_Q y (x :: l1) l2).
  Proof.
    intros.
    repeat rewrite ap_pp.
    refine (whiskerR (concat_pp_p _ _ _) _ @ concat_pp_p _ _ _ @ whiskerL _ (sapp_R x y l1 l2)^ @ concat_p_pp _ _ _ @ _ @ concat_pp_p _ _ _ @ whiskerL _ (concat_p_pp _ _ _)); apply whiskerR.
    refine ((swap_natural x y (h l2))^ @ _); apply whiskerR.
    exact (sapp_blank_beta_swap x y l1 l2)^.
  Qed.

  Lemma tau_slist_nil_swap
    : forall (x y : X) (l : slist X) (h : l = l ++ nil),
      ap (cons x) (ap (cons y) h) @ ap (fun w : slist X => w ++ nil) (swap x y l)
      = ap idmap (swap x y l) @ ap (cons y) (ap (cons x) h).
  Proof.
    intros; simpl.
    refine (_ @ whiskerR (ap_idmap _)^ _).
    refine (_ @ (swap_natural x y h)^); apply whiskerL.
    exact (sapp_blank_beta_swap x y l nil).
  Defined.

Lemma tau_slist
  : forall l1 l2 : slist X,
    l1 ++ l2 = l2 ++ l1.
Proof.
  srapply @slist_ind_to_fam_paths_in_gpd; hnf.
  + change (forall l' : slist X, l' = l' ++ nil).
    srapply @slist_ind_to_paths_in_gpd; hnf.
    - constructor.
    - intros x l h.
      change (x :: l = x :: l ++ nil).
      exact (ap (cons x) h).
    - hnf. apply tau_slist_nil_swap.
  + intros x l1 h l2.
    change (x :: l1 ++ l2 = l2 ++ x :: l1).
    exact (ap (cons x) (h l2) @ sapp_Q x l1 l2).
  + hnf. apply tau_slist_swap.
Defined.

(* pentagon *)
Lemma pentagon_slist
  : forall l1 l2 l3 l4 : slist X,
      alpha_slist (l1 ++ l2) l3 l4 @ alpha_slist l1 l2 (l3 ++ l4)
      = (ap011 sapp (alpha_slist l1 l2 l3) 1 @ alpha_slist l1 (l2 ++ l3) l4) @ ap011 sapp 1 (alpha_slist l2 l3 l4).
Proof.
  intros; revert l1; srapply @slist_ind_to_2paths_in_gpd; hnf.
  + simpl. refine (concat_p1 _ @ _ @ (concat_1p _)^).
    change (alpha_slist l2 l3 l4 = ap idmap (alpha_slist l2 l3 l4)).
    exact (ap_idmap _)^.
  + intros x l1 h.
    change (ap (cons x) (alpha_slist (l1 ++ l2) l3 l4) @ ap (cons x) (alpha_slist l1 l2 (l3 ++ l4)) =
(ap011 sapp (ap (cons x) (alpha_slist l1 l2 l3)) 1 @ ap (cons x) (alpha_slist l1 (l2 ++ l3) l4)) @
ap011 sapp (ap (cons x) 1) (alpha_slist l2 l3 l4)).
    rewrite (ap011_sapp_ap_cons x (alpha_slist l1 l2 l3) (idpath l4)).
    rewrite (ap011_sapp_ap_cons x (idpath l1) (alpha_slist l2 l3 l4)).
    repeat rewrite <- (ap_pp (cons x)); apply ap; exact h.
Qed.

(* triangle *)
Lemma triangle_slist
  : forall l1 l2 : slist X,
      alpha_slist l1 nil l2 @ ap011 sapp 1 (lambda_slist l2)
      = ap011 sapp (rho_slist l1) 1.
Proof.
  intros; revert l1; srapply @slist_ind_to_2paths_in_gpd; hnf.
  + constructor.
  + intros x l1 h; unfold lambda_slist.
    change (ap (cons x) (alpha_slist l1 nil l2) @ ap (cons x) 1 = ap011 sapp (ap (cons x) (rho_slist l1)) 1).
    rewrite (ap011_sapp_ap_cons x (rho_slist l1) 1).
    rewrite <- (ap_pp (cons x)); apply ap; exact h.
Defined.

(* hexagon *)
Lemma sapp_H (x : X) (l1 l3 : slist X)
  : forall l2 : slist X,
    ((ap (cons x) (alpha_slist l2 l1 l3) @ ap (cons x) (ap011 sapp 1 (tau_slist l1 l3)))
      @ (ap (cons x) (alpha_slist l2 l3 l1))^)
    @ (sapp_Q x l1 (l2 ++ l3) @ alpha_slist l2 l3 (x :: l1))
    = (ap011 sapp (sapp_Q x l1 l2) 1 @ alpha_slist l2 (x :: l1) l3)
    @ (ap011 sapp 1 (ap (cons x) (tau_slist l1 l3)) @ ap011 sapp 1 (sapp_Q x l1 l3)).
Proof.
  intro l2; repeat rewrite (ap011_1p sapp); revert l2.
  srapply @slist_ind_to_2paths_in_gpd; hnf.
  + simpl. refine (concat2 (concat_p1 _ @ concat_1p _) (concat_p1 _) @ _ @ (concat_1p _)^).
    refine (whiskerL _ (ap_idmap _)^ @ _); apply whiskerR.
    refine ((ap_compose idmap (cons x) _)^ @ ap_compose (cons x) idmap _).
  + intros y l2 h.
    change (((ap (cons x) (ap (cons y) (alpha_slist l2 l1 l3)) @ ap (cons x) (ap (cons y o sapp l2) (tau_slist l1 l3))) @ (ap (cons x) (ap (cons y) (alpha_slist l2 l3 l1)))^) @ ((swap x y ((l2 ++ l3) ++ l1) @ ap (cons y) (sapp_Q x l1 (l2 ++ l3))) @ ap (cons y) (alpha_slist l2 l3 (x :: l1))) = (ap011 sapp (swap x y (l2 ++ l1) @ ap (cons y) (sapp_Q x l1 l2)) (1 @ 1) @ ap (cons y) (alpha_slist l2 (x :: l1) l3)) @ (ap (cons y o sapp l2) (ap (cons x) (tau_slist l1 l3)) @ ap (cons y o sapp l2) (sapp_Q x l1 l3)));
    rewrite <- (ap011_pqpq sapp (swap x y (l2 ++ l1)) _ 1 1);
    repeat rewrite (ap_compose (sapp l2) (cons y)).
    repeat rewrite <- ap_V.
    repeat rewrite <- (ap_pp (cons x)).
    repeat rewrite <- (ap_pp (cons y)).
    refine (whiskerL _ (concat_pp_p _ _ _) @ concat_p_pp _ _ _ @ whiskerR (swap_natural x y _)^ _ @ _).
    rewrite (ap011_p1 sapp (swap x y (sapp l2 l1)));
    refine (concat_pp_p _ _ _ @ _ @ whiskerR (sapp_blank_beta_swap x y (l2 ++ l1) l3)^ _ @ concat_p_pp _ _ _ @ concat_p_pp _ _ _); apply whiskerL.
    repeat rewrite <- (ap_pp (cons y));
    repeat rewrite (ap_pp (cons x));
    repeat rewrite ap_V.
    refine (ap (ap (cons y)) h @ _).
    rewrite ap011_sapp_ap_cons.
    repeat rewrite <- (ap_pp (cons y)).
    apply ap.
    refine (concat_pp_p _ _ _).
Qed.

Lemma hexagon_slist
  : forall l1 l2 l3 : slist X,
    (alpha_slist l1 l2 l3 @ tau_slist l1 (l2 ++ l3)) @ alpha_slist l2 l3 l1
    = (ap011 sapp (tau_slist l1 l2) 1 @ alpha_slist l2 l1 l3) @ ap011 sapp 1 (tau_slist l1 l3).
Proof.
  intros; revert l2; revert l1; srapply @slist_ind_to_fam_2paths_in_gpd; hnf.
  + srapply @slist_ind_to_2paths_in_gpd; hnf.
    - change (1 @ tau_slist nil l3 @ 1 = 1 @ 1 @ ap idmap (tau_slist nil l3)).
      refine (concat_p1 _ @ concat_1p _ @ (ap_idmap _)^ @ (concat_1p _)^).
    - intros y l2 h.
      change ((ap (cons y) (alpha_slist nil l2 l3) @ ap (cons y) (tau_slist nil (l2 ++ l3))) @ ap (cons y) (alpha_slist l2 l3 nil) = (ap011 sapp (tau_slist nil (y :: l2)) 1 @ alpha_slist (y :: l2) nil l3) @ ap011 sapp 1 (tau_slist nil l3)).
      repeat rewrite <- (ap_pp (cons y)).
      refine (ap (ap (cons y)) h @ _).
      repeat rewrite (ap_pp (cons y)).
      refine (concat2 (concat2 _ 1) _).
      change (ap (cons y) (ap011 sapp (tau_slist nil l2) (idpath l3)) = ap011 sapp (ap (cons y) (tau_slist nil l2)) 1).
      exact (ap011_sapp_ap_cons y _ _)^.
      exact (ap011_sapp_ap_cons y (idpath l2) _)^.
  + intros x l1 hl1 l2.
    change ((ap (cons x) (alpha_slist l1 l2 l3) @ (ap (cons x) (tau_slist l1 (l2 ++ l3)) @ sapp_Q x l1 (l2 ++ l3))) @ alpha_slist l2 l3 (x :: l1) = (ap011 sapp (tau_slist (x :: l1) l2) 1 @ alpha_slist l2 (x :: l1) l3) @ ap011 sapp 1 (tau_slist (x :: l1) l3)).
    refine (whiskerR (concat_p_pp _ _ _ @ whiskerR ((concat_p1 _)^ @ whiskerL _ (concat_pV (ap (cons x) (alpha_slist _ _ _)))^ @ concat_p_pp _ _ _ @ whiskerR (whiskerR (ap_pp _ _ _)^ _ @ (ap_pp _ _ _)^ @ ap (ap (cons x)) (hl1 l2) @ ap_pp _ _ _ @ whiskerR (ap_pp _ _ _) _) _) _) _ @ _).
    refine (concat_pp_p _ _ _ @ whiskerR (concat_pp_p _ _ _ @ concat_pp_p _ _ _ @ whiskerL _ (concat_p_pp _ _ _)) _ @ concat_pp_p _ _ _ @ whiskerL _ (sapp_H x l1 l3 l2) @ _).
    refine (_ @ concat_p_pp _ _ _).
    refine (whiskerR (ap011_sapp_ap_cons x (tau_slist l1 l2) idpath)^ _ @ _).
    change (ap011 sapp (ap (cons x) (tau_slist l1 l2)) 1 @ ((ap011 sapp (sapp_Q x l1 l2) 1 @ alpha_slist l2 (cons x l1) l3) @  (ap011 sapp 1 (ap (cons x) (tau_slist l1 l3)) @ ap011 sapp 1 (sapp_Q x l1 l3))) = ap011 sapp (tau_slist (cons x l1) l2) 1 @ (alpha_slist l2 (cons x l1) l3 @ ap011 sapp (1 @ 1) (ap (cons x) (tau_slist _ _) @ sapp_Q x l1 l3))).
    rewrite <- (ap011_pqpq sapp 1 1 _ (sapp_Q x l1 l3)).
    refine (whiskerL _ (concat_pp_p _ _ _) @ concat_p_pp _ _ _ @ _); apply whiskerR.
    exact (ap011_pqpq sapp _ (sapp_Q x l1 l2) 1 1).
Qed.

(* bigon *)
Lemma bigon_slist
  : forall l1 l2 : slist X,
    tau_slist l1 l2 @ tau_slist _ _ = idpath.
Proof.
  srapply @slist_ind_to_fam_2paths_in_gpd; hnf.
  + srapply @slist_ind_to_2paths_in_gpd; hnf.
    - constructor.
    - intros y l2 h.
      refine (whiskerL _ (concat_p1 _) @ _).
      change (ap (cons y) (tau_slist nil l2) @ ap (cons y) (tau_slist l2 nil) = ap (cons y) idpath).
      refine ((ap_pp (cons y) _ _)^ @ _).
      exact (ap (ap (cons y)) h).
  + intros x l1 hl1.
    srapply @slist_ind_to_2paths_in_gpd; hnf.
    - refine (whiskerR (concat_p1 _) _ @ _).
      change (ap (cons x) (tau_slist l1 nil) @ ap (cons x) (tau_slist nil l1) = ap (cons x) idpath).
      refine ((ap_pp (cons x) _ _)^ @ _).
      exact (ap (ap (cons x)) (hl1 nil)).
    - intros y l2 hl2.
      change ((ap (cons x) (tau_slist l1 (y :: l2)) @ (swap x y (l2 ++ l1) @ ap (cons y) (sapp_Q x l1 l2))) @ (ap (cons y) (tau_slist l2 (x :: l1)) @ (swap y x (l1 ++ l2) @ ap (cons x) (sapp_Q y l2 l1))) = 1);
      apply concat_1_pq;
      repeat rewrite inv_pp;
      repeat rewrite <- ap_V.
      refine (_ @ concat_p_pp _ _ _).
      refine (whiskerR (ap (ap (cons x)) (concat_pq_1 (hl1 (y :: l2)))) _ @ _).
      change (ap (cons x) (ap (cons y) (tau_slist l2 l1) @ sapp_Q y l2 l1)^ @ (swap x y (l2 ++ l1) @ ap (cons y) (sapp_Q x l1 l2)) = ap (cons x) (sapp_Q y l2 l1)^ @ ((swap y x (l1 ++ l2))^ @ ap (cons y) (tau_slist l2 (x :: l1))^));
      rewrite inv_pp;
      rewrite ap_pp.
      refine (concat_pp_p _ _ _ @ _); apply whiskerL.
      refine (_ @ whiskerR (concat_pq_1 (double x y (l1 ++ l2))) _).
      rewrite <- ap_V.
      refine (whiskerR (ap (ap (cons x)) (ap (ap (cons y)) (concat_pq_1 (hl1 l2))^)) _ @ concat_p_pp _ _ _ @ _).
      refine (whiskerR (swap_natural x y (tau_slist l1 l2))^ _ @ concat_pp_p _ _ _ @ _); apply whiskerL.
      refine ((ap_pp (cons y) _ _ )^ @ ap (ap (cons y)) (concat_pq_1 hl2)).
Qed.

End sapp_monoidal_product.

Require Export smonoidalgroupoid.

Definition slistSMG `{Funext} (X : Type)
  : SymMonoidalGroupoid
  := @Build_SymMonoidalGroupoid (slist X) (T_slist) nil sapp alpha_slist lambda_slist rho_slist tau_slist pentagon_slist triangle_slist hexagon_slist bigon_slist.
