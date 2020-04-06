Require Export monoidalgroupoid.

Section lists.

Section list_truncations.

Open Scope list.

Context (X : Type). (* (T : IsHSet X). *)

Fixpoint list_code (l k : list X) : Type
  := match l, k with
    | nil, nil => Unit
    | x :: l', nil => Empty
    | nil, y :: k' => Empty
    | x :: l', y :: k' => (x = y) * list_code l' k' end.

Definition r (l : list X)
  : list_code l l.
Proof.
  induction l; simpl.
  + exact tt.
  + exact (idpath, IHl).
Defined.

Definition list_encode {l k : list X}
  : l = k -> list_code l k.
Proof.
  intro p.
  exact (transport (list_code l) p (r l)).
Defined.

Arguments cons {A} _ _.

Lemma list_encode_switch {x y : X} (p : x = y) {l k : list X} (q : l = k)
  : list_encode (ap011 cons p q) = (p, list_encode q).
Proof.
  induction p, q; constructor.
Defined.

Fixpoint list_decode {l k : list X}
  : list_code l k -> l = k.
Proof.
  refine (match l, k with
    | nil, nil => fun c => _
    | x :: l', nil => _
    | nil, y :: k' => _
    | x :: l', y :: k' => _ end); simpl.
  + exact idpath.
  + exact Empty_rec.
  + exact Empty_rec.
  + intros [p c].
    exact (ap011 cons p (list_decode l' k' c)).
(*     exact (ap (fun z => cons z l') p @ ap (fun z => cons y z) (decode l' k' c)). *)
Defined.

Lemma list_decode_encode {l k : list X} (p : l = k)
  : list_decode (list_encode p) = p.
Proof.
  induction p; simpl.
  induction l; simpl.
  + constructor.
  + change (ap (fun z : list X => a :: z) (list_decode (r l)) = ap (fun z : list X => a :: z) idpath).
    apply ap. exact IHl.
Defined.

Fixpoint list_encode_decode {l k : list X}
  : forall c : list_code l k, list_encode (list_decode c) = c.
Proof.
  refine (match l, k with
    | nil, nil => _
    | x :: l', nil => _
    | nil, y :: k' => _
    | x :: l', y :: k' => _ end); simpl.
  + induction c; constructor.
  + induction c.
  + induction c.
  + intros [p c].
    refine (list_encode_switch p (list_decode c) @ _).
    srapply @path_prod'.
    - constructor.
    - exact (list_encode_decode l' k' c).
Defined.

Lemma equiv_list_encode_decode
  : forall l k : list X, l = k <~> list_code l k.
Proof.
  intros; exact (equiv_adjointify list_encode list_decode list_encode_decode list_decode_encode).
Defined.

Global Instance trunc_Empty {n : trunc_index}
  : IsTrunc n.+1 Empty.
Proof.
  induction n.
  + exact _.
  + srapply @trunc_succ.
Defined.

Definition trunc_code {n : trunc_index} {T : IsTrunc n.+2 X}
  : forall (l k : list X), IsTrunc n.+1 (list_code l k).
Proof.
  induction l.
  + induction k; exact _.
  + induction k; simpl.
    - exact _.
    - srapply @trunc_prod.
Defined.

(* in general, assuming univalence, we have this: *)
Lemma trunc_list `{Univalence} {n : trunc_index} {T : IsTrunc n.+2 X} (l k : list X)
  : IsTrunc n.+1 (l = k).
Proof.
  exact (transport (IsTrunc n.+1) (path_universe_uncurried (equiv_list_encode_decode l k)^-1) (trunc_code l k)).
Defined.

(* however, we can do it without univalence *)
Lemma set_list {T : IsHSet X} 
  : forall (l k : list X) (p q : l = k), p = q.
Proof.
  intros.
  refine ((list_decode_encode p)^ @ _ @ list_decode_encode q).
  apply ap.
  srapply @path_ishprop.
  exact (@trunc_code (-2) T l k).
Defined.

Lemma IsHSet_list {T : IsHSet X} 
  : IsHSet (list X).
Proof.
  srapply hset_axiomK.
  unfold axiomK; intros.
  exact (set_list x x p idpath).
Defined.

Lemma gpd_list {T : IsTrunc 1 X}
  : forall (l k : list X) (p q : l = k) (a b : p = q), a = b.
Proof.
  intros.
  refine ((moveR_Vp _ _ _ (concat_A1p (@list_decode_encode l k) a))^ @ _ @ moveR_Vp _ _ _ (concat_A1p (@list_decode_encode l k) b));
  apply whiskerL; apply whiskerR.
  refine (ap_compose list_encode list_decode a @ _ @ (ap_compose list_encode list_decode b)^);
  apply ap.
  apply (@trunc_code (-1) T l k).
Defined.

End list_truncations.

Section MonoidalStructureList.

Fixpoint app {X : Type} (l : list X)
  : list X -> list X
  := fun k => match l with
  | nil => k
  | cons x l' => cons x (app l' k)
  end.

Lemma ap_cons_app {X : Type} (x : X)
  {l1 l2 l1' l2' : list X} (p1 : l1 = l1') (p2 : l2 = l2')
  : ap011 app (ap (cons x) p1) p2
    = ap (cons x) (ap011 app p1 p2).
Proof.
  induction p1, p2; constructor.
Defined.

Lemma app_reflnil {X : Type} {l1 l2 : list X} (p : l1 = l2)
  : ap011 app (idpath nil) p = p.
Proof.
  induction p; constructor.
Defined.

Lemma alpha_list {X : Type}
  : forall a b c : list X, app (app a b) c = app a (app b c).
Proof.
  intros; induction a; simpl.
  + constructor.
  + exact (ap (cons a) IHa).
Defined.

Lemma lambda_list {X : Type}
  : forall b : list X, app nil b = b.
Proof.
  intros; constructor.
Defined.

Lemma rho_list {X : Type}
  : forall a : list X, app a nil = a.
Proof.
  intros; induction a.
  + constructor.
  + exact (ap (cons a) IHa).
Defined.

(* pentagon and triangle hold automatically if X is a set; however, they hold in general *)
Lemma pentagon_list {X : Type}
  : forall l1 l2 l3 l4 : list X,
      alpha_list (app l1 l2) l3 l4 @ alpha_list l1 l2 (app l3 l4)
      = ap011 app (alpha_list l1 l2 l3) idpath @ alpha_list l1 (app l2 l3) l4 @ ap011 app idpath (alpha_list l2 l3 l4).
Proof.
  intros; induction l1 as [|x l1]; simpl.
  + exact (concat_p1 _ @ (concat_1p _)^ @ (app_reflnil _)^).
  + refine (_ @ whiskerL _ (ap_cons_app x idpath (alpha_list l2 l3 l4))^ @ whiskerR (whiskerR (ap_cons_app x (alpha_list l1 l2 l3) idpath)^ _) _).
    refine ((ap_pp (cons x) _ _)^ @ _ @ ap_pp (cons x) _ _ @ whiskerR (ap_pp (cons x) _ _) _).
    apply ap; exact IHl1.
Defined.

Lemma triangle_list {X : Type}
  : forall l1 l2 : list X,
      alpha_list l1 nil l2 @ ap011 app (idpath l1) (lambda_list l2)
      = ap011 app (rho_list l1) (idpath l2).
Proof.
  intros; induction l1 as [|x l1]; simpl.
  + constructor.
  + refine (whiskerL _ (ap_cons_app x idpath (lambda_list l2)) @ _ @ (ap_cons_app x (rho_list l1) idpath)^).
    refine ((ap_pp (cons x) _ _)^ @ _).
    apply ap; exact IHl1.
Defined.

Definition listMG (X : Type) {T : IsHSet X} : MonoidalGroupoid
  := Build_MonoidalGroupoid (list X) (@trunc_succ 0 _ (IsHSet_list X)) nil app alpha_list lambda_list rho_list pentagon_list triangle_list.

Fixpoint list_functor_fun {X Y : Type} (h : X -> Y) (l : list X)
  : list Y
  := match l with
      | nil => nil
      | cons x l => cons (h x) (list_functor_fun h l) end.

Lemma ap_list_functor_fun_ap_cons {X Y : Type} (h : X -> Y) (x : X)
  {l1 l2 : list X} (p : l1 = l2)
  : ap (list_functor_fun h) (ap (cons x) p) = ap (cons (h x)) (ap (list_functor_fun h) p).
Proof.
  induction p; constructor.
Defined.

Fixpoint list_functor_fun_app {X Y : Type}
  (h : X -> Y) (l1 l2 : list X) {struct l1}
  : app (list_functor_fun h l1) (list_functor_fun h l2) = list_functor_fun h (app l1 l2)
  := match l1 with
    | nil => idpath
    | cons x l1 => ap (cons (h x)) (list_functor_fun_app h l1 l2) end.

Definition list_functor_arr
  : forall (X Y : Type) (T_X : IsHSet X) (T_Y : IsHSet Y), (X -> Y) -> MonoidalFunctor (listMG X) (listMG Y).
Proof.
  intros ???? h.
  srapply @Build_MonoidalFunctor; unfold mg_mm, mg_m; simpl.
  + exact (list_functor_fun h).
  + constructor.
  + apply @list_functor_fun_app.
  + intros l1 l2 l3; induction l1 as [|x l1]; simpl.
    - refine (concat_1p _ @ concat_p1 _ @ _ @ (concat_1p _)^ @ (concat_p1 _)^).
      exact (app_reflnil _).
    - refine (whiskerL _ (whiskerR (ap_cons_app (h x) idpath _) _) @ _ @ whiskerR (whiskerR (ap_cons_app (h x) _ idpath)^ _) _ @ whiskerL _ (ap_list_functor_fun_ap_cons h x _)^).
      refine (whiskerL _ (ap_pp (cons (h x)) _ _)^ @ (ap_pp (cons (h x)) _ _)^ @ _ @ ap_pp (cons (h x)) _ _ @ whiskerR (ap_pp (cons (h x)) _ _) _).
      exact (ap (ap (cons (h x))) IHl1).
  + constructor.
  + intro l1; induction l1 as [|x l1]; simpl.
    - constructor.
    - refine (_ @ whiskerR (whiskerR (ap_cons_app (h x) idpath idpath)^ _) _ @ whiskerL _ (ap_list_functor_fun_ap_cons h x _)^).
      refine (_ @ ap_pp (cons (h x)) _ _ @ whiskerR (ap_pp (cons (h x)) _ _) _).
      exact (ap (ap (cons (h x))) IHl1).
Defined.

Definition list_functor_id
  : forall (X : Type) (T_X : IsHSet X),
    MonoidalNatIso (list_functor_arr X X T_X T_X idmap) (MonoidalFunctor_id (listMG X)).
Proof.
  intros; srapply @Build_MonoidalNatIso.
  + exact (fix recid (l : list X) : list_functor_arr X X T_X T_X idmap l = MonoidalFunctor_id (listMG X) l := match l with nil => idpath | cons x l' => ap (cons x) (recid l') end).
  + constructor.
  + simpl.
    intros a b; refine (_ @ (concat_p1 _)^); revert b; revert a.
    refine (fix recid2 (a : list X) : forall b : list X, _ := match a with nil => _ | cons x l' => _ end); simpl; intro b.
    - refine (concat_1p _ @ _). exact (app_reflnil _)^.
    - refine ((ap_pp (cons x) _ _)^ @ _).
      refine (ap (ap (cons x)) (recid2 l' b) @ (ap_cons_app x _ _)^).
Defined.

Definition list_functor_comp
  : forall (X Y Z : Type) (T_X : IsHSet X) (T_Y : IsHSet Y) (T_Z : IsHSet Z) (g : Y -> Z) (f : X -> Y),
    MonoidalNatIso
      (MonoidalFunctor_comp (list_functor_arr Y Z T_Y T_Z g) (list_functor_arr X Y T_X T_Y f))
      (list_functor_arr X Z T_X T_Z (fun x : X => g (f x))).
Proof.
  intros; srapply @Build_MonoidalNatIso.
  + refine (fix reccomp (l : list X) : MonoidalFunctor_comp (list_functor_arr Y Z T_Y T_Z g) (list_functor_arr X Y T_X T_Y f) l = list_functor_arr X Z T_X T_Z (fun x : X => g (f x)) l := match l with nil => idpath | cons x l' => ap (cons (g (f x))) (reccomp l') end).
  + constructor.
  + refine (fix reccomp2 (a : list X) : forall b : listMG X, _ := match a with nil => _ | cons x l' => _ end); simpl; intro b.
    - refine (concat_1p _ @ _ @ (concat_p1 _)^).
      exact (app_reflnil _)^.
    - refine (whiskerR (whiskerL _ (ap_list_functor_fun_ap_cons g (f x) _) @ (ap_pp (cons (g (f x))) _ _)^) _ @ (ap_pp (cons (g (f x))) _ _)^ @ _).
      refine (_ @ ap_pp (cons (g (f x))) _ _ @ whiskerR (ap_cons_app (g (f x)) _ _)^ _).
      apply ap. exact (reccomp2 l' b).
Defined.

Definition list_functor
  : IsFunctor (fun X T_X => listMG X).
Proof.
  srapply @Build_IsFunctor; simpl.
  + exact list_functor_arr.
  + exact list_functor_id.
  + exact list_functor_comp.
Defined.

Section Redefinitions.

Context (X : Type) {T : IsTrunc 0 X}.

Definition alpha_list_natural {l1 l2 l3 l1' l2' l3' : list X}
  (p1 : l1 = l1') (p2 : l2 = l2') (p3 : l3 = l3')
  := @alpha_natural (listMG X) l1 l2 l3 l1' l2' l3' p1 p2 p3.

Definition lambda_list_natural {l2 l2' : list X} (p2 : l2 = l2')
  := @lambda_natural (listMG X) l2 l2' p2.

Definition rho_list_natural {l1 l1' : list X} (p1 : l1 = l1')
  := @rho_natural (listMG X) l1 l1' p1.

Definition rho_list_l1_nil (l1 : list X)
  := @rho_a_e (listMG X) l1.

Definition lambda_list_nil_l2 (l2 : list X)
  := @lambda_e_b (listMG X) l2.

Definition alpha_lambda_list (l1 l2 : list X)
  := @alpha_lambda (listMG X) l1 l2.

Definition alpha_rho_list (l1 l2 : list X)
  := @alpha_rho (listMG X) l1 l2.

Definition lambda_rho_list_nil
  := @lambda_rho_e (listMG X).

End Redefinitions.

End MonoidalStructureList.

End lists.