Require Export lists FMG.

Section Coherence.

Context (X : Type) {T_X : IsHSet X}.

Open Scope list.

Definition K_fun
  : FMG X -> list X
  := FMG_rec X (list X) nil (fun x => cons x nil) app alpha_list lambda_list rho_list pentagon_list triangle_list (@trunc_succ 0 (list X) (IsHSet_list X)).

Definition K_fun_beta_alpha (a b c : FMG X)
  : ap K_fun (alpha a b c) = alpha_list (K_fun a) (K_fun b) (K_fun c)
  := FMG_rec_beta_alpha X (list X) nil (fun x => cons x nil) app alpha_list lambda_list rho_list pentagon_list triangle_list (@trunc_succ 0 (list X) (IsHSet_list X)) a b c.

Definition K_fun_beta_lambda (b : FMG X)
  : ap K_fun (lambda b) = lambda_list (K_fun b)
  := FMG_rec_beta_lambda X (list X) nil (fun x => cons x nil) app alpha_list lambda_list rho_list pentagon_list triangle_list (@trunc_succ 0 (list X) (IsHSet_list X)) b.

Definition K_fun_beta_rho (a : FMG X)
  : ap K_fun (rho a) = rho_list (K_fun a)
  := FMG_rec_beta_rho X (list X) nil (fun x => cons x nil) app alpha_list lambda_list rho_list pentagon_list triangle_list (@trunc_succ 0 (list X) (IsHSet_list X)) a.

Definition K
  : MonoidalFunctor (FMG_MG X) (listMG X).
Proof.
  srapply @Build_MonoidalFunctor;
  unfold mg_mm, mg_m; simpl.
  + exact K_fun.
  + constructor.
  + constructor.
  + intros; simpl.
    refine (concat_p1 _ @ _^ @ (concat_1p _)^).
    exact (K_fun_beta_alpha a b c).
  + intros; simpl.
    refine (_^ @ (concat_1p _)^).
    exact (K_fun_beta_lambda b).
  + intros; simpl.
    refine (_^ @ (concat_1p _)^).
    exact (K_fun_beta_rho a).
Defined.

Fixpoint J_fun (l : list X)
  : FMG X
  := match l with
    | nil => e
    | x :: l => m (iota x) (J_fun l) end.

Lemma ap_J_ap_cons {l l' : list X} (x : X)
  (p : l = l')
  : ap J_fun (ap (cons x) p) = mm idpath (ap J_fun p).
Proof.
  induction p; constructor.
Defined.

Fixpoint J_2 (l1 l2 : list X) {struct l1}
  : m (J_fun l1) (J_fun l2) = J_fun (app l1 l2)
  := match l1 with
    | nil => lambda _
    | x :: l1 => alpha _ _ _ @ mm idpath (J_2 l1 l2) end.

Definition J_alpha
  : forall a b c : list X,
    alpha (J_fun a) (J_fun b) (J_fun c) @ (ap011 m 1 (J_2 b c) @ J_2 a (app b c))
    = (ap011 m (J_2 a b) 1 @ J_2 (app a b) c) @ ap J_fun (alpha_list a b c).
Proof.
  intros l1 l2 l3; induction l1 as [|x l1]; hnf.
  + refine (_ @ (concat_p1 _)^).
    refine (whiskerL _ (lambda_FMG_natural (J_2 l2 l3))^ @ concat_p_pp _ _ _ @ _); apply whiskerR.
    exact (alpha_lambda_FMG (J_fun l2) (J_fun l3)).
  + refine (whiskerL _ (concat_p_pp _ _ _ @ whiskerR (alpha_FMG_natural idpath idpath (J_2 l2 l3))^ _ @ concat_pp_p _ _ _) @ _).
    refine (concat_p_pp _ _ _ @ whiskerR (pentagon _ _ _ _ @ concat_pp_p _ _ _) _ @ _);
    refine (concat_pp_p _ _ _ @ _ @ concat_p_pp _ _ _ @ whiskerR (ap011_pqpq m _ _ idpath idpath) _ @ concat_p_pp _ _ _); apply whiskerL.
    refine (concat_pp_p _ _ _ @ _ @ concat_p_pp _ _ _ @ whiskerR (alpha_FMG_natural _ _ _) _ @ concat_pp_p _ _ _ @ whiskerL _ (concat_p_pp _ _ _)); apply whiskerL.
    refine (_ @ whiskerL _ (ap_J_ap_cons x _)^ @ concat_pp_p _ _ _).
    refine (whiskerL _ (ap011_pqpq m idpath idpath _ _) @ ap011_pqpq m idpath idpath _ _ @ _ @ (ap011_pqpq m idpath idpath _ _)^ @ whiskerR (ap011_pqpq m idpath idpath _ _)^ _);
    apply ap; exact IHl1.
Defined.

Definition J_lambda
  : forall b : list X,
    lambda (J_fun b) = (ap011 m 1 1 @ J_2 nil b) @ idpath.
Proof.
  intro l2; simpl.
  exact ((concat_1p _)^ @ (concat_p1 _)^).
Defined.

Definition J_rho
  : forall a : list X,
  rho (J_fun a) = (ap011 m 1 1 @ J_2 a nil) @ ap J_fun (rho_list a).
Proof.
  intro l1; induction l1 as [|x l1]; hnf.
  + refine (_^ @ (concat_1p _)^ @ (concat_p1 _)^).
    exact lambda_rho_FMG_e.
  + refine (_ @ concat_p_pp _ _ _ @ (concat_1p _)^ @ concat_p_pp _ _ _);
    refine ((alpha_rho_FMG _ _)^ @ _); apply whiskerL.
    refine (ap (mm idpath) IHl1 @ (ap011_pqpq m idpath idpath _ _)^ @ whiskerR (ap011_pqpq m idpath idpath _ _)^ _ @ concat_pp_p _ _ _ @ concat_1p _ @ _); apply whiskerL.
    exact (ap_J_ap_cons x _)^.
Defined.

Definition J
  : MonoidalFunctor (listMG X) (FMG_MG X)
  := Build_MonoidalFunctor (listMG X) (FMG_MG X) J_fun idpath J_2 J_alpha J_lambda J_rho.

(***)

Lemma eta_homotopy_alpha (a b c : FMG X)
  (a' : a = J_fun (K_fun a)) (b' : b = J_fun (K_fun b)) (c' : c = J_fun (K_fun c))
  : (mm (mm a' b' @ J_2 (K_fun a) (K_fun b)) c' @ J_2 (K_fun (m a b)) (K_fun c))
    @ ap (J_fun o K_fun) (alpha a b c)
    = ap idmap (alpha a b c)
    @ (mm a' (mm b' c' @ J_2 (K_fun b) (K_fun c)) @ J_2 (K_fun a) (K_fun (m b c))).
Proof.
  refine (whiskerR (whiskerR (ap011_pqp1 m (mm a' b') (J_2 (K_fun a) (K_fun b)) c')^ _) _ @ _ @ whiskerL _ (whiskerR (ap011_pq1q m a' (mm b' c') (J_2 (K_fun b) (K_fun c))) _)).
  refine (whiskerL _ (ap_compose K_fun J_fun _ @ ap (ap J_fun) (K_fun_beta_alpha a b c)) @ _).
  refine (whiskerR (concat_pp_p _ _ _) _ @ concat_pp_p _ _ _ @ whiskerL _ (J_alpha (K_fun a) (K_fun b) (K_fun c))^ @ concat_p_pp _ _ _ @ _ @ concat_pp_p _ _ _ @ whiskerL _ (concat_p_pp _ _ _));
    apply whiskerR.
  refine (_ @ whiskerR (ap_idmap _)^ _).
  exact (alpha_FMG_natural a' b' c')^.
Defined.

Lemma eta_homotopy_lambda (b : FMG X) (b' : b = J_fun (K_fun b))
  : (mm 1 b' @ J_2 (K_fun e) (K_fun b)) @ ap (fun w : FMG X => J_fun (K_fun w)) (lambda b)
    = ap idmap (lambda b) @ b'.
Proof.
  refine (whiskerL _ (ap_compose K_fun J_fun _ @ ap (ap J_fun) (K_fun_beta_lambda b)) @ concat_p1 _ @ _).
  refine (_ @ whiskerR (ap_idmap _)^ _).
  exact (lambda_FMG_natural b')^.
Defined.

Lemma eta_homotopy_rho (a : FMG X) (a' : a = J_fun (K_fun a))
  : (mm a' 1 @ J_2 (K_fun a) (K_fun e)) @ ap (fun w : FMG X => J_fun (K_fun w)) (rho a)
    = ap idmap (rho a) @ a'.
Proof.
  refine (whiskerL _ (ap_compose K_fun J_fun _ @ ap (ap J_fun) (K_fun_beta_rho a)) @ _).
  refine (concat_pp_p _ _ _ @ whiskerL _ (whiskerR (concat_1p _)^ _ @ (J_rho (K_fun a))^) @ _).
  refine (_ @ whiskerR (ap_idmap _)^ _).
  exact (rho_FMG_natural a')^.
Defined.

Lemma eta_homotopy (* unit of the adjunction *)
  : (fun a : FMG X => a) == J o K.
Proof.
  srapply FMG_ind_to_paths_in_gpd; simpl.
  + constructor.
  + intros; exact (rho _)^.
  + intros ?? IHa IHb;
    change (m a b = J_fun (app (K_fun a) (K_fun b))).
    refine (mm IHa IHb @ _).
    apply J_2.
  + exact eta_homotopy_alpha. (* this case uses J_alpha, which uses pentagon and alpha_lambda, which uses both pentagon and triangle *)
  + exact eta_homotopy_lambda. (* this case is simpler and does not use coherence diagrams (J_lambda does not) *)
  + exact eta_homotopy_rho. (* this case uses J_rho, which uses both coherence diagrams (because of rho_alpha and lambda_rho_e) *)
  + exact T_FMG.
Defined.

(** Check that this is a monoidal natural isomorphism **)

Definition eta
  : MonoidalNatIso (MonoidalFunctor_id _) (MonoidalFunctor_comp J K).
Proof.
  srapply @Build_MonoidalNatIso.
  + exact eta_homotopy.
  + constructor.
  + intros; unfold mg_f2; simpl.
    change (idpath @ (mm (eta_homotopy a) (eta_homotopy b) @ J_2 (K_fun a) (K_fun b)) = ap011 m (eta_homotopy a) (eta_homotopy b) @ (J_2 (K_fun a) (K_fun b) @ 1)).
    exact (concat_1p _ @ whiskerL _ (concat_p1 _)^).
Defined.

(***)

Theorem FMG_coherence
  : forall {a b : FMG X} (p q : a = b), p = q.
Proof.
  intros.
  refine ((moveR_pV _ _ _ (concat_pA1 eta_homotopy p))^ @ _ @ moveR_pV _ _ _ (concat_pA1 eta_homotopy q)).
  apply whiskerR; apply whiskerL.
  refine (ap_compose K J p @ _ @ (ap_compose K J q)^).
  apply ap.
  srapply @set_list.
Defined.

Corollary IsHSet_FMG
  : IsHSet (FMG X).
Proof.
  srapply hset_axiomK.
  exact (fun x p => FMG_coherence p idpath).
Defined.

(* other important stuff *)

Lemma ap_cons_ap_K {a b : FMG X} (x : X)
  (p : a = b)
  : ap K (mm (idpath (iota x)) p) = ap (cons x) (ap K p).
Proof.
  induction p; constructor.
Defined.

Fixpoint epsilon_homotopy (l : list X)
  : K (J l) = l
  := match l with
    | nil => idpath
    | x :: l => ap (cons x) (epsilon_homotopy l) end.

Definition epsilon
  : MonoidalNatIso (MonoidalFunctor_comp K J) (MonoidalFunctor_id _).
Proof.
  srapply @Build_MonoidalNatIso.
  + exact epsilon_homotopy.
  + constructor.
  + intros l1 l2; unfold mg_f2; simpl.
    refine (whiskerR (concat_1p _) _ @ _ @ (concat_p1 _)^).
    induction l1 as [|x l1]; hnf.
    - refine (whiskerR (K_fun_beta_lambda _) _ @ concat_1p _ @ _).
      exact (app_reflnil _)^.
    - refine (whiskerR (ap_pp K_fun (alpha (iota x) (J_fun l1) (J_fun l2)) (mm 1 (J_2 l1 l2))) _ @ _).
      refine (whiskerR (@concat2 _ _ _ _ (ap K_fun (alpha (iota x) (J_fun l1) (J_fun l2))) _ (ap K_fun (mm 1 (J_2 l1 l2))) (ap (cons x) (ap K (J_2 l1 l2))) (K_fun_beta_alpha _ _ _) (ap_cons_ap_K x (J_2 l1 l2)) @ concat_1p _) _ @ _).
      refine ((ap_pp (cons x) _ _)^ @ _ @ (ap_cons_app x _ _)^);
        apply ap; exact IHl1.
Defined.

Proposition equiv_FMG_list : FMG X <~> list X.
Proof.
  srefine (equiv_adjointify K J epsilon_homotopy (fun x => (eta_homotopy x)^)).
Defined.

Definition mon_equiv_FMG_list
  : MonoidalEquivalence (FMG_MG X) (listMG X)
  := (K; J; (MonoidalNatIso_V _ _ eta, epsilon)).



(** This part serves as comparison to previous formalisations **)
Section comparison_Beylin.

Context `{Funext}. (* already required for N *)

Definition N
  : FMG X -> (list X -> list X).
Proof.
  srapply @FMG_rec.
  + exact idmap.
  + intro x; exact (cons x).
  + intros f g; exact (f o g).
  + constructor.
  + constructor.
  + constructor.
  + constructor.
  + constructor.
  + exact (@trunc_forall _ (list X) (fun _ => list X) 1 (fun _ => @trunc_succ 0 (list X) (IsHSet_list X))).
Defined.

Definition N_beta_alpha (a b c : FMG X)
  : ap N (alpha a b c) = idpath
  := FMG_rec_beta_alpha _ _ _ _ _ _ _ _ _ _ _ a b c.

Definition N_beta_lambda (b : FMG X)
  : ap N (lambda b) = idpath
  := FMG_rec_beta_lambda _ _ _ _ _ _ _ _ _ _ _ b.

Definition N_beta_rho (a : FMG X)
  : ap N (rho a) = idpath
  := FMG_rec_beta_rho _ _ _ _ _ _ _ _ _ _ _ a.

Definition ev
  : list X -> (list X -> list X) -> list X
  := fun l f => f l.

Lemma evN_K
  : forall (a : FMG X) (l : list X), ev l (N a) = app (K a) l.
Proof.
  unfold ev.
  srefine (FMG_ind_to_fam_paths_in_gpd X (list X) (list X) N (fun a l => app (K a) l) _ _ _ _ _ _ (@trunc_succ 0 (list X) (IsHSet_list X))); hnf.
  + constructor.
  + constructor.
  + intros a b IHa IHb l.
    change (N a (N b l) = app (app (K a) (K b)) l).
    refine (ap (N a) (IHb l) @ IHa (app (K b) l) @ _).
    exact (alpha_list _ _ _)^.
  + intros a b c IHa IHb IHc l; simpl.
    refine (_ @ (concat_1p _)^ @ whiskerR (ap (ap (ev l)) (N_beta_alpha a b c)^ @ (ap_compose N (ev l) (alpha a b c))^) _).
    change (
((ap (N a o N b) (IHc l) @
  ((ap (N a) (IHb (app (K_fun c) l)) @ IHa (app (K_fun b) (app (K_fun c) l))) @
   (alpha_list (K_fun a) (K_fun b) (app (K_fun c) l))^)) @ (alpha_list (app _ _) (K_fun c) l)^) @
ap (fun z : FMG X => app (K_fun z) l) (alpha a b c) =
(ap (N a) ((ap (N b) (IHc l) @ IHb (app (K_fun c) l)) @ (alpha_list (K_fun b) (K_fun c) l)^) @
 IHa (app (K_fun (m b c)) l)) @ (alpha_list (K_fun a) (app _ _) l)^
).
    refine (concat_pp_p _ _ _ @ concat_pp_p _ _ _ @ whiskerR (ap_compose (N b) (N a) (IHc l)) _ @ _ @ concat_p_pp _ _ _ @ whiskerR (ap_pp _ _ _)^ _ @ concat_p_pp _ _ _ @ whiskerR (ap_pp _ _ _)^ _ @ concat_p_pp _ _ _); apply whiskerL.
    refine (concat_pp_p _ _ _ @ concat_pp_p _ _ _ @ _); apply whiskerL.
    change (IHa (app (K_fun b) (app (K_fun c) l)) @ ((alpha_list (K_fun a) (K_fun b) (app (K_fun c) l))^ @ ((alpha_list (app _ _) (K_fun c) l)^ @ ap (fun z : FMG X => app (K_fun z) l) (alpha a b c))) =
ap (N a) (alpha_list (K_fun b) (K_fun c) l)^ @ (IHa (app (app _ _) l) @ (alpha_list (K_fun a) (app _ _) l)^)).
    refine (whiskerL _ (concat_p_pp _ _ _ @ whiskerR ((inv_pp _ _)^ @ ap inverse (pentagon_list (K_fun a) (K_fun b) (K_fun c) l) @ inv_pp _ _ @ whiskerL _ (inv_pp _ _) @ concat_p_pp _ _ _) _ @ concat_pp_p _ _ _ @ whiskerL _ (whiskerR (ap inverse (ap011_p1 app _)) _ @ whiskerL _ (ap_compose K_fun (fun z => app z l) (alpha a b c) @ ap (ap (fun z => app z l)) (K_fun_beta_alpha a b c)) @ concat_Vp _) @ concat_p1 _) @ _).
    refine (concat_p_pp _ _ _ @ _ @ concat_pp_p _ _ _); apply whiskerR.
    refine (whiskerL _ (ap inverse (ap011_1p app (alpha_list _ _ _))) @ _ @ whiskerR (ap_V _ _)^ _);
    apply moveL_Vp; refine (concat_p_pp _ _ _ @ _); apply moveR_pV.
    exact (homotopy_square IHa (alpha_list _ _ _))^.
  + intros b IHb l; simpl.
    refine (whiskerR (concat_p1 _ @ concat_p1 _ @ ap_idmap _) _ @ _).
    refine (_ @ concat_p1 _ @ (concat_1p _)^ @ whiskerR (ap (ap (ev l)) (N_beta_lambda b)^ @ (ap_compose N (ev l) (lambda b))^) _); apply whiskerL.
    refine (ap_compose K_fun (fun z => app z l) (lambda b) @ _).
    refine (ap (ap (fun z => app z l)) (K_fun_beta_lambda _)).
  + intros a IHa l; simpl.
    refine (whiskerR (whiskerR (concat_1p _) _) _ @ concat_pp_p _ _ _ @ _).
    refine (_ @ concat_p1 _ @ (concat_1p _)^ @ whiskerR (ap (ap (ev l)) (N_beta_rho a)^ @ (ap_compose N (ev l) (rho a))^) _); apply whiskerL.
    refine (whiskerL _ (ap_compose K_fun (fun z => app z l) (rho a) @ ap (ap (fun z => app z l)) (K_fun_beta_rho _)) @ _).
    refine (whiskerL _ (ap011_p1 app _)^ @ _);
    change ((alpha_list (K_fun a) nil l)^ @ ap011 app (rho_list (K_fun a)) idpath = ap011 app idpath (lambda_list l));
    apply moveR_Vp.
    exact (triangle_list (K_fun a) l)^.
Defined.

Lemma N_K
  : forall a : FMG X, N a nil = K a.
Proof.
  intro a.
  exact (evN_K a nil @ rho_list (K a)).
Defined.

End comparison_Beylin.

End Coherence.

