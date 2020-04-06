Require Export slists FSMG.

Section Coherence.

Context `{Funext}.
Context (X : Type) {T_X : IsHSet X}.

Definition K_fun
  : FSMG X -> slist X
  := FSMG_rec X (slist X) nil (fun x => x :: nil) sapp alpha_slist lambda_slist rho_slist tau_slist  pentagon_slist triangle_slist hexagon_slist bigon_slist T_slist.

Definition K_fun_beta_alpha (a b c : FSMG X)
  : ap K_fun (alpha a b c) = alpha_slist (K_fun a) (K_fun b) (K_fun c)
  := FSMG_rec_beta_alpha X (slist X) nil (fun x => x :: nil) sapp alpha_slist lambda_slist rho_slist tau_slist  pentagon_slist triangle_slist hexagon_slist bigon_slist _ a b c.

Definition K_fun_beta_lambda (b : FSMG X)
  : ap K_fun (lambda b) = lambda_slist (K_fun b)
  := FSMG_rec_beta_lambda X (slist X) nil (fun x => x :: nil) sapp alpha_slist lambda_slist rho_slist tau_slist  pentagon_slist triangle_slist hexagon_slist bigon_slist _ b.

Definition K_fun_beta_rho (a : FSMG X)
  : ap K_fun (rho a) = rho_slist (K_fun a)
  := FSMG_rec_beta_rho X (slist X) nil (fun x => x :: nil) sapp alpha_slist lambda_slist rho_slist tau_slist  pentagon_slist triangle_slist hexagon_slist bigon_slist _ a.

Definition K_fun_beta_tau (a b : FSMG X)
  : ap K_fun (tau a b) = tau_slist (K_fun a) (K_fun b)
  := FSMG_rec_beta_tau X (slist X) nil (fun x => x :: nil) sapp alpha_slist lambda_slist rho_slist tau_slist  pentagon_slist triangle_slist hexagon_slist bigon_slist _ a b.

Definition K
  : SymMonoidalFunctor (FSMG_SMG X) (slistSMG X).
Proof.
  srapply @Build_SymMonoidalFunctor;
  unfold smg_mm, smg_m; simpl.
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
  + intros; simpl.
    refine (concat_p1 _ @ _^ @ (concat_1p _)^).
    exact (K_fun_beta_tau a b).
Defined.

  Definition J_fun_swap
    : swap'_rec_type (FSMG X) (fun (x : X) (a : FSMG X) => m (iota x) a).
  Proof.
    unfold_slist_types; intros x y a.
    exact ((alpha _ _ _)^ @ mm (tau _ _) 1 @ alpha _ _ _).
  Defined.

  Definition J_fun_double
    : double'_rec_type (FSMG X) (fun (x : X) (a : FSMG X) => m (iota x) a) J_fun_swap.
  Proof.
    unfold_slist_types; unfold J_fun_swap; intros x y a.
    refine (concat_pp_p _ _ _ @ whiskerL _ (whiskerL _ (concat_pp_p _ _ _) @ concat_p_pp _ _ _ @ whiskerR (concat_pV _) _ @ concat_1p _) @ _).
    refine (concat_p_pp _ _ _ @ whiskerR (concat_pp_p _ _ _ @ whiskerL _ (ap011_pqpq m (tau _ _) (tau _ _) 1 1 @ ap011 mm (bigon _ _) (idpath idpath)) @ concat_p1 _) _ @ _).
    exact (concat_Vp _).
  Defined.

  Definition J_fun_triple
    : triple'_rec_type (FSMG X) (fun (x : X) (a : FSMG X) => m (iota x) a) J_fun_swap.
  Proof.
    unfold_slist_types; unfold J_fun_swap; intros x y z a.
    repeat rewrite (ap_pp (m (iota x))), (ap_pp (m (iota y))), (ap_pp (m (iota z)));
    repeat rewrite ap_V;
    repeat rewrite concat_p_pp.
    refine (whiskerL _ ((concat_1p _)^ @ whiskerR (concat_Vp (alpha _ _ _))^ _ @ concat_pp_p _ _ _ @ whiskerL _ (pentagon _ _ _ _)) @ _);
    repeat rewrite concat_p_pp; apply whiskerR.
    refine (whiskerL _ ((concat_1p _)^ @ whiskerR (concat_Vp (mm (mm 1 (tau _ _)) 1))^ _ @ concat_pp_p _ _ _ @ whiskerL _ (alpha_FSMG_natural 1 (tau _ _) 1)^) @ _);
    repeat rewrite concat_p_pp; apply whiskerR.
    refine (whiskerL _ ((concat_1p _)^ @ whiskerR (concat_Vp (mm (alpha _ _ _) (idpath a)))^ _ @ concat_pp_p _ _ _) @ concat_p_pp _ _ _ @ _);
    apply moveL_pV; refine (concat_pp_p _ _ _ @ whiskerL _ (pentagon _ _ _ _)^ @ _);
    repeat rewrite concat_p_pp; apply whiskerR.
    refine (whiskerL _ ((concat_1p _)^ @ whiskerR (concat_Vp (mm (mm (tau _ _) 1) 1))^ _ @ concat_pp_p _ _ _ @ whiskerL _ (alpha_FSMG_natural (tau _ _) 1 1)^) @ _);
    repeat rewrite concat_p_pp; apply whiskerR.
    apply moveR_pM; repeat apply moveR_pV;
    refine (_ @ whiskerL _ (whiskerR (ap011_pqpq m _ _ 1 1) _ @ (ap011_pqpq m _ _ 1 1) @ ap011 mm (hexagon _ _ _) (idpath idpath) @ (ap011_pqpq m _ _ 1 1)^ @ whiskerR (ap011_pqpq m _ _ 1 1)^ _ @ concat_pp_p _ _ _) @ concat_p_pp _ _ _ @ concat_p_pp _ _ _);
    repeat rewrite concat_p_pp; apply whiskerR; apply moveR_pV.
    refine (whiskerL _ ((concat_1p _)^ @ whiskerR (concat_Vp (alpha _ _ _))^ _ @ concat_pp_p _ _ _ @ whiskerL _ (alpha_FSMG_natural (tau _ _) 1 1)) @ _);
    repeat rewrite concat_p_pp; apply whiskerR.
    refine (whiskerL _ ((concat_1p _)^ @ whiskerR (concat_Vp (mm (tau _ _) 1))^ _ @ concat_pp_p _ _ _ @ whiskerL _ (ap011_pqpq m _ _ 1 1 @ ap011 mm (tau_FSMG_natural _ _) (idpath idpath) @ (ap011_pqpq m _ _ 1 1)^)) @ _);
    repeat rewrite concat_p_pp; apply whiskerR.
    refine (_ @ whiskerL _ ((concat_1p _)^ @ whiskerR (concat_pV _)^ _ @ concat_pp_p _ _ _) @ concat_p_pp _ _ _ @ whiskerL _ ((concat_1p _)^ @ whiskerR (concat_Vp _)^ _ @ concat_pp_p _ _ _) @ concat_p_pp _ _ _ @ whiskerL _ ((concat_1p _)^ @ whiskerR (concat_Vp _)^ _ @ concat_pp_p _ _ _ @ whiskerL _ (concat_p_pp _ _ _ @ concat_p_pp _ _ _)) @ concat_p_pp _ _ _ @  whiskerL _ (moveR_pV _ _ _ (moveR_pV _ _ _ (pentagon _ _ _ _)))).
    apply moveL_pV;
    refine (concat_pp_p _ _ _ @ whiskerL _ (alpha_FSMG_natural _ _ _)^ @ concat_p_pp _ _ _ @ _);
    apply whiskerR.
    repeat rewrite concat_pp_p.
    refine (_ @ (moveL_Vp _ _ _ (moveR_pV _ _ _ (moveL_Vp _ _ _ (pentagon _ _ _ _) @ concat_p_pp _ _ _)))^); apply whiskerL; repeat rewrite concat_p_pp; apply whiskerR; repeat rewrite concat_pp_p; apply moveL_Vp.
    refine (concat_p_pp _ _ _ @ whiskerR (alpha_FSMG_natural (tau _ _) 1 1) _ @ concat_pp_p _ _ _ @ _).
    apply (cancelR _ _ (mm (tau _ _) 1)); apply (cancelR _ _ (mm (alpha _ _ _) 1));
    refine (_ @ whiskerR (ap011_pqpq m _ _ 1 1) _ @ ap011_pqpq m _ _ 1 1 @ ap011 mm (hexagon _ _ _)^ (idpath idpath) @ (ap011_pqpq m _ _ 1 1)^ @ whiskerR (ap011_pqpq m _ _ 1 1)^ _);
    repeat rewrite concat_pp_p; apply whiskerL.
    refine (concat_p_pp _ _ _ @ whiskerR (pentagon _ _ _ _) _ @ concat_pp_p _ _ _ @ concat_pp_p _ _ _ @ _); apply whiskerL.
    refine (whiskerL _ (concat_p_pp _ _ _ @ whiskerR (concat_pV _) _ @ concat_1p _) @ _).
    refine (concat_p_pp _ _ _ @ whiskerR (alpha_FSMG_natural 1 (tau _ _) 1) _ @ concat_pp_p _ _ _ @ _);
    apply moveR_Mp;
    refine (_ @ (concat_Vp _)^).
    refine (whiskerL _ (whiskerL _ (whiskerL _ (whiskerL _ (concat_p_pp _ _ _ @ whiskerR (concat_Vp _) _ @ concat_1p _)))) @ _);
    apply moveR_Mp; refine (_ @ (concat_p1 _)^); apply moveR_Mp; refine (concat_p_pp _ _ _ @ _); apply moveR_pM; repeat rewrite <- inv_pp; apply ap; refine (_ @ concat_pp_p _ _ _); apply pentagon.
  Qed.

Definition J_fun
  : slist X -> FSMG X.
Proof.
  srapply @slist_rec.
  + exact e.
  + intros x a; exact (m (iota x) a).
  + exact J_fun_swap.
  + exact J_fun_double.
  + exact J_fun_triple.
  + exact T_FSMG.
Defined.

Lemma ap_J_ap_cons {l l' : slist X} (x : X)
  (p : l = l')
  : ap J_fun (ap (cons x) p) = mm idpath (ap J_fun p).
Proof.
  induction p; constructor.
Defined.

Definition J_fun_beta_swap (x y : X) (l : slist X)
  : ap J_fun (swap x y l) = ((alpha (iota x) (iota y) (J_fun l))^ @ mm (tau (iota x) (iota y)) 1) @ alpha (iota y) (iota x) (J_fun l).
Proof.
  srapply @slist_rec_beta_swap.
Defined.

    Definition J_2_swap (l2 : slist X)
      : forall (x y : X) (l1 : slist X) (h : m (J_fun l1) (J_fun l2) = J_fun (l1 ++ l2)),
        (alpha (iota x) (J_fun (y :: l1)) (J_fun l2) @ mm 1 (alpha (iota y) (J_fun l1) (J_fun l2) @ mm 1 h))
        @ ap (fun w : slist X => J_fun (w ++ l2)) (swap x y l1)
        = ap (fun w : slist X => m (J_fun w) (J_fun l2)) (swap x y l1)
        @ (alpha (iota y) (J_fun (x :: l1)) (J_fun l2) @ mm 1 (alpha (iota x) (J_fun l1) (J_fun l2) @ mm 1 h)).
    Proof.
      intros.
      refine (whiskerR (whiskerL _ (ap011_pqpq m 1 1 _ _)^) _ @ _ @ whiskerL _ (whiskerL _ (ap011_pqpq m 1 1 _ _))).
      repeat rewrite concat_p_pp.
      refine (whiskerL _ (ap_compose (fun w => w ++ l2) J_fun (swap x y l1) @ ap (ap J_fun) (sapp_blank_beta_swap x y l1 l2) @ J_fun_beta_swap x y (l1 ++ l2)) @ _);
      repeat rewrite concat_p_pp.
      refine (whiskerL _ ((concat_1p _)^ @ whiskerR (concat_Vp (mm (mm 1 1) h))^ _ @ concat_pp_p _ _ _ @ whiskerL _ (alpha_FSMG_natural 1 1 h)^) @ _);
      repeat rewrite concat_p_pp; apply whiskerR.
      refine (whiskerL _ ((concat_1p _)^ @ whiskerR (concat_Vp (alpha _ _ _))^ _ @ concat_pp_p _ _ _ @ whiskerL _ (pentagon _ _ _ _)) @ _);
      repeat rewrite concat_p_pp; apply whiskerR; apply whiskerR.
      refine (_ @ whiskerR (whiskerR (ap011_VV m _ 1)^ _ @ ap011_pqpq m _ _ 1 1) _ @ ap011_pqpq m _ _ 1 1 @ ap011 mm (J_fun_beta_swap x y l1)^ (idpath idpath) @ ap011_p1 m (ap J_fun (swap x y l1)) @ (ap_compose J_fun (fun w => m w (J_fun l2)) (swap x y l1))^);
      repeat rewrite concat_pp_p; apply moveL_Vp.
      refine (concat_p_pp _ _ _ @ concat_p_pp _ _ _ @ whiskerR (pentagon _ _ _ _)^ _ @ _);
      repeat rewrite concat_pp_p.
      refine (whiskerL _ (concat_p_pp _ _ _ @ whiskerR (alpha_FSMG_natural 1 1 h) _ @ concat_pp_p _ _ _ @ whiskerL _ (concat_p_pp _ _ _ @ whiskerR (concat_pV _) _ @ concat_1p _)) @ _).
      refine (whiskerL _ (concat_p_pp _ _ _ @ whiskerR (ap011_1qp1 m (tau _ _) h @ (ap011_p11q m (tau _ _) h)^) _ @ concat_pp_p _ _ _) @ whiskerL _ (whiskerL _ (concat_p_pp _ _ _ @ whiskerR (concat_pV _) _ @ concat_1p _)) @ _);
      repeat rewrite concat_p_pp; apply whiskerR; apply moveR_pV.
      exact (alpha_FSMG_natural (tau _ _) 1 1).
    Qed.

  Definition J_2
    : forall l1 l2 : slist X, m (J_fun l1) (J_fun l2) = J_fun (l1 ++ l2).
  Proof.
    intros l1 l2; revert l1; srapply @slist_ind_to_paths_in_gpd; hnf.
    + change (m e (J_fun l2) = J_fun l2). exact (lambda _).
    + intros x l1 h.
      change (m (m (iota x) (J_fun l1)) (J_fun l2) = m (iota x) (J_fun (l1 ++ l2))).
      exact (alpha _ _ _ @ mm 1 h).
    + hnf. apply J_2_swap.
    + exact T_FSMG.
  Defined.

  Definition J_alpha
    : forall l1 l2 l3 : slist X,
      alpha (J_fun l1) (J_fun l2) (J_fun l3) @ (ap011 m 1 (J_2 l2 l3) @ J_2 l1 (l2 ++ l3))
      = (mm (J_2 l1 l2) 1 @ J_2 (l1 ++ l2) l3) @ ap J_fun (alpha_slist l1 l2 l3).
  Proof.
    intros l1 l2 l3; revert l1; srapply @slist_ind_to_2paths_in_gpd; hnf.
    + exact T_FSMG.
    + simpl.
      change (alpha (J_fun nil) (J_fun l2) (J_fun l3) @ (ap011 m 1 (J_2 l2 l3) @ lambda (J_fun (l2 ++ l3))) = (mm (lambda (J_fun l2)) 1 @ J_2 l2 l3) @ 1).
      refine (_ @ (concat_p1 _)^).
      refine (whiskerL _ (lambda_FSMG_natural _)^ @ concat_p_pp _ _ _ @ _); apply whiskerR.
      apply alpha_lambda_FSMG.
    + intros x l1 h.
      change (alpha (J_fun (x :: l1)) (J_fun l2) (J_fun l3) @ (ap011 m (1 @ 1) (J_2 l2 l3) @ (alpha (iota x) (J_fun l1) (J_fun (l2 ++ l3)) @ mm 1 (J_2 l1 (l2 ++ l3)))) = (mm (alpha (iota x) (J_fun l1) (J_fun l2) @ mm 1 (J_2 l1 l2)) (1 @ 1) @ (alpha (iota x) (J_fun (l1 ++ l2)) (J_fun l3) @ mm 1 (J_2 (l1 ++ l2) l3))) @ ap J_fun (ap (cons x) (alpha_slist l1 l2 l3))).
      refine (whiskerL _ (concat_p_pp _ _ _ @ whiskerR (alpha_FSMG_natural 1 1 _)^ _ @ concat_pp_p _ _ _) @ concat_p_pp _ _ _ @ _).
      refine (whiskerR (pentagon _ _ _ _) _ @ _);
      repeat rewrite concat_pp_p;
      refine (_ @ concat_p_pp _ _ _ @ whiskerR (ap011_pqpq m _ _ 1 1) _);
      apply whiskerL.
      refine (whiskerL _ (whiskerL _ (ap011_pqpq m 1 1 _ _) @ (ap011_pqpq m 1 1 _ _) @ ap011 mm (idpath idpath) h @ (ap011_pqpq m 1 1 _ _)^ @ whiskerR (ap011_pqpq m 1 1 _ _)^ _) @ _);
      repeat rewrite concat_pp_p.
      refine (concat_p_pp _ _ _ @ whiskerR (alpha_FSMG_natural 1 _ 1) _ @ concat_pp_p _ _ _ @ _);
      apply whiskerL; apply whiskerL; apply whiskerL.
      exact (ap_J_ap_cons x (alpha_slist _ _ _))^.
  Qed.

  Definition J_lambda
    : forall l : slist X,
      lambda (J_fun l) = (ap011 m 1 1 @ J_2 nil l) @ idpath.
  Proof.
    intro l2; simpl.
    exact ((concat_1p _)^ @ (concat_p1 _)^).
  Qed.

  Definition J_rho
    : forall l : slist X,
    rho (J_fun l) = (ap011 m 1 1 @ J_2 l nil) @ ap J_fun (rho_slist l).
  Proof.
    srapply @slist_ind_to_2paths_in_gpd; hnf.
    + exact T_FSMG.
    + simpl. refine (_ @ (concat_1p _)^ @ (concat_p1 _)^).
      change (rho (J_fun nil) = lambda (J_fun nil)).
      exact (lambda_rho_FSMG_e)^.
    + intros x l h.
      change (rho (m (iota x) (J_fun l)) = (ap011 m 1 1 @ (alpha _ _ _ @ mm 1 (J_2 _ _))) @ ap J_fun (ap (cons x) (rho_slist l))).
      refine ((alpha_rho_FSMG (iota x) (J_fun l))^ @ _ @ concat_p_pp _ _ _ @ (concat_1p _)^ @ concat_p_pp _ _ _); apply whiskerL.
      refine (ap011 mm 1 h @ (ap011_pqpq m 1 1 _ _)^ @ whiskerR (ap011_pqpq m 1 1 _ _)^ _ @ concat_pp_p _ _ _ @ concat_1p _ @ _); apply whiskerL.
      exact (ap_J_ap_cons x (rho_slist l))^.
  Qed.

  Definition J_tau_V (x : X) (l1 : slist X)
    : forall l2 : slist X,
      alpha (J_fun l2) (iota x) (J_fun l1) @ J_2 l2 (x :: l1)
      = ap011 m (tau (J_fun l2) (iota x)) 1 @ alpha (iota x) (J_fun l2) (J_fun l1)
      @ ap011 m 1 (J_2 l2 l1) @ ap J_fun (sapp_Q x l1 l2).
  Proof.
    srapply @slist_ind_to_2paths_in_gpd; hnf.
    + exact T_FSMG.
    + simpl. refine (_ @ (concat_p1 _)^).
      change (alpha (J_fun nil) (iota x) (J_fun l1) @ lambda (m (iota x) (J_fun l1)) = (ap011 m (tau (J_fun nil) (iota x)) 1 @ alpha (iota x) (J_fun nil) (J_fun l1)) @ ap011 m 1 (lambda (J_fun l1))).
      refine (alpha_lambda_FSMG _ _ @ _).
      refine (_ @ whiskerL _ (triangle _ _)^ @ concat_p_pp _ _ _).
      refine (ap011 mm _ (idpath idpath) @ (ap011_pqpq m _ _ 1 1)^).
      exact (tau_rho_lambda_FSMG _)^.
    + intros y l2 h.
      change (alpha (J_fun (y :: l2)) (iota x) (J_fun l1) @ (alpha _ _ _ @ mm 1 (J_2 l2 (x :: l1))) = ((ap011 m (tau (J_fun (y :: l2)) (iota x)) 1 @ alpha (iota x) (J_fun (y :: l2)) (J_fun l1)) @ ap011 m 1 (alpha _ _ _ @ mm 1 (J_2 l2 l1))) @ ap J_fun (swap _ _ _ @ ap (cons y) (sapp_Q x l1 l2))).
      refine (concat_p_pp _ _ _ @ whiskerR (pentagon _ _ _ _) _ @ _).
      refine (concat_pp_p _ _ _ @ whiskerL _ (ap011_pqpq m 1 1 _ _ @ ap011 mm (idpath idpath) h @ (ap011_pqpq m 1 1 _ _)^ @ whiskerR ((ap011_pqpq m 1 1 _ _)^ @ whiskerR (ap011_pqpq m 1 1 _ _)^ _) _) @ _).
      repeat rewrite concat_p_pp.
      refine (_ @ concat_pp_p _ _ _ @ whiskerL _ (ap_pp J_fun (swap x y (l2 ++ l1)) (ap (cons y) (sapp_Q x l1 l2)))^).
      refine (concat2 _ (ap_J_ap_cons y (sapp_Q x l1 l2))^).
      repeat rewrite concat_pp_p.
      refine (whiskerL _ (concat_p_pp _ _ _ @ whiskerR (alpha_FSMG_natural 1 _ 1) _) @ _);
      repeat rewrite concat_p_pp.
      refine (whiskerL _ (moveL_Vp _ _ _ (alpha_FSMG_natural 1 1 _)) @ _);
      repeat rewrite concat_pp_p.
      refine (whiskerL _ (whiskerL _ (concat_p_pp _ _ _ @ concat_p_pp _ _ _ @ whiskerR (moveR_Vp _ _ _ (moveL_pV _ _ _ (pentagon _ _ _ _) @ concat_pp_p _ _ _ @ concat_pp_p _ _ _) @ concat_p_pp _ _ _)^ _)) @ _);
      repeat rewrite concat_p_pp.
      refine (_ @ whiskerL _ (J_fun_beta_swap x y (l2 ++ l1))^);
      repeat rewrite concat_p_pp; apply whiskerR; repeat rewrite concat_pp_p.
      refine (_ @ whiskerL _ (whiskerL _ (concat_p_pp _ _ _ @ whiskerR (ap011_pqpq m 1 1 _ _) _))).
      refine (_ @ whiskerL _ (whiskerR (moveR_Vp _ _ _ (pentagon _ _ _ _ @ concat_pp_p _ _ _)) _ @ concat_pp_p _ _ _));
      repeat rewrite concat_p_pp.
      refine (_ @ whiskerR (whiskerL _ ((moveR_pV _ _ _ (alpha_FSMG_natural 1 1 _))^ @ concat_pp_p _ _ _) @ concat_p_pp _ _ _ @ concat_p_pp _ _ _) _);
      repeat rewrite concat_p_pp.
      refine (_ @ whiskerL _ (ap011_p11q m (tau _ _) (J_2 l2 l1) @ (ap011_1qp1 m (tau _ _) (J_2 l2 l1))^) @ concat_p_pp _ _ _);
      repeat rewrite concat_p_pp; apply whiskerR.
      refine (_ @ whiskerL _ (alpha_FSMG_natural _ 1 1)^ @ concat_p_pp _ _ _);
      repeat rewrite concat_p_pp; apply whiskerR; apply moveR_pV.
      refine (cancelR _ _ (mm (mm 1 (tau _ _)) 1) _);
      repeat rewrite concat_pp_p.
      refine (_ @ whiskerL _ (whiskerL _ (whiskerR (ap011_pqpq m _ _ 1 1) _ @ ap011_pqpq m _ _ 1 1 @ ap011 mm (hexagon _ _ _ @ concat_pp_p _ _ _) (idpath idpath) @ (ap011_pqpq m _ _ 1 1)^ @ whiskerL _ (ap011_pqpq m _ _ 1 1)^))).
      refine (whiskerL _ (ap011_pqpq m _ _ 1 1 @ ap011 mm (ap011_pqpq m 1 1 _ _ @ ap011 mm (idpath idpath) (bigon _ _)) (idpath idpath)) @ concat_p1 _ @ _).
      refine (_ @ whiskerL _ (whiskerR ((concat_1p _)^ @ whiskerR (concat_Vp _)^ _ @ concat_pp_p _ _ _) _ @ concat_pp_p _ _ _)).
      refine (_ @ whiskerR (ap011 mm (bigon _ _)^ (idpath idpath) @ (ap011_pqpq m _ _ 1 1)^) _ @ concat_pp_p _ _ _).
      exact (concat_1p _)^.
  Qed.

  Definition J_tau
    : forall l1 l2 : slist X,
      tau (J_fun l1) (J_fun l2) @ J_2 l2 l1 = J_2 l1 l2 @ ap J_fun (tau_slist l1 l2).
  Proof.
    srapply @slist_ind_to_fam_2paths_in_gpd; hnf.
    + exact T_FSMG.
    + srapply @slist_ind_to_2paths_in_gpd; hnf.
      - exact T_FSMG.
      - simpl. refine (_ @ (concat_p1 _)^).
        change (tau (J_fun nil) (J_fun nil) @ lambda (J_fun nil) = lambda (J_fun nil)).
        refine (tau_lambda_rho_FSMG e @ _).
        exact (lambda_rho_FSMG_e)^.
      - intros y l2 h.
        change (tau (J_fun nil) (m (iota y) (J_fun l2)) @ (alpha _ _ _ @ mm 1 (J_2 _ _)) =
lambda (J_fun (y :: l2)) @ ap J_fun (ap (cons y) (tau_slist nil l2))).
        refine (cancelL (alpha (J_fun nil) _ _) _ _ _);
        repeat rewrite concat_p_pp;
        refine (whiskerR (hexagon _ _ _) _ @ _).
        refine (_ @ whiskerR (alpha_lambda_FSMG _ _)^ _).
        repeat rewrite concat_pp_p.
        refine (whiskerL _ (whiskerL _ (ap011_pqpq m 1 1 _ _ @ ap011 mm (idpath idpath) h @ (ap011_pqpq m 1 1 _ _)^)) @ _).
        refine (_ @ whiskerL _ (ap_J_ap_cons y (tau_slist nil l2))^).
        refine (_ @ concat_p_pp _ _ _ @ whiskerR (ap011_pqpq m _ _ 1 1 @ ap011 mm (tau_rho_lambda_FSMG _) (idpath idpath)) _); apply whiskerL.
        refine (concat_p_pp _ _ _ @ _); apply whiskerR.
        exact (triangle _ _).
    + intros x l1 hl1 l2.
      change (tau (J_fun (x :: l1)) (J_fun l2) @ J_2 l2 (x :: l1) = (alpha _ _ _ @ mm 1 (J_2 _ _)) @ ap J_fun (ap (cons x) (tau_slist _ _) @ sapp_Q x l1 l2)).
      refine (_ @ concat_pp_p _ _ _ @ whiskerL _ (ap_pp J_fun _ _)^).
      refine (_ @ whiskerR (whiskerL _ (ap011_pqpq m 1 1 _ _ @ ap011 mm (idpath idpath) (hl1 l2) @ (ap011_pqpq m 1 1 _ _)^) @ concat_p_pp _ _ _ @ whiskerL _ (ap_J_ap_cons x (tau_slist l1 l2))^) _).
      refine (whiskerR (bigon_var_FSMG _ _)^ _ @ _); apply moveR_Vp.
      refine (cancelL (alpha _ _ _) _ _ _).
      refine (_ @ whiskerR (hexagon _ _ _)^ _ @ concat_pp_p _ _ _ @ whiskerL _ (concat_p_pp _ _ _) @ concat_pp_p _ _ _).
      repeat rewrite concat_p_pp.
      refine (_ @ whiskerR (whiskerR ((concat_p1 _)^ @ whiskerL _ (ap011 mm (idpath idpath) (bigon _ _)^ @ (ap011_pqpq m 1 1 _ _)^) @ concat_p_pp _ _ _) _) _);
      repeat rewrite concat_p_pp.
      apply J_tau_V.
    Qed.

Definition J
  : SymMonoidalFunctor (slistSMG X) (FSMG_SMG X)
  := @Build_SymMonoidalFunctor (slistSMG X) (FSMG_SMG X) J_fun idpath J_2 J_alpha J_lambda J_rho J_tau.

Lemma epsilon_homotopy_alpha (a b c : FSMG X)
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
  exact (alpha_FSMG_natural a' b' c')^.
Defined.

Lemma epsilon_homotopy_lambda (b : FSMG X) (b' : b = J_fun (K_fun b))
  : (mm 1 b' @ J_2 (K_fun e) (K_fun b)) @ ap (fun w : FSMG X => J_fun (K_fun w)) (lambda b)
    = ap idmap (lambda b) @ b'.
Proof.
  refine (whiskerL _ (ap_compose K_fun J_fun _ @ ap (ap J_fun) (K_fun_beta_lambda b)) @ concat_p1 _ @ _).
  refine (_ @ whiskerR (ap_idmap _)^ _).
  exact (lambda_FSMG_natural b')^.
Defined.

Lemma epsilon_homotopy_rho (a : FSMG X) (a' : a = J_fun (K_fun a))
  : (mm a' 1 @ J_2 (K_fun a) (K_fun e)) @ ap (fun w : FSMG X => J_fun (K_fun w)) (rho a)
    = ap idmap (rho a) @ a'.
Proof.
  refine (whiskerL _ (ap_compose K_fun J_fun _ @ ap (ap J_fun) (K_fun_beta_rho a)) @ _).
  refine (concat_pp_p _ _ _ @ whiskerL _ (whiskerR (concat_1p _)^ _ @ (J_rho (K_fun a))^) @ _).
  refine (_ @ whiskerR (ap_idmap _)^ _).
  exact (rho_FSMG_natural a')^.
Defined.

Lemma epsilon_homotopy_tau (a b : FSMG X)
  (a' : a = J_fun (K_fun a)) (b' : b = J_fun (K_fun b))
  : (mm a' b' @ J_2 (K_fun a) (K_fun b)) @ ap (fun x : FSMG X => J_fun (K_fun x)) (tau a b)
    = ap idmap (tau a b) @ (mm b' a' @ J_2 (K_fun b) (K_fun a)).
Proof.
  refine (whiskerL _ (ap_compose K_fun J_fun _ @ ap (ap J_fun) (K_fun_beta_tau a b)) @ _).
  refine (concat_pp_p _ _ _ @ whiskerL _ (J_tau (K_fun a) (K_fun b))^ @ concat_p_pp _ _ _ @ _ @ concat_pp_p _ _ _); apply whiskerR.
  refine (_ @ whiskerR (ap_idmap _)^ _).
  exact (tau_FSMG_natural a' b')^.
Defined.

Lemma epsilon_homotopy (* unit of the adjunction *)
  : (fun a : FSMG X => a) == J o K.
Proof.
  srapply FSMG_ind_to_paths_in_gpd; simpl.
  + constructor.
  + intros; exact (rho _)^.
  + intros ?? IHa IHb;
    change (m a b = J_fun (sapp (K_fun a) (K_fun b))).
    refine (mm IHa IHb @ _).
    apply J_2.
  + exact epsilon_homotopy_alpha.
  + exact epsilon_homotopy_lambda.
  + exact epsilon_homotopy_rho.
  + exact epsilon_homotopy_tau. (* uses J_tau, which uses all coherence diagrams! *)
  + exact T_FSMG.
Defined.

Definition epsilon
  : SymMonoidalNatIso (SymMonoidalFunctor_id _) (SymMonoidalFunctor_comp J K).
Proof.
  srapply @Build_SymMonoidalNatIso.
  + exact epsilon_homotopy.
  + constructor.
  + intros; unfold smg_f2; simpl.
    change (idpath @ (mm (epsilon_homotopy a) (epsilon_homotopy b) @ J_2 (K_fun a) (K_fun b)) = mm (epsilon_homotopy a) (epsilon_homotopy b) @ (J_2 (K_fun a) (K_fun b) @ 1)).
    exact (concat_1p _ @ whiskerL _ (concat_p1 _)^).
Defined.

Lemma ap_cons_ap_K {a b : FSMG X} (x : X)
  (p : a = b)
  : ap K (mm (idpath (iota x)) p) = ap (cons x) (ap K p).
Proof.
  induction p; constructor.
Defined.

Lemma ap_K_mm_p_1 {a b c : FSMG X} (p : a = b)
  : ap K (mm p (idpath c)) = ap011 sapp (ap K p) (idpath (K c)).
Proof.
  induction p; constructor.
Defined.

  Lemma eta_homotopy_swap
    : forall (x y : X) (l : slist X) (h : K (J l) = l),
      ap (cons x) (ap (cons y) h) @ ap idmap (swap x y l)
      = ap (fun w : slist X => K (J w)) (swap x y l) @ ap (cons y) (ap (cons x) h).
  Proof.
    intros.
    refine (whiskerL _ (ap_idmap _) @ _).
    refine ((swap_natural x y h)^ @ _); apply whiskerR.
    symmetry.
    refine (ap_compose J K (swap x y l) @ _); simpl.
    refine (ap (ap K_fun) (J_fun_beta_swap x y l) @ _).
    refine (ap_pp _ _ _ @ whiskerR (ap_pp _ _ _) _ @ whiskerR (whiskerR (ap_V _ _) _) _ @ _).
    refine (concat2 (concat2 (ap inverse (K_fun_beta_alpha _ _ _)) idpath) (K_fun_beta_alpha _ _ _) @ _).
    refine (concat_p1 _ @ concat_1p _ @ _).
    refine (ap_K_mm_p_1 (tau (iota x) (iota y)) @ _).
    refine (ap011_p1 sapp (ap K (tau (iota x) (iota y))) @ _).
    refine (ap (ap (fun z : slist X => z ++ K_fun (J_fun l))) (K_fun_beta_tau _ _) @ _).
    change (ap (fun z : slist X => z ++ K_fun (J_fun l)) (ap (cons x) (tau_slist nil (y :: nil)) @ (swap x y nil @ ap (cons y) (sapp_Q x nil nil))) = swap x y (K_fun (J_fun l))); simpl.
    refine (ap (ap (fun z : slist X => z ++ K_fun (J_fun l))) (concat_1p _ @ concat_p1 _) @ _).
    exact (sapp_blank_beta_swap x y nil (K (J l))).
  Qed.

Definition eta_homotopy (* counit *)
  : forall l : slist X,
    K (J l) = l.
Proof.
  srapply @slist_ind_to_paths_in_gpd; hnf.
  + constructor.
  + intros x l h.
    change (x :: K (J l) = x :: l).
    exact (ap (cons x) h).
  + hnf. apply eta_homotopy_swap.
  + srapply T_slist.
Defined.

  Lemma eta_cons (l2 : slistSMG X)
    : forall (x : X) (l : slist X),
    ap K_fun (J_2 l l2) @ eta_homotopy (l ++ l2) = ap011 sapp (eta_homotopy l) (eta_homotopy l2) ->
    ap K_fun (J_2 (x :: l) l2) @ eta_homotopy ((x :: l) ++ l2) = ap011 sapp (eta_homotopy (x :: l)) (eta_homotopy l2).
  Proof.
    intros x l1 h.
    refine (whiskerR (ap_pp K_fun (alpha (iota x) (J_fun l1) (J_fun l2)) (mm 1 (J_2 l1 l2))) _ @ _).
    refine (whiskerR (@concat2 _ _ _ _ (ap K_fun (alpha (iota x) (J_fun l1) (J_fun l2))) _ (ap K_fun (mm 1 (J_2 l1 l2))) (ap (cons x) (ap K (J_2 l1 l2))) (K_fun_beta_alpha _ _ _) (ap_cons_ap_K x (J_2 l1 l2)) @ concat_1p _) _ @ _).
    change (ap (cons x) (ap K (J_2 l1 l2)) @ ap (cons x) (eta_homotopy (l1 ++ l2)) = ap011 sapp (ap (cons x) (eta_homotopy l1)) (eta_homotopy l2)).
    refine ((ap_pp (cons x) _ _)^ @ _ @ (ap011_sapp_ap_cons x _ _)^).
    change (ap (cons x) (ap K_fun (J_2 l1 l2) @ eta_homotopy (l1 ++ l2)) = ap (cons x) (ap011 sapp (eta_homotopy l1) (eta_homotopy l2))).
    apply ap; exact h.
  Qed.

Definition eta
  : SymMonoidalNatIso (SymMonoidalFunctor_comp K J) (SymMonoidalFunctor_id _).
Proof.
  srapply @Build_SymMonoidalNatIso.
  + exact eta_homotopy.
  + constructor.
  + intros l1 l2; unfold smg_f2; simpl.
    refine (whiskerR (concat_1p _) _ @ _ @ (concat_p1 _)^).
    revert l1; srapply @slist_ind_to_2paths_in_gpd; hnf.
    - srapply T_slist.
    - refine (whiskerR (K_fun_beta_lambda _) _ @ concat_1p _ @ _).
      change (eta_homotopy l2 = ap011 sapp (idpath nil) (eta_homotopy l2)).
      generalize (eta_homotopy l2); induction p; constructor.
    - exact (eta_cons l2).
Defined.

Proposition equiv_FSMG_slist : FSMG X <~> slist X.
Proof.
  exact (equiv_adjointify K J eta_homotopy (fun x => (epsilon_homotopy x)^)).
Defined.

End Coherence.