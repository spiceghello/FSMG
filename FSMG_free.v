Require Export FSMG.

Section Free.

Definition FSMG_functor_fun {X Y : Type} {T_X : IsHSet X} {T_Y : IsHSet Y}
  (h : X -> Y)
  : FSMG X -> FSMG Y
  := FSMG_rec X (FSMG Y) e (iota o h) m alpha lambda rho tau pentagon triangle hexagon bigon T_FSMG.

Definition FSMG_functor_fun_alpha {X Y : Type} {T_X : IsHSet X} {T_Y : IsHSet Y}
  (h : X -> Y) (a b c : FSMG X)
  : ap (FSMG_functor_fun h) (alpha a b c) = alpha (FSMG_functor_fun h a) (FSMG_functor_fun h b) (FSMG_functor_fun h c)
  := @FSMG_rec_beta_alpha X (FSMG Y) e (iota o h) m alpha lambda rho tau pentagon triangle hexagon bigon T_FSMG a b c.
Definition FSMG_functor_fun_lambda {X Y : Type} {T_X : IsHSet X} {T_Y : IsHSet Y}
  (h : X -> Y) (b : FSMG X)
  : ap (FSMG_functor_fun h) (lambda b) = lambda (FSMG_functor_fun h b)
  := @FSMG_rec_beta_lambda X (FSMG Y) e (iota o h) m alpha lambda rho tau pentagon triangle hexagon bigon T_FSMG b.
Definition FSMG_functor_fun_rho {X Y : Type} {T_X : IsHSet X} {T_Y : IsHSet Y}
  (h : X -> Y) (a : FSMG X)
  : ap (FSMG_functor_fun h) (rho a) = rho (FSMG_functor_fun h a)
  := @FSMG_rec_beta_rho X (FSMG Y) e (iota o h) m alpha lambda rho tau pentagon triangle hexagon bigon T_FSMG a.
Definition FSMG_functor_fun_tau {X Y : Type} {T_X : IsHSet X} {T_Y : IsHSet Y}
  (h : X -> Y) (a b : FSMG X)
  : ap (FSMG_functor_fun h) (tau a b) = tau (FSMG_functor_fun h a) (FSMG_functor_fun h b)
  := @FSMG_rec_beta_tau X (FSMG Y) e (iota o h) m alpha lambda rho tau pentagon triangle hexagon bigon T_FSMG a b.

Definition FSMG_functor_arr
  : forall (X Y : Type) (T_X : IsHSet X) (T_Y : IsHSet Y), (X -> Y) -> SymMonoidalFunctor (FSMG_SMG X) (FSMG_SMG Y).
Proof.
  intros ???? h.
  srapply @Build_SymMonoidalFunctor.
  + exact (FSMG_functor_fun h).
  + constructor.
  + constructor.
  + intros; simpl.
    refine (concat_p1 _ @ _ @ (concat_1p _)^).
    exact (FSMG_functor_fun_alpha h a b c)^.
  + intros; simpl.
    refine (_ @ (concat_1p _)^).
    exact (FSMG_functor_fun_lambda h b)^.
  + intros; simpl.
    refine (_ @ (concat_1p _)^).
    exact (FSMG_functor_fun_rho h a)^.
  + intros; simpl.
    refine (concat_p1 _ @ _ @ (concat_1p _)^).
    exact (FSMG_functor_fun_tau h a b)^.
Defined.

Definition FSMG_functor_id
  : forall (X : Type) (T_X : IsHSet X),
    SymMonoidalNatIso (FSMG_functor_arr X X T_X T_X idmap) (SymMonoidalFunctor_id (FSMG_SMG X)).
Proof.
  intros; srapply @Build_SymMonoidalNatIso; simpl.
  + unfold pointwise_paths. srapply @FSMG_ind_to_paths_in_gpd; simpl.
    - constructor.
    - constructor.
    - intros ?? IHa IHb.
      exact (mm IHa IHb).
    - intros ??? IHa IHb IHc; simpl.
      refine (whiskerL _ (ap_idmap _) @ _ @ whiskerR (FSMG_functor_fun_alpha idmap a b c)^ _).
      exact (@alpha_natural (FSMG_SMG X) _ _ _ _ _ _ IHa IHb IHc)^.
    - intros ? IHb; simpl.
      refine (whiskerL _ (ap_idmap _) @ _ @ whiskerR (FSMG_functor_fun_lambda idmap b)^ _).
      exact (@lambda_natural (FSMG_SMG X) _ _ IHb)^.
    - intros ? IHa; simpl.
      refine (whiskerL _ (ap_idmap _) @ _ @ whiskerR (FSMG_functor_fun_rho idmap a)^ _).
      exact (@rho_natural (FSMG_SMG X) _ _ IHa)^.
    - intros ?? IHa IHb; simpl.
      refine (whiskerL _ (ap_idmap _) @ _ @ whiskerR (FSMG_functor_fun_tau idmap a b)^ _).
      exact (@tau_natural (FSMG_SMG X) _ _ _ _ IHa IHb)^.
  + constructor.
  + intros; simpl.
    refine (concat_1p _ @ (concat_p1 _)^).
Defined.

Definition FSMG_functor_comp
  : forall (X Y Z : Type) (T_X : IsHSet X) (T_Y : IsHSet Y) (T_Z : IsHSet Z) (g : Y -> Z) (f : X -> Y),
    SymMonoidalNatIso
      (SymMonoidalFunctor_comp (FSMG_functor_arr Y Z T_Y T_Z g) (FSMG_functor_arr X Y T_X T_Y f))
      (FSMG_functor_arr X Z T_X T_Z (fun x : X => g (f x))).
Proof.
  intros; srapply @Build_SymMonoidalNatIso; simpl.
  + unfold pointwise_paths. srapply @FSMG_ind_to_paths_in_gpd; simpl.
    - constructor.
    - constructor.
    - intros ?? IHa IHb.
      exact (mm IHa IHb).
    - intros ??? IHa IHb IHc; simpl.
      refine (_ @ whiskerR (ap_compose (FSMG_functor_fun f) (FSMG_functor_fun g) _)^ _).
      refine (whiskerL _ (FSMG_functor_fun_alpha (g o f) a b c) @ _).
      refine (_ @ whiskerR ((FSMG_functor_fun_alpha g _ _ _)^ @ ap (ap (FSMG_functor_fun g)) (FSMG_functor_fun_alpha f a b c)^) _).
      exact (@alpha_natural (FSMG_SMG Z) _ _ _ _ _ _ IHa IHb IHc)^.
    - intros ? IHb; simpl.
      refine (_ @ whiskerR (ap_compose (FSMG_functor_fun f) (FSMG_functor_fun g) _)^ _).
      refine (whiskerL _ (FSMG_functor_fun_lambda (g o f) b) @ _).
      refine (_ @ whiskerR ((FSMG_functor_fun_lambda g _)^ @ ap (ap (FSMG_functor_fun g)) (FSMG_functor_fun_lambda f b)^) _).
      exact (@lambda_natural (FSMG_SMG Z) _ _ IHb)^.
    - intros ? IHa; simpl.
      refine (_ @ whiskerR (ap_compose (FSMG_functor_fun f) (FSMG_functor_fun g) _)^ _).
      refine (whiskerL _ (FSMG_functor_fun_rho (g o f) a) @ _).
      refine (_ @ whiskerR ((FSMG_functor_fun_rho g _)^ @ ap (ap (FSMG_functor_fun g)) (FSMG_functor_fun_rho f a)^) _).
      exact (@rho_natural (FSMG_SMG Z) _ _ IHa)^.
    - intros ?? IHa IHb; simpl.
      refine (_ @ whiskerR (ap_compose (FSMG_functor_fun f) (FSMG_functor_fun g) _)^ _).
      refine (whiskerL _ (FSMG_functor_fun_tau (g o f) a b) @ _).
      refine (_ @ whiskerR ((FSMG_functor_fun_tau g _ _)^ @ ap (ap (FSMG_functor_fun g)) (FSMG_functor_fun_tau f a b )^) _).
      exact (@tau_natural (FSMG_SMG Z) _ _ _ _ IHa IHb)^.
  + constructor.
  + intros; simpl.
    refine (concat_1p _ @ (concat_p1 _)^).
Defined.

Definition FSMG_functor
  : IsFunctor_Sym (fun X T_X => FSMG_SMG X).
Proof.
  srapply @Build_IsFunctor_Sym; simpl.
  + exact FSMG_functor_arr.
  + exact FSMG_functor_id.
  + exact FSMG_functor_comp.
Defined.

Definition phi {X : Type} {T_X : IsHSet X} {M : SymMonoidalGroupoid}
  (F : SymMonoidalFunctor (FSMG_SMG X) M)
  : X -> M
  := @smg_f _ _ F o iota.

Lemma phi_natural_M {X : Type} {T_X : IsHSet X} {M : SymMonoidalGroupoid}
  (F : SymMonoidalFunctor (FSMG_SMG X) M)
  {N : SymMonoidalGroupoid} (H : SymMonoidalFunctor M N)
  : H o phi F == phi (SymMonoidalFunctor_comp H F).
Proof.
  constructor.
Defined.

Definition psi_fun {X : Type} {T_X : IsHSet X} {M : SymMonoidalGroupoid}
  (f : X -> M)
  : FSMG X -> M
  := @FSMG_rec X M smg_e f smg_m smg_alpha smg_lambda smg_rho smg_tau smg_pentagon smg_triangle smg_hexagon smg_bigon smgtrunc.

Definition psi_fun_alpha {X : Type} {T_X : IsHSet X} {M : SymMonoidalGroupoid}
  (f : X -> M) (a b c : FSMG_SMG X)
  : ap (psi_fun f) (smg_alpha a b c) = smg_alpha (psi_fun f a) (psi_fun f b) (psi_fun f c)
  := FSMG_rec_beta_alpha X M smg_e f smg_m smg_alpha smg_lambda smg_rho smg_tau smg_pentagon smg_triangle smg_hexagon smg_bigon smgtrunc a b c.
Definition psi_fun_lambda {X : Type} {T_X : IsHSet X} {M : SymMonoidalGroupoid}
  (f : X -> M) (b : FSMG_SMG X)
  : ap (psi_fun f) (smg_lambda b) = smg_lambda (psi_fun f b)
  := FSMG_rec_beta_lambda X M smg_e f smg_m smg_alpha smg_lambda smg_rho smg_tau smg_pentagon smg_triangle smg_hexagon smg_bigon smgtrunc b.
Definition psi_fun_rho {X : Type} {T_X : IsHSet X} {M : SymMonoidalGroupoid}
  (f : X -> M) (a : FSMG_SMG X)
  : ap (psi_fun f) (smg_rho a) = smg_rho (psi_fun f a)
  := FSMG_rec_beta_rho X M smg_e f smg_m smg_alpha smg_lambda smg_rho smg_tau smg_pentagon smg_triangle smg_hexagon smg_bigon smgtrunc a.
Definition psi_fun_tau {X : Type} {T_X : IsHSet X} {M : SymMonoidalGroupoid}
  (f : X -> M) (a b : FSMG_SMG X)
  : ap (psi_fun f) (smg_tau a b) = smg_tau (psi_fun f a) (psi_fun f b)
  := FSMG_rec_beta_tau X M smg_e f smg_m smg_alpha smg_lambda smg_rho smg_tau smg_pentagon smg_triangle smg_hexagon smg_bigon smgtrunc a b.

Definition psi {X : Type} {T_X : IsHSet X} {M : SymMonoidalGroupoid}
  (f : X -> M)
  : SymMonoidalFunctor (FSMG_SMG X) M.
Proof.
  srapply @Build_SymMonoidalFunctor.
  + simpl. exact (psi_fun f).
  + constructor.
  + constructor.
  + intros; simpl.
    refine (concat_p1 _ @ _^ @ (concat_1p _)^).
    exact (psi_fun_alpha f a b c).
  + intros; simpl.
    refine (_^ @ (concat_1p _)^).
    exact (psi_fun_lambda f b).
  + intros; simpl.
    refine (_^ @ (concat_1p _)^).
    exact (psi_fun_rho f a).
  + intros; simpl.
    refine (concat_p1 _ @ _^ @ (concat_1p _)^).
    exact (psi_fun_tau f a b).
Defined.

  Lemma psi_natural_X_homotopy {X : Type} {T_X : IsHSet X} {M : SymMonoidalGroupoid}
    (f : X -> M)
    {Y : Type} {T_Y : IsHSet Y} (h : Y -> X)
    : SymMonoidalFunctor_comp (psi f) (FSMG_functor_arr Y X T_Y T_X h) == psi (f o h).
  Proof.
    simpl; unfold pointwise_paths.
    srefine (@FSMG_ind_to_paths_in_gpd Y M (psi f o FSMG_functor_fun h) (psi (f o h)) _ _ _ _ _ _ _ (@smgtrunc M)).
    + constructor.
    + constructor.
    + intros a b a' b'.
      change (smg_m ((psi f o FSMG_functor_fun h) a) ((psi f o FSMG_functor_fun h) b) = smg_m (psi (f o h) a) (psi (f o h) b)).
      exact (ap011 smg_m a' b').
    + hnf. intros.
      refine (_ @ whiskerR (ap_compose (FSMG_functor_fun h) (psi f) (alpha a b c))^ _).
      refine (whiskerL _ (psi_fun_alpha (f o h) a b c) @ _).
      refine (_ @ whiskerR (ap (ap (psi f)) (FSMG_functor_fun_alpha h a b c))^ _).
      refine (_ @ whiskerR (psi_fun_alpha f (FSMG_functor_fun h a) (FSMG_functor_fun h b) (FSMG_functor_fun h c))^ _).
      exact (alpha_natural a' b' c')^.
    + intros; hnf.
      refine (_ @ whiskerR (ap_compose (FSMG_functor_fun h) (psi f) (lambda b))^ _).
      refine (whiskerL _ (psi_fun_lambda (f o h) b) @ _).
      refine (_ @ whiskerR (ap (ap (psi f)) (FSMG_functor_fun_lambda h b))^ _).
      refine (_ @ whiskerR (psi_fun_lambda f (FSMG_functor_fun h b))^ _).
      exact (lambda_natural b')^.
    + intros; hnf.
      refine (_ @ whiskerR (ap_compose (FSMG_functor_fun h) (psi f) (rho a))^ _).
      refine (whiskerL _ (psi_fun_rho (f o h) a) @ _).
      refine (_ @ whiskerR (ap (ap (psi f)) (FSMG_functor_fun_rho h a))^ _).
      refine (_ @ whiskerR (psi_fun_rho f (FSMG_functor_fun h a))^ _).
      exact (rho_natural a')^.
    + hnf. intros.
      refine (_ @ whiskerR (ap_compose (FSMG_functor_fun h) (psi f) (tau a b))^ _).
      refine (whiskerL _ (psi_fun_tau (f o h) a b) @ _).
      refine (_ @ whiskerR (ap (ap (psi f)) (FSMG_functor_fun_tau h a b))^ _).
      refine (_ @ whiskerR (psi_fun_tau f (FSMG_functor_fun h a) (FSMG_functor_fun h b))^ _).
      exact (tau_natural a' b')^.
  Defined.

Lemma psi_natural_X {X : Type} {T_X : IsHSet X} {M : SymMonoidalGroupoid}
  (f : X -> M)
  {Y : Type} {T_Y : IsHSet Y} (h : Y -> X)
  : SymMonoidalNatIso (SymMonoidalFunctor_comp (psi f) (FSMG_functor_arr Y X T_Y T_X h)) (psi (f o h)).
Proof.
  srapply @Build_SymMonoidalNatIso.
  + exact (psi_natural_X_homotopy f h).
  + constructor.
  + intros; simpl.
    refine (concat_1p _ @ (concat_p1 _)^).
Defined.

Lemma theta (X : Type) (T_X : IsHSet X) (M : SymMonoidalGroupoid)
  : phi o psi == idmap.
Proof.
  constructor.
Defined.

  Lemma chi_homotopy_alpha (X : Type) (T_X : IsHSet X) (M : SymMonoidalGroupoid)
    (F : SymMonoidalFunctor (FSMG_SMG X) M)
    (a b c : FSMG X)
    (a' : psi_fun (phi F) a = F a)
    (b' : psi_fun (phi F) b = F b)
    (c' : psi_fun (phi F) c = F c)
    : (ap011 smg_m (ap011 smg_m a' b' @ @smg_f2 (FSMG_SMG X) M F a b) c' @ @smg_f2 (FSMG_SMG X) M F (m a b) c) @ ap F (alpha a b c)
      = ap (psi_fun (phi F)) (alpha a b c) @ (ap011 smg_m a' (ap011 smg_m b' c' @ @smg_f2 (FSMG_SMG X) M F b c) @ @smg_f2 (FSMG_SMG X) M F a (m b c)).
  Proof.
    refine (_ @ whiskerR (psi_fun_alpha (phi F) a b c)^ _).
    refine (whiskerR (whiskerR (ap011_pqp1 smg_m (ap011 smg_m a' b') (@smg_f2 (FSMG_SMG X) M F a b) c')^ _ @ concat_pp_p _ _ _) _ @ concat_pp_p _ _ _ @ _).
    refine (_ @ concat_pp_p _ _ _ @ whiskerL _ (concat_p_pp _ _ _ @ whiskerR (ap011_pq1q smg_m a' (ap011 smg_m b' c') (@smg_f2 (FSMG_SMG X) M F b c)) _)).
    refine (_ @ whiskerR (alpha_natural a' b' c')^ _).
    refine (_ @ concat_p_pp _ _ _); apply whiskerL;
    exact (@smg_dalpha _ _ F a b c)^.
  Qed.

  Lemma chi_homotopy_lambda (X : Type) (T_X : IsHSet X) (M : SymMonoidalGroupoid)
    (F : SymMonoidalFunctor (FSMG_SMG X) M)
    (b : FSMG X)
    (b' : psi_fun (phi F) b = F b)
    : (ap011 smg_m smg_f0 b' @ @smg_f2 (FSMG_SMG X) M F e b) @ ap F (lambda b) = ap (psi_fun (phi F)) (lambda b) @ b'.
  Proof.
    refine (_ @ whiskerR (psi_fun_lambda (phi F) b)^ _).
    refine (concat_pp_p _ _ _ @ whiskerR (ap011_1qp1 smg_m smg_f0 b')^ _ @ _).
    refine (concat_pp_p _ _ _ @ whiskerL _ (concat_p_pp _ _ _ @ (@smg_dlambda _ _ F b)^) @ _).
    exact (lambda_natural b')^.
  Qed.

  Lemma chi_homotopy_rho (X : Type) (T_X : IsHSet X) (M : SymMonoidalGroupoid)
    (F : SymMonoidalFunctor (FSMG_SMG X) M)
    (a : FSMG X)
    (a' : psi_fun (phi F) a = F a)
    : (ap011 smg_m a' smg_f0 @ @smg_f2 (FSMG_SMG X) M F a e) @ ap F (rho a) = ap (psi_fun (phi F)) (rho a) @ a'.
  Proof.
    refine (_ @ whiskerR (psi_fun_rho (phi F) a)^ _).
    refine (concat_pp_p _ _ _ @ whiskerR (ap011_p11q smg_m a' smg_f0)^ _ @ _).
    refine (concat_pp_p _ _ _ @ whiskerL _ (concat_p_pp _ _ _ @ (@smg_drho _ _ F a)^) @ _).
    exact (rho_natural a')^.
  Qed.

  Lemma chi_homotopy_tau (X : Type) (T_X : IsHSet X) (M : SymMonoidalGroupoid)
    (F : SymMonoidalFunctor (FSMG_SMG X) M)
    (a b : FSMG X)
    (a' : psi_fun (phi F) a = F a)
    (b' : psi_fun (phi F) b = F b)
    : (ap011 smg_m a' b' @ @smg_f2 (FSMG_SMG X) M F a b) @ ap F (tau a b)
      = ap (psi_fun (phi F)) (tau a b) @ (ap011 smg_m b' a' @ @smg_f2 (FSMG_SMG X) M F b a).
  Proof.
    refine (_ @ whiskerR (psi_fun_tau (phi F) a b)^ _).
    refine (concat_pp_p _ _ _ @ _ @ concat_p_pp _ _ _ @ whiskerR (tau_natural a' b')^ _ @ concat_pp_p _ _ _); apply whiskerL.
    exact (@smg_dtau _ _ F a b)^.
  Defined.

  Lemma chi_homotopy (X : Type) (T_X : IsHSet X) (M : SymMonoidalGroupoid)
    (F : SymMonoidalFunctor (FSMG_SMG X) M)
    : psi (phi F) == F.
  Proof.
    simpl; unfold pointwise_paths.
    srefine (@FSMG_ind_to_paths_in_gpd X M (psi_fun (phi F)) F _ _ _ _ _ _ _ smgtrunc).
    + change (smg_e = F e). exact smg_f0.
    + constructor.
    + intros a b a' b'. change (smg_m (psi_fun (phi F) a) (psi_fun (phi F) b) = F (m a b)).
      exact (ap011 smg_m a' b' @ @smg_f2 (FSMG_SMG X) M F a b).
    + intros; hnf.
      exact (chi_homotopy_alpha X T_X M F a b c a' b' c').
    + intros; hnf.
      exact (chi_homotopy_lambda X T_X M F b b').
    + intros; hnf.
      exact (chi_homotopy_rho X T_X M F a a').
    + intros; hnf.
      exact (chi_homotopy_tau X T_X M F a b a' b').
  Defined.

Lemma chi (X : Type) (T_X : IsHSet X) (M : SymMonoidalGroupoid)
  (F : SymMonoidalFunctor (FSMG_SMG X) M)
  : SymMonoidalNatIso (psi (phi F)) F.
Proof.
  srapply @Build_SymMonoidalNatIso.
  + apply chi_homotopy.
  + simpl. exact (concat_1p _).
  + intros; simpl. exact (concat_1p _).
Defined.


Lemma FSMG_FreeFunctor
  : IsFreeFunctor_Sym (fun X T_X => FSMG_SMG X).
Proof.
  srapply @Build_IsFreeFunctor_Sym.
  + exact FSMG_functor.
  + apply @phi.
  + apply @phi_natural_M.
  + apply @psi.
  + apply @psi_natural_X.
  + apply @theta.
  + apply @chi.
Defined.

End Free.
