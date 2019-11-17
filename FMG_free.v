Require Export FMG.

Section Free.

Definition FMG_functor_fun {X Y : Type} {T_X : IsHSet X} {T_Y : IsHSet Y}
  (h : X -> Y)
  : FMG X -> FMG Y
  := FMG_rec X (FMG Y) e (iota o h) m alpha lambda rho pentagon triangle T_FMG.

Definition FMG_functor_fun_alpha {X Y : Type} {T_X : IsHSet X} {T_Y : IsHSet Y}
  (h : X -> Y) (a b c : FMG X)
  : ap (FMG_functor_fun h) (alpha a b c) = alpha (FMG_functor_fun h a) (FMG_functor_fun h b) (FMG_functor_fun h c)
  := @FMG_rec_beta_alpha X (FMG Y) e (iota o h) m alpha lambda rho pentagon triangle T_FMG a b c.
Definition FMG_functor_fun_lambda {X Y : Type} {T_X : IsHSet X} {T_Y : IsHSet Y}
  (h : X -> Y) (b : FMG X)
  : ap (FMG_functor_fun h) (lambda b) = lambda (FMG_functor_fun h b)
  := @FMG_rec_beta_lambda X (FMG Y) e (iota o h) m alpha lambda rho pentagon triangle T_FMG b.
Definition FMG_functor_fun_rho {X Y : Type} {T_X : IsHSet X} {T_Y : IsHSet Y}
  (h : X -> Y) (a : FMG X)
  : ap (FMG_functor_fun h) (rho a) = rho (FMG_functor_fun h a)
  := @FMG_rec_beta_rho X (FMG Y) e (iota o h) m alpha lambda rho pentagon triangle T_FMG a.

Definition FMG_functor_arr
  : forall (X Y : Type) (T_X : IsHSet X) (T_Y : IsHSet Y), (X -> Y) -> MonoidalFunctor (FMG_MG X) (FMG_MG Y).
Proof.
  intros ???? h.
  srapply @Build_MonoidalFunctor.
  + exact (FMG_functor_fun h).
  + constructor.
  + constructor.
  + intros; simpl.
    refine (concat_p1 _ @ _ @ (concat_1p _)^).
    exact (FMG_functor_fun_alpha h a b c)^.
  + intros; simpl.
    refine (_ @ (concat_1p _)^).
    exact (FMG_functor_fun_lambda h b)^.
  + intros; simpl.
    refine (_ @ (concat_1p _)^).
    exact (FMG_functor_fun_rho h a)^.
Defined.

Definition FMG_functor_id
  : forall (X : Type) (T_X : IsHSet X),
    MonoidalNatIso (FMG_functor_arr X X T_X T_X idmap) (MonoidalFunctor_id (FMG_MG X)).
Proof.
  intros; srapply @Build_MonoidalNatIso; simpl.
  + unfold pointwise_paths. srapply @FMG_ind_to_paths_in_gpd; simpl.
    - constructor.
    - constructor.
    - intros ?? IHa IHb.
      exact (mm IHa IHb).
    - intros ??? IHa IHb IHc; simpl.
      refine (whiskerL _ (ap_idmap _) @ _ @ whiskerR (FMG_functor_fun_alpha idmap a b c)^ _).
      exact (@alpha_natural (FMG_MG X) _ _ _ _ _ _ IHa IHb IHc)^.
    - intros ? IHb; simpl.
      refine (whiskerL _ (ap_idmap _) @ _ @ whiskerR (FMG_functor_fun_lambda idmap b)^ _).
      exact (@lambda_natural (FMG_MG X) _ _ IHb)^.
    - intros ? IHa; simpl.
      refine (whiskerL _ (ap_idmap _) @ _ @ whiskerR (FMG_functor_fun_rho idmap a)^ _).
      exact (@rho_natural (FMG_MG X) _ _ IHa)^.
  + constructor.
  + intros; simpl.
    refine (concat_1p _ @ (concat_p1 _)^).
Defined.

Definition FMG_functor_comp
  : forall (X Y Z : Type) (T_X : IsHSet X) (T_Y : IsHSet Y) (T_Z : IsHSet Z) (g : Y -> Z) (f : X -> Y),
    MonoidalNatIso
      (MonoidalFunctor_comp (FMG_functor_arr Y Z T_Y T_Z g) (FMG_functor_arr X Y T_X T_Y f))
      (FMG_functor_arr X Z T_X T_Z (fun x : X => g (f x))).
Proof.
  intros; srapply @Build_MonoidalNatIso; simpl.
  + unfold pointwise_paths. srapply @FMG_ind_to_paths_in_gpd; simpl.
    - constructor.
    - constructor.
    - intros ?? IHa IHb.
      exact (mm IHa IHb).
    - intros ??? IHa IHb IHc; simpl.
      refine (_ @ whiskerR (ap_compose (FMG_functor_fun f) (FMG_functor_fun g) _)^ _).
      refine (whiskerL _ (FMG_functor_fun_alpha (g o f) a b c) @ _).
      refine (_ @ whiskerR ((FMG_functor_fun_alpha g _ _ _)^ @ ap (ap (FMG_functor_fun g)) (FMG_functor_fun_alpha f a b c)^) _).
      exact (@alpha_natural (FMG_MG Z) _ _ _ _ _ _ IHa IHb IHc)^.
    - intros ? IHb; simpl.
      refine (_ @ whiskerR (ap_compose (FMG_functor_fun f) (FMG_functor_fun g) _)^ _).
      refine (whiskerL _ (FMG_functor_fun_lambda (g o f) b) @ _).
      refine (_ @ whiskerR ((FMG_functor_fun_lambda g _)^ @ ap (ap (FMG_functor_fun g)) (FMG_functor_fun_lambda f b)^) _).
      exact (@lambda_natural (FMG_MG Z) _ _ IHb)^.
    - intros ? IHa; simpl.
      refine (_ @ whiskerR (ap_compose (FMG_functor_fun f) (FMG_functor_fun g) _)^ _).
      refine (whiskerL _ (FMG_functor_fun_rho (g o f) a) @ _).
      refine (_ @ whiskerR ((FMG_functor_fun_rho g _)^ @ ap (ap (FMG_functor_fun g)) (FMG_functor_fun_rho f a)^) _).
      exact (@rho_natural (FMG_MG Z) _ _ IHa)^.
  + constructor.
  + intros; simpl.
    refine (concat_1p _ @ (concat_p1 _)^).
Defined.

Definition FMG_functor
  : IsFunctor (fun X T_X => FMG_MG X).
Proof.
  srapply @Build_IsFunctor; simpl.
  + exact FMG_functor_arr.
  + exact FMG_functor_id.
  + exact FMG_functor_comp.
Defined.

Definition phi {X : Type} {T_X : IsHSet X} {M : MonoidalGroupoid}
  (F : MonoidalFunctor (FMG_MG X) M)
  : X -> M
  := @mg_f _ _ F o iota.

Lemma phi_natural_M {X : Type} {T_X : IsHSet X} {M : MonoidalGroupoid}
  (F : MonoidalFunctor (FMG_MG X) M)
  {N : MonoidalGroupoid} (H : MonoidalFunctor M N)
  : H o phi F == phi (MonoidalFunctor_comp H F).
Proof.
  constructor.
Defined.

Definition psi_fun {X : Type} {T_X : IsHSet X} {M : MonoidalGroupoid}
  (f : X -> M)
  : FMG X -> M
  := @FMG_rec X M mg_e f mg_m mg_alpha mg_lambda mg_rho mg_pentagon mg_triangle mgtrunc.

Definition psi_fun_alpha {X : Type} {T_X : IsHSet X} {M : MonoidalGroupoid}
  (f : X -> M) (a b c : FMG_MG X)
  : ap (psi_fun f) (mg_alpha a b c) = mg_alpha (psi_fun f a) (psi_fun f b) (psi_fun f c)
  := FMG_rec_beta_alpha X M mg_e f mg_m mg_alpha mg_lambda mg_rho mg_pentagon mg_triangle mgtrunc a b c.
Definition psi_fun_lambda {X : Type} {T_X : IsHSet X} {M : MonoidalGroupoid}
  (f : X -> M) (b : FMG_MG X)
  : ap (psi_fun f) (mg_lambda b) = mg_lambda (psi_fun f b)
  := FMG_rec_beta_lambda X M mg_e f mg_m mg_alpha mg_lambda mg_rho mg_pentagon mg_triangle mgtrunc b.
Definition psi_fun_rho {X : Type} {T_X : IsHSet X} {M : MonoidalGroupoid}
  (f : X -> M) (a : FMG_MG X)
  : ap (psi_fun f) (mg_rho a) = mg_rho (psi_fun f a)
  := FMG_rec_beta_rho X M mg_e f mg_m mg_alpha mg_lambda mg_rho mg_pentagon mg_triangle mgtrunc a.

Definition psi {X : Type} {T_X : IsHSet X} {M : MonoidalGroupoid}
  (f : X -> M)
  : MonoidalFunctor (FMG_MG X) M.
Proof.
  srapply @Build_MonoidalFunctor.
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
Defined.

  Lemma psi_natural_X_homotopy {X : Type} {T_X : IsHSet X} {M : MonoidalGroupoid}
    (f : X -> M)
    {Y : Type} {T_Y : IsHSet Y} (h : Y -> X)
    : MonoidalFunctor_comp (psi f) (FMG_functor_arr Y X T_Y T_X h) == psi (f o h).
  Proof.
    simpl; unfold pointwise_paths.
    srefine (FMG_ind_to_paths_in_gpd Y M (psi f o FMG_functor_fun h) (psi (f o h)) _ _ _ _ _ _ mgtrunc).
    + constructor.
    + constructor.
    + intros a b a' b'.
      change (mg_m ((psi f o FMG_functor_fun h) a) ((psi f o FMG_functor_fun h) b) = mg_m (psi (f o h) a) (psi (f o h) b)).
      exact (ap011 mg_m a' b').
    + hnf. intros.
      refine (_ @ whiskerR (ap_compose (FMG_functor_fun h) (psi f) (alpha a b c))^ _).
      refine (whiskerL _ (psi_fun_alpha (f o h) a b c) @ _).
      refine (_ @ whiskerR (ap (ap (psi f)) (FMG_functor_fun_alpha h a b c))^ _).
      refine (_ @ whiskerR (psi_fun_alpha f (FMG_functor_fun h a) (FMG_functor_fun h b) (FMG_functor_fun h c))^ _).
      exact (alpha_natural a' b' c')^.
    + intros; hnf.
      refine (_ @ whiskerR (ap_compose (FMG_functor_fun h) (psi f) (lambda b))^ _).
      refine (whiskerL _ (psi_fun_lambda (f o h) b) @ _).
      refine (_ @ whiskerR (ap (ap (psi f)) (FMG_functor_fun_lambda h b))^ _).
      refine (_ @ whiskerR (psi_fun_lambda f (FMG_functor_fun h b))^ _).
      exact (lambda_natural b')^.
    + intros; hnf.
      refine (_ @ whiskerR (ap_compose (FMG_functor_fun h) (psi f) (rho a))^ _).
      refine (whiskerL _ (psi_fun_rho (f o h) a) @ _).
      refine (_ @ whiskerR (ap (ap (psi f)) (FMG_functor_fun_rho h a))^ _).
      refine (_ @ whiskerR (psi_fun_rho f (FMG_functor_fun h a))^ _).
      exact (rho_natural a')^.
  Defined.

Lemma psi_natural_X {X : Type} {T_X : IsHSet X} {M : MonoidalGroupoid}
  (f : X -> M)
  {Y : Type} {T_Y : IsHSet Y} (h : Y -> X)
  : MonoidalNatIso (MonoidalFunctor_comp (psi f) (FMG_functor_arr Y X T_Y T_X h)) (psi (f o h)).
Proof.
  srapply @Build_MonoidalNatIso.
  + exact (psi_natural_X_homotopy f h).
  + constructor.
  + intros; simpl.
    refine (concat_1p _ @ (concat_p1 _)^).
Defined.

Lemma theta (X : Type) (T_X : IsHSet X) (M : MonoidalGroupoid)
  : phi o psi == idmap.
Proof.
  constructor.
Defined.

  Lemma chi_homotopy_alpha (X : Type) (T_X : IsHSet X) (M : MonoidalGroupoid)
    (F : MonoidalFunctor (FMG_MG X) M)
    (a b c : FMG X)
    (a' : psi_fun (phi F) a = F a)
    (b' : psi_fun (phi F) b = F b)
    (c' : psi_fun (phi F) c = F c)
    : (ap011 mg_m (ap011 mg_m a' b' @ @mg_f2 (FMG_MG X) M F a b) c' @ @mg_f2 (FMG_MG X) M F (m a b) c) @ ap F (alpha a b c)
      = ap (psi_fun (phi F)) (alpha a b c) @ (ap011 mg_m a' (ap011 mg_m b' c' @ @mg_f2 (FMG_MG X) M F b c) @ @mg_f2 (FMG_MG X) M F a (m b c)).
  Proof.
    refine (_ @ whiskerR (psi_fun_alpha (phi F) a b c)^ _).
    refine (whiskerR (whiskerR (ap011_pqp1 mg_m (ap011 mg_m a' b') (@mg_f2 (FMG_MG X) M F a b) c')^ _ @ concat_pp_p _ _ _) _ @ concat_pp_p _ _ _ @ _).
    refine (_ @ concat_pp_p _ _ _ @ whiskerL _ (concat_p_pp _ _ _ @ whiskerR (ap011_pq1q mg_m a' (ap011 mg_m b' c') (@mg_f2 (FMG_MG X) M F b c)) _)).
    refine (_ @ whiskerR (alpha_natural a' b' c')^ _).
    refine (_ @ concat_p_pp _ _ _); apply whiskerL;
    exact (@mg_dalpha _ _ F a b c)^.
  Qed.

  Lemma chi_homotopy_lambda (X : Type) (T_X : IsHSet X) (M : MonoidalGroupoid)
    (F : MonoidalFunctor (FMG_MG X) M)
    (b : FMG X)
    (b' : psi_fun (phi F) b = F b)
    : (ap011 mg_m mg_f0 b' @ @mg_f2 (FMG_MG X) M F e b) @ ap F (lambda b) = ap (psi_fun (phi F)) (lambda b) @ b'.
  Proof.
    refine (_ @ whiskerR (psi_fun_lambda (phi F) b)^ _).
    refine (concat_pp_p _ _ _ @ whiskerR (ap011_1qp1 mg_m mg_f0 b')^ _ @ _).
    refine (concat_pp_p _ _ _ @ whiskerL _ (concat_p_pp _ _ _ @ (@mg_dlambda _ _ F b)^) @ _).
    exact (lambda_natural b')^.
  Qed.

  Lemma chi_homotopy_rho (X : Type) (T_X : IsHSet X) (M : MonoidalGroupoid)
    (F : MonoidalFunctor (FMG_MG X) M)
    (a : FMG X)
    (a' : psi_fun (phi F) a = F a)
    : (ap011 mg_m a' mg_f0 @ @mg_f2 (FMG_MG X) M F a e) @ ap F (rho a) = ap (psi_fun (phi F)) (rho a) @ a'.
  Proof.
    refine (_ @ whiskerR (psi_fun_rho (phi F) a)^ _).
    refine (concat_pp_p _ _ _ @ whiskerR (ap011_p11q mg_m a' mg_f0)^ _ @ _).
    refine (concat_pp_p _ _ _ @ whiskerL _ (concat_p_pp _ _ _ @ (@mg_drho _ _ F a)^) @ _).
    exact (rho_natural a')^.
  Qed.

  Lemma chi_homotopy (X : Type) (T_X : IsHSet X) (M : MonoidalGroupoid)
    (F : MonoidalFunctor (FMG_MG X) M)
    : psi (phi F) == F.
  Proof.
    simpl; unfold pointwise_paths.
    srefine (@FMG_ind_to_paths_in_gpd X M (psi_fun (phi F)) F _ _ _ _ _ _ mgtrunc).
    + change (mg_e = F e). exact mg_f0.
    + constructor.
    + intros a b a' b'. change (mg_m (psi_fun (phi F) a) (psi_fun (phi F) b) = F (m a b)).
      exact (ap011 mg_m a' b' @ @mg_f2 (FMG_MG X) M F a b).
    + intros; hnf.
      exact (chi_homotopy_alpha X T_X M F a b c a' b' c').
    + intros; hnf.
      exact (chi_homotopy_lambda X T_X M F b b').
    + intros; hnf.
      exact (chi_homotopy_rho X T_X M F a a').
  Defined.

Lemma chi (X : Type) (T_X : IsHSet X) (M : MonoidalGroupoid)
  (F : MonoidalFunctor (FMG_MG X) M)
  : MonoidalNatIso (psi (phi F)) F.
Proof.
  srapply @Build_MonoidalNatIso.
  + apply chi_homotopy.
  + simpl. exact (concat_1p _).
  + intros; simpl. exact (concat_1p _).
Defined.


Lemma FMG_FreeFunctor
  : IsFreeFunctor (fun X T_X => FMG_MG X).
Proof.
  srapply @Build_IsFreeFunctor.
  + exact FMG_functor.
  + apply @phi.
  + apply @phi_natural_M.
  + apply @psi.
  + apply @psi_natural_X.
  + apply @theta.
  + apply @chi.
Defined.

End Free.
