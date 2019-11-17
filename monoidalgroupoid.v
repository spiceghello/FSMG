Require Export path_algebra_lemmas.

Section MonoidalGroupoids.

Section MonoidalStructure.

Context {X : Type} (e : X) (m : X -> X -> X).

Definition IsAssociative : Type
  := forall a b c : X, m (m a b) c = m a (m b c).

Definition IsLeftUnital : Type
  := forall b : X, m e b = b.

Definition IsRightUnital : Type
  := forall a : X, m a e = a.

Definition IsPentagonCoherent (alpha : IsAssociative) : Type
  := forall a b c d : X,
      alpha (m a b) c d @ alpha a b (m c d)
      = ap011 m (alpha a b c) (idpath d) @ alpha a (m b c) d @ ap011 m (idpath a) (alpha b c d).

Definition IsTriangleCoherent (alpha : IsAssociative) (lambda : IsLeftUnital) (rho : IsRightUnital) : Type
  := forall a b : X,
      alpha a e b @ ap011 m (idpath a) (lambda b)
      = ap011 m (rho a) (idpath b).

End MonoidalStructure.

Class MonoidalGroupoid := {
  mgcarrier : Type;
  mgtrunc : IsTrunc 1 mgcarrier;
  mg_e : mgcarrier;
  mg_m : mgcarrier -> mgcarrier -> mgcarrier;
  mg_alpha : IsAssociative mg_m;
  mg_lambda : IsLeftUnital mg_e mg_m;
  mg_rho : IsRightUnital mg_e mg_m;
  mg_pentagon : IsPentagonCoherent mg_m mg_alpha;
  mg_triangle : IsTriangleCoherent mg_e mg_m mg_alpha mg_lambda mg_rho
  }.
Coercion mgcarrier : MonoidalGroupoid >-> Sortclass.

Definition mg_mm {M : MonoidalGroupoid} {a b a' b'} (pa : a = a') (pb : b = b')
  : mg_m a b = mg_m a' b'
  := ap011 mg_m pa pb.

Definition mg_mmm {M : MonoidalGroupoid} {a b a' b'} {pa pa' : a = a'} {pb pb' : b = b'}
  (fa : pa = pa') (fb : pb = pb')
  : mg_mm pa pb = mg_mm pa' pb'
  := ap011 mg_mm fa fb.

Section Naturality.

Context {M : MonoidalGroupoid}.

Definition alpha_natural {a b c a' b' c'} (pa : a = a') (pb : b = b') (pc : c = c')
  : mg_alpha a b c @ mg_mm pa (mg_mm pb pc) = mg_mm (mg_mm pa pb) pc @ mg_alpha a' b' c'.
Proof.
  induction pa, pb, pc.
  exact (concat_p1 _ @ (concat_1p _)^).
Defined.

Definition lambda_natural {b b'} (pb : b = b')
  : mg_lambda b @ pb = mg_mm (idpath mg_e) pb @ mg_lambda b'.
Proof.
  induction pb;
  exact (concat_p1 _ @ (concat_1p _)^).
Defined.

Definition rho_natural {a a'} (pa : a = a')
  : mg_rho a @ pa = mg_mm pa (idpath mg_e) @ mg_rho a'.
Proof.
  induction pa;
  exact (concat_p1 _ @ (concat_1p _)^).
Defined.

End Naturality.

Section DerivedCoherence.

Context {M : MonoidalGroupoid}.

Definition rho_a_e (a : M)
  : mg_rho (mg_m a mg_e) = mg_mm (mg_rho a) (idpath mg_e).
Proof.
  apply (cancelR _ _ (mg_rho a)).
  exact (rho_natural (mg_rho a)).
Defined.

Definition lambda_e_b (b : M)
  : mg_lambda (mg_m mg_e b) = mg_mm (idpath mg_e) (mg_lambda b).
Proof.
  apply (cancelR _ _ (mg_lambda b)).
  exact (lambda_natural (mg_lambda b)).
Defined.

Definition alpha_lambda (a b : M)
  : mg_alpha mg_e a b @ mg_lambda (mg_m a b) = mg_mm (mg_lambda a) (idpath b).
Proof.
  apply (cancelL (mg_lambda _) _ _); refine (concat_p_pp _ _ _ @ _);
    refine (whiskerR (lambda_natural (mg_alpha mg_e a b)) _ @ concat_pp_p _ _ _ @ _).
  refine (whiskerL _ (lambda_natural (mg_lambda (mg_m a b))) @ concat_p_pp _ _ _ @ _).
  refine (_ @ (lambda_natural (mg_mm (mg_lambda a) (idpath b)))^); apply whiskerR.
  apply (cancelL (mg_alpha _ _ _) _ _); refine (concat_p_pp _ _ _ @ _);
    refine (_ @ (alpha_natural (idpath mg_e) (mg_lambda a) (idpath b))^);
    refine (concat_pp_p _ _ _ @ _).
  apply (cancelL (mg_mm (mg_alpha _ _ _) idpath) _ _);
    refine (concat_p_pp _ _ _ @ concat_p_pp _ _ _ @ _ @ concat_pp_p _ _ _);
    refine (whiskerR (mg_pentagon mg_e mg_e a b)^ _ @ concat_pp_p _ _ _ @ _).
  refine (whiskerL _ (mg_triangle mg_e (mg_m a b)) @ _).
  refine (alpha_natural (mg_rho mg_e) idpath idpath @ _); apply whiskerR.
  refine (_ @ (ap011_pqpq mg_m (mg_alpha mg_e mg_e a) (mg_mm idpath (mg_lambda a)) idpath idpath)^);
    exact (mg_mmm (mg_triangle _ _)^ idpath).
Defined.

Definition alpha_rho (a b : M)
  : mg_alpha a b mg_e @ mg_mm (idpath a) (mg_rho b) = mg_rho (mg_m a b).
Proof.
  apply (cancelL (mg_rho _) _ _); refine (concat_p_pp _ _ _ @ _).
  refine (whiskerR (rho_natural (mg_alpha a b mg_e)) _ @ concat_pp_p _ _ _ @ _).
  refine (whiskerL _ (rho_natural (mg_mm (idpath a) (mg_rho b))) @ concat_p_pp _ _ _ @ _).
  refine (_ @ (rho_natural (mg_rho (mg_m a b)))^); apply whiskerR.
  refine (_ @ mg_triangle (mg_m a b) mg_e).
  apply (cancelR _ _ (mg_alpha _ _ _)); refine (concat_pp_p _ _ _ @ _ @ concat_p_pp _ _ _).
  refine (whiskerL _ (alpha_natural idpath (mg_rho _) idpath)^ @ concat_p_pp _ _ _ @ _).
  refine (_ @ concat_pp_p _ _ _ @ whiskerL _ (alpha_natural idpath idpath (mg_lambda _))).
  refine (_ @ concat_p_pp _ _ _ @ whiskerR (mg_pentagon _ _ _ _)^ _); apply whiskerL.
  refine (_ @ (ap011_pqpq mg_m idpath idpath (mg_alpha b mg_e mg_e) (mg_mm idpath (mg_lambda mg_e)))^);
    exact (mg_mmm idpath (mg_triangle _ _)^).
Defined.

Definition lambda_rho_e
  : mg_lambda mg_e = mg_rho mg_e.
Proof.
  apply (cancelL (mg_rho (mg_m mg_e mg_e)) _ _).
  refine (rho_natural (mg_lambda mg_e) @ _).
  refine (_ @ (rho_natural (mg_rho mg_e))^); apply whiskerR.
  refine ((alpha_lambda mg_e mg_e)^ @ _).
  apply (cancelR _ _ (mg_lambda mg_e)); refine (concat_pp_p _ _ _ @ _).
  refine (whiskerL _ (lambda_natural (mg_lambda mg_e)) @ concat_p_pp _ _ _ @ _); apply whiskerR.
  apply mg_triangle.
Defined.

End DerivedCoherence.


Class MonoidalFunctor (A B : MonoidalGroupoid) := {
  mg_f : A -> B;
  mg_f0 : mg_e = mg_f mg_e;
  mg_f2 : forall a b : A, mg_m (mg_f a) (mg_f b) = mg_f (mg_m a b);
  mg_dalpha : forall a b c : A,
    mg_alpha (mg_f a) (mg_f b) (mg_f c) @ (mg_mm idpath (mg_f2 b c) @ mg_f2 a (mg_m b c))
    = (mg_mm (mg_f2 a b) idpath @ mg_f2 (mg_m a b) c) @ ap mg_f (mg_alpha a b c);
  mg_dlambda : forall b : A,
    mg_lambda (mg_f b) = mg_mm mg_f0 idpath @ mg_f2 mg_e b @ ap mg_f (mg_lambda b);
  mg_drho : forall a : A,
    mg_rho (mg_f a) = mg_mm idpath mg_f0 @ mg_f2 a mg_e @ ap mg_f (mg_rho a)
  }.
Coercion mg_f : MonoidalFunctor >-> Funclass.

Definition mg_f2_natural {A B : MonoidalGroupoid} (F : MonoidalFunctor A B)
  {a b a' b' : A} (pa : a = a') (pb : b = b')
  : mg_f2 a b @ ap mg_f (mg_mm pa pb)
    = mg_mm (ap mg_f pa) (ap mg_f pb) @ mg_f2 a' b'.
Proof.
  induction pa, pb; exact (concat_p1 _ @ (concat_1p _)^).
Defined.

Definition MonoidalFunctor_id (A : MonoidalGroupoid)
  : MonoidalFunctor A A.
Proof.
  srapply @Build_MonoidalFunctor.
  + exact idmap.
  + constructor.
  + constructor.
  + intros. simpl. refine (concat_p1 _ @ (ap_idmap _)^ @ (concat_1p _)^).
  + intros. simpl. refine ((ap_idmap _)^ @ (concat_1p _)^).
  + intros. simpl. refine ((ap_idmap _)^ @ (concat_1p _)^).
Defined.


Definition MonoidalFunctor_comp {A B C : MonoidalGroupoid}
  (G : MonoidalFunctor B C) (F : MonoidalFunctor A B)
  : MonoidalFunctor A C.
Proof.
  srapply @Build_MonoidalFunctor.
  + exact (fun x => G (F x)).
  + simpl. exact (@mg_f0 B C G @ ap G (@mg_f0 A B F)).
  + intros; simpl.
    exact (@mg_f2 B C G (F a) (F b) @ ap G (@mg_f2 A B F a b)).
  + intros; simpl.
    refine (whiskerL _ (whiskerR (ap011_pqpq mg_m idpath idpath (mg_f2 (F b) (F c)) (ap G (mg_f2 b c)))^ _) @ _ @ whiskerR (whiskerR (ap011_pqpq mg_m (mg_f2 (F a) (F b)) (ap G (mg_f2 a b)) idpath idpath) _) _).
    refine (whiskerL _ (concat_p_pp _ _ _ @ whiskerR (concat_pp_p _ _ _) _) @ _);
      refine (whiskerL _ (whiskerR (whiskerL _ (mg_f2_natural G (idpath (F a)) (mg_f2 b c))^ @ concat_p_pp _ _ _) _ @ concat_pp_p _ _ _) @ _).
    refine (concat_p_pp _ _ _ @ whiskerR (mg_dalpha _ _ _ @ concat_pp_p _ _ _) _ @ concat_pp_p _ _ _ @ _);
      refine (_ @ concat_p_pp _ _ _ @ concat_p_pp _ _ _); apply whiskerL.
    refine (whiskerL _ (ap_pp _ _ _)^ @ concat_pp_p _ _ _ @ whiskerL _ ((ap_pp _ _ _)^ @ ap (ap G) (mg_dalpha a b c) @ ap_pp _ _ _ @ whiskerR (ap_pp _ _ _) _ @ concat_pp_p _ _ _) @ concat_p_pp _ _ _ @ _).
    refine (whiskerR (mg_f2_natural G (mg_f2 a b) (idpath (F c))) _ @ concat_pp_p _ _ _ @ _); apply whiskerL;
      refine (concat_p_pp _ _ _ @ _); apply whiskerL.
    exact (ap_compose F G _)^.
  + intros; simpl.
    refine (_ @ concat_p_pp _ _ _ @ concat_p_pp _ _ _ @ whiskerR (whiskerR (ap011_pqpq mg_m mg_f0 (ap G mg_f0) idpath idpath) _) _).
    refine (mg_dlambda (F b) @ concat_pp_p _ _ _ @ _); apply whiskerL.
    refine (_ @ concat_pp_p _ _ _ @ whiskerL _ (concat_p_pp _ _ _));
      refine (_ @ concat_p_pp _ _ _ @ whiskerR (mg_f2_natural G mg_f0 idpath) _); apply whiskerL.
    refine (_ @ whiskerL _ (whiskerL _ (ap_compose F G (mg_lambda b))^)).
    refine (_ @ ap_pp G _ _ @ whiskerR (ap_pp G _ _) _ @ concat_pp_p _ _ _);
      apply ap; exact (mg_dlambda b).
  + intros; simpl.
    refine (_ @ concat_p_pp _ _ _ @ concat_p_pp _ _ _ @ whiskerR (whiskerR (ap011_pqpq mg_m idpath idpath mg_f0 (ap G mg_f0)) _) _).
    refine (mg_drho (F a) @ concat_pp_p _ _ _ @ _); apply whiskerL.
    refine (_ @ concat_pp_p _ _ _ @ whiskerL _ (concat_p_pp _ _ _));
      refine (_ @ concat_p_pp _ _ _ @ whiskerR (mg_f2_natural G idpath mg_f0) _); apply whiskerL.
    refine (_ @ whiskerL _ (whiskerL _ (ap_compose F G (mg_rho a))^)).
    refine (_ @ ap_pp G _ _ @ whiskerR (ap_pp G _ _) _ @ concat_pp_p _ _ _);
      apply ap; exact (mg_drho a).
Defined.

Class MonoidalNatIso {A B} (F G : MonoidalFunctor A B) := {
  mg_nt : F == G;
  mg_nt0 : @mg_f0 _ _ F @ mg_nt mg_e = @mg_f0 _ _ G;
  mg_nt2 : forall a b : A,
    @mg_f2 _ _ F a b @ mg_nt (mg_m a b)
    = ap011 mg_m (mg_nt a) (mg_nt b) @ @mg_f2 _ _ G a b
  }.

Lemma MonoidalNatIso_V {A B : MonoidalGroupoid} (F G : MonoidalFunctor A B)
  : MonoidalNatIso F G -> MonoidalNatIso G F.
Proof.
  intro eta.
  srapply @Build_MonoidalNatIso.
  + intro x. exact (mg_nt x)^.
  + simpl. refine (whiskerR (@mg_nt0 _ _ _ _ eta)^ _ @ _).
    exact (concat_pp_p _ _ _ @ whiskerL _ (concat_pV _) @ concat_p1 _).
  + simpl. intros.
    refine (_ @ whiskerR (ap011_VV _ _ _)^ _).
    apply moveL_Vp; refine (concat_p_pp _ _ _ @ _); apply moveR_pV.
    exact (mg_nt2 a b)^.
Defined.

Lemma MonoidalFunctor_comp_associative {A B C D : MonoidalGroupoid}
  (H : MonoidalFunctor C D) (G : MonoidalFunctor B C) (F : MonoidalFunctor A B)
  : MonoidalNatIso
      (MonoidalFunctor_comp (MonoidalFunctor_comp H G) F)
      (MonoidalFunctor_comp H (MonoidalFunctor_comp G F)).
Proof.
  srapply @Build_MonoidalNatIso.
  + simpl; constructor.
  + simpl. refine (concat_p1 _ @ concat_pp_p _ _ _ @ _).
    apply whiskerL.
    refine (_ @ (ap_pp H _ _)^).
    apply whiskerL.
    apply ap_compose.
  + intros; simpl. refine (concat_p1 _ @ concat_pp_p _ _ _ @ _ @ (concat_1p _)^).
    apply whiskerL.
    refine (_ @ (ap_pp H _ _)^).
    apply whiskerL.
    apply ap_compose.
Defined.

Lemma MonoidalFunctor_comp_left_unital {A B : MonoidalGroupoid}
  (F : MonoidalFunctor A B)
  : MonoidalNatIso (MonoidalFunctor_comp F (MonoidalFunctor_id A)) F.
Proof.
  srapply @Build_MonoidalNatIso; simpl.
  + constructor.
  + simpl. exact (concat_p1 _ @ concat_p1 _).
  + intros; simpl. exact (concat_p1 _ @ concat_p1 _ @ (concat_1p _)^).
Defined.

Lemma MonoidalFunctor_comp_right_unital {A B : MonoidalGroupoid}
  (F : MonoidalFunctor A B)
  : MonoidalNatIso (MonoidalFunctor_comp (MonoidalFunctor_id B) F) F.
Proof.
  srapply @Build_MonoidalNatIso; simpl.
  + constructor.
  + simpl. exact (concat_p1 _ @ concat_1p _ @ ap_idmap _).
  + intros; simpl. exact (concat_p1 _ @ concat_1p _ @ ap_idmap _ @ (concat_1p _)^).
Defined.

Lemma MonoidalNatIso_vcomp {A B : MonoidalGroupoid} {F G H : MonoidalFunctor A B}
  (theta : MonoidalNatIso F G) (eta : MonoidalNatIso G H)
  : MonoidalNatIso F H.
Proof.
  srapply @Build_MonoidalNatIso.
  + intro x. exact (mg_nt x @ mg_nt x).
  + simpl. refine (concat_p_pp _ _ _ @ _).
    exact (whiskerR mg_nt0 _ @ mg_nt0).
  + intros; simpl.
    refine (_ @ whiskerR (ap011_pqpq mg_m (mg_nt a) (mg_nt a) (mg_nt b) (mg_nt b)) _).
    refine (concat_p_pp _ _ _ @ _ @ concat_p_pp _ _ _).
    refine (whiskerR (mg_nt2 a b) _ @ concat_pp_p _ _ _ @ _); apply whiskerL.
    exact (mg_nt2 a b).
Defined.

Lemma MonoidalNatIso_hcomp {A B C : MonoidalGroupoid}
  {G1 G2 : MonoidalFunctor B C} {F1 F2 : MonoidalFunctor A B}
  (eta : MonoidalNatIso G1 G2) (theta : MonoidalNatIso F1 F2)
  : MonoidalNatIso (MonoidalFunctor_comp G1 F1) (MonoidalFunctor_comp G2 F2).
Proof.
  srapply @Build_MonoidalNatIso; simpl.
  + intro x. exact (mg_nt (F1 x) @ ap G2 (mg_nt x)).
  + simpl.
    refine (concat_pp_p _ _ _ @ _ @ concat_p_pp _ _ _ @ whiskerR mg_nt0 _); apply whiskerL.
    refine (concat_p_pp _ _ _ @ _ @ concat_pp_p _ _ _ @ whiskerL _ ((ap_pp _ _ _)^ @ ap (ap G2) mg_nt0));
    apply whiskerR.
    exact (homotopy_square mg_nt mg_f0)^.
  + intros; simpl.
    refine (_ @ whiskerR (ap011_pqpq mg_m _ _ _ _) _).
    refine (concat_pp_p _ _ _ @ whiskerL _ (concat_p_pp _ _ _ @ whiskerR (homotopy_square mg_nt (@mg_f2 _ _ F1 a b))^ _ @ concat_pp_p _ _ _) @ concat_p_pp _ _ _ @ _).
    refine (whiskerL _ ((ap_pp _ _ _)^ @ ap (ap G2) (mg_nt2 a b) @ ap_pp _ _ _) @ _);
    refine (concat_p_pp _ _ _ @ _ @ concat_pp_p _ _ _); apply whiskerR.
    refine (whiskerR (mg_nt2 (F1 a) (F1 b)) _ @ concat_pp_p _ _ _ @ _ @ concat_p_pp _ _ _); apply whiskerL.
    (* this would need a lemma ... *)
    generalize (mg_nt a) as p; induction p; generalize (mg_nt b) as q; induction q.
    exact (concat_p1 _ @ (concat_1p _)^).
Defined.

Definition MonoidalEquivalence (M N : MonoidalGroupoid) : Type
  := {F : MonoidalFunctor M N & {G : MonoidalFunctor N M & (MonoidalNatIso (MonoidalFunctor_comp G F) (MonoidalFunctor_id M)) * (MonoidalNatIso (MonoidalFunctor_comp F G) (MonoidalFunctor_id N))}}.

Section UniversalProperty.

Class IsFunctor (F : forall X : Type, IsHSet X -> MonoidalGroupoid) := {
  F_arr : forall (X Y : Type) (T_X : IsHSet X) (T_Y : IsHSet Y) (f : X -> Y),
          MonoidalFunctor (F X T_X) (F Y T_Y);
  F_id : forall (X : Type) (T_X : IsHSet X),
          MonoidalNatIso (F_arr X X T_X T_X (fun x => x)) (MonoidalFunctor_id (F X T_X));
  F_comp : forall (X Y Z : Type) (T_X : IsHSet X) (T_Y : IsHSet Y) (T_Z : IsHSet Z)
            (g : Y -> Z) (f : X -> Y),
            MonoidalNatIso (MonoidalFunctor_comp (F_arr Y Z T_Y T_Z g) (F_arr X Y T_X T_Y f)) (F_arr X Z T_X T_Z (g o f))
  }.

Class IsFreeFunctor (F : forall X : Type, IsHSet X -> MonoidalGroupoid) := {
  free_functor : IsFunctor F;
  Phi : forall (X : Type) (T_X : IsHSet X)
        (M : MonoidalGroupoid) (G : MonoidalFunctor (F X T_X) M),
        X -> @mgcarrier M;
  Phi_nat_M : forall (X : Type) (T_X : IsHSet X)
              (M : MonoidalGroupoid) (G : MonoidalFunctor (F X T_X) M)
              (N : MonoidalGroupoid) (H : MonoidalFunctor M N),
              H o Phi X T_X M G == Phi X T_X N (MonoidalFunctor_comp H G);
  Psi : forall (X : Type) (T_X : IsHSet X)
        (M : MonoidalGroupoid) (g : X -> @mgcarrier M),
        MonoidalFunctor (F X T_X) M;
  Psi_nat_X : forall (X : Type) (T_X : IsHSet X)
              (M : MonoidalGroupoid) (g : X -> @mgcarrier M)
              (Y : Type) (T_Y : IsHSet Y) (h : Y -> X),
              MonoidalNatIso
                (MonoidalFunctor_comp (Psi X T_X M g) (@F_arr F free_functor Y X T_Y T_X h))
                (Psi Y T_Y M (g o h));
  Theta : forall (X : Type) (T_X : IsHSet X) (M : MonoidalGroupoid),
          Phi X T_X M o Psi X T_X M == idmap;
  Chi : forall (X : Type) (T_X : IsHSet X)
          (M : MonoidalGroupoid) (G : MonoidalFunctor (F X T_X) M),
          MonoidalNatIso (Psi X T_X M (Phi X T_X M G)) G
  }.

End UniversalProperty.

End MonoidalGroupoids.



 