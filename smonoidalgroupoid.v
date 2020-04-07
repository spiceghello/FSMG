Require Export hott_lemmas.

Open Scope type.

Section SymMonoidalGroupoids.

Section SymMonoidalStructure.

Context {X : Type} (e : X) (m : X -> X -> X).

Definition IsAssociative : Type
  := forall a b c : X, m (m a b) c = m a (m b c).

Definition IsLeftUnital : Type
  := forall b : X, m e b = b.

Definition IsRightUnital : Type
  := forall a : X, m a e = a.

Definition IsSymmetric : Type
  := forall a b : X, m a b = m b a.

Definition IsPentagonCoherent (alpha : IsAssociative) : Type
  := forall a b c d : X,
      alpha (m a b) c d @ alpha a b (m c d)
      = ap011 m (alpha a b c) (idpath d) @ alpha a (m b c) d @ ap011 m (idpath a) (alpha b c d).

Definition IsTriangleCoherent (alpha : IsAssociative) (lambda : IsLeftUnital) (rho : IsRightUnital) : Type
  := forall a b : X,
      alpha a e b @ ap011 m (idpath a) (lambda b)
      = ap011 m (rho a) (idpath b).

Definition IsHexagonCoherent (alpha : IsAssociative) (tau : IsSymmetric) : Type
  := forall a b c : X,
      alpha a b c @ tau a (m b c) @ alpha b c a
      = ap011 m (tau a b) (idpath c) @ alpha b a c @ ap011 m (idpath b) (tau a c).

Definition IsBigonCoherent (tau : IsSymmetric) : Type
  := forall a b : X,
      tau a b @ tau b a = idpath (m a b).

End SymMonoidalStructure.

Class SymMonoidalGroupoid := {
  smgcarrier : Type;
  smgtrunc : IsTrunc 1 smgcarrier;
  smg_e : smgcarrier;
  smg_m : smgcarrier -> smgcarrier -> smgcarrier;
  smg_alpha : IsAssociative smg_m;
  smg_lambda : IsLeftUnital smg_e smg_m;
  smg_rho : IsRightUnital smg_e smg_m;
  smg_tau : IsSymmetric smg_m;
  smg_pentagon : IsPentagonCoherent smg_m smg_alpha;
  smg_triangle : IsTriangleCoherent smg_e smg_m smg_alpha smg_lambda smg_rho;
  smg_hexagon : IsHexagonCoherent smg_m smg_alpha smg_tau;
  smg_bigon : IsBigonCoherent smg_m smg_tau
  }.
Coercion smgcarrier : SymMonoidalGroupoid >-> Sortclass.

Definition smg_mm {M : SymMonoidalGroupoid} {a b a' b'} (pa : a = a') (pb : b = b')
  : smg_m a b = smg_m a' b'
  := ap011 smg_m pa pb.

Definition smg_mmm {M : SymMonoidalGroupoid} {a b a' b'} {pa pa' : a = a'} {pb pb' : b = b'}
  (fa : pa = pa') (fb : pb = pb')
  : smg_mm pa pb = smg_mm pa' pb'
  := ap011 smg_mm fa fb.

Section Naturality.

Context {M : SymMonoidalGroupoid}.

Definition alpha_natural {a b c a' b' c'} (pa : a = a') (pb : b = b') (pc : c = c')
  : smg_alpha a b c @ smg_mm pa (smg_mm pb pc) = smg_mm (smg_mm pa pb) pc @ smg_alpha a' b' c'.
Proof.
  induction pa, pb, pc;
  exact (concat_p1 _ @ (concat_1p _)^).
Defined.

Definition lambda_natural {b b'} (pb : b = b')
  : smg_lambda b @ pb = smg_mm (idpath smg_e) pb @ smg_lambda b'.
Proof.
  induction pb;
  exact (concat_p1 _ @ (concat_1p _)^).
Defined.

Definition rho_natural {a a'} (pa : a = a')
  : smg_rho a @ pa = smg_mm pa (idpath smg_e) @ smg_rho a'.
Proof.
  induction pa;
  exact (concat_p1 _ @ (concat_1p _)^).
Defined.

Definition tau_natural {a a' b b'} (pa : a = a') (pb : b = b')
  : smg_tau a b @ smg_mm pb pa = smg_mm pa pb @ smg_tau a' b'.
Proof.
  induction pa, pb;
  exact (concat_p1 _ @ (concat_1p _)^).
Defined.

End Naturality.

Section DerivedCoherence.

Context {M : SymMonoidalGroupoid}.

Definition rho_a_e (a : M)
  : smg_rho (smg_m a smg_e) = smg_mm (smg_rho a) (idpath smg_e).
Proof.
  apply (cancelR _ _ (smg_rho a)).
  exact (rho_natural (smg_rho a)).
Defined.

Definition lambda_e_b (b : M)
  : smg_lambda (smg_m smg_e b) = smg_mm (idpath smg_e) (smg_lambda b).
Proof.
  apply (cancelR _ _ (smg_lambda b)).
  exact (lambda_natural (smg_lambda b)).
Defined.

Definition alpha_lambda (a b : M)
  : smg_alpha smg_e a b @ smg_lambda (smg_m a b) = smg_mm (smg_lambda a) (idpath b).
Proof.
  apply (cancelL (smg_lambda _) _ _); refine (concat_p_pp _ _ _ @ _);
    refine (whiskerR (lambda_natural (smg_alpha smg_e a b)) _ @ concat_pp_p _ _ _ @ _).
  refine (whiskerL _ (lambda_natural (smg_lambda (smg_m a b))) @ concat_p_pp _ _ _ @ _).
  refine (_ @ (lambda_natural (smg_mm (smg_lambda a) (idpath b)))^); apply whiskerR.
  apply (cancelL (smg_alpha _ _ _) _ _); refine (concat_p_pp _ _ _ @ _);
    refine (_ @ (alpha_natural (idpath smg_e) (smg_lambda a) (idpath b))^);
    refine (concat_pp_p _ _ _ @ _).
  apply (cancelL (smg_mm (smg_alpha _ _ _) idpath) _ _);
    refine (concat_p_pp _ _ _ @ concat_p_pp _ _ _ @ _ @ concat_pp_p _ _ _);
    refine (whiskerR (smg_pentagon smg_e smg_e a b)^ _ @ concat_pp_p _ _ _ @ _).
  refine (whiskerL _ (smg_triangle smg_e (smg_m a b)) @ _).
  refine (alpha_natural (smg_rho smg_e) idpath idpath @ _); apply whiskerR.
  refine (_ @ (ap011_pqpq smg_m (smg_alpha smg_e smg_e a) (smg_mm idpath (smg_lambda a)) idpath idpath)^);
    exact (smg_mmm (smg_triangle _ _)^ idpath).
Defined.

Definition alpha_rho (a b : M)
  : smg_alpha a b smg_e @ smg_mm (idpath a) (smg_rho b) = smg_rho (smg_m a b).
Proof.
  apply (cancelL (smg_rho _) _ _); refine (concat_p_pp _ _ _ @ _).
  refine (whiskerR (rho_natural (smg_alpha a b smg_e)) _ @ concat_pp_p _ _ _ @ _).
  refine (whiskerL _ (rho_natural (smg_mm (idpath a) (smg_rho b))) @ concat_p_pp _ _ _ @ _).
  refine (_ @ (rho_natural (smg_rho (smg_m a b)))^); apply whiskerR.
  refine (_ @ smg_triangle (smg_m a b) smg_e).
  apply (cancelR _ _ (smg_alpha _ _ _)); refine (concat_pp_p _ _ _ @ _ @ concat_p_pp _ _ _).
  refine (whiskerL _ (alpha_natural idpath (smg_rho _) idpath)^ @ concat_p_pp _ _ _ @ _).
  refine (_ @ concat_pp_p _ _ _ @ whiskerL _ (alpha_natural idpath idpath (smg_lambda _))).
  refine (_ @ concat_p_pp _ _ _ @ whiskerR (smg_pentagon _ _ _ _)^ _); apply whiskerL.
  refine (_ @ (ap011_pqpq smg_m idpath idpath (smg_alpha b smg_e smg_e) (smg_mm idpath (smg_lambda smg_e)))^);
    exact (smg_mmm idpath (smg_triangle _ _)^).
Defined.

Definition lambda_rho_e
  : smg_lambda smg_e = smg_rho smg_e.
Proof.
  apply (cancelL (smg_rho (smg_m smg_e smg_e)) _ _).
  refine (rho_natural (smg_lambda smg_e) @ _).
  refine (_ @ (rho_natural (smg_rho smg_e))^); apply whiskerR.
  refine ((alpha_lambda smg_e smg_e)^ @ _).
  apply (cancelR _ _ (smg_lambda smg_e)); refine (concat_pp_p _ _ _ @ _).
  refine (whiskerL _ (lambda_natural (smg_lambda smg_e)) @ concat_p_pp _ _ _ @ _); apply whiskerR.
  apply smg_triangle.
Defined.

Definition tau_lambda_rho (a : M)
  : smg_tau a smg_e @ smg_lambda a = smg_rho a.
Proof.
  apply (cancelL (smg_lambda (smg_m a smg_e)) _ _);
  refine (concat_p_pp _ _ _ @ whiskerR (lambda_natural (smg_tau a smg_e)) _ @ _).
  refine (concat_pp_p _ _ _ @ whiskerL _ (lambda_natural (smg_lambda a)) @ _).
  refine (concat_p_pp _ _ _ @ _ @ (lambda_natural (smg_rho a))^); apply whiskerR.
  apply (cancelL (smg_alpha smg_e a smg_e) _ _);
  refine (_ @ (alpha_rho smg_e a)^).
  apply (cancelL (smg_mm (smg_tau a smg_e) idpath) _ _);
  refine (_ @ rho_natural (smg_tau a smg_e)).
  refine (_ @ whiskerR (rho_a_e a)^ _).
  refine (_ @ whiskerR (smg_triangle a smg_e) _).
  refine (_ @ whiskerR (whiskerL _ (smg_mmm (idpath idpath) lambda_rho_e)^) _).
  refine (_ @ whiskerL _ (tau_natural idpath (smg_rho smg_e)) @ concat_p_pp _ _ _).
  refine (concat_p_pp _ _ _ @ concat_p_pp _ _ _ @ whiskerR (smg_hexagon a smg_e smg_e)^ _ @ concat_pp_p _ _ _ @ _ @ concat_pp_p _ _ _); apply whiskerL.
  apply smg_triangle.
Defined.

Definition tau_rho_lambda (a : M)
  : smg_tau smg_e a @ smg_rho a = smg_lambda a.
Proof.
  refine (whiskerL _ (tau_lambda_rho a)^ @ concat_p_pp _ _ _ @ _).
  exact (whiskerR (smg_bigon smg_e a) _ @ concat_1p _).
Defined.

Definition bigon_var (a b : M)
  : (smg_tau a b)^ = smg_tau b a.
Proof.
  apply (cancelL (smg_tau a b) _ _ ).
  exact (concat_pV _ @ (smg_bigon _ _)^).
Defined.

Definition hexagon_var (a b c : M)
  : smg_alpha a b c @ (smg_tau (smg_m b c) a)^ @ smg_alpha b c a
    = smg_mm (smg_tau b a)^ (idpath c) @ smg_alpha b a c @ smg_mm (idpath b) (smg_tau c a)^.
Proof.
  refine (whiskerR (whiskerL _ (bigon_var (smg_m b c) a)) _ @ _ @ concat2 (whiskerR (smg_mmm (bigon_var b a)^ (idpath idpath)) _) (smg_mmm (idpath idpath) (bigon_var c a)^)).
  apply smg_hexagon.
Defined.

End DerivedCoherence.


Class SymMonoidalFunctor (A B : SymMonoidalGroupoid) := {
  smg_f : A -> B;
  smg_f0 : smg_e = smg_f smg_e;
  smg_f2 : forall a b : A, smg_m (smg_f a) (smg_f b) = smg_f (smg_m a b);
  smg_dalpha : forall a b c : A,
    smg_alpha (smg_f a) (smg_f b) (smg_f c) @ (smg_mm idpath (smg_f2 b c) @ smg_f2 a (smg_m b c))
    = (smg_mm (smg_f2 a b) idpath @ smg_f2 (smg_m a b) c) @ ap smg_f (smg_alpha a b c);
  smg_dlambda : forall b : A,
    smg_lambda (smg_f b) = smg_mm smg_f0 idpath @ smg_f2 smg_e b @ ap smg_f (smg_lambda b);
  smg_drho : forall a : A,
    smg_rho (smg_f a) = smg_mm idpath smg_f0 @ smg_f2 a smg_e @ ap smg_f (smg_rho a);
  smg_dtau : forall a b : A,
    smg_tau (smg_f a) (smg_f b) @ smg_f2 b a = smg_f2 a b @ ap smg_f (smg_tau a b)
  }.
Coercion smg_f : SymMonoidalFunctor >-> Funclass.

Definition smg_f2_natural {A B : SymMonoidalGroupoid} (F : SymMonoidalFunctor A B)
  {a b a' b' : A} (pa : a = a') (pb : b = b')
  : smg_f2 a b @ ap smg_f (smg_mm pa pb)
    = smg_mm (ap smg_f pa) (ap smg_f pb) @ smg_f2 a' b'.
Proof.
  induction pa, pb; exact (concat_p1 _ @ (concat_1p _)^).
Defined.

Definition SymMonoidalFunctor_id (A : SymMonoidalGroupoid)
  : SymMonoidalFunctor A A.
Proof.
  srapply @Build_SymMonoidalFunctor.
  + exact idmap.
  + constructor.
  + constructor.
  + intros. simpl. refine (concat_p1 _ @ (ap_idmap _)^ @ (concat_1p _)^).
  + intros. simpl. refine ((ap_idmap _)^ @ (concat_1p _)^).
  + intros. simpl. refine ((ap_idmap _)^ @ (concat_1p _)^).
  + intros. simpl. refine (concat_p1 _ @ (ap_idmap _)^ @ (concat_1p _)^).
Defined.


Definition SymMonoidalFunctor_comp {A B C : SymMonoidalGroupoid}
  (G : SymMonoidalFunctor B C) (F : SymMonoidalFunctor A B)
  : SymMonoidalFunctor A C.
Proof.
  srapply @Build_SymMonoidalFunctor.
  + exact (fun x => G (F x)).
  + simpl. exact (@smg_f0 B C G @ ap G (@smg_f0 A B F)).
  + intros; simpl.
    exact (@smg_f2 B C G (F a) (F b) @ ap G (@smg_f2 A B F a b)).
  + intros; simpl.
    refine (whiskerL _ (whiskerR (ap011_pqpq smg_m idpath idpath (smg_f2 (F b) (F c)) (ap G (smg_f2 b c)))^ _) @ _ @ whiskerR (whiskerR (ap011_pqpq smg_m (smg_f2 (F a) (F b)) (ap G (smg_f2 a b)) idpath idpath) _) _).
    refine (whiskerL _ (concat_p_pp _ _ _ @ whiskerR (concat_pp_p _ _ _) _) @ _);
      refine (whiskerL _ (whiskerR (whiskerL _ (smg_f2_natural G (idpath (F a)) (smg_f2 b c))^ @ concat_p_pp _ _ _) _ @ concat_pp_p _ _ _) @ _).
    refine (concat_p_pp _ _ _ @ whiskerR (smg_dalpha _ _ _ @ concat_pp_p _ _ _) _ @ concat_pp_p _ _ _ @ _);
      refine (_ @ concat_p_pp _ _ _ @ concat_p_pp _ _ _); apply whiskerL.
    refine (whiskerL _ (ap_pp _ _ _)^ @ concat_pp_p _ _ _ @ whiskerL _ ((ap_pp _ _ _)^ @ ap (ap G) (smg_dalpha a b c) @ ap_pp _ _ _ @ whiskerR (ap_pp _ _ _) _ @ concat_pp_p _ _ _) @ concat_p_pp _ _ _ @ _).
    refine (whiskerR (smg_f2_natural G (smg_f2 a b) (idpath (F c))) _ @ concat_pp_p _ _ _ @ _); apply whiskerL;
      refine (concat_p_pp _ _ _ @ _); apply whiskerL.
    exact (ap_compose F G _)^.
  + intros; simpl.
    refine (_ @ concat_p_pp _ _ _ @ concat_p_pp _ _ _ @ whiskerR (whiskerR (ap011_pqpq smg_m smg_f0 (ap G smg_f0) idpath idpath) _) _).
    refine (smg_dlambda (F b) @ concat_pp_p _ _ _ @ _); apply whiskerL.
    refine (_ @ concat_pp_p _ _ _ @ whiskerL _ (concat_p_pp _ _ _));
      refine (_ @ concat_p_pp _ _ _ @ whiskerR (smg_f2_natural G smg_f0 idpath) _); apply whiskerL.
    refine (_ @ whiskerL _ (whiskerL _ (ap_compose F G (smg_lambda b))^)).
    refine (_ @ ap_pp G _ _ @ whiskerR (ap_pp G _ _) _ @ concat_pp_p _ _ _);
      apply ap; exact (smg_dlambda b).
  + intros; simpl.
    refine (_ @ concat_p_pp _ _ _ @ concat_p_pp _ _ _ @ whiskerR (whiskerR (ap011_pqpq smg_m idpath idpath smg_f0 (ap G smg_f0)) _) _).
    refine (smg_drho (F a) @ concat_pp_p _ _ _ @ _); apply whiskerL.
    refine (_ @ concat_pp_p _ _ _ @ whiskerL _ (concat_p_pp _ _ _));
      refine (_ @ concat_p_pp _ _ _ @ whiskerR (smg_f2_natural G idpath smg_f0) _); apply whiskerL.
    refine (_ @ whiskerL _ (whiskerL _ (ap_compose F G (smg_rho a))^)).
    refine (_ @ ap_pp G _ _ @ whiskerR (ap_pp G _ _) _ @ concat_pp_p _ _ _);
      apply ap; exact (smg_drho a).
  + intros; simpl.
    refine (concat_p_pp _ _ _ @ whiskerR (smg_dtau (F a) (F b)) _ @ concat_pp_p _ _ _ @ _ @ concat_p_pp _ _ _); apply whiskerL.
    refine ((ap_pp G _ _)^ @ _ @ ap_pp G _ _ @ whiskerL _ (ap_compose F G _)^); apply ap.
    exact (smg_dtau a b).
Defined.

Class SymMonoidalNatIso {A B} (F G : SymMonoidalFunctor A B) := {
  smg_nt : F == G;
  smg_nt0 : @smg_f0 _ _ F @ smg_nt smg_e = @smg_f0 _ _ G;
  smg_nt2 : forall a b : A,
    @smg_f2 _ _ F a b @ smg_nt (smg_m a b)
    = ap011 smg_m (smg_nt a) (smg_nt b) @ @smg_f2 _ _ G a b
  }.

Lemma SymMonoidalNatIso_V {A B : SymMonoidalGroupoid} (F G : SymMonoidalFunctor A B)
  : SymMonoidalNatIso F G -> SymMonoidalNatIso G F.
Proof.
  intro eta.
  srapply @Build_SymMonoidalNatIso.
  + intro x. exact (smg_nt x)^.
  + simpl. refine (whiskerR (@smg_nt0 _ _ _ _ eta)^ _ @ _).
    exact (concat_pp_p _ _ _ @ whiskerL _ (concat_pV _) @ concat_p1 _).
  + simpl. intros.
    refine (_ @ whiskerR (ap011_VV _ _ _)^ _).
    apply moveL_Vp; refine (concat_p_pp _ _ _ @ _); apply moveR_pV.
    exact (smg_nt2 a b)^.
Defined.

Lemma SymMonoidalFunctor_comp_associative {A B C D : SymMonoidalGroupoid}
  (H : SymMonoidalFunctor C D) (G : SymMonoidalFunctor B C) (F : SymMonoidalFunctor A B)
  : SymMonoidalNatIso
      (SymMonoidalFunctor_comp (SymMonoidalFunctor_comp H G) F)
      (SymMonoidalFunctor_comp H (SymMonoidalFunctor_comp G F)).
Proof.
  srapply @Build_SymMonoidalNatIso.
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

Lemma SymMonoidalFunctor_comp_left_unital {A B : SymMonoidalGroupoid}
  (F : SymMonoidalFunctor A B)
  : SymMonoidalNatIso (SymMonoidalFunctor_comp F (SymMonoidalFunctor_id A)) F.
Proof.
  srapply @Build_SymMonoidalNatIso; simpl.
  + constructor.
  + simpl. exact (concat_p1 _ @ concat_p1 _).
  + intros; simpl. exact (concat_p1 _ @ concat_p1 _ @ (concat_1p _)^).
Defined.

Lemma SymMonoidalFunctor_comp_right_unital {A B : SymMonoidalGroupoid}
  (F : SymMonoidalFunctor A B)
  : SymMonoidalNatIso (SymMonoidalFunctor_comp (SymMonoidalFunctor_id B) F) F.
Proof.
  srapply @Build_SymMonoidalNatIso; simpl.
  + constructor.
  + simpl. exact (concat_p1 _ @ concat_1p _ @ ap_idmap _).
  + intros; simpl. exact (concat_p1 _ @ concat_1p _ @ ap_idmap _ @ (concat_1p _)^).
Defined.

Lemma SymMonoidalNatIso_vcomp {A B : SymMonoidalGroupoid} {F G H : SymMonoidalFunctor A B}
  (theta : SymMonoidalNatIso F G) (eta : SymMonoidalNatIso G H)
  : SymMonoidalNatIso F H.
Proof.
  srapply @Build_SymMonoidalNatIso.
  + intro x. exact (smg_nt x @ smg_nt x).
  + simpl. refine (concat_p_pp _ _ _ @ _).
    exact (whiskerR smg_nt0 _ @ smg_nt0).
  + intros; simpl.
    refine (_ @ whiskerR (ap011_pqpq smg_m (smg_nt a) (smg_nt a) (smg_nt b) (smg_nt b)) _).
    refine (concat_p_pp _ _ _ @ _ @ concat_p_pp _ _ _).
    refine (whiskerR (smg_nt2 a b) _ @ concat_pp_p _ _ _ @ _); apply whiskerL.
    exact (smg_nt2 a b).
Defined.

Lemma SymMonoidalNatIso_hcomp {A B C : SymMonoidalGroupoid}
  {G1 G2 : SymMonoidalFunctor B C} {F1 F2 : SymMonoidalFunctor A B}
  (eta : SymMonoidalNatIso G1 G2) (theta : SymMonoidalNatIso F1 F2)
  : SymMonoidalNatIso (SymMonoidalFunctor_comp G1 F1) (SymMonoidalFunctor_comp G2 F2).
Proof.
  srapply @Build_SymMonoidalNatIso; simpl.
  + intro x. exact (smg_nt (F1 x) @ ap G2 (smg_nt x)).
  + simpl.
    refine (concat_pp_p _ _ _ @ _ @ concat_p_pp _ _ _ @ whiskerR smg_nt0 _); apply whiskerL.
    refine (concat_p_pp _ _ _ @ _ @ concat_pp_p _ _ _ @ whiskerL _ ((ap_pp _ _ _)^ @ ap (ap G2) smg_nt0));
    apply whiskerR.
    exact (homotopy_square smg_nt smg_f0)^.
  + intros; simpl.
    refine (_ @ whiskerR (ap011_pqpq smg_m _ _ _ _) _).
    refine (concat_pp_p _ _ _ @ whiskerL _ (concat_p_pp _ _ _ @ whiskerR (homotopy_square smg_nt (@smg_f2 _ _ F1 a b))^ _ @ concat_pp_p _ _ _) @ concat_p_pp _ _ _ @ _).
    refine (whiskerL _ ((ap_pp _ _ _)^ @ ap (ap G2) (smg_nt2 a b) @ ap_pp _ _ _) @ _);
    refine (concat_p_pp _ _ _ @ _ @ concat_pp_p _ _ _); apply whiskerR.
    refine (whiskerR (smg_nt2 (F1 a) (F1 b)) _ @ concat_pp_p _ _ _ @ _ @ concat_p_pp _ _ _); apply whiskerL.
    (* this would need a lemma ... *)
    generalize (smg_nt a) as p; induction p; generalize (smg_nt b) as q; induction q.
    exact (concat_p1 _ @ (concat_1p _)^).
Defined.

Definition SymMonoidalEquivalence (M N : SymMonoidalGroupoid) : Type
  := {F : SymMonoidalFunctor M N & {G : SymMonoidalFunctor N M & (SymMonoidalNatIso (SymMonoidalFunctor_comp G F) (SymMonoidalFunctor_id M)) * (SymMonoidalNatIso (SymMonoidalFunctor_comp F G) (SymMonoidalFunctor_id N))}}.

Section UniversalProperty.

Class IsFunctor_Sym (F : forall X : Type, IsHSet X -> SymMonoidalGroupoid) := {
  F_arr : forall (X Y : Type) (T_X : IsHSet X) (T_Y : IsHSet Y) (f : X -> Y),
          SymMonoidalFunctor (F X T_X) (F Y T_Y);
  F_id : forall (X : Type) (T_X : IsHSet X),
          SymMonoidalNatIso (F_arr X X T_X T_X (fun x => x)) (SymMonoidalFunctor_id (F X T_X));
  F_comp : forall (X Y Z : Type) (T_X : IsHSet X) (T_Y : IsHSet Y) (T_Z : IsHSet Z)
            (g : Y -> Z) (f : X -> Y),
            SymMonoidalNatIso (SymMonoidalFunctor_comp (F_arr Y Z T_Y T_Z g) (F_arr X Y T_X T_Y f)) (F_arr X Z T_X T_Z (g o f))
  }.

Class IsFreeFunctor_Sym (F : forall X : Type, IsHSet X -> SymMonoidalGroupoid) := {
  free_functor : IsFunctor_Sym F;
  Phi : forall (X : Type) (T_X : IsHSet X)
        (M : SymMonoidalGroupoid) (G : SymMonoidalFunctor (F X T_X) M),
        X -> @smgcarrier M;
  Phi_nat_M : forall (X : Type) (T_X : IsHSet X)
              (M : SymMonoidalGroupoid) (G : SymMonoidalFunctor (F X T_X) M)
              (N : SymMonoidalGroupoid) (H : SymMonoidalFunctor M N),
              H o Phi X T_X M G == Phi X T_X N (SymMonoidalFunctor_comp H G);
  Psi : forall (X : Type) (T_X : IsHSet X)
        (M : SymMonoidalGroupoid) (g : X -> @smgcarrier M),
        SymMonoidalFunctor (F X T_X) M;
  Psi_nat_X : forall (X : Type) (T_X : IsHSet X)
              (M : SymMonoidalGroupoid) (g : X -> @smgcarrier M)
              (Y : Type) (T_Y : IsHSet Y) (h : Y -> X),
              SymMonoidalNatIso
                (SymMonoidalFunctor_comp (Psi X T_X M g) (@F_arr F free_functor Y X T_Y T_X h))
                (Psi Y T_Y M (g o h));
  Theta : forall (X : Type) (T_X : IsHSet X) (M : SymMonoidalGroupoid),
          Phi X T_X M o Psi X T_X M == idmap;
  Chi : forall (X : Type) (T_X : IsHSet X)
          (M : SymMonoidalGroupoid) (G : SymMonoidalFunctor (F X T_X) M),
          SymMonoidalNatIso (Psi X T_X M (Phi X T_X M G)) G
  }.

End UniversalProperty.

End SymMonoidalGroupoids.
