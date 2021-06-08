Require Export smonoidalgroupoid.

Section FSMG.

Private Inductive FSMG (X : Type) : Type :=
  | e : FSMG X
  | iota : X -> FSMG X
  | m : FSMG X -> FSMG X -> FSMG X.
Global Arguments e {X}.
Global Arguments iota {X} _.
Global Arguments m {X} _ _.
Context (X : Type).

Definition mm {x x' y y' : FSMG X}
  (p : x = x') (q : y = y')
  : m x y = m x' y'
  := ap011 m p q.

Axiom alpha : @IsAssociative (FSMG X) m.
Axiom lambda : @IsLeftUnital (FSMG X) e m.
Axiom rho : @IsRightUnital (FSMG X) e m.
Axiom tau : @IsSymmetric (FSMG X) m.
Axiom pentagon : IsPentagonCoherent m alpha.
Axiom triangle : IsTriangleCoherent e m alpha lambda rho.
Axiom hexagon : IsHexagonCoherent m alpha tau.
Axiom bigon : IsBigonCoherent m tau.
Axiom T_FSMG : IsTrunc 1 (FSMG X).

Section FSMG_ind.

Context
  (P : FSMG X -> Type)
  (e' : P e)
  (iota' : forall x : X, P (iota x))
  (m' : forall (a b : FSMG X), P a -> P b -> P (m a b)).
Global Arguments m' {a} {b} _ _.

Definition mm'
  {a1 a2 b1 b2 : FSMG X} {p : a1 = a2} {q : b1 = b2}
  {a1' : P a1} {a2' : P a2} {b1' : P b1} {b2' : P b2}
  (p' : transport P p a1' = a2') (q' : transport P q b1' = b2')
  : transport P (mm p q) (m' a1' b1') = m' a2' b2'.
Proof.
  induction p, q, p', q'; constructor.
Defined.

Fixpoint FSMG_ind
  (alpha' : forall (a b c : FSMG X) (a' : P a) (b' : P b) (c' : P c),
    transport P (alpha a b c) (m' (m' a' b') c') = m' a' (m' b' c'))
  (lambda' : forall (b : FSMG X) (b' : P b),
    transport P (lambda b) (m' e' b') = b')
  (rho' : forall (a : FSMG X) (a' : P a),
    transport P (rho a) (m' a' e') = a')
  (tau' : forall (a b : FSMG X) (a' : P a) (b' : P b),
    transport P (tau a b) (m' a' b') = m' b' a')
  (pentagon' : forall (a b c d : FSMG X) (a' : P a) (b' : P b) (c' : P c) (d' : P d),
    concat_D
      (alpha' _ _ _ (m' a' b') c' d')
      (alpha' _ _ _ a' b' (m' c' d'))
    = ap (fun z => transport P z (m' (m' (m' a' b') c') d')) (pentagon a b c d)
      @ concat_D
          (concat_D
            (mm' (alpha' _ _ _ a' b' c') (transport_1 P d'))
            (alpha' _ _ _ a' (m' b' c') d'))
          (mm' (transport_1 P a') (alpha' _ _ _ b' c' d')))
  (triangle' : forall (a b : FSMG X) (a' : P a) (b' : P b),
    concat_D
      (alpha' _ _ _ a' e' b')
      (mm' (transport_1 P a') (lambda' _ b'))
    = ap (fun z => transport P z (m' (m' a' e') b')) (triangle a b)
      @ mm' (rho' _ a') (transport_1 P b'))
  (hexagon' : forall (a b c : FSMG X) (a' : P a) (b' : P b) (c' : P c),
    concat_D
      (concat_D
        (alpha' _ _ _ a' b' c')
        (tau' _ _ a' (m' b' c')))
      (alpha' _ _ _ b' c' a')
    = ap (fun z => transport P z (m' (m' a' b') c')) (hexagon a b c)
    @ concat_D
        (concat_D
          (mm' (tau' _ _ a' b') (transport_1 P c'))
          (alpha' _ _ _ b' a' c'))
        (mm' (transport_1 P b') (tau' _ _ a' c')))
  (bigon' : forall (a b : FSMG X) (a' : P a) (b' : P b),
    concat_D (tau' _ _ a' b') (tau' _ _ b' a')
    = ap (fun z => transport P z (m' a' b')) (bigon a b))
  (T' : forall (w : FSMG X), IsTrunc 1 (P w))
  (w : FSMG X) : P w
  := match w with
    | e => e'
    | iota x => iota' x
    | m a b => m' (FSMG_ind alpha' lambda' rho' tau' pentagon' triangle' hexagon' bigon' T' a) (FSMG_ind alpha' lambda' rho' tau' pentagon' triangle' hexagon' bigon' T' b) end.

Section Axioms.

Context
  (alpha' : forall (a b c : FSMG X) (a' : P a) (b' : P b) (c' : P c),
    transport P (alpha a b c) (m' (m' a' b') c') = m' a' (m' b' c'))
  (lambda' : forall (b : FSMG X) (b' : P b),
    transport P (lambda b) (m' e' b') = b')
  (rho' : forall (a : FSMG X) (a' : P a),
    transport P (rho a) (m' a' e') = a')
  (tau' : forall (a b : FSMG X) (a' : P a) (b' : P b),
    transport P (tau a b) (m' a' b') = m' b' a')
  (pentagon' : forall (a b c d : FSMG X) (a' : P a) (b' : P b) (c' : P c) (d' : P d),
    concat_D
      (alpha' _ _ _ (m' a' b') c' d')
      (alpha' _ _ _ a' b' (m' c' d'))
    = ap (fun z => transport P z (m' (m' (m' a' b') c') d')) (pentagon a b c d)
      @ concat_D
          (concat_D
            (mm' (alpha' _ _ _ a' b' c') (transport_1 P d'))
            (alpha' _ _ _ a' (m' b' c') d'))
          (mm' (transport_1 P a') (alpha' _ _ _ b' c' d')))
  (triangle' : forall (a b : FSMG X) (a' : P a) (b' : P b),
    concat_D
      (alpha' _ _ _ a' e' b')
      (mm' (transport_1 P a') (lambda' _ b'))
    = ap (fun z => transport P z (m' (m' a' e') b')) (triangle a b)
      @ mm' (rho' _ a') (transport_1 P b'))
  (hexagon' : forall (a b c : FSMG X) (a' : P a) (b' : P b) (c' : P c),
    concat_D
      (concat_D
        (alpha' _ _ _ a' b' c')
        (tau' _ _ a' (m' b' c')))
      (alpha' _ _ _ b' c' a')
    = ap (fun z => transport P z (m' (m' a' b') c')) (hexagon a b c)
    @ concat_D
        (concat_D
          (mm' (tau' _ _ a' b') (transport_1 P c'))
          (alpha' _ _ _ b' a' c'))
        (mm' (transport_1 P b') (tau' _ _ a' c')))
  (bigon' : forall (a b : FSMG X) (a' : P a) (b' : P b),
    concat_D (tau' _ _ a' b') (tau' _ _ b' a')
    = ap (fun z => transport P z (m' a' b')) (bigon a b))
  (T' : forall (w : FSMG X), IsTrunc 1 (P w)).

Let FSMG_ind' := FSMG_ind alpha' lambda' rho' tau' pentagon' triangle' hexagon' bigon' T'.

Axiom FSMG_ind_beta_alpha
  : forall (a b c : FSMG X),
    apD FSMG_ind' (alpha a b c) = alpha' _ _ _ (FSMG_ind' a) (FSMG_ind' b) (FSMG_ind' c).

Axiom FSMG_ind_beta_lambda
  : forall (b : FSMG X),
    apD FSMG_ind' (lambda b) = lambda' _ (FSMG_ind' b).

Axiom FSMG_ind_beta_rho
  : forall (a : FSMG X),
    apD FSMG_ind' (rho a) = rho' _ (FSMG_ind' a).

Axiom FSMG_ind_beta_tau
  : forall (a b : FSMG X),
    apD FSMG_ind' (tau a b) = tau' _ _ (FSMG_ind' a) (FSMG_ind' b).

(* Axioms for pentagon and triangle omitted *)

End Axioms.

End FSMG_ind.

Section FSMG_ind_trunc.

Context
  (P : FSMG X -> Type)
  (e' : P e)
  (iota' : forall x : X, P (iota x))
  (m' : forall (a b : FSMG X), P a -> P b -> P (m a b)).
Global Arguments m' {a} {b} _ _.

Definition FSMG_ind_to_set
  (alpha' : forall (a b c : FSMG X) (a' : P a) (b' : P b) (c' : P c),
    transport P (alpha a b c) (m' (m' a' b') c') = m' a' (m' b' c'))
  (lambda' : forall (b : FSMG X) (b' : P b),
    transport P (lambda b) (m' e' b') = b')
  (rho' : forall (a : FSMG X) (a' : P a),
    transport P (rho a) (m' a' e') = a')
  (tau' : forall (a b : FSMG X) (a' : P a) (b' : P b),
    transport P (tau a b) (m' a' b') = m' b' a')
  (T' : forall (w : FSMG X), IsTrunc 0 (P w))
  : forall w : FSMG X, P w.
Proof.
  refine (FSMG_ind P e' iota' (@m') alpha' lambda' rho' tau' _ _ _ _ _);
  intros; apply T'.
Defined.

Definition FSMG_ind_to_prop
  (T' : forall (w : FSMG X), IsTrunc (-1) (P w))
  : forall w : FSMG X, P w.
Proof.
  refine (FSMG_ind_to_set _ _ _ _ _);
    intros; apply T'.
Defined.

End FSMG_ind_trunc.

Section FSMG_ind_paths.

Definition FSMG_ind_to_paths_in_gpd
  (P : Type)
  (f f' : FSMG X -> P)
  (e' : f e = f' e)
  (iota' : forall x : X, f (iota x) = f' (iota x))
  (m' : forall a b : FSMG X, f a = f' a -> f b = f' b -> f (m a b) = f' (m a b))
  (alpha' : forall (a b c : FSMG X) (a' : f a = f' a) (b' : f b = f' b) (c' : f c = f' c),
    m' (m a b) c (m' a b a' b') c' @ ap f' (alpha a b c)
    = ap f (alpha a b c) @ m' a (m b c) a' (m' b c b' c'))
  (lambda' : forall (b : FSMG X) (b' : f b = f' b),
     m' e b e' b' @ ap f' (lambda b) = ap f (lambda b) @ b')
  (rho' : forall (a : FSMG X) (a' : f a = f' a),
    m' a e a' e' @ ap f' (rho a) = ap f (rho a) @ a')
  (tau' : forall (a b : FSMG X) (a' : f a = f' a) (b' : f b = f' b),
    m' a b a' b' @ ap f' (tau a b) = ap f (tau a b) @ m' b a b' a')
  (T' : IsTrunc 1 P)
  : forall w : FSMG X, f w = f' w.
Proof.
  srapply (@FSMG_ind_to_set (fun w => f w = f' w) e' iota' m');
  intros; simpl;
  refine (transport_paths_FlFr _ _ @ _);
  refine (concat_pp_p _ _ _ @ _); apply moveR_Vp.
  + apply alpha'.
  + apply lambda'.
  + apply rho'.
  + apply tau'.
Defined.

Definition FSMG_ind_to_paths_in_set
  (P : Type)
  (f f' : FSMG X -> P)
  (e' : f e = f' e)
  (iota' : forall x : X, f (iota x) = f' (iota x))
  (m' : forall a b : FSMG X, f a = f' a -> f b = f' b -> f (m a b) = f' (m a b))
  (T' : IsTrunc 0 P)
  : forall w : FSMG X, f w = f' w.
Proof.
  srapply (@FSMG_ind_to_prop (fun w => f w = f' w) e' iota' m').
Defined.

Definition FSMG_ind_to_2paths_in_gpd
  (P : Type)
  (f f' : FSMG X -> P)
  (p p' : forall a : FSMG X, f a = f' a)
  (e' : p e = p' e)
  (iota' : forall x : X, p (iota x) = p' (iota x))
  (m' : forall a b : FSMG X, p a = p' a -> p b = p' b -> p (m a b) = p' (m a b))
  (T' : IsTrunc 1 P)
  : forall w : FSMG X, p w = p' w.
Proof.
  srapply (@FSMG_ind_to_prop (fun w => p w = p' w) e' iota' m').
Defined.

Definition FSMG_ind_to_fam_paths_in_gpd
  `{Funext}
  (B C : Type)
  (f f' : FSMG X -> B -> C)
  (e' : forall (b : B), f e b = f' e b)
  (iota' : forall (x : X) (b : B), f (iota x) b = f' (iota x) b)
  (m' : forall (a b : FSMG X)
    (a' : forall c : B, f a c = f' a c)
    (b' : forall c : B, f b c = f' b c)
    (q : B),
    f (m a b) q = f' (m a b) q)
  (alpha' : forall (a b c : FSMG X)
    (a' : forall z : B, f a z = f' a z)
    (b' : forall z : B, f b z = f' b z)
    (c' : forall z : B, f c z = f' c z)
    (q : B),
    m' (m a b) c (m' a b a' b') c' q @ ap (fun z : FSMG X => f' z q) (alpha a b c)
    = ap (fun z : FSMG X => f z q) (alpha a b c) @ m' a (m b c) a' (m' b c b' c') q)
  (lambda' : forall (b : FSMG X)
    (b' : forall z : B, f b z = f' b z)
    (q : B),
    m' e b e' b' q @ ap (fun a : FSMG X => f' a q) (lambda b)
    = ap (fun a : FSMG X => f a q) (lambda b) @ b' q)
  (rho' : forall (a : FSMG X)
    (a' : forall z : B, f a z = f' a z)
    (q : B),
    m' a e a' e' q @ ap (fun a0 : FSMG X => f' a0 q) (rho a)
    = ap (fun a0 : FSMG X => f a0 q) (rho a) @ a' q)
  (tau' : forall (a b : FSMG X)
    (a' : forall z : B, f a z = f' a z)
    (b' : forall z : B, f b z = f' b z)
    (q : B),
    m' a b a' b' q @ ap (fun a0 : FSMG X => f' a0 q) (tau a b)
    = ap (fun a0 : FSMG X => f a0 q) (tau a b) @ m' b a b' a' q)
  (T' : IsTrunc 1 C)
  : forall (a : FSMG X) (b : B), f a b = f' a b.
Proof.
  srefine (@FSMG_ind_to_set (fun a => forall b : B, f a b = f' a b) e' iota' m' _ _ _ _ _);
  simpl; intros;
  apply path_forall; intro q;
  refine (transport_forall' f f' _ _ _ @ _); apply moveR_Vp.
  + apply alpha'.
  + apply lambda'.
  + apply rho'.
  + apply tau'.
Defined.

End FSMG_ind_paths.

Section FSMG_rec.

Context
  (A : Type)
  (e' : A)
  (iota' : X -> A)
  (m' : A -> A -> A)
  (alpha' : @IsAssociative A m')
  (lambda' : @IsLeftUnital A e' m')
  (rho' : @IsRightUnital A e' m')
  (tau' : @IsSymmetric A m')
  (pentagon' : IsPentagonCoherent m' alpha')
  (triangle' : IsTriangleCoherent e' m' alpha' lambda' rho')
  (hexagon' : IsHexagonCoherent m' alpha' tau')
  (bigon' : IsBigonCoherent m' tau')
  (T' : IsTrunc 1 A).

Lemma mm'_transport_const
  {a1 a2 b1 b2 : FSMG X} (p : a1 = a2) (q : b1 = b2)
  {a1' a2' b1' b2' : A}
  (p' : a1' = a2') (q' : b1' = b2')
  : mm' (fun _ => A) (fun _ => fun _ => m') (transport_const p a1' @ p') (transport_const q b1' @ q')
    = transport_const (mm p q) (m' a1' b1') @ ap011 m' p' q'.
Proof.
  induction p, q, p', q'; constructor.
Defined.

Definition FSMG_rec_pentagon 
  : forall (a b c d : FSMG X) (a' b' c' d' : A),
    concat_D 
      (transport_const (alpha (m a b) c d) (m' (m' (m' a' b') c') d') @ alpha' (m' a' b') c' d')
      (transport_const (alpha a b (m c d)) (m' (m' a' b') (m' c' d')) @ alpha' a' b' (m' c' d'))
    = ap (fun z : m (m (m a b) c) d = m a (m b (m c d)) => transport (fun _ : FSMG X => A) z (m' (m' (m' a' b') c') d')) (pentagon a b c d)
      @ concat_D
          (concat_D
            (mm' (fun _ : FSMG X => A) (fun _ _ : FSMG X => m') (transport_const (alpha a b c) (m' (m' a' b') c') @ alpha' a' b' c') (transport_1 (fun _ : FSMG X => A) d'))
            (transport_const (alpha a (m b c) d) (m' (m' a' (m' b' c')) d') @ alpha' a' (m' b' c') d'))
        (mm' (fun _ : FSMG X => A) (fun _ _ : FSMG X => m') (transport_1 (fun _ : FSMG X => A) a') (transport_const (alpha b c d) (m' (m' b' c') d') @ alpha' b' c' d')).
Proof.
  intros.
  rewrite transport_1_const, transport_1_const,
    mm'_transport_const, mm'_transport_const,
    concat_D_const_p, concat_D_const_p, concat_D_const_p.
  refine (whiskerL _ (pentagon' a' b' c' d') @ _).
  refine (_ @ concat_pp_p _ _ _); apply whiskerR.
  exact (transport_const_pq _ _)^.
Defined.

Definition FSMG_rec_triangle
  : forall (a b : FSMG X) (a' b' : A),
    concat_D
      (transport_const (alpha a e b) (m' (m' a' e') b') @ alpha' a' e' b')
      (mm' (fun _ : FSMG X => A) (fun _ _ : FSMG X => m') (transport_1 (fun _ : FSMG X => A) a') (transport_const (lambda b) (m' e' b') @ lambda' b'))
    = ap (fun z : m (m a e) b = m a b => transport (fun _ : FSMG X => A) z (m' (m' a' e') b')) (triangle a b)
      @ mm' (fun _ : FSMG X => A) (fun _ _ : FSMG X => m') (transport_const (rho a) (m' a' e') @ rho' a') (transport_1 (fun _ : FSMG X => A) b').
Proof.
  intros.
  rewrite transport_1_const, transport_1_const,
    mm'_transport_const, mm'_transport_const,
    concat_D_const_p.
  refine (whiskerL _ (triangle' a' b') @ _).
  refine (_ @ concat_pp_p _ _ _); apply whiskerR.
  exact (transport_const_pq _ _)^.
Defined.

Definition FSMG_rec_hexagon
  : forall (a b c : FSMG X) (a' b' c' : A),
    concat_D
      (concat_D
        (transport_const (alpha a b c) (m' (m' a' b') c') @ alpha' a' b' c')
        (transport_const (tau a (m b c)) (m' a' (m' b' c')) @ tau' a' (m' b' c')))
      (transport_const (alpha b c a) (m' (m' b' c') a') @ alpha' b' c' a')
    = ap (fun z : m (m a b) c = m b (m c a) => transport (fun _ : FSMG X => A) z (m' (m' a' b') c'))
  (hexagon a b c)
  @ concat_D
      (concat_D
        (mm' (fun _ : FSMG X => A) (fun _ _ : FSMG X => m')
          (transport_const (tau a b) (m' a' b') @ tau' a' b')
          (transport_1 (fun _ : FSMG X => A) c'))
        (transport_const (alpha b a c) (m' (m' b' a') c') @ alpha' b' a' c'))
      (mm' (fun _ : FSMG X => A) (fun _ _ : FSMG X => m')
        (transport_1 (fun _ : FSMG X => A) b')
        (transport_const (tau a c) (m' a' c') @ tau' a' c')).
Proof.
  intros.
  rewrite transport_1_const, transport_1_const,
    mm'_transport_const, mm'_transport_const,
    concat_D_const_p, concat_D_const_p, concat_D_const_p, concat_D_const_p.
  refine (whiskerL _ (hexagon' a' b' c') @ _).
  refine (_ @ concat_pp_p _ _ _); apply whiskerR.
  exact (transport_const_pq _ _)^.
Defined.

Definition FSMG_rec_bigon
  : forall (a b : FSMG X) (a' b' : A),
    concat_D
      (transport_const (tau a b) (m' a' b') @ tau' a' b')
      (transport_const (tau b a) (m' b' a') @ tau' b' a')
    = ap (fun z : m a b = m a b => transport (fun _ : FSMG X => A) z (m' a' b')) (bigon a b).
Proof.
  intros.
  rewrite concat_D_const_p.
  refine (whiskerL _ (bigon' a' b') @ concat_p1 _ @ _).
  srefine ((transport_const_pq (bigon a b) _)^ @ _); simpl.
  exact (concat_p1 _).
Defined.

Definition FSMG_rec
  : FSMG X -> A.
Proof.
  srapply (@FSMG_ind (fun _ => A) e' iota' (fun _ => fun _ => m')); hnf.
  + intros. exact (transport_const _ _ @ alpha' a' b' c').
  + intros. exact (transport_const _ _ @ lambda' b').
  + intros. exact (transport_const _ _ @ rho' a').
  + intros. exact (transport_const _ _ @ tau' a' b').
  + hnf. exact FSMG_rec_pentagon.
  + hnf. exact FSMG_rec_triangle.
  + hnf. exact FSMG_rec_hexagon.
  + hnf. exact FSMG_rec_bigon.
Defined.

Definition FSMG_rec_beta_alpha
  : forall a b c : FSMG X,
    ap FSMG_rec (alpha a b c) = alpha' (FSMG_rec a) (FSMG_rec b) (FSMG_rec c).
Proof.
  intros.
  eapply (cancelL (transport_const (alpha a b c) _)).
  refine ((apD_const _ (alpha a b c))^ @ _).
  srapply (@FSMG_ind_beta_alpha _ _ iota' _ _ _ _ _ FSMG_rec_pentagon FSMG_rec_triangle FSMG_rec_hexagon FSMG_rec_bigon _ a b c).
Defined.

Definition FSMG_rec_beta_lambda
  : forall b : FSMG X,
    ap FSMG_rec (lambda b) = lambda' (FSMG_rec b).
Proof.
  intros.
  eapply (cancelL (transport_const (lambda b) _)).
  refine ((apD_const _ (lambda b))^ @ _).
  srapply @FSMG_ind_beta_lambda.
Defined.

Definition FSMG_rec_beta_rho
  : forall a : FSMG X,
    ap FSMG_rec (rho a) = rho' (FSMG_rec a).
Proof.
  intros.
  eapply (cancelL (transport_const (rho a) _)).
  refine ((apD_const _ (rho a))^ @ _).
  srapply @FSMG_ind_beta_rho.
Defined.

Definition FSMG_rec_beta_tau
  : forall a b : FSMG X,
    ap FSMG_rec (tau a b) = tau' (FSMG_rec a) (FSMG_rec b).
Proof.
  intros.
  eapply (cancelL (transport_const (tau a b) _)).
  refine ((apD_const _ (tau a b))^ @ _).
  srapply @FSMG_ind_beta_tau.
Defined.

End FSMG_rec.

Section FSMG_rec_trunc.

Lemma FSMG_rec_to_set
  (A : Type)
  (e' : A)
  (iota' : X -> A)
  (m' : A -> A -> A)
  (alpha' : @IsAssociative A m')
  (lambda' : @IsLeftUnital A e' m')
  (rho' : @IsRightUnital A e' m')
  (tau' : @IsSymmetric A m')
  (T' : IsTrunc 0 A)
  : FSMG X -> A.
Proof.
  refine (@FSMG_rec A e' iota' m' alpha' lambda' rho' tau' _ _ _ _ _);
  [unfold IsPentagonCoherent | unfold IsTriangleCoherent | unfold IsHexagonCoherent | unfold IsBigonCoherent];
  intros; apply T'.
Defined.

Lemma FSMG_rec_to_prop
  (A : Type)
  (e' : A)
  (iota' : X -> A)
  (m' : A -> A -> A)
  (T' : IsTrunc (-1) A)
  : FSMG X -> A.
Proof.
  srapply (@FSMG_rec_to_set A e' iota' m');
  [unfold IsAssociative | unfold IsLeftUnital | unfold IsRightUnital | unfold IsSymmetric];
  intros; apply T'.
Defined.

End FSMG_rec_trunc.

End FSMG.

Arguments mm {X} {_} {_} {_} {_} p q.

Arguments alpha {X} _ _ _.
Arguments lambda {X} _.
Arguments rho {X} _.
Arguments tau {X} _ _.
Arguments pentagon {X} _ _ _ _.
Arguments triangle {X} _ _.
Arguments hexagon {X} _ _ _.
Arguments bigon {X} _ _.
Arguments T_FSMG {X} _ _ _ _ _ _.

Definition FSMG_SMG (X : Type) {T_X : IsHSet X} : SymMonoidalGroupoid
  := Build_SymMonoidalGroupoid (FSMG X) T_FSMG e m alpha lambda rho tau pentagon triangle hexagon bigon.

Section Redefinitions.

Context {X : Type} {T_X : IsHSet X}.

Definition alpha_FSMG_natural {a b c a' b' c' : FSMG X} (pa : a = a') (pb : b = b') (pc : c = c')
  := @alpha_natural (FSMG_SMG X) a b c a' b' c' pa pb pc.

Definition lambda_FSMG_natural {b b' : FSMG X} (pb : b = b')
  := @lambda_natural (FSMG_SMG X) b b' pb.

Definition rho_FSMG_natural {a a' : FSMG X} (pa : a = a')
  := @rho_natural (FSMG_SMG X) a a' pa.

Definition tau_FSMG_natural {a a' b b' : FSMG X} (pa : a = a') (pb : b = b')
  := @tau_natural (FSMG_SMG X) a a' b b' pa pb.

Definition rho_FSMG_a_e (a : FSMG X)
  := @rho_a_e (FSMG_SMG X) a.

Definition lambda_FSMG_e_b (b : FSMG X)
  := @lambda_e_b (FSMG_SMG X) b.

Definition alpha_lambda_FSMG (a b : FSMG X)
  := @alpha_lambda (FSMG_SMG X) a b.

Definition alpha_rho_FSMG (a b : FSMG X)
  := @alpha_rho (FSMG_SMG X) a b.

Definition lambda_rho_FSMG_e
  := @lambda_rho_e (FSMG_SMG X).

Definition tau_lambda_rho_FSMG (a : FSMG X)
  := @tau_lambda_rho (FSMG_SMG X) a.

Definition tau_rho_lambda_FSMG (a : FSMG X)
  := @tau_rho_lambda (FSMG_SMG X) a.

Definition bigon_var_FSMG (a b : FSMG X)
  := @bigon_var (FSMG_SMG X) a b.

Definition hexagon_var_FSMG (a b c : FSMG X)
  := @ hexagon_var (FSMG_SMG X) a b c.

End Redefinitions.