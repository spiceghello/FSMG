Require Export monoidalgroupoid.

Section FMG.

Private Inductive FMG (X : Type) : Type :=
  | e : FMG X
  | iota : X -> FMG X
  | m : FMG X -> FMG X -> FMG X.
Global Arguments e {X}.
Global Arguments iota {X} _.
Global Arguments m {X} _ _.
Context (X : Type).

Definition mm {x x' y y' : FMG X}
  (p : x = x') (q : y = y')
  : m x y = m x' y'
  := ap011 m p q.

Axiom alpha : @IsAssociative (FMG X) m.
Axiom lambda : @IsLeftUnital (FMG X) e m.
Axiom rho : @IsRightUnital (FMG X) e m.
Axiom pentagon : IsPentagonCoherent m alpha.
Axiom triangle : IsTriangleCoherent e m alpha lambda rho.
Axiom T_FMG : IsTrunc 1 (FMG X).

Section FMG_ind.

Context
  (P : FMG X -> Type)
  (e' : P e)
  (iota' : forall x : X, P (iota x))
  (m' : forall (a b : FMG X), P a -> P b -> P (m a b)).
Global Arguments m' {a} {b} _ _.

Definition mm'
  {a1 a2 b1 b2 : FMG X} {p : a1 = a2} {q : b1 = b2}
  {a1' : P a1} {a2' : P a2} {b1' : P b1} {b2' : P b2}
  (p' : transport P p a1' = a2') (q' : transport P q b1' = b2')
  : transport P (mm p q) (m' a1' b1') = m' a2' b2'.
Proof.
  induction p, q, p', q'; constructor.
Defined.

Fixpoint FMG_ind
  (alpha' : forall (a b c : FMG X) (a' : P a) (b' : P b) (c' : P c),
    transport P (alpha a b c) (m' (m' a' b') c') = m' a' (m' b' c'))
  (lambda' : forall (b : FMG X) (b' : P b),
    transport P (lambda b) (m' e' b') = b')
  (rho' : forall (a : FMG X) (a' : P a),
    transport P (rho a) (m' a' e') = a')
  (pentagon' : forall (a b c d : FMG X) (a' : P a) (b' : P b) (c' : P c) (d' : P d),
    concat_D
      (alpha' _ _ _ (m' a' b') c' d')
      (alpha' _ _ _ a' b' (m' c' d'))
    = ap (fun z => transport P z (m' (m' (m' a' b') c') d')) (pentagon a b c d)
      @ concat_D
          (concat_D
            (mm' (alpha' _ _ _ a' b' c') (transport_1 P d'))
            (alpha' _ _ _ a' (m' b' c') d'))
          (mm' (transport_1 P a') (alpha' _ _ _ b' c' d')))
  (triangle' : forall (a b : FMG X) (a' : P a) (b' : P b),
    concat_D
      (alpha' _ _ _ a' e' b')
      (mm' (transport_1 P a') (lambda' _ b'))
    = ap (fun z => transport P z (m' (m' a' e') b')) (triangle a b)
      @ mm' (rho' _ a') (transport_1 P b'))
  (T' : forall (w : FMG X), IsTrunc 1 (P w))
  (w : FMG X) : P w
  := match w with
    | e => e'
    | iota x => iota' x
    | m a b => m' (FMG_ind alpha' lambda' rho' pentagon' triangle' T' a) (FMG_ind alpha' lambda' rho' pentagon' triangle' T' b) end.

Section Axioms.

Context
  (alpha' : forall (a b c : FMG X) (a' : P a) (b' : P b) (c' : P c),
    transport P (alpha a b c) (m' (m' a' b') c') = m' a' (m' b' c'))
  (lambda' : forall (b : FMG X) (b' : P b),
    transport P (lambda b) (m' e' b') = b')
  (rho' : forall (a : FMG X) (a' : P a),
    transport P (rho a) (m' a' e') = a')
  (pentagon' : forall (a b c d : FMG X) (a' : P a) (b' : P b) (c' : P c) (d' : P d),
    concat_D
      (alpha' _ _ _ (m' a' b') c' d')
      (alpha' _ _ _ a' b' (m' c' d'))
    = ap (fun z => transport P z (m' (m' (m' a' b') c') d')) (pentagon a b c d)
      @ concat_D
          (concat_D
            (mm' (alpha' _ _ _ a' b' c') (transport_1 P d'))
            (alpha' _ _ _ a' (m' b' c') d'))
          (mm' (transport_1 P a') (alpha' _ _ _ b' c' d')))
  (triangle' : forall (a b : FMG X) (a' : P a) (b' : P b),
    concat_D
      (alpha' _ _ _ a' e' b')
      (mm' (transport_1 P a') (lambda' _ b'))
    = ap (fun z => transport P z (m' (m' a' e') b')) (triangle a b)
      @ mm' (rho' _ a') (transport_1 P b'))
  (T' : forall (w : FMG X), IsTrunc 1 (P w)).

Let FMG_ind' := FMG_ind alpha' lambda' rho' pentagon' triangle' T'.

Axiom FMG_ind_beta_alpha
  : forall (a b c : FMG X),
    apD FMG_ind' (alpha a b c) = alpha' _ _ _ (FMG_ind' a) (FMG_ind' b) (FMG_ind' c).

Axiom FMG_ind_beta_lambda
  : forall (b : FMG X),
    apD FMG_ind' (lambda b) = lambda' _ (FMG_ind' b).

Axiom FMG_ind_beta_rho
  : forall (a : FMG X),
    apD FMG_ind' (rho a) = rho' _ (FMG_ind' a).

(* Axioms for pentagon and triangle omitted *)

End Axioms.

End FMG_ind.

Section FMG_ind_trunc.

Context
  (P : FMG X -> Type)
  (e' : P e)
  (iota' : forall x : X, P (iota x))
  (m' : forall (a b : FMG X), P a -> P b -> P (m a b)).
Global Arguments m' {a} {b} _ _.

Definition FMG_ind_to_set
  (alpha' : forall (a b c : FMG X) (a' : P a) (b' : P b) (c' : P c),
    transport P (alpha a b c) (m' (m' a' b') c') = m' a' (m' b' c'))
  (lambda' : forall (b : FMG X) (b' : P b),
    transport P (lambda b) (m' e' b') = b')
  (rho' : forall (a : FMG X) (a' : P a),
    transport P (rho a) (m' a' e') = a')
  (T' : forall (w : FMG X), IsTrunc 0 (P w))
  : forall w : FMG X, P w.
Proof.
  refine (FMG_ind P e' iota' (@m') alpha' lambda' rho' _ _ _);
  intros; apply T'.
Defined.

Definition FMG_ind_to_prop
  (T' : forall (w : FMG X), IsTrunc (-1) (P w))
  : forall w : FMG X, P w.
Proof.
  refine (FMG_ind_to_set _ _ _ _);
    intros; apply T'.
Defined.

End FMG_ind_trunc.

Section FMG_ind_paths.

Definition FMG_ind_to_paths_in_gpd
  (P : Type)
  (f f' : FMG X -> P)
  (e' : f e = f' e)
  (iota' : forall x : X, f (iota x) = f' (iota x))
  (m' : forall a b : FMG X, f a = f' a -> f b = f' b -> f (m a b) = f' (m a b))
  (alpha' : forall (a b c : FMG X) (a' : f a = f' a) (b' : f b = f' b) (c' : f c = f' c),
    m' (m a b) c (m' a b a' b') c' @ ap f' (alpha a b c)
    = ap f (alpha a b c) @ m' a (m b c) a' (m' b c b' c'))
  (lambda' : forall (b : FMG X) (b' : f b = f' b),
     m' e b e' b' @ ap f' (lambda b) = ap f (lambda b) @ b')
  (rho' : forall (a : FMG X) (a' : f a = f' a),
    m' a e a' e' @ ap f' (rho a) = ap f (rho a) @ a')
  (T' : IsTrunc 1 P)
  : forall w : FMG X, f w = f' w.
Proof.
  srapply (@FMG_ind_to_set (fun w => f w = f' w) e' iota' m');
  intros; simpl;
  refine (transport_paths_FlFr _ _ @ _);
  refine (concat_pp_p _ _ _ @ _); apply moveR_Vp.
  + apply alpha'.
  + apply lambda'.
  + apply rho'.
Defined.

Definition FMG_ind_to_paths_in_set
  (P : Type)
  (f f' : FMG X -> P)
  (e' : f e = f' e)
  (iota' : forall x : X, f (iota x) = f' (iota x))
  (m' : forall a b : FMG X, f a = f' a -> f b = f' b -> f (m a b) = f' (m a b))
  (T' : IsTrunc 0 P)
  : forall w : FMG X, f w = f' w.
Proof.
  srapply (@FMG_ind_to_prop (fun w => f w = f' w) e' iota' m').
Defined.

Definition FMG_ind_to_2paths_in_gpd
  (P : Type)
  (f f' : FMG X -> P)
  (p p' : forall a : FMG X, f a = f' a)
  (e' : p e = p' e)
  (iota' : forall x : X, p (iota x) = p' (iota x))
  (m' : forall a b : FMG X, p a = p' a -> p b = p' b -> p (m a b) = p' (m a b))
  (T' : IsTrunc 1 P)
  : forall w : FMG X, p w = p' w.
Proof.
  srapply (@FMG_ind_to_prop (fun w => p w = p' w) e' iota' m').
Defined.

Definition FMG_ind_to_fam_paths_in_gpd
  `{Funext}
  (B C : Type)
  (f f' : FMG X -> B -> C)
  (e' : forall (b : B), f e b = f' e b)
  (iota' : forall (x : X) (b : B), f (iota x) b = f' (iota x) b)
  (m' : forall (a b : FMG X)
    (a' : forall c : B, f a c = f' a c)
    (b' : forall c : B, f b c = f' b c)
    (q : B),
    f (m a b) q = f' (m a b) q)
  (alpha' : forall (a b c : FMG X)
    (a' : forall z : B, f a z = f' a z)
    (b' : forall z : B, f b z = f' b z)
    (c' : forall z : B, f c z = f' c z)
    (q : B),
    m' (m a b) c (m' a b a' b') c' q @ ap (fun z : FMG X => f' z q) (alpha a b c)
    = ap (fun z : FMG X => f z q) (alpha a b c) @ m' a (m b c) a' (m' b c b' c') q)
  (lambda' : forall (b : FMG X)
    (b' : forall z : B, f b z = f' b z)
    (q : B),
    m' e b e' b' q @ ap (fun a : FMG X => f' a q) (lambda b)
    = ap (fun a : FMG X => f a q) (lambda b) @ b' q)
  (rho' : forall (a : FMG X)
    (a' : forall z : B, f a z = f' a z)
    (q : B),
    m' a e a' e' q @ ap (fun a0 : FMG X => f' a0 q) (rho a)
    = ap (fun a0 : FMG X => f a0 q) (rho a) @ a' q)
  (T' : IsTrunc 1 C)
  : forall (a : FMG X) (b : B), f a b = f' a b.
Proof.
  srefine (@FMG_ind_to_set (fun a => forall b : B, f a b = f' a b) e' iota' m' _ _ _ _);
  simpl; intros;
  apply path_forall; intro q;
  refine (transport_forall' f f' _ _ _ @ _); apply moveR_Vp.
  + apply alpha'.
  + apply lambda'.
  + apply rho'.
Defined.

End FMG_ind_paths.

Section FMG_rec.

Context
  (A : Type)
  (e' : A)
  (iota' : X -> A)
  (m' : A -> A -> A)
  (alpha' : @IsAssociative A m')
  (lambda' : @IsLeftUnital A e' m')
  (rho' : @IsRightUnital A e' m')
  (pentagon' : IsPentagonCoherent m' alpha')
  (triangle' : IsTriangleCoherent e' m' alpha' lambda' rho')
  (T' : IsTrunc 1 A).

Lemma mm'_transport_const
  {a1 a2 b1 b2 : FMG X} (p : a1 = a2) (q : b1 = b2)
  {a1' a2' b1' b2' : A}
  (p' : a1' = a2') (q' : b1' = b2')
  : mm' (fun _ => A) (fun _ => fun _ => m') (transport_const p a1' @ p') (transport_const q b1' @ q')
    = transport_const (mm p q) (m' a1' b1') @ ap011 m' p' q'.
Proof.
  induction p, q, p', q'; constructor.
Defined.

Definition FMG_rec_pentagon 
  : forall (a b c d : FMG X) (a' b' c' d' : A),
    concat_D 
      (transport_const (alpha (m a b) c d) (m' (m' (m' a' b') c') d') @ alpha' (m' a' b') c' d')
      (transport_const (alpha a b (m c d)) (m' (m' a' b') (m' c' d')) @ alpha' a' b' (m' c' d'))
    = ap (fun z : m (m (m a b) c) d = m a (m b (m c d)) => transport (fun _ : FMG X => A) z (m' (m' (m' a' b') c') d')) (pentagon a b c d)
      @ concat_D
          (concat_D
            (mm' (fun _ : FMG X => A) (fun _ _ : FMG X => m') (transport_const (alpha a b c) (m' (m' a' b') c') @ alpha' a' b' c') (transport_1 (fun _ : FMG X => A) d'))
            (transport_const (alpha a (m b c) d) (m' (m' a' (m' b' c')) d') @ alpha' a' (m' b' c') d'))
        (mm' (fun _ : FMG X => A) (fun _ _ : FMG X => m') (transport_1 (fun _ : FMG X => A) a') (transport_const (alpha b c d) (m' (m' b' c') d') @ alpha' b' c' d')).
Proof.
  intros.
  rewrite transport_1_const, transport_1_const,
    mm'_transport_const, mm'_transport_const,
    concat_D_const_p, concat_D_const_p, concat_D_const_p.
  refine (whiskerL _ (pentagon' a' b' c' d') @ _).
  refine (_ @ concat_pp_p _ _ _); apply whiskerR.
  exact (transport_const_pq _ _)^.
Defined.

Definition FMG_rec_triangle
  : forall (a b : FMG X) (a' b' : A),
    concat_D
      (transport_const (alpha a e b) (m' (m' a' e') b') @ alpha' a' e' b')
      (mm' (fun _ : FMG X => A) (fun _ _ : FMG X => m') (transport_1 (fun _ : FMG X => A) a') (transport_const (lambda b) (m' e' b') @ lambda' b'))
    = ap (fun z : m (m a e) b = m a b => transport (fun _ : FMG X => A) z (m' (m' a' e') b')) (triangle a b)
      @ mm' (fun _ : FMG X => A) (fun _ _ : FMG X => m') (transport_const (rho a) (m' a' e') @ rho' a') (transport_1 (fun _ : FMG X => A) b').
Proof.
  intros.
  rewrite transport_1_const, transport_1_const,
    mm'_transport_const, mm'_transport_const,
    concat_D_const_p.
  refine (whiskerL _ (triangle' a' b') @ _).
  refine (_ @ concat_pp_p _ _ _); apply whiskerR.
  exact (transport_const_pq _ _)^.
Defined.

Definition FMG_rec
  : FMG X-> A.
Proof.
  srapply (@FMG_ind (fun _ => A) e' iota' (fun _ => fun _ => m')); hnf.
  + intros. exact (transport_const _ _ @ alpha' a' b' c').
  + intros. exact (transport_const _ _ @ lambda' b').
  + intros. exact (transport_const _ _ @ rho' a').
  + hnf. exact FMG_rec_pentagon.
  + hnf. exact FMG_rec_triangle.
Defined.

Definition FMG_rec_beta_alpha
  : forall a b c : FMG X,
    ap FMG_rec (alpha a b c) = alpha' (FMG_rec a) (FMG_rec b) (FMG_rec c).
Proof.
  intros.
  eapply (cancelL (transport_const (alpha a b c) _)).
  refine ((apD_const _ (alpha a b c))^ @ _).
  unfold FMG_rec.
  srapply @FMG_ind_beta_alpha.
Defined.

Definition FMG_rec_beta_lambda
  : forall b : FMG X,
    ap FMG_rec (lambda b) = lambda' (FMG_rec b).
Proof.
  intros.
  eapply (cancelL (transport_const (lambda b) _)).
  refine ((apD_const _ (lambda b))^ @ _).
  srapply @FMG_ind_beta_lambda.
Defined.

Definition FMG_rec_beta_rho
  : forall a : FMG X,
    ap FMG_rec (rho a) = rho' (FMG_rec a).
Proof.
  intros.
  eapply (cancelL (transport_const (rho a) _)).
  refine ((apD_const _ (rho a))^ @ _).
  srapply @FMG_ind_beta_rho.
Defined.

End FMG_rec.

Section FMG_rec_trunc.

Lemma FMG_rec_to_set
  (A : Type)
  (e' : A)
  (iota' : X -> A)
  (m' : A -> A -> A)
  (alpha' : @IsAssociative A m')
  (lambda' : @IsLeftUnital A e' m')
  (rho' : @IsRightUnital A e' m')
  (T' : IsTrunc 0 A)
  : FMG X -> A.
Proof.
  refine (@FMG_rec A e' iota' m' alpha' lambda' rho' _ _ _);
  [unfold IsPentagonCoherent | unfold IsTriangleCoherent];
  intros; apply T'.
Defined.

Lemma FMG_rec_to_prop
  (A : Type)
  (e' : A)
  (iota' : X -> A)
  (m' : A -> A -> A)
  (T' : IsTrunc (-1) A)
  : FMG X -> A.
Proof.
  srapply (@FMG_rec_to_set A e' iota' m');
  [unfold IsAssociative | unfold IsLeftUnital | unfold IsRightUnital];
  intros; apply T'.
Defined.

End FMG_rec_trunc.

End FMG.

Arguments mm {X} {_} {_} {_} {_} p q.

Arguments alpha {X} _ _ _.
Arguments lambda {X} _.
Arguments rho {X} _.
Arguments pentagon {X} _ _ _ _.
Arguments triangle {X} _ _.
Arguments T_FMG {X} _ _ _ _ _ _.

Definition FMG_MG (X : Type) {T_X : IsHSet X} : MonoidalGroupoid
  := Build_MonoidalGroupoid (FMG X) T_FMG e m alpha lambda rho pentagon triangle.

Lemma FMG_rec_MonoidalFunctor (X : Type) (T_X : IsHSet X)
  (M : MonoidalGroupoid) (iota' : X -> M)
  : MonoidalFunctor (FMG_MG X) M.
Proof.
  srefine (let fmgrec := (FMG_rec X M mg_e iota' mg_m mg_alpha mg_lambda mg_rho mg_pentagon mg_triangle mgtrunc) in
    @Build_MonoidalFunctor (FMG_MG X) M fmgrec _ _ _ _ _);
  try constructor;
  intros; simpl;
  refine (_ @ (concat_1p _)^).
  + refine (concat_p1 _ @ _).
    exact (FMG_rec_beta_alpha X M mg_e iota' mg_m mg_alpha mg_lambda mg_rho mg_pentagon mg_triangle mgtrunc a b c)^.
  + exact (FMG_rec_beta_lambda X M mg_e iota' mg_m mg_alpha mg_lambda mg_rho mg_pentagon mg_triangle mgtrunc b)^.
  + exact (FMG_rec_beta_rho X M mg_e iota' mg_m mg_alpha mg_lambda mg_rho mg_pentagon mg_triangle mgtrunc a)^.
Defined.

Section Redefinitions.

Context {X : Type} {T_X : IsHSet X}.

Definition alpha_FMG_natural {a b c a' b' c' : FMG X} (pa : a = a') (pb : b = b') (pc : c = c')
  := @alpha_natural (FMG_MG X) a b c a' b' c' pa pb pc.

Definition lambda_FMG_natural {b b' : FMG X} (pb : b = b')
  := @lambda_natural (FMG_MG X) b b' pb.

Definition rho_FMG_natural {a a' : FMG X} (pa : a = a')
  := @rho_natural (FMG_MG X) a a' pa.

Definition rho_FMG_a_e (a : FMG X)
  := @rho_a_e (FMG_MG X) a.

Definition lambda_FMG_e_b (b : FMG X)
  := @lambda_e_b (FMG_MG X) b.

Definition alpha_lambda_FMG (a b : FMG X)
  := @alpha_lambda (FMG_MG X) a b.

Definition alpha_rho_FMG (a b : FMG X)
  := @alpha_rho (FMG_MG X) a b.

Definition lambda_rho_FMG_e
  := @lambda_rho_e (FMG_MG X).

End Redefinitions.