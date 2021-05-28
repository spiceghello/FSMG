Require Export HoTT.
Require Export UnivalenceImpliesFunext.

(** Simple path algebra **)
Section path_algebra.

Lemma concat_pq_1 {A} {x} {y} {p : x = y :> A} {q : y = x}
  : p @ q = idpath -> p = q^.
Proof.
  induction q; intro h.
  exact ((concat_p1 p)^ @ h).
Defined.

Lemma concat_1_pq {A} {x} {y} {p : x = y :> A} {q : y = x}
  : p = q^ -> p @ q = idpath.
Proof.
  induction q; intro h.
  exact (concat_p1 p @ h).
Defined.

Lemma homotopy_square {A B} {f g : A -> B} (h : f == g)
  {x y : A} (p : x = y)
  : h x @ ap g p = ap f p @ h y.
Proof.
  induction p; exact (concat_p1 _ @ (concat_1p _)^).
Defined.

End path_algebra.


(** About transport and concatenation of pathovers **)
Section transport.

Definition concat_D {A} {B : A -> Type}
  {a b c : A} {p : a = b} {q : b = c}
  {x : B a} {y : B b} {z : B c}
  (p' : transport B p x = y) (q' : transport B q y = z)
  : transport B (p @ q) x = z.
Proof.
  induction p', q', p, q; constructor.
Defined.

  (**) Section concat_D_lemmas.

  Context {A} {B : A -> Type}.

  Definition concat_D_cancelR
    {a b c : A} {p : a = b} {q : b = c}
    {x : B a} {y : B b} {z z' : B c}
    (p' : transport B p x = y) (q' : transport B q y = z) (r : z = z')
    : concat_D p' (q' @ r) = concat_D p' q' @ r.
  Proof.
    induction p', q', p, q, r; constructor.
  Defined.

  Definition concat_D_cancelL
    {a b c : A} {p : a = b} {q : b = c}
    {x : B a} {y y' : B b} {z : B c}
    (p' : transport B p x = y) (q' : transport B q y' = z) (r : y = y')
    : concat_D (p' @ r) q' = concat_D p' (ap (transport B q) r @ q').
  Proof.
    induction p', q', p, q, r; constructor.
  Defined.

  Definition concat_D_concat_D_p
    {a b c d : A} {p : a = b} {q : b = c} {r : c = d}
    {x : B a} {y : B b} {z : B c} {w : B d}
    (p' : p # x = y) (q' : q # y = z) (r' : r # z = w)
    : concat_D (concat_D p' q') r'
      = ap (fun h : a = d => transport B h x) (concat_pp_p p q r) @ concat_D p' (concat_D q' r').
  Proof.
    induction p', q', r', p, q, r; constructor.
  Defined.

  Definition concat_D_p_concat_D
    {a b c d : A} {p : a = b} {q : b = c} {r : c = d}
    {x : B a} {y : B b} {z : B c} {w : B d}
    (p' : p # x = y) (q' : q # y = z) (r' : r # z = w)
    : concat_D p' (concat_D q' r')
      = ap (fun h : a = d => transport B h x) (concat_p_pp p q r) @ concat_D (concat_D p' q') r'.
  Proof.
    induction p', q', r', p, q, r; constructor.
  Defined.

  End concat_D_lemmas.

(**) Definition concat_D_const {A B}
  {a b c : A} (p : a = b) (q : b = c) (x : B)
  : concat_D (transport_const p x) (transport_const q x) = transport_const (p @ q) x.
Proof.
  induction p, q; constructor.
Defined.

Definition concat_D_const_p {A B}
  {a b c : A} {p : a = b} {q : b = c}
  {x y z : B} (p' : x = y) (q' : y = z)
  : concat_D (transport_const p x @ p') (transport_const q y @ q') = transport_const (p @ q) x @ (p' @ q').
Proof.
  induction p, q, p', q'; constructor.
Defined.

Definition transport_const_pq {A B}
  {x y : A} {p q : x = y} (f : p = q) (b : B)
  : ap (fun z => transport (fun _ => B) z b) f @ transport_const q b = transport_const p b.
Proof.
  induction f, p; constructor.
Defined.

Lemma transport_1_const {A B}
  {x : A} {y : B}
  : @transport_1 A (fun _ => B) x y
    = @transport_const A B x x idpath y @ idpath.
Proof.
  constructor.
Defined.

Lemma transport_forall'
  {A B C} (f g : A -> B -> C)
  {x1 x2 : A} (p : x1 = x2)
  (x' : forall b, f x1 b = g x1 b)
  (y : B)
  : transport (fun a : A => forall b : B, f a b = g a b) p x' y
    = (ap (fun a : A => f a y) p)^ @ (x' y @ ap (fun a : A => g a y) p).
Proof.
  induction p; simpl.
  refine ((concat_p1 _)^ @ (concat_1p _)^).
Defined.

Lemma transport_ap {A} (B : A -> Type)
  (f : A -> A) (g : forall a, B a -> B (f a))
  {x y : A} (p : x = y) {x' : B x} {y' : B y}
  (h : transport B p x' = y')
  : transport B (ap f p) (g x x') = g y y'.
Proof.
  refine (_ @ ap (g y) h).
  induction p. constructor.
Defined.

(**) Lemma transport_ap_transport_const {A B}
  (f : A -> A) (g : B -> B)
  {x y : A} (p : x = y) {x' : B}
  : @transport_ap A (fun _ => B) f (fun _ => g) x y p x' x' (transport_const p x')
    = transport_const (ap f p) (g x').
Proof.
  induction p; constructor.
Defined.

Lemma transport_ap_transport_const_p {A B}
  (f : A -> A) (g : B -> B)
  {x y : A} (p : x = y) {x' y' : B} (q : x' = y')
  : @transport_ap A (fun _ => B) f (fun _ => g) x y p x' y' (transport_const p x' @ q)
    = transport_const (ap f p) (g x') @ ap g q.
Proof.
  induction p, q; constructor.
Defined.

End transport.


(** About application of multivariable functions (ap011) **)
Section ap_multiple_variables.

Context {A B C} (f : A -> B -> C).

Lemma ap011_VV
  {x x' : A} {y y' : B}
  (p : x = x') (q : y = y')
  : ap011 f p^ q^ = (ap011 f p q)^.
Proof.
  induction p, q; constructor.
Defined.

Lemma ap011_pqpq
  {x x' x'' : A} {y y' y'' : B}
  (p : x = x') (p' : x' = x'') (q : y = y') (q' : y' = y'')
  : ap011 f p q @ ap011 f p' q' = ap011 f (p @ p') (q @ q').
Proof.
  induction p, p', q, q'; constructor.
Defined.

Lemma ap011_1qpq
  {x x' : A} {y y' y'' : B}
  (p : x = x') (q : y = y') (q' : y' = y'')
  : ap011 f idpath q @ ap011 f p q' = ap011 f p (q @ q').
Proof.
  induction p, q, q'; constructor.
Defined.

Lemma ap011_p1pq
  {x x' x'' : A} {y y' : B}
  (p : x = x') (p' : x' = x'') (q : y = y')
  : ap011 f p idpath @ ap011 f p' q = ap011 f (p @ p') q.
Proof.
  induction p, p', q; constructor.
Defined.

Lemma ap011_pq1q
  {x x' : A} {y y' y'' : B}
  (p : x = x') (q : y = y') (q' : y' = y'')
  : ap011 f p q @ ap011 f idpath q' = ap011 f p (q @ q').
Proof.
  induction p, q, q'; constructor.
Defined.

Lemma ap011_pqp1
  {x x' x'' : A} {y y' : B}
  (p : x = x') (p' : x' = x'') (q : y = y')
  : ap011 f p q @ ap011 f p' idpath = ap011 f (p @ p') q.
Proof.
  induction p, p', q; constructor.
Defined.

Lemma ap011_1qp1
  {x x' : A} {y y' : B}
  (p : x = x') (q : y = y')
  : ap011 f idpath q @ ap011 f p idpath = ap011 f p q.
Proof.
  induction p, q; constructor.
Defined.

Lemma ap011_p11q
  {x x' : A} {y y' : B}
  (p : x = x') (q : y = y')
  : ap011 f p idpath @ ap011 f idpath q = ap011 f p q.
Proof.
  induction p, q; constructor.
Defined.

Lemma ap011_1p
  {x : A} {y y' : B}
  (q : y = y')
  : ap011 f (idpath x) q = ap (f x) q.
Proof.
  induction q; constructor.
Defined.

Lemma ap011_p1
  {x x' : A} {y : B}
  (p : x = x')
  : ap011 f p (idpath y) = ap (fun z => f z y) p.
Proof.
  induction p; constructor.
Defined.

(**) Lemma ap011_1pp
  {x : A} {y y' y'' : B}
  (p : y = y') (p' : y' = y'')
  : ap011 f (idpath x) (p @ p') = ap011 f 1 p @ ap011 f 1 p'.
Proof.
  induction p, p'; constructor.
Defined.

(**) Lemma ap011_pp1
  {x x' x'' : A} {y : B}
  (p : x = x') (p' : x' = x'')
  : ap011 f (p @ p') (idpath y) = ap011 f p 1 @ ap011 f p' 1.
Proof.
  induction p, p'; constructor.
Defined.

End ap_multiple_variables.


(** About paths in Sigma-types **)
Section sigma.

Lemma path_sigma'_concat (* formerly path2_sigma' *)
  {A : Type} (P : A -> Type)
  {x x' x'' : A} {y : P x} {y' : P x'} {y'' : P x''}
  (p : x = x') (p' : x' = x'') (q : p # y = y') (q' : p' # y' = y'')
  : path_sigma' P p q @ path_sigma' P p' q' = path_sigma' P (p @ p') (concat_D q q').
Proof.
  induction p, p', q, q'; constructor.
Defined.

Lemma sigma_truncfib
  {A : Type} (P : A -> Type)
  {x x' : A} {y : P x} {y' : P x'}
  (T : forall a : A, IsHProp (P a))
  (p : x = x')
  : (x; y) = (x'; y').
Proof.
  refine (path_sigma' _ p _).
  apply path_ishprop.
Defined.

Lemma sigma_truncfib_concat
  {A : Type} (P : A -> Type)
  {x x' x'' : A} {y : P x} {y' : P x'} {y'' : P x''}
  (T : forall a : A, IsHProp (P a))
  (p : x = x') (p' : x' = x'')
  : @sigma_truncfib A P _ _ y y' T p @ @sigma_truncfib A P _ _ y' y'' T p'
    = @sigma_truncfib A P _ _ y y'' T (p @ p').
Proof.
  unfold sigma_truncfib; simpl.
  refine (path_sigma'_concat P p p' _ _ @ _).
  apply ap. srapply @path_ishprop.
Defined.

Lemma sigma_truncfib_1
  {A : Type} (P : A -> Type)
  {x : A} (y : P x)
  (T : forall a : A, IsHProp (P a))
  (p : x = x) (r : p = idpath)
  : @sigma_truncfib A P x x y y T p = idpath.
Proof.
  rewrite r.
  change (path_sigma' P idpath (path_ishprop (transport P 1 y) y) = path_sigma' P idpath idpath).
  apply ap. srapply @path_ishprop.
Defined.

End sigma.

(** About function extensionality (used for symmetric monoidality) **)
Section funext_algebra.

Context `{Funext}.

Lemma ap_apD10inv
  {A B} {f g : A -> B}
  (h : forall a, f a = g a)
  (a : A)
  : ap (fun k : A -> B => k a) (apD10^-1 h) = h a.
Proof.
  change (apD10 (apD10^-1 h) a = h a).
  revert a. apply apD10. apply eisretr.
Defined.

(**) Lemma ap_apD10inv_D
  {A} {P : A -> Type}
  {f g : forall a, P a}
  (h : forall a, f a = g a)
  (a : A)
  : ap (fun q : forall a : A, P a => q a) (apD10^-1 h) = h a.
Proof.
  change (apD10 (apD10^-1 h) a = h a).
  revert a. apply apD10. apply eisretr.
Defined.

Lemma ap_pf
  {A B} {f g : A -> B}
  (h : forall a, f a = g a)
  (a : A)
  : ap (fun k : A -> B => k a) (path_forall f g h) = h a.
Proof.
  unfold path_forall. apply ap_apD10inv.
Defined.

(**) Lemma ap_pf_D
  {A} {P : A -> Type}
  {f g : forall a, P a}
  (h : forall a, f a = g a)
  (a : A)
  : ap (fun q : forall a : A, P a => q a) (path_forall f g h) = h a.
Proof.
  unfold path_forall. apply ap_apD10inv_D.
Defined.

Lemma ap_apD10inv_2 (* apD10^-1 respects postcomposition *)
  {A B} {f g : A -> B} {h : A -> A} {c : B -> B}
  (k : forall a, f a = g a)
  : ap (fun (z : A -> B) (x : A) => c (z x)) (apD10^-1 (fun x : A => k (h x))) = apD10^-1 (fun x => ap c (k (h x))).
Proof.
  refine ((eissect apD10 _)^ @ _). apply ap.
  apply path_forall. intro a.
  refine (@ap10_ap_postcompose A B B c _ _ _ _ @ _).
  apply ap.
  change (apD10 (apD10^-1 (k o h)) a = (k o h) a).
  refine (@apD10 _ _ (apD10 (apD10^-1 (k o h))) (k o h) _ a).
  apply eisretr.
Defined.

Lemma ap_pf_2
  {A B} {f g : A -> B} {h : A -> A} {c : B -> B}
  (k : forall a, f a = g a)
  : ap (fun (z : A -> B) (x : A) => c (z x)) (path_forall _ _ (k o h)) = path_forall _ _ (fun x => ap c (k (h x))).
Proof.
  unfold path_forall. apply ap_apD10inv_2.
Defined.

End funext_algebra.

(** On connectedness **)
Section connectedness.

Context `{Univalence}.

Definition path_connected
  (A : Type) {C : Contr (Trunc 0 A)} (x y : A)
  : merely (x = y).
Proof.
  refine ((equiv_path_Tr x y)^-1 (path_contr (tr x) (tr y))).
Defined.

Lemma conn_to_prop {A : Type} {C : Contr (Trunc 0 A)}
  (P : A -> Type) (T : forall a : A, IsHProp (P a))
  : forall a0 : A, P a0 -> forall a : A, P a.
Proof.
  intros a0 y a.
  set (p := path_connected A a0 a).
  generalize p; clear p. srapply @Trunc_rec; intro p.
  exact (transport P p y).
Defined.

Lemma conn_to_prop_at_point {A : Type} {C : Contr (Trunc 0 A)}
  (P : A -> Type) (T : forall a : A, IsHProp (P a))
  (a0 : A) (a0' : P a0)
  : @conn_to_prop A C P T a0 a0' a0 = a0'.
Proof.
  srapply @path_ishprop.
Defined.

End connectedness.

(** About paths in the universe and truncation of types **)
Section universe.
Context `{Univalence}.

Lemma equiv_idmap_sum
  (A B : Type)
  : equiv_idmap A +E equiv_idmap B = equiv_idmap (A + B).
Proof.
  apply path_equiv. apply path_forall.
  intros [a|b]; constructor.
Defined.

Lemma ap011_path_universe_uncurried_sum
  {A A' B B' : Type} (e : A <~> A') (f : B <~> B')
  : ap011 (fun X Y : Type => (X + Y)%type) (path_universe_uncurried e) (path_universe_uncurried f) = path_universe_uncurried (e +E f).
  Proof.
    srefine (@equiv_induction _ A (fun A' e => ap011 (fun X Y : Type => (X + Y)%type) (path_universe_uncurried e) (path_universe_uncurried f) = path_universe_uncurried (e +E f)) _ A' e); simpl.
    srefine (@equiv_induction _ B (fun B' f => ap011 (fun X Y : Type => (X + Y)%type) (path_universe_uncurried 1) (path_universe_uncurried f) = path_universe_uncurried (1 +E f)) _ B' f); simpl.
    change (ap011 (fun X Y : Type => (X + Y)%type) (path_universe (equiv_idmap A)) (path_universe (equiv_idmap B)) = path_universe_uncurried (equiv_idmap A +E equiv_idmap B)).
    refine (ap011 (ap011 (fun X Y : Type => (X + Y)%type)) path_universe_1 path_universe_1 @ _); simpl.
    change (idpath = path_universe (equiv_idmap A +E equiv_idmap B)).
    refine (path_universe_1^ @ _).
    change (path_universe_uncurried (equiv_idmap (A + B)) = path_universe_uncurried (equiv_idmap A +E equiv_idmap B)).
    apply ap. symmetry. apply equiv_idmap_sum.
Defined.

Lemma ap011_path_universe_uncurried_sum_e1
  {A A' B : Type} (e : A <~> A')
  : ap011 (fun X Y : Type => (X + Y)%type) (path_universe_uncurried e) idpath = path_universe_uncurried (e +E equiv_idmap B).
  Proof.
    refine (ap (ap011 (fun X Y : Type => (X + Y)%type) (path_universe_uncurried e)) path_universe_1^ @ _).
    apply ap011_path_universe_uncurried_sum.
Defined.

Lemma ap011_path_universe_uncurried_sum_1e
  {A B B' : Type} (f : B <~> B')
  : ap011 (fun X Y : Type => (X + Y)%type) idpath (path_universe_uncurried f) = path_universe_uncurried (equiv_idmap A +E f).
  Proof.
    refine (ap (fun z => ap011 (fun X Y : Type => (X + Y)%type) z (path_universe_uncurried f)) path_universe_1^ @ _).
    apply ap011_path_universe_uncurried_sum.
Defined.

Definition trunc_sigma'
  {A : Type} {B : A -> Type} {n : trunc_index}
  {TB : forall a : A, IsTrunc n.+1 (B a)}
  {Ts : forall p q : sig B, IsTrunc n (p.1 = q.1)}
  : IsTrunc n.+1 (sig B).
Proof.
  intros x y.
  enough (Tp : (IsTrunc n {p : x.1 = y.1 & transport B p x.2 = y.2})).
  { revert Tp. srapply @trunc_equiv'.
  exact (Build_Equiv _ _ (path_sigma_uncurried B x y) _). }
  srapply @trunc_sigma.
Defined.

Definition hset_Finite
  (A : Type)
  : Finite A -> IsHSet A.
Proof.
  intros [n t]; revert t; srapply @Trunc_rec; intro e.
  exact (@trunc_equiv' (Fin n) A e^-1 0 _).
Defined.

End universe.