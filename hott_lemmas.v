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

End ap_multiple_variables.


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