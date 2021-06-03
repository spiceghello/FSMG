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

Lemma homotopy_square_2
  {A B} (f : A -> B)
  (m : A -> A -> A) (m' : B -> B -> B)
  (h2 : forall a a' : A, m' (f a) (f a') = f (m a a'))
  {x x' y y' : A} (p : x = x') (q : y = y')
  : h2 x y @ ap f (ap011 m p q) = ap011 m' (ap f p) (ap f q) @ h2 x' y'.
Proof.
  induction p, q; exact (concat_p1 _ @ (concat_1p _)^).
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

Lemma transport_ap' {A : Type} {B : A -> Type} {A' : Type} {B' : A' -> Type}
  (f : A -> A') (g : forall a : A, B a -> B' (f a))
  {x y : A} (p : x = y) {x' : B x} {y' : B y}
  (h : transport B p x' = y')
  : transport B' (ap f p) (g x x') = g y y'.
Proof.
  refine (_ @ ap (g y) h).
  induction p. constructor.
Defined.

(** For indexed families **)

Open Scope nat.

Lemma transport_ap_nat {A : nat -> Type} {B : forall n : nat, A n -> Type}
  (f : forall n : nat, A n -> A n.+1) (g : forall (n : nat) (a : A n), B n a -> B n.+1 (f n a))
  {n : nat} {x y : A n} (p : x = y) {x' : B n x} {y' : B n y}
  (h : transport (B n) p x' = y')
  : transport (B n.+1) (ap (f n) p) (g n x x') = g n y y'.
Proof.
  refine (_ @ ap (g n y) h).
  induction p. constructor.
Defined.

Lemma transport_ap_nat_const {A B : nat -> Type}
  (f : forall n : nat, A n -> A n.+1) (g : forall (n : nat), B n -> B n.+1)
  {n : nat} {x y : A n} (p : x = y) {x' y' : B n}
  (h : transport (fun _ : A n => B n) p x' = y')
  : transport_ap_nat f (fun n _ => g n) p h
    = transport_const (ap (f n) p) (g n x') @ ap (g n) ((transport_const p x')^ @ h).
Proof.
  induction p, h. constructor.
Defined.

Lemma transport_ap_nat_transport_const {A B : nat -> Type}
  (f : forall n : nat, A n -> A n.+1) (g : forall (n : nat), B n -> B n.+1)
  {n : nat} {x y : A n} (p : x = y) {x' : B n}
  : @transport_ap_nat A (fun n _ => B n) f (fun n _ => g n) n x y p x' x' (transport_const p x')
    = transport_const (ap (f n) p) (g n x').
Proof.
  induction p; constructor.
Defined.

Lemma transport_ap_nat_transport_const_p {A B : nat -> Type}
  (f : forall n : nat, A n -> A n.+1) (g : forall (n : nat), B n -> B n.+1)
  {n : nat} {x y : A n} (p : x = y) {x' y' : B n} (q : x' = y')
  : @transport_ap_nat A (fun n _ => B n) f (fun n _ => g n) n x y p x' y' (transport_const p x' @ q)
    = transport_const (ap (f n) p) (g n x') @ ap (g n) q.
Proof.
  induction p, q; constructor.
Defined.

(** Transport in families of functions with identity types as target **)

Lemma transport_forall_fun_path
  {A : Type} {B C : A -> Type} (f g : forall a : A, C a)
  {x1 x2 : A} (p : x1 = x2)
  (x' : B x1 -> f x1 = g x1)
  (y : B x2)
  : transport (fun a : A => B a -> f a = g a) p x' y
    = (apD f p)^ @ ap (transport C p) (x' (transport B p^ y)) @ (apD g p).
Proof.
  induction p; simpl.
  induction (x' y); constructor.
Defined.

Lemma transport_forall_fun_path_idmap_r
  {A : Type} {B : A -> Type} (f : A -> A)
  {x1 x2 : A} (p : x1 = x2)
  (x' : B x1 -> f x1 = x1)
  (y : B x2)
  : transport (fun a : A => B a -> f a = a) p x' y = (ap f p)^ @ x' (transport B p^ y) @ p.
Proof.
  induction p; simpl.
  induction (x' y); constructor.
Defined.

Lemma transport_forall_fun_path_idmap_l
  {A : Type} {B : A -> Type} (g : A -> A)
  {x1 x2 : A} (p : x1 = x2)
  (x' : B x1 -> x1 = g x1)
  (y : B x2)
  : transport (fun a : A => B a -> a = g a) p x' y = p^ @ x' (transport B p^ y) @ (ap g p).
Proof.
  induction p; simpl.
  induction (x' y); constructor.
Defined.

Lemma transport_forall_fun_path_const_l_idmap_r
  {A : Type} {B : A -> Type} (a0 : A)
  {x1 x2 : A} (p : x1 = x2)
  (x' : B x1 -> a0 = x1)
  (y : B x2)
  : transport (fun a : A => B a -> a0 = a) p x' y = x' (transport B p^ y) @ p.
Proof.
  induction p; simpl.
  induction (x' y); constructor.
Defined.

Lemma transport_forall_fun_path_idmap_l_const_r
  {A : Type} {B : A -> Type} (a0 : A)
  {x1 x2 : A} (p : x1 = x2)
  (x' : B x1 -> x1 = a0)
  (y : B x2)
  : transport (fun a : A => B a -> a = a0) p x' y = p^ @ x' (transport B p^ y).
Proof.
  induction p; simpl.
  induction (x' y); constructor.
Defined.

Lemma transport_forall_fun_path_const_l_Fr
  {A : Type} {B : A -> Type} {C : Type} (c0 : C)
  {x1 x2 : A} (p : x1 = x2)
  (g : A -> C)
  (x' : B x1 -> c0 = g x1)
  (y : B x2)
  : transport (fun a : A => B a -> c0 = g a) p x' y = x' (transport B p^ y) @ ap g p.
Proof.
  induction p; simpl.
  induction (x' y); constructor.
Defined.

Lemma transport_forall_fun_path_Fl_const_r
  {A : Type} {B : A -> Type} {C : Type} (c0 : C)
  {x1 x2 : A} (p : x1 = x2)
  (f : A -> C)
  (x' : B x1 -> f x1 = c0)
  (y : B x2)
  : transport (fun a : A => B a -> f a = c0) p x' y = ap f p^ @ x' (transport B p^ y).
Proof.
  induction p; simpl.
  induction (x' y); constructor.
Defined.

End transport.


(** About application of multivariable functions (ap011) **)
Section ap_multiple_variables.

Lemma ap011_path_prod' {A A' B B' C C' : Type}
  (f : A -> B -> C) (f' : A' -> B' -> C')
  {a1 a2 : A} (p : a1 = a2) {a'1 a'2 : A'} (p' : a'1 = a'2)
  {b1 b2 : B} (q : b1 = b2) {b'1 b'2 : B'} (q' : b'1 = b'2)
  : ap011 (fun (X : A * A') (Y : B * B') => (f (fst X) (fst Y), f' (snd X) (snd Y))) (path_prod' p p') (path_prod' q q') = path_prod' (ap011 f p q) (ap011 f' p' q').
Proof.
  induction p, p', q, q'; constructor.
Defined.

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


(** About functions and paths in Sigma-types **)
Section sigma.

Lemma ap_sigma_ap_fiber {A} (B : A -> Type) {C}
  (f : sig B -> C)
  {a : A} {b b' : B a} (p : b = b')
  : ap f (path_sigma' _ idpath p) = ap (fun z : B a => f (a; z)) p.
Proof.
  induction p; constructor.
Defined.

Lemma path_sigma'_ap'
  {A : Type} (P : A -> Type) {A' : Type} (P' : A' -> Type)
  (F1 : A -> A') (F2 : forall a : A, P a -> P' (F1 a))
  {x x' : A} {y : P x} {y' : P x'} (p : x = x') (p' : transport P p y = y')
  : ap (fun z : {a : A & P a} => (F1 z.1; F2 z.1 z.2)) (path_sigma' P p p')
    = path_sigma' P' (ap F1 p) (transport_ap' F1 F2 p p').
Proof.
  induction p, p'; constructor.
Defined.

Lemma path_sigma'_ap'_p
  {A : Type} (P : A -> Type) {A' : Type} (P' : A' -> Type)
  (F1 : A -> A') (F2 : forall a : A, P a -> P' (F1 a))
  {x x' : A} {y : P x} {y' : P x'} (p : (x; y) = (x'; y'))
  : ap (fun z : {a : A & P a} => (F1 z.1; F2 z.1 z.2)) p
    = path_sigma' P' (ap F1 p..1) (transport_ap' F1 F2 p..1 p..2).
Proof.
  induction p; constructor.
Defined.

Lemma path_path_sigma'_concat
  {A : Type} (P : A -> Type)
  {x x' x'' : A} {y : P x} {y' : P x'} {y'' : P x''}
  (p : x = x') (q : x' = x'')
  (p' : transport P p y = y')
  (q' : transport P q y' = y'')
  : path_sigma' P p p' @ path_sigma' P q q' = path_sigma' P (p @ q) (concat_D p' q').
Proof.
  induction p, q, p', q'; constructor.
Defined.

Lemma path_sigma'_pr1
  {A : Type} {P : A -> Type}
  {x x' : A} {y : P x} {y' : P x'}
  (p : x = x') {p' : p # y = y'}
  : ap pr1 (path_sigma' P p p') = p.
Proof.
  induction p, p'; constructor.
Defined.

Definition sigma_function
  {A : Type} {P : A -> Type} {A' : Type} {P' : A' -> Type}
  (F1 : A -> A') (F2 : forall a : A, P a -> P' (F1 a))
  : sig P -> sig P'.
Proof.
  intros [a b]. exact (F1 a; F2 a b).
Defined.

Lemma sigma_function_equiv
  {A : Type} {P : A -> Type} {A' : Type} {P' : A' -> Type}
  (F1 : A <~> A') (F2 : forall a : A, P a <~> P' (F1 a))
  : sig P <~> sig P'.
Proof.
  srapply @equiv_adjointify.
  + exact (sigma_function F1 F2).
  + refine (sigma_function F1^-1 _).
    intros a' b'. exact ((F2 (F1^-1 a'))^-1 (transport P' (eisretr F1 a')^ b')).
  + unfold Sect; intros [a' b'].
    unfold sigma_function. srapply @path_sigma'.
    - apply eisretr.
    - refine (ap (fun z => transport P' (eisretr F1 a') z) (eisretr (F2 (F1^-1 a')) _) @ _).
      refine ((transport_pp _ _ _ _)^ @ _).
      exact (ap (fun z => transport P' z b') (concat_Vp _)).
  + unfold Sect; intros [a b].
    unfold sigma_function. srapply @path_sigma'.
    - apply eissect.
    - path_via (transport P (eissect F1 a) ((F2 (F1^-1 (F1 a)))^-1 (transport P' (ap F1 (eissect F1 a)^) ((F2 a) b)))).
        { apply ap. apply ap. refine (ap (fun z => transport P' z _) _). refine (_ @ (ap_V _ _)^). apply ap. apply eisadj. }
      refine (ap (transport P (eissect F1 a)) (ap ((F2 (F1^-1 (F1 a)))^-1) (@transport_ap' A P A' P' F1 F2 _ _ (eissect F1 a)^ b (transport P (eissect F1 a)^ b) idpath)) @ _).
      path_via (transport P (eissect F1 a) (transport P (eissect F1 a)^ b)).
        { apply ap. apply eissect. }
      refine ((transport_pp _ _ _ _)^ @ _).
      exact (ap (fun z => transport P z b) (concat_Vp _)).
Defined.

Lemma path_sigma_function
  {A : Type} {P : A -> Type} {A' : Type} {P' : A' -> Type}
  (F1 : A -> A') (F2 : forall a : A, P a -> P' (F1 a))
  {x x' : A} {y : P x} {y' : P x'}
  (p : F1 x = F1 x') (q : transport P' p (F2 x y) = F2 x' y')
  : sigma_function F1 F2 (x; y) = sigma_function F1 F2 (x'; y').
Proof.
  unfold sigma_function;
  exact (path_sigma' _ p q).
Defined.

Lemma ap_sigma_function_p
  {A : Type} {P : A -> Type} {A' : Type} {P' : A' -> Type}
  (F1 : A -> A') (F2 : forall a : A, P a -> P' (F1 a))
  {x x' : A} {y : P x} {y' : P x'} (p : (x; y) = (x'; y'))
  : ap (sigma_function F1 F2) p = path_sigma_function F1 F2 (ap F1 p..1) (transport_ap' F1 F2 p..1 p..2).
Proof.
  srapply @path_sigma'_ap'_p.
Defined.

Lemma ap_sigma_function_path_sigma_function
  {A : Type} {P : A -> Type} {A' : Type} {P' : A' -> Type}
  {B : Type} {Q : B -> Type}
  (F1 : A -> A') (F2 : forall a : A, P a -> P' (F1 a))
  (G1 : A' -> B) (G2 : forall a' : A', P' a' -> Q (G1 a'))
  {x x' : A} {y : P x} {y' : P x'}
  (p : F1 x = F1 x') (q : transport P' p (F2 x y) = F2 x' y')
  : ap (sigma_function G1 G2) (path_sigma_function F1 F2 p q)
    = path_sigma_function (G1 o F1) (fun z w => G2 (F1 z) (F2 z w)) (ap G1 p) (transport_ap' G1 G2 p q).
Proof.
  change (ap (fun z : {a' : A' & P' a'} => (G1 z.1; G2 z.1 z.2)) (path_sigma' P' p q) = path_sigma' Q (ap G1 p) (transport_ap' G1 G2 p q)).
  srapply @path_sigma'_ap'.
Defined.

Lemma ap_sigma_function_path_sigma'_1
  {A} (P : A -> Type) {A'} (P' : A' -> Type)
  (F1 : A -> A') (F2 : forall a : A, P a -> P' (F1 a))
  {x : A} {y y' : P x} (p : y = y')
  : ap (sigma_function F1 F2) (path_sigma' P (idpath x) p) = path_sigma' P' (idpath (F1 x)) (ap (F2 x) p).
Proof.
  induction p; constructor.
Defined.

Lemma path_sigma'_1
  {A : Type} (P : A -> Type)
  {x : A} {y : P x}
  {p : x = x} (q : p # y = y)
  (r : p = idpath) (s : ap (fun z : x = x => transport P z y) r = q)
  : path_sigma' P p q = idpath.
Proof.
  enough (t : (p; q) = (idpath; idpath) :> {z : x = x & z # y = y}).
  { unfold path_sigma', path_sigma.
    change (path_sigma_uncurried P (x; y) (x; y) (p; q) = path_sigma_uncurried P (x; y) (x; y) (idpath; idpath)).
    apply ap; exact t. }
  srefine (path_sigma' _ r _).
  refine (@transport_paths_Fl (x = x) _ (fun z => transport P z y) p idpath y r _ @ _).
  apply moveR_Vp; refine (s^ @ (concat_p1 _)^).
Defined.

Lemma ap_to_fiber_path_sigma'_1 {A : Type} (B : A -> Type)
  {x : A} {y y' : B x} (p : y = y')
  : ap (fun b : B x => (x; b)) p = path_sigma' B idpath p.
Proof.
  induction p; constructor.
Defined.

Lemma ap_base_path_sigma'_1 {A : Type} (B : A -> Type) {C : Type}
  (f : forall a : A, B a -> C)
  {x : A} {y y' : B x} (q : y = y')
  : ap (fun z : {a : A & B a} => f z.1 z.2) (path_sigma' B idpath q) = ap (f x) q.
Proof.
  induction q; constructor.
Defined.

Lemma path_sigma'_concat
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

Lemma sigma_truncfib_pr1
  {A : Type} (P : A -> Type)
  {x x' : A} {y : P x} {y' : P x'}
  (T : forall a : A, IsHProp (P a))
  (p : x = x')
  : (@sigma_truncfib A P _ _ y y' T p)..1 = p.
Proof.
  srapply @pr1_path_sigma_uncurried.
Defined.

Lemma path_sigma_truncfib
  {A : Type} (P : A -> Type)
  {x x' : A} {y : P x} {y' : P x'}
  (p q : (x; y) = (x'; y') :> {a : A & P a})
  (T : forall a : A, IsTrunc 0 (P a))
  : ap pr1 p = ap pr1 q -> p = q.
Proof.
  intro r; srapply @path_path_sigma.
  - exact r.
  - apply path_ishprop.
Defined.

Lemma path_path_sigma'_truncfib
  {A : Type} (P : A -> Type)
  {x x' : A} {y : P x} {y' : P x'} {p q : x = x'}
  (r : p = q)
  (p' : transport P p y = y')
  (q' : transport P q y = y')
  (T : forall a : A, IsTrunc 0 (P a))
  : path_sigma' P p p' = path_sigma' P q q'.
Proof.
  srapply @path_sigma_truncfib.
  refine (path_sigma'_pr1 p @ r @ (path_sigma'_pr1 q)^).
Defined.

Section ap011_m_base_fiber.

Context {A} (B : A -> Type) {A'} (B' : A' -> Type) {A''} (B'' : A'' -> Type).

Lemma transport_ap011
  (m_base : A -> A' -> A'')
  (m_fiber : forall (a : A) (a' : A'), B a -> B' a' -> B'' (m_base a a'))
  {a1 a2 : A} (p : a1 = a2) {b1 : B a1}
  {a'1 a'2 : A'} (p' : a'1 = a'2) {b'1 : B' a'1}
  : transport B'' (ap011 m_base p p') (m_fiber a1 a'1 b1 b'1) = m_fiber a2 a'2 (transport B p b1) (transport B' p' b'1).
Proof.
  induction p, p'; constructor.
Defined.

Lemma m_base_fiber
  (m_base : A -> A' -> A'')
  (m_fiber : forall (a : A) (a' : A'), B a -> B' a' -> B'' (m_base a a'))
  : sig B -> sig B' -> sig B''.
Proof.
  intros [a b] [a' b'].
  exact (m_base a a'; m_fiber a a' b b').
Defined.

Context (m_base : A -> A' -> A'')
  (m_fiber : forall (a : A) (a' : A'), B a -> B' a' -> B'' (m_base a a')).

Lemma ap011_m_base_fiber
  {a1 a2 : A} (p : a1 = a2) {b1 : B a1} {b2 : B a2} (q : p # b1 = b2)
  {a'1 a'2 : A'} (p' : a'1 = a'2) {b'1 : B' a'1} {b'2 : B' a'2} (q' : p' # b'1 = b'2)
  : ap011 (m_base_fiber m_base m_fiber) (path_sigma' _ p q) (path_sigma' _ p' q') = path_sigma' _ (ap011 m_base p p') (transport_ap011 m_base m_fiber p p' @ ap011 (m_fiber a2 a'2) q q').
Proof.
  induction p, p', q, q'; constructor.
Defined.

Lemma ap011_m_base_fiber_sigma_truncfib
  (TB : forall a, IsHProp (B a)) (TB' : forall a', IsHProp (B' a')) (TB'' : forall a'', IsHProp (B'' a''))
  {a1 a2 : A} (p : a1 = a2) {b1 : B a1} {b2 : B a2}
  {a'1 a'2 : A'} (p' : a'1 = a'2) {b'1 : B' a'1} {b'2 : B' a'2}
  : ap011 (m_base_fiber m_base m_fiber) (sigma_truncfib B TB p) (sigma_truncfib B' TB' p') = @sigma_truncfib _ B'' (m_base a1 a'1) (m_base a2 a'2) (m_fiber _ _ b1 b'1) (m_fiber _ _ b2 b'2) TB'' (ap011 m_base p p').
Proof.
  refine (ap011_m_base_fiber p _ p' _ @ _).
  induction p, p'; simpl.
  unfold sigma_truncfib.
  apply ap. srapply @path_ishprop. 
Defined.

End ap011_m_base_fiber.

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

(* Lemma ap_apD10inv_2 (* apD10^-1 respects postcomposition *)
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
Defined. *)

Lemma ap_apD10inv_2 (* apD10^-1 respects postcomposition *)
  {A B C : Type} {f g : A -> B} {h : A -> A} {c : B -> C}
  (k : forall a : A, f a = g a)
  : ap (fun (z : A -> B) (x : A) => c (z x)) (apD10^-1 (fun x : A => k (h x))) = apD10^-1 (fun x => ap c (k (h x))).
Proof.
  refine ((eissect apD10 _)^ @ _). apply ap.
  apply path_forall. intro a.
  refine (@ap10_ap_postcompose A B C c _ _ _ _ @ _).
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

Lemma ap_compose_pf
  {A B C : Type} (f : B -> C)
  {g1 g2 : A -> B} (h : g1 == g2)
  : ap (fun (h : A -> B) (a : A) => f (h a)) (path_forall g1 g2 h) = path_forall (f o g1) (f o g2) (fun z => ap f (h z)).
Proof.
  srapply @ap_apD10inv_2.
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


(** On natural numbers **)
Section nat.

Open Scope nat.

Lemma not_sn_0 {n : nat}
  : (n.+1 = 0) -> Empty.
Proof.
  intro p.
  exact (transport (nat_rec Type Unit (fun _ _ => Empty)) p^ tt).
Defined.

Lemma sn_sm {n m : nat}
  : S n = S m -> n = m.
Proof.
  transparent assert (code : (nat -> nat -> Type)).
    { exact (fix code (m n : nat) {struct m} : Type :=
      match m with
      | 0 => match n with
         | 0 => Unit
         | _.+1 => Empty end
      | m'.+1 => match n with
         | 0 => Empty
         | n'.+1 => code m' n' end end). }
  transparent assert (r : (forall n : nat, code n n)).
    { exact (fun n : nat => nat_rect (fun n0 : nat => code n0 n0) tt (fun n0 : nat => idmap) n). }
  transparent assert (encode : (forall m n : nat, m = n -> code m n)).
    { exact (fun (m n : nat) (p : m = n) => transport (code m) p (r m)). }
  transparent assert (decode : (forall m n : nat, code m n -> m = n)).
    { exact (fix decode (m n : nat) (u : code m n) {struct m} : m = n :=
  nat_rect (fun m0 : nat => code m0 n -> m0 = n)
    (fun u0 : code 0 n =>
     match n as n0 return (code 0 n0 -> 0 = n0) with
     | 0 => fun _ : code 0 0 => idpath
     | n0.+1 => fun u1 : code 0 n0.+1 => Empty_rect (fun _ : Empty => 0 = n0.+1) u1
     end u0)
    (fun (m0 : nat) (IHm : code m0 n -> m0 = n) (u0 : code m0.+1 n) =>
     match n as n0 return (code m0.+1 n0 -> (code m0 n0 -> m0 = n0) -> m0.+1 = n0) with
     | 0 =>
         fun (u1 : code m0.+1 0) (_ : code m0 0 -> m0 = 0) => Empty_rect (fun _ : Empty => m0.+1 = 0) u1
     | n0.+1 => fun (u1 : code m0.+1 n0.+1) (_ : code m0 n0.+1 -> m0 = n0.+1) => ap S (decode m0 n0 u1)
     end u0 IHm) m u). }
  intro p.
  exact (decode n m (encode n.+1 m.+1 p)).
Defined.

Lemma not_ssn_1 {n : nat}
  : (n.+2 = 1) -> Empty.
Proof.
  intro p. exact (not_sn_0 (sn_sm p)).
Defined.

End nat.


(** On truncations **)
Section truncations.

Lemma truncmap (n : trunc_index) {A B : Type} (f : A -> B)
  : Trunc n A -> Trunc n B.
Proof.
  srapply @Trunc_rec. exact (tr o f).
Defined.

End truncations.