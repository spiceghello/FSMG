Require Export HoTT.


Definition eq_to_eqEquiv `{Funext} {A B : Type} {e e' : A <~> B} (h : equiv_fun e == equiv_fun e')
  : e = e'.
Proof.
  srapply @path_equiv.
  srapply @path_forall.
  exact h.
Defined.

Lemma ap_VV {A B : Type} (f : A -> B) {x y : A} (p : x = y)
  : (ap f p^)^ = ap f p.
Proof.
  induction p; constructor.
Defined.

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

Lemma homotopy_square {A B : Type} {f g : A -> B} (h : f == g)
  {x y : A} (p : x = y)
  : h x @ ap g p = ap f p @ h y.
Proof.
  induction p; exact (concat_p1 _ @ (concat_1p _)^).
Defined.

Section transporting_paths.

Definition transport_paths_FlFr' {A B : Type} (f g : A -> B)
  {x1 x2 : A} {p : x1 = x2} {q : f x1 = g x1}
  {r : f x2 = g x2}
  : q @ ap g p = ap f p @ r -> transport (fun x : A => f x = g x) p q = r
  := fun h => (transport_paths_FlFr p q @ concat_pp_p (ap f p)^ q (ap g p)) @ moveR_Vp (q @ ap g p) r (ap f p) h.

Definition transport_paths_r_concat_1p_coh {A : Type} {x y : A} {p q : x = y} (f : p = q)
  : (transport_paths_r p 1 @ concat_1p p) @ f =
    ((transport_paths_r p 1 @ whiskerL 1 f) @ (transport_paths_r q 1)^) @ (transport_paths_r q 1 @ concat_1p q).
Proof.
  induction f, p; constructor.
Defined.

Definition concat_D {A : Type} {B : A -> Type}
  {a b c : A} {p : a = b} {q : b = c}
  {x : B a} {y : B b} {z : B c}
  (p' : transport B p x = y) (q' : transport B q y = z)
  : transport B (p @ q) x = z.
Proof.
  induction p', q', p, q; constructor.
(*   refine (transport_pp B p q x @ ((ap _ p') @ q')). *)
Defined.

Definition concat_D_cancelR {A : Type} {B : A -> Type}
  {a b c : A} {p : a = b} {q : b = c}
  {x : B a} {y : B b} {z z' : B c}
  (p' : transport B p x = y) (q' : transport B q y = z) (r : z = z')
  : concat_D p' (q' @ r) = concat_D p' q' @ r.
Proof.
  induction p', q', p, q, r; constructor.
Defined.

Definition concat_D_cancelL {A : Type} {B : A -> Type}
  {a b c : A} {p : a = b} {q : b = c}
  {x : B a} {y y' : B b} {z : B c}
  (p' : transport B p x = y) (q' : transport B q y' = z) (r : y = y')
  : concat_D (p' @ r) q' = concat_D p' (ap (transport B q) r @ q').
Proof.
  induction p', q', p, q, r; constructor.
Defined.

Definition concat_D_transport_paths_r_pp_1 {A : Type}
  {a b c : A} (p : a = b) (q : b = c)
  : concat_D ((transport_paths_r p idpath) @ concat_1p p) (transport_paths_r q p)
    = transport_paths_r (p @ q) idpath @ (concat_1p (p @ q)).
Proof.
  induction p, q; constructor.
Defined.

Definition concat_D_concat_D_p {A : Type} {B : A -> Type}
  {a b c d : A} {p : a = b} {q : b = c} {r : c = d}
  {x : B a} {y : B b} {z : B c} {w : B d}
  (p' : p # x = y) (q' : q # y = z) (r' : r # z = w)
  : concat_D (concat_D p' q') r'
    = ap (fun h : a = d => transport B h x) (concat_pp_p p q r) @ concat_D p' (concat_D q' r').
Proof.
  induction p', q', r', p, q, r; constructor.
Defined.

Definition concat_D_p_concat_D {A : Type} {B : A -> Type}
  {a b c d : A} {p : a = b} {q : b = c} {r : c = d}
  {x : B a} {y : B b} {z : B c} {w : B d}
  (p' : p # x = y) (q' : q # y = z) (r' : r # z = w)
  : concat_D p' (concat_D q' r')
    = ap (fun h : a = d => transport B h x) (concat_p_pp p q r) @ concat_D (concat_D p' q') r'.
Proof.
  induction p', q', r', p, q, r; constructor.
Defined.

Definition concat_D_const {A B : Type}
  {a b c : A} (p : a = b) (q : b = c) (x : B)
  : concat_D (transport_const p x) (transport_const q x) = transport_const (p @ q) x.
Proof.
  induction p, q; constructor.
Defined.

Definition concat_D_const_p {A B : Type}
  {a b c : A} {p : a = b} {q : b = c}
  {x y z : B} (p' : x = y) (q' : y = z)
  : concat_D (transport_const p x @ p') (transport_const q y @ q') = transport_const (p @ q) x @ (p' @ q').
Proof.
  induction p, q, p', q'; constructor.
Defined.

Definition apD_pp {A : Type} {B : A -> Type} (f : forall a : A, B a)
  {x y z : A} (p : x = y) (q : y = z)
  : apD f (p @ q) = concat_D (apD f p) (apD f q).
Proof.
  induction p, q; constructor.
Defined.

Definition transport_const_pq {A B : Type} {x y : A} {p q : x = y} (f : p = q) (b : B)
  : ap (fun z => transport (fun _ => B) z b) f @ transport_const q b = transport_const p b.
Proof.
  induction f, p; constructor.
Defined.

Lemma apD_const' {A B : Type} {x y : A} (f : A -> B) (p : x = y)
  : ap f p = (transport_const p (f x))^ @ apD f p.
Proof.
  induction p; constructor.
Defined.

Lemma apD_idmap {A : Type} {x y : A} (p : x = y)
  : @apD A (fun _ => A) idmap _ _ p = transport_const p x @ p.
Proof.
  induction p; constructor.
Defined.

Lemma transport_apD {A B : Type} (f : A -> B) {x y : A} {p q : x = y} (r : p = q)
  : ap f p
    = (transport_const q (f x))^ @ transport (fun z : x = y => transport (fun _ : A => B) z (f x) = f y) r (apD f p).
Proof.
  induction r, p; constructor.
Defined.

Lemma ap_ap {A B : Type} (f : A -> B) {x y : A} {p q : x = y} (r : p = q)
  : ap (ap f) r
    = transport_apD f r @ whiskerL (transport_const q (f x))^ (apD (apD f) r) @ (apD_const' f q)^.
Proof.
  induction r, p; constructor.
Defined.

Definition transport_paths_FFlr_ap {A B : Type} {f : A -> B} {g : B -> A}
  {x1 x2 : A} (s : g (f x1) = x1) {p1 p2 : x1 = x2} (r : p1 = p2)
  : ap (fun z : x1 = x2 => transport (fun x : A => g (f x) = x) z s) r
    = transport_paths_FFlr p1 s @ ap (fun z : x1 = x2 => ((ap g (ap f z))^ @ s) @ z) r @ (transport_paths_FFlr p2 s)^.
Proof.
  induction r. induction p1. simpl.
  apply moveL_pV.
  refine (concat_1p _ @ (concat_p1 _)^).
Defined.

Definition transport_paths_r_ap {A : Type} {x y1 y2 : A}
  {p1 p2 : y1 = y2} (q : x = y1) (r : p1 = p2)
  : ap (fun z : y1 = y2 => transport (fun y : A => x = y) z q) r
    = (transport_paths_r p1 q) @ ap (fun z : y1 = y2 => q @ z) r @ (transport_paths_r p2 q)^.
Proof.
  induction p1, r, q; constructor.
Defined.

Definition ap_1p_concat_1p {A : Type} {x y : A} {p q : x = y} (r : p = q)
  : ap (fun z : x = y => idpath @ z) r = concat_1p p @ r @ (concat_1p q)^.
Proof.
  induction r, p; constructor.
Defined.

Definition ap_transport_paths_1 {A : Type} {x y : A} {p q : x = y} (r : p = q)
  : ap (fun z : x = y => transport (fun y : A => x = y) z idpath) r
    = transport_paths_r p idpath @ whiskerL idpath r @ (transport_paths_r q idpath)^.
Proof.
  induction r, p; constructor.
Defined.

Lemma transport_1_const {A B : Type} {x : A} {y : B}
  : @transport_1 A (fun _ => B) x y
    = @transport_const A B x x idpath y @ idpath.
Proof.
  constructor.
Defined.

End transporting_paths.


Section multiple_variables.

Lemma ap011_VV {A B C : Type} (f : A -> B -> C)
  {x x' : A} {y y' : B}
  (p : x = x') (q : y = y')
  : ap011 f p^ q^ = (ap011 f p q)^.
Proof.
  induction p, q; constructor.
Defined.

Lemma ap011_pqpq {A B C : Type} (f : A -> B -> C)
  {x x' x'' : A} {y y' y'' : B}
  (p : x = x') (p' : x' = x'') (q : y = y') (q' : y' = y'')
  : ap011 f p q @ ap011 f p' q' = ap011 f (p @ p') (q @ q').
Proof.
  induction p, p', q, q'; constructor.
Defined.

Lemma ap011_1qpq {A B C : Type} (f : A -> B -> C)
  {x x' : A} {y y' y'' : B}
  (p : x = x') (q : y = y') (q' : y' = y'')
  : ap011 f idpath q @ ap011 f p q' = ap011 f p (q @ q').
Proof.
  induction p, q, q'; constructor.
Defined.

Lemma ap011_p1pq {A B C : Type} (f : A -> B -> C)
  {x x' x'' : A} {y y' : B}
  (p : x = x') (p' : x' = x'') (q : y = y')
  : ap011 f p idpath @ ap011 f p' q = ap011 f (p @ p') q.
Proof.
  induction p, p', q; constructor.
Defined.

Lemma ap011_pq1q {A B C : Type} (f : A -> B -> C)
  {x x' : A} {y y' y'' : B}
  (p : x = x') (q : y = y') (q' : y' = y'')
  : ap011 f p q @ ap011 f idpath q' = ap011 f p (q @ q').
Proof.
  induction p, q, q'; constructor.
Defined.

Lemma ap011_pqp1 {A B C : Type} (f : A -> B -> C)
  {x x' x'' : A} {y y' : B}
  (p : x = x') (p' : x' = x'') (q : y = y')
  : ap011 f p q @ ap011 f p' idpath = ap011 f (p @ p') q.
Proof.
  induction p, p', q; constructor.
Defined.

Lemma ap011_1qp1 {A B C : Type} (f : A -> B -> C)
  {x x' : A} {y y' : B}
  (p : x = x') (q : y = y')
  : ap011 f idpath q @ ap011 f p idpath = ap011 f p q.
Proof.
  induction p, q; constructor.
Defined.

Lemma ap011_p11q {A B C : Type} (f : A -> B -> C)
  {x x' : A} {y y' : B}
  (p : x = x') (q : y = y')
  : ap011 f p idpath @ ap011 f idpath q = ap011 f p q.
Proof.
  induction p, q; constructor.
Defined.

Lemma ap011_1p {A B C : Type} (f : A -> B -> C)
  {x : A} {y y' : B}
  (q : y = y')
  : ap011 f (idpath x) q = ap (f x) q.
Proof.
  induction q; constructor.
Defined.

Lemma ap011_p1 {A B C : Type} (f : A -> B -> C)
  {x x' : A} {y : B}
  (p : x = x')
  : ap011 f p (idpath y) = ap (fun z => f z y) p.
Proof.
  induction p; constructor.
Defined.

End multiple_variables.



Section transporting.

Lemma ap_transport_const
  {A B : Type} {x1 x2 : A} (p : x1 = x2) {y1 y2 : B} (q : y1 = y2)
  : ap (transport (fun _ : A => B) p) q @ transport_const p y2
    = transport_const p y1 @ q.
Proof.
(*   exact (@concat_Ap B B (transport (fun _ : A => B) p) idmap (transport_const p) y1 y2 q @ whiskerL _ (ap_idmap _)). *)
  induction p, q; constructor.
Defined.

Lemma transport_forall'
  {A B C : Type} (f g : A -> B -> C)
  {x1 x2 : A} (p : x1 = x2)
  (x' : forall b : B, f x1 b = g x1 b)
  (y : B)
  : transport (fun a : A => forall b : B, f a b = g a b) p x' y
    = (ap (fun a : A => f a y) p)^ @ (x' y @ ap (fun a : A => g a y) p).
Proof.
  induction p; simpl.
  refine ((concat_p1 _)^ @ (concat_1p _)^).
Defined.

Lemma transport_forall''
  {A : Type} {B C : A -> Type} (f g : forall a : A, C a)
  {x1 x2 : A} (p : x1 = x2)
  (x' : forall (a : A) (b : B a), f x1 = g x1)
  (y : B x2)
  : transport (fun a : A => B a -> f a = g a) p (x' x1) y
    = (apD f p)^ @ ap (transport C p) (x' x1 (transport B p^ y)) @ (apD g p).
Proof.
  induction p; simpl.
  induction (x' x1 y); constructor.
Defined.

Lemma transport_forall''d
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

Lemma transport_forall''d_idmap_r
  {A : Type} {B : A -> Type} (f : A -> A)
  {x1 x2 : A} (p : x1 = x2)
  (x' : B x1 -> f x1 = x1)
  (y : B x2)
  : transport (fun a : A => B a -> f a = a) p x' y = (ap f p)^ @ x' (transport B p^ y) @ p.
Proof.
  induction p; simpl.
  induction (x' y); constructor.
Defined.

Lemma transport_forall''d_idmap_l
  {A : Type} {B : A -> Type} (g : A -> A)
  {x1 x2 : A} (p : x1 = x2)
  (x' : B x1 -> x1 = g x1)
  (y : B x2)
  : transport (fun a : A => B a -> a = g a) p x' y = p^ @ x' (transport B p^ y) @ (ap g p).
Proof.
  induction p; simpl.
  induction (x' y); constructor.
Defined.

Lemma transport_forall''d_const_l_idmap_r
  {A : Type} {B : A -> Type} (a0 : A)
  {x1 x2 : A} (p : x1 = x2)
  (x' : B x1 -> a0 = x1)
  (y : B x2)
  : transport (fun a : A => B a -> a0 = a) p x' y = x' (transport B p^ y) @ p.
Proof.
  induction p; simpl.
  induction (x' y); constructor.
Defined.

Lemma transport_forall''d_idmap_l_const_r
  {A : Type} {B : A -> Type} (a0 : A)
  {x1 x2 : A} (p : x1 = x2)
  (x' : B x1 -> x1 = a0)
  (y : B x2)
  : transport (fun a : A => B a -> a = a0) p x' y = p^ @ x' (transport B p^ y).
Proof.
  induction p; simpl.
  induction (x' y); constructor.
Defined.

Lemma transport_forall_nat_sigma_fst
  {A : nat -> Type}
  (B C : forall (n : nat), A n -> Type) (* X and P *)
  (D : forall (n : nat) (a : A n), B n a -> C n a -> Type)
  (fA : forall (n : nat), A n -> A n.+1)
  (fC : forall (n : nat) (a : A n), (forall b : B n a, {c : C n a & D n a b c}) -> B n.+1 (fA n a) -> C n.+1 (fA n a))
  (fD : forall (n : nat) (a : A n) (ih : forall b : B n a, {c : C n a & D n a b c}) (b : B n.+1 (fA n a)),
        D n.+1 (fA n a) b (fC n a ih b))
  {n : nat} {a a' : A n} (p : fA n a = fA n a')
  (s : forall b : B n a, {c : C n a & D n a b c})
  (y : B n.+1 (fA n a'))
  : (transport (fun a : A n.+1 => forall b : B n.+1 a, {c : C n.+1 a & D n.+1 a b c}) p (fun b : B n.+1 (fA n a) => (fC n a s b; fD n a s b)) y).1
    = transport (fun a : A n.+1 => B n.+1 a -> C n.+1 a) p (fC n a s) y.
Proof.
  induction p; constructor.
Defined.

Lemma transport_ap {A : Type} (B : A -> Type)
  (f : A -> A) (g : forall a : A, B a -> B (f a))
  {x y : A} (p : x = y) {x' : B x} {y' : B y}
  (h : transport B p x' = y')
  : transport B (ap f p) (g x x') = g y y'.
Proof.
  refine (_ @ ap (g y) h).
  induction p. constructor.
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

Lemma transport_ap_transport_const {A B : Type}
  (f : A -> A) (g : B -> B)
  {x y : A} (p : x = y) {x' : B}
  : @transport_ap A (fun _ => B) f (fun _ => g) x y p x' x' (transport_const p x')
    = transport_const (ap f p) (g x').
Proof.
  induction p; constructor.
Defined.

Lemma transport_ap_transport_const_p {A B : Type}
  (f : A -> A) (g : B -> B)
  {x y : A} (p : x = y) {x' y' : B} (q : x' = y')
  : @transport_ap A (fun _ => B) f (fun _ => g) x y p x' y' (transport_const p x' @ q)
    = transport_const (ap f p) (g x') @ ap g q.
Proof.
  induction p, q; constructor.
Defined.

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

End transporting.


Section apD10_algebra.
Context `{Funext}.

Lemma ap_apD10inv
  {A B : Type} {f g : A -> B}
  (h : forall a : A, f a = g a)
  (a : A)
  : ap (fun k : A -> B => k a) (apD10^-1 h) = h a.
Proof.
  change (apD10 (apD10^-1 h) a = h a).
  revert a. apply apD10. apply eisretr.
Defined.

Lemma ap_apD10inv_D
  {A : Type} {P : A -> Type}
  {f g : forall (a : A), P a}
  (h : forall (a : A), f a = g a)
  (a : A)
  : ap (fun q : forall a : A, P a => q a) (apD10^-1 h) = h a.
Proof.
  change (apD10 (apD10^-1 h) a = h a).
  revert a. apply apD10. apply eisretr.
Defined.

Lemma ap_pf
  {A B : Type} {f g : A -> B}
  (h : forall a : A, f a = g a)
  (a : A)
  : ap (fun k : A -> B => k a) (path_forall f g h) = h a.
Proof.
  unfold path_forall. apply ap_apD10inv.
Defined.

Lemma ap_pf_D
  {A : Type} {P : A -> Type}
  {f g : forall (a : A), P a}
  (h : forall (a : A), f a = g a)
  (a : A)
  : ap (fun q : forall a : A, P a => q a) (path_forall f g h) = h a.
Proof.
  unfold path_forall. apply ap_apD10inv_D.
Defined.

Lemma ap_apD10inv_2 (* apD10^-1 respects postcomposition *)
  {A B : Type} {f g : A -> B} {h : A -> A} {c : B -> B}
  (k : forall a : A, f a = g a)
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
  {A B : Type} {f g : A -> B} {h : A -> A} {c : B -> B}
  (k : forall a : A, f a = g a)
  : ap (fun (z : A -> B) (x : A) => c (z x)) (path_forall _ _ (k o h)) = path_forall _ _ (fun x => ap c (k (h x))).
Proof.
  unfold path_forall. apply ap_apD10inv_2.
Defined.

Lemma ap_pf2
  {A B : Type} (P : A -> B -> Type) (f g : forall (x : A) (y : B), P x y) (h : forall (x : A) (y : B), f x y = g x y)
  (a : A) (b : B)
  : ap (fun q : (forall (x : A) (y : B), P x y) => q a b) (path_forall2 f g h) = h a b.
Proof.
  unfold path_forall2.
  refine (ap_compose (fun q => q a) (fun q => q b) _ @ _).
  enough (Hh : (apD10 (ap (fun q : forall (x : A) (x0 : B), P x x0 => q a) (path_forall f g (fun x : A => path_forall (f x) (g x) (h x)))) = h a)).
    refine (ap (ap (fun q : forall x : B, P a x => q b)) ((eissect apD10 _)^ @ ap (apD10^-1) Hh) @ _).
    apply ap_apD10inv_D.
  refine (ap apD10 (@ap_pf_D A (fun a => forall b : B, P a b) f g (fun x : A => path_forall (f x) (g x) (h x)) a) @ _).
  apply eisretr.
Defined.

Context {A : Type} {P : A -> Type}.

Lemma apD10_V
  {f g : forall a : A, P a}
  (k : f = g)
  : apD10 k^ = (fun a => (apD10 k a)^).
Proof.
  induction k; constructor.
Defined.

Lemma apD10inv_V
  {f g : forall a : A, P a}
  (h : forall a : A, f a = g a)
  : apD10^-1 (fun a => (h a)^) = (apD10^-1 h)^.
Proof.
  refine (_ @ eissect apD10 (apD10^-1 h)^).
  apply ap. refine (_ @ (apD10_V (apD10^-1 h))^).
  apply path_forall; intro a; apply ap.
  exact (apD10 (eisretr apD10 h) a)^.
Defined.

Lemma apD10_pp
  {f f' f'' : forall a : A, P a}
  (k : f = f') (k' : f' = f'')
  : apD10 (k @ k') = (fun a => apD10 k a @ apD10 k' a).
Proof.
  induction k, k'; constructor.
Defined.

Lemma apD10inv_pp
  {f f' f'' : forall a : A, P a}
  (h : forall a : A, f a = f' a) (h' : forall a : A, f' a = f'' a)
  : apD10^-1 (fun a => h a @ h' a) = apD10^-1 h @ apD10^-1 h'.
Proof.
  refine (_ @ eissect apD10 _).
  apply ap. refine (_ @ (apD10_pp _ _)^).
  apply path_forall; intro a.
  apply concat2; exact (apD10 (eisretr apD10 _) a)^.
Defined.

Lemma apD10_1
  {f : forall a : A, P a}
  : apD10 (idpath f) = (fun a => idpath (f a)).
Proof.
  constructor.
Defined.

Lemma apD10inv_1
  {f : forall a : A, P a}
  : apD10^-1 (fun a => idpath (f a)) = (idpath f).
Proof.
  refine (_ @ eissect apD10 _).
  apply ap. constructor.
Defined.

Lemma apD20
  {f g : forall a : A, P a}
  {k k' : f = g}
  (r : k = k')
  : forall a : A, apD10 k a = apD10 k' a.
Proof.
  induction r; constructor.
Defined.

Lemma apD20inv
  {f g : forall a : A, P a}
  {p q : forall a : A, f a = g a}
  (r : forall a : A, p a = q a)
  : apD10^-1 p = apD10^-1 q.
Proof.
  apply ap. apply apD10^-1. exact r.
Defined.

End apD10_algebra.


Section squares.

Context {A : Type}.

Lemma split_h_rectangle {tl tc tr bl bc br : A}
  {ptl : tl = tc} {ptr : tc = tr} {pr : tr = br}
  {pl : tl = bl} {pbl : bl = bc} {pbr : bc = br}
  (q : tc = bc)
  : (ptl @ q = pl @ pbl) * (ptr @ pr = q @ pbr) ->
    (ptl @ ptr) @ pr = pl @ (pbl @ pbr).
Proof.
  intros (hl, hr).
  refine (concat_pp_p _ _ _ @ whiskerL ptl hr @ concat_p_pp _ _ _ @ whiskerR hl pbr @ concat_pp_p _ _ _).
Defined.

Lemma split_v_rectangle {tl tr cl cr bl br : A}
  {pt : tl = tr} {prt : tr = cr} {prb : cr = br}
  {plt : tl = cl} {plb : cl = bl} {pb : bl = br}
  (q : cl = cr)
  : (pt @ prt = plt @ q) * (q @ prb = plb @ pb) ->
    pt @ (prt @ prb) = (plt @ plb) @ pb.
Proof.
  intros (ht, hb).
  refine (concat_p_pp _ _ _ @ whiskerR ht prb @ concat_pp_p _ _ _ @ whiskerL plt hb @ concat_p_pp _ _ _).
Defined.

End squares.


Section sigma_truncatedness.

Definition trunc_sigma_succ (* credit: Kristian *)
  {A : Type} (B : A -> Type) (n : trunc_index)
  (A_t : forall p q : {a : A & B a}, IsTrunc n (p.1 = q.1))
  (B_t : forall a : A, IsTrunc n.+1 (B a))
  : IsTrunc n.+1 {a : A & B a}.
Proof.
  intros x y.
  enough (AB_t : IsTrunc n {p : x.1 = y.1 & transport B p x.2 = y.2}).
  + refine (trunc_equiv' {p : x.1 = y.1 & transport B p x.2 = y.2} _).
    exact (BuildEquiv _ _ (path_sigma_uncurried B x y) _).
  + apply trunc_sigma.
Defined.

(* This part is from the library! *)

Definition path_sigma_hprop_1 {A : Type} {P : A -> Type}
           `{forall x, IsHProp (P x)} (u : sigT P)
: path_sigma_hprop u u 1 = idpath.
Proof.
  unfold path_sigma_hprop.
  unfold isequiv_pr1_contr; simpl.
  refine (ap (fun p => match p in (_ = v2) return (u = (u.1; v2)) with idpath => idpath end)
             (contr (idpath u.2))).
Defined.

Definition path_sigma_hprop_V {A : Type} {P : A -> Type}
           `{forall x, IsHProp (P x)} {a b : A} (p : a = b)
           (x : P a) (y : P b)
: path_sigma_hprop (b;y) (a;x) p^ = (path_sigma_hprop (a;x) (b;y) p)^.
Proof.
  destruct p; simpl.
  rewrite (path_ishprop x y).
  refine (path_sigma_hprop_1 _ @ (ap inverse (path_sigma_hprop_1 _))^).
Qed.

Definition path_sigma_hprop_pp
           {A : Type}
           {P : A -> Type}
           `{forall x, IsHProp (P x)}
           {a b c : A}
           (p : a = b) (q : b = c)
           (x : P a) (y : P b) (z : P c)
: path_sigma_hprop (a;x) (c;z) (p @ q)
    =
  path_sigma_hprop (a;x) (b;y) p @ path_sigma_hprop (b;y) (c;z) q.
Proof.
  destruct p, q.
  rewrite (path_ishprop y x).
  rewrite (path_ishprop z x).
  refine (_ @ (ap (fun z => z @ _) (path_sigma_hprop_1 _))^).
  apply (concat_1p _)^.
Qed.

(* end of part of the library *)

Lemma path_sigma_hprop_1'
  {A : Type} (P : A -> Type) `{forall x : A, IsHProp (P x)}
  {x : A} {y y' : P x}
  : path_sigma_hprop (x; y) (x; y') idpath = ap (fun z => (x; z)) (center (y = y')).
Proof.
  induction (center (y = y')); simpl.
  exact (path_sigma_hprop_1 _).
Defined.

Definition ap_f1f2_path_sigma_hprop
  {A : Type} {P : A -> Type}
  `{forall x : A, IsHProp (P x)}
  (F1 : A -> A) (F2 : forall a : A, P a -> P (F1 a))
  {x x' : A} {y : P x} {y' : P x'} (p : x = x')
  : ap (fun c : sig P => (F1 c.1; F2 c.1 c.2)) (path_sigma_hprop (x; y) (x'; y') p) = path_sigma_hprop (F1 x; F2 x y) (F1 x'; F2 x' y') (ap F1 p).
Proof.
  induction p; simpl.
  refine (ap (ap _) (path_sigma_hprop_1' _) @ _).
  refine (_ @ (@path_sigma_hprop_1' _ _ _ (F1 x) (F2 x y) (F2 x y'))^).
  refine ((ap_compose (fun z : P x => (x; z)) (fun c : {x : _ & P x} => (F1 c.1; F2 c.1 c.2)) (center (y = y')))^ @ _).
  refine (ap_compose (fun z : P x => F2 x z) (fun z => (F1 x; z)) (center (y = y')) @ _).
  apply ap.
  srapply @path_ishprop.
Defined.

End sigma_truncatedness.


Section finitedness.

Definition IsHSet_Finite `{Funext}
  : forall A : Type, Finite A -> IsHSet A.
Proof.
  intros A [n t]. strip_truncations.
  apply (trunc_equiv' (Fin n) t^-1).
Defined.

Definition Is1Trunc_Finite `{Univalence}
  : IsTrunc 1 {A : Type & Finite A}.
Proof.
  apply trunc_sigma_succ.
  + intros A B.
    srapply @istrunc_paths_Type.
    apply IsHSet_Finite. exact B.2.
  + exact (fun a => _).
Defined.

End finitedness.


Section sigmas.

(* lemmas about sigma types with truncations, which we mainly need for BS *)

Lemma sigma_truncfib
  {A : Type} (P : A -> Type)
  {x x' : A} {y : P x} {y' : P x'}
  (T : forall a : A, IsHProp (P a))
  (p : x = x')
  : (x; y) = (x'; y').
Proof.
  srapply @path_sigma'.
  exact p.
  apply path_ishprop.
Defined.

Lemma sigma'_truncfib
  {A : Type} (P : A -> Type)
  {a b : sig P} (p : a.1 = b.1)
  (T : forall a : A, IsHProp (P a))
  : a = b.
Proof.
  refine (path_sigma P a b p _).
  apply path_ishprop.
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
  exact r.
  apply path_ishprop.
Defined.

Lemma path_sigma'_pr1
  {A : Type} {P : A -> Type}
  {x x' : A} {y : P x} {y' : P x'}
  (p : x = x') {p' : p # y = y'}
  : ap pr1 (path_sigma' P p p') = p.
Proof.
  induction p, p'; constructor.
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
(*   induction r. apply ap.
  apply path_ishprop. *)
  srapply @path_sigma_truncfib.
  refine (path_sigma'_pr1 p @ r @ (path_sigma'_pr1 q)^).
Defined.

Lemma path_path_sigma'_truncfib'
  {A : Type} (P : A -> Type)
  {x x' : A} {y : P x} {y' : P x'} {p q : x = x'}
  (r : p = q)
  (p' : transport P p y = y')
  (q' : transport P q y = y')
  (T : forall a : A, IsTrunc 0 (P a))
  : path_sigma' P p p' = path_sigma' P q (transport (fun z => transport P z y = y') r p').
Proof.
  induction r. apply ap.
  apply path_ishprop.
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

Lemma path_path_sigma'_1
  {A : Type} (P : A -> Type)
  {x : A} (y : P x)
  : path_sigma' P (idpath x) (transport_1 P y) = idpath.
Proof.
  constructor.
Defined.

Lemma path_path_sigma'_1_truncfib
  {A : Type} (P : A -> Type)
  {x : A} (y : P x)
  {refl' : transport P 1 y = y}
  (T : forall a : A, IsTrunc 0 (P a))
  : path_sigma' P (idpath x) refl' = idpath.
Proof.
  change (path_sigma' P 1 refl' = path_sigma' P idpath (transport_1 P y)).
  apply ap.
  apply path_ishprop.
Defined.

Lemma path_path_sigma'_truncfib_path_ishprop
  {A : Type} (P : A -> Type)
  {x x' : A} {p q : x = x'} (r : p = q) {y : P x} {y' : P x'}
  (T : forall a : A, IsTrunc -1 (P a))
  : path_sigma' P p (path_ishprop (transport P p y) y') = path_sigma' P q (path_ishprop (transport P q y) y').
Proof.
  induction r; constructor.
Defined.

Lemma path_sigma'_ap
  {A : Type} (P : A -> Type) {A' : Type} (P' : A' -> Type)
  (F1 : A -> A') (F2 : forall a : A, P a -> P' (F1 a))
  {x x' : A} {y : P x} {y' : P x'} (p : x = x') (p' : transport P p y = y')
  : ap (fun z : {a : A & P a} => (F1 z.1; F2 z.1 z.2)) (path_sigma' P p p') =
 path_sigma' P' (ap F1 p) (paths_rect A x (fun (x' : A) (p : x = x') => forall y' : P x', transport P p y = y' -> transport P' (ap F1 p) (F2 x y) = F2 x' y') (fun (y' : P x) (p' : transport P 1 y = y') => match p' in (_ = y0) return (transport P' (ap F1 1) (F2 x y) = F2 x y0) with | idpath => idpath end) x' p y' p').
Proof.
  induction p, p'; constructor.
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

Lemma path_sigma'_ap_truncfib
  {A : Type} (P : A -> Type) {A' : Type} (P' : A' -> Type)
  (F1 : A -> A') (F2 : forall a : A, P a -> P' (F1 a))
  {x x' : A} {y : P x} {y' : P x'} (p : x = x') (p' : transport P p y = y')
  (T : forall a' : A', IsTrunc -1 (P' a'))
  : ap (fun z : {a : A & P a} => (F1 z.1; F2 z.1 z.2)) (path_sigma' P p p') = path_sigma' P' (ap F1 p) (center (transport P' (ap F1 p) (F2 x y) = (F2 x' y'))).
Proof.
  refine (path_sigma'_ap _ _ _ _ _ _ @ _).
  apply ap.
  srapply @path_ishprop.
Defined.

Lemma path_sigma'_components
  {A : Type} (P : A -> Type)
  {x x' : A} {y : P x} {y' : P x'}
  (p : (x; y) = (x'; y'))
  : path_sigma' P p..1 p..2 = p.
Proof.
  induction p; constructor.
Defined.

Lemma ap_pr1_path_sigma'
  {A : Type} {P : A -> Type}
  {x x' : A} (p : x = x')
  {y : P x} {y' : P x'} (q : transport P p y = y')
  : ap pr1 (path_sigma' P p q) = p.
Proof.
  induction p, q; constructor.
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
        apply ap. apply ap. refine (ap (fun z => transport P' z _) _). refine (_ @ (ap_V _ _)^). apply ap. apply eisadj.
      refine (ap (transport P (eissect F1 a)) (ap ((F2 (F1^-1 (F1 a)))^-1) (@transport_ap' A P A' P' F1 F2 _ _ (eissect F1 a)^ b (transport P (eissect F1 a)^ b) idpath)) @ _).
      path_via (transport P (eissect F1 a) (transport P (eissect F1 a)^ b)).
        apply ap. apply eissect.
      refine ((transport_pp _ _ _ _)^ @ _).
      exact (ap (fun z => transport P z b) (concat_Vp _)).
Defined.

Lemma ap_pr1_sigma_function
  {A : Type} {P : A -> Type} {A' : Type} {P' : A' -> Type}
  (F1 : A -> A') (F2 : forall a : A, P a -> P' (F1 a))
  {x x' : A} {y : P x} {y' : P x'} (p : (x; y) = (x'; y') :> sig P)
  : ap pr1 (ap (sigma_function F1 F2) p) = ap F1 (ap pr1 p).
Proof.
  induction p; constructor.
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

Lemma path2_sigma_function
  {A : Type} {P : A -> Type} {A' : Type} {P' : A' -> Type}
  (F1 : A -> A') (F2 : forall a : A, P a -> P' (F1 a))
  {x x' : A} {y : P x} {y' : P x'}
  (p p' : F1 x = F1 x')
  (q : transport P' p (F2 x y) = F2 x' y')
  (q' : transport P' p' (F2 x y) = F2 x' y')
  (r : p = p')
  (s : transport (fun p0 : F1 x = F1 x' => transport P' p0 (F2 x y) = F2 x' y') r q = q')
  : path_sigma_function F1 F2 p q = path_sigma_function F1 F2 p' q'.
Proof.
  induction r, s; constructor.
Defined.

Lemma path_sigma_function_1
  {A : Type} {P : A -> Type} {A' : Type} {P' : A' -> Type}
  (F1 : A -> A') (F2 : forall a : A, P a -> P' (F1 a))
  (x : A) (y : P x)
  : path_sigma_function F1 F2 (idpath (F1 x)) (idpath (F2 x y)) = idpath.
Proof.
  unfold path_sigma_function;
  srapply @path_path_sigma'_1.
Defined.

Lemma path_sigma_function_1_via
  {A : Type} {P : A -> Type} {A' : Type} {P' : A' -> Type}
  (F1 : A -> A') (F2 : forall a : A, P a -> P' (F1 a))
  {x : A} {y : P x}
  (p : F1 x = F1 x) (q : transport P' p (F2 x y) = F2 x y)
  (r : p = idpath)
  (s : ap (fun p0 : F1 x = F1 x => transport P' p0 (F2 x y)) r = q)
  : path_sigma_function F1 F2 p q = idpath.
Proof.
  path_via (path_sigma_function F1 F2 (idpath (F1 x)) (idpath (F2 x y))).
  refine (path2_sigma_function F1 F2 p idpath q idpath r _).
  refine (@transport_paths_Fl (F1 x = F1 x) _ (fun p0 => transport P' p0 (F2 x y)) _ _ (F2 x y) r q @ _).
  apply moveR_Vp; refine (_ @ (concat_p1 _)^); symmetry.
  exact s.
Defined.

Lemma path_sigma_function_pp
  {A : Type} {P : A -> Type} {A' : Type} {P' : A' -> Type}
  (F1 : A -> A') (F2 : forall a : A, P a -> P' (F1 a))
  {x x' x'' : A} {y : P x} {y' : P x'} {y'' : P x''}
  (p : F1 x = F1 x') (p' : F1 x' = F1 x'')
  (q : transport P' p (F2 x y) = F2 x' y')
  (q' : transport P' p' (F2 x' y') = F2 x'' y'')
  : path_sigma_function F1 F2 p q @ path_sigma_function F1 F2 p' q'
    = path_sigma_function F1 F2 (p @ p') (concat_D q q').
Proof.
  unfold path_sigma_function.
  apply path_path_sigma'_concat.
Defined.

Lemma sigma_function_compose
  {A : Type} {P : A -> Type} {A' : Type} {P' : A' -> Type}
  {B : Type} {Q : B -> Type}
  (F1 : A -> A') (F2 : forall a : A, P a -> P' (F1 a))
  (G1 : A' -> B) (G2 : forall a' : A', P' a' -> Q (G1 a'))
  (x : A) (y : P x)
  : sigma_function G1 G2 (sigma_function F1 F2 (x; y))
    = sigma_function (G1 o F1) (fun z w => G2 (F1 z) (F2 z w)) (x; y).
Proof.
  constructor.
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

Lemma ap_sigma_function_p
  {A : Type} {P : A -> Type} {A' : Type} {P' : A' -> Type}
  (F1 : A -> A') (F2 : forall a : A, P a -> P' (F1 a))
  {x x' : A} {y : P x} {y' : P x'} (p : (x; y) = (x'; y'))
  : ap (sigma_function F1 F2) p = path_sigma_function F1 F2 (ap F1 p..1) (transport_ap' F1 F2 p..1 p..2).
Proof.
  srapply @path_sigma'_ap'_p.
Defined.

Lemma ap_pr1_path_sigma_function
  {A : Type} {P : A -> Type} {A' : Type} {P' : A' -> Type}
  (F1 : A -> A') (F2 : forall a : A, P a -> P' (F1 a))
  {x x' : A} {y : P x} {y' : P x'}
  (p : F1 x = F1 x') (q : transport P' p (F2 x y) = F2 x' y')
  : ap pr1 (path_sigma_function F1 F2 p q) = p.
Proof.
  unfold path_sigma_function.
  apply ap_pr1_path_sigma'.
Defined.

Lemma path_sigma_function_truncfib
  {A : Type} {P : A -> Type} {A' : Type} {P' : A' -> Type}
  (F1 : A -> A') (F2 : forall a : A, P a -> P' (F1 a))
  {x x' : A} (y : P x) (y' : P x')
  (p : F1 x = F1 x')
  (T : forall a : A', IsHProp (P' a))
  : sigma_function F1 F2 (x; y) = sigma_function F1 F2 (x'; y').
Proof.
  unfold sigma_function.
  srapply @sigma_truncfib.
  exact p.
Defined.

Lemma path_sigma_function_truncfib'
  {A : Type} {P : A -> Type} {A' : Type} {P' : A' -> Type}
  (F1 : A -> A') (F2 : forall a : A, P a -> P' (F1 a))
  {x y : sig P} (p : F1 x.1 = F1 y.1)
  (T : forall a : A', IsHProp (P' a))
  : sigma_function F1 F2 x = sigma_function F1 F2 y.
Proof.
  srefine (path_sigma_function F1 F2 p _).
  srapply @path_ishprop.
Defined.

Lemma path2_sigma_function_truncfib
  {A : Type} {P : A -> Type} {A' : Type} {P' : A' -> Type}
  (F1 : A -> A') (F2 : forall a : A, P a -> P' (F1 a))
  {x x' : A} {y : P x} {y' : P x'}
  (p p' : F1 x = F1 x')
  (q : transport P' p (F2 x y) = F2 x' y')
  (q' : transport P' p' (F2 x y) = F2 x' y')
  (r : p = p')
  (T : forall a : A', IsHSet (P' a))
  : path_sigma_function F1 F2 p q = path_sigma_function F1 F2 p' q'.
Proof.
  srapply @path_sigma_truncfib.
  refine (ap_pr1_path_sigma_function F1 F2 p q @ r @ (ap_pr1_path_sigma_function F1 F2 p' q')^).
Defined.

Definition ap_pr1_sigma_truncfib
  {A : Type} (P : A -> Type) {x x' : A} {y : P x} {y' : P x'}
  {t : forall a : A, IsHProp (P a)} (p : x = x')
  : ap pr1 (@sigma_truncfib _ P _ _ y y' t p) = p.
Proof.
  unfold sigma_truncfib.
  apply path_sigma'_pr1.
Defined.

Lemma ap_pr1_path_sigma_function_truncfib
  {A : Type} {P : A -> Type} {A' : Type} {P' : A' -> Type}
  (F1 : A -> A') (F2 : forall a : A, P a -> P' (F1 a))
  {x x' : A} {y : P x} {y' : P x'}
  (p : F1 x = F1 x')
  (T : forall a : A', IsHProp (P' a))
  : ap pr1 (path_sigma_function_truncfib F1 F2 y y' p T) = p.
Proof.
  unfold path_sigma_function_truncfib.
  apply ap_pr1_sigma_truncfib.
Defined.

(* Lemma path_sigma_truncfib_name
  {A : Type} (B : A -> Type) (T : forall a : A, IsHSet (B a))
  {a a' : A} {b : B a} {b' : B a'} (p q : (a; b) = (a'; b') :> sig B)
  (h : p..1 = q..1)
  : p = q.
Proof.
  srapply @path_path_sigma.
  + exact h.
  + srapply @path_ishprop.
Defined. *)

Lemma transport_path_sigma_pr1
  {A B : Type} (C : B -> Type) (f g : A -> sig C)
  {x y : A} (p : x = y) (q : f x = g x)
  : (transport (fun a : A => f a = g a) p q)..1 = transport (fun a : A => (f a).1 = (g a).1) p q..1.
Proof.
  induction p; constructor.
Defined.

Lemma reduce_contr_sigma_bastard
  {A B : Type} (C : B -> Type)
  (T : forall b : B, IsHProp (C b))
  (f : A -> sig C) (bx : B) (cx : C bx)
  : Contr {a : A & (f a).1 = bx} -> Contr {a : A & f a = (bx; cx)}.
Proof.
  intros [[cent_a cent_p] cont].
  set (cont' := fun (a : A) (p : (f a).1 = bx) => cont (a; p)).
  transparent assert (cont_a : (forall (a : A) (p : (f a).1 = bx), cent_a = a)).
    exact (fun a p => (cont' a p)..1).
  transparent assert (cont_p : (forall (a : A) (p : (f a).1 = bx), transport (fun a : A => (f a).1 = bx) (cont' a p) ..1 cent_p = p)).
    exact (fun a p => (cont' a p)..2).
  unfold cont' in cont_a, cont_p. clear cont'.

  srapply @BuildContr.
  + srefine (_; _).
    - exact cent_a.
    - simpl. srapply @sigma_truncfib. exact cent_p.
  + intros [a p]. srapply @path_sigma'.
    - exact (cont_a a p..1).
    - srapply @path_sigma_truncfib.
      refine (_ @ cont_p a p..1).
      change (
        (transport (fun a0 : A => f a0 = (bx; cx)) (cont_a a p..1) (sigma_truncfib C T cent_p)) ..1 =
        transport (fun a0 : A => (f a0).1 = bx) (cont_a a p..1) cent_p
      ).
      refine (transport_path_sigma_pr1 _ _ _ _ _ @ _); simpl.
      apply ap. srapply @sigma_truncfib_pr1.
Defined.

End sigmas.


Section lib.
Context `{Funext}.
(* from the library *)
Definition path_forall_V `{A : Type} `{P : A -> Type} (f g : forall x, P x)
           (p : f == g)
  : path_forall _ _ (fun x => (p x)^) = (path_forall _ _ p)^.
Proof.
  transitivity (path_forall _ _ (fun x => (apD10 (path_forall _ _ p) x)^)).
  f_ap. symmetry. apply (@ap _ _ (fun h x => (h x)^)). apply eisretr.
  transitivity (path_forall _ _ (apD10 (path_forall _ _ p)^)).
  apply ap, inverse. apply apD10_V.
  apply eissect.
Defined.
End lib.