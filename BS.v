Require Export smonoidalgroupoid.

Open Scope type.
Open Scope nat.

Section BS.
Context `{Univalence}.

(** Definition of the subuniverse BS of finite types **)

Definition BS : nat -> Type
  := fun n => {A : Type & merely (A <~> Fin n)}.

Definition BS_Finite (n : nat) (Xt : BS n)
  : Finite Xt.1
  := @Build_Finite _ n Xt.2.

(** BS n is a 1-type for every n **)

Lemma BS_trunc (n : nat)
  : IsTrunc 1 (BS n).
Proof.
  unfold BS. srapply @trunc_sigma';
  change (forall X Y : BS n, IsHSet (X.1 = Y.1)).
  intros [A tA] [B tB]; simpl.
  srapply @istrunc_paths_Type.
  apply hset_Finite.
  exact (Build_Finite B n tB).
Defined.

(** BS 0 and BS 1 are contractible **)

Lemma Contr_BS0
  : Contr (BS 0).
Proof.
  unfold BS. srapply @Build_Contr.
  + exact (Fin 0; tr 1%equiv).
  + intros [A t].
    srapply @sigma_truncfib. symmetry.
    strip_truncations.
    exact (path_universe_uncurried t).
Defined.

Lemma Contr_BS1
  : Contr (BS 1).
Proof.
  unfold BS. srapply @Build_Contr.
  + exact (Fin 1; tr 1%equiv).
  + intros [A t].
    srapply @sigma_truncfib. symmetry.
    strip_truncations.
    exact (path_universe_uncurried t).
Defined.

(** BS n is connected for every n **)

Lemma Conn_BS
  : forall n : nat, Contr (Trunc 0 (BS n)).
Proof.
  intro n. srapply @Build_Contr.
  + apply tr. exact (Fin n; tr 1%equiv).
  + srapply @Trunc_ind.
    intros [A t]. strip_truncations.
    apply ap. srapply @sigma_truncfib.
    exact (path_universe_uncurried t)^.
Defined.

Lemma forall_BS_hprop (n : nat)
  (P : BS n -> Type) (T : forall Xt : BS n, IsHProp (P Xt))
  : forall b : BS n, P b -> forall x : BS n, P x.
Proof.
  intro b.
  exact (@conn_to_prop _ _ (Conn_BS n) P T b).
Defined.

(** Paths in BS are equivalent to paths between the underlying types **)

Lemma path_in_BS {n : nat}
  : forall X Y : BS n, X = Y <~> X.1 = Y.1.
Proof.
  intros X Y.
  srapply @equiv_adjointify.
  + intro p. exact p..1.
  + intro p. exact (path_sigma _ _ _ p (path_ishprop _ _)).
  + unfold Sect; intro p; simpl.
    srapply ap_pr1_path_sigma.
  + unfold Sect; intro p; simpl.
    srapply @path_path_sigma; simpl.
    - apply ap_pr1_path_sigma.
    - srapply @path_ishprop.
Defined.

Lemma path_in_BS_equiv {n : nat}
  : forall X Y : BS n, X = Y -> X.1 <~> Y.1.
Proof.
  intros X Y p. apply equiv_path. apply path_in_BS. exact p.
Defined.

Lemma IsHSet_path_in_BS {n : nat}
  : forall (X Y : BS n), IsHSet (X.1 = Y.1).
Proof.
  intros.
  srefine (@transport _ IsHSet (X = Y) (X.1 = Y.1) _ _).
  + srapply @path_universe_uncurried. apply path_in_BS.
  + srapply @istrunc_paths. apply BS_trunc.
Defined.

Lemma path2_in_BS {n : nat}
  : forall (X Y : BS n) (p q : X = Y), p..1 = q..1 <~> p = q.
Proof.
  intros.
  srapply @equiv_adjointify.
  + intro r. exact (path_path_sigma _ _ _ _ _ r (path_ishprop _ _)).
  + intro r. exact (ap (ap pr1) r).
  + unfold Sect; intro r; simpl.
    srapply @path_ishprop.
    srapply @istrunc_paths. srapply @istrunc_paths. apply BS_trunc.
  + unfold Sect; intro r.
    srapply @path_ishprop. srapply @istrunc_paths.
    srefine (@transport _ IsHSet (X = Y) _ _ _).
    - srapply path_universe_uncurried. exact (path_in_BS X Y).
    - srapply @istrunc_paths. apply BS_trunc.
Defined.

Lemma IsHProp_path2_in_BS {n : nat}
  : forall (X Y : BS n) (p q : X = Y), IsHProp (p..1 = q..1).
Proof.
  intros.
  srefine (@transport _ IsHProp (p = q) _ _ _).
  + srapply @path_universe_uncurried. exact (path2_in_BS X Y p q)^-1%equiv.
  + srapply @istrunc_paths. srapply @istrunc_paths. apply BS_trunc.
Defined.

Lemma IsHProp_path2_in_BS_type {n : nat}
  : forall (X Y : BS n) (p q : X.1 = Y.1), IsHProp (p = q).
Proof.
  intros.
  rewrite <- (@ap_pr1_path_sigma Type (fun X => merely (X <~> Fin n)) X Y p (path_ishprop _ _)).
  rewrite <- (@ap_pr1_path_sigma Type (fun X => merely (X <~> Fin n)) X Y q (path_ishprop _ _)).
  apply IsHProp_path2_in_BS.
Defined.

(** Finite types are 0-types **)

Lemma IsHSet_finite {n : nat} (X : BS n)
  : IsHSet X.1.
Proof.
  induction X as [A t]; simpl.
  apply hset_Finite.
  exact (Build_Finite A n t).
Defined.

(** Definition of BS_dot and its variant. *)

Definition BS_dot
  : Type
  := sig BS.

Definition BS_dot'
  : Type
  := {X : nat * Type & merely (snd X <~> Fin (fst X))}.

Lemma BS_dot_dot'
  : BS_dot <~> BS_dot'.
Proof.
  unfold BS_dot, BS_dot', BS.
  srapply @equiv_adjointify; hnf.
  + intros [n [A t]]. exact ((n, A); t).
  + intros [[n A] t]. exact (n; (A; t)).
  + intros [[n A] t]; constructor.
  + intros [n [A t]]; constructor.
Defined.

Lemma BS_dot_trunc
  : IsTrunc 1 BS_dot.
Proof.
  srapply @trunc_sigma.
  apply BS_trunc.
Defined.

Lemma BS_dot'_trunc
  : IsTrunc 1 BS_dot'.
Proof.
  exact (@trunc_equiv' _ _ BS_dot_dot' 1 BS_dot_trunc).
Defined.

End BS.


(** Symmetric monoidal structure on BS_dot **)

Section BS_monoidal_structure.
Context `{Univalence}.

  Lemma can_fin_coproduct (nA nB : nat)
    : (Fin nA + Fin nB) <~> Fin (nA + nB).
  Proof.
    induction nA; simpl.
    + srapply @equiv_adjointify; hnf.
      - intros [[]|x]; exact x.
      - exact inr.
      - constructor.
      - intros [[]|x]; constructor.
    + refine (_ oE equiv_sum_assoc (Fin nA) Unit (Fin nB)).
      refine (_ oE (1%equiv +E equiv_sum_symm Unit (Fin nB))).
      refine (_ oE (equiv_sum_assoc (Fin nA) (Fin nB) Unit)^-1%equiv).
      exact (IHnA +E 1%equiv).
  Defined.

  Lemma fin_coproduct {nA nB : nat} {A B : Type}
    (tA : Trunc (-1) (A <~> Fin nA)) (tB : Trunc (-1) (B <~> Fin nB))
    : Trunc (-1) (A + B <~> Fin (nA + nB)).
  Proof.
    strip_truncations; apply tr.
    refine (can_fin_coproduct nA nB oE (tA +E tB)).
  Defined.

Definition BS_dot'_product
  : BS_dot' -> BS_dot' -> BS_dot'.
Proof.
  unfold BS_dot', BS.
  intros [[nA A] tA] [[nB B] tB].
  srefine ((nA + nB, (A + B)%type); _).
  simpl in *. exact (fin_coproduct tA tB).
Defined.


(** We need a symmetric monoidal structure on nat **)

  Lemma nat_alp
    : forall n1 n2 n3 : nat, (n1 + n2) + n3 = n1 + (n2 + n3).
  Proof.
    intros; induction n1; simpl.
    + constructor.
    + apply ap; apply IHn1.
  Defined.

  Lemma nat_lam
    : forall n : nat, 0 + n = n.
  Proof.
    constructor.
  Defined.

  Lemma nat_rho
    : forall n : nat, n + 0 = n.
  Proof.
    induction n; simpl.
    + constructor.
    + apply ap; exact IHn.
  Defined.

  Lemma nat_tau
    : forall n1 n2 : nat, n1 + n2 = n2 + n1.
  Proof.
    induction n1; simpl.
    + induction n2; simpl.
      - constructor.
      - apply ap; exact IHn2.
    + induction n2; simpl.
      - apply ap. change (n1 + 0 = 0 + n1). apply IHn1.
      - apply ap. refine (IHn1 (n2.+1) @ _ @ IHn2).
        change ((n2 + n1).+1 = (n1 + n2).+1).
        apply ap. exact (IHn1 n2)^.
  Defined.

  Lemma nat_pentagon
    : forall n1 n2 n3 n4 : nat,
      ap011 (fun n m => n + m) (nat_alp n1 n2 n3) (idpath n4) @ nat_alp n1 (n2 + n3) n4 @ ap011 (fun n m => n + m) (idpath n1) (nat_alp n2 n3 n4) = nat_alp (n1 + n2) n3 n4 @ nat_alp n1 n2 (n3 + n4).
  Proof.
    intros. srapply @path_ishprop.
  Defined.

  Lemma nat_triangle
    : forall n1 n2 : nat,
      nat_alp _ _ _ @ ap011 (fun n m => n + m) (idpath n1) (nat_lam _) = ap011 (fun n m => n + m) (nat_rho n1) (idpath n2).
  Proof.
    intros. srapply @path_ishprop.
  Defined.

  Lemma nat_hexagon
    : forall n1 n2 n3 : nat,
      nat_alp n1 n2 n3 @ nat_tau n1 (n2 + n3) @ nat_alp n2 n3 n1 = ap011 (fun n m => n + m) (nat_tau n1 n2) (idpath n3) @ nat_alp _ _ _ @ ap011 (fun n m => n + m) (idpath n2) (nat_tau n1 n3).
  Proof.
    intros. srapply @path_ishprop.
  Defined.

  Lemma nat_bigon
    : forall n1 n2 : nat,
      nat_tau n1 n2 @ nat_tau _ _ = idpath.
  Proof.
    intros. srapply @path_ishprop.
  Defined.

(** ... and a symmetric monoidal structure on Type **)

  Lemma coproduct_alp_equiv
    : forall A B C : Type, ((A + B) + C)%type <~> (A + (B + C))%type.
  Proof.
    srapply equiv_sum_assoc.
  Defined.

  Lemma coproduct_alp
    : forall A B C : Type, ((A + B) + C)%type = (A + (B + C))%type.
  Proof.
    intros; srapply @path_universe_uncurried. srapply coproduct_alp_equiv.
  Defined.

  Lemma coproduct_lam_equiv
    : forall B : Type, (Empty + B)%type <~> B.
  Proof.
    intros.
    srapply @equiv_adjointify; hnf.
    + intros [[]|b]; exact b.
    + intro b; exact (inr b).
    + intro b; constructor.
    + intros [[]|b]; constructor.
  Defined.

  Lemma coproduct_lam
    : forall B : Type, (Empty + B)%type = B.
  Proof.
    intros; srapply @path_universe_uncurried. srapply coproduct_lam_equiv.
  Defined.

  Lemma coproduct_rho_equiv
    : forall A : Type, (A + Empty)%type <~> A.
  Proof.
    intros.
    srapply @equiv_adjointify; hnf.
    + intros [a|[]]; exact a.
    + intro a; exact (inl a).
    + intro a; constructor.
    + intros [a|[]]; constructor.
  Defined.

  Lemma coproduct_rho
    : forall A : Type, (A + Empty)%type = A.
  Proof.
    intros; srapply @path_universe_uncurried. srapply coproduct_rho_equiv.
  Defined.

  Lemma coproduct_tau_equiv
    : forall A B : Type, (A + B)%type <~> (B + A)%type.
  Proof.
    srapply equiv_sum_symm.
  Defined.

  Lemma coproduct_tau
    : forall A B : Type, (A + B)%type = (B + A)%type.
  Proof.
    intros. srapply @path_universe_uncurried. srapply coproduct_tau_equiv.
  Defined.

  Lemma coproduct_pentagon_equiv
    : forall A B C D : Type, (1%equiv +E coproduct_alp_equiv B C D) oE (coproduct_alp_equiv A (B + C) D oE (coproduct_alp_equiv A B C +E 1%equiv)) = coproduct_alp_equiv A B (C + D) oE coproduct_alp_equiv (A + B) C D.
  Proof.
    intros. apply path_equiv. apply path_forall.
    intros [[[a|b]|c]|d]; constructor.
  Defined.

  Lemma coproduct_pentagon
    : forall A B C D : Type, (ap011 (fun X Y => (X + Y)%type) (coproduct_alp A B C) idpath @ coproduct_alp A (B + C) D) @ ap011 (fun X Y => (X + Y)%type) idpath (coproduct_alp B C D) = coproduct_alp (A + B) C D @ coproduct_alp A B (C + D).
  Proof.
    intros. unfold coproduct_alp.
    refine (whiskerR (whiskerR (ap011_path_universe_uncurried_sum_e1 _) _) _ @ whiskerL _ (ap011_path_universe_uncurried_sum_1e _) @ _).
    change ((path_universe (coproduct_alp_equiv A B C +E 1) @ path_universe (coproduct_alp_equiv A (B + C) D)) @
path_universe (1 +E coproduct_alp_equiv B C D) = path_universe (coproduct_alp_equiv (A + B) C D) @ path_universe (coproduct_alp_equiv A B (C + D))).
    refine (whiskerR (path_universe_compose _ _)^ _ @ _).
    change (path_universe (coproduct_alp_equiv A (B + C) D oE (coproduct_alp_equiv A B C +E 1%equiv)) @
path_universe (1 +E coproduct_alp_equiv B C D) = path_universe (coproduct_alp_equiv (A + B) C D) @ path_universe (coproduct_alp_equiv A B (C + D))).
    refine ((path_universe_compose _ _)^ @ _ @ path_universe_compose _ _).
    change (path_universe_uncurried ((1%equiv +E coproduct_alp_equiv B C D) oE (coproduct_alp_equiv A (B + C) D oE (coproduct_alp_equiv A B C +E 1%equiv))) = path_universe_uncurried (coproduct_alp_equiv A B (C + D) oE coproduct_alp_equiv (A + B) C D)).
    apply ap.
    apply coproduct_pentagon_equiv.
  Defined.

  Lemma coproduct_triangle_equiv
    : forall A B : Type, (equiv_idmap A +E coproduct_lam_equiv _) oE coproduct_alp_equiv _ _ _ = coproduct_rho_equiv A +E equiv_idmap B.
  Proof.
    intros. apply path_equiv. apply path_forall.
    intros [[a|[]]|b]; constructor.
  Defined.

  Lemma coproduct_triangle
    : forall A B : Type, coproduct_alp _ _ _ @ ap011 (fun X Y => (X + Y)%type) (idpath A) (coproduct_lam _) = ap011 (fun X Y => (X + Y)%type) (coproduct_rho A) (idpath B).
  Proof.
    intros. unfold coproduct_alp, coproduct_lam, coproduct_rho.
    refine (whiskerL _ (ap011_path_universe_uncurried_sum_1e _) @ _ @ (ap011_path_universe_uncurried_sum_e1 _)^).
    change (path_universe (coproduct_alp_equiv A Empty B) @ path_universe (1 +E coproduct_lam_equiv B) = path_universe_uncurried (coproduct_rho_equiv A +E 1)).
    refine ((path_universe_compose _ _)^ @ _).
    change (path_universe_uncurried ((1 +E coproduct_lam_equiv B) oE coproduct_alp_equiv A Empty B) = path_universe_uncurried (coproduct_rho_equiv A +E 1)).
    apply ap.
    apply coproduct_triangle_equiv.
  Defined.

  Lemma coproduct_hexagon_equiv
    : forall A B C : Type, coproduct_alp_equiv B C A oE (coproduct_tau_equiv A (B + C) oE coproduct_alp_equiv A B C) =
(1 +E coproduct_tau_equiv A C) oE (coproduct_alp_equiv B A C oE (coproduct_tau_equiv A B +E 1)).
  Proof.
    intros. apply path_equiv. apply path_forall.
    intros [[a|b]|c]; constructor.
  Defined.

  Lemma coproduct_hexagon
    : forall A B C : Type, coproduct_alp A B C @ coproduct_tau A (B + C)%type @ coproduct_alp B C A = ap011 (fun X Y => (X + Y)%type) (coproduct_tau A B) (idpath C) @ coproduct_alp _ _ _ @ ap011 (fun X Y => (X + Y)%type) (idpath B) (coproduct_tau A C).
  Proof.
    intros. unfold coproduct_alp, coproduct_tau.
    refine (_ @ whiskerR (whiskerR (ap011_path_universe_uncurried_sum_e1 _)^ _) _ @ whiskerL _ (ap011_path_universe_uncurried_sum_1e _)^).
    change ((path_universe (coproduct_alp_equiv A B C) @ path_universe (coproduct_tau_equiv A (B + C))) @
path_universe (coproduct_alp_equiv B C A) = (path_universe (coproduct_tau_equiv A B +E 1) @ path_universe (coproduct_alp_equiv B A C)) @ path_universe (1 +E coproduct_tau_equiv A C)).
    refine (whiskerR (path_universe_compose _ _)^ _ @ _ @ whiskerR (path_universe_compose _ _) _).
    change (path_universe (coproduct_tau_equiv A (B + C) oE coproduct_alp_equiv A B C) @ path_universe (coproduct_alp_equiv B C A) = path_universe (coproduct_alp_equiv B A C oE (coproduct_tau_equiv A B +E 1)) @ path_universe (1 +E coproduct_tau_equiv A C)).
    refine ((path_universe_compose _ _)^ @ _ @ path_universe_compose _ _).
    change (path_universe_uncurried (coproduct_alp_equiv B C A oE (coproduct_tau_equiv A (B + C) oE coproduct_alp_equiv A B C)) = path_universe_uncurried ((1 +E coproduct_tau_equiv A C) oE (coproduct_alp_equiv B A C oE (coproduct_tau_equiv A B +E 1)))).
    apply ap.
    apply coproduct_hexagon_equiv.
  Defined.

  Lemma coproduct_bigon_equiv
    : forall A B : Type, coproduct_tau_equiv B A oE coproduct_tau_equiv A B = 1%equiv.
  Proof.
    intros. apply path_equiv. apply path_forall.
    intros [a|b]; constructor.
  Defined.

  Lemma coproduct_bigon
    : forall A B : Type, coproduct_tau A B @ coproduct_tau B A = idpath.
  Proof.
    intros. unfold coproduct_tau.
    change (path_universe (coproduct_tau_equiv A B) @ path_universe (coproduct_tau_equiv B A) = idpath).
    refine ((path_universe_compose (coproduct_tau_equiv A B) (coproduct_tau_equiv B A))^ @ _).
    refine (_ @ path_universe_1).
    change (path_universe_uncurried (coproduct_tau_equiv B A oE coproduct_tau_equiv A B) = path_universe_uncurried 1%equiv).
    apply ap.
    apply coproduct_bigon_equiv.
  Defined.

(** Here we combine the symmetric monoidal structures **)

Lemma BS_dot'_alp
  : forall a b c : BS_dot', BS_dot'_product (BS_dot'_product a b) c = BS_dot'_product a (BS_dot'_product b c).
Proof.
  unfold BS_dot', BS, BS_dot'_product.
  intros [[nA A] tA] [[nB B] tB] [[nC C] tC].
  srapply @sigma_truncfib. srapply @path_prod'.
  + apply nat_alp.
  + apply coproduct_alp.
Defined.

Lemma BS_dot'_lam
  : forall b : BS_dot', BS_dot'_product ((0, Empty); tr 1%equiv) b = b.
Proof.
  unfold BS_dot', BS, BS_dot'_product.
  intros [[nB B] tB].
  srapply @sigma_truncfib. srapply @path_prod'.
  + apply nat_lam.
  + apply coproduct_lam.
Defined.

Lemma BS_dot'_rho
  : forall a : BS_dot', BS_dot'_product a ((0, Empty); tr 1%equiv) = a.
Proof.
  unfold BS_dot', BS, BS_dot'_product.
  intros [[nA A] tA].
  srapply @sigma_truncfib. srapply @path_prod'.
  + apply nat_rho.
  + apply coproduct_rho.
Defined.

Lemma BS_dot'_tau
  : forall a b : BS_dot', BS_dot'_product a b = BS_dot'_product b a.
Proof.
  unfold BS_dot', BS, BS_dot'_product.
  intros [[nA A] tA] [[nB B] tB].
  srapply @sigma_truncfib. srapply @path_prod'.
  + apply nat_tau.
  + apply coproduct_tau.
Defined.

(** We omit three out of the four coherence diagrams from the formalization,
as they just involve very complex path algebra. As a title of example, we
just show the bigon. **)
Lemma BS_dot'_pentagon
  : IsPentagonCoherent BS_dot'_product BS_dot'_alp.
Proof.
Admitted.

Lemma BS_dot'_triangle
  : IsTriangleCoherent ((0, Empty); tr 1%equiv) BS_dot'_product BS_dot'_alp BS_dot'_lam BS_dot'_rho.
Proof.
Admitted.

Lemma BS_dot'_hexagon
  : IsHexagonCoherent BS_dot'_product BS_dot'_alp BS_dot'_tau.
Proof.
Admitted.

Lemma BS_dot'_bigon
  : IsBigonCoherent BS_dot'_product BS_dot'_tau.
Proof.
  unfold IsBigonCoherent.
  intros.
  unfold BS_dot'_tau.
  refine (sigma_truncfib_concat (fun X : nat * Type => merely (snd X <~> Fin (fst X))) _ _ _ @ _).
  srapply @sigma_truncfib_1.
  unfold path_prod'.
  refine ((path_prod_pp _ _ _ _ _ _ _)^ @ _).
  change (path_prod (fst a.1 + fst b.1, (snd a.1 + snd b.1)%type) (fst a.1 + fst b.1, (snd a.1 + snd b.1)%type) (nat_tau (fst a.1) (fst b.1) @ nat_tau (fst b.1) (fst a.1)) (coproduct_tau (snd a.1) (snd b.1) @ coproduct_tau (snd b.1) (snd a.1)) = path_prod (fst a.1 + fst b.1, (snd a.1 + snd b.1)%type) (fst a.1 + fst b.1, (snd a.1 + snd b.1)%type) idpath idpath).
  apply ap011.
  + apply nat_bigon.
  + apply coproduct_bigon.
Defined.

Definition BS_smgpd
  : SymMonoidalGroupoid
  := Build_SymMonoidalGroupoid BS_dot' BS_dot'_trunc ((0, Empty); tr 1%equiv) BS_dot'_product BS_dot'_alp BS_dot'_lam BS_dot'_rho BS_dot'_tau BS_dot'_pentagon BS_dot'_triangle BS_dot'_hexagon BS_dot'_bigon.

End BS_monoidal_structure.