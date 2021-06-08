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

Lemma Connected_BS
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
  exact (@conn_to_prop _ _ (Connected_BS n) P T b).
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
  srapply m_base_fiber.
  + intros [nA A] [nB B]. exact (nA + nB, (A + B)%type).
  + intros ?? tA tB; simpl in *. exact (fin_coproduct tA tB).
Defined.


(** We need a symmetric monoidal structure on nat **)
Open Scope type.
Open Scope nat.

  Lemma alpha_nat
    : forall n1 n2 n3 : nat, (n1 + n2) + n3 = n1 + (n2 + n3).
  Proof.
    intros; induction n1; simpl.
    + constructor.
    + apply ap; apply IHn1.
  Defined.

  Lemma lambda_nat
    : forall n : nat, 0 + n = n.
  Proof.
    constructor.
  Defined.

  Lemma rho_nat
    : forall n : nat, n + 0 = n.
  Proof.
    induction n; simpl.
    + constructor.
    + apply ap; exact IHn.
  Defined.

  Lemma tau_nat
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

  Lemma pentagon_nat
    : IsPentagonCoherent (fun n m => n + m) alpha_nat.
  Proof.
    unfold IsPentagonCoherent; intros; srapply @path_ishprop.
  Qed.

  Lemma triangle_nat
    : IsTriangleCoherent 0 (fun n m => n + m) alpha_nat lambda_nat rho_nat.
  Proof.
    unfold IsTriangleCoherent; intros; srapply @path_ishprop.
  Qed.

  Lemma hexagon_nat
    : IsHexagonCoherent (fun n m => n + m) alpha_nat tau_nat.
  Proof.
    unfold IsHexagonCoherent; intros; srapply @path_ishprop.
  Qed.

  Lemma bigon_nat
    : IsBigonCoherent (fun n m => n + m) tau_nat.
  Proof.
    unfold IsBigonCoherent; intros; srapply @path_ishprop.
  Qed.

(** ... and a symmetric monoidal structure on Type **)

  Definition U_e
    : Type
    := Empty.

  Lemma alpha_U_equiv
    : forall A B C : Type, ((A + B) + C)%type <~> (A + (B + C))%type.
  Proof.
    srapply equiv_sum_assoc.
  Defined.

  Lemma alpha_U
    : forall A B C : Type, ((A + B) + C)%type = (A + (B + C))%type.
  Proof.
    intros; srapply @path_universe_uncurried. srapply alpha_U_equiv.
  Defined.

  Lemma lambda_U_equiv
    : forall B : Type, (U_e + B)%type <~> B.
  Proof.
    intros.
    srapply @equiv_adjointify; hnf.
    + intros [[]|b]; exact b.
    + intro b; exact (inr b).
    + intro b; constructor.
    + intros [[]|b]; constructor.
  Defined.

  Lemma lambda_U
    : forall B : Type, (U_e + B)%type = B.
  Proof.
    intros; srapply @path_universe_uncurried. srapply lambda_U_equiv.
  Defined.

  Lemma rho_U_equiv
    : forall A : Type, (A + U_e)%type <~> A.
  Proof.
    intros.
    srapply @equiv_adjointify; hnf.
    + intros [a|[]]; exact a.
    + intro a; exact (inl a).
    + intro a; constructor.
    + intros [a|[]]; constructor.
  Defined.

  Lemma rho_U
    : forall A : Type, (A + U_e)%type = A.
  Proof.
    intros; srapply @path_universe_uncurried. srapply rho_U_equiv.
  Defined.

  Lemma tau_U_equiv
    : forall A B : Type, (A + B)%type <~> (B + A)%type.
  Proof.
    srapply equiv_sum_symm.
  Defined.

  Lemma tau_U
    : forall A B : Type, (A + B)%type = (B + A)%type.
  Proof.
    intros. srapply @path_universe_uncurried. srapply tau_U_equiv.
  Defined.

  Lemma pentagon_U_equiv
    : forall A B C D : Type, alpha_U_equiv A B (C + D) oE alpha_U_equiv (A + B) C D = (1 +E alpha_U_equiv B C D) oE (alpha_U_equiv A (B + C) D oE (alpha_U_equiv A B C +E 1)).
  Proof.
    intros. apply path_equiv. apply path_forall.
    intros [[[a|b]|c]|d]; constructor.
  Defined.

  Lemma pentagon_U
    : IsPentagonCoherent (fun A B => (A + B)%type) alpha_U.
  Proof.
    unfold IsPentagonCoherent; intros A B C D. unfold alpha_U.
    refine (_ @ whiskerR (whiskerR (ap011_path_universe_uncurried_sum_e1 _)^ _) _ @ whiskerL _ (ap011_path_universe_uncurried_sum_1e _)^).
    change (path_universe (alpha_U_equiv (A + B) C D) @ path_universe (alpha_U_equiv A B (C + D)) = (path_universe (alpha_U_equiv A B C +E 1) @ path_universe (alpha_U_equiv A (B + C) D)) @
path_universe (1 +E alpha_U_equiv B C D)).
    refine (_ @ whiskerR (path_universe_compose _ _) _).
    change (path_universe (alpha_U_equiv (A + B) C D) @ path_universe (alpha_U_equiv A B (C + D)) = path_universe (alpha_U_equiv A (B + C) D oE (alpha_U_equiv A B C +E 1%equiv)) @ path_universe (1 +E alpha_U_equiv B C D)).
    refine ((path_universe_compose _ _)^ @ _ @ path_universe_compose _ _).
    change (path_universe_uncurried (alpha_U_equiv A B (C + D) oE alpha_U_equiv (A + B) C D) = path_universe_uncurried ((1%equiv +E alpha_U_equiv B C D) oE (alpha_U_equiv A (B + C) D oE (alpha_U_equiv A B C +E 1%equiv)))).
    apply ap.
    apply pentagon_U_equiv.
  Defined.

  Lemma triangle_U_equiv
    : forall A B : Type, (equiv_idmap A +E lambda_U_equiv _) oE alpha_U_equiv _ _ _ = rho_U_equiv A +E equiv_idmap B.
  Proof.
    intros. apply path_equiv. apply path_forall.
    intros [[a|[]]|b]; constructor.
  Defined.

  Lemma triangle_U
    : IsTriangleCoherent U_e (fun A B => (A + B)%type) alpha_U lambda_U rho_U.
  Proof.
    unfold IsTriangleCoherent; intros A B. unfold alpha_U, lambda_U, rho_U.
    refine (whiskerL _ (ap011_path_universe_uncurried_sum_1e _) @ _ @ (ap011_path_universe_uncurried_sum_e1 _)^).
    change (path_universe (alpha_U_equiv A Empty B) @ path_universe (1 +E lambda_U_equiv B) = path_universe_uncurried (rho_U_equiv A +E 1)).
    refine ((path_universe_compose _ _)^ @ _).
    change (path_universe_uncurried ((1 +E lambda_U_equiv B) oE alpha_U_equiv A Empty B) = path_universe_uncurried (rho_U_equiv A +E 1)).
    apply ap.
    apply triangle_U_equiv.
  Defined.

  Lemma hexagon_U_equiv
    : forall A B C : Type, alpha_U_equiv B C A oE (tau_U_equiv A (B + C) oE alpha_U_equiv A B C) =
(1 +E tau_U_equiv A C) oE (alpha_U_equiv B A C oE (tau_U_equiv A B +E 1)).
  Proof.
    intros. apply path_equiv. apply path_forall.
    intros [[a|b]|c]; constructor.
  Defined.

  Lemma hexagon_U
    : IsHexagonCoherent (fun A B => (A + B)%type) alpha_U tau_U.
  Proof.
    unfold IsHexagonCoherent; intros A B C. unfold alpha_U, tau_U.
    refine (_ @ whiskerR (whiskerR (ap011_path_universe_uncurried_sum_e1 _)^ _) _ @ whiskerL _ (ap011_path_universe_uncurried_sum_1e _)^).
    change ((path_universe (alpha_U_equiv A B C) @ path_universe (tau_U_equiv A (B + C))) @
path_universe (alpha_U_equiv B C A) = (path_universe (tau_U_equiv A B +E 1) @ path_universe (alpha_U_equiv B A C)) @ path_universe (1 +E tau_U_equiv A C)).
    refine (whiskerR (path_universe_compose _ _)^ _ @ _ @ whiskerR (path_universe_compose _ _) _).
    change (path_universe (tau_U_equiv A (B + C) oE alpha_U_equiv A B C) @ path_universe (alpha_U_equiv B C A) = path_universe (alpha_U_equiv B A C oE (tau_U_equiv A B +E 1)) @ path_universe (1 +E tau_U_equiv A C)).
    refine ((path_universe_compose _ _)^ @ _ @ path_universe_compose _ _).
    change (path_universe_uncurried (alpha_U_equiv B C A oE (tau_U_equiv A (B + C) oE alpha_U_equiv A B C)) = path_universe_uncurried ((1 +E tau_U_equiv A C) oE (alpha_U_equiv B A C oE (tau_U_equiv A B +E 1)))).
    apply ap.
    apply hexagon_U_equiv.
  Defined.

  Lemma bigon_U_equiv
    : forall A B : Type, tau_U_equiv B A oE tau_U_equiv A B = 1%equiv.
  Proof.
    intros. apply path_equiv. apply path_forall.
    intros [a|b]; constructor.
  Defined.

  Lemma bigon_U
    : IsBigonCoherent (fun A B => (A + B)%type) tau_U.
  Proof.
    unfold IsBigonCoherent; intros A B. unfold tau_U.
    change (path_universe (tau_U_equiv A B) @ path_universe (tau_U_equiv B A) = idpath).
    refine ((path_universe_compose (tau_U_equiv A B) (tau_U_equiv B A))^ @ _).
    refine (_ @ path_universe_1).
    change (path_universe_uncurried (tau_U_equiv B A oE tau_U_equiv A B) = path_universe_uncurried 1%equiv).
    apply ap.
    apply bigon_U_equiv.
  Defined.

(** Here we combine the symmetric monoidal structures **)

Lemma BS_dot'_e
  : BS_dot'.
Proof.
  unfold BS_dot'.
  srefine ((_, _); _). (* we need this, otherwise Coq will think Empty is in type0 and I don't know how to convince it otherwise *)
  + exact 0.
  + exact Empty.
  + simpl. exact (tr 1%equiv).
Defined.

Lemma alpha_BS_dot'
  : forall a b c : BS_dot', BS_dot'_product (BS_dot'_product a b) c = BS_dot'_product a (BS_dot'_product b c).
Proof.
  unfold BS_dot', BS, BS_dot'_product.
  intros [[nA A] tA] [[nB B] tB] [[nC C] tC].
  srapply @sigma_truncfib. srapply @path_prod'.
  + apply alpha_nat.
  + apply alpha_U.
Defined.

Lemma lambda_BS_dot'
  : forall b : BS_dot', BS_dot'_product BS_dot'_e b = b.
Proof.
  unfold BS_dot', BS, BS_dot'_product.
  intros [[nB B] tB].
  srapply @sigma_truncfib. srapply @path_prod'.
  + apply lambda_nat.
  + apply lambda_U.
Defined.

Lemma rho_BS_dot'
  : forall a : BS_dot', BS_dot'_product a BS_dot'_e = a.
Proof.
  unfold BS_dot', BS, BS_dot'_product.
  intros [[nA A] tA].
  srapply @sigma_truncfib. srapply @path_prod'.
  + apply rho_nat.
  + apply rho_U.
Defined.

Lemma tau_BS_dot'
  : forall a b : BS_dot', BS_dot'_product a b = BS_dot'_product b a.
Proof.
  unfold BS_dot', BS, BS_dot'_product.
  intros [[nA A] tA] [[nB B] tB].
  srapply @sigma_truncfib. srapply @path_prod'.
  + apply tau_nat.
  + apply tau_U.
Defined.

Lemma pentagon_BS_dot'
  : IsPentagonCoherent BS_dot'_product alpha_BS_dot'.
Proof.
  unfold IsPentagonCoherent; intros.
  refine (_ @ whiskerL _ (ap (fun z => ap011 BS_dot'_product z (alpha_BS_dot' b c d)) (sigma_truncfib_1 (fun X : nat * Type => merely (snd X <~> Fin (fst X))) _ (fun a0 : nat * Type => istrunc_truncation (-1) (snd a0 <~> Fin (fst a0))) idpath idpath)) @ whiskerR (whiskerR (ap (ap011 BS_dot'_product (alpha_BS_dot' a b c)) (sigma_truncfib_1 (fun X : nat * Type => merely (snd X <~> Fin (fst X))) _ (fun a0 : nat * Type => istrunc_truncation (-1) (snd a0 <~> Fin (fst a0))) idpath idpath)) _) _).
  unfold alpha_BS_dot'.
  refine (_ @ whiskerR (whiskerR (ap011_m_base_fiber_sigma_truncfib _ _ _ _ _ _ _ _ (path_prod' (alpha_nat (fst a.1) (fst b.1) (fst c.1)) (alpha_U (snd a.1) (snd b.1) (snd c.1))) idpath)^ _) _ @ whiskerL _ (ap011_m_base_fiber_sigma_truncfib _ _ _ _ _ _ _ _ idpath (path_prod' (alpha_nat (fst b.1) (fst c.1) (fst d.1)) (alpha_U (snd b.1) (snd c.1) (snd d.1))))^).
  repeat rewrite sigma_truncfib_concat.
  apply ap011.
  + srapply @path_ishprop.
  + set (nA := fst a.1); set (nB := fst b.1); set (nC := fst c.1); set (nD := fst d.1);
    set (A := snd a.1); set (B := snd b.1); set (C := snd c.1); set (D := snd d.1).
change (path_prod' (alpha_nat (nA + nB) nC nD) (alpha_U (A + B) C D) @ path_prod' (alpha_nat nA nB (nC + nD)) (alpha_U A B (C + D)) = (ap011 (fun X X0 : nat * Type => (fst X + fst X0, (snd X + snd X0)%type)) (path_prod' (alpha_nat nA nB nC) (alpha_U A B C)) 1 @ path_prod' (alpha_nat nA (nB + nC) nD) (alpha_U A (B + C) D)) @ ap011 (fun X X0 : nat * Type => (fst X + fst X0, (snd X + snd X0)%type)) 1 (path_prod' (alpha_nat nB nC nD) (alpha_U B C D))).
  refine (_ @ whiskerR (whiskerR (ap011_path_prod' (fun n n' => (n + n')) (fun X Y => (X + Y)%type) (alpha_nat nA nB nC) (alpha_U A B C) idpath idpath)^ _) _ @ whiskerL _ (ap011_path_prod' (fun n n' => (n + n')) (fun X Y => (X + Y)%type) idpath idpath (alpha_nat nB nC nD) (alpha_U B C D))^).
  repeat rewrite <- path_prod_pp.
  apply ap011.
  - apply pentagon_nat.
  - apply pentagon_U.
Qed.

Lemma triangle_BS_dot'
  : IsTriangleCoherent BS_dot'_e BS_dot'_product alpha_BS_dot' lambda_BS_dot' rho_BS_dot'.
Proof.
  unfold IsTriangleCoherent; intros.
  refine (whiskerL _ (ap (fun z => ap011 BS_dot'_product z (lambda_BS_dot' b)) (sigma_truncfib_1 (fun X : nat * Type => merely (snd X <~> Fin (fst X))) _ (fun a0 : nat * Type => istrunc_truncation (-1) (snd a0 <~> Fin (fst a0))) idpath idpath))^ @ _);
  refine (_ @ ap (ap011 BS_dot'_product (rho_BS_dot' a)) (sigma_truncfib_1 (fun X : nat * Type => merely (snd X <~> Fin (fst X))) _ (fun a0 : nat * Type => istrunc_truncation (-1) (snd a0 <~> Fin (fst a0))) idpath idpath)).
  unfold alpha_BS_dot', lambda_BS_dot', rho_BS_dot'.
  refine (whiskerL _ (ap011_m_base_fiber_sigma_truncfib _ _ _ _ _ _ _ _ idpath (path_prod' (lambda_nat (fst b.1)) (lambda_U (snd b.1)))) @ _ @ (ap011_m_base_fiber_sigma_truncfib _ _ _ _ _ _ _ _ (path_prod' (rho_nat (fst a.1)) (rho_U (snd a.1))) idpath)^).
  repeat rewrite sigma_truncfib_concat.
  apply ap011.
  + srapply @path_ishprop.
  + refine (whiskerL _ (ap011_path_prod' (fun n n' => (n + n')) (fun X Y => (X + Y)%type) idpath idpath (lambda_nat (fst b.1)) (lambda_U (snd b.1))) @ _ @ (ap011_path_prod' (fun n n' => (n + n')) (fun X Y => (X + Y)%type) (rho_nat (fst a.1)) (rho_U (snd a.1)) idpath idpath)^).
    repeat rewrite <- path_prod_pp.
    apply ap011.
    - apply triangle_nat.
    - apply triangle_U.
Qed.

Lemma hexagon_BS_dot'
  : IsHexagonCoherent BS_dot'_product alpha_BS_dot' tau_BS_dot'.
Proof.
  unfold IsHexagonCoherent; intros.
  refine (_ @ whiskerR (whiskerR (ap (ap011 BS_dot'_product (tau_BS_dot' a b)) (sigma_truncfib_1 (fun X : nat * Type => merely (snd X <~> Fin (fst X))) _ (fun a0 : nat * Type => istrunc_truncation (-1) (snd a0 <~> Fin (fst a0))) idpath idpath)) _) _ @ whiskerL _ (ap (fun z => ap011 BS_dot'_product z (tau_BS_dot' a c)) (sigma_truncfib_1 (fun X : nat * Type => merely (snd X <~> Fin (fst X))) _ (fun a0 : nat * Type => istrunc_truncation (-1) (snd a0 <~> Fin (fst a0))) idpath idpath))).
  unfold alpha_BS_dot', tau_BS_dot'.
  refine (_ @ whiskerR (whiskerR (ap011_m_base_fiber_sigma_truncfib _ _ _ _ _ _ _ _ (path_prod' (tau_nat (fst a.1) (fst b.1)) (tau_U (snd a.1) (snd b.1))) idpath)^ _) _ @ whiskerL _ (ap011_m_base_fiber_sigma_truncfib _ _ _ _ _ _ _ _ idpath (path_prod' (tau_nat (fst a.1) (fst c.1)) (tau_U (snd a.1) (snd c.1))))^).
  repeat rewrite sigma_truncfib_concat.
  apply ap011.
  + srapply @path_ishprop.
  + refine (_ @ whiskerR (whiskerR (ap011_path_prod' (fun n n' => (n + n')) (fun X Y => (X + Y)%type) (tau_nat (fst a.1) (fst b.1)) (tau_U (snd a.1) (snd b.1)) idpath idpath)^ _) _ @ whiskerL _ (ap011_path_prod' (fun n n' => (n + n')) (fun X Y => (X + Y)%type) idpath idpath (tau_nat (fst a.1) (fst c.1)) (tau_U (snd a.1) (snd c.1)))^).
    repeat rewrite <- path_prod_pp.
    apply ap011.
    - apply hexagon_nat.
    - apply hexagon_U.
Qed.

Lemma bigon_BS_dot'
  : IsBigonCoherent BS_dot'_product tau_BS_dot'.
Proof.
  unfold IsBigonCoherent.
  intros.
  unfold tau_BS_dot'.
  refine (sigma_truncfib_concat (fun X : nat * Type => merely (snd X <~> Fin (fst X))) _ _ _ @ _).
  srapply @sigma_truncfib_1.
  unfold path_prod'.
  refine ((path_prod_pp _ _ _ _ _ _ _)^ @ _).
  change (path_prod (fst a.1 + fst b.1, (snd a.1 + snd b.1)%type) (fst a.1 + fst b.1, (snd a.1 + snd b.1)%type) (tau_nat (fst a.1) (fst b.1) @ tau_nat (fst b.1) (fst a.1)) (tau_U (snd a.1) (snd b.1) @ tau_U (snd b.1) (snd a.1)) = path_prod (fst a.1 + fst b.1, (snd a.1 + snd b.1)%type) (fst a.1 + fst b.1, (snd a.1 + snd b.1)%type) idpath idpath).
  apply ap011.
  + apply bigon_nat.
  + apply bigon_U.
Qed.

Definition BSSMG
  : SymMonoidalGroupoid
  := Build_SymMonoidalGroupoid BS_dot' BS_dot'_trunc BS_dot'_e BS_dot'_product alpha_BS_dot' lambda_BS_dot' rho_BS_dot' tau_BS_dot' pentagon_BS_dot' triangle_BS_dot' hexagon_BS_dot' bigon_BS_dot'.

End BS_monoidal_structure.