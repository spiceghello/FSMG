Require Export UnivalenceImpliesFunext.
Require Export BS deloop combinatorics_tmp.

Section deloop_to_BS.
Let deloop := deloop.deloop.

Open Scope type.

Context `{Univalence}.

(** We define a family of functions deloop n -> BS n **)

  Definition dtb_dlpt0b
    : Type
    := Fin 0.

  Definition dtb_dlpt0f
    : Trunc (-1) (dtb_dlpt0b <~> Fin 0)
    := (tr 1%equiv).

  Definition dtb_dlib
    : nat -> Type -> Type
    := fun _ => add.

  Definition dtb_dlif
    : forall (n : nat) (A : Type), merely (A <~> Fin n) -> merely (dtb_dlib n A <~> Fin n.+1).
  Proof.
    simpl; intros n A; unfold dtb_dlib, add.
    srapply @Trunc_rec; intro e.
    exact (tr (exp e)).
  Qed.

  Definition dtb_dltwb
    : forall (n : nat) (A : Type), dtb_dlib n.+1 (dtb_dlib n A) = dtb_dlib n.+1 (dtb_dlib n A).
  Proof.
    intros; unfold dtb_dlib, add.
    exact (gamma A).
  Defined.

  Definition dtb_dldob
    : forall (n : nat) (A : Type), dtb_dltwb n A @ dtb_dltwb n A = idpath.
  Proof.
    intros; unfold dtb_dltwb.
    apply gamma_double.
  Defined.

  Definition dtb_dlbrb
    : forall (n : nat) (A : Type),
      (dtb_dltwb n.+1 (dtb_dlib n A) @ ap (dtb_dlib n.+2) (dtb_dltwb n A)) @ dtb_dltwb n.+1 (dtb_dlib n A) =
      (ap (dtb_dlib n.+2) (dtb_dltwb n A) @ dtb_dltwb n.+1 (dtb_dlib n A)) @ ap (dtb_dlib n.+2) (dtb_dltwb n A).
  Proof.
    intros; unfold dtb_dlib, dtb_dltwb.
    apply gamma_triple.
  Defined.

Definition deloop_to_BS
  : forall n : nat, deloop n -> BS n
  := deloop_rec_subuniverse (fun n A => merely (A <~> Fin n)) BS_trunc _ dtb_dlpt0b dtb_dlpt0f dtb_dlib dtb_dlif dtb_dltwb dtb_dldob dtb_dlbrb.

Definition deloop_to_BSb
  : forall n : nat, deloop n -> Type
  := fun n a => (deloop_to_BS n a).1.

(** judgmentally, we have that
   deloop_to_BSb 0 dlpt0        computes to   Empty, and
   deloop_to_BSb n.+1 (dli a)   computes to   deloop_to_BSb n a + Unit, for every n : nat, a : deloop n.
The other 'computation' rule comes below: **)

Definition ap_deloop_to_BSb_dltw {n} (a : deloop n)
  : ap (deloop_to_BSb n.+2) (dltw a) = gamma (deloop_to_BSb n a).
Proof.
  unfold deloop_to_BSb.
  refine (ap_compose (deloop_to_BS n.+2) pr1 (dltw a) @ _).
  exact (deloop_rec_truncfib_beta_dltw Type (fun n A => merely (A <~> Fin n)) BS_trunc _ dtb_dlpt0b dtb_dlpt0f dtb_dlib dtb_dlif dtb_dltwb dtb_dldob dtb_dlbrb n a).
Defined.

Definition ap_deloop_to_BSb_ap_dli
  {n} {a b : deloop n} (p : a = b)
  : ap (deloop_to_BSb n.+1) (ap dli p) = ap add (ap (deloop_to_BSb n) p).
Proof.
  induction p; constructor.
Defined.

(** We define our preferred finite types **)
Definition FFin (n : nat)
  : Type
  := deloop_to_BSb n (dlpt n).

Lemma FFin_Fin
  : forall n : nat, FFin n = Fin n.
Proof.
  induction n.
  + constructor.
  + exact (ap add IHn).
Defined.


(** Some results we can achieve via deloop_to_BS **)

Lemma not_dltw_idpath {n : nat} (a : deloop n)
  : dltw a = idpath -> Empty.
Proof.
  intro p.
  apply (@not_omega_id (deloop_to_BSb n a)).
  refine ((eisretr (equiv_path _ _) _)^ @ _ @ eisretr (equiv_path _ _) _); apply ap.
  change (gamma (deloop_to_BSb n a) = path_universe_uncurried 1%equiv).
  refine (_ @ path_universe_1^).
  refine ((ap_deloop_to_BSb_dltw a)^ @ _).
  exact (ap (ap (deloop_to_BSb n.+2)) p).
Defined.

Lemma not_deloop_set_from_2 (n : nat)
  : (forall (a b : deloop n.+2) (p q : a = b), p = q) -> Empty.
Proof.
  intro abs.
  exact (not_dltw_idpath (dlpt n) (abs (dlpt n.+2) (dlpt n.+2) (dltw (dlpt n)) idpath)).
Defined.


(** Definition of the function deloop_dot -> BS_dot **)

Definition deloop_to_BS_dot
  : deloop_dot -> BS_dot
  := sigma_function idmap deloop_to_BS.

Definition deloop_to_BSb_dot
  : deloop_dot -> Type
  := fun x => (deloop_to_BS_dot x).2.1.

Definition deloop_to_BS_dot'
  : deloop_dot -> BS_dot'
  := BS_dot_dot' o deloop_to_BS_dot.

Definition Saddb
  : nat * Type -> nat * Type
  := fun x => match x with (n, A) => (S n, add A) end.

Definition Sadd
  : BS_dot' -> BS_dot'
  := @sigma_function (nat * Type) (fun z => merely (snd z <~> Fin (fst z))) (nat * Type) (fun z => merely (snd z <~> Fin (fst z))) Saddb (fun z => dtb_dlif (fst z) (snd z)).

Lemma deloop_to_BS_dot'_Sdli
  : forall x : deloop_dot, deloop_to_BS_dot' (Sdli x) = Sadd (deloop_to_BS_dot' x).
Proof.
  constructor.
Defined.

(** Sketch of the proof that it is a symmetric monoidal functor **)
Open Scope nat.

Definition deloop_to_BS_dot'_0
  : BS_dot'_e = deloop_to_BS_dot' (dlpt0_dot)
  := idpath.

  Definition deloop_to_BS_dot'_2_dlpt0 (m : nat) (b : deloop m)
    : BS_dot'_product (deloop_to_BS_dot' (0; dlpt0)) (deloop_to_BS_dot' (m; b)) = deloop_to_BS_dot' (deloop_m (0; dlpt0) (m; b)).
  Proof.
    intros.
    srefine (sigma_truncfib _ _ _); simpl.
    exact (path_prod' idpath (lambda_U _)).
  Defined.

  Definition deloop_to_BS_dot'_2_dli (m : nat) (b : deloop m)
    : forall (n : nat) (a : deloop.deloop n),
    BS_dot'_product (deloop_to_BS_dot' (n; a)) (deloop_to_BS_dot' (m; b)) = deloop_to_BS_dot' (deloop_m (n; a) (m; b)) ->
    BS_dot'_product (deloop_to_BS_dot' (n.+1; dli a)) (deloop_to_BS_dot' (m; b)) = deloop_to_BS_dot' (deloop_m (n.+1; dli a) (m; b)).
  Proof.
    intros n a h.
    srefine (sigma_truncfib _ _ _).
    change (((n + m).+1, (deloop_to_BSb n a + Unit + deloop_to_BSb m b)%type) = ((deloop_to_BS_dot (deloop_m (n; a) (m; b))).1.+1,
deloop_to_BSb_dot (Sdli (deloop_m (n; a) (m; b))))).
    refine (path_prod' idpath (alpha_U _ _ _ @ (ap011 (fun X Y => (X + Y)%type) idpath (tau_U _ _)) @ (alpha_U _ _ _)^) @ _).
    change (Saddb (n + m, (deloop_to_BSb n a + deloop_to_BSb m b)%type) = (((deloop_to_BS_dot (deloop_m (n; a) (m; b))).1).+1, deloop_to_BSb_dot (Sdli (deloop_m (n; a) (m; b))))).
    exact (ap Saddb h..1).
  Defined.

  Definition deloop_to_BS_dot'_2_dltw (m : nat) (b : deloop m)
    : forall (n : nat) (a : deloop n) (a' : BS_dot'_product (deloop_to_BS_dot' (n; a)) (deloop_to_BS_dot' (m; b)) =
      deloop_to_BS_dot' (deloop_m (n; a) (m; b))),
      transport
        (fun a0 : deloop n.+2 => BS_dot'_product (deloop_to_BS_dot' (n.+2; a0)) (deloop_to_BS_dot' (m; b)) = deloop_to_BS_dot' (deloop_m (n.+2; a0) (m; b)))
        (dltw a)
        (deloop_to_BS_dot'_2_dli m b n.+1 (dli a) (deloop_to_BS_dot'_2_dli m b n a a'))
      = deloop_to_BS_dot'_2_dli m b n.+1 (dli a) (deloop_to_BS_dot'_2_dli m b n a a').
  Proof.
    intros n a h; hnf.
    refine (@transport_paths_FlFr (deloop n.+2) _ (fun a0 => BS_dot'_product (deloop_to_BS_dot' (n.+2; a0)) (deloop_to_BS_dot' (m; b))) (fun a0 => deloop_to_BS_dot' (deloop_m (n.+2; a0) (m; b))) _ _ (dltw a) _ @ concat_pp_p _ _ _ @ _); apply moveR_Vp.
    (* ignore second component; split for nat and Type;
        for nat this is trivial, as nat is a set;
        for Type (see thesis) we can look at the equivalences instead of the paths, and verify that the underlying functions are homotopic *)
  Admitted.

Definition deloop_to_BS_dot'_2
  : forall x y : deloop_dot, 
    BS_dot'_product (deloop_to_BS_dot' x) (deloop_to_BS_dot' y) = deloop_to_BS_dot' (deloop_m x y).
Proof.
  intros [n a] [m b]; revert a; revert n.
  assert (T : forall (n : nat) (a : deloop n), IsHSet (BS_dot'_product (deloop_to_BS_dot' (n; a)) (deloop_to_BS_dot' (m; b)) = deloop_to_BS_dot' (deloop_m (n; a) (m; b)))).
  { intros. srapply @istrunc_paths. exact BS_dot'_trunc. }
  srefine (deloop_ind_to_set _ _ _ _ T); clear T; hnf.
  + exact (deloop_to_BS_dot'_2_dlpt0 m b).
  + exact (deloop_to_BS_dot'_2_dli m b).
  + exact (deloop_to_BS_dot'_2_dltw m b).
Defined.

(* the _alp, _lam, _rho and _tau components only involve deloop_to_BS_dot'_2_dlpt0 and deloop_to_BS_dot'_2_dli;
   again one can look at the 2-paths in the base (nat * Type) and solve in nat by its 0-truncation and in Type by looking at the corresponding functions *)

End deloop_to_BS.
