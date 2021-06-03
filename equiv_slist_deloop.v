Require Export UnivalenceImpliesFunext.
(* Require Export deloop_to_BS. *)
Require Export slists.
Require Export deloop.

(** An equivalence slist Unit <~> deloop_dot **)
Section slist_Unit_deloop.
Let deloop := deloop.deloop.

Context `{Univalence}.
Open Scope nat.

(** function slist Unit -> deloop_dot **)
  Lemma cons'_for_slist_Unit_to_deloop
    : Unit -> deloop_dot -> deloop_dot.
  Proof.
    intros _. exact Sdli.
  Defined.

  Lemma swap'_for_slist_Unit_to_deloop
    : swap'_rec_type deloop_dot cons'_for_slist_Unit_to_deloop.
  Proof.
    unfold swap'_rec_type.
    intros [] [] a; unfold cons'_for_slist_Unit_to_deloop.
    exact (dltw_dot a).
  Defined.

  Lemma double'_for_slist_Unit_to_deloop
    : double'_rec_type deloop_dot cons'_for_slist_Unit_to_deloop swap'_for_slist_Unit_to_deloop.
  Proof.
    unfold double'_rec_type.
    intros [] [] a; unfold swap'_for_slist_Unit_to_deloop.
    exact (dldo_dot a).
  Qed.

  Lemma triple'_for_slist_Unit_to_deloop
    : triple'_rec_type deloop_dot cons'_for_slist_Unit_to_deloop swap'_for_slist_Unit_to_deloop.
  Proof.
    unfold triple'_rec_type.
    intros [] [] [] a; unfold cons'_for_slist_Unit_to_deloop, swap'_for_slist_Unit_to_deloop.
    exact (dlbr_dot a).
  Qed.

Definition slist_Unit_to_deloop
  : slist Unit -> deloop_dot.
Proof.
  srapply @slist_rec.
  + exact (0; dlpt0).
  + exact cons'_for_slist_Unit_to_deloop.
  + exact swap'_for_slist_Unit_to_deloop.
  + exact double'_for_slist_Unit_to_deloop.
  + exact triple'_for_slist_Unit_to_deloop.
  + exact dlT_dot.
Defined.

(** function deloop_dot -> slist Unit **)

  Lemma dli'_for_deloop_to_slist_Unit
    : nat -> slist Unit -> slist Unit.
  Proof.
    intros _ l; exact (cons tt l).
  Defined.

  Lemma dltw'_for_deloop_to_slist_Unit
    : dltw'_rec_type (fun _ : nat => slist Unit) dli'_for_deloop_to_slist_Unit.
  Proof.
    unfold dltw'_rec_type, dli'_for_deloop_to_slist_Unit.
    intros _ l. exact (swap tt tt l).
  Defined.

  Lemma dldo'_for_deloop_to_slist_Unit
    : dldo'_rec_type (fun _ : nat => slist Unit) dli'_for_deloop_to_slist_Unit dltw'_for_deloop_to_slist_Unit.
  Proof.
    unfold dldo'_rec_type, dltw'_for_deloop_to_slist_Unit.
    intros ? l; exact (double tt tt l).
  Defined.

  Lemma dlbr'_for_deloop_to_slist_Unit
    : dlbr'_rec_type (fun _ : nat => slist Unit) dli'_for_deloop_to_slist_Unit dltw'_for_deloop_to_slist_Unit.
  Proof.
    unfold dlbr'_rec_type, dltw'_for_deloop_to_slist_Unit, dli'_for_deloop_to_slist_Unit.
    intros _ l.
    change ((swap tt tt (cons tt l) @ ap (cons tt) (swap tt tt l)) @ swap tt tt (cons tt l) = (ap (cons tt) (swap tt tt l) @ swap tt tt (cons tt l)) @ ap (cons tt) (swap tt tt l)).
    exact (triple tt tt tt l).
  Defined.

Definition deloop_to_slist_Unit
  : deloop_dot -> slist Unit.
Proof.
  intros [n a]; revert a; revert n.
  srapply @deloop_rec; simpl. (* here we could also use deloop_rec_const! *)
  + exact nil.
  + exact dli'_for_deloop_to_slist_Unit.
  + exact dltw'_for_deloop_to_slist_Unit.
  + exact dldo'_for_deloop_to_slist_Unit.
  + exact dlbr'_for_deloop_to_slist_Unit.
  + intro; apply T_slist.
Defined.

(** proof of equivalence **)

Lemma Sect_deloop_to_slist_Unit_slist_Unit_to_deloop
  : Sect deloop_to_slist_Unit slist_Unit_to_deloop.
Proof.
  unfold Sect; intros [n a]; revert a; revert n.
  srapply @deloop_ind_to_set; hnf.
  + constructor.
  + intros n a a'.
    refine (ap (sigma_function S (fun n => dli)) a').
  + intros n a a'; simpl.
    refine (@transport_paths_FlFr (deloop n.+2) {n : nat & deloop n} (fun s => slist_Unit_to_deloop (deloop_to_slist_Unit (n.+2; s))) (fun s => (n.+2; s)) _ _ (dltw a) _ @ _).
    refine (concat_pp_p _ _ _ @ _); apply moveR_Vp.
    rewrite (ap_compose (fun s => deloop_to_slist_Unit (n.+2; s)) slist_Unit_to_deloop (dltw a)).
    unfold deloop_to_slist_Unit.
    rewrite (deloop_rec_beta_dltw (fun _ => slist Unit) nil dli'_for_deloop_to_slist_Unit dltw'_for_deloop_to_slist_Unit dldo'_for_deloop_to_slist_Unit dlbr'_for_deloop_to_slist_Unit (fun _ => T_slist) n a).
    unfold dltw'_for_deloop_to_slist_Unit.
    change (
ap (sigma_function S (fun n0 : nat => dli)) (ap (sigma_function S (fun n0 : nat => dli)) a') @
ap (fun s : deloop n.+2 => (n.+2; s)) (dltw a) =
ap slist_Unit_to_deloop (swap tt tt (deloop_to_slist_Unit (n; a))) @
ap (sigma_function S (fun n0 : nat => dli)) (ap (sigma_function S (fun n0 : nat => dli)) a')
    ).
    unfold slist_Unit_to_deloop.
    rewrite (slist_rec_beta_swap {n : nat & deloop n} trunc_sigma (0; dlpt0) cons'_for_slist_Unit_to_deloop swap'_for_slist_Unit_to_deloop double'_for_slist_Unit_to_deloop triple'_for_slist_Unit_to_deloop tt tt (deloop_to_slist_Unit (n; a))).
    change (
ap (sigma_function S (fun n0 : nat => dli)) (ap (sigma_function S (fun n0 : nat => dli)) a') @
ap (fun s : deloop n.+2 => (n.+2; s)) (dltw a) =
swap'_for_slist_Unit_to_deloop tt tt (slist_Unit_to_deloop (deloop_to_slist_Unit (n; a))) @
ap (sigma_function S (fun n0 : nat => dli)) (ap (sigma_function S (fun n0 : nat => dli)) a')
    ).
    unfold swap'_for_slist_Unit_to_deloop.
    rewrite ap_to_fiber_path_sigma'_1.
    exact (dltw_natural_n_sigma_f (slist_Unit_to_deloop o deloop_to_slist_Unit) a').
  + intros. srapply dlT_dot.
Defined.

Lemma Sect_slist_Unit_to_deloop_deloop_to_slist_Unit
  : Sect slist_Unit_to_deloop deloop_to_slist_Unit.
Proof.
  unfold Sect.
  srapply @slist_ind_to_set; hnf.
  + constructor.
  + intros [] l l'.
    exact (ap (cons tt) l').
  + intros [] [] l IHl.
    refine (@transport_paths_FFlr _ _ slist_Unit_to_deloop deloop_to_slist_Unit _ _ (swap _ _ l) _ @ _).
    refine (concat_pp_p _ _ _ @ _); apply moveR_Vp.
    unfold slist_Unit_to_deloop.
    rewrite (slist_rec_beta_swap {n : nat & deloop n} trunc_sigma (0; dlpt0) _ _ _ triple'_for_slist_Unit_to_deloop).
    change (
ap (cons tt) (ap (cons tt) IHl) @ swap tt tt l = ap deloop_to_slist_Unit (swap'_for_slist_Unit_to_deloop tt tt (slist_Unit_to_deloop l)) @ ap (cons tt) (ap (cons tt) IHl)
    ).
    unfold swap'_for_slist_Unit_to_deloop.
    change (
ap (cons tt) (ap (cons tt) IHl) @ swap tt tt l =
ap deloop_to_slist_Unit (path_sigma' (fun n : nat => deloop n) 1 (dltw (slist_Unit_to_deloop l).2)) @
ap (cons tt) (ap (cons tt) IHl)
    ).
    unfold deloop_to_slist_Unit.
    change (
ap (cons tt) (ap (cons tt) IHl) @ swap tt tt l = ap (fun na : {n : nat & deloop n} => deloop_rec (fun _ : nat => slist Unit) nil dli'_for_deloop_to_slist_Unit dltw'_for_deloop_to_slist_Unit dldo'_for_deloop_to_slist_Unit dlbr'_for_deloop_to_slist_Unit (fun _ : nat => T_slist) na.1 na.2) (path_sigma' (fun n : nat => deloop n) 1 (dltw (slist_Unit_to_deloop l).2)) @ ap (cons tt) (ap (cons tt) IHl)
    ).
    rewrite ap_base_path_sigma'_1.
    rewrite (deloop_rec_beta_dltw (fun _ => slist Unit) nil _ _ _ dlbr'_for_deloop_to_slist_Unit (fun _ => T_slist) (slist_Unit_to_deloop l).1 (slist_Unit_to_deloop l).2).
    unfold dltw'_for_deloop_to_slist_Unit.
    exact (swap_natural tt tt IHl)^.
  + intros; srapply T_slist.
Defined.

Lemma slist_Unit_deloop
  : slist Unit <~> deloop_dot.
Proof.
  srapply @equiv_adjointify.
  + exact slist_Unit_to_deloop.
  + exact deloop_to_slist_Unit.
  + exact Sect_deloop_to_slist_Unit_slist_Unit_to_deloop.
  + exact Sect_slist_Unit_to_deloop_deloop_to_slist_Unit.
Defined.

(** proof that slist_Unit_to_deloop is a symmetric monoidal functor **)

Lemma ap_slist_Unit_to_deloop_ap_cons
  {x : Unit} {l l' : slist Unit} (p : l = l')
  : ap slist_Unit_to_deloop (ap (cons x) p) = ap Sdli (ap slist_Unit_to_deloop p).
Proof.
  induction p; constructor.
Defined.

Definition ap_slist_Unit_to_deloop_sapp
  (l l2 : slist Unit)
  : ap (fun w : slist Unit => slist_Unit_to_deloop (w ++ l2)) (swap tt tt l) = dltw_dot (slist_Unit_to_deloop (l ++ l2)).
Proof.
  refine (ap_compose (fun w : slist Unit => w ++ l2) slist_Unit_to_deloop _ @ _).
  refine (ap (ap slist_Unit_to_deloop) (sapp_blank_beta_swap tt tt l l2) @ _).
  exact (slist_rec_beta_swap _ _ _ _ _ _ _ tt tt (l ++ l2)).
Qed.

Lemma ap_deloop_m_slist_Unit_to_deloop
  (l l2 : slist Unit)
  : ap (fun w : slist Unit => deloop_m (slist_Unit_to_deloop w) (slist_Unit_to_deloop l2)) (swap tt tt l) = dltw_dot (deloop_m (slist_Unit_to_deloop l) (slist_Unit_to_deloop l2)).
Proof.
  refine (ap_compose slist_Unit_to_deloop (fun w => deloop_m w (slist_Unit_to_deloop l2)) _ @ _).
  refine (ap (ap (fun w : deloop_dot => deloop_m w (slist_Unit_to_deloop l2))) (slist_rec_beta_swap _ _ _ _ _ _ _ tt tt l) @ _).
  change (ap (fun w : deloop_dot => deloop_m w (slist_Unit_to_deloop l2)) (dltw_dot (slist_Unit_to_deloop l)) = dltw_dot (deloop_m (slist_Unit_to_deloop l) (slist_Unit_to_deloop l2))).
  srapply @ap_deloop_m_dltw_dot.
Defined.

  Definition slist_Unit_to_deloop_2
    : forall l1 l2 : slist Unit, deloop_m (slist_Unit_to_deloop l1) (slist_Unit_to_deloop l2) = slist_Unit_to_deloop (l1 ++ l2).
  Proof.
    intros l1 l2; revert l1.
    srapply @slist_ind_to_paths_in_gpd.
    + constructor.
    + hnf. intros x l IHl.
      change (Sdli (deloop_m (slist_Unit_to_deloop l) (slist_Unit_to_deloop l2)) = Sdli (slist_Unit_to_deloop (l ++ l2))).
      apply ap. exact IHl.
    + simpl; intros [] [] l IHl.
      refine (whiskerL _ (ap_slist_Unit_to_deloop_sapp l l2) @ dltw_dot_natural IHl @ _); apply whiskerR.
      exact (ap_deloop_m_slist_Unit_to_deloop _ _)^.
    + exact dlT_dot.
  Defined.

  Lemma slist_Unit_to_deloop_alp
    : forall l1 l2 l3 : slist Unit,
    alpha_deloop (slist_Unit_to_deloop l1) (slist_Unit_to_deloop l2) (slist_Unit_to_deloop l3) @ (ap011 deloop_m idpath (slist_Unit_to_deloop_2 l2 l3) @ slist_Unit_to_deloop_2 l1 (l2 ++ l3)) = (ap011 deloop_m (slist_Unit_to_deloop_2 l1 l2) idpath @ slist_Unit_to_deloop_2 (l1 ++ l2) l3) @ ap slist_Unit_to_deloop (alpha_slist l1 l2 l3).
  Proof.
    intros l1 l2 l3; revert l1.
    srapply (slist_ind_to_2paths_in_gpd _ dlT_dot); hnf.
    + refine (concat_1p _ @ concat_p1 _ @ _ @ (concat_1p _)^ @ (concat_p1 _)^).
      change (ap011 deloop_m (idpath (slist_Unit_to_deloop nil)) (slist_Unit_to_deloop_2 l2 l3) = slist_Unit_to_deloop_2 l2 l3).
      generalize (slist_Unit_to_deloop_2 l2 l3); induction p; constructor.
    + intros [] l IHl.
      change (ap Sdli (alpha_deloop (slist_Unit_to_deloop l) (slist_Unit_to_deloop l2) (slist_Unit_to_deloop l3)) @
(ap011 deloop_m (ap Sdli (idpath (slist_Unit_to_deloop l))) (slist_Unit_to_deloop_2 l2 l3) @ slist_Unit_to_deloop_2 (tt :: l) (l2 ++ l3)) =
(ap011 deloop_m (slist_Unit_to_deloop_2 (tt :: l) l2) 1 @ ap Sdli (slist_Unit_to_deloop_2 (l ++ l2) l3)) @
ap slist_Unit_to_deloop (ap (cons tt) (alpha_slist l l2 l3))).
      refine (_ @ whiskerL _ (ap_slist_Unit_to_deloop_ap_cons _)^).
      refine (whiskerL _ (whiskerR (ap011_deloop_m_ap_Sdli _ _) _) @ _).
      change (ap Sdli (alpha_deloop (slist_Unit_to_deloop l) (slist_Unit_to_deloop l2) (slist_Unit_to_deloop l3)) @
(ap Sdli (ap011 deloop_m 1 (slist_Unit_to_deloop_2 l2 l3)) @ ap Sdli (slist_Unit_to_deloop_2 l (l2 ++ l3))) =
(ap011 deloop_m (ap Sdli (slist_Unit_to_deloop_2 l l2)) 1 @ ap Sdli (slist_Unit_to_deloop_2 (l ++ l2) l3)) @
ap Sdli (ap slist_Unit_to_deloop (alpha_slist l l2 l3))).
      refine (_ @ whiskerR (whiskerR (ap011_deloop_m_ap_Sdli _ _)^ _) _).
      repeat rewrite <- (ap_pp Sdli); apply ap.
      exact IHl.
  Qed.

  Lemma slist_Unit_to_deloop_lam
    : forall l2 : slist Unit,
    lambda_deloop (slist_Unit_to_deloop l2) = (ap011 deloop_m 1 1 @ slist_Unit_to_deloop_2 nil l2) @ ap slist_Unit_to_deloop (lambda_slist l2).
  Proof.
    constructor.
  Qed.

  Lemma slist_Unit_to_deloop_rho
    : forall l1 : slist Unit,
    rho_deloop (slist_Unit_to_deloop l1) = (ap011 deloop_m 1 1 @ slist_Unit_to_deloop_2 l1 nil) @ ap slist_Unit_to_deloop (rho_slist l1).
  Proof.
    srapply (slist_ind_to_2paths_in_gpd _ dlT_dot); hnf.
    + simpl. constructor.
    + intros [] l IHl; simpl.
      change (ap Sdli (rho_deloop (slist_Unit_to_deloop l)) = (ap Sdli idpath @ ap Sdli (slist_Unit_to_deloop_2 l nil)) @ ap slist_Unit_to_deloop (ap (cons tt) (rho_slist l))).
      refine (_ @ whiskerL _ (ap_slist_Unit_to_deloop_ap_cons _)^).
      repeat rewrite <- (ap_pp Sdli); apply ap.
      exact IHl.
  Qed.

    Lemma slist_Unit_to_deloop_tau_cons (l : slist Unit)
      : forall l2 : slist Unit,
      tau_deloop_Q (slist_Unit_to_deloop l) (slist_Unit_to_deloop l2) @ slist_Unit_to_deloop_2 l2 (tt :: l) = ap Sdli (slist_Unit_to_deloop_2 l2 l) @ ap slist_Unit_to_deloop (sapp_Q tt l l2).
    Proof.
      srapply (slist_ind_to_2paths_in_gpd _ dlT_dot); hnf.
      + constructor.
      + intros [] l2 IHl2.
        change (dltw_dot (deloop_m (slist_Unit_to_deloop l2) (slist_Unit_to_deloop l)) @ ap Sdli (tau_deloop_Q (slist_Unit_to_deloop l) (slist_Unit_to_deloop l2)) @ ap Sdli (slist_Unit_to_deloop_2 l2 (tt :: l)) = ap Sdli (ap Sdli (slist_Unit_to_deloop_2 l2 l)) @ ap slist_Unit_to_deloop (swap tt tt (sapp l2 l) @ ap (cons tt) (sapp_Q tt l l2))).
        rewrite (ap_pp slist_Unit_to_deloop).
        rewrite ap_slist_Unit_to_deloop_ap_cons.
        refine (concat_pp_p _ _ _ @ _); rewrite <- (ap_pp Sdli).
        refine (whiskerL _ (ap (ap Sdli) IHl2) @ _); rewrite (ap_pp Sdli).
        refine (concat_p_pp _ _ _ @ whiskerR (dltw_dot_natural _)^ _ @ concat_pp_p _ _ _ @ _);
        apply whiskerL; apply whiskerR.
        symmetry. srapply @slist_rec_beta_swap.
    Qed.

  Lemma slist_Unit_to_deloop_tau
    : forall l1 l2 : slist Unit,
    tau_deloop (slist_Unit_to_deloop l1) (slist_Unit_to_deloop l2) @ slist_Unit_to_deloop_2 l2 l1 = slist_Unit_to_deloop_2 l1 l2 @ ap slist_Unit_to_deloop (tau_slist l1 l2).
  Proof.
    srapply (slist_ind_to_fam_2paths_in_gpd _ dlT_dot); hnf.
    + srapply (slist_ind_to_2paths_in_gpd _ dlT_dot); hnf.
      - constructor.
      - intros [] l h.
        change (ap Sdli (tau_deloop (slist_Unit_to_deloop nil) (slist_Unit_to_deloop l)) @ ap Sdli (slist_Unit_to_deloop_2 l nil) = ap Sdli (slist_Unit_to_deloop_2 nil l) @ ap slist_Unit_to_deloop (ap (cons tt) (tau_slist nil l))).
        rewrite ap_slist_Unit_to_deloop_ap_cons.
        repeat rewrite <- (ap_pp Sdli); apply ap; exact h.
    + intros [] l IHl l2.
      change ((ap Sdli (tau_deloop (slist_Unit_to_deloop l) (slist_Unit_to_deloop l2)) @ tau_deloop_Q (slist_Unit_to_deloop l) (slist_Unit_to_deloop l2)) @
slist_Unit_to_deloop_2 l2 (tt :: l) = ap Sdli (slist_Unit_to_deloop_2 l l2) @ ap slist_Unit_to_deloop (ap (cons tt) (tau_slist l l2) @ sapp_Q tt l l2));
      rewrite ap_pp; rewrite ap_slist_Unit_to_deloop_ap_cons.
      refine (concat_pp_p _ _ _ @ _ @ concat_p_pp _ _ _ @ whiskerR ((ap_pp Sdli _ _)^ @ ap (ap Sdli) (IHl l2) @ ap_pp Sdli _ _) _ @ concat_pp_p _ _ _);
      apply whiskerL.
      srapply @slist_Unit_to_deloop_tau_cons.
  Defined.

Definition slist_Unit_to_deloop_SymMonFun
  : SymMonoidalFunctor (slistSMG Unit) deloopSMG
  := @Build_SymMonoidalFunctor (slistSMG Unit) deloopSMG slist_Unit_to_deloop idpath slist_Unit_to_deloop_2 slist_Unit_to_deloop_alp slist_Unit_to_deloop_lam slist_Unit_to_deloop_rho slist_Unit_to_deloop_tau.

(** proof of the symmetric monoidal equivalence **)

Theorem slist_Unit_deloop_SymMonEquivalence
  : SymMonoidalEquivalence (slistSMG Unit) deloopSMG.
Proof.
  srapply SymMonoidalEquivalence_from_equivalence.
  + exact slist_Unit_to_deloop_SymMonFun.
  + simpl. exact (equiv_isequiv slist_Unit_deloop).
Defined.

End slist_Unit_deloop.