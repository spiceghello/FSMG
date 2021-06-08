Require Export deloop_to_BS.

(** Equivalence: formalization is not complete **)

Section equiv_deloop_to_BS.
Open Scope nat.
Let deloop := deloop.deloop.

Context `{Univalence}.

(** deloop_to_BS n is an equivalence if
ap (deloop_to_BSb) : (a = dlpt n) -> (deloop_to_BSb a = Finn n)
is an embedding for every a : deloop n **)

Theorem condition_equiv_deloop_to_BS (n : nat)
  : (forall (a : deloop n) (p : deloop_to_BSb n a = FFin n), {q : a = dlpt n & ap (deloop_to_BSb n) q = p}) ->
    IsEquiv (deloop_to_BS n).
Proof.
  intro h.
  srapply @isequiv_fcontr.  (* to show that it is an equivalence, we can check that the all fibers are contractible *)
  refine (forall_BS_hprop n _ _ (deloop_to_BS n (dlpt n)) _); (* since BS n.+2 is connected, we can verify only selected fibers *)
  hnf.
  srapply @contr_sigma_prop; (* since the family is of paths in a sigma-type with contractible fibers, we ignore those *)
  change (Contr {a : deloop n & deloop_to_BSb n a = FFin n}).
  srapply @Build_Contr.
  { exact (dlpt n; idpath). } (* center of contraction *)
  (* we need the proof of contraction *)
  intros [a p]. symmetry. srapply @path_sigma; simpl.
  + exact (h a p).1.
  + refine (@transport_paths_Fl (deloop n) _ (deloop_to_BSb n) _ _ (FFin n) (h a p).1 p @ _);
    apply moveR_Vp; refine (_ @ (concat_p1 _)^).
    exact (h a p).2^.
Defined.

(** in order to verify the embedding, we can use the elimination principle of deloop **)

  Lemma conditions_equiv_deloop_to_BS_b_dltw
    (eib : forall (n : nat) (a : deloop n), (deloop_to_BSb n a = FFin n -> a = dlpt n) -> deloop_to_BSb n.+1 (dli a) = FFin n.+1 -> dli a = dlpt n.+1)
    (etwb : forall (n : nat) (a' : deloop_to_BSb n (dlpt n) = FFin n -> dlpt n = dlpt n) (p : FFin n.+2 = FFin n.+2),
      eib n.+1 (dli (dlpt n)) (eib n (dlpt n) a') (gamma (FFin n) @ p)
      = dltw (dlpt n) @ eib n.+1 (dli (dlpt n)) (eib n (dlpt n) a') p)
    : forall (n : nat) (a : deloop.deloop n) (a' : deloop_to_BSb n a = FFin n -> a = dlpt n), transport (fun a0 : deloop n.+2 => deloop_to_BSb n.+2 a0 = FFin n.+2 -> a0 = dlpt n.+2) (dltw a) (eib n.+1 (dli a) (eib n a a')) = eib n.+1 (dli a) (eib n a a').
  Proof.
    intros. by_extensionality p.
    refine (@transport_forall_fun_path_idmap_l_const_r (deloop n.+2) (fun a => deloop_to_BSb n.+2 a = FFin n.+2) (dlpt n.+2) _ _ (dltw a) _ p @ _); apply moveR_Vp.
    refine (ap (eib n.+1 (dli a) (eib n a a')) (@transport_paths_Fl (deloop n.+2) _ (deloop_to_BSb n.+2) _ _ _ (dltw a)^ p @ whiskerR (ap inverse (ap_V _ _) @ inv_V _ @ ap_deloop_to_BSb_dltw a) _) @ _).
    revert p; revert a'; revert a.
    assert (T : forall a : deloop n, IsHProp (forall (a' : deloop_to_BSb n a = FFin n -> a = dlpt n) (p : deloop_to_BSb n.+2 (dli (dli a)) = FFin n.+2), eib n.+1 (dli a) (eib n a a') (gamma (deloop_to_BSb n a) @ p) = dltw a @ eib n.+1 (dli a) (eib n a a') p)).
    { intros. enough (forall (a' : deloop_to_BSb n a = FFin n -> a = dlpt n) (p : deloop_to_BSb n.+2 (dli (dli a)) = FFin n.+2), IsHProp (eib n.+1 (dli a) (eib n a a') (gamma (deloop_to_BSb n a) @ p) = dltw a @ eib n.+1 (dli a) (eib n a a') p)). { srapply @trunc_forall. }
      intros. srapply @istrunc_paths. srapply @istrunc_paths. apply dlT. }
    srefine (@conn_to_prop _ (deloop n) (Connected_deloopn n) _ T (dlpt n) _); hnf.
    exact (etwb n).
  Qed.

  Definition conditions_equiv_deloop_to_BS_b
  (e0b : deloop_to_BSb 0 dlpt0 = FFin 0 -> dlpt0 = dlpt 0)
  (eib : forall (n : nat) (a : deloop n) (ihb : deloop_to_BSb n a = FFin n -> a = dlpt n), deloop_to_BSb n.+1 (dli a) = FFin n.+1 -> dli a = dlpt n.+1)
  (etwb : forall (n : nat) (a' : deloop_to_BSb n (dlpt n) = FFin n -> dlpt n = dlpt n) (p : FFin n.+2 = FFin n.+2),
    eib n.+1 (dli (dlpt n)) (eib n (dlpt n) a') (gamma (FFin n) @ p)
    = dltw (dlpt n) @ eib n.+1 (dli (dlpt n)) (eib n (dlpt n) a') p)
    : forall (n : nat) (a : deloop n), deloop_to_BSb n a = FFin n -> a = dlpt n.
  Proof.
    assert (T : forall n a, IsHSet (deloop_to_BSb n a = FFin n -> a = dlpt n)).
    { intros. enough (deloop_to_BSb n a = FFin n -> IsHSet (a = dlpt n)). { apply trunc_forall. }
      intros. srapply @istrunc_paths. apply dlT. }
    srefine (deloop_ind_to_set _ e0b eib (conditions_equiv_deloop_to_BS_b_dltw eib etwb) T).
  Defined.

Lemma conditions_equiv_deloop_to_BS
  (e0b : deloop_to_BSb 0 dlpt0 = FFin 0 -> dlpt0 = dlpt 0)
  (eib : forall (n : nat) (a : deloop n) (ihb : deloop_to_BSb n a = FFin n -> a = dlpt n), deloop_to_BSb n.+1 (dli a) = FFin n.+1 -> dli a = dlpt n.+1)
  (etwb : forall (n : nat) (a' : deloop_to_BSb n (dlpt n) = FFin n -> dlpt n = dlpt n) (p : FFin n.+2 = FFin n.+2),
    eib n.+1 (dli (dlpt n)) (eib n (dlpt n) a') (gamma (FFin n) @ p)
    = dltw (dlpt n) @ eib n.+1 (dli (dlpt n)) (eib n (dlpt n) a') p)
  (e0f : forall p, ap (deloop_to_BSb 0) (e0b p) = p)
  (eif : forall (n : nat) (a : deloop n) (ihb : deloop_to_BSb n a = FFin n -> a = dlpt n) (ihf : forall (p : deloop_to_BSb n a = FFin n), ap (deloop_to_BSb n) (ihb p) = p) (p : deloop_to_BSb n.+1 (dli a) = FFin n.+1), ap (deloop_to_BSb n.+1) (eib n a ihb p) = p)
  : forall (n : nat), IsEquiv (deloop_to_BS n).
Proof.
  intro n. apply condition_equiv_deloop_to_BS; revert n.
  enough (e' : {eb : forall (n : nat) (a : deloop n), deloop_to_BSb n a = FFin n -> a = dlpt n & forall (n : nat) (a : deloop n) (p : deloop_to_BSb n a = FFin n), ap (deloop_to_BSb n) (eb n a p) = p}).
  { intros n a p. exact (e'.1 n a p; e'.2 n a p). }
  srefine (_; _).
  + exact (conditions_equiv_deloop_to_BS_b e0b eib etwb).
  + simpl. assert (T : forall n a, IsHProp (forall p : deloop_to_BSb n a = FFin n, ap (deloop_to_BSb n) (conditions_equiv_deloop_to_BS_b e0b eib etwb n a p) = p)).
    { intros. enough (forall p, IsHProp (ap (deloop_to_BSb n) (conditions_equiv_deloop_to_BS_b e0b eib etwb n a p) = p)).
      { srapply @trunc_forall. } intros. apply IsHProp_path2_in_BS_type. }
    srefine (deloop_ind_to_prop _ e0f _ T); hnf.
    intros. exact (eif n a (conditions_equiv_deloop_to_BS_b e0b eib etwb n a) a' p).
Defined.

(** Proofs of lemmas relative to dlpt0 **)

Definition e0b
  : deloop_to_BSb 0 dlpt0 = FFin 0 -> dlpt0 = dlpt 0
  := fun _ => idpath.

Definition e0f
  : forall p, ap (deloop_to_BSb 0) (e0b p) = p.
Proof.
  intros; simpl. srapply @path_ishprop.
Defined.

(** Combinatorics relative to dli **)

Arguments equiv_path {_} {_} _.

Definition move {n : nat}
  : FFin n -> FFin n = FFin n.
Proof.
  intro i; induction n.
  + exact idpath.
  + clear IHn. induction n.
    - exact idpath.
    - clear IHn. change (FFin n.+1 + Unit)%type in i. induction i as [j|[]].
      * induction n.
        ++ exact (gamma Empty).
        ++ change (FFin n.+1 + Unit)%type in j. induction j as [k|[]].
          -- exact (gamma (FFin n.+1) @ ap add (IHn k) @ gamma (FFin n.+1)).
          -- exact (gamma (FFin n.+1)).
      * exact idpath.
Defined.

Lemma move_inr_tt {n : nat}
  : @move n.+1 (inr tt) = idpath.
Proof.
  induction n; constructor.
Qed.

Lemma move_do' {n : nat} (i : FFin n)
  : (move i)^ = move i.
Proof.
  induction n.
  + simpl. constructor.
  + clear IHn. induction n.
    - simpl. constructor.
    - clear IHn. change (FFin n.+1 + Unit)%type in i; induction i as [j|[]].
      * induction n.
        ++ simpl. apply gamma_double'.
        ++ change (FFin n.+1 + Unit)%type in j; induction j as [k|[]].
          -- change ((gamma (FFin n.+1) @ ap add (@move n.+2 (inl k)) @ gamma (FFin n.+1))^ = gamma (FFin n.+1) @ ap add (@move n.+2 (inl k)) @ gamma (FFin n.+1)).
             refine (inv_pp _ _ @ concat2 (gamma_double' _) (inv_pp _ _ @ concat2 ((ap_V _ _)^ @ ap (ap add) _) (gamma_double' _)) @ concat_p_pp _ _ _).
             apply IHn.
          -- simpl. apply gamma_double'.
      * simpl. constructor.
Defined.

Lemma move_do {n : nat} (i : FFin n)
  : move i @ move i = idpath.
Proof.
  exact (whiskerL _ (move_do' i)^ @ concat_pV _).
Defined.

Lemma equiv_path_move_i_move_i {n : nat} (i : FFin n)
  : equiv_path (move i @ move i) = 1%equiv.
Proof.
  exact (ap equiv_path (move_do i)).
Defined.

Lemma equiv_path_move_i_i {n : nat} (i : FFin n.+1)
  : equiv_path (move i) i = inr tt.
Proof.
  induction n.
  - simpl. induction i as [[]|[]]. constructor.
  - clear IHn. change (FFin n.+1 + Unit)%type in i; induction i as [j|[]].
    * induction n.
      ++ simpl. rewrite (transport_idmap_path_universe (omega Empty)).
         induction j as [[]|[]]. constructor.
      ++ change (FFin n.+1 + Unit)%type in j; induction j as [k|[]].
        -- change (equiv_path (gamma (FFin n.+1) @ ap add (@move n.+2 (inl k)) @ gamma (FFin n.+1)) (inl (inl k)) = inr tt).
           repeat rewrite equiv_path_pp; unfold gamma.
           repeat rewrite (eisretr equiv_path).
           rewrite equiv_path_ap_add.
           change (omega (FFin n.+1) (exp (equiv_path (@move n.+2 (inl k))) (omega (FFin n.+1) (inl (inl k)))) = inr tt).
           change (omega (FFin n.+1) (exp (equiv_path (@move n.+2 (inl k))) (inl (inl k))) = inr tt).
           change (omega (FFin n.+1) (inl (equiv_path (@move n.+2 (inl k)) (inl k))) = inr tt).
           rewrite IHn.
           constructor.
        -- simpl. rewrite (transport_idmap_path_universe (omega (FFin n.+1))). constructor.
    * simpl. constructor.
Qed.

Definition path_last {A n} (p : (A + Unit)%type = FFin n.+1)
  : FFin n.+1
  := equiv_path p (inr tt).

Definition path_second_last {A n} (p : (A + Unit + Unit)%type = FFin n.+2)
  : FFin n.+2
  := equiv_path p (inl (inr tt)).

Definition path_last_ne_path_second_last {A n} (p : (A + Unit + Unit)%type = FFin n.+2)
  : path_last p = path_second_last p -> Empty.
Proof.
  refine (equiv_diff (equiv_path p) _).
  apply inr_ne_inl.
Defined.

Lemma path_last_gamma_p {A n} (p : (A + Unit + Unit)%type = FFin n.+2)
  : path_last (gamma A @ p) = path_second_last p.
Proof.
  unfold path_last. rewrite equiv_path_pp.
  change (equiv_path p (equiv_path (gamma A) (inr tt)) = path_second_last p).
  rewrite (eisretr equiv_path _). constructor.
Defined.

Lemma path_second_last_gamma_p {A n} (p : (A + Unit + Unit)%type = FFin n.+2)
  : path_second_last (gamma A @ p) = path_last p.
Proof.
  unfold path_second_last. rewrite equiv_path_pp.
  change (equiv_path p (equiv_path (gamma A) (inl (inr tt))) = path_last p).
  rewrite (eisretr equiv_path _). constructor.
Defined.

Lemma pre_reduce_last {A n} (p : (A + Unit)%type = FFin n.+1)
  : equiv_path (p @ move (path_last p)) (inr tt) = inr tt.
Proof.
  rewrite equiv_path_pp.
  change (equiv_path (move (path_last p)) (path_last p) = inr tt).
  srapply equiv_path_move_i_i.
Qed.

Definition reduce {A n} (p : (A + Unit)%type = FFin n.+1)
  : A = FFin n.
Proof.
  refine (path_universe_uncurried (restriction (equiv_path (p @ move (path_last p))) _)).
  apply pre_reduce_last.
Defined.

Lemma reduce_add {A n} (p : A = FFin n)
  : reduce (ap add p) = p.
Proof.
  unfold reduce, path_last.
  assert (h : equiv_path (ap add p @ @move n.+1 (equiv_path (ap add p) (inr tt))) = exp (equiv_path p)).
  { refine (_ @ equiv_path_ap_add _); apply ap.
    refine (_ @ concat_p1 _); apply whiskerL.
    rewrite equiv_path_ap_add.
    change (@move n.+1 (inr tt) = idpath).
    apply move_inr_tt. }
  refine (ap path_universe_uncurried (restriction_invariant _ _ (pre_reduce_last (ap add p)) h) @ _).
  refine (_ @ eissect equiv_path p); apply (ap path_universe_uncurried).
  refine (_ @ restriction_exp (equiv_path p)).
  apply restriction_invariant_p.
Qed.

Lemma ap_add_reduce {A n} (p : (A + Unit)%type = FFin n.+1)
  : ap add (reduce p) = p @ @move n.+1 (path_last p).
Proof.
  unfold reduce.
  refine (ap_add_ua _ @ _ @ eissect equiv_path _); apply (ap path_universe_uncurried).
  apply exp_restriction.
Defined.

Definition movedel {n : nat}
  : FFin n -> dlpt n = dlpt n.
Proof.
  intro i; induction n.
  + exact idpath.
  + clear IHn. induction n.
    - exact idpath.
    - clear IHn. change (FFin n.+1 + Unit)%type in i. induction i as [j|[]].
      * induction n.
        ++ exact (dltw dlpt0).
        ++ change (FFin n.+1 + Unit)%type in j. induction j as [k|[]].
          -- exact (dltw (dlpt n.+1) @ ap dli (IHn k) @ dltw (dlpt n.+1)).
          -- exact (dltw (dlpt n.+1)).
      * exact idpath.
Defined.

Lemma ap_deloop_to_BSb_movedel {n} (i : FFin n)
  : ap (deloop_to_BSb n) (movedel i) = move i.
Proof.
  induction n.
  + constructor.
  + clear IHn. induction n.
    - constructor.
    - clear IHn. change (FFin n.+1 + Unit)%type in i. induction i as [j|[]].
      * induction n.
        ++ exact (ap_deloop_to_BSb_dltw dlpt0).
        ++ change (FFin n.+1 + Unit)%type in j. induction j as [k|[]].
          -- change (ap (deloop_to_BSb n.+3) (dltw (dlpt n.+1) @ ap dli (@movedel n.+2 (inl k)) @ dltw (dlpt n.+1)) = gamma (FFin n.+1) @ ap add (@move n.+2 (inl k)) @ gamma (FFin n.+1)).
             refine (ap_pp _ _ _ @ whiskerR (ap_pp _ _ _) _ @ concat2 (concat2 (ap_deloop_to_BSb_dltw (dlpt n.+1)) _) (ap_deloop_to_BSb_dltw (dlpt n.+1))).
             refine (ap_deloop_to_BSb_ap_dli (@movedel n.+2 (inl k)) @ _); apply ap.
             exact (IHn k).
          -- exact (ap_deloop_to_BSb_dltw (dlpt n.+1)).
      * constructor.
Defined.

(** Proofs of lemmas relative to dli **)

Definition eib
  : forall (n : nat) (a : deloop n)
    (ihb : deloop_to_BSb n a = FFin n -> a = dlpt n),
    deloop_to_BSb n.+1 (dli a) = FFin n.+1 -> dli a = dlpt n.+1.
Proof.
  intros n a ihb p.
  exact (ap dli (ihb (reduce p)) @ @movedel n.+1 (path_last p)).
Defined.

Definition eif
  : forall (n : nat) (a : deloop n)
    (ihb : deloop_to_BSb n a = FFin n -> a = dlpt n)
    (ihf : forall (p : deloop_to_BSb n a = FFin n), ap (deloop_to_BSb n) (ihb p) = p)
    (p : deloop_to_BSb n.+1 (dli a) = FFin n.+1),
    ap (deloop_to_BSb n.+1) (eib n a ihb p) = p.
Proof.
  intros. unfold eib.
  refine (ap_pp _ _ _ @ _).
  rewrite ap_deloop_to_BSb_ap_dli.
  rewrite (ihf (reduce p)).
  rewrite ap_add_reduce.
  refine (concat_pp_p _ _ _ @ _ @ concat_p1 _); apply whiskerL.
  rewrite <- (move_do' _); apply moveR_Vp; refine (_ @ (concat_p1 _)^).
  srapply ap_deloop_to_BSb_movedel.
Qed.


(** Combinatorics relative to dltw **)

Lemma movedel_do {n : nat} (i : FFin n)
  : movedel i @ movedel i = idpath.
Proof.
  induction n.
  + simpl. constructor.
  + clear IHn. induction n.
    - simpl. constructor.
    - clear IHn. change (FFin n.+1 + Unit)%type in i; induction i as [j|[]].
      * induction n.
        ++ simpl. apply dldo.
        ++ change (FFin n.+1 + Unit)%type in j; induction j as [k|[]].
          -- change ((dltw (dlpt n.+1) @ ap dli (@movedel n.+2 (inl k)) @ dltw (dlpt n.+1)) @ (dltw (dlpt n.+1) @ ap dli (@movedel n.+2 (inl k)) @ dltw (dlpt n.+1)) = idpath).
             exact (whiskerL _ (concat_pp_p _ _ _) @ concat_p_pp _ _ _ @ whiskerR (concat_pp_p _ _ _ @ whiskerL _ (dldo _) @ concat_p1 _) _ @ concat_p_pp _ _ _ @ whiskerR (concat_pp_p _ _ _ @ whiskerL _ ((ap_pp dli _ _)^ @ ap (ap dli) (IHn k)) @ concat_p1 _) _ @ dldo _).
          -- simpl. apply dldo.
      * simpl. constructor.
Defined.

Lemma movedel_do' {n : nat} (i : FFin n)
  : (movedel i)^ = movedel i.
Proof.
  refine ((concat_p1 _)^ @ _); apply moveR_Vp; exact (movedel_do _)^.
Defined.

Lemma movedel_br {n} (i : FFin n)
  : dltw (dlpt n) @ ap dli (@movedel n.+1 (inl i)) @ dltw (dlpt n)
    = ap dli (@movedel n.+1 (inl i)) @ dltw (dlpt n) @ ap dli (@movedel n.+1 (inl i)).
Proof.
  induction n.
  + induction i.
  + change (FFin n + Unit)%type in i. induction i as [j|[]].
    - induction n.
      * apply dlbr.
      * clear IHn0.
        change ((dltw (dlpt n.+2) @ ap dli (dltw (dlpt n.+1) @ ap dli (@movedel n.+2 (inl j)) @ dltw (dlpt n.+1))) @ dltw (dlpt n.+2) = (ap dli (dltw (dlpt n.+1) @ ap dli (@movedel n.+2 (inl j)) @ dltw (dlpt n.+1)) @ dltw (dlpt n.+2)) @ ap dli (dltw (dlpt n.+1) @ ap dli (@movedel n.+2 (inl j)) @ dltw (dlpt n.+1))).
        repeat rewrite ap_pp.
        refine (whiskerR (concat_p_pp _ _ _ @ whiskerR (concat_p_pp _ _ _ @ whiskerR ((concat_p1 _)^ @ whiskerL _ (dldo (dlpt n.+2))^ @ concat_p_pp _ _ _) _ @ concat_pp_p _ _ _) _ @ concat_pp_p _ _ _) _ @ _).
        refine (whiskerR (whiskerL _ (whiskerR (dltw_natural (@movedel n.+2 (inl j)))^ _)) _ @ _).
        refine (whiskerR (whiskerR (dlbr (dlpt n.+1)) _ @ concat_p_pp _ _ _) _ @ concat_pp_p _ _ _ @ whiskerR (concat_p_pp _ _ _) _ @ concat_pp_p _ _ _ @ whiskerL _ (concat_p_pp _ _ _ @ dlbr (dlpt n.+1)) @ _).
        refine (whiskerL _ (concat_pp_p _ _ _) @ concat_p_pp _ _ _ @ whiskerR (concat_pp_p _ _ _ @ concat_pp_p _ _ _ @ whiskerL _ (whiskerL _ (ap_pp dli _ _)^ @ (ap_pp dli _ _)^ @ ap (ap dli) (concat_p_pp _ _ _ @ IHn j) @ ap_pp dli _ _ @ whiskerR (ap_pp dli _ _) _)) _ @ _).
        refine (whiskerR (concat_pp_p _ _ _ @ whiskerL _ (whiskerL _ (concat_pp_p _ _ _) @ concat_p_pp _ _ _ @ whiskerR (dltw_natural (@movedel n.+2 (inl j)))^ _ @ concat_p_pp _ _ _) @ concat_p_pp _ _ _) _ @ concat_p_pp _ _ _ @ whiskerR (concat_pp_p _ _ _ @ whiskerL _ (dltw_natural (@movedel n.+2 (inl j)))) _ @ _).
        refine (whiskerR (concat_p_pp _ _ _ @ whiskerR (concat_pp_p _ _ _ @ whiskerL _ (concat_pp_p _ _ _ @ concat_pp_p _ _ _ @ whiskerL _ (concat_p_pp _ _ _ @ dlbr (dlpt n.+1)))) _) _ @ _).
        repeat rewrite concat_pp_p. constructor.
    - induction n; apply dlbr.
Qed.

Definition last_reduce_w {n} (i j : FFin n.+2) (d : i = j -> Empty)
  : FFin n.+1.
Proof.
  induction n.
  + exact (inr tt).
  + change (FFin n + Unit + Unit + Unit)%type in i, j.
    induction i as [[i|[]]|[]].
    - induction j as [[j|[]]|[]].
      * exact (inl (IHn (inl i) (inl j) (fun p => d (ap inl p)))).
      * exact (inr tt).
      * exact (inl i).
    - induction j as [[j|[]]|[]].
      * exact (inl j).
      * induction (d idpath).
      * exact (inr tt).
    - induction j as [j|[]].
      * exact j.
      * induction (d idpath). 
Defined.


Lemma last_reduce_w_inl_i_inr_tt {n} (i : FFin n.+1)
  : last_reduce_w (inl i) (inr tt) (inl_ne_inr i tt) = i.
Proof.
  induction n.
  + induction i as [[]|[]]; constructor.
  + change (FFin n + Unit + Unit)%type in i.
    induction i as [[i|[]]|[]]; constructor.
Defined.

Lemma last_reduce_w_d {n} (i j : FFin n.+2) (d d' : i = j -> Empty)
  : last_reduce_w i j d = last_reduce_w i j d'.
Proof.
  apply ap. apply path_forall. intro z. induction (d z).
Defined.

Lemma last_reduce_w_pq {n} {i i' j j' : FFin n.+2}
  (p : i = i') (q : j = j')
  (d : i = j -> Empty)
  : last_reduce_w i j d = last_reduce_w i' j' (fun z : i' = j' => d (p @ z @ q^)).
Proof.
  induction p, q; simpl.
  apply last_reduce_w_d.
Defined.

Lemma equiv_path_move_i_j {n} (i j : FFin n.+2) (d : i = j -> Empty)
  : equiv_path (@move n.+2 i) j = inl (last_reduce_w i j d).
Proof.
  change (FFin n.+1 + Unit)%type in i, j.
  induction i as [i|[]].
  * induction n.
    ++ simpl. rewrite (transport_idmap_path_universe_uncurried (omega Empty)).
       induction i as [[]|[]]; induction j as [[[]|[]]|[]].
       +++ induction (d idpath).
       +++ constructor.
    ++ change (FFin n.+1 + Unit)%type in i. induction i as [i|[]].
      -- change (equiv_path (gamma (FFin n.+1) @ ap add (@move n.+2 (inl i)) @ gamma (FFin n.+1)) j = inl (@last_reduce_w n.+1 (inl (inl i)) j d)).
         repeat rewrite equiv_path_pp.
         rewrite equiv_path_ap_add.
         change (transport idmap (gamma (FFin n.+1)) (exp (equiv_path (@move n.+2 (inl i))) (transport idmap (gamma (FFin n.+1)) j)) = inl (@last_reduce_w n.+1 (inl (inl i)) j d)).
         repeat rewrite (transport_idmap_path_universe_uncurried (omega (FFin n.+1))).
         change (FFin n.+1 + Unit + Unit)%type in j. induction j as [[j|[]]|[]].
        --- change (omega (FFin n.+1) (inl (equiv_path (@move n.+2 (inl i)) (inl j))) = inl (@last_reduce_w n.+1 (inl (inl i)) (inl (inl j)) d)).
            rewrite (IHn i (inl j) (fun p => d (ap inl p))). constructor.
        --- constructor.
        --- change (omega (FFin n.+1) (inl ((equiv_path (@move n.+2 (inl i))) (inr tt))) = inl (@last_reduce_w n.+1 (inl (inl i)) (inr tt) d)).
            rewrite (IHn i (inr tt) (inl_ne_inr i tt)). simpl.
            apply ap. apply ap.
            apply last_reduce_w_inl_i_inr_tt.
      -- change (transport idmap (gamma (FFin n.+1)) j = inl (@last_reduce_w n.+1 (inl (inr tt)) j d)).
         rewrite (transport_idmap_path_universe_uncurried (omega (FFin n.+1))).
         change (FFin n.+1 + Unit + Unit)%type in j. induction j as [[j|[]]|[]]; simpl.
        --- constructor.
        --- induction (d idpath).
        --- constructor.
  * simpl. induction n.
    ++ induction j as [[[]|[]]|[]]; simpl.
      -- constructor.
      -- induction (d idpath).
    ++ change (FFin n.+1 + Unit + Unit)%type in j. induction j as [[j|[]]|[]]; simpl.
      -- constructor.
      -- constructor.
      -- induction (d idpath).
Qed.

Lemma last_reduce {n} (a : deloop n) (p : deloop_to_BSb n.+2 (dli (dli a)) = FFin n.+2)
  : path_last (reduce p) = last_reduce_w (path_last p) (path_second_last p) (path_last_ne_path_second_last p).
Proof.
  srefine (@coproduct_paths_l _ Unit _ _ _).
  refine (_ @ equiv_path_move_i_j _ _ _).
  unfold path_second_last.
  change (inl (path_last (reduce p)) = (equiv_path (move (path_last p)) oE (equiv_path p)) (inl (inr tt))).
  rewrite <- equiv_path_pp.
  unfold path_last.
  unfold reduce.
  rewrite (eisretr equiv_path).
  refine (inl_un_inl _ _).
Qed.

Lemma Assumption_1 {n} (p : FFin n.+2 = FFin n.+2)
  (h : path_last p = inr tt)
  : reduce p = reduce (gamma (FFin n) @ p).
Proof.
Admitted.

Lemma Assumption_2 {n} (p : FFin n.+2 = FFin n.+2)
  (h : path_last p = inl (inr tt)) (h' : {j : FFin n & path_second_last p = inl (inl j)})
  : reduce (reduce p) = reduce (reduce (gamma (FFin n) @ p)).
Proof.
Admitted.

Lemma Assumption_3 (n : nat)
  (a' : deloop_to_BSb n.+1 (dlpt n.+1) = FFin n.+1 -> dlpt n.+1 = dlpt n.+1)
  (p : FFin n.+3 = FFin n.+3)
  (i : FFin n.+1) (hi : path_last p = inl (inl i))
  (j : FFin n.+1) (hj : path_second_last p = inl (inl j))
  (IHn : forall (a' : FFin n = FFin n -> dlpt n = dlpt n) (p : FFin n.+2 = FFin n.+2)
      (i : FFin n.+2) (hi : path_last p = i)
      (j : FFin n.+2) (hj : path_second_last p = j),
      ap dli (ap dli (a' (reduce (reduce (gamma (FFin n) @ p))))) @ (ap dli (@movedel n.+1 (path_last (reduce (gamma (FFin n) @ p)))) @ @movedel n.+2 j)
      = ap dli (ap dli (a' (reduce (reduce p)))) @ (dltw (dlpt n) @ (ap dli (@movedel n.+1 (path_last (reduce p))) @ @movedel n.+2 i)))
  : ap dli (ap dli (a' (reduce (reduce (gamma (FFin n.+1) @ p))))) @ (ap dli (@movedel n.+2 (path_last (reduce (gamma (FFin n.+1) @ p)))) @ @movedel n.+3 (inl (inl j)))
  = ap dli (ap dli (a' (reduce (reduce p)))) @ (dltw (dlpt n.+1) @ (ap dli (@movedel n.+2 (path_last (reduce p))) @ @movedel n.+3 (inl (inl i)))).
Proof.
Admitted.


(** Proof of lemma relative to dltw **)

  Lemma etwb_2_reduce_reduce (p : FFin 2 = FFin 2)
    : reduce (reduce (gamma Empty @ p)) = reduce (reduce p).
  Proof.
    srapply @path_ishprop.
  Qed.

  Lemma etwb_2_reduce_last (p : FFin 2 = FFin 2)
    : path_last (reduce p) = inr tt.
  Proof.
    exact (last_reduce (dlpt 0) p).
  Qed.

  Lemma etwb_2_reduce_gamma_p_last (p : FFin 2 = FFin 2)
    : path_last (reduce (gamma Empty @ p)) = inr tt.
  Proof.
    exact (last_reduce (dlpt 0) _).
  Qed.

  Lemma etwb_3_inr_tt_inl_inr_tt_reduce_p_last {n} (p : FFin n.+3 = FFin n.+3)
    (hi : path_last p = inr tt) (hj : path_second_last p = inl (inr tt))
    : path_last (reduce p) = inr tt.
  Proof.
    refine (last_reduce (dlpt n.+1) p @ _).
    exact (last_reduce_w_pq hi hj _).
  Qed.

  Lemma etwb_3_inr_tt_inl_inl_j_reduce_p_last {n} (j : FFin n.+1) (p : FFin n.+3 = FFin n.+3)
    (hi : path_last p = inr tt) (hj : path_second_last p = inl (inl j))
    : path_last (reduce p) = inl j.
  Proof.
    refine (last_reduce (dlpt n.+1) p @ _).
    exact (last_reduce_w_pq hi hj _).
  Qed.

  Lemma etwb_3_inl_inr_tt_inl_inl_j_reduce_p_last {n} (j : FFin n.+1) (p : FFin n.+3 = FFin n.+3)
    (hi : path_last p = inl (inr tt)) (hj : path_second_last p = inl (inl j))
    : path_last (reduce p) = inl j.
  Proof.
    refine (last_reduce (dlpt n.+1) p @ _).
    exact (last_reduce_w_pq hi hj _).
  Qed.

  Lemma etwb_3_inl_inr_tt_inl_inl_j_reduce_gamma_p_last {n} (j : FFin n.+1) (p : FFin n.+3 = FFin n.+3)
    (hi : path_last p = inl (inr tt)) (hj : path_second_last p = inl (inl j))
    : path_last (reduce (gamma (FFin n.+1) @ p)) = inr tt.
  Proof.
    refine (last_reduce (dlpt n.+1) (gamma (FFin n.+1) @ p) @ _).
    exact (last_reduce_w_pq (path_last_gamma_p p @ hj) (path_second_last_gamma_p p @ hi) _).
  Qed.

Definition etwb
  : forall (n : nat) (a' : deloop_to_BSb n (dlpt n) = FFin n -> dlpt n = dlpt n)
    (p : FFin n.+2 = FFin n.+2),
    eib n.+1 (dli (dlpt n)) (eib n (dlpt n) a') (gamma (FFin n) @ p)
    = dltw (dlpt n) @ eib n.+1 (dli (dlpt n)) (eib n (dlpt n) a') p.
Proof.
  intros.
  unfold eib. repeat rewrite ap_pp.
  rewrite path_last_gamma_p.
  refine (_ @ whiskerR (whiskerR (dltw_natural (a' (reduce (reduce p)))) _ @ concat_pp_p _ _ _) _ @ concat_pp_p _ _ _).
  repeat rewrite concat_pp_p.
  remember (path_last p) as i eqn:hi.
  remember (path_second_last p) as j eqn:hj.
  rewrite hi, hj.
  change (FFin n + Unit + Unit)%type in i, j.
  induction n.
  + rewrite etwb_2_reduce_reduce, etwb_2_reduce_gamma_p_last, etwb_2_reduce_last.
    apply whiskerL. refine (concat_1p _ @ _ @ whiskerL _ (concat_1p _)^).
    induction i as [[[]|[]]|[]]; induction j as [[[]|[]]|[]]; try induction (path_last_ne_path_second_last p (hi @ hj^)).
    - simpl. exact (dldo dlpt0)^.
    - simpl. exact (concat_p1 _)^.
  + induction i as [[i|[]]|[]]; induction j as [[j|[]]|[]].
    all:try induction (path_last_ne_path_second_last p (hi @ hj^)).
    - (* case (vii), not formalized *)
      exact (Assumption_3 n a' p i hi j hj IHn).
    - (* case (vi), similar to case (iv) *)
      refine (_ @ whiskerR (ap (ap dli) (ap (ap dli) (ap a' (ap reduce (ap reduce (concat_p_pp _ _ _ @ whiskerR (gamma_double (FFin n.+1)) p @ concat_1p p)))))) _).
      refine (_ @ whiskerL _ (whiskerL _ (whiskerR (ap (ap dli) (ap (@movedel n.+2) (ap path_last (ap reduce (concat_p_pp _ _ _ @ whiskerR (gamma_double (FFin n.+1)) p @ concat_1p p))))) _))).
      set (q := gamma (FFin n.+1) @ p).
      set (ki := @path_last_gamma_p (FFin n.+1) n.+1 p @ hj : path_last q = inl (inr tt)).
      set (kj := @path_second_last_gamma_p (FFin n.+1) n.+1 p @ hi : path_second_last q = inl (inl i)).
      rewrite <- (@Assumption_2 n.+1 q ki (i; kj)).
      rewrite (etwb_3_inl_inr_tt_inl_inl_j_reduce_p_last i q ki kj).
      rewrite (etwb_3_inl_inr_tt_inl_inl_j_reduce_gamma_p_last i q ki kj).
      apply whiskerL. change (ap dli (@movedel n.+2 (inl i)) @ dltw (dlpt n.+1) = dltw (dlpt n.+1) @ (idpath @ (dltw (dlpt n.+1) @ ap dli (@movedel n.+2 (inl i)) @ dltw (dlpt n.+1)))).
      refine (_ @ concat_pp_p _ _ _ @ concat_pp_p _ _ _); apply whiskerR.
      refine ((concat_1p _)^ @ whiskerR _ _ @ concat_pp_p _ _ _).
      refine ((dldo (dlpt n.+1))^ @ whiskerR (concat_p1 _)^ _).      
    - (* case (v), similar to case (ii) *)
      refine (_ @ whiskerR (ap (ap dli) (ap (ap dli) (ap a' (ap reduce (ap reduce (concat_p_pp _ _ _ @ whiskerR (gamma_double (FFin n.+1)) p @ concat_1p p)))))) _).
      refine (_ @ whiskerL _ (whiskerL _ (whiskerR (ap (ap dli) (ap (@movedel n.+2) (ap path_last (ap reduce (concat_p_pp _ _ _ @ whiskerR (gamma_double (FFin n.+1)) p @ concat_1p p))))) _))).
      set (q := gamma (FFin n.+1) @ p).
      set (ki := @path_last_gamma_p (FFin n.+1) n.+1 p @ hj : path_last q = inr tt).
      set (kj := @path_second_last_gamma_p (FFin n.+1) n.+1 p @ hi : path_second_last q = inl (inl i)).
      rewrite <- (@Assumption_1 n.+1 q ki).
      repeat rewrite (etwb_3_inr_tt_inl_inl_j_reduce_p_last i q ki kj).
      apply whiskerL.
      refine (concat_p1 _ @ _).
      change (ap dli (@movedel n.+2 (inl i)) = dltw (dlpt n.+1) @ (ap dli (@movedel n.+2 (inl i)) @ (dltw (dlpt n.+1) @ ap dli (@movedel n.+2 (inl i)) @ dltw (dlpt n.+1)))).
      refine (_ @ concat_p_pp _ _ _ @ whiskerR (movedel_br i @ concat_pp_p _ _ _)^ _ @ concat_pp_p _ _ _ @ whiskerL _ (concat_p_pp _ _ _) @ concat_pp_p _ _ _).
      refine ((concat_p1 _)^ @ _); apply whiskerL.
      symmetry.
      refine (concat_p_pp _ _ _ @ whiskerR (concat_pp_p _ _ _ @ whiskerL _ ((ap_pp dli _ _)^ @ ap (ap dli) (@movedel_do n.+2 (inl i))) @ concat_p1 _) _ @ _).
      apply dldo.
    - (* case (iv) *)
      rewrite <- (Assumption_2 p hi (j; hj)).
      rewrite (etwb_3_inl_inr_tt_inl_inl_j_reduce_p_last j p hi hj).
      rewrite (etwb_3_inl_inr_tt_inl_inl_j_reduce_gamma_p_last j p hi hj).
      apply whiskerL. refine (concat_1p _ @ concat_pp_p _ _ _).
    - (* case (iii), similar to case (i) *)
      refine (_ @ whiskerR (ap (ap dli) (ap (ap dli) (ap a' (ap reduce (ap reduce (concat_p_pp _ _ _ @ whiskerR (gamma_double (FFin n.+1)) p @ concat_1p p)))))) _).
      refine (_ @ whiskerL _ (whiskerL _ (whiskerR (ap (ap dli) (ap (@movedel n.+2) (ap path_last (ap reduce (concat_p_pp _ _ _ @ whiskerR (gamma_double (FFin n.+1)) p @ concat_1p p))))) _))).
      set (q := gamma (FFin n.+1) @ p).
      set (ki := @path_last_gamma_p (FFin n.+1) n.+1 p @ hj : path_last q = inr tt).
      set (kj := @path_second_last_gamma_p (FFin n.+1) n.+1 p @ hi : path_second_last q = inl (inr tt)).
      rewrite <- (@Assumption_1 n.+1 q ki).
      repeat rewrite (etwb_3_inr_tt_inl_inr_tt_reduce_p_last q ki kj).
      apply whiskerL. simpl.
      refine ((dldo _)^ @ whiskerL _ (concat_1p _)^).
    - (* case (ii) *)
      rewrite <- (Assumption_1 p hi).
      repeat rewrite (etwb_3_inr_tt_inl_inl_j_reduce_p_last j p hi hj).
      apply whiskerL.
      refine (_ @ whiskerL _ (concat_p1 _)^).
      change (ap dli (@movedel n.+2 (inl j)) @ (dltw (dlpt n.+1) @ ap dli (@movedel n.+2 (inl j)) @ dltw (dlpt n.+1)) =
dltw (dlpt n.+1) @ ap dli (@movedel n.+2 (inl j))).
      refine (whiskerL _ (movedel_br j @ concat_pp_p _ _ _) @ concat_p_pp _ _ _ @ _).
      refine (_ @ concat_1p _); apply whiskerR.
      refine ((ap_pp dli _ _)^ @ _).
      change (ap dli (@movedel n.+2 (inl j) @ @movedel n.+2 (inl j)) = ap dli idpath); apply ap.
      apply movedel_do.
    - (* case (i) *)
      rewrite <- (Assumption_1 p hi).
      repeat rewrite (etwb_3_inr_tt_inl_inr_tt_reduce_p_last p hi hj).
      apply whiskerL. simpl.
      exact (concat_1p _ @ (concat_p1 _)^).
Qed.


(** Equivalence **)

Theorem equiv_deloop_to_BS
  : forall n, IsEquiv (deloop_to_BS n).
Proof.
  exact (conditions_equiv_deloop_to_BS e0b eib etwb e0f eif).
Defined.

End equiv_deloop_to_BS.
