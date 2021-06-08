Require Export UnivalenceImpliesFunext.
Require Export hott_lemmas.
Open Scope type.

Section add_exp.
Context `{Univalence}.

Definition add
  : Type -> Type
  := fun X => X + Unit.

Definition exp {A B} (e : A <~> B)
  : A + Unit <~> B + Unit
  := e +E 1.

Definition ap_add_ua {A B} (e : A <~> B)
  : ap add (path_universe_uncurried e) = path_universe_uncurried (exp e).
Proof.
  refine (_ @ ap path_universe_uncurried (ap exp (eisretr (equiv_path _ _) e))).
  change (ap add (path_universe_uncurried e) = path_universe_uncurried (exp (equiv_path A B (path_universe_uncurried e)))).
  induction (path_universe_uncurried e); simpl.
  refine (path_universe_1^ @ ap path_universe_uncurried _).
  apply path_equiv; apply path_forall; intros [a|[]]; constructor.
Defined.

Definition equiv_path_ap_add {A B} (p : A = B)
  : equiv_path _ _ (ap add p) = exp (equiv_path _ _ p).
Proof.
  induction p; simpl.
  apply path_equiv; apply path_forall; intros [a|x]; constructor.
Defined.

End add_exp.


Section restriction.

Section coproduct_paths.
Context {A B : Type}.

Definition code_coproduct
  : A + B -> A + B -> Type.
Proof.
  intros [a1|b1]; intros [a2|b2].
  + exact (a1 = a2).
  + exact Empty.
  + exact Empty.
  + exact (b1 = b2).
Defined.

Definition encode_coproduct {x1 x2 : A + B}
  : x1 = x2 -> code_coproduct x1 x2.
Proof.
  path_induction. induction x1; constructor.
Defined.

Definition coproduct_paths_l {a1 a2 : A}
  : @inl A B a1 = inl a2 -> a1 = a2
  := encode_coproduct.

Definition coproduct_paths_r {b1 b2 : B}
  : @inr A B b1 = inr b2 -> b1 = b2
  := encode_coproduct.

End coproduct_paths.

Context `{Funext}.

Lemma coproduct_equiv_unfunctor_sum {A A' B B'} (e : A + B <~> A' + B')
  (hA : forall a, is_inl (e (inl a)))
  (hB : forall b, is_inr (e (inr b)))
  : equiv_unfunctor_sum_l e hA hB +E equiv_unfunctor_sum_r e hA hB = e.
Proof.
  apply path_equiv. apply path_forall. intros [a|b]; simpl.
  + apply inl_un_inl.
  + apply inr_un_inr.
Defined.

  Definition restriction_h_l {A B} (e : A + Unit <~> B + Unit)
    (p : e (inr tt) = inr tt)
    : forall a : A, is_inl (e (inl a)).
  Proof.
    enough (h' : forall (a : A) (x : B + Unit), e (inl a) = x -> is_inl x).
    { intro a. exact (h' a (e (inl a)) idpath). }
    intros a [b|[]].
    - intro; exact tt.
    - intro q; apply Empty_rec.
      apply (inl_ne_inr a tt).
      refine ((eissect e _)^ @ ap e^-1 (q @ p^) @ eissect e _).
  Defined.

  Definition restriction_h_r {A B} (e : A + Unit <~> B + Unit)
    (p : e (inr tt) = inr tt)
    : forall b : Unit, is_inr (e (inr b)).
  Proof.
    intros []. exact (transport is_inr p^ tt).
  Defined.

Definition restriction {A B} (e : A + Unit <~> B + Unit)
  (p : e (inr tt) = inr tt)
  : A <~> B
  := equiv_unfunctor_sum_l e (restriction_h_l e p) (restriction_h_r e p).

Lemma restriction_invariant_p {A B} (e : A + Unit <~> B + Unit)
  (p p' : e (inr tt) = inr tt) 
  : restriction e p = restriction e p'.
Proof.
  apply path_equiv; apply path_forall.
  intro a. simpl. unfold unfunctor_sum_l.
  apply ap. srapply @path_ishprop.
Defined.

Lemma restriction_invariant {A B} (e e' : A + Unit <~> B + Unit)
  (p : e (inr tt) = inr tt) (h : e = e')
  : restriction e p = restriction e' (ap10_equiv h^ (inr tt) @ p).
Proof.
  induction h; apply restriction_invariant_p.
Defined.

Lemma exp_restriction {A B} (e : A + Unit <~> B + Unit)
  (p : e (inr tt) = inr tt)
  : exp (restriction e p) = e.
Proof.
  refine (_ @ coproduct_equiv_unfunctor_sum e (restriction_h_l e p) (restriction_h_r e p)).
  change (restriction e p +E 1 = restriction e p +E equiv_unfunctor_sum_r e (restriction_h_l e p) (restriction_h_r e p)).
  refine (ap (fun z => restriction e p +E z) _).
  apply path_equiv. apply path_forall. intro. srapply @path_ishprop.
Defined.

Lemma restriction_exp {A B} (e : A <~> B)
  : restriction (exp e) idpath = e.
Proof.
  apply path_equiv. apply path_forall. constructor.
Defined.

Lemma equiv_diff {A B} (e : A <~> B) {a a'}
  : (a = a' -> Empty) <~> (e a = e a' -> Empty).
Proof.
  srapply @equiv_adjointify.
  + intros f p; apply f. exact ((eissect e _)^ @ ap e^-1 p @ eissect e _).
  + intros f p; apply f. exact (ap e p).
  + unfold Sect; intro f; by_extensionality p.
    apply ap. refine (ap_pp e _ _ @ whiskerR (ap_pp e _ _ @ whiskerR (ap_V e _) _) _ @ concat_pp_p _ _ _ @ _); apply moveR_Vp.
    refine (whiskerR (ap_compose e^-1 e p)^ _ @ _ @ whiskerL _ (ap_idmap p)).
    refine (whiskerL _ (eisadj e a')^ @ _ @ whiskerR (eisadj e a) _).
    exact (homotopy_square (eisretr e) p)^.
  + unfold Sect; intro f. by_extensionality p; induction p; simpl.
    apply ap. refine (concat_pp_p _ _ _ @ _); apply moveR_Vp.
    exact (concat_1p _ @ (concat_p1 _)^).
Defined.

End restriction.


Section omega.
Context `{Univalence}.

  Definition omega_fun (A : Type)
    : A + Unit + Unit -> A + Unit + Unit.
  Proof.
    intros [[a|x]|y].
    + exact (inl (inl a)).
    + exact (inr x).
    + exact (inl (inr y)).
  Defined.

  Definition omega_fun_involution_pt {A}
    : Sect (omega_fun A) (omega_fun A).
  Proof.
    intros [[a|x]|y]; constructor.
  Defined.

  Definition isequiv_omega {A}
    : IsEquiv (omega_fun A)
    := isequiv_adjointify (omega_fun A) (omega_fun A) omega_fun_involution_pt omega_fun_involution_pt.

Definition omega (A : Type)
  : A + Unit + Unit <~> A + Unit + Unit
  := Build_Equiv _ _ (omega_fun A) isequiv_omega.

Definition omega_double (A : Type)
  : omega A oE omega A = 1%equiv.
Proof.
  apply path_equiv; apply path_forall.
  exact omega_fun_involution_pt.
Defined.

Definition omega_triple (A : Type)
  : omega (add A) oE (exp (omega A) oE omega (add A)) = exp (omega A) oE (omega (add A) oE exp (omega A)).
Proof.
  apply path_equiv; apply path_forall.
  intros [[[a|x]|y]|z]; constructor.
Defined.

Definition gamma (A : Type)
  : A + Unit + Unit = A + Unit + Unit
  := path_universe_uncurried (omega A).

Definition gamma_double (A : Type)
  : gamma A @ gamma A = idpath.
Proof.
  refine ((path_universe_compose (omega A) (omega A))^ @ ap path_universe_uncurried _ @ path_universe_1).
  apply omega_double.
Defined.

  Definition gamma_double' (A : Type)
    : (gamma A)^ = gamma A.
  Proof.
    refine ((concat_1p _)^ @ _); apply moveR_pV; exact (gamma_double _)^.
  Defined.

Definition gamma_triple (A : Type)
  : (gamma (add A) @ ap add (gamma A)) @ gamma (add A) = (ap add (gamma A) @ gamma (add A)) @ ap add (gamma A).
Proof.
  refine (whiskerR (whiskerL _ (ap_add_ua (omega A))) _ @ _ @ whiskerR (whiskerR (ap_add_ua (omega A))^ _) _ @ whiskerL _ (ap_add_ua (omega A))^).
  change ((path_universe (omega (add A)) @ path_universe (exp (omega A))) @ path_universe (omega (add A)) = (path_universe (exp (omega A)) @ path_universe (omega (add A))) @ path_universe (exp (omega A))).
  refine (whiskerR (path_universe_compose (omega (add A)) (exp (omega A)))^ _ @ (path_universe_compose (exp (omega A) oE omega (add A)) (omega (add A)))^ @ _ @ path_universe_compose (omega (add A) oE exp (omega A)) (exp (omega A)) @ whiskerR (path_universe_compose (exp (omega A)) (omega (add A))) _).
  refine (ap path_universe_uncurried _).
  apply omega_triple.
Defined.


Lemma not_omega_id {A}
  : omega A = 1%equiv -> Empty.
Proof.
  intro p.
  apply (@inl_ne_inr (A + Unit) Unit (inr tt) tt).
  exact (apD10 (ap equiv_fun p) (inr tt)).
Defined.

End omega.