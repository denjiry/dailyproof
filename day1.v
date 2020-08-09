(* 元の文 *)
(* ドラえもんはネズミが嫌い。 *)
(* すべての嫌いなものは好きものである。 *)
(* ドラえもんはネズミが好き。 *)
(* 論理式 *)
Require Export lib.
Parameter _ネズミ : Entity -> Prop.
Parameter _ドラえもん : Entity -> Prop.
Parameter _嫌い : Event -> Prop.
Parameter _好き : Event -> Prop.

Theorem t1:
  (exists x,(_ネズミ(x) /\ exists z4,(_ドラえもん(z4) /\ exists e,(_嫌い(e) /\ (Acc(e) = x) /\ (Nom(e) = z4)))))
  ->
  (forall x z, exists e,(_嫌い(e) /\ (Acc(e) = z) /\ (Nom(e) = x)) -> exists e,(_好き(e) /\ (Acc(e) = z) /\ (Nom(e) = x)))
  ->
  (exists x,(_ドラえもん(x) /\ exists z22,(_ネズミ(z22) /\ exists e,(_好き(e)  /\ (Acc(e) = z22) /\ (Nom(e) = x))))).
Proof.
  intros H1 H2.
  destruct H1.
  destruct H.
  destruct H0 as [z4 [d eq]].
  exists z4.  split. assumption. 
  exists x. split. assumption.
  
