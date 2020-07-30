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
  (forall x, exists e,(_嫌い(e) /\ (Acc(e) = x)) -> exists e,(_好き(e) /\ (Acc(e) = x)))
  ->
  (exists x,(_ドラえもん(x) /\ exists z22,(_ネズミ(z22) /\ exists e,(_好き(e) /\ (Nom(e) = x) /\ (Acc(e) = z22))))).
Proof.
  intros H1 H2.
  eexists ?[x].
  split.
  
