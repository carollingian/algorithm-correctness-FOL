(* begin hide *)
From Stdlib Require Import Arith.
From Stdlib Require Import Classical.
(* end hide *)

(** Seja [P] uma propriedade sobre os números naturais. O Princípio da
    Indução Matemática (PIM) pode ser enunciado da seguinte forma: *)
Definition PIM :=
  forall P: nat -> Prop,
    (P 0) ->
    (forall k, P k -> P (S k)) ->
    forall n, P n.

(** Seja [Q] uma propriedade sobre os números naturais. O Princípio da
    Indução Forte (PIF) pode ser enunciado da seguinte forma: *)
Definition PIF :=
  forall Q: nat -> Prop,
    (forall k, (forall m, m < k -> Q m) -> Q k) ->
    forall n, Q n.

(** Dado um predicado [P] sobre naturais, se existe um natural [n] que
    satisfaz a propriedade [P], então existe um [m] que é o menor
    natural que satisfaz a propriedade [P]. Esta propriedade é conhecida
    como o Princípio da Boa Ordenação (PBO): *)
Definition PBO := forall P : nat -> Prop,
  (exists n : nat, P n) ->
  exists m : nat, P m /\ forall x : nat, x < m -> ~ P x.

(** ** Parte 1: PIM <-> PIF *)

(** O coração da direção PIM -> PIF é o truque de "fortalecer" o
    predicado: a indução simples não consegue provar [Q n] diretamente a
    partir da hipótese de indução forte [Hpasso], pois o passo indutivo
    de [Q k] para [Q (S k)] descartaria o histórico. A solução foi aplicar
    o PIM ao predicado acumulado

        [fun n => forall m, m < n -> Q m]

    ("[Q] vale em todo o segmento inicial [[0, n)]"), que carrega o
    histórico completo de uma iteração para a seguinte. *)
Lemma PIM_acumula_historico:
  PIM ->
  forall Q : nat -> Prop,
    (forall k, (forall m, m < k -> Q m) -> Q k) ->
    forall n m, m < n -> Q m.
Proof.
  intros HPIM Q Hpasso.
  apply (HPIM (fun n => forall m, m < n -> Q m)).
  - (* Caso base: o segmento inicial [0, 0) é vazio, pois nenhum
       natural é menor do que 0. *)
    intros m Hm.
    exfalso.
    apply (Nat.nlt_0_r m).
    exact Hm.
  - (* Passo indutivo: de "Q vale abaixo de k" (IH) para "Q vale
       abaixo de S k". Dado m < S k, ou m < k (e a IH conclui), ou
       m = k (e a hipótese de indução forte, alimentada com a IH,
       conclui). *)
    intros k IH m Hm.
    apply -> Nat.lt_succ_r in Hm.        (* Força a direção de ida: m < S k -> m <= k *)
    apply -> Nat.lt_eq_cases in Hm.      (* Força a direção de ida: m <= k -> m < k \/ m = k *)
    destruct Hm as [Hlt | Heq].
    + apply IH. exact Hlt.
    + subst m. apply Hpasso. exact IH.
Qed.

(** Com o histórico acumulado salvo ao alcance, [Q n] continuamos:
    basta observar que [n] pertence ao segmento inicial [[0, S n)]. *)
Lemma PIM_implies_PIF: PIM -> PIF.
Proof.
  unfold PIF.
  intros HPIM Q Hpasso n.
  apply (PIM_acumula_historico HPIM Q Hpasso (S n)).
  apply Nat.lt_succ_diag_r.
Qed.

(** A recíproca é direta: a indução simples é um caso particular da
    indução forte. No passo forte para [k], analisamos [k]:
    - [k = 0]: é exatamente a base do PIM;
    - [k = S k']: como [k' < S k'], a hipótese de indução forte fornece
      [P k'], e o passo indutivo do PIM conclui [P (S k')]. *)
Lemma PIF_implies_PIM: PIF -> PIM.
Proof.
  unfold PIF, PIM.
  intros HPIF P HP0 HPS n.
  apply HPIF.
  intros k IH.
  destruct k as [| k'].
  - (* Caso k = 0 *)
    exact HP0.
  - (* Caso k = S k' *)
    apply HPS.
    apply IH.
    apply Nat.lt_succ_diag_r.
Qed.

Theorem PIM_equiv_PIF: PIM <-> PIF.
Proof.
  split.
  - apply PIM_implies_PIF.
  - apply PIF_implies_PIM.
Qed.


Theorem PBO_equiv_PIM: PBO <-> PIM.
Proof. Admitted.

Theorem PBO_equiv_PIF: PBO <-> PIF.
Proof. Admitted.

(** Repositório: %\url{https://github.com/flaviodemoura/ind_equiv}% *)
