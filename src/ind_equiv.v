(** * Equivalência entre diferentes noções de indução

    Projeto de Lógica Computacional 1 (2026/1) — Tema 5

    Este arquivo formaliza a equivalência entre três princípios sobre os
    números naturais:

    - PIM: Princípio da Indução Matemática;
    - PIF: Princípio da Indução Forte (ou completa);
    - PBO: Princípio da Boa Ordenação.

    A equivalência é estabelecida pelos teoremas [PIM_equiv_PIF],
    [PBO_equiv_PIM] e [PBO_equiv_PIF].

    Estrutura: cada parte possui um "lema-núcleo" que concentra o
    argumento matemático central, e lemas de implicação finos que apenas
    o instanciam. Os teoremas finais são composições dessas implicações.

    Ferramenta: Rocq (versão 9 ou superior). Caso seja utilizada uma
    versão anterior (Coq 8.x), basta substituir as duas linhas de
    importação abaixo por: [Require Import Arith Classical.] *)

(* begin hide *)
From Stdlib Require Import Arith.

(* ADAPTAÇÃO DE CÓDIGO NECESSÁRIA PARA O PROJETO:
   Importamos a biblioteca de Lógica Clássica, pois as demonstrações que
   envolvem o Princípio da Boa Ordenação (PBO) requerem o Princípio do
   Terceiro Excluído ([classic : forall P, P \/ ~P]) e a eliminação da
   dupla negação ([NNPP : forall P, ~~P -> P]). Como o predicado
   [P : nat -> Prop] é arbitrário (possivelmente indecidível), não é
   possível, de forma puramente construtiva, decidir se [P] vale ou não
   em um dado ponto, o que bloqueia a busca pelo elemento mínimo.

   A importação usa o prefixo [Stdlib] (padrão do Rocq 9) para manter a
   consistência com a importação de [Arith] acima. *)
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

(** ** Parte 2: implicações envolvendo o PBO *)

(** Lema-núcleo da direção PIF -> PBO: por indução forte em [a],
    provamos que qualquer testemunha [P a] garante a existência de um
    menor natural satisfazendo [P]. No passo forte para [k], o Terceiro
    Excluído ([classic]) decide se já existe alguma testemunha [j < k]:
    - se existe, a hipótese de indução forte aplicada a [j] conclui;
    - se não existe, o próprio [k] é o mínimo procurado, pois qualquer
      [x < k] com [P x] contradiria a inexistência. *)
Lemma PIF_encontra_minimo:
  PIF ->
  forall P : nat -> Prop,
  forall a, P a ->
    exists m, P m /\ forall x, x < m -> ~ P x.
Proof.
  intros HPIF P.
  apply (HPIF (fun a => P a ->
               exists m, P m /\ forall x, x < m -> ~ P x)).
  intros k IH HPk.
  destruct (classic (exists j, j < k /\ P j)) as [Hj | Hnj].
  - (* Existe testemunha abaixo de k: a HI forte resolve. *)
    destruct Hj as [j [Hjk HPj]].
    exact (IH j Hjk HPj).
  - (* Não existe testemunha abaixo de k: k é o mínimo. *)
    exists k. split.
    + exact HPk.
    + intros x Hxk HPx.
      apply Hnj.
      exists x. split.
      * exact Hxk.
      * exact HPx.
Qed.

Lemma PIF_implies_PBO: PIF -> PBO.
Proof.
  unfold PBO.
  intros HPIF P Hex.
  destruct Hex as [n HPn].
  exact (PIF_encontra_minimo HPIF P n HPn).
Qed.

(** Lema-núcleo das direções PBO -> PIM e PBO -> PIF: dado um
    contraexemplo de [Q], o PBO aplicado ao predicado complementar
    [fun m => ~ Q m] fornece o MENOR contraexemplo [m]. A minimalidade
    vem do PBO na forma negativa [forall x, x < m -> ~ ~ Q x]; a
    eliminação da dupla negação ([NNPP]) — usada somente aqui — a
    converte para a forma positiva [forall x, x < m -> Q x], muito mais
    conveniente nos pontos de uso. *)
Lemma PBO_menor_contraexemplo:
  PBO ->
  forall (Q : nat -> Prop) (n : nat),
    ~ Q n ->
    exists m, ~ Q m /\ forall x, x < m -> Q x.
Proof.
  intros HPBO Q n HnQn.
  assert (Hex: exists m, ~ Q m) by (exists n; exact HnQn).
  destruct (HPBO (fun m => ~ Q m) Hex) as [m [HnQm Hmin]].
  exists m. split.
  - exact HnQm.
  - intros x Hx.
    apply NNPP.
    apply Hmin.
    exact Hx.