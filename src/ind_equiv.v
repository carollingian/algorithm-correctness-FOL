(** * Introdução *)

(** * Equivalência entre diferentes noções de indução

    Este arquivo formaliza a equivalência entre três princípios sobre os
    números naturais:

    - PIM: Princípio da Indução Matemática;
    - PIF: Princípio da Indução Forte (ou completa);
    - PBO: Princípio da Boa Ordenação.

    A equivalência é estabelecida pelos teoremas [PIM_equiv_PIF],
    [PBO_equiv_PIM] e [PBO_equiv_PIF].

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
    satisfaz a propriedade [P], then existe um [m] que é o menor
    natural que satisfaz a propriedade [P]. Esta propriedade é conhecida
    como o Princípio da Boa Ordenação (PBO): *)

Definition PBO := forall P : nat -> Prop,
  (exists n : nat, P n) ->
  exists m : nat, P m /\ forall x : nat, x < m -> ~ P x.

(** ** Equivalência entre o Princípio da Indução Matemática (PIM) e o Princípio da Indução Forte (PIF) *)

(** O coração da direção PIM -> PIF é o truque de "fortalecer" o
    predicado: a indução simples não consegue provar [Q n] diretamente a
    partir da hipótese de indução forte [Hpasso], pois o passo indutivo
    de [Q k] para [Q (S k)] descartaria o histórico. A solução foi aplicar
    o PIM ao predicado acumulado

        [fun n => forall m, m < n -> Q m]

    ("[Q] vale em todo o segmento inicial [[0, n]]"), que carrega o
    histórico completo de uma iteração para a seguinte. *)
Lemma PIM_acumula_historico:
  PIM ->
  forall Q : nat -> Prop,
    (forall k, (forall m, m < k -> Q m) -> Q k) ->
    forall n m, m < n -> Q m.
Proof.
  intros HPIM Q Hpasso.
  apply (HPIM (fun n => forall m, m < n -> Q m)).
  - (* Caso base: o segmento inicial [0, 0] é vazio, pois nenhum
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
    basta observar que [n] pertence ao segmento inicial [[0, S n]]. *)
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

(** ** Equivalência entre o Princípio da Boa Ordenação (PBO) e o Princípio da Indução Matemática (PIM)

    Esta seção apresenta a demonstração formal da equivalência lógica entre o Princípio da Boa Ordenação (PBO) e o Princípio da Indução Matemática (PIM). A prova da equivalência ([PBO <-> PIM]) é dividida em duas direções: a ida ([PBO -> PIM]) e a volta ([PIM -> PBO]).

    ** Justificativa Técnica: A Necessidade da Lógica Clássica

    Antes de detalhar as demonstrações, é fundamental apresentar uma adaptação realizada no código-base do projeto. O Princípio da Boa Ordenação estabelece que qualquer propriedade sobre os números naturais que possua pelo menos um elemento satisfatório, que então forme um subconjunto não vazio de %$\mathbb{N}$%, possui um elemento mínimo.

    Como o predicado matemático avaliado é genérico, ele pode ser computacionalmente indecidível. Em uma abordagem de lógica puramente intuicionista, o assistente de provas não seria capaz de decidir se a propriedade vale ou não para um determinado ponto sem um algoritmo explícito de busca. Para contornar esse problema e viabilizar a localização abstrata do elemento mínimo, fez-se necessária a importação e o uso da Lógica Clássica.

    Utilizou-se o Princípio do Terceiro Excluído, para analisar as alternativas de existência ou inexistência de elementos abaixo de um limite, e a Eliminação da Dupla Negação (%$\neg\neg A \rightarrow A$%). Sem essa lógica clássica, a prova de minimalidade do PBO se tornaria irresolvível no Rocq.

    ** Demonstração da Ida: PBO implica PIM ([PBO -> PIM])

    A estratégia adotada para demonstrar que o Princípio da Boa Ordenação implica a validade da Indução Matemática clássica fundamenta-se no método de prova por contradição.

    *** O Lema do Menor Contraexemplo

    Para estruturar o argumento, foi construído inicialmente um lema auxiliar para estabelecer que, dado um predicado qualquer que falhe para um número natural [n], o Princípio da Boa Ordenação garante a existência de um menor contraexemplo [m].

    A minimalidade desse elemento [m] é obtida sob a forma clássica de negação: nenhum número menor que [m] pode falhar no predicado. Utilizando a eliminação da dupla negação, o lema converte essa propriedade de maneira conveniente, garantindo formalmente que a propriedade em questão é verdadeira para absolutamente todos os números naturais contidos no segmento anterior a [m]. *)

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
Qed.

(** **** Análise de Casos do Elemento Mínimo

    Com o lema estabelecido, vai se assumir como hipóteses as premissas da Indução Matemática: a base da indução e o passo indutivo. O objetivo é demonstrar que a propriedade vale para um natural arbitrário [n].

    Aplica-se a redução ao absurdo: supõe-se, por hipótese de contradição, que a propriedade falha para [n]. Pelo lema do menor contraexemplo, nós temos a existência de um número natural [m] que representa o menor elemento a falhar na propriedade. A partir daí, tem uma análise do número [m] por meio de uma divisão de casos:

    - %\textbf{Caso $m = 0$:}% Se o menor contraexemplo fosse zero, teríamos que a propriedade falha em zero. No entanto, isso entra em contradição com a primeira premissa assumida, que é a base da indução, garantindo a validade da propriedade para o número zero.
    - %\textbf{Caso $m = S(m')$ (Sucessor):}% Se o menor contraexemplo é o sucessor de algum número [m'], avalia-se a minimalidade de [m]. Como [m'] é menor que seu sucessor [S m'], e [m] é o menor contraexemplo possível, conclui-se que a propriedade é obrigatoriamente verdadeira para [m']. Ao aplicar o passo indutivo sobre essa afirmação, pode se deduzir que a propriedade também deve ser verdadeira para o sucessor de [m'], que é o próprio [m]. Isso gera uma contradição com a definição de [m], que havia sido estabelecido justamente como um contraexemplo, que era onde a propriedade deveria falhar.

    Esgotados os casos dos números naturais e como temos o absurdo em ambos, a suposição de que a propriedade falhava para [n] é rejeitada. Portanto, por eliminação da dupla negação, podemos concluir a prova do teorema de indução. *)

Lemma PBO_implies_PIM: PBO -> PIM.
Proof.
  unfold PIM.
  intros HPBO P HP0 HPS n.
  apply NNPP. intro HnPn.
  destruct (PBO_menor_contraexemplo HPBO P n HnPn)
    as [m [HnPm Hmenores]].
  destruct m as [| m'].
  - (* m = 0: contradiz a base do PIM. *)
    apply HnPm. exact HP0.
  - (* m = S m': contradiz o passo indutivo do PIM. *)
    apply HnPm.
    apply HPS.
    apply Hmenores.
    apply Nat.lt_succ_diag_r.
Qed.

(** *** Demonstração da Volta: PIM implica PBO ([PIM -> PBO])

    Aextensãoda volta, que é para provar que o Princípio da Indução Matemática é suficiente para garantir o Princípio da Boa Ordenação, foi realizada de forma modular por meio da transitividade.

    Em vez de construir uma indução simples diretamente sobre o enunciado do PBO, o que traria dificuldades técnicas para carregar o histórico de minimalidade entre as iterações, a demonstração apoia-se nos resultados intermediários obtidos no projeto:

    - Primeiramente, utiliza-se o fato de que o PIM implica o Princípio da Indução Forte (PIF). Essa passagem baseia-se na técnica de fortalecimento do predicado, acumulando o histórico de validade em segmentos iniciais.
    - Em seguida, voltamos a utilizar o lema que demonstra que o Princípio da Indução Forte implica o Princípio da Boa Ordenação ([PIF -> PBO]), onde a indução completa é utilizada para varrer os elementos inferiores e testar a existência de um elemento mínimo com o auxílio do terceiro excluído.

    Pela aplicação sucessiva dessas implicações, a hipótese de que o PIM é verdadeiro é colocada na cadeia de teoremas. O PIM instancia a validade do PIF que, por sua vez, instancia e conclui a validade do PBO. Essa composição fecha a equivalência bidirecional formalmente. *)

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

Lemma PIM_implies_PBO: PIM -> PBO.
Proof.
  intro HPIM.
  apply PIF_implies_PBO.
  apply PIM_implies_PIF.
  exact HPIM.
Qed.

(** *** Teorema Principal: Equivalência entre PBO e PIM *)

Theorem PBO_equiv_PIM: PBO <-> PIM.
Proof.
  split.
  - apply PBO_implies_PIM.
  - apply PIM_implies_PBO.
Qed.

(** ** Equivalência entre o Princípio da Boa Ordenação e a Indução Forte *)

(** Finalmente, esta é a equivalência necessária para fechar o ciclo. A partir de agora, 
a transitividade é a base da demonstração. Ao estabelecer que PBO <-> PIF, a lógica clássica 
garante automaticamente que as três noções são equivalentes (PIM <-> PIF <-> PBO). 
Não é necessário provar diretamente que PBO implica PIM, pois a transitividade já corrobora essa prova. *)

(** *** Lema [PBO_implies_PIF] *)

(** O objetivo deste lema é mostrar que, se todo subconjunto não-vazio de números naturais tem um menor 
elemento (PBO), então o Princípio da Indução Forte (PIF) é válido. A estratégia utilizada aqui é 
baseada em prova por contradição, utilizando a lógica clássica.

Para provar o PIF, é necessário garantir que a propriedade [Q] é válida para todos os naturais, 
assumindo apenas que o passo da indução é verdadeiro, ou seja, se [Q] é válido para 
todos os naturais menores que [n], então [Q] é obrigatoriamente válida para [n].

PBO prova disso a partir de:

1. Assumir, por absurdo, que a propriedade [Q] não vale para todos os naturais. 
   Então, o conjunto de contraexemplos (onde Q falha) não é vazio.

2. Como esse conjunto de contraexemplos não é vazio, a premissa do PBO garante que ele 
   deve possuir um menor elemento [m].

3. Por [m] ser o menor elemento para o qual [Q] falha, é verdade absoluta 
   que [Q] é verdadeira para todos os números menores que [m]. 

4. A hipótese de indução forte afirma que, se a propriedade é válida para todos os antecessores
   de [m], então ela tem que ser válida para [m].

5. Daí, [Q(m)] tem que ser falsa, pois [m] foi definido como um contraexemplo e, 
   ao mesmo tempo, [Q(m)] tem que ser verdadeira pela hipótese de indução.

Essa contradição final compromete a suposição inicial de que existia um contraexemplo. Logo, o 
conjunto contraexemplo é necessariamente vazio, provando que [Q] é 
verdadeiro para todo e qualquer natural. *)

Lemma PBO_implies_PIF: PBO -> PIF.
Proof.
  unfold PIF.
  intros HPBO Q Hpasso n.
  apply NNPP. intro HnQn.
  destruct (PBO_menor_contraexemplo HPBO Q n HnQn)
    as [m [HnQm Hmenores]].
  apply HnQm.
  apply Hpasso.
  exact Hmenores.
Qed.

(** *** Teorema [PBO_equiv_PIF] *)

(** Por fim, o teorema [PBO_equiv_PIF] estabelece a equivalência bidirecional formal por meio de:
  - [split.]: divide a equivalênciaem suas duas direções: PBO -> PIF e PIF -> PBO.
  - [apply PBO_implies_PIF.]: Resolve a ida utilizando o lema provado anteriormente.
  - [apply PIF_implies_PBO.]: Resolve a volta utilizando o lema de que a Indução Forte implica 
    na Boa Ordenação. *)

Theorem PBO_equiv_PIF: PBO <-> PIF.
Proof.
  split.
  - apply PBO_implies_PIF.
  - apply PIF_implies_PBO.
Qed.

(** * Conclusão *)