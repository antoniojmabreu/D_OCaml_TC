open List
open Scanf
open Array

type regexp =
 | V
 | E
 | C of char
 | U of regexp * regexp
 | P of regexp * regexp
 | S of regexp


(*converte regexp para string*)
let rec string_of_regexp s =
  match s with
  | V       -> "0"
  | E       -> "1"
  | C  c    -> String.make 1 c
  | U (f,g) -> "("^(string_of_regexp f)^" + "^(string_of_regexp g)^")"
  | P (f,g) -> "("^(string_of_regexp f)^" . "^(string_of_regexp g)^")"
  | S s     -> (string_of_regexp s)^"*"
(* **************************************************************************************************************** *)
(* ********************************************   ComeÃ§ar aqui **************************************************** *)

type trans = (*cada transição tem 2 estados e um simbolo; & -> epsilon*)
  {
    fromState:int;
    symbol:char;
    toState:int
  }

let createTrans state1 c state2 = (*cria uma transição (state symbol state)*)
  {
    fromState = state1;
    symbol = c;
    toState = state2
  }

let finals card_f k = (*converte a string que recebe os estados finais, num array de inteiros de dimensão card_f onde cada posição contem um estado final*)
  let index = ref 0 in
  let t = Array.make card_f 1 in (*inicializa o array do conjunto dos estados finais*)
  for a=0 to card_f - 1 do
    t.(a)<-int_of_char k.[!index] - 48; (*lê a string de 2 em 2 posições por causa dos espaços e coloca o respetivo inteiro no array*)
    index:=!index+2; (*incrementa o índice da string de 2 em 2*)
  done;
  t

let trans card_m = (*lê as card_m linhas seguintes e constroi o autómato*)
  let t = Array.make card_m (createTrans 1 'a' 1) in (*inicializa o array que guarda as transições do autómato*)
  for a=0 to card_m - 1 do
    let m = read_line() in (*lê card_m linhas*)
    t.(a)<-(createTrans (int_of_char m.[0] - 48) m.[2] (int_of_char m.[4] - 48)) (*cria uma transição to tipo (state symbol state)*)
  done;
  t (*devolve o array que representa o autómato*)

(* verifica se s está contido em r *)
let rec contains r s =
  if r = s then true else
    match r with
    | V  | E | C _ -> r = s
    | P (a,b) | U (a,b) -> contains a s || contains b s
    | S a -> contains a s

(*função de simplificação da expressão resultante é aplicada ao output antes da sua impressão de forma a simplificar o resultado*)
let rec simplify (a:regexp) =
 match a with
 | U (r,s) -> (*união*)
   let sr = simplify r in
   let ss = simplify s in
   if sr = V then ss
   else if ss = V then sr
   else if ss = sr then sr
   else U (sr,ss)
 | P (r,s) -> (*concatenação*)
   let sr = simplify r in
   let ss = simplify s in
   if sr = V then V
   else if ss = V then V
   else if sr = E then ss
     else if ss = E then sr
   else P (sr,ss)
 | S r -> let sr = simplify r in (*Kleene star*)
   if sr = V || sr = E
   then E else (
     match sr with
       U (E,rr) | U (rr,E) -> S rr
       | _ -> S sr
     )
 |  _ -> a


(*
A função yamada é baseada em programação dinâmica
Usa uma matriz tridimensional (n * n * n+1)  onde n é o conjunto S e n+1 representa K
A matriz é preenchida de cima para baixo, da esquerda para a direita
A posição (1).(1).(1) do array, representa R(1,1,1) do algoritmo dado nas aulas, ou seja, o array segue a notação R(i,j,k), tal como nas aulas
O array é assim preenchido de (1).(1).(1) para (n).(n).(1), ou seja, de R(1,1,1) até R(i,j,k)
Para efeitos de simplificação, a explicação linha a linha da função seguinte, segue a notação i j k
*)
let yamada n m card_m =
  let yam = Array.init (n+1) (fun _ -> Array.init (n+1) (fun _ -> (Array.init (n+2) (fun _ -> V)))) in (*inicializa o array 3d que guarda os resultados*)
  let flag = ref 0 in (*flag que vai ser usada em casos i=j para adicionar 1 + ...*)
  (*k = 1*)
  for i=1 to n do (*itera sobre i*)
    for j=1 to n do (*itera sobre j*)
      flag:=0;
      for d=0 to card_m - 1 do (*precorre o autómato*)
        let s = m.((card_m-1)-d) in (*o autómato é precorrido ao contrário para garantir associatividade á direita*)
        if i = j then flag := 1; (*se i=j levanta a flag para adicionar 1 + no fim de precorrer o autómato*)
        if s.fromState = i && s.toState = j then begin (*se encontrar a transição (i symbol j), no autómato*)
          if yam.(i).(j).(1) = V then yam.(i).(j).(1)<-C s.symbol (*se R ainda estiver vazio fica com valor C*)
          else yam.(i).(j).(1)<- U (C s.symbol,yam.(i).(j).(1)) (*se não, une o conteúdo de R com C na forma (C+ R*)
        end
      done;
      if !flag = 1 then begin (*se a flag tiver sido levantada*)
        if yam.(i).(j).(1) = V then yam.(i).(j).(1)<-E (*se R ainda estiver vazio fica com valor 1*)
        else yam.(i).(j).(1)<- U (E,yam.(i).(j).(1)) (*se não une 1 na forma (1+ R)*)
      end;
    done;
  done;
  (*k > 1*)
  for k=2 to n + 1 do (*itera sobre k*)
    for i=1 to n do (*itera sobre i*)
      for j=1 to n do (*itera sobre j*)
        let a = yam.(i).(j).(k-1) in (*R(i,j,k)*)
        let b = yam.(i).(k-1).(k-1) in (*R(i,k,k)*)
        let c = yam.(k-1).(k-1).(k-1) in (*R(k,k,k)*)
        let d = yam.(k-1).(j).(k-1) in (*R(k,j,k)*)
        yam.(i).(j).(k) <- U(a,(P(b,P((S c),d)))); (*R(i,j,k+1) = R(i,j,k) + R(i,k,k).R(k,k,k)*.R(k,j,k)*)
      done;
    done;
  done;
  yam


(*
Assim, o array 'yam' devolvido segue a seguinte configuração

k=1:
R(1,1,1) R(1,2,1) R(1,3,1) ...
R(2,1,1)    ...
R(3,1,1)            ...
...                        ...

k = ...

k=n
R(1,1,n) R(1,2,n) R(1,3,n) ...
R(2,1,n)    ...
R(3,1,1)            ...
...                        ...

Onde R(i,j,k) contem a expressão que lhe está associada
*)


(*
Gera a string para o output do programa
Para cada estado final, vai ao array yamadaArray, buscar a expressão que equivale a R(i,f.(k),n+1)
Se houver mais do que um estado final, faz a união das expressões, tal que Output = R(i,f.(k1),n+1)+...+R(i,f.(km-1),n+1)
*)
let printOutput i f n card_f yamadaArray =
  let str = ref (yamadaArray.(i).(f.(0)).(n+1)) in (*inicializa o valor de retorno*)
    if card_f>1 then
      for k=1 to card_f - 1 do (*se houver mais do que um estado final, faz a união dos R*)
        str:= U(!str,yamadaArray.(i).(f.(k)).(n+1)) (*união dos valores quando card_f>1*)
      done;
    !str (*retorna o resultado*)

let n = read_int() (*conjunto S*)
let i = read_int()(*estado inicial*)
let card_f = read_int() (*cardinalidade do conjunto F*)
let k = read_line() (*conjunto dos estados finais*)
let f = finals card_f k (*converte a string que recebe os estados finais, num array de inteiros de dimensão card_f onde cada posição contem um estado final*)
let card_m = read_int() (*cardinalidade de R*)
let m = trans card_m (*lê as card_m linhas seguintes e constroi o autómato*)
let yamadaArray = yamada n m card_m (*constroi o array 3d*)


(*
Passa a string devolvida por printOutput para a função simplify que simplifica a expressão, e depois é convertida para string com string_of_regexp
A espressão resultante de string_of_regexp(simplify(exp)) é impressa
*)
let () = print_endline(string_of_regexp(simplify(printOutput i f n card_f yamadaArray)))

(*

http://www.di.ubi.pt/~desousa/TC/aula_tc3-pp.pdf
exercícios das aulas práticas
esclarecimento de dúvidas

*)
