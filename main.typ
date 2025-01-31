#import "template.typ": *
#import "@preview/curryst:0.3.0": rule, proof-tree
#show: thmrules

#show: project.with(
  title: [証言定理],
  authors: (
    "PALALANSOUKÎ",
  ),
)

#let uprsans(X) = $upright(sans(#X))$

#let theory(c) = $uprsans(#c)$

#let Cobham   = $theory("R"_0)$
#let Robinson = $theory("Q")$
#let Ind(X)   = $theory("I")#X$
#let Bnd(X)   = $theory("I")#X$
#let OMEGA    = $theory(Omega)$
#let IOpen    = $theory("IOpen")$
#let Peano    = $theory("PA")$

#let BS(i)    = $theory("S")_2^(#i)$
#let BT(i)    = $theory("T")_2^(#i)$

#let complexityClass(c) = $uprsans(#c)$

#let PolyTime          = $complexityClass("P")$
#let NPolyTime         = $complexityClass("NP")$
#let Sigmap(i)         = $complexityClass(Sigma)^upright("p")_#i$
#let Pip(i)            = $complexityClass(Pi)^upright("p")_#i$
#let PolyTimeHierarchy = $complexityClass("PH")$

#let Squarep(i) = $square.big^upright("p")_#i$
#let FP = $complexityClass("FP")$
#let FPSPACE = $complexityClass("FPSPACE")$

#let BASIC = $sans("BASIC")$

#let Sigmab(i)         = $Sigma^upright("b")_#i$
#let Pib(i)            = $Pi^upright("b")_#i$
#let Deltab(i)         = $Delta^upright("b")_#i$

#outline(indent: auto,)

= Preliminaries

== 計算複雑性クラス

言語または関数の計算複雑性クラス $sans(L), sans(K)$ について， $sans(L)^sans(K)$ を，$sans(K)$ の神託のもとでの $sans(L)$ の計算複雑性クラスとする．

#definition[多項式時間階層][
  計算複雑性クラス $Sigmap(i), Pip(i), PolyTimeHierarchy$ を次のように定義する．
  $
    Sigmap(0) &:= PolyTime \
    Sigmap(i+1) &:= NPolyTime^(Sigmap(i)) \
    Pip(i) &:= complexityClass("co")Sigmap(i) \
    PolyTimeHierarchy &:= union.big_(i in Nat) Sigmap(i)
  $
]

$FP$ を多項式時間計算可能な関数の為す計算複雑性クラスとする．

#definition[
  $i >= 1$ について $Squarep(i) := FP^(Sigmap(i - 1))$ と定める．
]

特に $Squarep(1) = FP$, $Squarep(2) = FP^NPolyTime$.

== 算術

#let ArithLang = $cal(L)_"OR"$

#let BALang = $cal(L)_2$
#let div2(x) = $floor(#x\/2)$


算術の言語に $x |-> div2(x),$ $x |-> size(x)$, そして smush function $(x, y) |-> x smash y$

$
  n smash m = 2^(size(n) dot size(m))
$

を追加したものを $BALang$ と呼ぶ．

鋭有界量化子_sharply bounded quantifier_とは次のいずれかの形をした量化子のことである．
$
  (forall x <= size(t)), (exists x <= size(t))
$

#definition[鋭有界論理式][
  $Sigmab(i)$, $Pib(i)$ は次を満たす最小の $BALang$-論理式のクラスである．
  $
    Sigmab(0) = Pib(0) = "現れる量化子が全て鋭有界量化子である論理式から為るクラス" \
    Sigmab(i) union Pib(i) subset.eq Sigmab(i + 1) sect Pib(i + 1) \
    phi, psi in Sigmab(i + 1) ==>
      phi and psi, phi or psi, (forall x < size(t))phi, (exists x < size(t))phi in Sigmab(i+1), not phi in Pib(i+1) \
    phi, psi in Pib(i + 1) ==>
      phi and psi, phi or psi, (forall x < size(t))phi, (exists x < size(t))phi in Pib(i+1), not phi in Sigmab(i+1) \
    phi in Sigmab(i + 1) ==> (exists x <= t)phi in Sigmab(i+1) \
    phi in Pib(i + 1) ==> (forall x <= t)phi in Pib(i+1) \
  $

  $T$ 上の $Deltab(i)$ 論理式は次の条件を満たす論理式 $phi$ の為すクラスである：
  ある $phi_1 in Sigmab(i)$, $phi_2 in Pib(i)$ が存在し $T proves phi <-> phi_1 <-> phi_2 $ を満たす．
]

= $BS(i)$

#let PIND(x) = $#x""theory("-PIND")$
#let IND(x) = $#x""theory("-IND")$

以降論理式は常に否定標準形を取っているとする．

#definition[推件計算][
  推件 $Gamma --> Delta$ が構造規則と以下の推論規則によって導出されるとき， $BS(i)$-証明可能であるといい，
  $BS(i) proves Gamma --> Delta$ と書く．

  #align(center)[
    #table(
      columns: 2,
      align: center + horizon,
      stroke: none,
    
      table.cell(colspan: 2)[
        #proof-tree(
          rule(
            name: $uprsans(upright("I"))$,
            $alpha --> alpha$,
          )
        )
      ],
      [
        #proof-tree(
          rule(
            name: $uprsans(upright("IL"))$,
            $alpha, not alpha -->$
          )
        )
      ],
      [
        #proof-tree(
          rule(
            name: $uprsans(upright("IR"))$,
            $--> alpha, not alpha$
          )
        )
      ],
      [
        #proof-tree(
          rule(
            name: $uprsans(and"L")$,
            $ phi and psi, Gamma --> , Delta $,
            $ phi, psi, Gamma --> Delta$
          )
        )
      ],
      [
        #proof-tree(
          rule(
            name: $uprsans(and"R")$,
            $ Gamma --> phi and psi, Delta $,
            $Gamma --> phi, Delta$,
            $Gamma --> psi, Delta$
          )
        )
      ],
      [
        #proof-tree(
          rule(
            name: $uprsans(or"L")$,
            $phi or psi, Gamma --> Delta $,
            $phi, Gamma --> Delta$,
            $psi, Gamma --> Delta$
          )
        )
      ],
      [
        #proof-tree(
          rule(
            name: $uprsans(or"R")$,
            $ Gamma --> phi or psi, Delta $,
            $ Gamma --> phi, psi, Delta$
          )
        )
    
      ],
      [
        #proof-tree(
          rule(
            name: $uprsans(forall"L")$,
            $ (forall x) phi(x), Gamma --> Delta $,
            $ phi(t), Gamma --> Delta$
          )
        )
      ],
      [
        #proof-tree(
          rule(
            name: $uprsans(forall"R")$,
            $ Gamma --> (forall x) phi(x), Delta$,
            $ Gamma --> phi(a), Delta$
          )
        )
      ],
      [
        #proof-tree(
          rule(
            name: $uprsans(exists"L")$,
            $ (exists x) phi(x), Gamma --> Delta $,
            $ phi(a), Gamma --> Delta$
          )
        )
      ],
      [
        #proof-tree(
          rule(
            name: $uprsans(exists"R")$,
            $ Gamma --> (exists x) phi(x), Delta$,
            $ Gamma --> phi(t), Delta$
          )
        )
      ],
      table.cell(colspan: 2)[
        #proof-tree(
          rule(
            name: $uprsans("CUT")$,
            $Gamma --> Delta$,
            $Gamma --> phi, Delta$,
            $phi, Gamma --> Delta$,
          )
        )
      ],
      table.cell(colspan: 2)[
        #proof-tree(
          rule(
            name: $PIND(Sigmab(i))$,
            $gamma(0), Gamma --> gamma(t), Delta$,
            $gamma(div2(a)), Gamma --> gamma(a), Delta$
          )
        )
      ],
        table.cell(colspan: 2)[
        #proof-tree(
          rule(
            name: $uprsans("BASIC")$,
            $ --> xi$,
          )
        )
      ],
    )
  ]
  
  自由変数(eigenvariable) $a$ は $Gamma, Delta$ に自由に表れないとする．
  $xi$ は $BASIC$ に含まれる開論理式であり， $alpha$ は原始論理式またはその否定， 
  $PIND(Sigmab(i))$ において $gamma$ (principal formula) は $Sigmab(i)$-論理式であるとする．
]

$BS(i) proves --> phi$ のとき，これを $BS(i) proves phi$ と略記する．
$PIND(Sigmab(i))$ を以下の推論規則に置き換えた推件計算を $BT(i)$  と呼ぶ．

$
  #proof-tree(
    rule(
      name: $IND(Sigmab(i))$,
      $gamma(0), Gamma --> gamma(t), Delta$,
      $gamma(a), Gamma --> gamma(a + 1), Delta$
    )
  )
$
ただし $a$ はeigenvariable であり $gamma in Sigmab(i).$

== $Squarep(i)$ の形式化

TODO



== 自由カット除去

#definition[
  証明図 $d$ に現れる論理式 $phi$ が以下の条件をいずれも満たさないとき， $phi$ は自由_free_であるという．
  - $phi$ は非論理的公理の子孫である
  - $phi$ は $PIND(Sigmab(i))$ の principal formula の子孫である．
  またカット規則 で消去される論理式が自由であるとき，そのカットを自由カット_free cut_と呼ぶ．
]

#theorem[自由カット除去 free cut free][
  $BS(i) proves Gamma --> Delta$ ならば，自由カットを持たない証明図が存在する．
]<free-cut-free>

#corollary[
  $Gamma union Delta subset.eq Sigmab(i)$ とする．
  $BS(i) proves Gamma --> Delta$ ならば $Sigmab(i)$-論理式しか現れないような証明図が存在する．
]<free-cut-free-col>

== Parikh の定理

#theorem[
  $BS(i) proves (forall arrow(x))(exists y)phi(arrow(x), y)$ ならば，
  ある項 $t(arrow(x))$ が存在して $BS(i) proves (forall arrow(x))(exists y <= t(arrow(x)))phi(arrow(x), y)$
]

== 証言定理

葉に自然数が割り振られた木を次のようにコードする：例えば木が
$
  brak(A, brak(B, C), D, brak())
$
ならば， 表記通り $\" angle.l \" |-> \"1, 0\"$, $\"A\" |-> \"0, A\"$, $\" angle.r\" |-> \"1,1\"$ で置換する．
$
  w = brak(1,0,0,A,1,0,0,B,0,C,1,1,0,D,1,0,1,1,1,1)
$
木 $w$ の根から続くノードの数， それを根とする $n$ 番目の部分木を返す関数は $BS(1)$ 上 $Deltab(1)$ 定義可能であり， 
それぞれ（記号の乱用だが） $|w|$, $(w)_n$ と表記することにする．

#let wt = $class("relation", ⧐)$
#let cancelwt = $class("relation", cancel(⧐))$

#definition[
  $i >= 1$ とする． 木（を意味する自由変数） $w$ と $phi in Sigmab(i)$ について 論理式 $w wt_i phi$ ($w$ は $phi$ を証言する)を帰納的に定義する
  #footnote[これは一般的な記法ではない．].
  $
    w wt_i alpha &:= alpha " if " alpha in Sigmab(i-1) union Pib(i-1) \
    w wt_i phi and psi &:= [(w)_0 wt_i phi] and [(w)_1 wt_i psi] \
    w wt_i phi or psi &:= [(w)_0 wt_i phi] or [(w)_1 wt_i psi] \
    w wt_i (forall x <= size(t))phi(x) &:= (forall x <= size(t))[(w)_x wt_i phi(x)] \
    w wt_i (exists x <= size(t))phi(x) &:= (exists x <= size(t))[w wt_i phi(x)] \
    w wt_i (exists x <= t)phi(x) &:= lr(|(w)_0|) <= t and [(w)_1 wt_i phi((w)_0)]
  $
]

$"FV"(w wt_i phi) subset.eq {w} union "FV"(phi)$ に注意．
以降 $i$ が明らかな場合は単に $w wt phi$ と書く．
また論理式の列 $w_0 wt_i phi_0, space w_1 wt_i phi_1, space ...$ を
$arrow(w) = w_0, w_1, ...$, $Gamma = phi_0, phi_1, ...$ によって $arrow(w) wt_i Gamma$ と略記する．

#lemma[
  $i >= 1$, $phi in Sigmab(i)$ とする．
  1. $w wt_i phi$  は $BS(1)$ 上で $Deltab(i)$
  2. $BS(1) proves w wt phi --> phi$.
  3. 項 $t_phi$ が存在して $BS(i) proves phi --> (exists w <= t_phi)[w wt phi]$.
]<witness-basic>

#lemma[
  $i >= 1$, $phi in  Sigmab(i)$ とする． $w wt_i phi$ の真偽判定は $Squarep(i)$.
]<witness-evaluate>
#proof[ $phi$ についての帰納法． ]

#theorem[
  $i >= 1$, $Gamma union Delta subset.eq Sigmab(i)$ とする．
  $
    BS(i) proves Gamma --> Delta
  $
  ならば関数 $arrow(F) = F_0, F_1, ... in Squarep(i)$ が存在して
  $
    BS(i) proves arrow(w) wt_i Gamma --> arrow(F) (arrow(w), arrow(b)) wt_i Delta
  $
  ここで $arrow(b)$ は $Gamma, Delta$ に現れるすべての自由変数である．
]<witness-lemma>

#proof[
  $Gamma --> Delta$ の証明図に関する帰納法． @free-cut-free-col より現れる論理式は $Sigmab(i)$ のみとして良い．
  / (構造規則, $uprsans("I"), uprsans("IL"), uprsans("IR"), uprsans("BASIC")$): あきらか．

  / ($uprsans(and"L")$):
    証明図の末尾が以下の形であると仮定する．
    $ 
      #proof-tree(
        rule(
          $ phi and psi, Gamma --> Delta $,
          rule($phi, psi, Gamma --> Delta$, $dots.v$),
        )
      )
    $
    帰納法の仮定より，次が証明可能であるような関数 $arrow(F) in Squarep(i)$ が存在する．
    $
      u wt phi, space v wt psi, space arrow(w) wt Gamma -->
        arrow(F)(u, v, arrow(w), arrow(b)) wt Delta
    $
    関数 $arrow(G) in Squarep(i)$ を次のように定義する．
    $
      G_k (x, arrow(w), arrow(b)) :=
        F_k ((x)_0, (x)_1, arrow(w), arrow(b))
    $
    このとき
    $
      x wt phi and psi, space arrow(w) wt Gamma -->
        arrow(G)(x, arrow(w), arrow(b)) wt Delta
    $
  / ($uprsans(and"R")$):
    証明図の末尾が以下の形であると仮定する．
    $ 
      #proof-tree(
        rule(
          $ Gamma --> phi and psi, Delta $,
          rule($Gamma --> phi, Delta$, $dots.v$),
          rule($Gamma --> psi, Delta$, $dots.v$)
        )
      )
    $
    帰納法の仮定より，次が証明可能であるような関数 $F_phi, F_psi, arrow(G), arrow(H) in Squarep(i)$ が存在する．
    $
      arrow(w) wt Gamma &-->
        F_phi (arrow(w), arrow(b)) wt phi, space 
        arrow(G) (arrow(w), arrow(b)) wt Delta \
      arrow(w) wt Gamma &-->
        F_psi (arrow(w), arrow(b)) wt psi, space
        arrow(H) (arrow(w), arrow(b)) wt Delta
    $
    次のように関数 $I$, $arrow(J)$ を定める．
    $
      I(arrow(w), arrow(b)) &:=
        brak(F_phi (arrow(w), arrow(b)), space F_psi (arrow(w), arrow(b))) \
      J_k (arrow(w), arrow(b)) &:=
        cases(
          G_k (arrow(w), arrow(b)) &" if " F_phi (arrow(w), arrow(b)) cancelwt phi,
          H_k (arrow(w), arrow(b)) &" if " F_psi (arrow(w), arrow(b)) cancelwt psi,
          brak() &" otherwise ",
        
        )
    $
    @witness-evaluate よりこれらは共に $Squarep(i)$. このとき
    $ 
      arrow(w) wt Gamma &-->
        I_phi (arrow(w), arrow(b)) wt phi and psi, space 
        arrow(J) (arrow(w), arrow(b)) wt Delta
    $
  / ($uprsans(or"L")$):
    証明図の末尾が以下の形であると仮定する．
    $     #proof-tree(
      rule(
        $phi or psi, Gamma --> Delta $,
        rule($phi, Gamma --> Delta$, $dots.v$),
        rule($psi, Gamma --> Delta$, $dots.v$)
      ))
    $
    帰納法の仮定より，次が証明可能であるような関数 $arrow(F), arrow(G) in Squarep(i)$ が存在する．
    $
      u wt phi, space arrow(w) wt Gamma &-->
        arrow(F) (u, arrow(w), arrow(b)) wt Delta \
      v wt psi, space arrow(w) wt Gamma &-->
        arrow(G) (v, arrow(w), arrow(b)) wt Delta
    $
    関数 $arrow(H)$ を次のように定める．
    $
      H_k (x, arrow(w), arrow(b)) :=
        cases(
          F_k (x, arrow(w), arrow(b)) & " if " x wt phi,
          G_k (x, arrow(w), arrow(b)) & " if " x wt psi,
          brak() & "otherwise"
        )
    $
    このとき
    $
      x wt phi or psi, space arrow(w) wt Gamma -->
        arrow(H) (x, arrow(w), arrow(b)) wt Delta
    $
  / ($uprsans(or"R")$):
    証明図の末尾が以下の形であると仮定する．
    $
    #proof-tree(
      rule(
        $ Gamma --> phi or psi, Delta $,
        rule($Gamma --> phi, psi, Delta$, $dots.v$)
      )
    )
    $
    帰納法の仮定より，次が証明可能であるような関数 $F_phi, F_psi, arrow(G) in Squarep(i)$ が存在する．
    $
      arrow(w) wt Gamma &-->
        F_phi (arrow(w), arrow(b)) wt phi, space
        F_psi (arrow(w), arrow(b)) wt psi, space
        arrow(G) (arrow(w), arrow(b)) wt Delta
    $
    関数 $arrow(H)$ を次のように定める．
    $
      H (arrow(w), arrow(b)) :=
        brak(F_phi (arrow(w), arrow(b)), F_psi (arrow(w), arrow(b)))
    $
    このとき
    $
      arrow(w) wt Gamma &-->
        H (arrow(w), arrow(b)) wt phi or psi, space
        arrow(G) (arrow(w), arrow(b)) wt Delta
    $

  / ($uprsans(forall"L")$):
    証明図の末尾が以下の形であると仮定する． 現れる論理式は $Sigmab(i)$ のみなのでこのように仮定して良い．
    $
      #proof-tree(
        rule(
          $ (forall x <= t) phi(x), Gamma --> Delta $,
          rule($u <= t -> phi(u), Gamma --> Delta$, $dots.v$)
        )
      )
    $
    帰納法の仮定より，次が証明可能であるような関数 $arrow(F) in Squarep(i)$ が存在する．
    $ u <= t -> u wt phi(u), space arrow(w) wt Gamma -->
      arrow(F)(u, arrow(w), arrow(b)) wt Delta $
    関数 $arrow(G)$ を以下のように定義する．
    $ G_k (v, arrow(b)) :=
      F_k ((v)_u(arrow(b)), arrow(w), arrow(b)) $
    $uprsans(forall"L")$ より以下が成り立つ．
    $ v wt  (forall x <= t)phi(x), arrow(w) wt Gamma -->
        arrow(G)(v, arrow(w), arrow(b)) wt Delta $

  / ($uprsans(forall"R")$):
    証明図の末尾が以下の形であると仮定する． 現れる論理式は $Sigmab(i)$ のみなのでこのように仮定して良い．
    $
      #proof-tree(
        rule(
          $ Gamma --> (forall x <= t)phi(x), Delta $,
          rule($Gamma --> a <= t -> phi(a),  Delta$, $dots.v$)
        )
      )
    $
    帰納法の仮定より，次が証明可能であるような関数 $F$ が存在する．
    $ arrow(w) wt Gamma -->
      a <= t -> F (arrow(w), a, arrow(b)) wt phi(a), space
      arrow(G) (arrow(w), a, arrow(b)) wt Delta $
    次のように関数 $S, H in Squarep(i)$ を定義する．

    $ R (0, arrow(w), arrow(b)) &:= brak() \
      R (c + 1, arrow(w), arrow(b)) &:=
        R (c, arrow(w), arrow(b)) paren.t brak(F (arrow(w), c, arrow(b))) \
      S(arrow(w), arrow(b)) &:= R (t(arrow(b)) + 1, arrow(w), arrow(b))
    $
    $
      H_k (arrow(w), arrow(b)) :=
        cases(
          G_k (arrow(w), a, arrow(b)) &
            " if there is" a <= t(arrow(b)) "such that " F (arrow(w), a, arrow(b)) cancelwt phi(a) \
          brak() & " otherwise"
        )
    $
    このとき，
    $ arrow(w) wt Gamma -->
      S (arrow(w), arrow(b)) wt (forall x <= t)phi(x), space
      arrow(H) (arrow(w), arrow(b)) wt Delta $
    #struct[
      次が証明できれば良い． これは帰納法の仮定より従う．
      $
        a <= t and F (arrow(w), a, arrow(b)) cancelwt phi(a), space arrow(w) wt Gamma -->
        
        arrow(G) (arrow(w), a, arrow(b)) wt Delta
      $
    ]
      
  / ($uprsans(exists"L")$):
    証明図の末尾が以下の形であると仮定する． 現れる論理式は $Sigmab(i)$ のみなのでこのように仮定して良い．
    $
      #proof-tree(
        rule(
          $ (exists x <= t) phi(x), Gamma --> Delta $,
          rule($a <= t and phi(a), Gamma --> Delta$, $dots.v$)
        )
      )
    $
    帰納法の仮定より，次が証明可能であるような関数 $arrow(F) in Squarep(i)$ が存在する．
    $
      a <= t and u wt phi(a), space arrow(w) wt Gamma -->
        arrow(F) (u, arrow(w), a, arrow(b)) wt Delta
    $
    以下のように関数を定義する．
    $
      G_k (u, arrow(w), arrow(b)) :=
        cases(F_k (u, arrow(w), a, arrow(b)) &
          " if there is " a <= t(arrow(b)) "such that " u wt phi(a),
        brak() & " otherwise")
    $
    このとき，
    $
      u wt (exists x <= t)phi(x), space arrow(w) wt Gamma -->
        arrow(G) (u, arrow(w), arrow(b)) wt Delta
    $
  / ($uprsans(exists"R")$):
    証明図の末尾が以下の形であると仮定する． 現れる論理式は $Sigmab(i)$ のみなのでこのように仮定して良い．
    $
    #proof-tree(
      rule(
        $ Gamma --> (exists x <= t) phi(x), Delta$,
        rule($ Gamma --> u <= t and phi(u), Delta$, $dots.v$)
      )
    )
    $
    帰納法の仮定より，次が証明可能であるような関数 $F, arrow(G) in Squarep(i)$ が存在する．
    $
      arrow(w) wt Gamma -->
        u <= t and F (arrow(w), arrow(b)) wt phi(u), space
        arrow(G)(arrow(w), arrow(b)) wt Delta
    $
    $uprsans(exists"R")$ を用いて
    $
      arrow(w) wt Gamma -->
        F (arrow(w), arrow(b)) wt (exists x <= t) phi(x), space
        arrow(G)(arrow(w), arrow(b)) wt Delta
    $

  / ($uprsans("CUT")$):
    証明図の末尾が以下の形であると仮定する． 現れる論理式は $Sigmab(i)$ のみなので $phi in Sigmab(i)$.
    $
    #proof-tree(
      rule(
        $Gamma --> Delta$,
        rule($Gamma --> phi, Delta$, $dots.v$),
        rule($phi, Gamma --> Delta$, $dots.v$),
      )
    )
    $
    帰納法の仮定より，次が証明可能であるような関数 $F, arrow(G), arrow(H) in Squarep(i)$ が存在する．
    $
      arrow(w) wt Gamma &-->
        F (arrow(w), arrow(b)) wt phi, space
        arrow(G)(arrow(w), arrow(b)) wt Delta \
      u wt phi, space arrow(w) wt Gamma &-->
        arrow(H)(u, arrow(w), arrow(b)) wt Delta
    $
    以下のような関数 $arrow(K)$ を定義する．
    $
      K_k (arrow(w), arrow(b)) :=
        cases(
          arrow(G)(arrow(w), arrow(b)) &
            " if " F (arrow(w), arrow(b)) cancelwt phi \
          H_k (F (arrow(w), arrow(b)), arrow(w), arrow(b)) &
            " if " F (arrow(w), arrow(b)) wt phi
        )
    $
    このとき，
    $
      arrow(w) wt Gamma &-->
        arrow(K)(arrow(w), arrow(b)) wt Delta
    $
    #struct[
      次の２つの場合を示せばよい． いずれも帰納法の仮定より従う．
      $
        F (arrow(w), arrow(b)) cancelwt phi, space
        arrow(w) wt Gamma &-->
          arrow(G)(arrow(w), arrow(b)) wt Delta \
        F (arrow(w), arrow(b)) wt phi, space
          arrow(w) wt Gamma &-->
          H_k (F (arrow(w), arrow(b)), arrow(w), arrow(b)) wt Delta
      $]

  / ($PIND(Sigmab(i))$):
    証明図の末尾が以下の形であると仮定する． 
    $
    #proof-tree(
      rule(
        $gamma(0), Gamma --> gamma(t), Delta$,
        rule($gamma(div2(a)), Gamma --> gamma(a), Delta$, $dots.v$)
      )
    )
    $
    帰納法の仮定より，次が証明可能であるような関数 $F, arrow(G) in Squarep(i)$ が存在する．
    $
      u wt gamma(div2(a)), space arrow(w) wt Gamma -->
        F (u, arrow(w), a, arrow(b)) wt gamma(a), space
        arrow(G)(u, arrow(w), a, arrow(b)) wt Delta
    $
    次のように $S$, $K$ を定義する．
    $
      R(a, u_0, arrow(w), arrow(b)) &:=
        cases(
          u_0 &
          " if " a = 0,
          F(R(div2(a), u_0, arrow(w), arrow(b)), arrow(w), a, arrow(b)) &
          " if " a eq.not 0
          ) \
        S(u_0, arrow(w), arrow(b)) &:=
          R(t(arrow(b)), u_0, arrow(w), arrow(b))
    $
    $
      H_k (a, u_0, arrow(w), arrow(b)) &:=
        cases(
          brak()
            &" if " a = 0,
          G_k (R(div2(a), u_0, arrow(w), arrow(b)), arrow(w), a, arrow(b))
            &" if " a eq.not 0 "and" R(div2(a), u_0, arrow(w), arrow(b)) wt gamma(div2(a)),
          H_k (div2(a), u_0, arrow(w), arrow(b)) &
            " if " a eq.not 0 "and" R(div2(a), u_0, arrow(w), arrow(b)) cancelwt gamma(div2(a))
        ) \
      K_k (u_0, arrow(w), arrow(b)) &:=
        H_k (t(arrow(b)), u_0, arrow(w), arrow(b))
    $
    このとき
    $
      u_0 wt gamma(0), space
      arrow(w) wt Gamma -->
      S(u_0, arrow(w), arrow(b)) wt gamma(t), space
      arrow(K)(u_0, arrow(w), arrow(b)) wt  Delta
    $
    #struct[
      次を示せば良い．
      $
        &u_0 wt gamma(0), space
        arrow(w) wt Gamma, space \
        &R(div2(a), u_0, arrow(w), arrow(b)) wt gamma(div2(a)) or
          or.big arrow(H) (div2(a), u_0, arrow(w), arrow(b)) wt Delta \
        -->
        &R(a, u_0, arrow(w), arrow(b)) wt gamma(a) or or.big
        arrow(H) (a, u_0, arrow(w), arrow(b)) wt Delta
      $
      これは以下の２つから従う． ここで $R_a := R(a, u_0, arrow(w), arrow(b))$, 
      $H_a := H(a, u_0, arrow(w), arrow(b))$ と略記している．
      $
        &u_0 wt gamma(0), space
        arrow(w) wt Gamma, space \
        &R_(div2(a)) wt gamma(div2(a))  \
        -->
        &F(R_(div2(a)), arrow(w), a, arrow(b)) wt gamma(a), space
        arrow(G)(R_(div2(a)), arrow(w), a, arrow(b)) wt Delta \

        &\ &\

        &u_0 wt gamma(0), space
        arrow(w) wt Gamma, space \
        &R_(div2(a)) cancelwt gamma(div2(a)), or.big arrow(H)_(div2(a)) wt Delta \
        -->
        &F(R_(div2(a)), arrow(w), a, arrow(b)) wt gamma(a), space
        or.big arrow(H)_(div2(a)) wt Delta
      $
      下はトートロジー， 上は帰納法の仮定より従う．
    ]
]

#corollary[証言定理][
  $i >= 1$, $phi in Sigmab(i)$ とする．
  $BS(i) proves (forall x)(exists y) phi(x, y)$ ならば関数 $F in Squarep(i)$ が存在して，
  $ BS(i) proves (forall x) phi(x, F(x)) $
]
#proof[
  Parikhの定理より， 項 $t(x)$ が存在して $BS(i) proves (exists y <= t(x))phi(x, y) $.
  @witness-lemma と @witness-basic よりある関数 $F in Squarep(i)$ が存在して，
  $BS(i) proves phi(x, F(x))$.
]
