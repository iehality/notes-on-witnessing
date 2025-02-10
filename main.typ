#import "template.typ": *
#import "@preview/curryst:0.3.0": rule, proof-tree
#show: thmrules

#show: project.with(
  title: [証言定理],
  authors: ("Palalansoukî",),
  repo: "https://github.com/iehality/notes-on-witnessing",
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


算術の言語に $x |-> div2(x),$ $x |-> size(x)$, そして smash function $(x, y) |-> x smash y$

$
  n smash m = 2^(size(n) dot size(m))
$

を追加したものを $BALang$ と呼ぶ．

鋭有界量化子_sharply bounded quantifier_とは次のいずれかの形をした量化子のことである．
$
  (forall x <= size(t)), (exists x <= size(t))
$

#definition[
  $Sigmab(i)$, $Pib(i)$ は次を満たす最小の $BALang$-論理式のクラスである．
  $
    Sigmab(0) = Pib(0) = "鋭有界論理式のクラス" = "現れる量化子が全て鋭有界量化子である論理式から為るクラス" \
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
  推件 $Gamma ==> Delta$ が構造規則と以下の推論規則によって導出されるとき， $BS(i)$-証明可能であるといい，
  $BS(i) proves Gamma ==> Delta$ と書く．

  #align(center)[
    #table(
      columns: 2,
      align: center + horizon,
      stroke: none,
    
      table.cell(colspan: 2)[
        #proof-tree(
          rule(
            name: $uprsans(upright("I"))$,
            $alpha ==> alpha$,
          )
        )
      ],
      [
        #proof-tree(
          rule(
            name: $uprsans(upright("IL"))$,
            $alpha, not alpha ==>$
          )
        )
      ],
      [
        #proof-tree(
          rule(
            name: $uprsans(upright("IR"))$,
            $==> alpha, not alpha$
          )
        )
      ],
      [
        #proof-tree(
          rule(
            name: $uprsans(and"L")$,
            $ phi and psi, Gamma ==> , Delta $,
            $ phi, psi, Gamma ==> Delta$
          )
        )
      ],
      [
        #proof-tree(
          rule(
            name: $uprsans(and"R")$,
            $ Gamma ==> phi and psi, Delta $,
            $Gamma ==> phi, Delta$,
            $Gamma ==> psi, Delta$
          )
        )
      ],
      [
        #proof-tree(
          rule(
            name: $uprsans(or"L")$,
            $phi or psi, Gamma ==> Delta $,
            $phi, Gamma ==> Delta$,
            $psi, Gamma ==> Delta$
          )
        )
      ],
      [
        #proof-tree(
          rule(
            name: $uprsans(or"R")$,
            $ Gamma ==> phi or psi, Delta $,
            $ Gamma ==> phi, psi, Delta$
          )
        )
    
      ],
      [
        #proof-tree(
          rule(
            name: $uprsans(forall"L")$,
            $ (forall x) phi(x), Gamma ==> Delta $,
            $ phi(t), Gamma ==> Delta$
          )
        )
      ],
      [
        #proof-tree(
          rule(
            name: $uprsans(forall"R")$,
            $ Gamma ==> (forall x) phi(x), Delta$,
            $ Gamma ==> phi(a), Delta$
          )
        )
      ],
      [
        #proof-tree(
          rule(
            name: $uprsans(exists"L")$,
            $ (exists x) phi(x), Gamma ==> Delta $,
            $ phi(a), Gamma ==> Delta$
          )
        )
      ],
      [
        #proof-tree(
          rule(
            name: $uprsans(exists"R")$,
            $ Gamma ==> (exists x) phi(x), Delta$,
            $ Gamma ==> phi(t), Delta$
          )
        )
      ],
      table.cell(colspan: 2)[
        #proof-tree(
          rule(
            name: $uprsans("CUT")$,
            $Gamma ==> Delta$,
            $Gamma ==> phi, Delta$,
            $phi, Gamma ==> Delta$,
          )
        )
      ],
      table.cell(colspan: 2)[
        #proof-tree(
          rule(
            name: $PIND(Sigmab(i))$,
            $gamma(0), Gamma ==> gamma(t), Delta$,
            $gamma(div2(a)), Gamma ==> gamma(a), Delta$
          )
        )
      ],
        table.cell(colspan: 2)[
        #proof-tree(
          rule(
            name: $uprsans("BASIC")$,
            $ ==> beta$,
          )
        )
      ],
    )
  ]
  
  $a$ は自由変数であり $Gamma, Delta, gamma(x), t$ に自由に表れないとする．
  $beta$ は $BASIC$ に含まれる開論理式であり， $alpha$ は原始論理式またはその否定， 
  $PIND(Sigmab(i))$ において $gamma$ (principal formula) は $Sigmab(i)$-論理式であるとする．
]

$BS(i) proves ==> phi$ のとき，これを $BS(i) proves phi$ と略記する．
$PIND(Sigmab(i))$ を以下の推論規則に置き換えた推件計算を $BT(i)$  と呼ぶ．

$
  #proof-tree(
    rule(
      name: $IND(Sigmab(i))$,
      $gamma(0), Gamma ==> gamma(t), Delta$,
      $gamma(a), Gamma ==> gamma(a + 1), Delta$
    )
  )
$
ただし $a$ は $Gamma,  Delta, gamma(x), t$ に現れず $gamma in Sigmab(i).$

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
  $BS(i) proves Gamma ==> Delta$ ならば，自由カットを持たない証明図が存在する．
]<free-cut-free>

#corollary[
  $Gamma union Delta subset.eq Sigmab(i)$ とする．
  $BS(i) proves Gamma ==> Delta$ ならば $Sigmab(i)$-論理式しか現れないような証明図が存在する．
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
  mu = brak(1,0,0,A,1,0,0,B,0,C,1,1,0,D,1,0,1,1,1,1)
$
木 $mu$ の根から続くノードの数， それを根とする $n$ 番目の部分木を返す関数は $BS(1)$ 上 $Deltab(1)$ 定義可能であり， 
それぞれ（記号の乱用だが） $size(mu)$, $(mu)_n$ と表記することにする． 木を指す変数記号は $mu, eta, xi, pi, ...$ と表記する．

#let wt = $class("relation", ⧐)$
#let cancelwt = $class("relation", cancel(⧐))$

#definition[
  $i >= 1$ とする． 木（を意味する自由変数） $mu$ と $phi in Sigmab(i)$ について 論理式 $mu wt_i phi$ ($mu$ は $phi$ を証言する)を帰納的に定義する
  #footnote[これは一般的な記法ではない．].
  $
    mu wt_i alpha &:= alpha " if " alpha in Sigmab(i-1) union Pib(i-1) \
    mu wt_i phi and psi &:= [(mu)_0 wt_i phi] and [(mu)_1 wt_i psi] \
    mu wt_i phi or psi &:= [(mu)_0 = 0 and (mu)_1 wt_i phi] or [(mu)_0 eq.not 0 and (mu)_1 wt_i psi] \
    mu wt_i (forall x <= size(t))phi(x) &:= (forall x <= size(t))[(mu)_x wt_i phi(x)] \
    mu wt_i (exists x <= t)phi(x) &:= (mu)_0 <= t and [(mu)_1 wt_i phi((mu)_0)]
  $
]

$"FV"(mu wt_i phi) subset.eq {mu} union "FV"(phi)$ に注意．
以降 $i$ が明らかな場合は単に $mu wt phi$ と書く．
また論理式の列 $w_0 wt_i phi_0, space w_1 wt_i phi_1, space ...$ を
$arrow(mu) = w_0, w_1, ...$, $Gamma = phi_0, phi_1, ...$ によって $arrow(mu) wt_i Gamma$ と略記する．

#lemma[
  $i >= 1$, $phi in Sigmab(i)$ とする．
  1. $mu wt phi$  は $BS(1)$ 上で $Deltab(i)$.
  2. $BS(1) proves mu wt phi ==> phi$.
  3. 項 $t_phi$ が存在して $BS(i) proves phi ==> (exists mu <= t_phi)[mu wt phi]$.
]<witness-basic>

#lemma[
  $i >= 1$, $phi(arrow(x)) in  Sigmab(i)$ とする． 関数
  $
    (mu, arrow(x)) |->
      cases(
        1 &" if " mu wt phi(arrow(x)),
        0 &" if " mu cancelwt phi(arrow(x))
        )
  $
  は $Squarep(i)$.
]<witness-evaluate>
#proof[ $phi$ についての帰納法． ]

#theorem[
  $i >= 1$, $Gamma union Delta subset.eq Sigmab(i)$ とする．
  $
    BS(i) proves Gamma ==> Delta
  $
  ならば関数 $arrow(F) = F_0, F_1, ... in Squarep(i)$ が存在して
  $
    BS(i) proves arrow(mu) wt Gamma ==> arrow(F) (arrow(mu), arrow(b)) wt Delta
  $
  ここで $arrow(b)$ は $Gamma, Delta$ に現れるすべての自由変数である．
]<witness-lemma>

#proof[
  $Gamma ==> Delta$ の証明図に関する帰納法． @free-cut-free-col より現れる論理式は $Sigmab(i)$ のみとして良い．
  / (構造規則のとき, 証明木の根が $Sigmab(i-1)$-論理式であるとき): あきらか．

  / ($uprsans(and"L")$):
    証明図の末尾が以下の形であると仮定する．
    $ 
      #proof-tree(
        rule(
          $ phi and psi, Gamma ==> Delta $,
          rule($phi, psi, Gamma ==> Delta$, $dots.v$),
        )
      )
    $
    帰納法の仮定より，次が証明可能であるような関数 $arrow(F) in Squarep(i)$ が存在する．
    $
      eta wt phi, space xi wt psi, space arrow(mu) wt Gamma ==>
        arrow(F)(eta, xi, arrow(mu), arrow(b)) wt Delta
    $
    関数 $arrow(G) in Squarep(i)$ を次のように定義する．
    $
      G_k (pi, arrow(mu), arrow(b)) := F_k ((pi)_0, (pi)_1, arrow(mu), arrow(b))
    $
    このとき
    $
      pi wt phi and psi, space arrow(mu) wt Gamma ==> arrow(G)(pi, arrow(mu), arrow(b)) wt Delta
    $
  / ($uprsans(and"R")$):
    証明図の末尾が以下の形であると仮定する．
    $ 
      #proof-tree(
        rule(
          $ Gamma ==> phi and psi, Delta $,
          rule($Gamma ==> phi, Delta$, $dots.v$),
          rule($Gamma ==> psi, Delta$, $dots.v$)
        )
      )
    $
    帰納法の仮定より，次が証明可能であるような関数 $F_phi, F_psi, arrow(G), arrow(H) in Squarep(i)$ が存在する．
    $
      arrow(mu) wt Gamma &==>
        F_phi (arrow(mu), arrow(b)) wt phi, space 
        arrow(G) (arrow(mu), arrow(b)) wt Delta \
      arrow(mu) wt Gamma &==>
        F_psi (arrow(mu), arrow(b)) wt psi, space
        arrow(H) (arrow(mu), arrow(b)) wt Delta
    $
    次のように関数 $I$, $arrow(J)$ を定める．
    $
      I(arrow(mu), arrow(b)) &:=
        brak(F_phi (arrow(mu), arrow(b)), space F_psi (arrow(mu), arrow(b))) \
      J_k (arrow(mu), arrow(b)) &:=
        cases(
          G_k (arrow(mu), arrow(b)) &" if " F_phi (arrow(mu), arrow(b)) cancelwt phi,
          H_k (arrow(mu), arrow(b)) &" if " F_psi (arrow(mu), arrow(b)) cancelwt psi,
          brak() &" otherwise ",
        
        )
    $
    @witness-evaluate よりこれらは共に $Squarep(i)$. このとき
    $ 
      arrow(mu) wt Gamma &==>
        I_phi (arrow(mu), arrow(b)) wt phi and psi, space 
        arrow(J) (arrow(mu), arrow(b)) wt Delta
    $
  / ($uprsans(or"L")$):
    証明図の末尾が以下の形であると仮定する．
    $     #proof-tree(
      rule(
        $phi or psi, Gamma ==> Delta $,
        rule($phi, Gamma ==> Delta$, $dots.v$),
        rule($psi, Gamma ==> Delta$, $dots.v$)
      ))
    $
    帰納法の仮定より，次が証明可能であるような関数 $arrow(F), arrow(G) in Squarep(i)$ が存在する．
    $
      eta wt phi, space arrow(mu) wt Gamma &==>
        arrow(F) (eta, arrow(mu), arrow(b)) wt Delta \
      eta wt psi, space arrow(mu) wt Gamma &==>
        arrow(G) (eta, arrow(mu), arrow(b)) wt Delta
    $
    関数 $arrow(H)$ を次のように定める．
    $
      H_k (x, arrow(mu), arrow(b)) :=
        cases(
          F_k (x, arrow(mu), arrow(b)) & "if" (x)_0 = 0,
          G_k (x, arrow(mu), arrow(b)) & "otherwise",
        )
    $
    このとき
    $
      pi wt phi or psi, space arrow(mu) wt Gamma ==>
        arrow(H) (pi, arrow(mu), arrow(b)) wt Delta
    $
  / ($uprsans(or"R")$):
    証明図の末尾が以下の形であると仮定する．
    $
    #proof-tree(
      rule(
        $ Gamma ==> phi or psi, Delta $,
        rule($Gamma ==> phi, psi, Delta$, $dots.v$)
      )
    )
    $
    帰納法の仮定より，次が証明可能であるような関数 $F_phi, F_psi, arrow(G) in Squarep(i)$ が存在する．
    $
      arrow(mu) wt Gamma &==>
        F_phi (arrow(mu), arrow(b)) wt phi, space
        F_psi (arrow(mu), arrow(b)) wt psi, space
        arrow(G) (arrow(mu), arrow(b)) wt Delta
    $
    関数 $arrow(H)$ を次のように定める．
    $
      H (arrow(mu), arrow(b)) :=
        cases(
          brak(0, F_(phi)(arrow(mu), arrow(b))) &"if" F_(phi)(arrow(mu), arrow(b)) wt phi,
          brak(1, F_(psi)(arrow(mu), arrow(b))) &"if" F_(psi)(arrow(mu), arrow(b)) wt phi
        )
    $
    このとき
    $
      arrow(mu) wt Gamma &==>
        H (arrow(mu), arrow(b)) wt phi or psi, space
        arrow(G) (arrow(mu), arrow(b)) wt Delta
    $

  / ($uprsans(forall"L")$):
    証明図の末尾が以下の形であると仮定する． 現れる論理式は $Sigmab(i)$ のみなのでこのように仮定して良い．
    $
      #proof-tree(
        rule(
          $ (forall x <= size(t)) phi(x), Gamma ==> Delta $,
          rule($u <= size(t) -> phi(u), Gamma ==> Delta$, $dots.v$)
        )
      )
    $
    帰納法の仮定より，次が証明可能であるような関数 $arrow(F) in Squarep(i)$ が存在する．
    $
      u <= |t| -> eta wt phi(u), space arrow(mu) wt Gamma ==>
      arrow(F)(eta, arrow(mu), arrow(b)) wt Delta
    $
    関数 $arrow(G)$ を以下のように定義する．
    $ 
      G_k (xi, arrow(mu), arrow(b)) := F_k ((xi)_(u(arrow(b))), arrow(mu), arrow(b))
    $
    $uprsans(forall"L")$ より以下が成り立つ．
    $
      xi wt (forall x <= t)phi(x), arrow(mu) wt Gamma ==> arrow(G)(xi, arrow(mu), arrow(b)) wt Delta
    $

  / ($uprsans(forall"R")$):
    証明図の末尾が以下の形であると仮定する． 現れる論理式は $Sigmab(i)$ のみなのでこのように仮定して良い．
    $
      #proof-tree(
        rule(
          $ Gamma ==> (forall x <= size(t))phi(x), Delta $,
          rule($Gamma ==> a <= size(t) -> phi(a),  Delta$, $dots.v$)
        )
      )
    $
    帰納法の仮定より，次が証明可能であるような関数 $F$ が存在する．
    $ arrow(mu) wt Gamma ==>
      a <= size(t) -> F(arrow(mu), a, arrow(b)) wt phi(a), space
      arrow(G) (arrow(mu), a, arrow(b)) wt Delta $
    次のように関数 $S, H in Squarep(i)$ を定義する．

    $ R (0, arrow(mu), arrow(b)) &:= brak() \
      R (c + 1, arrow(mu), arrow(b)) &:=
        R (c, arrow(mu), arrow(b)) paren.t brak(F (arrow(mu), c, arrow(b))) \
      S(arrow(mu), arrow(b)) &:= R (|t(arrow(b))| + 1, arrow(mu), arrow(b))
    $
    $
      H_k (arrow(mu), arrow(b)) :=
        cases(
          G_k (arrow(mu), a, arrow(b)) &
            " if there is" a <= |t(arrow(b))| "such that " F (arrow(mu), a, arrow(b)) cancelwt phi(a) \
          brak() & " otherwise"
        )
    $
    このとき，
    $ arrow(mu) wt Gamma ==>
      S (arrow(mu), arrow(b)) wt (forall x <= t)phi(x), space
      arrow(H) (arrow(mu), arrow(b)) wt Delta $
    #struct[
      次が証明できれば良い． これは帰納法の仮定より従う．
      $
        a <= t and F (arrow(mu), a, arrow(b)) cancelwt phi(a), space arrow(mu) wt Gamma ==>
        
        arrow(G) (arrow(mu), a, arrow(b)) wt Delta
      $
    ]
      
  / ($uprsans(exists"L")$):
    証明図の末尾が以下の形であると仮定する． 現れる論理式は $Sigmab(i)$ のみなのでこのように仮定して良い．
    $
      #proof-tree(
        rule(
          $ (exists x <= t) phi(x), Gamma ==> Delta $,
          rule($a <= t and phi(a), Gamma ==> Delta$, $dots.v$)
        )
      )
    $
    帰納法の仮定より，次が証明可能であるような関数 $arrow(F) in Squarep(i)$ が存在する．
    $
      a <= t and (eta wt phi(a)), space arrow(mu) wt Gamma ==>
        arrow(F) (eta, arrow(mu), a, arrow(b)) wt Delta
    $
    以下のように $arrow(G)$ を定める．
    $
      G_k (eta, arrow(mu), arrow(b)) :=
        F_(k)((eta)_1, arrow(mu), (eta)_0, b)
    $
    このとき，
    $
      eta wt (exists x <= t)phi(x), space arrow(mu) wt Gamma ==>
        arrow(G)(eta, arrow(mu), arrow(b)) wt Delta
    $
  / ($uprsans(exists"R")$):
    証明図の末尾が以下の形であると仮定する． 現れる論理式は $Sigmab(i)$ のみなのでこのように仮定して良い．
    $
    #proof-tree(
      rule(
        $ Gamma ==> (exists x <= t) phi(x), Delta$,
        rule($ Gamma ==> eta <= t and phi(eta), Delta$, $dots.v$)
      )
    )
    $
    帰納法の仮定より，次が証明可能であるような関数 $F, arrow(G) in Squarep(i)$ が存在する．
    $
      arrow(mu) wt Gamma ==>
        eta <= t and F (arrow(mu), arrow(b)) wt phi(eta), space
        arrow(G)(arrow(mu), arrow(b)) wt Delta
    $
    $
      H(arrow(mu), arrow(b)) := brak(t(arrow(b)), F(arrow(mu), arrow(b)))
    $
    $uprsans(exists"R")$ を用いて
    $
      arrow(mu) wt Gamma ==>
        H (arrow(mu), arrow(b)) wt (exists x <= t) phi(x), space
        arrow(G)(arrow(mu), arrow(b)) wt Delta
    $

  / ($uprsans("CUT")$):
    証明図の末尾が以下の形であると仮定する． 現れる論理式は $Sigmab(i)$ のみなので $phi in Sigmab(i)$.
    $
    #proof-tree(
      rule(
        $Gamma ==> Delta$,
        rule($Gamma ==> phi, Delta$, $dots.v$),
        rule($phi, Gamma ==> Delta$, $dots.v$),
      )
    )
    $
    帰納法の仮定より，次が証明可能であるような関数 $F, arrow(G), arrow(H) in Squarep(i)$ が存在する．
    $
      arrow(mu) wt Gamma &==>
        F (arrow(mu), arrow(b)) wt phi, space
        arrow(G)(arrow(mu), arrow(b)) wt Delta \
      eta wt phi, space arrow(mu) wt Gamma &==>
        arrow(H)(eta, arrow(mu), arrow(b)) wt Delta
    $
    以下のような関数 $arrow(K)$ を定義する．
    $
      K_k (arrow(mu), arrow(b)) :=
        cases(
          arrow(G)(arrow(mu), arrow(b)) &
            " if " F (arrow(mu), arrow(b)) cancelwt phi \
          H_k (F (arrow(mu), arrow(b)), arrow(mu), arrow(b)) &
            " if " F (arrow(mu), arrow(b)) wt phi
        )
    $
    このとき，
    $
      arrow(mu) wt Gamma &==>
        arrow(K)(arrow(mu), arrow(b)) wt Delta
    $
    #struct[
      次の２つの場合を示せばよい． いずれも帰納法の仮定より従う．
      $
        F (arrow(mu), arrow(b)) cancelwt phi, space
        arrow(mu) wt Gamma &==>
          arrow(G)(arrow(mu), arrow(b)) wt Delta \
        F (arrow(mu), arrow(b)) wt phi, space
          arrow(mu) wt Gamma &==>
          H_k (F (arrow(mu), arrow(b)), arrow(mu), arrow(b)) wt Delta
      $]

  / ($PIND(Sigmab(i))$):
    証明図の末尾が以下の形であると仮定する． 
    $
    #proof-tree(
      rule(
        $gamma(0), Gamma ==> gamma(t), Delta$,
        rule($gamma(div2(a)), Gamma ==> gamma(a), Delta$, $dots.v$)
      )
    )
    $
    帰納法の仮定より，次が証明可能であるような関数 $F, arrow(G) in Squarep(i)$ が存在する．
    $
      eta wt gamma(div2(a)), space arrow(mu) wt Gamma ==>
        F (eta, arrow(mu), a, arrow(b)) wt gamma(a), space
        arrow(G)(eta, arrow(mu), a, arrow(b)) wt Delta
    $
    次のように $S$, $K$ を定義する．
    $
      R(a, xi, arrow(mu), arrow(b)) &:=
        cases(
          xi &
          " if " a = 0,
          F(R(div2(a), xi, arrow(mu), arrow(b)), arrow(mu), a, arrow(b)) &
          " if " a eq.not 0
          ) \
        S(xi, arrow(mu), arrow(b)) &:=
          R(t(arrow(b)), xi, arrow(mu), arrow(b))
    $
    $
      H_k (a, xi, arrow(mu), arrow(b)) &:=
        cases(
          brak()
            &" if " a = 0,
          G_k (R(div2(a), xi, arrow(mu), arrow(b)), arrow(mu), a, arrow(b))
            &" if " a eq.not 0 "and" R(div2(a), xi, arrow(mu), arrow(b)) wt gamma(div2(a)),
          H_k (div2(a), xi, arrow(mu), arrow(b)) &
            " if " a eq.not 0 "and" R(div2(a), xi, arrow(mu), arrow(b)) cancelwt gamma(div2(a))
        ) \
      K_k (xi, arrow(mu), arrow(b)) &:=
        H_k (t(arrow(b)), xi, arrow(mu), arrow(b))
    $
    このとき
    $
      xi wt gamma(0), space
      arrow(mu) wt Gamma ==>
      S(xi, arrow(mu), arrow(b)) wt gamma(t), space
      arrow(K)(xi, arrow(mu), arrow(b)) wt  Delta
    $
    #struct[
      次を示せば良い．
      $
        &xi wt gamma(0), space
        arrow(mu) wt Gamma, space \
        &R(div2(a), xi, arrow(mu), arrow(b)) wt gamma(div2(a)) or
          or.big arrow(H) (div2(a), xi, arrow(mu), arrow(b)) wt Delta \
        ==>
        &R(a, xi, arrow(mu), arrow(b)) wt gamma(a) or or.big
        arrow(H) (a, xi, arrow(mu), arrow(b)) wt Delta
      $
      これは以下の２つから従う． ここで $R_a := R(a, xi, arrow(mu), arrow(b))$, 
      $H_a := H(a, xi, arrow(mu), arrow(b))$ と略記している．
      $
        &xi wt gamma(0), space
        arrow(mu) wt Gamma, space \
        &R_(div2(a)) wt gamma(div2(a))  \
        ==>
        &F(R_(div2(a)), arrow(mu), a, arrow(b)) wt gamma(a), space
        arrow(G)(R_(div2(a)), arrow(mu), a, arrow(b)) wt Delta \

        &\ &\

        &xi wt gamma(0), space
        arrow(mu) wt Gamma, space \
        &R_(div2(a)) cancelwt gamma(div2(a)), or.big arrow(H)_(div2(a)) wt Delta \
        ==>
        &F(R_(div2(a)), arrow(mu), a, arrow(b)) wt gamma(a), space
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
