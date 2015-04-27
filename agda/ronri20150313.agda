module ronri20150313 where

open import Data.Nat

data Form : Set where
  Atom : ℕ -> Form
  ⊥ : Form
  ¬ : Form -> Form
  _∨_ : Form -> Form -> Form
  _∧_ : Form -> Form -> Form
  _⊃_ : Form -> Form -> Form
{-
可算個の命題変数 (propositional variables) があると
しており , n 番目の命題変数が Atom n である . ⊥は
偽を表わす命題記号 , ¬ が否定 , ∨ , ∧ , ⊃はそれぞれ
選言 , 連言 , 含意をつくる論理記号である .
Form 型の値に対する等号を規定しておく . これは
帰納的定義から機械的に得られるものだが , Agda シ
ステムは等号を用意しておらず , 利用者が定義しなけ
ればならない .
-}
open import Data.Bool renaming (_∧_ to _and_; _∨_ to _or_) hiding (_≟_)
open import Relation.Binary.Core 
open import Relation.Nullary hiding (¬_)

_==_ : Form → Form → Bool
(Atom m) == (Atom n) with m ≟ n 
... | yes _ = true
... | no _ = false
( ¬ P) == ( ¬ P’) = P == P’
(P ∨ Q) == (P’ ∨ Q’) = (P == P’) and (Q == Q’)
(P ∧ Q) == (P’ ∧ Q’) = (P == P’) and (Q == Q’)
(P ⊃ Q) == (P’ ⊃ Q’) = (P == P’) and (Q == Q’)
_ == _ = false

{-
こうすれば , たとえば , 真偽値計算のプログラムを
書くことができる . ev は , 論理式と , 各命題変数への
真偽値の付値φを受けとって , その付値のもとでの論
理式の真偽値を返すものである . ここで , 引数である
論理式の形に関する場合分けが行なわれていること
に注意する . 浅い付値では , そのようなことができな
かった .
-}

ev : Form → (ℕ → Bool) → Bool
ev (Atom n) φ = φ n
ev ⊥ φ        = false
ev ( ¬ P) φ   = not (ev P φ)  
ev (P ∨ Q) φ  = ev P φ or ev Q φ
ev (P ∧ Q) φ  = ev P φ and ev Q φ
ev (P ⊃ Q) φ  = not (ev P φ) or ev Q φ 

{-
浅い符号化のときのように , 自然推論による推論も
符号化することができる . そのために , 各論理式の証
明図全体がつくるデータ型 Proof を次のように定義
する .
-}
open import Data.List

_＼_ : List Form → Form → List Form
Ps ＼ Q = dropWhile (λ x → x == Q) Ps 

data Proof : List Form → Form → Set where
  Assume : (P : Form) → Proof (P ∷ []) P
  ⊥E : {fs : List Form} → {P : Form} → Proof fs ⊥ → Proof fs P
  ¬I : {fs : List Form} → {P : Form} → Proof fs ⊥ → Proof (fs ＼ P) (¬ P)
  ¬E : {fs gs : List Form} → {P : Form} → Proof fs P → Proof gs ( ¬ P) → Proof (fs ++ gs) ⊥
  ∧I : {fs gs : List Form} → {P Q : Form} → Proof fs P → Proof gs Q → Proof (fs ++ gs) (P ∧ Q)
  ∧E1 : {fs : List Form} → {P Q : Form} → Proof fs (P ∧ Q) → Proof fs P
  ∧E2 : {fs : List Form} → {P Q : Form} → Proof fs (P ∧ Q) → Proof fs Q
  ∨I1 : {fs : List Form} → {P Q : Form} → Proof fs P → Proof fs (P ∨ Q)
  ∨I2 : {fs : List Form} → {P Q : Form} → Proof fs Q → Proof fs (P ∨ Q)
  ∨E : {fs gs hs : List Form} → {P Q R : Form} → Proof fs (P ∨ Q) → Proof gs R → Proof hs R → Proof ((fs ++ (gs ＼ P)) ++ (hs ＼ Q)) R
  ⊃I : {fs : List Form} → {P Q : Form} → Proof fs Q → Proof (fs ＼ P) (P ⊃ Q)
  ⊃E : {fs gs : List Form} → {P Q : Form} → Proof fs P → Proof gs (P ⊃ Q) → Proof (fs ++ gs) Q
  LEM : (P : Form) → Proof [] (P ∨ ( ¬ P))
{-
＼は Proof の定義のために必要な演算である .
Ps ＼ Q は , 論理式のリスト Ps から , 論理式 Q を
除去してえられるリストを返す演算子である . Ps の
中に Q が二回以上現われていても , Ps ＼ Q の中に
は Q は現われない .
Proof Ps Q は , リスト Ps にある論理式を前提
(premise) とし , Q を帰結 (conclusion) とする証明図
全体がつくるデータ型である . 証明規則毎に , Proof
の構成子が一つずつあたえられている . たとえば
Assume P は論理式 P を前提とし , それ自身を帰結
とする証明図である .
個別の構成子に対する説明は , 自然演繹を知る読者
には不要であろう . ただ , ここではプログラミングの
簡単のために , 前提の解放 (discharge) の処理を単純
にしている . 論理式 P を解放するときには , 前提のリ
ストのなかのすべての P を解放する . 一般には , すべ
ての P の出現を解放する必要はなく , その一部分 (0
個の出現でもよい ) を解放するだけでよい , として十
分である .
最後の構成子は , 排中律であり , LEM P は P ∨ ¬
P の証明図である . 直観主義論理を得たければ , この
構成子を定義しなければよい . 浅い符号化では , LEM
を postulate によって導入しなければならなかった
が , ここでは , データ型宣言に一つの構成子を加える
だけでよい .
以上の設定のもとで , Atom ０という , 特定の命題
に関する二重否定除去の規則の証明を次のように書
くことができる .
A : Form
A = Atom ０
DNE0 : Proof [] (( ¬ ( ¬ A)) ⊃ A)
DNE0 = ⊃ I ( ∨ E (LEM A)
(Assume A)
( ⊥ E ( ¬ E (Assume ( ¬ A))
(Assume ( ¬ ( ¬ A))))))
-}
