<link rel="stylesheet" href="{{site.github.url}}/css/tpp2020.css" charset="utf-8">

# The 16th Theorem Proving and Provers meeting (TPP 2020)

TPP (Theorem Proving and Provers) ミーティングは，
2005年から年に1回開催され，
定理証明系を作っている人から使う側の人まで幅広い人たちが集まり，
様々な側面からの話をしてアイディアの交換をしてきたものです．

ミーティング期間中の討論を大切にしたいと考えていますので，
出来上がった仕事の講演だけでなく，進行中の仕事，未完成の仕事についての講演も歓迎します．
参加者には可能な限りご講演いただくことを期待しています．

TPP is a series of annual meetings for developers as well as users of theorem provers.
Discussions from various aspects and exchanges of ideas have taken place in the past meetings since 2005.

We regard the discussions during the meeting to be most important.
As such, not only the talks about completed work, but those about ongoing 
work and half-baked work are also welcome.
We hope all participants would consider giving a talk.


## 開催日程 / Date
2020年11月16日(月), 17日(火) / Mon. 16th to Tue. 17th, November.

## 会場 / Venue
今年度はコロナウイルス感染症 (COVID-19)の感染拡大防止のため，オンライン(Zoom)で開催する予定です．
事前に参加申し込みしていただいた方々には別途，接続方法等の詳細をお知らせします．

In order to prevent the spread of coronavirus infection (COVID-19), 
we are planning to hold an online meeting (Zoom) this year. 
Those who have registered in advance will be notified of the details of how to join the meeting.

<!--
## 住所 / Address

〒755-8611 山口県宇部市常盤台2-16-1 / 2-16-1 Tokiwa-dai, Ube, Yamaguchi 755-8611
[アクセス](https://www.nii.ac.jp/about/access/) / [Access](https://www.nii.ac.jp/en/about/access/)
-->

## 懇親会 / Dinner Party
- 日時: 11/16 18:30～ / Time: 16th Mon. 18:30～
- 会場 / Place: オンライン(Zoom)


## 幹事 / Organizer

中正和久 (山口大学工学部) /
Kazuhisa NAKASHO (Faculty of Engineering, Yamaguchi University)

Email: nakasho&lt;at&gt;yamaguchi-u.ac.jp

## 参加申し込み / Registration
11/11(水)までに / Please register by 11th November from

<span style="font-size:150%">
[こちらから / here](https://docs.google.com/forms/d/e/1FAIpQLSceNfw0KZRPFjw9FMe2m5NJ3RGDCnJOtYbJgxktdOl4RxWQdA/viewform)
</span>

## プログラム / Technical Program
TBA

<!--
### Nov. 18
### Nov. 19
-->

## TPPmark 
※ <span style="color: red">(modified at 20:10, Sep. 28th, 2020)</span>

SAT/SMTソルバで解を探索するような問題にしてみました．それぞれ手証明も可能です．回答は nakasho <at> yamaguchi-u.ac.jp まで送付をお願いします．

I made problems to find the solutions using SAT/SMT solvers. You can also prove them without solvers. Please send your answer to nakasho <at> yamaguchi-u.ac.jp.

### 問1.
124本のベクトルからなる集合 X = {(x,y,z) | x,y,z ∈ {0,±1,±√2}} \ {(0,0,0)} の各要素を白または黒に塗り分けることを考えます．
このとき，次の2条件 a), b) を満たすようにベクトルを白または黒に塗り分けることはできないことを証明してください． 
- a) 2つの直交するベクトルのうち，少なくとも1本は黒色である． 
- b) 互いに直交し合う3つのベクトルのうち，少なくとも1本は白色である． 

Consider painting each element of the set X = {(x,y,z) | x,y,z ∈ {0,±1,±√2}} \ {(0,0,0)} of 124 vectors white or black.
Prove that the vectors cannot be painted white or black in such a way that the following two conditions a) and b) are met. 
- a) Whenever two of the vectors are orthogonal, at least one is black. 
- b) Whenever three of the vectors are mutually orthogonal, at least one is white. 

### 問2. 
条件 c) を満たしつつ，条件 a) と b) の少なくとも一方は成り立たないように，ベクトルの集合 X からできるだけ多くの要素を減らしてください． （ヒント: 33本まで減らせることが知られています．）
- c) 集合内に互いに直交し合う3つのベクトルの集合が少なくとも1つは存在する．

Reduce as many elements as possible from the set of vectors X such that at least one of the conditions a) and b) does not hold while condition c) is satisfied. (Hint: It is known that you can reduce the number to 33.)
- c) There is at least one set of three mutually orthogonal vectors in the set. 

### 問3.
より一般的に n 次元 (n > 3) の場合に拡張してください．
このとき問題は，条件 c') を満たしつつ，条件 a) と b') の少なくとも一方は成り立たないように， n 次元ベクトルの集合を見つけることとなります．
- a) 2つの直交するベクトルのうち，少なくとも1本は黒色である． 
- b') 互いに直交し合うn本のベクトルのうち，少なくとも1本は白色である． 
- c') 集合内に互いに直交し合う n 個のベクトルの集合が少なくとも1つは存在する．

一般の場合はとても難しいです．特定の n (> 3) に対して，このようなベクトルの集合を構成する回答も歓迎します．

More generally, extend it to the case of n dimensions (n > 3). 
The problem is to find a set of n-dimensional vectors such that at least one of the conditions a) and b') does not hold while condition c') is satisfied.
- a) Whenever two of the vectors are orthogonal, at least one is black.
- b') Whenever n vectors are mutually orthogonal, at least one is white.
- c') There exists at least one set of n vectors in the set that are mutually orthogonal to each other.

The general case is very difficult. The constitution of such a set of vectors for a particular n (> 3) is also welcome.

### 解答 / Solutions
TBA

## これまでのTPP / Past TPPs
[TPP2019](https://akihisayamada.github.io/tpp2019/) /
[TPP2018](https://ksk.github.io/tpp2018/) /
[TPP2017](https://aigarashi.github.io/TPP2017/) /
[TPP2016](http://pllab.is.ocha.ac.jp/~asai/tpp2016/) /
[TPP2015](https://sites.google.com/a/progsci.info.kanagawa-u.ac.jp/tpp2015/) /
[TPP2014](http://imi.kyushu-u.ac.jp/lasm/tpp2014/) /
[TPP2013](http://shirodanuki.cs.shinshu-u.ac.jp/TPP/) /
[TPP2012](http://www.math.s.chiba-u.ac.jp/tpp2012/) /
[TPP2011](http://staff.aist.go.jp/reynald.affeldt/tpp2011/) /
[TPP2010](http://www.math.nagoya-u.ac.jp/~garrigue/tpp10/) /
[TPP2009](http://ist.ksc.kwansei.ac.jp/~ktaka/TPP09/TPP09.html) /
[TPP2008](http://www.score.cs.tsukuba.ac.jp/~minamide/tpp/) /
[TPP2007](http://www.score.cs.tsukuba.ac.jp/~minamide/tpp/tpp07/index.html) /
[TPP2006](http://www.jaist.ac.jp/joint-workshop/TPSmeeting/2006_11/program.html) /
[TPP2005](http://www.jaist.ac.jp/joint-workshop/TPSmeeting/2005_11/program.html)

