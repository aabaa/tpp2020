From mathcomp Require Import all_ssreflect.
Require Import ZArith.

Set Implicit Arguments.

(* Represent a + b sqrt(2) as a pair of integers *)
Definition K : Set := Z * Z.

(* Add a decidable equality structure to Z *)
Lemma Zeq_boolP : Equality.axiom Zeq_bool.
Proof.
move=> x y.
by apply: (iffP idP) => /Zeq_is_eq_bool.
Qed.

Definition Zeq_mixin := EqMixin Zeq_boolP.
Canonical Z_eqType := Eval hnf in EqType _ Zeq_mixin.

(* Addition and multiplication on K *)
Definition addK (a b : K) : K := (a.1 + b.1, a.2 + b.2)%Z.
Definition mulK (a b : K) : K :=
  (a.1 * b.1 + a.2 * b.2 * 2, a.1 * b.2 + a.2 * b.1)%Z.

(* 3-dimensional vectors *)
Definition K3 : Set := K * K * K.

Definition scalar (k1 k2 : K3) : K :=
  let '(x1,y1,z1) := k1 in
  let '(x2,y2,z2) := k2 in
  addK (mulK x1 x2) (addK (mulK y1 y2) (mulK z1 z2)).

Module Scalar.
(* Our encoding really corresponds to the scalar product in R3 *)
Require Import Reals Field.
Open Scope R_scope.

Definition IKR (a : K) := IZR a.1 + IZR a.2 * sqrt (IZR 2).

Lemma addKE (a b : K) : IKR (addK a b) = IKR a + IKR b.
Proof. rewrite /IKR /addK /= !plus_IZR. field. Qed.

Lemma mulKE (a b : K) : IKR (mulK a b) = IKR a * IKR b.
Proof.
rewrite /IKR /mulK !(plus_IZR,mult_IZR) -[in _ * IZR 2](sqrt_def (IZR 2)).
  field.
auto with real.
Qed.

Lemma scalarE (v w : K3) :
  let: (x1,y1,z1) := v in let: (x2,y2,z2) := w in
  IKR (scalar v w) = IKR x1 * IKR x2 + IKR y1 * IKR y2 + IKR z1 * IKR z2.
Proof.
case: v => [[x1 y1] z1].
case: w => [[x2 y2] z2].
rewrite /scalar !(addKE,mulKE).
field.
Qed.
End Scalar.

(* A finite type representation for our vectors *)
Definition K0 := option (bool * bool).
Definition K0toK (a : K0) : K :=
  match a with
  | None => (0, 0)
  | Some (s, v) =>
    let x := if s then 1 else -1 in
    if v then (x, 0) else (0, x)
  end%Z.

Definition vals := [:: (0,0); (1,0); (0,1); (-1,0); (0,-1)]%Z.

Lemma vals_ok : vals = map K0toK (enum [set: K0]).
Proof.
rewrite /vals enum_setT Finite.EnumDef.enumDef /=.
rewrite Finite.EnumDef.enumDef /=.
rewrite /prod_enum enumT.
by rewrite !Finite.EnumDef.enumDef.
Qed.

Section flat_map.
Variables A B : eqType.
Variable f : A -> seq B.
Definition flat_map l := flatten (map f l).

Lemma flat_map_cat l1 l2 : flat_map (l1 ++ l2) = flat_map l1 ++ flat_map l2.
Proof. by rewrite /flat_map map_cat flatten_cat. Qed.
End flat_map.
Arguments flat_map {A B}.
Notation "l >>= f" := (flat_map f l) (at level 49).

Definition vecs : seq K3 :=
  [seq (xy,z) | xy <- [seq (x,y) | x <- vals, y <- vals], z <- vals].

Lemma uniq_vals : uniq vals.
Proof. done. Qed.

Lemma uniq_vecs : uniq vecs.
Proof.
have uv := uniq_vals.
apply allpairs_uniq => //.
move=> [x y] [x' y'].
move=> /allpairsP [p] [] Hx Hy [] xp1 xp2; subst.
by move=> /allpairsP [p'] [] Hx' Hy' [] xp1 xp2; subst.
Qed.

Definition K03 : Set := K0 * K0 * K0.
Definition K0toK3 (v : K03) : K3 :=
  let: (x,y,z) := v in (K0toK x, K0toK y, K0toK z).

Lemma vecs_ok : vecs =i map K0toK3 (enum [set: K03]).
Proof.
move=> v.
rewrite /vecs vals_ok.
case: mapP.
  case => -[[x y] z] Hv -> {v}.
  apply/flattenP.
    exists [seq (K0toK x, K0toK y, z)|z <- [seq K0toK i | i <- enum [set: K0]]].
    apply/mapP.
    exists (K0toK x, K0toK y) => //.
    apply/allpairsP.
    exists (K0toK x, K0toK y) => //=.
    by do !split; apply map_f; rewrite mem_enum in_setT.
  apply/mapP.
  exists (K0toK z) => //.
  apply map_f.
  by rewrite mem_enum in_setT.
move=> Hv; apply/negP => Hv'.
elim: Hv.
case/flattenP: Hv' => s /mapP [] x /allpairsP [] xy [] /mapP [x0] _ ->.
case/mapP => y0 _ -> -> -> {x s} /mapP [z] /mapP [z0] _ -> -> {v z}.
exists (x0, y0, z0) => //.
by rewrite mem_enum in_setT.
Qed.

Lemma K0toK_inj : injective K0toK.
Proof. by move => [[[] []]|] [[[] []]|]. Qed.

Lemma K0toK3_inj : injective K0toK3.
Proof.
move=> [[x y] z] [[x' y'] z'] /= [] /K0toK_inj -> /K0toK_inj -> /K0toK_inj ->.
done.
Qed.

(* Prove that we are using the right set of vectors *)
Lemma vecs_ok' :
  behead vecs =i map K0toK3 (enum ([set: K03] :\ (None,None,None))).
Proof.
have -> : behead vecs = rem ((0,0),(0,0),(0,0))%Z vecs by [].
move=> v.
rewrite (mem_rem_uniq _ uniq_vecs).
rewrite inE /= vecs_ok.
case Hv: (v == _) => /=.
  symmetry; apply/mapP => -[v0].
  rewrite mem_enum inE inE => /andP [v0n] _ vv0.
  subst.
  elim: (negP v0n).
  apply/eqP/K0toK3_inj.
  by rewrite (eqP Hv).
case: mapP.
  move=> [v0] _ Hv'.
  apply/esym/mapP.
  exists v0 => //.
  rewrite mem_enum !inE andbT.
  apply/negP => /eqP Hv0.
  by rewrite Hv' (f_equal K0toK3 Hv0) eqxx in Hv.
move=> Hv'.
apply/esym/negP => /mapP [v0].
rewrite mem_enum !inE andbT => Hv0 Hv''.
elim: Hv'.
exists v0 => //.
by rewrite mem_enum in_setT.
Qed.

(* Reduce the number of vectors by removing parallel ones 124 -> 49 *)
Definition reducible (k : K3) :=
  match k with
  | ((0,_),(0,_),(0,_)) | ((-1,_),_,_)
  | ((0,_),(-1,_),_)    | ((0,_),(0,_),(-1,_)) => true
  | _ => false
  end%Z.
Definition vertices := [seq k <- behead vecs | ~~ reducible k]%Z.

Definition defK3 := ((1,0),(1,0),(1,0))%Z.
Definition getv n := nth defK3 vertices n.
Definition indices := iota 0 (size vertices).

(* Represent the orthogonality relation as a list of list of indices *)
Definition orthogonal k1 k2 :=
  scalar k1 k2 == (0,0)%Z.
Definition edges :=
  [seq [seq orthogonal (getv i) (getv j) | j <- indices] | i <- indices].
Definition edge k1 k2 := nth false (nth [::] edges k1) k2.

Lemma edgeE i j :
  i < size indices -> j < size indices ->
  edge i j = orthogonal (getv i) (getv j).
Proof.
rewrite /edge /edges => isz jsz.
rewrite (@nth_map _ 0) // (@nth_map _ 0) //.
by rewrite !nth_iota.
Qed.

Definition color := option bool.
Definition black : color := Some false.
Definition white : color := Some true.

(* Definition of a good coloring *)
Definition good_coloring (vectors : seq K3) (coloring : K3 -> color) :=
  (forall v, v \in vectors -> coloring v != None) /\
  (forall v w, v \in vectors -> w \in vectors -> orthogonal v w ->
     black \in map coloring [:: v; w]) /\
  (forall v w u, v \in vectors -> w \in vectors -> u \in vectors ->
     orthogonal v w -> orthogonal v u -> orthogonal w u ->
     white \in map coloring [:: v; w; u]).

Lemma vertices_sub (v : K3) : v \in vertices -> v \in behead vecs.
Proof. by rewrite mem_filter => /andP[_]. Qed.

Definition KtoK0 (x : K) : K0 :=
  match x with
  | (1,0) => Some (true, true)
  | (-1,0) => Some (false, true)
  | (0,1) => Some (true, false)
  | (0,-1) => Some (false, false)
  | _ => None
  end%Z.

Definition K3toK0 (v : K3) : K03 :=
  let: (x,y,z) := v in (KtoK0 x, KtoK0 y, KtoK0 z).

Lemma cancelKtoK0 : cancel K0toK KtoK0.
Proof. by case=> [[[] []]|]. Qed.

Definition scale (k : K3) :=
  match k with
  | ((0,x),(0,y),(0,z)) => ((x,0),(y,0),(z,0))
  | _ => k
  end%Z.

Definition negK (k : K) : K :=
  let: (x,y) := k in (-x,-y)%Z.

Definition negK3 (v : K3) : K3 :=
  let: (x,y,z) := v in (negK x, negK y, negK z).

Definition reduce (k : K3) :=
  let k := scale k in
  match k with
  | ((-1,_),_,_)
  | ((0,_),(-1,_),_)
  | ((0,_),(0,_),(-1,_)) => negK3 k
  | _ => k
  end%Z.

Lemma reduce_sub (v : K3) : v \in behead vecs -> (reduce v \in vertices).
Proof.
rewrite /vertices vecs_ok' => /mapP [v0].
rewrite mem_enum 3!inE andbT => Hv0 -> {v}.
rewrite mem_filter vecs_ok'.
apply/andP; split.
  by case: v0 Hv0 => -[] [[[] []]|] //= [[[] []]|] //= [[[] []]|].
apply/mapP.
exists (K3toK0 (reduce (K0toK3 v0))).
  rewrite mem_enum !inE andbT.
  by case: v0 Hv0 => -[] [[[] []]|] //= [[[] []]|] //= [[[] []]|].
by case: v0 Hv0 => -[] [[[] []]|] //= [[[] []]|] //= [[[] []]|].
Qed.

Lemma reduce_ortho_l v w : orthogonal v w -> orthogonal (reduce v) w.
Proof.
rewrite /reduce => Hvw.
have Hsvw: orthogonal (scale v) w.
  rewrite /scale.
  case: v Hvw => [[[[|x1|x1] x2] // [[|y1|y1] y2]] // [[|z1|z1] z2]] //.
  case: w => [[[x1' x2'] [y1' y2']] [z1' z2']].
  rewrite /orthogonal /scalar /addK /mulK /= => /eqP [] Ho1 Ho2.
  rewrite !Z.add_0_r Ho2.
  apply/eqP; congr pair.
  move: Ho1.
  by rewrite -!Z.mul_add_distr_r => /Z.mul_eq_0_l ->.
have : orthogonal (negK3 (scale v)) w.
  move: Hsvw.
  rewrite /negK3.
  case: (scale v) => -[[x1 x2] [y1 y2]] [z1 z2] /=.
  case: w {Hvw} => [[[x1' x2'] [y1' y2']] [z1' z2']].
  rewrite /orthogonal /scalar /addK /mulK /= => /eqP [] Ho1 Ho2.
  by rewrite !Z.mul_opp_l -!Z.opp_add_distr Ho1 Ho2.
move: Hsvw {Hvw}.
case: (scale v) => -[] [[|x1|x1] x2] //=.
  case=> -[|y1|y1] y2 //=.
    case=> -[|z1|z1] z2 //.
    by case: z1.
  by case: y1.
by case: x1.
Qed.

Lemma mulKC a b : mulK a b = mulK b a.
Proof.
case: a b => [a1 a2] [b1 b2].
rewrite /mulK /=.
by rewrite !(Z.mul_comm b1) !(Z.mul_comm b2) (Z.add_comm (a2 * b1)).
Qed.

Lemma orthogonalC v w : orthogonal v w = orthogonal w v.
Proof.
rewrite /orthogonal /scalar.
case: v => -[x1 y1] z1.
case: w => -[x2 y2] z2.
by rewrite (mulKC x2) (mulKC y2) (mulKC z2).
Qed.

Lemma reduce_ortho v w : orthogonal v w -> orthogonal (reduce v) (reduce w).
Proof.
move=> Hvw.
apply reduce_ortho_l.
rewrite orthogonalC.
apply reduce_ortho_l.
by rewrite orthogonalC.
Qed.

(* Proof that reduction does not change colorabillity *)
Lemma reduction_ok :
  (exists coloring, good_coloring (behead vecs) coloring) <->
  (exists coloring, good_coloring vertices coloring).
Proof.
split => -[coloring] []; rewrite -/K3 => ok1 [ok2 ok3].
- exists coloring.
  do !split; rewrite /= -/K3.
  + by move=> v /vertices_sub /ok1.
  + move=> v w /vertices_sub Hv /vertices_sub; exact: ok2.
  + move=> v w u /vertices_sub Hv /vertices_sub Hw /vertices_sub; exact: ok3.
- exists (coloring \o reduce).
  do !split.
  + by move=> v /reduce_sub /ok1.
  + move=> v w /reduce_sub Hv /reduce_sub Hw /reduce_ortho; exact: ok2.
  + move=> v w u /reduce_sub Hv /reduce_sub Hw /reduce_sub Hu.
    move/reduce_ortho => Hvw /reduce_ortho Hvu /reduce_ortho; exact: ok3.
Qed.


(* Algorithm searching for a good coloring *)

Definition check_triangles (v : nat) (coloring : seq color) :=
  let getc := nth None coloring in
  let c := getc v in
  let orth := [seq w <- indices | edge v w] in
  (c != None) &&
  if c == white then white \notin map getc orth else
  ~~ has (fun w => (getc w == c) &&
            has (fun t => edge w t && (getc t == c)) orth)
         orth.

Definition filterM {A} (f : A -> bool) (x : A) : seq A :=
  if f x then [:: x] else [::].

Definition set (coloring : seq color) := set_nth None coloring.

Definition uncolored : seq color := [::].

Fixpoint color_vertices rem coloring :=
  match rem with
  | nil => [:: coloring]
  | v :: rem =>
    [:: set coloring v black; set coloring v white]
    >>= filterM (check_triangles v)
    >>= color_vertices rem
  end.

(* Computation checking the absence of good colorings *)
Lemma no_coloring : color_vertices indices uncolored = [::].
Proof. by vm_compute. Qed.


(* Proof that the algorithm is correct *)

Lemma take_diff_index {A : eqType} v (v0 : A) (s : seq A) :
  v0 \in take v.+1 s -> v0 \notin take v s -> index v0 s = v.
Proof.
move=> Hv0 Hv0'.
move: (index_cat v0 (take v s) (drop v s)).
rewrite (negbTE Hv0') cat_take_drop => ->.
move: Hv0.
rewrite -addn1 takeD mem_cat (negbTE Hv0') size_take /=.
case: ifPn => Hsz.
  case: (drop _ _) => //= a l.
  rewrite take0 inE => /eqP ->.
  by rewrite eqxx addn0.
by rewrite drop_oversize // leqNgt.
Qed.

Lemma getv_index v : v \in vertices -> getv (index v vertices) = v.
Proof. move=> Hv; by rewrite /getv nth_index. Qed.

Lemma index_vertices v : v \in vertices -> index v vertices \in indices.
Proof. move=> Hv; by rewrite mem_iota leq0n add0n index_mem. Qed.

Lemma index_orthogonal v w :
  v \in vertices -> w \in vertices ->
  index w vertices \in filter (edge (index v vertices)) indices =
  orthogonal v w.
Proof.
move=> Hv Hw; rewrite mem_filter edgeE ?index_mem // !getv_index //.
by rewrite index_vertices // andbT.
Qed.

Lemma color_other {c : color} {b} : c != None -> c != Some b -> c = Some (~~ b).
Proof. by case: c b => -[] []. Qed.

Lemma getv_take v n :
  n < size vertices -> v < n.+1 -> getv v \in take n.+1 vertices.
Proof.
move=> Hn Hv.
by rewrite /getv -(nth_take defK3 (n0:=n.+1) (i:=v)) // mem_nth // size_takel.
Qed.

Lemma check_triangles_ok n (coloring : seq color) :
  let colorf k := nth None coloring (index k vertices) in
  good_coloring (take n vertices) colorf ->
  (forall i, i > n -> nth None coloring i = None) ->
  n < size vertices ->
  reflect (good_coloring (take n.+1 vertices) colorf)
          (check_triangles n coloring).
Proof.
move=> colorf [ok1 [ok2 ok3]] Hnone Hnsz.
case/boolP: (check_triangles n _) => Hch; constructor.
  case/andP: Hch => Hch1 Hch.
  do !split.
  - move=> v Hv.
    case/boolP: (v \in take n vertices) => Hv'.
      exact: ok1.
    by rewrite /colorf (take_diff_index n).
  - move=> v w Hv Hw.
    case/boolP: ((v \in take n vertices) && (w \in take n vertices)).
      case/andP=> Hv' Hw'.
      exact: ok2.
    rewrite negb_and.
    move: Hv Hw.
    wlog: v w / (v \notin take n vertices).
      move=> Hwl Hv Hw /orP [] Hnv Ho.
        apply Hwl => //.
        by rewrite Hnv.
      have: black \in [seq colorf i | i <- [:: w; v]].
        apply Hwl => //.
          by rewrite Hnv.
        by rewrite orthogonalC.
      by rewrite !inE orbC.
    move=> Hvn Hv Hw _ Ho.
    rewrite !inE.
    have Hi := take_diff_index _ _ _ Hv Hvn.
    move: (Hv) (Hw) Hch => /mem_take Hv' /mem_take Hw'.
    case: ifPn => Hwh.
      case/boolP: (black == colorf w) => Hcw.
        by rewrite orbT.
      move/mapP; elim.
      exists (index w vertices).
        rewrite mem_filter -Hi edgeE ?index_mem // !getv_index //.
        by rewrite Ho index_vertices.
      case/boolP: (w \in take n vertices) => Hwn.
        rewrite eq_sym in Hcw.
        by rewrite -/(colorf w) (color_other (ok1 w Hwn) Hcw).
      by rewrite (take_diff_index n) // (eqP Hwh).
    move=> _.
    by rewrite /colorf Hi (color_other Hch1 Hwh).
  - move=> v w u Hv Hw Hu.
    case/boolP: ((v \in take n vertices) && (w \in take n vertices)
                 && (u \in take n vertices)).
      case/andP => /andP[] Hv' Hw' Hu'.
      exact: ok3.
    rewrite !negb_and.
    move: Hv Hw Hu.
    wlog: v w u / (v \notin take n vertices).
      move=> Hwl Hv Hw Hu /orP [/orP []|] Hnv Hvw Hvu Hwu.
          apply Hwl => //.
          by rewrite Hnv.
        have: white \in [seq colorf i | i <- [:: w; v; u]].
          apply Hwl => //.
            by rewrite Hnv.
          by rewrite orthogonalC.
        by rewrite !inE !orbA (orbC (_ == colorf w)).
      have: white \in [seq colorf i | i <- [:: u; v; w]].
        apply Hwl => //; by rewrite (Hnv,orthogonalC).
      by rewrite !inE orbC !orbA.
    move=> Hvn Hv Hw Hu _ Hvw Hvu Hwu.
    rewrite !inE !(eq_sym white).
    have Hn := take_diff_index _ _ _ Hv Hvn.
    move: Hch.
    case: ifPn => Hwh.
      by rewrite /colorf Hn Hwh.
    rewrite /(colorf v) Hn (color_other Hch1 Hwh) [_ || _]/=.
    case/boolP: (colorf w == white) => Hcw //.
    case/boolP: (colorf u == white) => Hcu //.
    move/negP; elim.
    apply/hasP.
    move/mem_take in Hv.
    move/mem_take: (Hw) => Hw'.
    move/mem_take: (Hu) => Hu'.
    exists (index w vertices).
      by rewrite -Hn index_orthogonal.
    apply/andP; split.
      case/boolP: (w \in take n vertices) => Hwn.
        by rewrite -/(colorf w) (color_other (ok1 w Hwn) Hcw).
      by rewrite (take_diff_index n) // (color_other Hch1 Hwh).
    apply/hasP.
    exists (index u vertices).
      by rewrite -Hn index_orthogonal.
    rewrite edgeE ?index_mem // !getv_index // Hwu.
    case/boolP: (u \in take n vertices) => Hun.
      by rewrite -/(colorf u) (color_other (ok1 u Hun) Hcu).
    by rewrite (take_diff_index n) // (color_other Hch1 Hwh).
move=> Hgc.
move/negP: Hch; elim.
case: Hgc => {}ok1 [{}ok2 {}ok3].
rewrite /check_triangles.
case: ifPn => Hwh.
  rewrite (eqP Hwh) [~~ _]/=.
  apply/mapP => -[m] Hm Hcm.
  have Hmn1: m < n.+1.
    rewrite ltnNge; apply/negP => Hmn.
    by move: (Hnone _ Hmn); rewrite -Hcm.
  move: Hm; rewrite mem_filter => /andP[].
  have Hmsz : m < size indices.
    exact: (leq_trans Hmn1).
  rewrite edgeE // => /ok2.
  rewrite size_iota in Hmsz.
  rewrite !getv_take // 2!inE /colorf !index_uniq // => /(_ isT isT).
  by rewrite (eqP Hwh) -Hcm.
case/boolP: (nth None coloring n == black) => /eqP Hbk.
  rewrite Hbk andTb.
  apply/hasP => -[w] Hw' /andP[] /eqP Hcw /hasP [u] Hu' /andP[] Hwu /eqP Hcu.
  move: Hw' Hu'.
  rewrite !mem_filter => /andP[].
  have Hwn: w < n.+1.
    rewrite ltnNge; apply/negP => Hmn.
    by move: (Hnone _ Hmn); rewrite Hcw.
  have Hun: u < n.+1.
    rewrite ltnNge; apply/negP => Hmn.
    by move: (Hnone _ Hmn); rewrite Hcu.
  have Hwsz : w < size indices by exact: (leq_trans Hwn).
  have Husz : u < size indices by exact: (leq_trans Hun).
  rewrite !edgeE // => Hvw _ /andP[] Hvu _.
  rewrite edgeE // in Hwu.
  rewrite size_iota in Hwsz Husz.
  move/(ok3 _ _ (getv u)): Hvw.
  rewrite Hvu Hwu !getv_take // 3!inE; do !move/(_ isT).
  by rewrite /colorf !index_uniq // Hbk Hcw Hcu.
move: (ok1 (getv n)).
rewrite getv_take // => /(_ isT).
rewrite /colorf index_uniq // => Hn.
elim Hbk; by rewrite (color_other Hn Hwh).
Qed.

Definition le_coloring (col1 col2 : K3 -> color) :=
  forall v, col1 v = None \/ col1 v = col2 v.

Lemma flat_map_amb {A B : eqType} f (a1 a2 : A) (b : B) :
  b \in ([:: a1; a2] >>= f) = (b \in f a1) || (b \in f a2).
Proof.
apply/flattenP; case: ifP.
  case/orP => Hb ; [exists (f a1) | exists (f a2)];
    by rewrite // map_f // !inE eqxx // orbT.
move=> Hb [s].
rewrite !inE => /orP [] /eqP -> Hb'; by rewrite Hb' // orbT in Hb.
Qed.

Lemma flat_map_comp {A B C : eqType} (f1 : A -> seq B) (f2 : B -> seq C) s :
  (s >>= f1) >>= f2 = s >>= (flat_map f2 \o f1).
Proof.
rewrite /flat_map /comp.
elim: s => //= a s IH.
by rewrite map_cat flatten_cat IH.
Qed.

Lemma color_vertices_mono n (coloring coloring' : seq color) :
  n <= size vertices ->
  coloring' \in color_vertices (iota n (size vertices - n)) coloring ->
  forall i, i < n -> nth None coloring i = nth None coloring' i.
Proof.
move=> Hsz.
rewrite -{1 3}(subKn Hsz).
have : size vertices - n <= size vertices by rewrite leq_subr.
elim: (size vertices - n) {Hsz} coloring => [|{}n IH] coloring Hn /=.
  by rewrite inE => /eqP ->.
rewrite {2}/flat_map /= /filterM.
rewrite subnS (@ltn_predK 0); last by rewrite subn_gt0.
set set_coloring := set _ _.
have {}IH : forall b,
    coloring' \in color_vertices (iota (49 - n) n) (set_coloring b) ->
    forall i, i < (49 - n).-1 -> nth None coloring i = nth None coloring' i.
  move=> b Hcol i Hi.
  transitivity (nth None (set_coloring b) i).
    by rewrite nth_set_nth /= ltn_eqF.
  apply IH. exact: ltnW. exact: Hcol.
  apply: (leq_trans Hi).
  exact: leq_pred.
case: (check_triangles _ _); case: (check_triangles _ _); rewrite !cats0 /=.
      rewrite flat_map_amb => /orP[]; exact: IH.
    rewrite /flat_map /= cats0; exact: IH.
  rewrite /flat_map /= cats0; exact: IH.
done.
Qed.

Lemma good_coloring_eq vertices (coloring coloring' : K3 -> color) :
  {in vertices, coloring =1 coloring'} ->
  good_coloring vertices coloring -> good_coloring vertices coloring'.
Proof.
move=> Hcol [ok1] [ok2 ok3].
do! split.
- by move=> v Hv; rewrite -Hcol // ok1.
- move=> v w Hv Hw /(ok2 _ _ Hv Hw). by rewrite !inE !Hcol.
- move=> v w u Hv Hw Hu Hvw Hvu /(ok3 _ _ _ Hv Hw Hu).
  rewrite !inE !Hcol; exact.
Qed.

Lemma good_coloring_le n gc gc' :
  good_coloring vertices gc -> le_coloring gc' gc ->
  {in take n vertices, forall v, gc' v != None} ->
  good_coloring (take n vertices) gc'.
Proof.
case => ok1 [ok2 ok3] Hle Hnone.
do! split.
- by move=> v /Hnone.
- move=> v w Hv Hw.
  move/(ok2 _ _ (mem_take Hv) (mem_take Hw)).
  rewrite !inE.
  move/Hnone: Hv.
  move/Hnone: Hw.
  by case: (Hle v) (Hle w) => -> // [] ->.
- move=> v w u Hv Hw Hu Hvw Hvu.
  move/(ok3 _ _ _ (mem_take Hv) (mem_take Hw) (mem_take Hu) Hvw Hvu).
  rewrite !inE.
  move/Hnone: Hv.
  move/Hnone: Hw.
  move/Hnone: Hu.
  by case: (Hle v) (Hle w) (Hle u) => -> // [] -> // [] ->.
Qed.  

Lemma color_vertices_ok n coloring gc :
  n <= size vertices ->
  let colorf k := nth None coloring (index k vertices) in
  good_coloring (take n vertices) colorf ->
  le_coloring colorf gc ->
  {in vertices, forall v, gc v != None} ->
  size coloring = n ->
  reflect (good_coloring vertices gc)
          (map gc vertices \in
              color_vertices (iota n (size vertices - n)) coloring).
Proof.
move Hvertices: vertices => vertices.
move Hm: (size vertices - n) => m Hszn.
have -> : n = size vertices - m by rewrite -Hm subKn.
have : m <= size vertices by rewrite -Hm leq_subr.
elim: m {n Hm Hszn} coloring => [|m IH] coloring Hszm colorf.
  rewrite subn0 take_size [color_vertices _ _]/=.
  case=> ok1 [ok2 ok3] Hle Hnone Hsz.
  have Hcol: {in vertices, colorf =1 gc}.
    move=> v Hv.
    move: (ok1 v).
    case: (Hle v) => // ->.
    by rewrite Hv eqxx => /(_ isT).
  have -> : map gc vertices = coloring.
    apply: (eq_from_nth (x0:=None)).
      by rewrite size_map.
    move=> i.
    rewrite size_map => Hi.
    rewrite -(proj1 (eq_in_map _ _ _) Hcol) /colorf.
    by rewrite (nth_map defK3) // /colorf /getv index_uniq // -Hvertices.
  rewrite inE eqxx.
  constructor.
  do! split.
  + move=> v Hc.
    rewrite -Hcol //.
    exact: ok1.
  + move=> v w Hv Hw.
    move: (ok2 v w Hv Hw).
    by rewrite !inE !Hcol.
  + move=> v w u Hv Hw Hu.
    move: (ok3 v w u Hv Hw Hu).
    by rewrite !inE !Hcol.
move=> Hgc Hle Hnone Hsz /=.
rewrite [in _.+1]subnS (@ltn_predK 0) ?subn_gt0 //.
rewrite {2}/flat_map /= cats0.
set n := size vertices - m.+1 in Hgc Hsz *.
set coloring' := set coloring n (gc (getv n)).
set colorf' := fun k => nth None coloring' (index k vertices).
have Hset : {in take n vertices,  colorf =1 colorf'}.
  move=> v Hv.
  rewrite /colorf /colorf' nth_set_nth /=.
  case: ifP => // /eqP.
  rewrite -{1}(cat_take_drop n vertices).
  rewrite index_cat Hv => Hv'.
  move: Hv.
  by rewrite -index_mem Hv' size_takel (ltnn,leq_subr).
rewrite /filterM flat_map_cat mem_cat.
have Htr : reflect (good_coloring (take n.+1 vertices) colorf')
                   (check_triangles n coloring').
  rewrite /colorf' -Hvertices.
  apply check_triangles_ok; rewrite ?Hvertices.
      by apply (good_coloring_eq Hset).
    move=> i Hi.
    rewrite nth_set_nth /= eq_sym ltn_eqF //.
    by rewrite nth_default // Hsz ltnW.
  by rewrite /n subnS prednK ?subn_gt0 // leq_subr.
have Hszn: n < size vertices.
  by rewrite /n ltn_subrL /= (leq_ltn_trans (leq0n m)).
have Hgcn : gc (getv n) \in [:: black; white].
  move: (Hnone (getv n)).
  rewrite !inE /getv Hvertices mem_nth // => /(_ isT).
  by case: (gc _) => // -[].
(* generalize colors *)
have: true = ~~false /\ gc (getv n) \in [:: black; white] by [].
rewrite /black /white.
generalize false true => blk wht.
wlog: blk wht / gc (getv n) = Some blk.
  case/boolP: (gc (getv n) == Some blk).
    move/eqP ->; exact.
  rewrite 2!inE => /negbTE -> /= H [].
  rewrite eq_sym orbC => Hbw /eqP Hgcn'.
  apply: H => //.
  rewrite !inE Hbw negbK -Hbw Hgcn' eqxx; by split.
move=> {}Hgcn [-> _] {wht}.
have Hszm': 0 < size vertices - m by rewrite ltn_subRL addn0.
rewrite orbC.
case/boolP: (_ \in _).
  case: ifP => Hch; last by rewrite in_nil.
  rewrite /flat_map /= cats0.
  rewrite -{2}(subKn (ltnW Hszm)) -{3}Hvertices => /color_vertices_mono.
  rewrite Hvertices leq_subr => /(_ isT n).
  rewrite /n subnS ltn_predL Hszm' nth_set_nth /= eqxx => /(_ isT).
  rewrite (nth_map defK3).
    rewrite -{1}Hvertices -subnS Hgcn; by destruct blk.
  by rewrite prednK ?leq_subr.
move=> _ /=.
have Hle': le_coloring colorf' gc.
  move=> v; rewrite /colorf' nth_set_nth /=.
  case: ifP => /eqP Hv; last by exact: Hle.
  move: Hgcn.
  rewrite -Hv -Hvertices getv_index.
    move ->; by right.
  by rewrite -index_mem Hvertices Hv.
case: ifP => Hch;
  rewrite /colorf' /coloring' Hgcn /n Hch [in _.+1]subnS prednK // in Htr.
  rewrite /flat_map /= cats0.
  apply IH => //.
        exact: ltnW.
      exact/Htr.
    by rewrite -Hgcn.
  rewrite size_set_nth /n subnS prednK //.
  apply/maxn_idPl.
  by rewrite Hsz /n subnS leq_pred.
rewrite in_nil.
constructor.
rewrite -Hvertices.
have Hnone': {in take (size vertices - m) vertices,
                 forall v, colorf' v != None}.
  move=> v Hv.
  rewrite /colorf' nth_set_nth /=.
  case: ifP => /eqP Hi.
    by rewrite Hgcn.
  apply: (proj1 Hgc).
  case/boolP: (_ \in _) => Hv' //.
  rewrite -(@prednK (_ - m)) // -subnS in Hv.
  by move: (take_diff_index _ _ _ Hv Hv') Hi => ->.
rewrite -{2}Hvertices in Hnone'.
move/(@good_coloring_le (size vertices - m) gc colorf') => /(_ Hle' Hnone').
by rewrite Hvertices /colorf' /coloring' Hgcn => /Htr.
Qed.

(* Answer to question 1 *)
Theorem no_vecs_coloring :
  ~ ex (good_coloring (behead vecs)).
Proof.
move/reduction_ok => [] gc Hgc.
apply/(@color_vertices_ok (locked 0) uncolored): (Hgc) => //.
- by rewrite -lock.
- rewrite -lock [take _ _]/=.
  do! split; move=> v; by rewrite in_nil.
- move=> v.
  rewrite nth_default //; by left.
- apply: (proj1 Hgc); by rewrite -lock.
- by rewrite -lock.
- by rewrite -lock subn0 no_coloring in_nil.
Qed.
