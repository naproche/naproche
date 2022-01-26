section \<open>Some rudiments of ZFC\<close>

text \<open>See also \<^url>\<open>https://www.isa-afp.org/entries/ZFC_in_HOL.html\<close> by L.C. Paulson.\<close>

theory ZFC_Rudiments
  imports Main
begin

typedecl V

axiomatization elts :: "V \<Rightarrow> V set"
 where ext [intro?]:    "elts x = elts y \<Longrightarrow> x=y"
   and down_raw:        "Y \<subseteq> elts x \<Longrightarrow> Y \<in> range elts"
   and Union_raw:       "X \<in> range elts \<Longrightarrow> Union (elts ` X) \<in> range elts"
   and Pow_raw:         "X \<in> range elts \<Longrightarrow> inv elts ` Pow X \<in> range elts"
   and replacement_raw: "X \<in> range elts \<Longrightarrow> f ` X \<in> range elts"
   and inf_raw:         "range (g :: nat \<Rightarrow> V) \<in> range elts"
   and foundation:      "wf {(x,y). x \<in> elts y}"

definition small :: "'a set \<Rightarrow> bool" 
  where "small X \<equiv> \<exists>V_of :: 'a \<Rightarrow> V. inj_on V_of X \<and> V_of ` X \<in> range elts"

definition set :: "V set \<Rightarrow> V"
  where "set X \<equiv> (if small X then inv elts X else inv elts {})"

definition VPow :: "V \<Rightarrow> V"
  where "VPow x = set (set ` Pow (elts x))"

definition vpair :: "V \<Rightarrow> V \<Rightarrow> V"
  where "vpair a b = set {set {a},set {a,b}}"

definition vfst :: "V \<Rightarrow> V"
  where "vfst p = (THE x. \<exists>y. p = vpair x y)"

definition vsnd :: "V \<Rightarrow> V"
  where "vsnd p = (THE y. \<exists>x. p = vpair x y)"

definition VSigma :: "V \<Rightarrow> (V \<Rightarrow> V) \<Rightarrow> V"
  where "VSigma A B = set(\<Union>x \<in> elts A. \<Union>y \<in> elts (B x). {vpair x y})"

abbreviation vtimes :: "V \<Rightarrow> V \<Rightarrow> V"
  where "vtimes A B \<equiv> VSigma A (\<lambda>x. B)"

definition pairs :: "V \<Rightarrow> (V \<times> V) set"
  where "pairs r = {(x,y). vpair x y \<in> elts r}"

definition VLambda :: "V \<Rightarrow> (V \<Rightarrow> V) \<Rightarrow> V"
  where "VLambda A b = set ((\<lambda>x. vpair x (b x)) ` elts A)"

definition app :: "V \<Rightarrow> V \<Rightarrow> V"
  where "app f x \<equiv> THE y. vpair x y \<in> elts f"

definition VPi :: "V \<Rightarrow> (V \<Rightarrow> V) \<Rightarrow> V"
  where "VPi A B =
    set {f \<in> elts (VPow (VSigma A B)). elts A \<subseteq> Domain (pairs f) \<and> single_valued (pairs f)}"

end
