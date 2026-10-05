(** * Reachable frontier phases for the M block-list core.

    A 137-state automaton reads the finite right word and remembers the
    nearest eight left symbols. At B0 with an empty right word it permits
    exactly the frontier prefixes 01001 and 01101101. Coq checks every
    abstract step, every empty-right step, and the padded B0 reset.

    The conjunction with BlockCoreMReturnTr's boundary invariant admits
    positive marked B0 returns. It is reached after twelve blank steps.
    block_core_m_frontier.py reproduces the untrusted pushdown search;
    the finite certificate below is checked independently in the kernel.
*)
From Coq Require Import Arith Lia List Bool.
From BBB4 Require Import BBB4_Statement BBBT4_Statement CTape.
From BBB4.Counters Require Import WTape NestCountTr LoopRunTr BlockCoreMRankTr BlockCoreMReturnTr.
From BBB4.Checkers.IRules Require Import AnchorVisitsTr.
Import ListNotations.
Fixpoint ms_prefix(n:nat)(L:list Sym):list Sym:=match n with
|0=>[]|S n=>chd L::ms_prefix n(ctl L)end.
Fixpoint ms_words(n:nat):list(list Sym):=match n with
|0=>[[]]|S n=>map(cons S0)(ms_words n)++map(cons S1)(ms_words n)end.
Lemma ms_prefix_length:forall n L,length(ms_prefix n L)=n.
Proof. induction n;intro L;cbn;auto. Qed.
Lemma ms_words_complete:forall n L,length L=n->In L(ms_words n).
Proof. induction n;intros[|s L]E;try discriminate;[left;reflexivity|].
 injection E as E. cbn[ms_words];apply in_app_iff;destruct s;[left|right];apply in_map;apply IHn;exact E. Qed.
(* BEGIN GENERATED FINITE CERTIFICATE *)
Inductive ms_dfa:=MS0|MS1|MS2|MS3|MS4|MS5|MS6|MS7|MS8|MS9|MS10|MS11|MS12|MS13|MS14|MS15|MS16|MS17|MS18|MS19|MS20|MS21|MS22|MS23|MS24|MS25|MS26|MS27|MS28|MS29|MS30|MS31|MS32|MS33|MS34|MS35|MS36|MS37|MS38|MS39|MS40|MS41|MS42|MS43|MS44|MS45|MS46|MS47|MS48|MS49|MS50|MS51|MS52|MS53|MS54|MS55|MS56|MS57|MS58|MS59|MS60|MS61|MS62|MS63|MS64|MS65|MS66|MS67|MS68|MS69|MS70|MS71|MS72|MS73|MS74|MS75|MS76|MS77|MS78|MS79|MS80|MS81|MS82|MS83|MS84|MS85|MS86|MS87|MS88|MS89|MS90|MS91|MS92|MS93|MS94|MS95|MS96|MS97|MS98|MS99|MS100|MS101|MS102|MS103|MS104|MS105|MS106|MS107|MS108|MS109|MS110|MS111|MS112|MS113|MS114|MS115|MS116|MS117|MS118|MS119|MS120|MS121|MS122|MS123|MS124|MS125|MS126|MS127|MS128|MS129|MS130|MS131|MS132|MS133|MS134|MS135|MS136.
Definition ms_states:list ms_dfa:=[MS0;MS1;MS2;MS3;MS4;MS5;MS6;MS7;MS8;MS9;MS10;MS11;MS12;MS13;MS14;MS15;MS16;MS17;MS18;MS19;MS20;MS21;MS22;MS23;MS24;MS25;MS26;MS27;MS28;MS29;MS30;MS31;MS32;MS33;MS34;MS35;MS36;MS37;MS38;MS39;MS40;MS41;MS42;MS43;MS44;MS45;MS46;MS47;MS48;MS49;MS50;MS51;MS52;MS53;MS54;MS55;MS56;MS57;MS58;MS59;MS60;MS61;MS62;MS63;MS64;MS65;MS66;MS67;MS68;MS69;MS70;MS71;MS72;MS73;MS74;MS75;MS76;MS77;MS78;MS79;MS80;MS81;MS82;MS83;MS84;MS85;MS86;MS87;MS88;MS89;MS90;MS91;MS92;MS93;MS94;MS95;MS96;MS97;MS98;MS99;MS100;MS101;MS102;MS103;MS104;MS105;MS106;MS107;MS108;MS109;MS110;MS111;MS112;MS113;MS114;MS115;MS116;MS117;MS118;MS119;MS120;MS121;MS122;MS123;MS124;MS125;MS126;MS127;MS128;MS129;MS130;MS131;MS132;MS133;MS134;MS135;MS136].
Lemma ms_states_complete:forall s,In s ms_states.
Proof. intro s;destruct s;vm_compute;tauto. Qed.
Inductive ms_tree:=ms_leaf(bool_value:bool)|ms_node(left right:ms_tree).
Fixpoint ms_eval(t:ms_tree)(L:list Sym):bool:=match t with ms_leaf b=>b|ms_node l r=>match L with []=>false|S0::U=>ms_eval l U|S1::U=>ms_eval r U end end.
Definition ms_t0:ms_tree:=ms_leaf false.
Definition ms_t1:ms_tree:=ms_leaf true.
Definition ms_t2:ms_tree:=ms_node ms_t0 ms_t1.
Definition ms_t3:ms_tree:=ms_node ms_t2 ms_t0.
Definition ms_t4:ms_tree:=ms_node ms_t0 ms_t3.
Definition ms_t5:ms_tree:=ms_node ms_t0 ms_t4.
Definition ms_t6:ms_tree:=ms_node ms_t5 ms_t0.
Definition ms_t7:ms_tree:=ms_node ms_t3 ms_t6.
Definition ms_t8:ms_tree:=ms_node ms_t0 ms_t7.
Definition ms_t9:ms_tree:=ms_node ms_t1 ms_t0.
Definition ms_t10:ms_tree:=ms_node ms_t0 ms_t9.
Definition ms_t11:ms_tree:=ms_node ms_t0 ms_t10.
Definition ms_t12:ms_tree:=ms_node ms_t9 ms_t10.
Definition ms_t13:ms_tree:=ms_node ms_t1 ms_t12.
Definition ms_t14:ms_tree:=ms_node ms_t11 ms_t13.
Definition ms_t15:ms_tree:=ms_node ms_t4 ms_t14.
Definition ms_t16:ms_tree:=ms_node ms_t1 ms_t15.
Definition ms_t17:ms_tree:=ms_node ms_t16 ms_t16.
Definition ms_t18:ms_tree:=ms_node ms_t8 ms_t0.
Definition ms_t19:ms_tree:=ms_node ms_t11 ms_t9.
Definition ms_t20:ms_tree:=ms_node ms_t3 ms_t19.
Definition ms_t21:ms_tree:=ms_node ms_t1 ms_t20.
Definition ms_t22:ms_tree:=ms_node ms_t21 ms_t21.
Definition ms_t23:ms_tree:=ms_node ms_t1 ms_t22.
Definition ms_t24:ms_tree:=ms_node ms_t3 ms_t10.
Definition ms_t25:ms_tree:=ms_node ms_t9 ms_t0.
Definition ms_t26:ms_tree:=ms_node ms_t25 ms_t0.
Definition ms_t27:ms_tree:=ms_node ms_t24 ms_t26.
Definition ms_t28:ms_tree:=ms_node ms_t24 ms_t27.
Definition ms_t29:ms_tree:=ms_node ms_t20 ms_t28.
Definition ms_t30:ms_tree:=ms_node ms_t7 ms_t29.
Definition ms_t31:ms_tree:=ms_node ms_t7 ms_t30.
Definition ms_t32:ms_tree:=ms_node ms_t12 ms_t26.
Definition ms_t33:ms_tree:=ms_node ms_t24 ms_t32.
Definition ms_t34:ms_tree:=ms_node ms_t20 ms_t33.
Definition ms_t35:ms_tree:=ms_node ms_t20 ms_t34.
Definition ms_t36:ms_tree:=ms_node ms_t7 ms_t35.
Definition ms_t37:ms_tree:=ms_node ms_t1 ms_t11.
Definition ms_t38:ms_tree:=ms_node ms_t11 ms_t37.
Definition ms_t39:ms_tree:=ms_node ms_t3 ms_t38.
Definition ms_t40:ms_tree:=ms_node ms_t1 ms_t39.
Definition ms_t41:ms_tree:=ms_node ms_t40 ms_t40.
Definition ms_t42:ms_tree:=ms_node ms_t0 ms_t19.
Definition ms_t43:ms_tree:=ms_node ms_t1 ms_t42.
Definition ms_t44:ms_tree:=ms_node ms_t43 ms_t43.
Definition ms_t45:ms_tree:=ms_node ms_t2 ms_t44.
Definition ms_t46:ms_tree:=ms_node ms_t1 ms_t25.
Definition ms_t47:ms_tree:=ms_node ms_t25 ms_t9.
Definition ms_t48:ms_tree:=ms_node ms_t46 ms_t47.
Definition ms_t49:ms_tree:=ms_node ms_t1 ms_t48.
Definition ms_t50:ms_tree:=ms_node ms_t42 ms_t49.
Definition ms_t51:ms_tree:=ms_node ms_t4 ms_t50.
Definition ms_t52:ms_tree:=ms_node ms_t1 ms_t51.
Definition ms_t53:ms_tree:=ms_node ms_t12 ms_t32.
Definition ms_t54:ms_tree:=ms_node ms_t20 ms_t53.
Definition ms_t55:ms_tree:=ms_node ms_t20 ms_t54.
Definition ms_t56:ms_tree:=ms_node ms_t20 ms_t55.
Definition ms_t57:ms_tree:=ms_node ms_t13 ms_t10.
Definition ms_t58:ms_tree:=ms_node ms_t1 ms_t57.
Definition ms_t59:ms_tree:=ms_node ms_t0 ms_t58.
Definition ms_t60:ms_tree:=ms_node ms_t59 ms_t59.
Definition ms_t61:ms_tree:=ms_node ms_t13 ms_t47.
Definition ms_t62:ms_tree:=ms_node ms_t1 ms_t61.
Definition ms_t63:ms_tree:=ms_node ms_t42 ms_t62.
Definition ms_t64:ms_tree:=ms_node ms_t4 ms_t63.
Definition ms_t65:ms_tree:=ms_node ms_t0 ms_t38.
Definition ms_t66:ms_tree:=ms_node ms_t1 ms_t65.
Definition ms_t67:ms_tree:=ms_node ms_t66 ms_t66.
Definition ms_t68:ms_tree:=ms_node ms_t1 ms_t44.
Definition ms_t69:ms_tree:=ms_node ms_t0 ms_t47.
Definition ms_t70:ms_tree:=ms_node ms_t1 ms_t69.
Definition ms_t71:ms_tree:=ms_node ms_t42 ms_t70.
Definition ms_t72:ms_tree:=ms_node ms_t3 ms_t71.
Definition ms_t73:ms_tree:=ms_node ms_t1 ms_t72.
Definition ms_t74:ms_tree:=ms_node ms_t10 ms_t14.
Definition ms_t75:ms_tree:=ms_node ms_t1 ms_t74.
Definition ms_t76:ms_tree:=ms_node ms_t75 ms_t75.
Definition ms_t77:ms_tree:=ms_node ms_t9 ms_t19.
Definition ms_t78:ms_tree:=ms_node ms_t1 ms_t77.
Definition ms_t79:ms_tree:=ms_node ms_t78 ms_t78.
Definition ms_t80:ms_tree:=ms_node ms_t1 ms_t79.
Definition ms_t81:ms_tree:=ms_node ms_t77 ms_t53.
Definition ms_t82:ms_tree:=ms_node ms_t20 ms_t81.
Definition ms_t83:ms_tree:=ms_node ms_t20 ms_t82.
Definition ms_t84:ms_tree:=ms_node ms_t46 ms_t10.
Definition ms_t85:ms_tree:=ms_node ms_t1 ms_t84.
Definition ms_t86:ms_tree:=ms_node ms_t0 ms_t85.
Definition ms_t87:ms_tree:=ms_node ms_t86 ms_t86.
Definition ms_t88:ms_tree:=ms_node ms_t0 ms_t87.
Definition ms_t89:ms_tree:=ms_node ms_t25 ms_t37.
Definition ms_t90:ms_tree:=ms_node ms_t85 ms_t89.
Definition ms_t91:ms_tree:=ms_node ms_t1 ms_t90.
Definition ms_t92:ms_tree:=ms_node ms_t42 ms_t91.
Definition ms_t93:ms_tree:=ms_node ms_t1 ms_t87.
Definition ms_t94:ms_tree:=ms_node ms_t0 ms_t37.
Definition ms_t95:ms_tree:=ms_node ms_t85 ms_t94.
Definition ms_t96:ms_tree:=ms_node ms_t1 ms_t95.
Definition ms_t97:ms_tree:=ms_node ms_t0 ms_t96.
Definition ms_t98:ms_tree:=ms_node ms_t0 ms_t71.
Definition ms_t99:ms_tree:=ms_node ms_t1 ms_t98.
Definition ms_t100:ms_tree:=ms_node ms_t77 ms_t81.
Definition ms_t101:ms_tree:=ms_node ms_t20 ms_t100.
Definition ms_t102:ms_tree:=ms_node ms_t9 ms_t38.
Definition ms_t103:ms_tree:=ms_node ms_t1 ms_t102.
Definition ms_t104:ms_tree:=ms_node ms_t103 ms_t103.
Definition ms_t105:ms_tree:=ms_node ms_t10 ms_t50.
Definition ms_t106:ms_tree:=ms_node ms_t1 ms_t105.
Definition ms_t107:ms_tree:=ms_node ms_t0 ms_t25.
Definition ms_t108:ms_tree:=ms_node ms_t0 ms_t107.
Definition ms_t109:ms_tree:=ms_node ms_t10 ms_t108.
Definition ms_t110:ms_tree:=ms_node ms_t0 ms_t109.
Definition ms_t111:ms_tree:=ms_node ms_t110 ms_t110.
Definition ms_t112:ms_tree:=ms_node ms_t107 ms_t107.
Definition ms_t113:ms_tree:=ms_node ms_t0 ms_t112.
Definition ms_t114:ms_tree:=ms_node ms_t11 ms_t10.
Definition ms_t115:ms_tree:=ms_node ms_t1 ms_t114.
Definition ms_t116:ms_tree:=ms_node ms_t25 ms_t115.
Definition ms_t117:ms_tree:=ms_node ms_t85 ms_t116.
Definition ms_t118:ms_tree:=ms_node ms_t1 ms_t117.
Definition ms_t119:ms_tree:=ms_node ms_t0 ms_t115.
Definition ms_t120:ms_tree:=ms_node ms_t85 ms_t119.
Definition ms_t121:ms_tree:=ms_node ms_t1 ms_t120.
Definition ms_t122:ms_tree:=ms_node ms_t0 ms_t89.
Definition ms_t123:ms_tree:=ms_node ms_t1 ms_t122.
Definition ms_t124:ms_tree:=ms_node ms_t42 ms_t123.
Definition ms_t125:ms_tree:=ms_node ms_t77 ms_t100.
Definition ms_t126:ms_tree:=ms_node ms_t10 ms_t63.
Definition ms_t127:ms_tree:=ms_node ms_t11 ms_t47.
Definition ms_t128:ms_tree:=ms_node ms_t1 ms_t127.
Definition ms_t129:ms_tree:=ms_node ms_t42 ms_t128.
Definition ms_t130:ms_tree:=ms_node ms_t9 ms_t129.
Definition ms_t131:ms_tree:=ms_node ms_t1 ms_t130.
Definition ms_t132:ms_tree:=ms_node ms_t11 ms_t19.
Definition ms_t133:ms_tree:=ms_node ms_t1 ms_t132.
Definition ms_t134:ms_tree:=ms_node ms_t25 ms_t133.
Definition ms_t135:ms_tree:=ms_node ms_t85 ms_t134.
Definition ms_t136:ms_tree:=ms_node ms_t46 ms_t0.
Definition ms_t137:ms_tree:=ms_node ms_t0 ms_t136.
Definition ms_t138:ms_tree:=ms_node ms_t0 ms_t137.
Definition ms_t139:ms_tree:=ms_node ms_t10 ms_t138.
Definition ms_t140:ms_tree:=ms_node ms_t0 ms_t139.
Definition ms_t141:ms_tree:=ms_node ms_t0 ms_t44.
Definition ms_t142:ms_tree:=ms_node ms_t1 ms_t112.
Definition ms_t143:ms_tree:=ms_node ms_t0 ms_t26.
Definition ms_t144:ms_tree:=ms_node ms_t143 ms_t143.
Definition ms_t145:ms_tree:=ms_node ms_t25 ms_t10.
Definition ms_t146:ms_tree:=ms_node ms_t1 ms_t145.
Definition ms_t147:ms_tree:=ms_node ms_t11 ms_t146.
Definition ms_t148:ms_tree:=ms_node ms_t42 ms_t147.
Definition ms_t149:ms_tree:=ms_node ms_t1 ms_t148.
Definition ms_t150:ms_tree:=ms_node ms_t25 ms_t149.
Definition ms_t151:ms_tree:=ms_node ms_t13 ms_t0.
Definition ms_t152:ms_tree:=ms_node ms_t0 ms_t151.
Definition ms_t153:ms_tree:=ms_node ms_t0 ms_t152.
Definition ms_t154:ms_tree:=ms_node ms_t10 ms_t153.
Definition ms_t155:ms_tree:=ms_node ms_t11 ms_t0.
Definition ms_t156:ms_tree:=ms_node ms_t0 ms_t155.
Definition ms_t157:ms_tree:=ms_node ms_t0 ms_t156.
Definition ms_t158:ms_tree:=ms_node ms_t9 ms_t157.
Definition ms_t159:ms_tree:=ms_node ms_t0 ms_t158.
Definition ms_t160:ms_tree:=ms_node ms_t25 ms_t38.
Definition ms_t161:ms_tree:=ms_node ms_t1 ms_t160.
Definition ms_t162:ms_tree:=ms_node ms_t161 ms_t161.
Definition ms_t163:ms_tree:=ms_node ms_t0 ms_t146.
Definition ms_t164:ms_tree:=ms_node ms_t42 ms_t163.
Definition ms_t165:ms_tree:=ms_node ms_t1 ms_t164.
Definition ms_t166:ms_tree:=ms_node ms_t0 ms_t165.
Definition ms_t167:ms_tree:=ms_node ms_t25 ms_t43.
Definition ms_t168:ms_tree:=ms_node ms_t0 ms_t167.
Definition ms_t169:ms_tree:=ms_node ms_t25 ms_t146.
Definition ms_t170:ms_tree:=ms_node ms_t42 ms_t169.
Definition ms_t171:ms_tree:=ms_node ms_t1 ms_t170.
Definition ms_t172:ms_tree:=ms_node ms_t42 ms_t171.
Definition ms_t173:ms_tree:=ms_node ms_t25 ms_t47.
Definition ms_t174:ms_tree:=ms_node ms_t1 ms_t173.
Definition ms_t175:ms_tree:=ms_node ms_t42 ms_t174.
Definition ms_t176:ms_tree:=ms_node ms_t42 ms_t175.
Definition ms_t177:ms_tree:=ms_node ms_t1 ms_t176.
Definition ms_t178:ms_tree:=ms_node ms_t25 ms_t157.
Definition ms_t179:ms_tree:=ms_node ms_t0 ms_t178.
Definition ms_t180:ms_tree:=ms_node ms_t85 ms_t0.
Definition ms_t181:ms_tree:=ms_node ms_t0 ms_t180.
Definition ms_t182:ms_tree:=ms_node ms_t0 ms_t181.
Definition ms_t183:ms_tree:=ms_node ms_t25 ms_t129.
Definition ms_t184:ms_tree:=ms_node ms_t1 ms_t183.
Definition ms_t185:ms_tree:=ms_node ms_t25 ms_t66.
Definition ms_t186:ms_tree:=ms_node ms_t85 ms_t157.
Definition ms_t187:ms_tree:=ms_node ms_t0 ms_t186.
Definition ms_t188:ms_tree:=ms_node ms_t0 ms_t143.
Definition ms_t189:ms_tree:=ms_node ms_t42 ms_t188.
Definition ms_t190:ms_tree:=ms_node ms_t0 ms_t189.
Definition ms_t191:ms_tree:=ms_node ms_t0 ms_t190.
Definition ms_t192:ms_tree:=ms_node ms_t25 ms_t19.
Definition ms_t193:ms_tree:=ms_node ms_t1 ms_t192.
Definition ms_t194:ms_tree:=ms_node ms_t25 ms_t193.
Definition ms_t195:ms_tree:=ms_node ms_t42 ms_t194.
Definition ms_t196:ms_tree:=ms_node ms_t25 ms_t89.
Definition ms_t197:ms_tree:=ms_node ms_t1 ms_t196.
Definition ms_t198:ms_tree:=ms_node ms_t42 ms_t197.
Definition ms_t199:ms_tree:=ms_node ms_t25 ms_t94.
Definition ms_t200:ms_tree:=ms_node ms_t1 ms_t199.
Definition ms_t201:ms_tree:=ms_node ms_t0 ms_t200.
Definition ms_t202:ms_tree:=ms_node ms_t25 ms_t161.
Definition ms_t203:ms_tree:=ms_node ms_t25 ms_t116.
Definition ms_t204:ms_tree:=ms_node ms_t1 ms_t203.
Definition ms_t205:ms_tree:=ms_node ms_t25 ms_t119.
Definition ms_t206:ms_tree:=ms_node ms_t1 ms_t205.
Definition ms_t207:ms_tree:=ms_node ms_t25 ms_t134.
Definition ms_trees(s:ms_dfa):list ms_tree:=match s with
|MS0=>[ms_t8;ms_t17;ms_t18;ms_t1;ms_t23;ms_t7;ms_t7;ms_t31]
|MS1=>[ms_t8;ms_t17;ms_t22;ms_t1;ms_t23;ms_t7;ms_t7;ms_t36]
|MS2=>[ms_t1;ms_t41;ms_t6;ms_t3;ms_t45;ms_t16;ms_t16;ms_t52]
|MS3=>[ms_t21;ms_t17;ms_t22;ms_t1;ms_t23;ms_t7;ms_t7;ms_t56]
|MS4=>[ms_t5;ms_t60;ms_t44;ms_t2;ms_t2;ms_t1;ms_t1;ms_t64]
|MS5=>[ms_t2;ms_t67;ms_t15;ms_t1;ms_t68;ms_t40;ms_t40;ms_t73]
|MS6=>[ms_t21;ms_t76;ms_t22;ms_t1;ms_t80;ms_t20;ms_t20;ms_t83]
|MS7=>[ms_t43;ms_t60;ms_t1;ms_t0;ms_t88;ms_t4;ms_t4;ms_t92]
|MS8=>[ms_t0;ms_t1;ms_t1;ms_t1;ms_t93;ms_t59;ms_t59;ms_t97]
|MS9=>[ms_t4;ms_t1;ms_t44;ms_t1;ms_t1;ms_t1;ms_t1;ms_t72]
|MS10=>[ms_t1;ms_t67;ms_t39;ms_t1;ms_t68;ms_t66;ms_t66;ms_t99]
|MS11=>[ms_t21;ms_t76;ms_t79;ms_t1;ms_t80;ms_t20;ms_t20;ms_t101]
|MS12=>[ms_t1;ms_t104;ms_t19;ms_t3;ms_t45;ms_t75;ms_t75;ms_t106]
|MS13=>[ms_t1;ms_t111;ms_t87;ms_t0;ms_t113;ms_t42;ms_t42;ms_t118]
|MS14=>[ms_t0;ms_t60;ms_t3;ms_t0;ms_t88;ms_t59;ms_t59;ms_t97]
|MS15=>[ms_t1;ms_t67;ms_t87;ms_t1;ms_t9;ms_t0;ms_t0;ms_t121]
|MS16=>[ms_t1;ms_t60;ms_t58;ms_t0;ms_t2;ms_t1;ms_t1;ms_t1]
|MS17=>[ms_t43;ms_t67;ms_t1;ms_t1;ms_t9;ms_t3;ms_t3;ms_t124]
|MS18=>[ms_t1;ms_t1;ms_t1;ms_t1;ms_t1;ms_t1;ms_t1;ms_t1]
|MS19=>[ms_t3;ms_t1;ms_t44;ms_t1;ms_t1;ms_t1;ms_t1;ms_t98]
|MS20=>[ms_t1;ms_t67;ms_t65;ms_t1;ms_t68;ms_t66;ms_t66;ms_t99]
|MS21=>[ms_t78;ms_t76;ms_t79;ms_t1;ms_t80;ms_t20;ms_t20;ms_t125]
|MS22=>[ms_t11;ms_t60;ms_t44;ms_t2;ms_t2;ms_t1;ms_t1;ms_t126]
|MS23=>[ms_t2;ms_t67;ms_t74;ms_t1;ms_t68;ms_t103;ms_t103;ms_t131]
|MS24=>[ms_t86;ms_t60;ms_t112;ms_t0;ms_t2;ms_t1;ms_t1;ms_t135]
|MS25=>[ms_t0;ms_t112;ms_t19;ms_t0;ms_t0;ms_t110;ms_t110;ms_t140]
|MS26=>[ms_t2;ms_t0;ms_t87;ms_t0;ms_t0;ms_t0;ms_t0;ms_t121]
|MS27=>[ms_t0;ms_t60;ms_t58;ms_t0;ms_t88;ms_t59;ms_t59;ms_t97]
|MS28=>[ms_t86;ms_t1;ms_t0;ms_t1;ms_t1;ms_t1;ms_t1;ms_t120]
|MS29=>[ms_t1;ms_t0;ms_t0;ms_t0;ms_t141;ms_t66;ms_t66;ms_t99]
|MS30=>[ms_t1;ms_t60;ms_t1;ms_t0;ms_t2;ms_t1;ms_t1;ms_t1]
|MS31=>[ms_t1;ms_t76;ms_t0;ms_t1;ms_t142;ms_t42;ms_t42;ms_t123]
|MS32=>[ms_t1;ms_t0;ms_t0;ms_t2;ms_t141;ms_t66;ms_t66;ms_t99]
|MS33=>[ms_t43;ms_t67;ms_t1;ms_t1;ms_t9;ms_t0;ms_t0;ms_t124]
|MS34=>[ms_t0;ms_t1;ms_t44;ms_t1;ms_t1;ms_t1;ms_t1;ms_t98]
|MS35=>[ms_t78;ms_t76;ms_t79;ms_t1;ms_t80;ms_t77;ms_t77;ms_t125]
|MS36=>[ms_t43;ms_t60;ms_t1;ms_t0;ms_t88;ms_t10;ms_t10;ms_t92]
|MS37=>[ms_t10;ms_t1;ms_t44;ms_t1;ms_t1;ms_t1;ms_t1;ms_t130]
|MS38=>[ms_t1;ms_t67;ms_t102;ms_t1;ms_t68;ms_t66;ms_t66;ms_t99]
|MS39=>[ms_t107;ms_t144;ms_t1;ms_t0;ms_t141;ms_t85;ms_t85;ms_t150]
|MS40=>[ms_t11;ms_t0;ms_t0;ms_t0;ms_t0;ms_t0;ms_t0;ms_t154]
|MS41=>[ms_t0;ms_t0;ms_t109;ms_t0;ms_t0;ms_t107;ms_t107;ms_t159]
|MS42=>[ms_t86;ms_t60;ms_t0;ms_t0;ms_t2;ms_t1;ms_t1;ms_t120]
|MS43=>[ms_t0;ms_t0;ms_t0;ms_t0;ms_t0;ms_t0;ms_t0;ms_t0]
|MS44=>[ms_t1;ms_t0;ms_t87;ms_t0;ms_t0;ms_t0;ms_t0;ms_t121]
|MS45=>[ms_t0;ms_t162;ms_t1;ms_t1;ms_t68;ms_t85;ms_t85;ms_t166]
|MS46=>[ms_t0;ms_t60;ms_t44;ms_t0;ms_t2;ms_t1;ms_t1;ms_t98]
|MS47=>[ms_t0;ms_t67;ms_t65;ms_t1;ms_t9;ms_t0;ms_t0;ms_t0]
|MS48=>[ms_t0;ms_t1;ms_t112;ms_t1;ms_t1;ms_t1;ms_t1;ms_t168]
|MS49=>[ms_t1;ms_t112;ms_t19;ms_t0;ms_t141;ms_t75;ms_t75;ms_t106]
|MS50=>[ms_t1;ms_t104;ms_t19;ms_t9;ms_t68;ms_t75;ms_t75;ms_t106]
|MS51=>[ms_t0;ms_t60;ms_t9;ms_t0;ms_t88;ms_t59;ms_t59;ms_t97]
|MS52=>[ms_t43;ms_t67;ms_t1;ms_t1;ms_t68;ms_t9;ms_t9;ms_t172]
|MS53=>[ms_t9;ms_t1;ms_t44;ms_t1;ms_t1;ms_t1;ms_t1;ms_t98]
|MS54=>[ms_t1;ms_t0;ms_t44;ms_t0;ms_t141;ms_t25;ms_t25;ms_t177]
|MS55=>[ms_t0;ms_t67;ms_t84;ms_t1;ms_t9;ms_t143;ms_t143;ms_t179]
|MS56=>[ms_t0;ms_t60;ms_t0;ms_t0;ms_t88;ms_t10;ms_t10;ms_t182]
|MS57=>[ms_t10;ms_t0;ms_t0;ms_t0;ms_t0;ms_t0;ms_t0;ms_t158]
|MS58=>[ms_t0;ms_t0;ms_t25;ms_t0;ms_t0;ms_t0;ms_t0;ms_t0]
|MS59=>[ms_t0;ms_t144;ms_t1;ms_t0;ms_t141;ms_t85;ms_t85;ms_t166]
|MS60=>[ms_t1;ms_t67;ms_t44;ms_t1;ms_t9;ms_t0;ms_t0;ms_t165]
|MS61=>[ms_t1;ms_t67;ms_t84;ms_t1;ms_t68;ms_t161;ms_t161;ms_t184]
|MS62=>[ms_t43;ms_t0;ms_t1;ms_t0;ms_t0;ms_t0;ms_t0;ms_t124]
|MS63=>[ms_t0;ms_t67;ms_t0;ms_t1;ms_t9;ms_t0;ms_t0;ms_t0]
|MS64=>[ms_t107;ms_t67;ms_t1;ms_t1;ms_t9;ms_t0;ms_t0;ms_t185]
|MS65=>[ms_t11;ms_t60;ms_t44;ms_t0;ms_t2;ms_t1;ms_t1;ms_t126]
|MS66=>[ms_t0;ms_t67;ms_t74;ms_t1;ms_t9;ms_t107;ms_t107;ms_t159]
|MS67=>[ms_t11;ms_t1;ms_t44;ms_t1;ms_t1;ms_t1;ms_t1;ms_t126]
|MS68=>[ms_t1;ms_t67;ms_t74;ms_t1;ms_t68;ms_t103;ms_t103;ms_t131]
|MS69=>[ms_t1;ms_t76;ms_t44;ms_t1;ms_t142;ms_t42;ms_t42;ms_t171]
|MS70=>[ms_t1;ms_t67;ms_t0;ms_t1;ms_t68;ms_t66;ms_t66;ms_t99]
|MS71=>[ms_t43;ms_t60;ms_t44;ms_t0;ms_t2;ms_t1;ms_t1;ms_t176]
|MS72=>[ms_t0;ms_t67;ms_t0;ms_t9;ms_t9;ms_t0;ms_t0;ms_t0]
|MS73=>[ms_t46;ms_t67;ms_t0;ms_t1;ms_t9;ms_t0;ms_t0;ms_t178]
|MS74=>[ms_t1;ms_t0;ms_t26;ms_t0;ms_t141;ms_t66;ms_t66;ms_t99]
|MS75=>[ms_t0;ms_t0;ms_t87;ms_t0;ms_t0;ms_t0;ms_t0;ms_t187]
|MS76=>[ms_t0;ms_t0;ms_t0;ms_t0;ms_t141;ms_t9;ms_t9;ms_t191]
|MS77=>[ms_t9;ms_t0;ms_t0;ms_t0;ms_t0;ms_t0;ms_t0;ms_t0]
|MS78=>[ms_t1;ms_t0;ms_t44;ms_t0;ms_t0;ms_t0;ms_t0;ms_t165]
|MS79=>[ms_t43;ms_t1;ms_t0;ms_t1;ms_t1;ms_t1;ms_t1;ms_t164]
|MS80=>[ms_t46;ms_t1;ms_t44;ms_t1;ms_t1;ms_t1;ms_t1;ms_t183]
|MS81=>[ms_t1;ms_t67;ms_t160;ms_t1;ms_t68;ms_t66;ms_t66;ms_t99]
|MS82=>[ms_t1;ms_t111;ms_t0;ms_t0;ms_t113;ms_t42;ms_t42;ms_t123]
|MS83=>[ms_t1;ms_t67;ms_t0;ms_t1;ms_t68;ms_t25;ms_t25;ms_t99]
|MS84=>[ms_t10;ms_t67;ms_t0;ms_t1;ms_t9;ms_t0;ms_t0;ms_t158]
|MS85=>[ms_t1;ms_t0;ms_t25;ms_t0;ms_t141;ms_t66;ms_t66;ms_t99]
|MS86=>[ms_t43;ms_t1;ms_t1;ms_t1;ms_t93;ms_t10;ms_t10;ms_t92]
|MS87=>[ms_t43;ms_t1;ms_t112;ms_t1;ms_t1;ms_t1;ms_t1;ms_t195]
|MS88=>[ms_t43;ms_t111;ms_t1;ms_t0;ms_t113;ms_t42;ms_t42;ms_t198]
|MS89=>[ms_t0;ms_t67;ms_t0;ms_t1;ms_t68;ms_t25;ms_t25;ms_t191]
|MS90=>[ms_t25;ms_t60;ms_t44;ms_t0;ms_t2;ms_t1;ms_t1;ms_t98]
|MS91=>[ms_t86;ms_t0;ms_t0;ms_t0;ms_t0;ms_t0;ms_t0;ms_t186]
|MS92=>[ms_t0;ms_t0;ms_t44;ms_t0;ms_t0;ms_t0;ms_t0;ms_t190]
|MS93=>[ms_t43;ms_t60;ms_t0;ms_t0;ms_t2;ms_t1;ms_t1;ms_t164]
|MS94=>[ms_t0;ms_t76;ms_t1;ms_t1;ms_t142;ms_t42;ms_t42;ms_t201]
|MS95=>[ms_t43;ms_t67;ms_t1;ms_t1;ms_t68;ms_t25;ms_t25;ms_t172]
|MS96=>[ms_t25;ms_t1;ms_t44;ms_t1;ms_t1;ms_t1;ms_t1;ms_t98]
|MS97=>[ms_t0;ms_t60;ms_t112;ms_t0;ms_t2;ms_t1;ms_t1;ms_t168]
|MS98=>[ms_t1;ms_t67;ms_t0;ms_t9;ms_t68;ms_t66;ms_t66;ms_t99]
|MS99=>[ms_t0;ms_t67;ms_t0;ms_t1;ms_t68;ms_t9;ms_t9;ms_t191]
|MS100=>[ms_t9;ms_t60;ms_t44;ms_t0;ms_t2;ms_t1;ms_t1;ms_t98]
|MS101=>[ms_t1;ms_t76;ms_t87;ms_t1;ms_t142;ms_t42;ms_t42;ms_t118]
|MS102=>[ms_t1;ms_t60;ms_t9;ms_t0;ms_t2;ms_t1;ms_t1;ms_t1]
|MS103=>[ms_t107;ms_t76;ms_t1;ms_t1;ms_t142;ms_t42;ms_t42;ms_t202]
|MS104=>[ms_t1;ms_t111;ms_t112;ms_t0;ms_t113;ms_t42;ms_t42;ms_t204]
|MS105=>[ms_t0;ms_t67;ms_t44;ms_t1;ms_t9;ms_t0;ms_t0;ms_t190]
|MS106=>[ms_t0;ms_t144;ms_t0;ms_t0;ms_t141;ms_t85;ms_t85;ms_t191]
|MS107=>[ms_t43;ms_t0;ms_t0;ms_t0;ms_t0;ms_t0;ms_t0;ms_t189]
|MS108=>[ms_t0;ms_t111;ms_t1;ms_t0;ms_t113;ms_t42;ms_t42;ms_t201]
|MS109=>[ms_t1;ms_t67;ms_t112;ms_t1;ms_t9;ms_t0;ms_t0;ms_t206]
|MS110=>[ms_t107;ms_t0;ms_t1;ms_t0;ms_t0;ms_t0;ms_t0;ms_t185]
|MS111=>[ms_t86;ms_t1;ms_t112;ms_t1;ms_t1;ms_t1;ms_t1;ms_t135]
|MS112=>[ms_t1;ms_t67;ms_t112;ms_t1;ms_t68;ms_t25;ms_t25;ms_t184]
|MS113=>[ms_t107;ms_t60;ms_t112;ms_t0;ms_t2;ms_t1;ms_t1;ms_t207]
|MS114=>[ms_t43;ms_t67;ms_t0;ms_t1;ms_t9;ms_t0;ms_t0;ms_t189]
|MS115=>[ms_t0;ms_t111;ms_t0;ms_t0;ms_t113;ms_t42;ms_t42;ms_t188]
|MS116=>[ms_t1;ms_t0;ms_t112;ms_t0;ms_t0;ms_t0;ms_t0;ms_t206]
|MS117=>[ms_t107;ms_t1;ms_t0;ms_t1;ms_t1;ms_t1;ms_t1;ms_t205]
|MS118=>[ms_t1;ms_t0;ms_t0;ms_t0;ms_t141;ms_t25;ms_t25;ms_t99]
|MS119=>[ms_t107;ms_t162;ms_t1;ms_t1;ms_t68;ms_t85;ms_t85;ms_t150]
|MS120=>[ms_t107;ms_t1;ms_t44;ms_t1;ms_t1;ms_t1;ms_t1;ms_t183]
|MS121=>[ms_t107;ms_t0;ms_t1;ms_t0;ms_t141;ms_t25;ms_t25;ms_t150]
|MS122=>[ms_t0;ms_t76;ms_t0;ms_t1;ms_t142;ms_t42;ms_t42;ms_t188]
|MS123=>[ms_t0;ms_t0;ms_t112;ms_t0;ms_t0;ms_t0;ms_t0;ms_t179]
|MS124=>[ms_t107;ms_t60;ms_t0;ms_t0;ms_t2;ms_t1;ms_t1;ms_t205]
|MS125=>[ms_t0;ms_t67;ms_t1;ms_t1;ms_t68;ms_t25;ms_t25;ms_t166]
|MS126=>[ms_t1;ms_t67;ms_t44;ms_t1;ms_t68;ms_t25;ms_t25;ms_t177]
|MS127=>[ms_t0;ms_t67;ms_t112;ms_t1;ms_t9;ms_t0;ms_t0;ms_t179]
|MS128=>[ms_t107;ms_t0;ms_t0;ms_t0;ms_t0;ms_t0;ms_t0;ms_t178]
|MS129=>[ms_t0;ms_t0;ms_t1;ms_t0;ms_t141;ms_t25;ms_t25;ms_t166]
|MS130=>[ms_t43;ms_t1;ms_t44;ms_t1;ms_t1;ms_t1;ms_t1;ms_t176]
|MS131=>[ms_t107;ms_t67;ms_t0;ms_t1;ms_t9;ms_t0;ms_t0;ms_t178]
|MS132=>[ms_t0;ms_t0;ms_t0;ms_t0;ms_t141;ms_t25;ms_t25;ms_t191]
|MS133=>[ms_t43;ms_t76;ms_t1;ms_t1;ms_t142;ms_t42;ms_t42;ms_t198]
|MS134=>[ms_t1;ms_t76;ms_t112;ms_t1;ms_t142;ms_t42;ms_t42;ms_t204]
|MS135=>[ms_t107;ms_t1;ms_t112;ms_t1;ms_t1;ms_t1;ms_t1;ms_t207]
|MS136=>[ms_t107;ms_t67;ms_t1;ms_t1;ms_t68;ms_t25;ms_t25;ms_t150]
end.
Definition ms_cons(a:Sym)(s:ms_dfa):ms_dfa:=match a,s with
|S0,MS0=>MS1|S1,MS0=>MS2
|S0,MS1=>MS3|S1,MS1=>MS2
|S0,MS2=>MS4|S1,MS2=>MS5
|S0,MS3=>MS6|S1,MS3=>MS2
|S0,MS4=>MS7|S1,MS4=>MS8
|S0,MS5=>MS9|S1,MS5=>MS10
|S0,MS6=>MS11|S1,MS6=>MS12
|S0,MS7=>MS13|S1,MS7=>MS14
|S0,MS8=>MS15|S1,MS8=>MS16
|S0,MS9=>MS17|S1,MS9=>MS18
|S0,MS10=>MS19|S1,MS10=>MS20
|S0,MS11=>MS21|S1,MS11=>MS12
|S0,MS12=>MS22|S1,MS12=>MS23
|S0,MS13=>MS24|S1,MS13=>MS25
|S0,MS14=>MS26|S1,MS14=>MS27
|S0,MS15=>MS28|S1,MS15=>MS29
|S0,MS16=>MS30|S1,MS16=>MS8
|S0,MS17=>MS31|S1,MS17=>MS32
|S0,MS18=>MS18|S1,MS18=>MS18
|S0,MS19=>MS33|S1,MS19=>MS18
|S0,MS20=>MS34|S1,MS20=>MS20
|S0,MS21=>MS35|S1,MS21=>MS12
|S0,MS22=>MS36|S1,MS22=>MS8
|S0,MS23=>MS37|S1,MS23=>MS38
|S0,MS24=>MS39|S1,MS24=>MS8
|S0,MS25=>MS40|S1,MS25=>MS41
|S0,MS26=>MS42|S1,MS26=>MS43
|S0,MS27=>MS44|S1,MS27=>MS27
|S0,MS28=>MS45|S1,MS28=>MS18
|S0,MS29=>MS46|S1,MS29=>MS47
|S0,MS30=>MS30|S1,MS30=>MS8
|S0,MS31=>MS48|S1,MS31=>MS49
|S0,MS32=>MS46|S1,MS32=>MS47
|S0,MS33=>MS31|S1,MS33=>MS29
|S0,MS34=>MS33|S1,MS34=>MS18
|S0,MS35=>MS35|S1,MS35=>MS50
|S0,MS36=>MS13|S1,MS36=>MS51
|S0,MS37=>MS52|S1,MS37=>MS18
|S0,MS38=>MS53|S1,MS38=>MS20
|S0,MS39=>MS54|S1,MS39=>MS55
|S0,MS40=>MS56|S1,MS40=>MS43
|S0,MS41=>MS57|S1,MS41=>MS58
|S0,MS42=>MS59|S1,MS42=>MS8
|S0,MS43=>MS43|S1,MS43=>MS43
|S0,MS44=>MS42|S1,MS44=>MS43
|S0,MS45=>MS60|S1,MS45=>MS61
|S0,MS46=>MS62|S1,MS46=>MS8
|S0,MS47=>MS63|S1,MS47=>MS29
|S0,MS48=>MS64|S1,MS48=>MS18
|S0,MS49=>MS65|S1,MS49=>MS66
|S0,MS50=>MS67|S1,MS50=>MS68
|S0,MS51=>MS44|S1,MS51=>MS27
|S0,MS52=>MS69|S1,MS52=>MS70
|S0,MS53=>MS33|S1,MS53=>MS18
|S0,MS54=>MS71|S1,MS54=>MS72
|S0,MS55=>MS73|S1,MS55=>MS74
|S0,MS56=>MS75|S1,MS56=>MS51
|S0,MS57=>MS76|S1,MS57=>MS43
|S0,MS58=>MS77|S1,MS58=>MS43
|S0,MS59=>MS78|S1,MS59=>MS55
|S0,MS60=>MS79|S1,MS60=>MS29
|S0,MS61=>MS80|S1,MS61=>MS81
|S0,MS62=>MS82|S1,MS62=>MS43
|S0,MS63=>MS63|S1,MS63=>MS29
|S0,MS64=>MS83|S1,MS64=>MS29
|S0,MS65=>MS36|S1,MS65=>MS8
|S0,MS66=>MS84|S1,MS66=>MS85
|S0,MS67=>MS86|S1,MS67=>MS18
|S0,MS68=>MS37|S1,MS68=>MS38
|S0,MS69=>MS87|S1,MS69=>MS49
|S0,MS70=>MS34|S1,MS70=>MS20
|S0,MS71=>MS88|S1,MS71=>MS8
|S0,MS72=>MS63|S1,MS72=>MS29
|S0,MS73=>MS89|S1,MS73=>MS29
|S0,MS74=>MS90|S1,MS74=>MS47
|S0,MS75=>MS91|S1,MS75=>MS43
|S0,MS76=>MS92|S1,MS76=>MS63
|S0,MS77=>MS43|S1,MS77=>MS43
|S0,MS78=>MS93|S1,MS78=>MS43
|S0,MS79=>MS94|S1,MS79=>MS18
|S0,MS80=>MS95|S1,MS80=>MS18
|S0,MS81=>MS96|S1,MS81=>MS20
|S0,MS82=>MS97|S1,MS82=>MS25
|S0,MS83=>MS34|S1,MS83=>MS98
|S0,MS84=>MS99|S1,MS84=>MS29
|S0,MS85=>MS100|S1,MS85=>MS47
|S0,MS86=>MS101|S1,MS86=>MS102
|S0,MS87=>MS103|S1,MS87=>MS18
|S0,MS88=>MS104|S1,MS88=>MS25
|S0,MS89=>MS105|S1,MS89=>MS98
|S0,MS90=>MS62|S1,MS90=>MS8
|S0,MS91=>MS106|S1,MS91=>MS43
|S0,MS92=>MS107|S1,MS92=>MS43
|S0,MS93=>MS108|S1,MS93=>MS8
|S0,MS94=>MS109|S1,MS94=>MS49
|S0,MS95=>MS69|S1,MS95=>MS98
|S0,MS96=>MS33|S1,MS96=>MS18
|S0,MS97=>MS110|S1,MS97=>MS8
|S0,MS98=>MS34|S1,MS98=>MS20
|S0,MS99=>MS105|S1,MS99=>MS70
|S0,MS100=>MS62|S1,MS100=>MS8
|S0,MS101=>MS111|S1,MS101=>MS49
|S0,MS102=>MS30|S1,MS102=>MS8
|S0,MS103=>MS112|S1,MS103=>MS49
|S0,MS104=>MS113|S1,MS104=>MS25
|S0,MS105=>MS114|S1,MS105=>MS29
|S0,MS106=>MS92|S1,MS106=>MS55
|S0,MS107=>MS115|S1,MS107=>MS43
|S0,MS108=>MS116|S1,MS108=>MS25
|S0,MS109=>MS117|S1,MS109=>MS29
|S0,MS110=>MS118|S1,MS110=>MS43
|S0,MS111=>MS119|S1,MS111=>MS18
|S0,MS112=>MS120|S1,MS112=>MS98
|S0,MS113=>MS121|S1,MS113=>MS8
|S0,MS114=>MS122|S1,MS114=>MS29
|S0,MS115=>MS123|S1,MS115=>MS25
|S0,MS116=>MS124|S1,MS116=>MS43
|S0,MS117=>MS125|S1,MS117=>MS18
|S0,MS118=>MS46|S1,MS118=>MS72
|S0,MS119=>MS126|S1,MS119=>MS61
|S0,MS120=>MS95|S1,MS120=>MS18
|S0,MS121=>MS54|S1,MS121=>MS72
|S0,MS122=>MS127|S1,MS122=>MS49
|S0,MS123=>MS128|S1,MS123=>MS43
|S0,MS124=>MS129|S1,MS124=>MS8
|S0,MS125=>MS60|S1,MS125=>MS98
|S0,MS126=>MS130|S1,MS126=>MS98
|S0,MS127=>MS131|S1,MS127=>MS29
|S0,MS128=>MS132|S1,MS128=>MS43
|S0,MS129=>MS78|S1,MS129=>MS72
|S0,MS130=>MS133|S1,MS130=>MS18
|S0,MS131=>MS89|S1,MS131=>MS29
|S0,MS132=>MS92|S1,MS132=>MS72
|S0,MS133=>MS134|S1,MS133=>MS49
|S0,MS134=>MS135|S1,MS134=>MS49
|S0,MS135=>MS136|S1,MS135=>MS18
|S0,MS136=>MS126|S1,MS136=>MS98
end.
Fixpoint ms_fold(R:list Sym):ms_dfa:=match R with []=>MS0|a::R=>ms_cons a(ms_fold R)end.
Definition ms_ok(q:St)(h:Sym)(L:list Sym)(s:ms_dfa):bool:=
 ms_eval(nth(match q,h with StA,S0=>0|StA,S1=>1|StB,S0=>2|StB,S1=>3|StC,S0=>4|StC,S1=>5|StD,S0=>6|StD,S1=>7 end)(ms_trees s)ms_t0)L.
(* END GENERATED FINITE CERTIFICATE *)
Definition ms_inv(c:cconf):Prop:=let '(q,(L,h,R)):=c in ms_ok q h(ms_prefix 8 L)(ms_fold R)=true.
Definition ms_guard(L:list Sym):bool:=match L with
|S0::S1::S0::S0::S1::_=>true
|S0::S1::S1::S0::S1::S1::S0::S1::_=>true
|_=>false end.
Definition ms_tr(q:St)(h:Sym):Trans:=match bm_tm q h with
|Some t=>t|None=>mkTrans S0 DR StA end.
Definition ms_edge(q:St)(h:Sym)(U:list Sym)(s:ms_dfa)(r:Sym):bool:=
 let tr:=ms_tr q h in let L:=firstn 8 U in
 match t_dir tr with
 |DL=>implb(ms_ok q h L s)
   (ms_ok(t_next tr)(chd U)(firstn 8(ctl U))(ms_cons(t_write tr)s))
 |DR=>implb(ms_ok q h L(ms_cons r s))
   (ms_ok(t_next tr)r(firstn 8(t_write tr::U))s)
 end.
Definition ms_bottom(q:St)(h:Sym)(U:list Sym):bool:=
 let tr:=ms_tr q h in
 match t_dir tr,q,h with
 |DR,StB,S0=>true
 |DR,_,_=>implb(ms_ok q h(firstn 8 U)MS0)
   (ms_ok(t_next tr)S0(firstn 8(t_write tr::U))MS0)
 |DL,_,_=>true end.
Definition ms_post(U:list Sym):bool:=
 implb(ms_ok StB S0(firstn 8 U)MS0)(ms_guard(firstn 8 U)).
Definition ms_reset(U:list Sym):bool:=
 implb(ms_guard(firstn 8 U))
 (ms_ok StD(chd U)(firstn 8(ctl U))(ms_fold[S1;S1;S0])).
Definition ms_check:bool:=
 forallb(fun U=>
 ms_post U && ms_reset U &&
 forallb(fun q=>forallb(fun h=>ms_bottom q h U &&
 forallb(fun s=>forallb(fun r=>ms_edge q h U s r)[S0;S1])ms_states)[S0;S1])[StA;StB;StC;StD])
 (ms_words 9).
Lemma ms_checked:ms_check=true.
Proof. vm_compute;reflexivity. Qed.
Lemma ms_local:forall U,length U=9->ms_post U=true /\ms_reset U=true /\
 forall q h,ms_bottom q h U=true /\forall s r,ms_edge q h U s r=true.
Proof.
 intros U HU. pose proof ms_checked as H;unfold ms_check in H.
 rewrite forallb_forall in H.
 specialize(H U(ms_words_complete 9 U HU)).
 repeat rewrite andb_true_iff in H. destruct H as[[HP HR]H].
 split;[exact HP|split;[exact HR|]]. intros q h.
 rewrite forallb_forall in H. specialize(H q).
 assert(HQ:In q[StA;StB;StC;StD])by(destruct q;cbn;auto).
 specialize(H HQ). rewrite forallb_forall in H.
 assert(HH:In h[S0;S1])by(destruct h;cbn;auto).
 specialize(H h HH). apply andb_true_iff in H as[HB H].
 split;[exact HB|]. intros s r. rewrite forallb_forall in H.
 assert(HI:In s ms_states)by(apply ms_states_complete).
 specialize(H s HI). rewrite forallb_forall in H.
 apply H;destruct r;cbn;auto.
Qed.
Lemma ms_edge_ok:forall q h L s r,ms_edge q h(ms_prefix 9 L)s r=true.
Proof. intros;eapply(proj2(proj2(proj2(ms_local _ (ms_prefix_length 9 L))) q h)). Qed.
Lemma ms_bottom_ok:forall q h L,ms_bottom q h(ms_prefix 9 L)=true.
Proof. intros;exact(proj1(proj2(proj2(ms_local _ (ms_prefix_length 9 L)))q h)). Qed.
Lemma ms_seed:forall L,ms_guard(ms_prefix 8 L)=true->ms_inv(cL StD L[S1;S1;S0]).
Proof.
 intros L HG. pose proof(proj1(proj2(ms_local _ (ms_prefix_length 9 L))))as H.
 unfold ms_reset in H. change(implb(ms_guard(ms_prefix 8 L))(ms_ok StD(chd L)(ms_prefix 8(ctl L))(ms_fold[S1;S1;S0]))=true)in H.
 rewrite HG in H. exact H.
Qed.
Lemma ms_frontier:forall L,ms_inv(StB,(L,S0,[]))->ms_guard(ms_prefix 8 L)=true.
Proof.
 intros L HI. pose proof(proj1(ms_local _ (ms_prefix_length 9 L)))as H.
 unfold ms_post in H. change(implb(ms_ok StB S0(ms_prefix 8 L)MS0)(ms_guard(ms_prefix 8 L))=true)in H.
 unfold ms_inv in HI;cbn[ms_fold]in HI. rewrite HI in H;exact H.
Qed.
Section Machine.
Variable tm:TM.
Hypothesis Htm:forall q h,tm q h=bm_tm q h.
Lemma ms_step:forall c d,cstep tm c=Some d->ms_inv c->
 cinstr c<>(StB,S0) \/ snd(snd c)<>[]->ms_inv d.
Proof.
 intros[q[[L h]R]] e HE HI HN.
 assert(HP:=ms_edge_ok q h L(ms_fold R)S0).
 assert(HO:=ms_edge_ok q h L(ms_fold(ctl R))(chd R)).
 assert(HB:=ms_bottom_ok q h L).
 unfold ms_inv in HI;cbn in HN.
 unfold cstep in HE;rewrite Htm in HE.
 destruct q,h;cbn[bm_tm ctape_move t_dir t_write t_next]in HE;
 cbn[ms_edge ms_bottom ms_tr bm_tm t_dir t_write t_next]in HP,HO,HB.
 - destruct R as[|r R].
   + injection HE as <-. change(implb(ms_ok StA S0(ms_prefix 8 L)MS0)(ms_ok StB S0(ms_prefix 8(S0::L))MS0)=true)in HB.
     cbn[ms_fold]in HI;rewrite HI in HB;exact HB.
   + injection HE as <-. unfold ms_inv;cbn[chd ctl].
     change(implb(ms_ok StA S0(ms_prefix 8 L)(ms_cons r(ms_fold R)))(ms_ok StB r(ms_prefix 8(S0::L))(ms_fold R))=true)in HO.
     cbn[ms_fold]in HI;rewrite HI in HO;exact HO.
 - injection HE as <-. unfold ms_inv;cbn[chd ctl ms_fold].
   change(implb(ms_ok StA S1(ms_prefix 8 L)(ms_fold R))(ms_ok StD(chd L)(ms_prefix 8(ctl L))(ms_cons S1(ms_fold R)))=true)in HP.
   cbn[ms_fold]in HI;rewrite HI in HP;exact HP.
 - destruct R as[|r R].
   + destruct HN as[HN|HN];exfalso;apply HN;reflexivity.
   + injection HE as <-. unfold ms_inv;cbn[chd ctl].
     change(implb(ms_ok StB S0(ms_prefix 8 L)(ms_cons r(ms_fold R)))(ms_ok StC r(ms_prefix 8(S1::L))(ms_fold R))=true)in HO.
     cbn[ms_fold]in HI;rewrite HI in HO;exact HO.
 - destruct R as[|r R].
   + injection HE as <-. change(implb(ms_ok StB S1(ms_prefix 8 L)MS0)(ms_ok StC S0(ms_prefix 8(S0::L))MS0)=true)in HB.
     cbn[ms_fold]in HI;rewrite HI in HB;exact HB.
   + injection HE as <-. unfold ms_inv;cbn[chd ctl].
     change(implb(ms_ok StB S1(ms_prefix 8 L)(ms_cons r(ms_fold R)))(ms_ok StC r(ms_prefix 8(S0::L))(ms_fold R))=true)in HO.
     cbn[ms_fold]in HI;rewrite HI in HO;exact HO.
 - injection HE as <-. unfold ms_inv;cbn[chd ctl ms_fold].
   change(implb(ms_ok StC S0(ms_prefix 8 L)(ms_fold R))(ms_ok StA(chd L)(ms_prefix 8(ctl L))(ms_cons S1(ms_fold R)))=true)in HP.
   cbn[ms_fold]in HI;rewrite HI in HP;exact HP.
 - destruct R as[|r R].
   + injection HE as <-. change(implb(ms_ok StC S1(ms_prefix 8 L)MS0)(ms_ok StA S0(ms_prefix 8(S1::L))MS0)=true)in HB.
     cbn[ms_fold]in HI;rewrite HI in HB;exact HB.
   + injection HE as <-. unfold ms_inv;cbn[chd ctl].
     change(implb(ms_ok StC S1(ms_prefix 8 L)(ms_cons r(ms_fold R)))(ms_ok StA r(ms_prefix 8(S1::L))(ms_fold R))=true)in HO.
     cbn[ms_fold]in HI;rewrite HI in HO;exact HO.
 - destruct R as[|r R].
   + injection HE as <-. change(implb(ms_ok StD S0(ms_prefix 8 L)MS0)(ms_ok StA S0(ms_prefix 8(S1::L))MS0)=true)in HB.
     cbn[ms_fold]in HI;rewrite HI in HB;exact HB.
   + injection HE as <-. unfold ms_inv;cbn[chd ctl].
     change(implb(ms_ok StD S0(ms_prefix 8 L)(ms_cons r(ms_fold R)))(ms_ok StA r(ms_prefix 8(S1::L))(ms_fold R))=true)in HO.
     cbn[ms_fold]in HI;rewrite HI in HO;exact HO.
 - injection HE as <-. unfold ms_inv;cbn[chd ctl ms_fold].
   change(implb(ms_ok StD S1(ms_prefix 8 L)(ms_fold R))(ms_ok StD(chd L)(ms_prefix 8(ctl L))(ms_cons S0(ms_fold R)))=true)in HP.
   cbn[ms_fold]in HI;rewrite HI in HP;exact HP.
Qed.
End Machine.
Definition ms_P0:list Sym:=[S0;S1;S0;S0;S1].
Definition ms_P1:list Sym:=[S0;S1;S1;S0;S1;S1;S0;S1].
Lemma ms_guard_shape:forall L,ms_guard(ms_prefix 8 L)=true->
 (exists U,L=ms_P0++U)\/(exists U,L=ms_P1++U).
Proof.
 intros L H;unfold ms_P0,ms_P1.
 repeat match goal with
 |H:false=true|-_=>discriminate H
 |U:list Sym|-_=>first[left;exists U;reflexivity|right;exists U;reflexivity|
 destruct U as[|a U];[cbn[ms_prefix chd ctl ms_guard]in H|destruct a;cbn[ms_prefix chd ctl ms_guard]in H]]
 end.
Qed.
Definition ms_full(c:cconf):Prop:=bm_inv c /\ ms_inv c.
Definition ms_mark(c:cconf):Prop:=ms_full c /\ cinstr c=(StB,S0).
Section Returns.
Variable tm:TM.
Hypothesis Htm:forall q h,tm q h=bm_tm q h.
Lemma ms_full_step:forall c d,cstep tm c=Some d->ms_full c->
 cinstr c<>(StB,S0)\/snd(snd c)<>[]->ms_full d.
Proof. intros c d HS[HB HM]HN;split;[eapply bm_step|eapply ms_step];eauto. Qed.
Lemma ms_reaches:forall c,ms_full c->exists d,ms_mark d /\ Reach0 tm c d.
Proof.
 intros c HI.
 assert(H:exists d,ms_full d /\ cinstr d=(StB,S0) /\ Reach0 tm c d).
 { eapply(bmr_finite_hit tm
   (Htm StA S0)(Htm StA S1)(Htm StB S1)(Htm StC S0)(Htm StC S1)(Htm StD S0)(Htm StD S1)
   ms_full).
   - intros x y HX HN HS;apply(ms_full_step x y HS HX);left;exact HN.
   - intros q L h y[HX _]HN HS HD;exact(bm_no_escape tm Htm _ _ HS HX HN HD eq_refl).
   - exact HI. }
 destruct H as(d&HD&HT&HR). exists d;split;[split;assumption|exact HR].
Qed.
Lemma ms_return:forall c,ms_mark c->exists d,ms_mark d /\ Reach1 tm c d.
Proof.
 intros[q[[L h]R]][HI HT]. cbn[cinstr]in HT;injection HT as -> ->.
 destruct R as[|r R].
 - assert(HE:ms_full(cL StD L[S1;S1;S0])).
   { split;[apply bm_reset_inv|apply ms_seed,ms_frontier;exact(proj2 HI)]. }
   destruct(ms_reaches _ HE)as(d&HD&HR).
   exists d;split;[exact HD|eapply reach10;[apply bm_reset;exact Htm|exact HR]].
 - set(e:=(StC,(S1::L,r,R))).
   assert(HS:cstep tm(StB,(L,S0,r::R))=Some e).
   { cbn[cstep];rewrite Htm;reflexivity. }
   assert(HE:ms_full e)by(apply(ms_full_step _ _ HS HI);right;discriminate).
   destruct(ms_reaches _ HE)as(d&HD&HR). exists d;split;[exact HD|].
   eapply(r1_run _ 1 _ e);[lia|cbn[csteps cstep];rewrite Htm;reflexivity|exact HR].
Qed.
Lemma ms_mark_instr:forall c,ms_mark c->cinstr c=(StB,S0).
Proof. intros c[_ H];exact H. Qed.
Lemma ms_boot:stepn tm 12 InitES=Some(lift(StB,(ms_P0,S0,[]))).
Proof. apply boot_ok;unfold ms_P0;repeat(cbn[csteps cstep CTape.c0];rewrite ?Htm;cbn[bm_tm ctape_move t_dir t_next t_write chd ctl]);reflexivity. Qed.
Lemma ms_boot_mark:ms_mark(StB,(ms_P0,S0,[])).
Proof. repeat split;vm_compute;reflexivity. Qed.
End Returns.
