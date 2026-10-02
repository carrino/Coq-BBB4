#!/usr/bin/env python3
"""Deterministically replay the saved BLC5 certificates into CBT_AST_105.v.

The certificate search and this emitter are untrusted. ListGlueLexTr checks
both row proofs when Coq compiles the generated batch.
"""
import json,sys
from pathlib import Path
HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
sys.path.insert(0, str(HERE))
import lx5
certs=[json.loads(line) for line in (HERE / 'ast105.jsonl').read_text().splitlines() if line]
head='''(** Transition-level block-list closeout, with far-end lexicographic liveness.
    The untrusted certificates are checked by landed ListGlueLexTr. *)
From Coq Require Import Arith List ZArith.
From BBB4 Require Import BBB4_Statement BBBT4_Statement.
From BBB4.Census Require Import Deferred_Defs.
From BBB4.CloseoutTr Require Import CloseoutKitTr.
From BBB4.Checkers Require Import LapDecider.
From BBB4.Counters Require Import TriGlueTr ListGlue2Tr ListGlueLexTr.
Import ListNotations.
'''
from cbt import spec_row
out=head
for i,c in enumerate(certs):
 name=f'AST_105_{i:04}'
 out+=f"\n(* spec {c['spec']} *)\nDefinition r_{name} : list (option Trans) := {spec_row(c['spec'])}.\nLemma cv_{name} : coversTr (row_to_tm r_{name}).\nProof. "+lx5.renderx(lx5.detuplex(c))+' Qed.\n'
out+='\nDefinition cbtrows_AST_105 : list (list (option Trans)) := [r_AST_105_0000;r_AST_105_0001].\nLemma cbt_AST_105_covers : Forall coversTr (map row_to_tm cbtrows_AST_105).\nProof. exact (Forall_cons _ cv_AST_105_0000 (Forall_cons _ cv_AST_105_0001 (Forall_nil _))). Qed.\n'
(ROOT / 'theories/CloseoutTr/CBT_AST_105.v').write_text(out)
