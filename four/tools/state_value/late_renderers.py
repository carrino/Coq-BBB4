"""Pure source rendering for the late BBB(2,4) dependency families.

No legacy main, Coq compiler, native search, historical object validation or
receipt publication is invoked.  The caller owns input pinning and compares
every emitted Coq byte with its frozen source manifest.
"""
from collections import defaultdict
from pathlib import Path
import ast
import base64
import hashlib
import inspect
import json
import re
import zlib


def compact(ctx, rel):
    data = ctx.read_json(rel)
    if data.get('encoding') == 'zlib-base64':
        raw = zlib.decompress(base64.b64decode(data['data'], validate=True))
        if hashlib.sha256(raw).hexdigest() != data['uncompressed_sha256']:
            raise ValueError('Compact input checksum differs: ' + rel)
        data = json.loads(raw)
    return data


def emit(ctx, prefix, name, text, producer):
    rel = prefix.rstrip('/') + '/' + name
    if ctx.need(rel):
        ctx.emit(rel, text, producer)


def inventory(ctx, prefix, ns, rows, bound=0, module='Board', scope='state',
              board='board', small='small_sound', sound='sound',
              pending='was_pending', target='Inventory.v', instruction_bound=None):
    campaign = ctx.module('check_campaign')
    descriptor = dict(module=ns+'.'+module, machines=rows, board=board,
                      scope=scope, state_bound=bound,
                      instruction_bound=(bound if instruction_bound is None else instruction_bound) if scope == 'both' else None,
                      small_sound=small, sound=sound, was_pending=pending)
    emit(ctx, prefix, target, campaign.inventory_source(descriptor), 'inventory_source')


def _generic_cases(ctx):
    """Universal-template packages all expose the same small pure interface."""
    packages=sorted({p.split('/')[2] for p in ctx.targets if p.startswith('four/build/burn')})
    for package in packages:
        tool='check_'+package.replace('-','_')
        try:
            m=ctx.module(tool)
        except (FileNotFoundError, ModuleNotFoundError):
            continue
        if not hasattr(m, 'example') or not hasattr(m, 'NS'):
            continue
        build = getattr(m, 'BUILD', getattr(m, 'OUTPUT', None))
        if build is None:
            continue
        prefix = str(build.relative_to(ctx.repo))
        if not ctx.any_needed(prefix+'/'):
            continue
        base = 'four/research/'+package
        inp = base+'-proof-input.json'
        # The contextual-marker pilot predates the proof-input suffix.
        if package in ['burn9-context-marker','burn12-history-marker','burn14-right-parity','burn15-padded-wall']:
            inp = base+'-input.json'
        data = compact(ctx, inp)
        rows = data['rows']
        for rel, expected in data.get('template_sha256', {}).items():
            source = 'four/'+rel
            content = ctx.path(source).read_bytes()
            if hashlib.sha256(content).hexdigest() != expected:
                raise ValueError('Template checksum differs: '+source)
            emit(ctx, prefix, Path(rel).name, content, source)
        # S071 has one intentionally generated data module.
        if package == 'burn43-s071-far' and ctx.need(prefix+'/Data.v'):
            generator = ctx.module('generate_burn43_s071_far_data')
            witness = ctx.read_json('four/'+data['witness_file'])
            emit(ctx, prefix, 'Data.v', generator.render_data(witness), 'render_data')
        arity = len(inspect.signature(m.example).parameters)
        for i, row in enumerate(rows):
            text = m.example(i, row) if arity == 2 else m.example(row)
            emit(ctx, prefix, f'Example{i:02d}.v', text, tool+'.example')
        if hasattr(m, 'board'):
            body = m.board(rows)
        else:
            original = ctx.module('check_burn9_context_marker')
            body = original.board(rows).replace('From '+original.NS+' Require Import Example',
                                               'From '+m.NS+' Require Import Example')
        emit(ctx, prefix, 'Board.v', body, tool+'.board')
        inventory(ctx, prefix, m.NS, [r['machine'] for r in rows], data.get('state_bound', 0))


def _marker_batches(ctx):
    families = [('burn9-context-marker', 'check_burn9_context_marker', 'BBB24Burn9ContextMarker'),
                ('burn10-marker-history', 'check_burn10_marker_history', 'BBB24Burn10MarkerHistory'),
                ('burn12-history-marker', 'check_burn12_history_marker', 'BBB24Burn12HistoryMarker'),
                ('burn15-padded-wall', 'check_burn15_padded_wall', 'BBB24Burn15PaddedWall')]
    wrapper = ctx.module('check_burn9_context_marker')
    prefixes = sorted({p.split('/')[2] for p in ctx.targets if p.startswith('four/build/')})
    for base, tool, parent_ns in families:
        pilot = None
        for package in prefixes:
            if not package.startswith(base+'-'):
                continue
            # Names such as "burn12-history-marker" itself are rendered above.
            suffix = package[len(base)+1:]
            prefix = 'four/build/'+package+'/proof'
            if not ctx.any_needed(prefix+'/'):
                continue
            if pilot is None:
                pilot = ctx.module(tool)
            data = compact(ctx, 'four/research/'+package+'-proof-input.json')
            rows = data['rows']
            ns = parent_ns+suffix.capitalize()
            for i, row in enumerate(rows):
                emit(ctx, prefix, f'Example{i:02d}.v', pilot.example(i, row), tool+'.example')
            original_board = pilot.board(rows) if hasattr(pilot, 'board') else wrapper.board(rows)
            old_ns = pilot.NS if hasattr(pilot, 'board') else wrapper.NS
            body = original_board.replace('From '+old_ns+' Require Import Example',
                                          'From '+ns+' Require Import Example')
            emit(ctx, prefix, 'Board.v', body, tool+'.board')
            inventory(ctx, prefix, ns, [r['machine'] for r in rows], data.get('state_bound', 0))


def _routine(ctx):
    prefix = 'four/build/burn10-routine-states'
    if not ctx.any_needed(prefix+'/'):
        return
    m = ctx.module('replay_burn10_routine_states')
    campaign = ctx.module('check_campaign')
    for batch, label in [('full','Full'),('benchmark256','Benchmark')]:
        # The benchmark and full queue deliberately share their first shards.
        if batch == 'benchmark256' and not any(ctx.need(prefix+'/'+label+n)
                                             for n in ['Board.v','Inventory.v']):
            continue
        data = compact(ctx, 'four/research/burn10-routine-states-'+batch+'-input.json')
        links = []
        for stage, group in enumerate(data['groups']):
            for offset in range(0,len(group['rows']),256):
                suffix = f'S{stage:02}_{offset//256:04}'
                checker, link = 'Checker'+suffix, 'Link'+suffix
                emit(ctx, prefix, checker+'.v', m.checker_source(group['rows'][offset:offset+256],
                                                               group['certificate']), 'routine.checker_source')
                emit(ctx, prefix, link+'.v', m.link_source(checker), 'routine.link_source')
                links.append(link)
        emit(ctx, prefix, label+'Board.v', m.aggregate_source(links), 'routine.aggregate_source')
        machines = [campaign.unpack(n,17) for group in data['groups'] for n in group['rows']]
        inventory(ctx, prefix, m.NAMESPACE, machines, 4096,
                  module=label+'Board',target=label+'Inventory.v')


def _routine_prior(ctx):
    m = ctx.module('check_burn10_state_replay_pilot')
    campaign = ctx.module('check_campaign')
    for batch in ['pilot','64']:
        prefix = 'four/build/burn10-state-closeout/replay-'+batch
        if not ctx.any_needed(prefix+'/'):
            continue
        data = compact(ctx, 'four/research/burn10-state-replay-'+batch+'-input.json')
        rows = [dict(zip(data['columns'],v)) for v in data['rows']]
        groups = defaultdict(list)
        for row in rows:
            groups[tuple(row[k] for k in data['columns'][1:])].append(row)
        ns = m.NAMESPACE if batch == 'pilot' else 'BBB24Burn10StateReplay'+batch
        links, machines = [], []
        for index, (_, selected) in enumerate(sorted(groups.items())):
            checker, link = f'Checker{index:02}', f'Link{index:02}'
            emit(ctx, prefix, checker+'.v', m.checker_source(selected), 'routine-prior.checker_source')
            emit(ctx, prefix, link+'.v', m.link_source(checker).replace(m.NAMESPACE,ns), 'routine-prior.link_source')
            links.append(link);machines.extend(r['machine'] for r in selected)
        body = m.HEADER+f'From {ns} Require Import '+' '.join(links)+'.\n'
        body += 'Definition boards : list (list TM) := ['+';'.join(n+'.board' for n in links)+'].\nDefinition board := concat boards.\n'
        for field,bound in [('small_sound','(N.to_nat 4096%N)'),('sound','score')]:
            body += f'Lemma {field} : StateBoardSound {bound} board.\nProof. apply state_boards_sound. unfold boards.\n'
            body += campaign.forall_proof(links,field)+'\nQed.\n'
        body += 'Lemma was_pending : forall family, In family board -> bootstrap_pending family.\nProof. apply boards_pending. unfold boards.\n'
        body += campaign.forall_proof(links,'was_pending')+'\nQed.\n'
        body += '''Definition pending := remaining bootstrap_pending board.
Theorem coverage : forall tm, QHBound score tm \\/ pending tm.
Proof. exact (state_closeout_coverage _ _ _ bootstrap_state_coverage sound). Qed.
Theorem discharged : forall family, In family board -> forall tm, TM_le family tm ->
  bootstrap_pending tm /\\ QHBound score tm /\\ ~ pending tm.
Proof. exact (state_board_discharge _ _ was_pending sound). Qed.
Print Assumptions discharged.
'''
        emit(ctx,prefix,'Board.v',body,'routine-prior.aggregate')
        inventory(ctx,prefix,ns,machines,4096)


def _blank_routine(ctx):
    prefix = 'four/build/burn15-blank-routine'
    if not ctx.any_needed(prefix+'/'):
        return
    m = ctx.module('replay_burn15_blank_routine_sources')
    routine = ctx.module('replay_burn10_routine_states')
    campaign = ctx.module('check_campaign')
    data = compact(ctx,'four/research/burn15-blank-routine-input.json')
    modules=[]
    for stage,group in enumerate(data['groups']):
        for offset in range(0,len(group['rows']),256):
            name=f'CheckerS{stage:02}_{offset//256:03}';modules.append(name)
            text=routine.checker_source(group['rows'][offset:offset+256],group['certificate'])
            text+='''Lemma pending_checked : forallb (pending_check 9 empty bootstrap) board = true.
Proof. vm_compute. reflexivity. Qed.
Lemma was_pending : forall family, In family board -> bootstrap_pending family.
Proof.
  intros family Hin. apply pending_check_sound. pose proof pending_checked as H.
  apply forallb_forall with (x:=family) in H; assumption.
Qed.
'''
            emit(ctx,prefix,name+'.v',text,'blank-routine.checker')
    body=m.HEADER+f'From {m.NS} Require Import '+' '.join(modules)+'.\n'
    body+='Definition boards := ['+';'.join(n+'.board' for n in modules)+'].\nDefinition board := concat boards.\n'
    for field,bound in [('small_sound','(N.to_nat 4096%N)'),('sound','score')]:
        body+=f'Lemma {field} : StateBoardSound {bound} board.\nProof. apply state_boards_sound. unfold boards.\n'
        body+=campaign.forall_proof(modules,field)+'\nQed.\n'
    body+='Lemma was_pending : forall family, In family board -> bootstrap_pending family.\nProof. apply boards_pending. unfold boards.\n'
    body+=campaign.forall_proof(modules,'was_pending')+'\nQed.\n'
    emit(ctx,prefix,'Board.v',body,'blank-routine.aggregate')
    machines=[campaign.unpack(n,17) for group in data['groups'] for n in group['rows']]
    inventory(ctx,prefix,m.NS,machines,4096)


def _row_boards(ctx):
    closure=ctx.module('check_closure_wave')
    packages=[('burn2-rw',b,'BBB24Burn2RW'+b,'check_burn2_rw') for b in ['B128','B256','B512','B1024','B881']]
    packages += [('burn2-timeout-state','Priority207','BBB24Burn2TimeoutStatePriority207','check_burn2_timeout_states')]
    packages += [('burn5-timeout-instruction',b,'BBB24Burn5TimeoutInstruction'+b,'check_burn5_timeout_instructions')
                 for b in ['Pilot64','Rest771']]
    for group,batch,ns,tool in packages:
        prefix='four/build/'+group+'/'+batch.lower()
        if not ctx.any_needed(prefix+'/'):
            continue
        m=ctx.module(tool)
        data=compact(ctx,'four/research/'+group+'-'+batch.lower()+'-board-input.json')
        rows=[dict(zip(data['columns'],v)) for v in data['rows']]
        names=[]
        for row in rows:
            name='Row'+hashlib.sha256(row['machine'].encode()).hexdigest()[:16];names.append(name)
            emit(ctx,prefix,name+'.v',closure.shard_source([row]),tool+'.row')
        emit(ctx,prefix,'All.v',m.aggregate_source(rows,names,ns),tool+'.aggregate_source')


def _prototype(ctx):
    prefix='four/build/burn10-state-closeout/prototype'
    for name in ['StateCensus','RootBridge','StateShadow']:
        if ctx.need(prefix+'/'+name+'.v'):
            source='four/proof-sources/burn10-state-closeout/'+name+'.v'
            emit(ctx,prefix,name+'.v',ctx.path(source).read_bytes(),source)


def _state_queues(ctx):
    """The exact weighted/ordinary queue layouts are recorded in build plans."""
    campaign=ctx.module('check_campaign')
    weighted=ctx.module('check_weighted_state')
    closure=ctx.module('check_closure_wave')
    aggregate=ctx.module('check_state_pipeline_batch').aggregate
    configs={}
    for name in ['burn12']:
        try:
            plan=ctx.read_json('four/research/'+name+'-campaign-build.json')
        except FileNotFoundError:
            continue
        for step in plan.get('steps',[]):
            cmd=step.get('command',[])
            if len(cmd)<2 or Path(cmd[1]).name not in ['check_burn2_weighted_state.py','check_burn2_state_ordinary.py']:
                continue
            opts={cmd[i]:cmd[i+1] for i in range(2,len(cmd)-1) if cmd[i].startswith('--') and not cmd[i+1].startswith('--')}
            prefix=opts['--output-dir']
            if ctx.any_needed(prefix+'/'):
                configs[prefix]=(cmd[1],opts)
    for prefix,(tool,opts) in sorted(configs.items()):
        ns=opts['--namespace'];size=int(opts.get('--shard-size','8'))
        inp=ctx.path(opts['--input'])
        state=Path(tool).name=='check_burn2_weighted_state.py'
        if state:
            rows,_=weighted.load_input(inp)
        else:
            data=compact(ctx,opts['--input'])
            rows=[dict(zip(data['columns'],r))for r in data['rows']]
        limit=int(opts.get('--limit','0'));rows=rows[:limit or len(rows)]
        names=[]
        for offset in range(0,len(rows),size):
            name=('WeightedState'if state else'Ordinary')+f'{len(names):04d}';names.append(name)
            text=weighted.render_shard(rows[offset:offset+size])if state else closure.shard_source(rows[offset:offset+size])
            emit(ctx,prefix,name+'.v',text,'state-queue.render_shard')
        if state:
            emit(ctx,prefix,'WeightedStateAll.v',aggregate(names,len(rows),4096,ns),'state-queue.aggregate')
            inventory(ctx,prefix,ns,[r['machine']for r in rows],4096,module='WeightedStateAll',
                      board='state_board',small='state_board_small',sound='state_board_bound',
                      pending='state_board_pending',target='WeightedStateInventory.v')
        else:
            emit(ctx,prefix,'OrdinaryAll.v',closure.aggregate_source(names,ns,4096,len(rows)),'ordinary.aggregate')
            inventory(ctx,prefix,ns,[r['machine']for r in rows],4096,module='OrdinaryAll',scope='both',
                      target='OrdinaryInventory.v')


def _history_groups(ctx):
    """State history batches use packed rows; both-bound upgrades use columns."""
    engine=ctx.module('check_state_pipeline_batch')
    closure=ctx.module('check_closure_wave')
    configs=[
      ('burn2-diagnostic-short','BBB24Burn2DiagnosticShort',1),
      ('burn3-history','BBB24Burn3History',4),
      ('burn4-history-refinement-pilot','BBB24Burn4HistoryRefinement',1),
      ('burn4-history4-continuation','BBB24Burn4History4Continuation',None),
      ('burn4-history4-continuation-closure','BBB24Burn4History4Closure',None),
      ('burn4-history4-continuation-growth64','BBB24Burn4History4Growth64',None),
      ('burn4-history4-continuation-growth451','BBB24Burn4History4Growth451',None)]
    for package,ns,size in configs:
        prefix='four/build/'+package+'/proof'
        if not ctx.any_needed(prefix+'/'):
            continue
        data=compact(ctx,'four/research/'+package+'-proof-input.json');groups=data['groups']
        shards=[]
        if size is None:
            plan=ctx.read_json('four/research/'+package+'-shard-plan.json')
            for sh in plan['shards']:
                # Every continuation plan is checked against one certificate.
                shards.append((sh['rows'],groups[0]['certificate']))
        else:
            for group in groups:
                for i in range(0,len(group['rows']),size):shards.append((group['rows'][i:i+size],group['certificate']))
        names=[];machines=[]
        for packed,certificate in shards:
            name=f'History{len(names):03d}';names.append(name)
            emit(ctx,prefix,name+'.v',engine.shard_text(packed,certificate,4096),'history.shard_text')
            machines.extend(engine.unpack(n)for n in packed)
        emit(ctx,prefix,'HistoryAll.v',engine.aggregate(names,len(machines),4096,ns),'history.aggregate')
        inventory(ctx,prefix,ns,machines,4096,module='HistoryAll',board='state_board',small='state_board_small',
                  sound='state_board_bound',pending='state_board_pending',target='HistoryInventory.v')
    for package,prefix,ns,size in [
      ('burn3-history-instruction','four/build/burn3-history-instruction/proof','BBB24Burn3HistoryInstruction',4),
      ('burn4-history-timeout8-pilot','four/build/burn4-history-timeout8/pilot/proof','BBB24Burn4HistoryTimeout8Pilot',1),
      ('burn4-history-timeout8-rest','four/build/burn4-history-timeout8/rest/proof','BBB24Burn4HistoryTimeout8Rest',1)]:
        if not ctx.any_needed(prefix+'/'):
            continue
        data=compact(ctx,'four/research/'+package+'-proof-input.json')
        rows=[dict(zip(data['columns'],r))for r in data['rows']];names=[]
        for i in range(0,len(rows),size):
            name=f'History{len(names):03d}';names.append(name)
            emit(ctx,prefix,name+'.v',closure.shard_source(rows[i:i+size]),'history-both.shard_source')
        emit(ctx,prefix,'HistoryAll.v',closure.aggregate_source(names,ns,4096,len(rows)),'history-both.aggregate')
        inventory(ctx,prefix,ns,[r['machine']for r in rows],4096,module='HistoryAll',scope='both',target='HistoryInventory.v')


def _simple_template_boards(ctx):
    """Handwritten exact packages with a compact inventory/batch wrapper."""
    specs=[
      ('burn3-relaxed-marker','check_burn3_relaxed_marker','four/build/burn3-history-targets/proof','ExampleBoard'),
      ('burn3-relaxed-marker-batch','check_burn3_relaxed_marker_batch','four/build/burn3-relaxed-marker-batch/proof','Batch'),
      ('burn4-entry-marker','check_burn4_entry_marker','four/build/burn4-entry-marker/proof','Batch'),
      ('burn4-marker-composition','check_burn4_marker_composition','four/build/burn4-marker-composition/proof','CompositionBoard')]
    for package,tool,prefix,board_module in specs:
        if not ctx.any_needed(prefix+'/'):
            continue
        m=ctx.module(tool);data=compact(ctx,'four/research/'+package+'-input.json')
        for rel,h in data.get('template_sha256',{}).items():
            body=ctx.path('four/'+rel).read_bytes()
            if hashlib.sha256(body).hexdigest()!=h:raise ValueError('Template changed: '+rel)
            emit(ctx,prefix,Path(rel).name,body,rel)
        rows=data.get('rows')
        if rows is not None and hasattr(m,'batch_source'):
            emit(ctx,prefix,'Batch.v',m.batch_source(rows),tool+'.batch_source')
        machines=[r['machine']for r in rows]if rows is not None else[data['machine']]
        inventory(ctx,prefix,m.NAMESPACE,machines,data.get('state_bound',0),module=board_module)


def _special_graph_cases(ctx):
    codec=ctx.module('weighted_codec_v2')
    specs=[
      ('burn3-pair-capacity','four/build/burn3-frequent-invariants/proof','check_burn3_pair_capacity','GraphCertificate','render_graph','pair_capacity'),
      ('burn3-tail-invariant','four/build/burn3-tail-invariant/proof','check_burn3_tail_invariant','SevenTargets','render_seven',None),
      ('burn4-ternary-counter','four/build/burn4-ternary-counter/proof','check_burn4_ternary_counter','FiveTargets','render_five',None),
      ('burn6-triple-capacity','four/build/burn6-triple-capacity/proof','check_burn6_triple_capacity','GraphCertificate','render_graph','triple_capacity')]
    for package,prefix,tool,target,fun,capacity in specs:
        if not ctx.any_needed(prefix+'/'):
            continue
        m=ctx.module(tool);data=compact(ctx,'four/research/'+package+'-input.json')
        bundle=ctx.path('four/'+data['bundle']['path'])
        packed=codec.bundle_decode(bundle.read_text());row=codec.unpack(packed[0])
        renderer=getattr(m,fun)
        text=renderer(row,packed[0][capacity])if capacity else renderer(row)
        emit(ctx,prefix,target+'.v',text,tool+'.'+fun)
        # Other package modules are tracked research/*.v templates. They can
        # be copied directly, with target hashes checked by the caller.
        names={'burn3-pair-capacity':['PairCapacity','Closeout'],
               'burn3-tail-invariant':['TailInvariant','Closeout'],
               'burn4-ternary-counter':['Counter','Tail','Closeout'],
               'burn6-triple-capacity':['TripleCapacity','Regression','Closeout']}[package]
        for name in names:
            rel='four/research/'+package+'/'+name+'.v'
            if ctx.need(prefix+'/'+name+'.v'):emit(ctx,prefix,name+'.v',ctx.path(rel).read_bytes(),rel)
        inventory(ctx,prefix,m.NAMESPACE,[m.MACHINE],data.get('state_bound',0),module='Closeout',scope='both',
                  instruction_bound=data.get('instruction_bound',0))
    prefix='four/build/burn6-triple-capacity-remaining/proof'
    if ctx.any_needed(prefix+'/'):
        m=ctx.module('check_burn6_triple_capacity_remaining')
        data=compact(ctx,'four/research/burn6-triple-capacity-remaining-input.json')
        packed=codec.bundle_decode(ctx.path('four/'+data['bundle']['path']).read_text())
        names=[]
        for i,row in enumerate(packed):
            name=f'Row{i:03d}';names.append(name)
            emit(ctx,prefix,name+'.v',m.render_row(row,i),'triple-remaining.render_row')
        emit(ctx,prefix,'All.v',m.aggregate_source(names,m.NS,0,2),'triple-remaining.aggregate')
        inventory(ctx,prefix,m.NS,m.MACHINES,0,module='All',scope='both')


def _transfer_boards(ctx):
    for package,tool,template in [
      ('burn4-ternary-template','check_burn4_ternary_template','Template'),
      ('burn4-ternary-swapped','check_burn4_ternary_swapped','Swapped'),
      ('burn5-tail-template','check_burn5_tail_template','Transfer')]:
        prefix='four/build/'+package+'/proof'
        if not ctx.any_needed(prefix+'/'):
            continue
        m=ctx.module(tool);data=compact(ctx,'four/research/'+package+'-input.json');rows=data['rows']
        rel='four/research/'+package+'/'+template+'.v'
        emit(ctx,prefix,template+'.v',ctx.path(rel).read_bytes(),rel)
        emit(ctx,prefix,'Board.v',m.board_source(rows),tool+'.board_source')
        inventory(ctx,prefix,m.NAMESPACE,[r['machine']for r in rows],data.get('state_bound',0),scope='both',
                  instruction_bound=data.get('instruction_bound',0))


def _capacity_inventory(ctx):
    prefix='four/build/burn2-capacity/inventory-proof'
    if not ctx.any_needed(prefix+'/'):
        return
    c=ctx.module('check_campaign')
    for kind in ['ordinary','weighted','capacity','portfolio']:
        name=kind.title()+'.v'
        if not ctx.need(prefix+'/'+name):continue
        report=ctx.read_json('four/research/burn2-capacity-'+kind+'-check.json')
        data=ctx.read_json('four/research/burn2-capacity-'+kind+'-machines.json')
        rows=[r['machine']for r in data['rows']]
        original=dict(report['descriptor'],scope='both',state_bound=4096,instruction_bound=4096,machines=rows)
        emit(ctx,prefix,name,c.inventory_source(original),'capacity.inventory_source')


class SinkPath:
    """Path-like output sink for existing pure write-interface renderers."""
    def __init__(self,ctx,rel,producer):self.ctx,self.rel,self.producer=ctx,rel,producer
    def __truediv__(self,name):return SinkPath(self.ctx,self.rel.rstrip('/')+'/'+str(name),self.producer)
    @property
    def name(self):return Path(self.rel).name
    @property
    def stem(self):return Path(self.rel).stem
    def write_text(self,text,*a,**kw):
        if self.ctx.need(self.rel):self.ctx.emit(self.rel,text,self.producer)
        return len(text)
    def mkdir(self,*a,**kw):pass


def _structural(ctx):
    prefix='four/build/burn2-structural/proof'
    if not ctx.any_needed(prefix+'/'):
        return
    m=ctx.module('check_burn2_structural')
    closure=ctx.module('check_closure_wave');codec=ctx.module('weighted_codec_v2')
    data=compact(ctx,'four/research/burn2-structural-input.json')
    ordinary=[]
    for spec in data['ordinary_sources']:
        src=compact(ctx,'four/'+spec['path']);pool={r[0]:dict(zip(src['columns'],r))for r in src['rows']}
        ordinary.extend(pool[name]for name in spec['machines'])
    registry=ctx.read_json('four/'+data['weighted_registry']);pool={}
    for spec in registry['bundles']:
        for row in codec.bundle_decode(ctx.path('four/'+spec['path']).read_text()):pool[row['machine']]=row
    weighted=[pool[name]for name in data['weighted_sources']]
    names=[];specs=[]
    for offset in range(0,len(ordinary),8):
        name=f'OrdinarySources{offset//8:03d}';names.append(name)
        emit(ctx,prefix,name+'.v',closure.shard_source(ordinary[offset:offset+8]),'structural.ordinary')
        specs.append(m.source_spec(name))
    portfolio=ctx.module('check_weighted_portfolio').configure()
    emit(ctx,prefix,'WeightedSources.v',portfolio.shard_source(weighted),'structural.weighted')
    specs.append(m.source_spec('WeightedSources',True))
    machines=[r['machine']for r in ordinary+weighted]
    config=dict(source_bound=4096,output_bound=8192,sources=specs)
    conjugate=ctx.module('check_conjugate_batch')
    conjugate.generate(config,machines,data['rows'],SinkPath(ctx,prefix,'structural.conjugate.generate'),m.NS)
    inventory(ctx,prefix,m.NS,[r[0]for r in data['rows']],8192,module='ConjugateAll',scope='both')


def _capacity_instruction(ctx):
    prefix='four/build/burn3-capacity-instruction/proof'
    if not ctx.any_needed(prefix+'/'):
        return
    m=ctx.module('check_burn3_capacity_instructions');closure=ctx.module('check_closure_wave')
    data=compact(ctx,'four/research/burn3-capacity-instruction-input.json')
    rows=[dict(zip(data['columns'],r))for r in data['rows']];names=[]
    for i,row in enumerate(rows):
        name=f'History{i:03d}';names.append(name)
        emit(ctx,prefix,name+'.v',closure.shard_source([row]),'capacity-instruction.shard')
    emit(ctx,prefix,'All.v',closure.aggregate_source(names,m.NAMESPACE,4096,len(rows)),'capacity-instruction.aggregate')
    inventory(ctx,prefix,m.NAMESPACE,[r['machine']for r in rows],4096,module='All',scope='both')


def _structural_instructions(ctx):
    closure=ctx.module('check_closure_wave');conjugate=ctx.module('check_conjugate_batch')
    for package,ns in [('burn5-structural-instruction','BBB24Burn5StructuralInstruction'),
                       ('burn9-structural-instruction','BBB24Burn9StructuralInstruction')]:
        prefix='four/build/'+package+'/proof'
        if not ctx.any_needed(prefix+'/'):
            continue
        tool='check_'+package.replace('-','_')+'s'
        m=ctx.module(tool);data=compact(ctx,'four/research/'+package+'-input.json')
        specs=[];machines=[]
        for i,row in enumerate(data['source_certificates']):
            name=f'Source{i:03d}';machines.append(row['machine'])
            emit(ctx,prefix,name+'.v',closure.shard_source([row]),tool+'.source')
            specs.append(dict(module=ns+'.'+name,board='board',bound=4096,nonhalt='nonhalt',small_sound='small_sound'))
        if package=='burn5-structural-instruction':
            # The tail source is a literal pure template in the original
            # generator; extract that literal rather than copy an ignored .v.
            literals=[n.value for n in ast.walk(ast.parse(inspect.getsource(m.generate)))
                      if isinstance(n,ast.Constant)and isinstance(n.value,str)
                      and 'Definition board := BBB24Burn3Tail.Closeout.board.'in n.value]
            if len(literals)!=1:raise ValueError('Tail-source template is ambiguous')
            emit(ctx,prefix,'TailSource.v',literals[0],tool+'.literal_tail_source')
            specs.append(dict(module=ns+'.TailSource',board='board',bound=4096,nonhalt='nonhalt',small_sound='small_sound'))
            machines.append(data['tail_source'])
        config=dict(source_bound=4096,output_bound=8192,sources=specs)
        conjugate.generate(config,machines,data['rows'],SinkPath(ctx,prefix,tool+'.conjugate.generate'),ns)
        inventory(ctx,prefix,ns,[r[0]for r in data['rows']],8192,module='ConjugateAll',scope='both')


def render(ctx):
    _prototype(ctx)
    _generic_cases(ctx)
    _marker_batches(ctx)
    _routine(ctx)
    _routine_prior(ctx)
    _blank_routine(ctx)
    _row_boards(ctx)
    _state_queues(ctx)
    _history_groups(ctx)
    _simple_template_boards(ctx)
    _special_graph_cases(ctx)
    _transfer_boards(ctx)
    _capacity_inventory(ctx)
    _structural(ctx)
    _capacity_instruction(ctx)
    _structural_instructions(ctx)
