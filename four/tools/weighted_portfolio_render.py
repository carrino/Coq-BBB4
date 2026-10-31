"""Render separately checked instruction witnesses from several orientations."""
from weighted_render_v4 import HEADER as BASE_HEADER, render as previous

HEADER = BASE_HEADER+'From Coq Require Import Bool.\nFrom BBB24 Require Import InstructionPortfolio.\n'


def render(row):
    variants, choices = row['variants'], row['choices']
    if not 1 <= len(variants) <= 8 or set(choices) != {str(i) for i in range(8)}:
        raise ValueError('A portfolio must select a witness for every instruction')
    if any(type(i) is not int or not 0 <= i < len(variants) for i in choices.values()):
        raise ValueError('Invalid portfolio witness index')
    text = HEADER
    for index, variant in enumerate(variants):
        if variant['graph']['machine'] != row['machine']:
            raise ValueError('Portfolio graphs describe different machines')
        body = previous(variant).split('Lemma checked:', 1)[0]
        if not body.startswith(BASE_HEADER):
            raise ValueError('Unexpected certificate header')
        text += f'Module G{index}.\n'+body[len(BASE_HEADER):]+f'End G{index}.\n'
    text += 'Definition family:TM:=G0.family.\n'
    for index, variant in enumerate(variants):
        graph = variant['graph']
        targets = [target for target in range(8) if choices[str(target)] == index]
        labels = ';'.join(f'(St{chr(65+t//4)},S{t%4})' for t in targets)
        side = 'true' if graph['mirror'] else 'false'
        text += f'Definition part{index}:WPart:=mkWPart {side} {graph["n"]}%nat {graph["t"]}%nat G{index}.nodes [{labels}] G{index}.certificate.\n'
        text += f'Lemma part{index}_checked:wp_part_check family part{index}=true.\nProof. vm_compute. reflexivity. Qed.\n'
    text += 'Definition portfolio:list WPart:=['+';'.join(f'part{i}' for i in range(len(variants)))+'].\n'
    conjunction = 'true'
    for index in reversed(range(len(variants))):
        conjunction = f'(wp_part_check family part{index} && {conjunction})'
    text += 'Lemma checked:wp_portfolio_check family portfolio=true.\nProof. unfold wp_portfolio_check;apply andb_true_iff;split.\n'
    text += f'- change ({conjunction}=true).\n  rewrite '+','.join(f'part{i}_checked' for i in range(len(variants)))+';reflexivity.\n'
    text += '- vm_compute;reflexivity.\nQed.\n'
    text += 'Theorem family_zero:NonHalt family /\\ Bounds 0%N 0%N family.\nProof. exact(wp_portfolio_check_sound family portfolio checked). Qed.\n'
    text += 'Theorem family_run:NonHalt family /\\ Bounds 4096%N 4096%N family.\nProof. destruct family_zero as[Hnh Hb];split;[exact Hnh|]. eapply(bounds_weaken 0%N 0%N 4096%N 4096%N family);[vm_compute;discriminate|vm_compute;discriminate|exact Hb]. Qed.\n'
    if len(variants) > 1:
        text += 'Example omitted_part_rejected:wp_portfolio_check family[part0]=false.\nProof. vm_compute. reflexivity. Qed.\n'
    for index, variant in enumerate(variants):
        graph = variant['graph']; actual = '(mirror_tm family)' if graph['mirror'] else 'family'
        text += f'Example incomplete_part{index}_rejected:wc_graph_check 4096%N 4096%N {actual} {graph["n"]}%nat {graph["t"]}%nat G{index}.nodes G{index}.certificate=false.\nProof. vm_compute. reflexivity. Qed.\n'
    return text
