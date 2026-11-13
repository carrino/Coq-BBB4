"""Check the accelerated instruction search against direct simulation."""
import unittest

from instruction_accel_hunt import INF, NAMES, NVAR, Poly, Sim, parse, slot_last, sum_poly

CHAMPION = '1RB2LA1RA1LB_0LB2RB3RB1LA'
FORMER = '1RB2RA1LA2LB_2LB3RB0RB1RA'
SAMPLES = [CHAMPION, FORMER, '1LB2RB3LA2RA_2RA3LA0LA1RA', '1LB2RB0RA1LB_3RA2RA1LB0LA',
           '1LB0RA0RB3RA_3RB3RA3LA2LB', '1LB2RA3LB1RA_2RB3LA1LB1RA']


def direct(tm, steps):
    """Plain simulation: state, head position, nonblank cells and last firings."""
    tape, pos, state, last = {}, 0, 0, [0] * 8
    for step in range(1, steps + 1):
        symbol = tape.get(pos, 0)
        write, right, target = tm[state][symbol]
        last[state * 4 + symbol] = step
        tape[pos] = write
        pos += 1 if right else -1
        state = target
    return state, pos, {p: s for p, s in tape.items() if s}, last


def expanded(sim):
    """Nonblank cells of an accelerated tape, with the head as the origin."""
    def cells(stack):
        out = []
        for symbol, count in reversed(stack):
            if count == INF: break
            block = [(symbol >> (2 * (sim.k - 1 - i))) & 3 for i in range(sim.k)]
            out += [block] * count
        return out
    left = [s for block in cells(sim.left) for s in reversed(block)]
    right = [s for block in cells(sim.right) for s in block]
    return left, right


class AcceleratedSearchTests(unittest.TestCase):
    def finish(self, text, block):
        sim = Sim(parse(text), block)
        sim.run(10**6)
        return sim

    def test_champion_score_is_reproduced_exactly(self):
        sim = self.finish(CHAMPION, 1)
        self.assertEqual(sim.status, 'INF_CHAIN')
        self.assertEqual([NAMES[s] for s in range(8) if sim.infmask >> s & 1], ['B0'])
        self.assertEqual(slot_last(sim)[3], 205770076433044242247860)
        self.assertEqual(sim.steps, 205770076433044242247860)

    def test_former_champion_score_is_reproduced_exactly(self):
        sim = self.finish(FORMER, 1)
        self.assertEqual(sim.status, 'INF_CHAIN')
        self.assertEqual(max(slot_last(sim)[s] for s in (0, 1, 2, 3, 5, 6, 7)), 67093892759901295)

    def test_accelerated_configurations_match_direct_simulation(self):
        checked = 0
        for text in SAMPLES:
            for block in (1, 2, 3):
                tm = parse(text)
                sim = Sim(tm, block)
                for _ in range(12):
                    sim.run(37)
                    if sim.status != 'RUN' or sim.steps > 60000: break
                    checked += 1
                    state, pos, tape, last = direct(tm, sim.steps)
                    left, right = expanded(sim)
                    self.assertEqual(state, sim.state, (text, block, sim.steps))
                    # the head stands between blocks; align by the facing cell
                    origin = pos if sim.dir else pos + 1
                    want = {p - origin: s for p, s in tape.items()}
                    have = {i: s for i, s in enumerate(right) if s}
                    have.update({-1 - i: s for i, s in enumerate(left) if s})
                    self.assertEqual(want, have, (text, block, sim.steps))
                    bound = slot_last(sim)
                    for slot in range(8):
                        self.assertLessEqual(last[slot], bound[slot], (text, block, slot))
                        self.assertEqual(last[slot] == 0, bound[slot] == 0, (text, block, slot))
        self.assertGreater(checked, 100)

    def test_summed_polynomial_matches_repeated_evaluation(self):
        x, y = Poly.var(0), Poly.var(1)
        poly = x.mul(x).add(x.mul(y).scale(3)).add(y.scale(5)).add(Poly.const(7))
        total = sum_poly(poly, [-2, 3])
        for start in ((10, 1), (41, 6)):
            for count in (1, 2, 5):
                brute = sum(poly.ev({0: start[0] - 2 * j, 1: start[1] + 3 * j}) for j in range(count))
                self.assertEqual(total.ev({0: start[0], 1: start[1], NVAR: count}), brute)


if __name__ == '__main__':
    unittest.main()
