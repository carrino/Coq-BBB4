"""Guard the exact proof inventory when native costs determine shard sizes."""
import unittest

from check_burn4_history4_continuation import make_shards, validate_shard_rows


class ProofShardIntegrity(unittest.TestCase):
    def test_slow_family_is_isolated_without_losing_order(self):
        rows = [1, 2, 3, 4, 5, 6]
        costs = dict(zip(rows, [.1, .2, 2.5, .1, .2, .3]))
        shards = make_shards(rows, costs)
        validate_shard_rows(rows, shards)
        self.assertEqual([shard['rows'] for shard in shards], [[1, 2], [3], [4, 5, 6]])

    def test_cheap_rows_still_have_a_bounded_shard_size(self):
        rows = list(range(11))
        shards = make_shards(rows, dict.fromkeys(rows, 0.001))
        validate_shard_rows(rows, shards)
        self.assertEqual([len(shard['rows']) for shard in shards], [4, 4, 3])

    def test_corrupt_partitions_are_rejected(self):
        expected = [1, 2, 3, 4]
        for rows in ([1, 2, 3], [1, 2, 3, 3], [2, 1, 3, 4], [1, 2, 3, 5],
                     [True, 2, 3, 4], []):
            with self.subTest(rows=rows), self.assertRaises(ValueError):
                validate_shard_rows(expected, [{'rows': rows, 'native_seconds': 0.1}])

    def test_oversized_shard_is_rejected_even_when_inventory_matches(self):
        rows = list(range(5))
        with self.assertRaises(ValueError):
            validate_shard_rows(rows, [{'rows': rows, 'native_seconds': 0.1}])

    def test_invalid_native_timings_are_rejected(self):
        for value in (-1, float('nan'), float('inf')):
            with self.subTest(value=value), self.assertRaises(ValueError):
                make_shards([1], {1: value})


if __name__ == '__main__':
    unittest.main()
