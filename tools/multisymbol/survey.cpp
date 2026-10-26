// Exploratory, untrusted census. See README.md for the proof boundary.
// g++ -O3 -std=c++17 survey.cpp -o /tmp/bbb-survey
#include <algorithm>
#include <array>
#include <chrono>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <map>
#include <stdexcept>
#include <string>
#include <vector>
using namespace std;

struct Snapshot { int state, pos, lo; string tape; };
struct Result {
  string kind;
  int slot = -1, anchor = 0, period = 0, shift = 0, reach = 0;
  int state_score = 0, instr_score = 0;
};
int states = 2, symbols = 3, fuel = 256, window_size = 64;
vector<int> machine;
uint64_t nodes = 0, covered = 0;
map<string, uint64_t> leaves, weighted;
int max_state = 0, max_instr = 0;
string state_witness, instr_witness;
ofstream residue, certificates;

string encode() {
  string s;
  for (int i = 0; i < states * symbols; ++i) {
    if (i && i % symbols == 0) s += '_';
    int v = machine[i];
    if (v < 0) s += "---";
    else { s += char('0' + v / (2 * states)); s += (v / states % 2 ? 'R' : 'L'); s += char('A' + v % states); }
  }
  return s;
}
int at(const Snapshot& s, int p) {
  return p < s.lo || p >= s.lo + int(s.tape.size()) ? 0 : s.tape[p - s.lo];
}

Result simulate() {
  vector<unsigned char> tape(2 * fuel + 3, 0);
  const int origin = fuel + 1;
  int pos = 0, state = 0, lo = 0, hi = 0;
  vector<Snapshot> history;
  vector<int> fired;
  vector<int> last_state(states, 0);
  vector<int> last_instr(states * symbols, 0);
  for (int t = 0; t <= fuel; ++t) {
    int slot = state * symbols + tape[origin + pos];
    Snapshot now{state, pos, lo, string(tape.begin() + origin + lo, tape.begin() + origin + hi + 1)};
    int minpos = pos, maxpos = pos;
    for (int a = t - 1; a >= max(0, t - window_size); --a) {
      const auto& old = history[a];
      minpos = min(minpos, old.pos); maxpos = max(maxpos, old.pos);
      if (old.state != state || at(old, old.pos) != at(now, pos)) continue;
      int dx = pos - old.pos;
      int left = min(old.lo, now.lo - dx);
      int right = max(old.lo + int(old.tape.size()) - 1, now.lo + int(now.tape.size()) - 1 - dx);
      // A lap drifting right never needs cells left of its minimum;
      // drifting left is symmetric. The compared ray has blank padding.
      if (dx > 0) left = max(left, minpos);
      if (dx < 0) right = min(right, maxpos);
      bool same = true;
      for (int p = left; p <= right; ++p) if (at(old, p) != at(now, p + dx)) { same = false; break; }
      if (!same) continue;
      unsigned smask = 0, imask = 0;
      for (int j = a; j < t; ++j) { smask |= 1u << (fired[j] / symbols); imask |= 1u << fired[j]; }
      Result r{dx ? "translated" : "cycle"}; r.anchor = a; r.period = t - a; r.shift = dx; r.reach = dx < 0 ? maxpos - old.pos : old.pos - minpos;
      for (int q = 0; q < states; ++q) if (!(smask & (1u << q))) r.state_score = max(r.state_score, last_state[q]);
      for (int i = 0; i < states * symbols; ++i) if (!(imask & (1u << i))) r.instr_score = max(r.instr_score, last_instr[i]);
      return r;
    }
    if (machine[slot] < 0) {
      Result r{"halt"}; r.slot = slot; r.anchor = t; r.state_score = r.instr_score = t + 1; return r;
    }
    if (t == fuel) return Result{"unresolved"};
    history.push_back(move(now)); fired.push_back(slot);
    last_state[state] = last_instr[slot] = t + 1;
    int v = machine[slot];
    tape[origin + pos] = v / (2 * states); state = v % states; pos += (v / states % 2 ? 1 : -1);
    lo = min(lo, pos); hi = max(hi, pos);
  }
  throw logic_error("unreachable");
}
uint64_t power(unsigned n) { uint64_t v = 1; while (n--) v *= 2 * states * symbols + 1; return v; }
void record(const Result& r, int free_slots) {
  uint64_t weight = power(free_slots - (r.kind == "halt"));
  ++leaves[r.kind]; weighted[r.kind] += weight; covered += weight;
  if (r.state_score > max_state) { max_state = r.state_score; state_witness = encode(); }
  if (r.instr_score > max_instr) { max_instr = r.instr_score; instr_witness = encode(); }
  if (r.kind == "unresolved") residue << encode() << '\n';
  certificates << encode() << '\t' << r.kind << '\t' << weight << '\t' << r.anchor << '\t' << r.period << '\t' << r.shift << '\t' << r.state_score << '\t' << r.instr_score << '\t' << r.reach << '\n';
}
void census(int free_slots) {
  ++nodes;
  Result r = simulate();
  record(r, free_slots);
  if (r.kind != "halt") return;
  for (int v = 0; v < 2 * states * symbols; ++v) { machine[r.slot] = v; census(free_slots - 1); }
  machine[r.slot] = -1;
}
int main(int argc, char** argv) {
  if (argc < 2 || argc > 6) { cerr << "usage: survey OUTPUT_PREFIX [SYMBOLS=3] [FUEL=256] [WINDOW=64] [STATES=2]\n"; return 2; }
  if (argc > 2) symbols = stoi(argv[2]);
  if (argc > 3) fuel = stoi(argv[3]);
  if (argc > 4) window_size = stoi(argv[4]);
  if (argc > 5) states = stoi(argv[5]);
  if (states < 2 || states > 3) return 2;
  if (symbols < 2 || symbols > 4 || fuel < 1 || window_size < 1) return 2;
  machine.assign(states * symbols, -1);
  residue.open(string(argv[1]) + ".unresolved.txt"); certificates.open(string(argv[1]) + ".certificates.tsv");
  if (!residue || !certificates) return 2;
  certificates << "machine\tkind\tweight\tanchor\tperiod\tshift\tstate_score\tinstr_score\treach\n";
  auto start = chrono::steady_clock::now(); census(states * symbols);
  cout << "{\n  \"states\": " << states << ", \"symbols\": " << symbols << ", \"fuel\": " << fuel << ", \"window\": " << window_size
       << ",\n  \"nodes\": " << nodes << ", \"covered\": " << covered << ", \"expected\": " << power(states * symbols)
       << ",\n  \"max_state\": " << max_state << ", \"state_witness\": \"" << state_witness
       << "\",\n  \"max_instr\": " << max_instr << ", \"instr_witness\": \"" << instr_witness << "\",\n  \"leaves\": {";
  bool first = true; for (auto [k,v] : leaves) { if (!first) cout << ','; first = false; cout << '"' << k << "\":" << v; }
  cout << "},\n  \"weighted\": {"; first = true; for (auto [k,v] : weighted) { if (!first) cout << ','; first = false; cout << '"' << k << "\":" << v; }
  cout << "},\n  \"seconds\": " << chrono::duration<double>(chrono::steady_clock::now() - start).count() << "\n}\n";
  return covered == power(states * symbols) ? 0 : 1;
}
