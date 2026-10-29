// Untrusted, survivor-focused census search. Every emitted closed certificate
// must be replayed by BBB24.Census.verify before it discharges any family.
// Brent checkpoints remove the old survey's fixed period window. Hash hits are
// confirmed by exact tape comparison before a Cycle certificate is emitted.
#include <algorithm>
#include <array>
#include <chrono>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <memory>
#include <stdexcept>
#include <string>
#include <vector>
using namespace std;
using U = uint64_t;

struct Cert {
  char kind = 'D';
  int anchor = 0, period = 0, reach = 0;
  bool mirror = false;
  vector<unique_ptr<Cert>> children;
};
struct Outcome {
  bool cycle = false;
  int slot = -1, steps = 0, anchor = 0, period = 0, reach = 0, shift = 0;
};
struct Statistics {
  uint64_t nodes = 0, steps = 0, branch_nodes = 0, cycles = 0, halt_cases = 0;
  int max_anchor = 0, max_period = 0;
};

class Walker {
  int fuel, origin, old_lo = 0, old_hi = 0;
  vector<unsigned char> tape, anchor_tape;
  vector<U> powers, inverses, prefix;
  static constexpr U base = 0x9e3779b185ebca87ULL;

  U contribution(int p) const {
    if (p < -fuel || p > fuel) return 0;
    return U(tape[origin+p]) * powers[origin+p];
  }
public:
  explicit Walker(int f) : fuel(f), origin(f+2), tape(2*f+5,0),
                          powers(2*f+5), inverses(2*f+5) {
    U inv = 1;
    for (int i=0; i<6; ++i) inv *= U(2)-base*inv;
    powers[0]=inverses[0]=1;
    for (size_t i=1; i<powers.size(); ++i) {
      powers[i]=powers[i-1]*base;
      inverses[i]=inverses[i-1]*inv;
    }
  }

  Outcome simulate(const array<int,8>& tm) {
    fill(tape.begin()+origin+old_lo, tape.begin()+origin+old_hi+1, 0);
    int pos=0, state=0, lo=0, hi=0, t=0;
    int anchor_pos=0, anchor_state=0, anchor_lo=0, anchor_hi=0, anchor_t=0;
    int minimum=0, maximum=0, right_cut=0, left_cut=0, power=1;
    U total=0, right_hash=0, left_hash=0, anchor_total=0;
    auto anchor_prefix = [&](int p) -> U {
      if (p < anchor_lo) return 0;
      if (p >= anchor_hi) return anchor_total;
      return prefix[p-anchor_lo+1];
    };
    auto checkpoint = [&]() {
      anchor_pos=pos; anchor_state=state; anchor_lo=lo; anchor_hi=hi; anchor_t=t;
      minimum=maximum=pos; right_cut=left_cut=pos; anchor_total=total;
      anchor_tape.assign(tape.begin()+origin+lo,tape.begin()+origin+hi+1);
      prefix.resize(anchor_tape.size()+1); prefix[0]=0;
      for (size_t i=0; i<anchor_tape.size(); ++i)
        prefix[i+1]=prefix[i]+U(anchor_tape[i])*powers[origin+lo+int(i)];
      right_hash=total-anchor_prefix(pos-1);
      left_hash=anchor_prefix(pos);
    };
    auto exact_match = [&](int displacement) {
      int left=min(anchor_lo,lo-displacement), right=max(anchor_hi,hi-displacement);
      if (displacement >= 0) left=max(left,minimum);
      else right=min(right,maximum);
      for (int p=left; p<=right; ++p) {
        int a=(p<anchor_lo || p>anchor_hi) ? 0 : anchor_tape[p-anchor_lo];
        int q=p+displacement;
        int b=(q<lo || q>hi) ? 0 : tape[origin+q];
        if (a!=b) return false;
      }
      return true;
    };
    checkpoint();
    while (true) {
      int slot=4*state+tape[origin+pos];
      if (tm[slot]==16 || t==fuel) {
        old_lo=lo; old_hi=hi;
        Outcome r; r.steps=t; r.slot=tm[slot]==16 ? slot : -1; return r;
      }
      int code=tm[slot], write=code/4;
      U delta=(U(write)-U(tape[origin+pos]))*powers[origin+pos];
      total+=delta;
      if (pos>=right_cut) right_hash+=delta;
      if (pos<=left_cut) left_hash+=delta;
      tape[origin+pos]=static_cast<unsigned char>(write);
      state=code%2; pos+=(code&2) ? 1 : -1; ++t;
      lo=min(lo,pos); hi=max(hi,pos); minimum=min(minimum,pos); maximum=max(maximum,pos);
      int displacement=pos-anchor_pos;
      int new_right=minimum+displacement, new_left=maximum+displacement;
      while (right_cut<new_right) right_hash-=contribution(right_cut++);
      while (right_cut>new_right) right_hash+=contribution(--right_cut);
      while (left_cut<new_left) left_hash+=contribution(++left_cut);
      while (left_cut>new_left) left_hash-=contribution(left_cut--);
      if (state==anchor_state) {
        U old_hash=displacement>=0 ? anchor_total-anchor_prefix(minimum-1)
                                  : anchor_prefix(maximum);
        U now_hash=displacement>=0 ? right_hash : left_hash;
        if (old_hash*inverses[origin+anchor_pos]==now_hash*inverses[origin+pos]
            && exact_match(displacement)) {
          old_lo=lo; old_hi=hi;
          Outcome r; r.cycle=true; r.steps=t; r.anchor=anchor_t;
          r.period=t-anchor_t; r.shift=displacement;
          r.reach=displacement>=0 ? anchor_pos-minimum : maximum-anchor_pos;
          return r;
        }
      }
      if (t-anchor_t==power) { checkpoint(); power*=2; }
    }
  }
};

array<int,8> parse(const string& s) {
  if (s.size()!=25 || s[12]!='_') throw runtime_error("Invalid machine: "+s);
  array<int,8> tm;
  for (int i=0; i<8; ++i) {
    int p=3*i+(i>=4);
    if (s.substr(p,3)=="---") { tm[i]=16; continue; }
    if (s[p]<'0' || s[p]>'3' || (s[p+1]!='L' && s[p+1]!='R')
        || (s[p+2]!='A' && s[p+2]!='B')) throw runtime_error("Invalid machine: "+s);
    tm[i]=4*(s[p]-'0')+2*(s[p+1]=='R')+(s[p+2]=='B');
  }
  return tm;
}

unique_ptr<Cert> search(Walker& walker, array<int,8>& tm, uint64_t limit, Statistics& stats) {
  auto cert=make_unique<Cert>();
  if (stats.nodes>=limit) return cert;
  ++stats.nodes;
  Outcome result=walker.simulate(tm); stats.steps+=result.steps;
  if (result.cycle) {
    cert->kind='C'; cert->anchor=result.anchor; cert->period=result.period;
    cert->reach=result.reach; cert->mirror=result.shift<0; ++stats.cycles;
    stats.max_anchor=max(stats.max_anchor,result.anchor);
    stats.max_period=max(stats.max_period,result.period); return cert;
  }
  if (result.slot<0 || stats.nodes>=limit) return cert;
  cert->kind='B'; cert->anchor=result.steps;
  ++stats.branch_nodes; ++stats.halt_cases;
  for (int code=0; code<16; ++code) {
    tm[result.slot]=code;
    cert->children.push_back(search(walker,tm,limit,stats));
  }
  tm[result.slot]=16;
  return cert;
}

bool closed(const Cert& c) {
  if (c.kind=='C') return true;
  if (c.kind!='B' || c.children.size()!=16) return false;
  for (const auto& child:c.children) if (!closed(*child)) return false;
  return true;
}
void emit(ostream& out, const Cert& c) {
  if (c.kind=='C') {
    out << "[\"C\"," << (c.mirror?1:0) << ',' << c.anchor << ',' << c.period << ',' << c.reach << ']';
  } else if (c.kind=='B') {
    out << "[\"B\"," << c.anchor << ",[";
    for (size_t i=0;i<c.children.size();++i) { if(i)out<<','; emit(out,*c.children[i]); }
    out << "]]";
  } else out << "[\"D\"]";
}

int main(int argc,char** argv) {
  try {
    if (argc!=5) throw runtime_error("usage: late_cycles INPUT OUTPUT_JSONL FUEL NODE_BUDGET_PER_FAMILY");
    int fuel=stoi(argv[3]); uint64_t node_budget=stoull(argv[4]);
    if (fuel<1 || fuel>10000000 || node_budget<1) throw runtime_error("Invalid search budget");
    ifstream input(argv[1]); ofstream output(argv[2]);
    if (!input || !output) throw runtime_error("Cannot open input or output");
    Walker walker(fuel);
    uint64_t rows=0, successes=0, partial=0, partial_closed=0, total_steps=0;
    auto start=chrono::steady_clock::now();
    string machine;
    while (getline(input,machine)) {
      if (!machine.empty() && machine.back()=='\r') machine.pop_back();
      auto tm=parse(machine); int free=count(tm.begin(),tm.end(),16);
      Statistics stats; auto cert=search(walker,tm,node_budget,stats);
      bool done=closed(*cert); ++rows; successes+=done; partial+=(free>0); partial_closed+=(free>0&&done);
      total_steps+=stats.steps;
      output << "{\"machine\":\"" << machine << "\",\"free_cells\":" << free
             << ",\"status\":\"" << (done?"candidate_closed":"pending") << "\",\"nodes\":" << stats.nodes
             << ",\"steps\":" << stats.steps << ",\"branch_nodes\":" << stats.branch_nodes
             << ",\"cycle_leaves\":" << stats.cycles << ",\"halt_cases\":" << stats.halt_cases
             << ",\"max_anchor\":" << stats.max_anchor << ",\"max_period\":" << stats.max_period
             << ",\"certificate\":";
      if(done)emit(output,*cert); else output << "null";
      output << "}\n";
      if (rows%4096==0) cerr << rows << " families, " << successes << " candidates\n";
    }
    cout << "{\"families\":" << rows << ",\"candidate_closed\":" << successes
         << ",\"concrete\":" << rows-partial << ",\"partial\":" << partial
         << ",\"partial_candidate_closed\":" << partial_closed << ",\"steps\":" << total_steps
         << ",\"seconds\":" << chrono::duration<double>(chrono::steady_clock::now()-start).count()
         << "}\n";
  } catch(const exception& e) { cerr << e.what() << '\n'; return 2; }
}
